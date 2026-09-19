/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import LeanPool.ACMax.AHL.NBWeighted
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Real.Basic

/-!
# The AHL stationary-measure vocabulary — walk decomposition, weights, and marginal sums

This file lands nodes **W0–W2** of the Alon–Hoory–Linial irregular-Moore walk-count proof, i.e. the
*vocabulary* the weighted AM–GM assembly (W3–W9) consumes.  Building on the non-backtracking
machinery of `AHL.NBWalkCount` / `AHL.NBWeighted` (`nbWalksFrom`, `nbExtend`, `nb_concat_iff`,
`card_nbWalksFrom`), it packages three layers.

## Contents

* **W0 — the reusable one-step decomposition.**  `nbWalksFrom_succ_eq_biUnion` exhibits the
  length-`(k+1)` non-backtracking walks from `x` as the disjoint `biUnion` of the one-edge
  extensions of the length-`k` walks (`k ≥ 1`), with `pairwiseDisjoint_nbExtend`, the fiber
  cardinality `card_nbExtend` (`= deg (prefix end) − 1`), and the endpoint/penultimate fiber facts
  `adj_of_mem_nbExtend` / `penultimate_of_mem_nbExtend`.  Both the cardinality (already landed) and
  every weighted marginal below then reduce through `Finset.sum_biUnion`.  No new mathematics —
  this simply extracts the decomposition buried in `card_nbWalksFrom_succ`.
* **W1 — the AHL walk weight.**  `nbWeight ⟨v, p⟩ = ∏_{1 ≤ j < len} (deg (getVert j) − 1)⁻¹`
  (the product over the *intermediate* vertices only).  It is positive under `δ ≥ 2`
  (`nbWeight_pos`), is `1` on walks of length `≤ 1` (`nbWeight_one`), and multiplies by exactly
  `(deg end − 1)⁻¹` under a one-edge extension (`nbWeight_concat`) — the mass-conservation identity
  driving the exact degree-bias.
* **W2 — the marginal sums.**  Over the global sigma finset `nbAll k` (all length-`k`
  non-backtracking walks, tagged by start): the *last-edge* marginal `nbLastWeight k u v` (walks
  ending at `v` with penultimate `u`), the *end* marginal `nbEndWeight k v` (walks ending at `v`),
  and the total `nbWeightTotal k`.  Their exact values (`= 1`, `= deg v`, `= D`) are AHL's
  stationarity `xP = x`, proved in the follow-up node W3–W5, not here; this file lands the defs and
  their membership rewrite `mem_nbAll`.

## Formalization note — directed edges as (penultimate, end) pairs, not `SimpleGraph.Dart`

AHL runs its stationary walk over the `D` *directed edges*; the `xP = x` identity is a statement
about the *last* directed edge of a walk.  Mathlib offers `SimpleGraph.Dart`, but the landed
counting vocabulary already carries the whole walk, whose last directed edge `(penultimate, end)`
is recovered by `Walk.penultimate` and the endpoint tag `s.1`.  We therefore formalize a directed
edge as that `(penultimate, end)` pair and phrase the last-edge marginal `nbLastWeight` as a filter
on those two fields — keeping the marginal identities as sums over the already-landed `nbWalksFrom`
finsets with **no** `Dart`-to-walk bridge.  (`Walk.penultimate_concat` is already in Mathlib, so the
"penultimate of an extension" fiber fact needs no fresh lemma.)
-/

namespace ACMax

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]

/-! ### W0 — the reusable one-step decomposition -/

/-- **Disjointness of the extension fibers.**  Over distinct prefix walks the one-edge
non-backtracking extension sets `nbExtend G x` are disjoint: a shared extension `p.concat _`
determines its prefix `p` via `Walk.concat_inj`.  This is the disjointness the `biUnion`
decomposition and every weighted regrouping below rely on. -/
theorem pairwiseDisjoint_nbExtend (x : V) (k : ℕ) :
    Set.PairwiseDisjoint (↑(nbWalksFrom G x k)) (nbExtend G x) := by
  intro s _ s' _ hss'
  refine Finset.disjoint_left.mpr fun y hy hy' => ?_
  obtain ⟨u, p⟩ := s
  obtain ⟨u', p'⟩ := s'
  rw [nbExtend, Finset.mem_image] at hy hy'
  obtain ⟨b, hb, hby⟩ := hy
  obtain ⟨b', hb', hby'⟩ := hy'
  rw [Finset.mem_sdiff, mem_neighborFinset] at hb hb'
  simp only [dite_eq_left hb.1] at hby
  simp only [dite_eq_left hb'.1] at hby'
  rw [← hby'] at hby
  simp only [Sigma.mk.injEq] at hby
  obtain ⟨rfl, hheq⟩ := hby
  obtain ⟨rfl, hcopy⟩ := Walk.concat_inj (eq_of_heq hheq)
  rw [Walk.copy_rfl_rfl] at hcopy
  exact hss' (by rw [hcopy])

/-- **Fiber cardinality.**  A prefix walk `s` (non-nil, so its endpoint has a penultimate) has
exactly `deg s.1 − 1` non-backtracking extensions — one per neighbour of the endpoint other than
the arrived-from vertex.  This is `nb_extension_count` transported across the image. -/
theorem card_nbExtend {x : V} {s : Σ v : V, G.Walk x v} (hnn : ¬ s.2.Nil) :
    (nbExtend G x s).card = G.degree s.1 - 1 := by
  have hadj : G.Adj s.1 s.2.penultimate := (s.2.adj_penultimate hnn).symm
  rw [nbExtend, Finset.card_image_of_injOn, nb_extension_count G hadj]
  intro b hb b' hb' hbb
  rw [Finset.mem_coe, Finset.mem_sdiff, mem_neighborFinset] at hb hb'
  simp only [dite_eq_left hb.1, dite_eq_left hb'.1] at hbb
  exact congrArg Sigma.fst hbb

/-- **Penultimate of an extension.**  Every extension of `s` has the prefix endpoint `s.1` as its
penultimate vertex: the old endpoint becomes the new intermediate vertex.  (Immediate from
`Walk.penultimate_concat`.) -/
theorem penultimate_of_mem_nbExtend {x : V} {s s' : Σ v : V, G.Walk x v}
    (hs' : s' ∈ nbExtend G x s) : s'.2.penultimate = s.1 := by
  rw [nbExtend, Finset.mem_image] at hs'
  obtain ⟨b, hb, hbs'⟩ := hs'
  rw [Finset.mem_sdiff, mem_neighborFinset] at hb
  simp only [dite_eq_left hb.1] at hbs'
  rw [← hbs']
  exact Walk.penultimate_concat s.2 hb.1

/-- **The one-step decomposition** (W0).  For `k ≥ 1`, the length-`(k+1)` non-backtracking walks
from `x` are exactly the disjoint union of the one-edge non-backtracking extensions of the
length-`k` ones.  Extracted from the proof of `card_nbWalksFrom_succ`; the cardinality and every
weighted marginal of the AHL assembly are read off this identity via `Finset.sum_biUnion`. -/
theorem nbWalksFrom_succ_eq_biUnion (x : V) {k : ℕ} (hk : 1 ≤ k) :
    nbWalksFrom G x (k + 1) = (nbWalksFrom G x k).biUnion (nbExtend G x) := by
  have ha : ∀ s ∈ nbWalksFrom G x k, nbExtend G x s ⊆ nbWalksFrom G x (k + 1) := by
    intro s hs
    obtain ⟨hlen, hnb⟩ := mem_nbWalksFrom.mp hs
    have hnn : ¬ s.2.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
    intro y hy
    rw [nbExtend, Finset.mem_image] at hy
    obtain ⟨b, hb, hby⟩ := hy
    rw [Finset.mem_sdiff, mem_neighborFinset, Finset.mem_singleton] at hb
    simp only [dite_eq_left hb.1] at hby
    subst hby
    refine mem_nbWalksFrom.mpr ⟨?_, ?_⟩
    · change (s.2.concat hb.1).length = k + 1
      rw [Walk.length_concat, hlen]
    · change IsNonBacktracking (s.2.concat hb.1)
      exact (nb_concat_iff s.2 hnn hb.1).mpr ⟨hnb, hb.2⟩
  have hsub : nbWalksFrom G x (k + 1) ⊆ (nbWalksFrom G x k).biUnion (nbExtend G x) := by
    intro s' hs'
    obtain ⟨v, w⟩ := s'
    obtain ⟨hlen, hnb⟩ := mem_nbWalksFrom.mp hs'
    clear hs'
    cases w with
    | nil => rw [Walk.length_nil] at hlen; exact absurd hlen (by omega)
    | cons h p =>
      obtain ⟨u, q, h', hqc⟩ := Walk.exists_cons_eq_concat h p
      rw [Walk.length_cons] at hlen
      have hql : q.length = k := by
        have hc := congrArg Walk.length hqc
        rw [Walk.length_cons, Walk.length_concat] at hc
        omega
      have hqnn : ¬ q.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
      rw [hqc] at hnb
      obtain ⟨hqnb, hpen⟩ := (nb_concat_iff q hqnn h').mp hnb
      rw [Finset.mem_biUnion]
      refine ⟨⟨u, q⟩, mem_nbWalksFrom.mpr ⟨hql, hqnb⟩, ?_⟩
      rw [hqc, nbExtend, Finset.mem_image]
      refine ⟨v, ?_, ?_⟩
      · rw [Finset.mem_sdiff, mem_neighborFinset, Finset.mem_singleton]
        exact ⟨h', hpen⟩
      · simp only [dite_eq_left h']
  exact Finset.Subset.antisymm hsub (Finset.biUnion_subset.mpr ha)

/-! ### W1 — the AHL walk weight -/

/-- **The AHL walk weight.**  For a length-`len` non-backtracking walk `s = ⟨v, p⟩` starting at `x`,
the weight is the product `∏_{1 ≤ j < len} (deg (p.getVert j) − 1)⁻¹` over the *intermediate*
vertices only (endpoints `0` and `len` excluded; the empty product is `1` when `len ≤ 1`).  This is
AHL's non-returning-walk probability, cleared of the uniform starting mass. -/
noncomputable def nbWeight {x : V} (s : Σ v : V, G.Walk x v) : ℝ :=
  ∏ j ∈ Finset.Ico 1 s.2.length, ((G.degree (s.2.getVert j) : ℝ) - 1)⁻¹

omit [DecidableEq V] in
/-- Unfolding of `nbWeight` on an explicit sigma constructor. -/
theorem nbWeight_mk {x v : V} (p : G.Walk x v) :
    nbWeight (⟨v, p⟩ : Σ w : V, G.Walk x w) =
      ∏ j ∈ Finset.Ico 1 p.length, ((G.degree (p.getVert j) : ℝ) - 1)⁻¹ := rfl

omit [DecidableEq V] in
/-- **The weight is `1` on short walks.**  For a walk of length `≤ 1` the intermediate range
`Ico 1 len` is empty, so the weight is the empty product `1`. -/
theorem nbWeight_one {x : V} {s : Σ v : V, G.Walk x v} (h : s.2.length ≤ 1) : nbWeight s = 1 := by
  rw [nbWeight, Finset.Ico_eq_empty_of_le h, Finset.prod_empty]

omit [DecidableEq V] in
/-- **Positivity.**  Under `δ ≥ 2` every factor `(deg (getVert j) − 1)⁻¹` is positive, so the whole
weight is positive. -/
theorem nbWeight_pos (hδ2 : ∀ v, 2 ≤ G.degree v) {x : V} (s : Σ v : V, G.Walk x v) :
    0 < nbWeight s := by
  rw [nbWeight]
  refine Finset.prod_pos fun j _ => ?_
  rw [inv_pos, sub_pos]
  have h1 : (1 : ℝ) < (G.degree (s.2.getVert j) : ℝ) := by exact_mod_cast hδ2 (s.2.getVert j)
  exact h1

omit [DecidableEq V] in
/-- **Weight under a one-edge extension** (mass conservation).  Extending a non-nil walk
`p : G.Walk x v` by an edge `h : G.Adj v t` multiplies the weight by exactly `(deg v − 1)⁻¹` — the
old endpoint `v` becomes the new intermediate vertex.  This is the whole AHL trick: the weighted
end-count obeys an *exact* degree law (unlike the raw end-count). -/
theorem nbWeight_concat {x v t : V} (p : G.Walk x v) (hp : ¬ p.Nil) (h : G.Adj v t) :
    nbWeight (⟨t, p.concat h⟩ : Σ w : V, G.Walk x w) =
      nbWeight (⟨v, p⟩ : Σ w : V, G.Walk x w) * ((G.degree v : ℝ) - 1)⁻¹ := by
  have hL : 1 ≤ p.length := Walk.not_nil_iff_lt_length.mp hp
  have hgv : ∀ j, j < p.length → (p.concat h).getVert j = p.getVert j := by
    intro j hj
    rw [Walk.concat_eq_append, Walk.getVert_append]
    exact ite_eq_left hj
  have hlast : (p.concat h).getVert p.length = v := by
    calc (p.concat h).getVert p.length
        = (p.concat h).getVert ((p.concat h).length - 1) := by
          rw [Walk.length_concat, Nat.add_sub_cancel]
      _ = (p.concat h).penultimate := rfl
      _ = v := Walk.penultimate_concat p h
  rw [nbWeight_mk (p.concat h), nbWeight_mk p, Walk.length_concat, Finset.prod_Ico_succ_top hL]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [hgv j (Finset.mem_Ico.mp hj).2]
  · rw [hlast]

/-! ### W2 — the marginal sums -/

/-- The global sigma finset of all length-`k` non-backtracking walks, tagged by their start: an
element `⟨x, ⟨v, p⟩⟩` is a length-`k` non-backtracking walk `p : G.Walk x v`. -/
def nbAll (k : ℕ) : Finset (Σ x : V, Σ v : V, G.Walk x v) :=
  Finset.univ.sigma fun x => nbWalksFrom G x k

/-- Membership in `nbAll`: `⟨x, ⟨v, p⟩⟩` lies in `nbAll k` iff `p` has length `k` and is
non-backtracking (the start ranges over all of `V`). -/
theorem mem_nbAll {k : ℕ} {t : Σ x : V, Σ v : V, G.Walk x v} :
    t ∈ nbAll (G := G) k ↔ t.2.2.length = k ∧ IsNonBacktracking t.2.2 := by
  rw [nbAll, Finset.mem_sigma]
  simp only [Finset.mem_univ, true_and]
  exact mem_nbWalksFrom

/-- **The last-edge marginal** (AHL's `xP = x`, def only).  The total weight of the length-`k`
non-backtracking walks whose last directed edge is `(u, v)` — i.e. ending at `v` with penultimate
`u`.  Its value `1` (for `k ≥ 1`, `G.Adj u v`) is the stationarity identity proved in node W3. -/
noncomputable def nbLastWeight (k : ℕ) (u v : V) : ℝ :=
  ∑ t ∈ (nbAll (G := G) k).filter (fun t => t.2.1 = v ∧ t.2.2.penultimate = u), nbWeight t.2

/-- **The end marginal** (def only).  The total weight of the length-`k` non-backtracking walks
ending at `v`; its value `deg v` (node W4) is the marginal of `nbLastWeight` over the neighbours of
`v`. -/
noncomputable def nbEndWeight (k : ℕ) (v : V) : ℝ :=
  ∑ t ∈ (nbAll (G := G) k).filter (fun t => t.2.1 = v), nbWeight t.2

/-- **The total weight** (def only).  The total weight of all length-`k` non-backtracking walks;
its value `D = ∑ v, deg v` (node W5) is the normalization `∑_v nbEndWeight k v`. -/
noncomputable def nbWeightTotal (k : ℕ) : ℝ :=
  ∑ t ∈ nbAll (G := G) k, nbWeight t.2

end ACMax
