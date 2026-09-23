/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.AHL.AHLStationary
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-!
# The AHL stationary marginal VALUES — `xP = x` and its consequences (nodes W3–W5)

This file lands nodes **W3–W5** of the Alon–Hoory–Linial irregular-Moore walk-count proof, the
*hard* node of the ladder.  Building on the weight vocabulary of `AHL.AHLStationary` (`nbWeight`,
`nbWeight_concat`, `nbWalksFrom_succ_eq_biUnion`, the
marginal defs `nbLastWeight`/`nbEndWeight`/`nbWeightTotal`), it proves that the *weighted* marginals
attain their exact stationary values — the degree-bias is an identity, not an inequality.

Throughout `hδ2 : ∀ v, 2 ≤ G.degree v`.  A directed edge is the `(penultimate, end)` pair of a walk.

## Contents

* **W3 — the last-edge marginal** (`nbLastWeight_eq_one`, AHL's `xP = x`).  For every `k ≥ 1` and
  every directed edge `(u, v)` (`G.Adj u v`), the total weight of the length-`k` non-backtracking
  walks whose last directed edge is `(u, v)` is exactly `1`.  Proved by induction on `k`: the
  concat step splits a prefix's mass `(deg end − 1)⁻¹` to each of its `deg end − 1` extensions
  (`nbWeight_concat`), so the mass through each dart is invariant.  The engine is
  `nbLastWeight_succ_eq`, the exact one-step recursion built from the extension bijection.
* **W4 — the end marginal** (`nbEndWeight_eq_degree`).  The total weight of the length-`k`
  non-backtracking walks ending at `v` is exactly `deg v`; it is the marginal of `nbLastWeight`
  over the neighbours of `v`.
* **W5 — the total** (`nbWeightTotal_eq`).  The total weight of all length-`k` non-backtracking
  walks is exactly `D = ∑ v, deg v` — the normalization the weighted AM–GM (W7) consumes.
-/

@[expose] public section

namespace ACMax

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **Penultimate of a length-`1` walk is its start.**  A one-edge walk `x → w` has penultimate
vertex `getVert 0 = x`. -/
theorem penultimate_of_length_one {x w : V} {p : G.Walk x w} (hp : p.length = 1) :
    p.penultimate = x := by
  change p.getVert (p.length - 1) = x
  rw [hp]
  exact Walk.getVert_zero p

/-! ### The per-start expansion of a marginal sum -/

/-- **Sigma-to-per-start expansion.**  A weighted marginal filtered by a predicate `Q` of the
`(end, penultimate)` pair equals the sum over starts `x` of the per-start filtered weight.  This is
`Finset.sum_sigma` for the `nbAll = univ.sigma nbWalksFrom` decomposition. -/
theorem sum_nbAll_filter (k : ℕ) (Q : V → V → Prop) [DecidableRel Q] :
    ∑ t ∈ (nbAll (G := G) k).filter (fun t => Q t.2.1 t.2.2.penultimate), nbWeight t.2 =
      ∑ x : V, ∑ s ∈ (nbWalksFrom G x k).filter (fun s => Q s.1 s.2.penultimate), nbWeight s := by
  rw [nbAll, Finset.sum_filter, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_filter]

/-- The last-edge marginal `nbLastWeight k u v`, written as a sum over starts of the per-start
weight of length-`k` walks ending at `v` with penultimate `u`. -/
theorem nbLastWeight_eq_sum (k : ℕ) (u v : V) :
    nbLastWeight (G := G) k u v =
      ∑ x : V, ∑ s ∈ (nbWalksFrom G x k).filter (fun s => s.1 = v ∧ s.2.penultimate = u),
        nbWeight s := by
  rw [nbLastWeight]
  exact sum_nbAll_filter k (fun a b => a = v ∧ b = u)

/-- The prefix (source) sum of the extension bijection, written as a sum over starts.  These are the
length-`k` walks ending at `u` whose penultimate avoids `v` (so they extend to `v`). -/
theorem sum_R_eq_sum (k : ℕ) (u v : V) :
    ∑ t ∈ (nbAll (G := G) k).filter (fun t => t.2.1 = u ∧ t.2.2.penultimate ≠ v), nbWeight t.2 =
      ∑ x : V, ∑ s ∈ (nbWalksFrom G x k).filter (fun s => s.1 = u ∧ s.2.penultimate ≠ v),
        nbWeight s :=
  sum_nbAll_filter k (fun a b => a = u ∧ b ≠ v)

/-! ### The one-step extension identity (the core of W3) -/

/-- **The per-prefix extension mass.**  For a length-`k` non-backtracking prefix `s'` (`k ≥ 1`), the
weight it contributes to length-`(k+1)` walks with last edge `(u, v)` is `nbWeight s' · (deg u
−1)⁻¹`
when `s'` ends at `u` and its penultimate avoids `v` (so the extension to `v` is non-backtracking),
and `0` otherwise.  This is the mass-conservation identity behind `xP = x`. -/
theorem sum_nbExtend_ite {u v : V} (huv : G.Adj u v) {x : V} {k : ℕ} (hk : 1 ≤ k)
    {s' : Σ w : V, G.Walk x w} (hs' : s' ∈ nbWalksFrom G x k) :
    (∑ s ∈ nbExtend G x s', (if s.1 = v ∧ s.2.penultimate = u then nbWeight s else 0)) =
      (if s'.1 = u ∧ s'.2.penultimate ≠ v then nbWeight s' * ((G.degree u : ℝ) - 1)⁻¹ else 0) := by
  obtain ⟨hlen, _hnb⟩ := mem_nbWalksFrom.mp hs'
  have hnn : ¬ s'.2.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
  have hinj : Set.InjOn
      (fun t => if h : G.Adj s'.1 t then ⟨t, s'.2.concat h⟩ else (⟨x, Walk.nil⟩ : Σ w : V, G.Walk
        x w))
      (↑(G.neighborFinset s'.1 \ {s'.2.penultimate})) := by
    intro b hb b' hb' hbb
    rw [Finset.mem_coe, Finset.mem_sdiff, mem_neighborFinset] at hb hb'
    simp only [dite_eq_left hb.1, dite_eq_left hb'.1] at hbb
    exact congrArg Sigma.fst hbb
  have key1 : (∑ s ∈ nbExtend G x s', (if s.1 = v ∧ s.2.penultimate = u then nbWeight s else 0))
      = ∑ s ∈ nbExtend G x s', (if s.1 = v ∧ s'.1 = u then nbWeight s else 0) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    simp only [penultimate_of_mem_nbExtend hs]
  rw [key1, nbExtend, Finset.sum_image hinj]
  trans (∑ t ∈ G.neighborFinset s'.1 \ {s'.2.penultimate},
      (if t = v ∧ s'.1 = u then nbWeight s' * ((G.degree s'.1 : ℝ) - 1)⁻¹ else 0))
  · refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_sdiff, mem_neighborFinset, Finset.mem_singleton] at ht
    simp only [dite_eq_left ht.1, nbWeight_concat s'.2 hnn ht.1, Sigma.eta]
  · by_cases hu : s'.1 = u
    · have hsum : (∑ t ∈ G.neighborFinset s'.1 \ {s'.2.penultimate},
          (if t = v ∧ s'.1 = u then nbWeight s' * ((G.degree s'.1 : ℝ) - 1)⁻¹ else 0))
          = ∑ t ∈ G.neighborFinset s'.1 \ {s'.2.penultimate},
            (if t = v then nbWeight s' * ((G.degree s'.1 : ℝ) - 1)⁻¹ else 0) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases htv : t = v
        · rw [ite_eq_left ⟨htv, hu⟩, ite_eq_left htv]
        · rw [ite_eq_right (fun h => htv h.1), ite_eq_right htv]
      rw [hsum, Finset.sum_ite_eq']
      by_cases hp : s'.2.penultimate = v
      · have hvnD : v ∉ G.neighborFinset s'.1 \ {s'.2.penultimate} := by
          rw [Finset.mem_sdiff, Finset.mem_singleton]
          rintro ⟨-, hne⟩
          exact hne hp.symm
        rw [ite_eq_right hvnD, ite_eq_right (fun hc => hc.2 hp)]
      · have hvD : v ∈ G.neighborFinset s'.1 \ {s'.2.penultimate} := by
          rw [Finset.mem_sdiff, mem_neighborFinset, Finset.mem_singleton]
          exact ⟨by rw [hu]; exact huv, fun h => hp h.symm⟩
        rw [ite_eq_left hvD, ite_eq_left ⟨hu, hp⟩, hu]
    · rw [ite_eq_right (fun hc => hu hc.1)]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [ite_eq_right (fun hc => hu hc.2)]

/-- **Per-start one-step recursion.**  For a fixed start `x` and `k ≥ 1`, the per-start weight of
length-`(k+1)` walks with last edge `(u, v)` is the per-start prefix mass (walks ending at `u` whose
penultimate avoids `v`) scaled by `(deg u − 1)⁻¹`.  Assembled from the `biUnion` decomposition and
`sum_nbExtend_ite`. -/
theorem innerLast_succ {u v : V} (huv : G.Adj u v) (x : V) {k : ℕ} (hk : 1 ≤ k) :
    ∑ s ∈ (nbWalksFrom G x (k + 1)).filter (fun s => s.1 = v ∧ s.2.penultimate = u), nbWeight s =
      (∑ s' ∈ (nbWalksFrom G x k).filter (fun s' => s'.1 = u ∧ s'.2.penultimate ≠ v), nbWeight s')
        * ((G.degree u : ℝ) - 1)⁻¹ := by
  have hL : (∑ s ∈ (nbWalksFrom G x (k + 1)).filter (fun s => s.1 = v ∧ s.2.penultimate = u),
        nbWeight s)
      = ∑ s' ∈ nbWalksFrom G x k,
        (if s'.1 = u ∧ s'.2.penultimate ≠ v then nbWeight s' * ((G.degree u : ℝ) - 1)⁻¹ else 0) :=
          by
    rw [Finset.sum_filter, nbWalksFrom_succ_eq_biUnion x hk,
      Finset.sum_biUnion (pairwiseDisjoint_nbExtend x k)]
    exact Finset.sum_congr rfl fun s' hs' => sum_nbExtend_ite huv hk hs'
  have hR : (∑ s' ∈ (nbWalksFrom G x k).filter (fun s' => s'.1 = u ∧ s'.2.penultimate ≠ v),
        nbWeight s') * ((G.degree u : ℝ) - 1)⁻¹
      = ∑ s' ∈ nbWalksFrom G x k,
        (if s'.1 = u ∧ s'.2.penultimate ≠ v then nbWeight s' * ((G.degree u : ℝ) - 1)⁻¹ else 0) :=
          by
    rw [Finset.sum_filter, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s' _ => by split_ifs <;> ring
  rw [hL, hR]

/-- **Refolding the prefix mass into last-edge marginals.**  The prefix sum (length-`k` walks ending
at `u`, penultimate avoiding `v`) is the sum over admissible previous vertices `w ∈ N(u) \ {v}` of
the last-edge marginals `nbLastWeight k w u`.  A fiberwise partition on the penultimate. -/
theorem sum_R_eq_sum_lastWeight {u v : V} (huv : G.Adj u v) {k : ℕ} (hk : 1 ≤ k) :
    ∑ t ∈ (nbAll (G := G) k).filter (fun t => t.2.1 = u ∧ t.2.2.penultimate ≠ v), nbWeight t.2 =
      ∑ w ∈ G.neighborFinset u \ {v}, nbLastWeight (G := G) k w u := by
  have hmaps : ∀ t ∈ (nbAll (G := G) k).filter (fun t => t.2.1 = u ∧ t.2.2.penultimate ≠ v),
      t.2.2.penultimate ∈ G.neighborFinset u \ {v} := by
    rintro ⟨tx, tv, tp⟩ ht
    rw [Finset.mem_filter, mem_nbAll] at ht
    obtain ⟨⟨hlen, _⟩, hend, hpen⟩ := ht
    subst hend
    have hnn : ¬ tp.Nil := Walk.not_nil_iff_lt_length.mpr (by
      have : tp.length = k := hlen; omega)
    rw [Finset.mem_sdiff, mem_neighborFinset, Finset.mem_singleton]
    exact ⟨(tp.adj_penultimate hnn).symm, hpen⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun t => nbWeight t.2)]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hw
  rw [nbLastWeight, Finset.filter_filter]
  refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
  constructor
  · rintro ⟨⟨hend, _⟩, hpenw⟩
    exact ⟨hend, hpenw⟩
  · rintro ⟨hend, hpenw⟩
    exact ⟨⟨hend, fun h => hw.2 (hpenw.symm.trans h)⟩, hpenw⟩

/-- **The exact one-step recursion** (the engine of W3).  For `k ≥ 1` and `G.Adj u v`, the last-edge
marginal at step `k+1` is the sum of the previous-step last-edge marginals over the admissible
predecessors `w ∈ N(u) \ {v}`, scaled by `(deg u − 1)⁻¹` — the concat step redistributes each
prefix's mass equally to its `deg u − 1` extensions. -/
theorem nbLastWeight_succ_eq {u v : V} (huv : G.Adj u v) {k : ℕ} (hk : 1 ≤ k) :
    nbLastWeight (G := G) (k + 1) u v =
      (∑ w ∈ G.neighborFinset u \ {v}, nbLastWeight (G := G) k w u) * ((G.degree u : ℝ) - 1)⁻¹ := by
  calc nbLastWeight (G := G) (k + 1) u v
      = ∑ x : V, ∑ s ∈ (nbWalksFrom G x (k + 1)).filter (fun s => s.1 = v ∧ s.2.penultimate = u),
          nbWeight s := nbLastWeight_eq_sum (k + 1) u v
    _ = ∑ x : V, (∑ s' ∈ (nbWalksFrom G x k).filter (fun s' => s'.1 = u ∧ s'.2.penultimate ≠ v),
          nbWeight s') * ((G.degree u : ℝ) - 1)⁻¹ :=
        Finset.sum_congr rfl fun x _ => innerLast_succ huv x hk
    _ = (∑ x : V, ∑ s' ∈ (nbWalksFrom G x k).filter (fun s' => s'.1 = u ∧ s'.2.penultimate ≠ v),
          nbWeight s') * ((G.degree u : ℝ) - 1)⁻¹ := by rw [Finset.sum_mul]
    _ = (∑ t ∈ (nbAll (G := G) k).filter (fun t => t.2.1 = u ∧ t.2.2.penultimate ≠ v),
          nbWeight t.2) * ((G.degree u : ℝ) - 1)⁻¹ := by rw [sum_R_eq_sum k u v]
    _ = (∑ w ∈ G.neighborFinset u \ {v}, nbLastWeight (G := G) k w u) * ((G.degree u : ℝ) - 1)⁻¹
      := by
        rw [sum_R_eq_sum_lastWeight huv hk]

/-! ### W3 — the last-edge marginal `xP = x` -/

/-- **W3 (AHL's `xP = x`).**  Under `δ ≥ 2`, for every `k ≥ 1` and every directed edge `(u, v)` the
total weight of the length-`k` non-backtracking walks whose last directed edge is `(u, v)` is
exactly
`1`.  The weighted last-edge marginal is *stationary*.  Proof by induction on `k`: the base case is
the single edge `u → v` (weight `1`); the step uses `nbLastWeight_succ_eq`, the induction hypothesis
over the `deg u − 1` predecessors, and `mul_inv_cancel₀` with `deg u − 1 ≠ 0`. -/
theorem nbLastWeight_eq_one (hδ2 : ∀ w, 2 ≤ G.degree w) {k : ℕ} (hk : 1 ≤ k) :
    ∀ {u v : V}, G.Adj u v → nbLastWeight (G := G) k u v = 1 := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro u v huv
    rw [nbLastWeight_eq_sum]
    have h0 : ∀ x ∈ (univ : Finset V), x ≠ u →
        (∑ s ∈ (nbWalksFrom G x 1).filter (fun s => s.1 = v ∧ s.2.penultimate = u), nbWeight s)
          = 0 := by
      intro x _ hxu
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [Finset.mem_filter, mem_nbWalksFrom] at hs
      obtain ⟨⟨hslen, _⟩, _, hpen⟩ := hs
      exact absurd ((penultimate_of_length_one hslen).symm.trans hpen) hxu
    rw [Finset.sum_eq_single u h0 (fun h => absurd (mem_univ u) h)]
    rw [show (nbWalksFrom G u 1).filter (fun s => s.1 = v ∧ s.2.penultimate = u)
        = {⟨v, Walk.cons huv Walk.nil⟩} from ?_]
    · rw [Finset.sum_singleton]
      exact nbWeight_one (by rw [Walk.length_cons, Walk.length_nil])
    · rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_filter, mem_nbWalksFrom]
        refine ⟨⟨?_, ?_⟩, rfl, ?_⟩
        · rw [Walk.length_cons, Walk.length_nil]
        · exact isNonBacktracking_cons_nil huv
        · exact penultimate_of_length_one (by rw [Walk.length_cons, Walk.length_nil])
      · intro b hb
        obtain ⟨w, p⟩ := b
        rw [Finset.mem_filter, mem_nbWalksFrom] at hb
        obtain ⟨⟨hlen, _⟩, hend, _⟩ := hb
        subst hend
        cases p with
        | nil => simp at hlen
        | cons h q =>
          rw [Walk.length_cons] at hlen
          cases q with
          | nil => rfl
          | cons h' q' => rw [Walk.length_cons] at hlen; omega
  | succ k hk ih =>
    intro u v huv
    rw [nbLastWeight_succ_eq huv hk]
    have hone : ∀ w ∈ G.neighborFinset u \ {v}, nbLastWeight (G := G) k w u = 1 := by
      intro w hw
      rw [Finset.mem_sdiff, mem_neighborFinset] at hw
      exact ih hw.1.symm
    have hsub : ({v} : Finset V) ⊆ G.neighborFinset u := by
      rw [Finset.singleton_subset_iff, mem_neighborFinset]; exact huv
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_sdiff_of_subset hsub, card_neighborFinset_eq_degree, Finset.card_singleton]
    have hd : (1 : ℕ) ≤ G.degree u := by have := hδ2 u; omega
    rw [Nat.cast_sub hd, Nat.cast_one]
    have hne : (G.degree u : ℝ) - 1 ≠ 0 := by
      have h2 : (2 : ℝ) ≤ (G.degree u : ℝ) := by exact_mod_cast hδ2 u
      exact sub_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le one_lt_two h2))
    exact mul_inv_cancel₀ hne

/-! ### W4 — the end marginal -/

/-- **The end marginal is the sum of the last-edge marginals over the neighbours.**  A fiberwise
partition of the length-`k` walks ending at `v` by their penultimate vertex (which is always a
neighbour of `v`). -/
theorem nbEndWeight_eq_sum_lastWeight {v : V} {k : ℕ} (hk : 1 ≤ k) :
    nbEndWeight (G := G) k v = ∑ u ∈ G.neighborFinset v, nbLastWeight (G := G) k u v := by
  have hmaps : ∀ t ∈ (nbAll (G := G) k).filter (fun t => t.2.1 = v),
      t.2.2.penultimate ∈ G.neighborFinset v := by
    rintro ⟨tx, tv, tp⟩ ht
    rw [Finset.mem_filter, mem_nbAll] at ht
    obtain ⟨⟨hlen, _⟩, hend⟩ := ht
    subst hend
    have hnn : ¬ tp.Nil := Walk.not_nil_iff_lt_length.mpr (by
      have : tp.length = k := hlen; omega)
    rw [mem_neighborFinset]
    exact (tp.adj_penultimate hnn).symm
  rw [nbEndWeight, ← Finset.sum_fiberwise_of_maps_to hmaps (fun t => nbWeight t.2)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [nbLastWeight, Finset.filter_filter]

/-- **W4.**  Under `δ ≥ 2`, for `k ≥ 1` the total weight of the length-`k` non-backtracking walks
ending at `v` is exactly `deg v` — the exact degree-bias (unlike the raw end-count, which obeys no
usable law).  Each summand of the neighbour partition is `1` by W3, so the sum is `|N(v)| = deg
v`. -/
theorem nbEndWeight_eq_degree (hδ2 : ∀ w, 2 ≤ G.degree w) {v : V} {k : ℕ} (hk : 1 ≤ k) :
    nbEndWeight (G := G) k v = (G.degree v : ℝ) := by
  rw [nbEndWeight_eq_sum_lastWeight hk]
  have hone : ∀ u ∈ G.neighborFinset v, nbLastWeight (G := G) k u v = 1 := by
    intro u hu
    rw [mem_neighborFinset] at hu
    exact nbLastWeight_eq_one hδ2 hk hu.symm
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one,
    card_neighborFinset_eq_degree]

/-! ### W5 — the total weight -/

/-- **W5.**  Under `δ ≥ 2`, for `k ≥ 1` the total weight of all length-`k` non-backtracking walks is
exactly `D = ∑ v, deg v` — the constant the weighted AM–GM (W7) normalizes against (its exponent
collapse).  Sum the end marginals (W4) over all endpoints. -/
theorem nbWeightTotal_eq (hδ2 : ∀ w, 2 ≤ G.degree w) {k : ℕ} (hk : 1 ≤ k) :
    nbWeightTotal (G := G) k = ∑ v : V, (G.degree v : ℝ) := by
  have hmaps : ∀ t ∈ nbAll (G := G) k, t.2.1 ∈ (univ : Finset V) := fun _ _ => mem_univ _
  rw [nbWeightTotal, ← Finset.sum_fiberwise_of_maps_to hmaps (fun t => nbWeight t.2)]
  refine Finset.sum_congr rfl fun v _ => ?_
  change nbEndWeight (G := G) k v = (G.degree v : ℝ)
  exact nbEndWeight_eq_degree hδ2 hk

end ACMax
