/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — deleting the exceptional edges of a near-regular subgraph

`Nibble.AX1.tripleGraph_near_regular` (`Nibble.CoreGapTripleDegrees`) bounds the triangle degrees of
the tripartite graph of a cluster triple *outside an exceptional set of edges*.  The near-regularity
required by `Nibble.AX1.HasNearRegularFamily` has no exceptions on the **upper** bound, so those
edges must be deleted; deleting them lowers the triangle degrees of the edges that remain, and this
file bounds that loss.

* `Nibble.AX1.prune` — the subgraph obtained by deleting a set of edges, and
`Nibble.AX1.deletedDegree`
  — the number of deleted edges at a vertex.
* `Nibble.AX1.edgeTriangleDegree_prune_ge` — a triangle of `T` through a surviving edge `{x, y}`
  survives unless one of its two other edges was deleted, so the triangle degree drops by at most
  `deletedDegree x + deletedDegree y`.
* `Nibble.AX1.sum_deletedDegree_le` — the handshake bound `∑ᵥ deletedDegree v ≤ 2|Bad|`.
* `Nibble.AX1.card_edges_heavy_deleted_le` — hence at most `(2|Bad|/t)·|V|` edges have an endpoint
  at which more than `t` edges were deleted.
* `Nibble.AX1.prune_near_regular` — **the package**: after pruning, *every* surviving edge has
  triangle degree at most `(1+μ)d`, and all but `(2|Bad|/t)·|V|` of them have triangle degree at
  least `(1−μ)d − 2t`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapTripleDegrees

/-! # CoreGapPrune -/

public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Pruning a set of edges -/

/-- The subgraph of `T` obtained by deleting the edges lying in `Bad`. -/
noncomputable def prune (T : SimpleGraph V) (Bad : Finset (Finset V)) : SimpleGraph V :=
  edgeSelect T (fun e => e ∉ Bad)

noncomputable instance instDecidableRelPrune (T : SimpleGraph V) (Bad : Finset (Finset V)) :
    DecidableRel (prune T Bad).Adj := fun _ _ => Classical.dec _

omit [Fintype V] in
theorem prune_le (T : SimpleGraph V) (Bad : Finset (Finset V)) : prune T Bad ≤ T :=
  edgeSelect_le _ _

omit [Fintype V] in
theorem prune_adj (T : SimpleGraph V) (Bad : Finset (Finset V)) (x y : V) :
    (prune T Bad).Adj x y ↔ T.Adj x y ∧ ({x, y} : Finset V) ∉ Bad :=
  edgeSelect_adj _ _ _ _

/-- The number of deleted edges at a vertex. -/
def deletedDegree (T : SimpleGraph V) [DecidableRel T.Adj] (Bad : Finset (Finset V)) (v : V) : ℕ :=
  #{z ∈ (univ : Finset V) | T.Adj v z ∧ ({v, z} : Finset V) ∈ Bad}

/-! ### The triangle degree lost by pruning -/

/-- **Pruning costs a surviving edge at most the deleted degrees of its endpoints.** -/
theorem edgeTriangleDegree_prune_ge (T : SimpleGraph V) [DecidableRel T.Adj]
    (Bad : Finset (Finset V)) {x y : V} (hadj : (prune T Bad).Adj x y) :
    edgeTriangleDegree T {x, y}
      ≤ edgeTriangleDegree (prune T Bad) {x, y} + deletedDegree T Bad x +
          deletedDegree T Bad y := by
  classical
  have hTadj : T.Adj x y := (prune_le T Bad) hadj
  rw [edgeTriangleDegree_pair T hTadj, edgeTriangleDegree_pair _ hadj, deletedDegree,
    deletedDegree]
  have hsub : {z ∈ (univ : Finset V) | T.Adj x z ∧ T.Adj y z}
      ⊆ {z ∈ (univ : Finset V) | (prune T Bad).Adj x z ∧ (prune T Bad).Adj y z}
        ∪ ({z ∈ (univ : Finset V) | T.Adj x z ∧ ({x, z} : Finset V) ∈ Bad}
          ∪ {z ∈ (univ : Finset V) | T.Adj y z ∧ ({y, z} : Finset V) ∈ Bad}) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨hxz, hyz⟩ := hz
    by_cases hpx : ({x, z} : Finset V) ∈ Bad
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hxz, hpx⟩))
    · by_cases hpy : ({y, z} : Finset V) ∈ Bad
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hyz, hpy⟩))
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ z,
          (prune_adj T Bad x z).mpr ⟨hxz, hpx⟩, (prune_adj T Bad y z).mpr ⟨hyz, hpy⟩⟩)
  calc #{z ∈ (univ : Finset V) | T.Adj x z ∧ T.Adj y z}
      ≤ #({z ∈ (univ : Finset V) | (prune T Bad).Adj x z ∧ (prune T Bad).Adj y z}
          ∪ ({z ∈ (univ : Finset V) | T.Adj x z ∧ ({x, z} : Finset V) ∈ Bad}
            ∪ {z ∈ (univ : Finset V) | T.Adj y z ∧ ({y, z} : Finset V) ∈ Bad})) :=
        Finset.card_le_card hsub
    _ ≤ #{z ∈ (univ : Finset V) | (prune T Bad).Adj x z ∧ (prune T Bad).Adj y z}
          + (#{z ∈ (univ : Finset V) | T.Adj x z ∧ ({x, z} : Finset V) ∈ Bad}
            + #{z ∈ (univ : Finset V) | T.Adj y z ∧ ({y, z} : Finset V) ∈ Bad}) := by
        refine le_trans (Finset.card_union_le _ _) ?_
        exact Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ = _ := by ring

/-! ### The handshake bound -/

/-- **The total deleted degree is at most twice the number of deleted edges.** -/
theorem sum_deletedDegree_le (T : SimpleGraph V) [DecidableRel T.Adj] (Bad : Finset (Finset V)) :
    ∑ v : V, deletedDegree T Bad v ≤ 2 * #Bad := by
  classical
  set Q : V × V → Prop := fun p => T.Adj p.1 p.2 ∧ ({p.1, p.2} : Finset V) ∈ Bad with hQ
  set S : Finset (V × V) := {p ∈ (univ : Finset V) ×ˢ (univ : Finset V) | Q p} with hS
  have hsum : ∑ v : V, deletedDegree T Bad v = #S := by
    rw [hS, card_filter_product]
    exact Finset.sum_congr rfl fun v _ => by simp [deletedDegree, hQ]
  have hfib : ∀ e ∈ S.image (fun p => ({p.1, p.2} : Finset V)),
      #{p ∈ S | ({p.1, p.2} : Finset V) = e} ≤ 2 := by
    intro e he
    obtain ⟨p, hpS, hpe⟩ := Finset.mem_image.mp he
    have hpQ : Q p := (Finset.mem_filter.mp hpS).2
    have hne : p.1 ≠ p.2 := hpQ.1.ne
    have hsub : {q ∈ S | ({q.1, q.2} : Finset V) = e} ⊆ {(p.1, p.2), (p.2, p.1)} := by
      intro q hq
      rw [Finset.mem_filter] at hq
      have hqe : ({q.1, q.2} : Finset V) = ({p.1, p.2} : Finset V) := by rw [hq.2, hpe]
      have hqne : q.1 ≠ q.2 := ((Finset.mem_filter.mp hq.1).2).1.ne
      have h1 : q.1 ∈ ({p.1, p.2} : Finset V) := by rw [← hqe]; simp
      have h2 : q.2 ∈ ({p.1, p.2} : Finset V) := by rw [← hqe]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hqne
      · exact Or.inl (Prod.ext h1 h2)
      · exact Or.inr (Prod.ext h1 h2)
      · exact absurd (h1.trans h2.symm) hqne
    refine le_trans (Finset.card_le_card hsub) ?_
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  have himg : S.image (fun p => ({p.1, p.2} : Finset V)) ⊆ Bad := by
    intro e he
    obtain ⟨p, hpS, hpe⟩ := Finset.mem_image.mp he
    rw [← hpe]
    exact ((Finset.mem_filter.mp hpS).2).2
  calc ∑ v : V, deletedDegree T Bad v = #S := hsum
    _ ≤ 2 * #(S.image (fun p => ({p.1, p.2} : Finset V))) := Finset.card_le_mul_card_image S 2 hfib
    _ ≤ 2 * #Bad := Nat.mul_le_mul_left 2 (Finset.card_le_card himg)

/-- **Markov's inequality for the deleted degrees.** -/
theorem card_vertices_deletedDegree_gt (T : SimpleGraph V) [DecidableRel T.Adj]
    (Bad : Finset (Finset V)) {t : ℝ} :
    ((#{v ∈ (univ : Finset V) | t < (deletedDegree T Bad v : ℝ)} : ℕ) : ℝ) * t
      ≤ 2 * (#Bad : ℝ) := by
  classical
  set S : Finset V := {v ∈ (univ : Finset V) | t < (deletedDegree T Bad v : ℝ)} with hS
  have h1 : (#S : ℝ) * t ≤ ∑ v ∈ S, (deletedDegree T Bad v : ℝ) := by
    have : ∑ _v ∈ S, t ≤ ∑ v ∈ S, (deletedDegree T Bad v : ℝ) := by
      refine Finset.sum_le_sum fun v hv => ?_
      rw [hS, Finset.mem_filter] at hv
      exact le_of_lt hv.2
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have h2 : ∑ v ∈ S, (deletedDegree T Bad v : ℝ) ≤ ∑ v : V, (deletedDegree T Bad v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (by intro i _ _; positivity)
  have h3 : ∑ v : V, (deletedDegree T Bad v : ℝ) ≤ 2 * (#Bad : ℝ) := by
    have := sum_deletedDegree_le T Bad
    have hcast : ((∑ v : V, deletedDegree T Bad v : ℕ) : ℝ) ≤ ((2 * #Bad : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at hcast
    exact hcast
  linarith

/-- **Few edges have an endpoint at which many edges were deleted.** -/
theorem card_edges_heavy_deleted_le (T : SimpleGraph V) [DecidableRel T.Adj]
    (Bad : Finset (Finset V)) {t : ℝ} (ht : 0 < t) :
    ((#{e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)} : ℕ) : ℝ)
      ≤ (2 * (#Bad : ℝ) / t) * (Fintype.card V : ℝ) := by
  classical
  set S : Finset V := {v ∈ (univ : Finset V) | t < (deletedDegree T Bad v : ℝ)} with hS
  have hsub : {e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)}
      ⊆ S.biUnion (fun v => (univ : Finset V).image (fun z => ({v, z} : Finset V))) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨hecl, hbad⟩ := he
    push Not at hbad
    obtain ⟨v, hve, hvt⟩ := hbad
    have hvS : v ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ v, hvt⟩
    have hcard : #e = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp hecl).card_eq
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    simp only [Finset.mem_insert, Finset.mem_singleton] at hve
    refine Finset.mem_biUnion.mpr ⟨v, hvS, ?_⟩
    rcases hve with rfl | rfl
    · exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩
    · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, Finset.pair_comm v a⟩
  have hcard1 : #{e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)}
      ≤ ∑ _v ∈ S, Fintype.card V := by
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    refine Finset.sum_le_sum fun v _ => ?_
    exact le_trans Finset.card_image_le (by simp)
  have hcard2 : ((#{e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)} : ℕ) : ℝ)
      ≤ (#S : ℝ) * (Fintype.card V : ℝ) := by
    have := hcard1
    rw [Finset.sum_const, smul_eq_mul] at this
    exact_mod_cast this
  have hmark := card_vertices_deletedDegree_gt T Bad (t := t)
  have hSt : (#S : ℝ) ≤ 2 * (#Bad : ℝ) / t := by
    rw [le_div_iff₀ ht]
    exact hmark
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := by positivity
  calc ((#{e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)} : ℕ) : ℝ)
      ≤ (#S : ℝ) * (Fintype.card V : ℝ) := hcard2
    _ ≤ (2 * (#Bad : ℝ) / t) * (Fintype.card V : ℝ) := by
        exact mul_le_mul_of_nonneg_right hSt hn

/-! ### The pruned graph is near-regular with no exceptions above -/

/-- Every edge of the pruned graph is an edge of `T` outside `Bad`. -/
theorem mem_cliqueFinset_two_prune (T : SimpleGraph V) [DecidableRel T.Adj]
    (Bad : Finset (Finset V)) {e : Finset V} (he : e ∈ (prune T Bad).cliqueFinset 2) :
    e ∈ T.cliqueFinset 2 ∧ e ∉ Bad := by
  classical
  have hcard : #e = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp he).card_eq
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
  have hadj : (prune T Bad).Adj x y := (pair_mem_cliqueFinset_two _ hxy).mp he
  rw [prune_adj] at hadj
  exact ⟨(pair_mem_cliqueFinset_two T hxy).mpr hadj.1, hadj.2⟩

/-- **The pruned graph.**  If the triangle degrees of `T` are between `(1−μ)d` and `(1+μ)d` outside
`Bad`, then after deleting `Bad` *every* surviving edge has triangle degree at most `(1+μ)d`, and
all but at most `(2|Bad|/t)|V|` of them have triangle degree at least `(1−μ)d − 2t`. -/
theorem prune_near_regular (T : SimpleGraph V) [DecidableRel T.Adj] (Bad : Finset (Finset V))
    {μ d t : ℝ} (ht : 0 < t)
    (hhi : ∀ e ∈ T.cliqueFinset 2, e ∉ Bad → (edgeTriangleDegree T e : ℝ) ≤ (1 + μ) * d)
    (hlo : ∀ e ∈ T.cliqueFinset 2, e ∉ Bad → (1 - μ) * d ≤ (edgeTriangleDegree T e : ℝ)) :
    (∀ e ∈ (prune T Bad).cliqueFinset 2,
        (edgeTriangleDegree (prune T Bad) e : ℝ) ≤ (1 + μ) * d) ∧
      ∃ Exc : Finset (Finset V), ((#Exc : ℕ) : ℝ) ≤ (2 * (#Bad : ℝ) / t) * (Fintype.card V : ℝ) ∧
        ∀ e ∈ (prune T Bad).cliqueFinset 2, e ∉ Exc →
          (1 - μ) * d - 2 * t ≤ (edgeTriangleDegree (prune T Bad) e : ℝ) := by
  classical
  refine ⟨?_, ?_⟩
  · intro e he
    obtain ⟨heT, heB⟩ := mem_cliqueFinset_two_prune T Bad he
    have hmono : edgeTriangleDegree (prune T Bad) e ≤ edgeTriangleDegree T e :=
      edgeTriangleDegree_mono T (prune T Bad) (prune_le T Bad) e
    have : ((edgeTriangleDegree (prune T Bad) e : ℕ) : ℝ) ≤ ((edgeTriangleDegree T e : ℕ) : ℝ) := by
      exact_mod_cast hmono
    exact le_trans this (hhi e heT heB)
  · refine ⟨{e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)},
      card_edges_heavy_deleted_le T Bad ht, ?_⟩
    intro e he hexc
    obtain ⟨heT, heB⟩ := mem_cliqueFinset_two_prune T Bad he
    have hdeg : ∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t := by
      by_contra hc
      exact hexc (Finset.mem_filter.mpr ⟨heT, hc⟩)
    have hcard : #e = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp he).card_eq
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    have hadj : (prune T Bad).Adj x y := (pair_mem_cliqueFinset_two _ hxy).mp he
    have hdrop := edgeTriangleDegree_prune_ge T Bad hadj
    have hdrop' : ((edgeTriangleDegree T {x, y} : ℕ) : ℝ)
        ≤ ((edgeTriangleDegree (prune T Bad) {x, y} : ℕ) : ℝ)
          + ((deletedDegree T Bad x : ℕ) : ℝ) + ((deletedDegree T Bad y : ℕ) : ℝ) := by
      exact_mod_cast hdrop
    have hx : ((deletedDegree T Bad x : ℕ) : ℝ) ≤ t := hdeg x (by simp)
    have hy : ((deletedDegree T Bad y : ℕ) : ℝ) ≤ t := hdeg y (by simp)
    have hlo' := hlo {x, y} heT heB
    linarith

/-- Pruning destroys at most `|Bad|` edges. -/
theorem card_cliqueFinset_two_prune_ge (T : SimpleGraph V) [DecidableRel T.Adj]
    (Bad : Finset (Finset V)) :
    ((#(T.cliqueFinset 2) : ℕ) : ℝ) - ((#Bad : ℕ) : ℝ)
      ≤ ((#((prune T Bad).cliqueFinset 2) : ℕ) : ℝ) := by
  classical
  have hsub : T.cliqueFinset 2 \ Bad ⊆ (prune T Bad).cliqueFinset 2 := by
    intro e he
    rw [Finset.mem_sdiff] at he
    obtain ⟨heT, heB⟩ := he
    have hcard : #e = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp heT).card_eq
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    exact (pair_mem_cliqueFinset_two _ hxy).mpr
      ((prune_adj T Bad x y).mpr ⟨(pair_mem_cliqueFinset_two T hxy).mp heT, heB⟩)
  have h1 : #(T.cliqueFinset 2) - #Bad ≤ #(T.cliqueFinset 2 \ Bad) := by
    have := Finset.card_sdiff_add_card_eq_card (s := T.cliqueFinset 2 ∩ Bad)
      (t := T.cliqueFinset 2) Finset.inter_subset_left
    have h2 : #(T.cliqueFinset 2 \ Bad) = #(T.cliqueFinset 2) - #(T.cliqueFinset 2 ∩ Bad) := by
      rw [Finset.card_sdiff, Finset.inter_comm]
    have h3 : #(T.cliqueFinset 2 ∩ Bad) ≤ #Bad := Finset.card_le_card Finset.inter_subset_right
    omega
  have h4 : #(T.cliqueFinset 2 \ Bad) ≤ #((prune T Bad).cliqueFinset 2) :=
    Finset.card_le_card hsub
  have h5 : #(T.cliqueFinset 2) - #Bad ≤ #((prune T Bad).cliqueFinset 2) := le_trans h1 h4
  have h6 : ((#(T.cliqueFinset 2) : ℕ) : ℝ) - ((#Bad : ℕ) : ℝ)
      ≤ ((#(T.cliqueFinset 2) - #Bad : ℕ) : ℝ) := by
    rcases le_or_gt (#(T.cliqueFinset 2)) (#Bad) with h | h
    · have : ((#(T.cliqueFinset 2) : ℕ) : ℝ) ≤ ((#Bad : ℕ) : ℝ) := by exact_mod_cast h
      have hz : (#(T.cliqueFinset 2) - #Bad : ℕ) = 0 := by omega
      rw [hz]
      simp only [Nat.cast_zero]
      linarith
    · have : ((#(T.cliqueFinset 2) - #Bad : ℕ) : ℝ)
          = ((#(T.cliqueFinset 2) : ℕ) : ℝ) - ((#Bad : ℕ) : ℝ) := by
        have hle : #Bad ≤ #(T.cliqueFinset 2) := le_of_lt h
        push_cast [hle]
        ring
      linarith
  refine le_trans h6 ?_
  exact_mod_cast h5

/-! ### A near-regular member from a single cluster triple -/

/-- **A near-regular member of the family from one cluster triple.**  Under the hypotheses of
`Nibble.AX1.tripleGraph_near_regular` (three pairwise `ε`-uniform pairs of density at least `2ε`
whose three triangle-degree scales are equalised to `d` within `μ`), deleting the `≤ 4ε(|U||W| +
|U||X| + |W||X|)` exceptional edges produces a subgraph `H ≤ G` in which

* *every* edge has triangle degree at most `(1+μ)d`;
* all but `(2|Bad|/t)|V|` edges have triangle degree at least `(1−μ)d − 2t`;
* at most `|Bad|` edges of the tripartite graph of the triple were lost.

This is exactly one member of the family `Nibble.AX1.HasNearRegularFamily` asks for; what the
residual still needs is the *global* assembly of these members — see `RESIDUAL.md`. -/
theorem uniform_triple_member (G : SimpleGraph V) [DecidableRel G.Adj] {U W X : Finset V}
    (hUW : Disjoint U W) (hUX : Disjoint U X) (hWX : Disjoint W X) {ε μ d t : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t)
    (hUWu : G.IsUniform ε U W) (hUXu : G.IsUniform ε U X) (hWXu : G.IsUniform ε W X)
    (hdUW : 2 * ε ≤ (G.edgeDensity U W : ℝ)) (hdUX : 2 * ε ≤ (G.edgeDensity U X : ℝ))
    (hdWX : 2 * ε ≤ (G.edgeDensity W X : ℝ))
    (hXlo : (1 - μ) * d ≤ ((G.edgeDensity U X : ℝ) - ε) * ((G.edgeDensity W X : ℝ) - 2 * ε)
      * (#X : ℝ))
    (hXhi : ((G.edgeDensity U X : ℝ) + ε) * ((G.edgeDensity W X : ℝ) + 2 * ε) * (#X : ℝ)
      ≤ (1 + μ) * d)
    (hWlo : (1 - μ) * d ≤ ((G.edgeDensity U W : ℝ) - ε) * ((G.edgeDensity W X : ℝ) - 2 * ε)
      * (#W : ℝ))
    (hWhi : ((G.edgeDensity U W : ℝ) + ε) * ((G.edgeDensity W X : ℝ) + 2 * ε) * (#W : ℝ)
      ≤ (1 + μ) * d)
    (hUlo : (1 - μ) * d ≤ ((G.edgeDensity U W : ℝ) - ε) * ((G.edgeDensity U X : ℝ) - 2 * ε)
      * (#U : ℝ))
    (hUhi : ((G.edgeDensity U W : ℝ) + ε) * ((G.edgeDensity U X : ℝ) + 2 * ε) * (#U : ℝ)
      ≤ (1 + μ) * d) :
    ∃ Bad : Finset (Finset V),
      ((#Bad : ℕ) : ℝ) ≤ 4 * ε * ((#U : ℝ) * (#W : ℝ) + (#U : ℝ) * (#X : ℝ)
        + (#W : ℝ) * (#X : ℝ)) ∧
      prune (tripleGraph G U W X) Bad ≤ G ∧
      (∀ e ∈ (prune (tripleGraph G U W X) Bad).cliqueFinset 2,
        (edgeTriangleDegree (prune (tripleGraph G U W X) Bad) e : ℝ) ≤ (1 + μ) * d) ∧
      (∃ Exc : Finset (Finset V),
        ((#Exc : ℕ) : ℝ) ≤ (2 * ((#Bad : ℕ) : ℝ) / t) * (Fintype.card V : ℝ) ∧
        ∀ e ∈ (prune (tripleGraph G U W X) Bad).cliqueFinset 2, e ∉ Exc →
          (1 - μ) * d - 2 * t
            ≤ (edgeTriangleDegree (prune (tripleGraph G U W X) Bad) e : ℝ)) ∧
      ((#((tripleGraph G U W X).cliqueFinset 2) : ℕ) : ℝ) - ((#Bad : ℕ) : ℝ)
        ≤ ((#((prune (tripleGraph G U W X) Bad).cliqueFinset 2) : ℕ) : ℝ) := by
  classical
  obtain ⟨Bad, hBadcard, hBad⟩ := tripleGraph_near_regular G hUW hUX hWX hε hε1 hUWu hUXu hWXu
    hdUW hdUX hdWX hXlo hXhi hWlo hWhi hUlo hUhi
  refine ⟨Bad, hBadcard, le_trans (prune_le _ _) (tripleGraph_le G U W X), ?_, ?_, ?_⟩
  · exact (prune_near_regular (tripleGraph G U W X) Bad ht
      (fun e he hnb => (hBad e he hnb).2) (fun e he hnb => (hBad e he hnb).1)).1
  · exact (prune_near_regular (tripleGraph G U W X) Bad ht
      (fun e he hnb => (hBad e he hnb).2) (fun e he hnb => (hBad e he hnb).1)).2
  · exact card_cliqueFinset_two_prune_ge (tripleGraph G U W X) Bad

end Nibble.AX1
