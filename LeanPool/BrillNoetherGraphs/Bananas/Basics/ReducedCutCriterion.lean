/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Basics.BananaGeometry

/-!
# A cut criterion for reduced divisors

The paper's `SameStrand` argument is a reduced-divisor argument.  This lemma
packages the only finite-set calculation it needs: a strict total chip versus
boundary inequality produces the pointwise witness required by `qReduced`.
-/

@[expose] public section

namespace Bananas

open Utilities

open Utilities Finset

/-- A `q`-effective divisor is `q`-reduced if every nonempty set avoiding
`q` carries strictly fewer total chips than its outgoing edge multiplicity. -/
theorem q_reduced_of_sum_lt_cut
    (G : CFGraph) (q : G.V) (D : CFDiv G)
    (hEff : qEffective q D)
    (hCut : ∀ S : Finset G.V, S ⊆ Finset.univ.filter (· ≠ q) → S.Nonempty →
      (∑ v ∈ S, D v) <
        ∑ v ∈ S, ∑ w ∈ (Finset.univ.filter fun x => x ∉ S),
          (numEdges G v w : ℤ)) :
    qReduced G q D := by
  refine ⟨hEff, ?_⟩
  intro S hqS hSNonempty hLegal
  have hS : S ⊆ Finset.univ.filter (· ≠ q) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hvq
    exact hqS (hvq ▸ hv)
  have hPointwise : ∀ v ∈ S,
      ∑ w ∈ (Finset.univ.filter fun x => x ∉ S), (numEdges G v w : ℤ) ≤ D v := by
    intro v hv
    rw [← outdeg_S_eq_sum_filter]
    exact hLegal v hv
  have hSum :
      (∑ v ∈ S, ∑ w ∈ (Finset.univ.filter fun x => x ∉ S),
        (numEdges G v w : ℤ)) ≤ ∑ v ∈ S, D v := by
    exact Finset.sum_le_sum fun v hv => hPointwise v hv
  have hStrict := hCut S hS hSNonempty
  omega

/-- A two-chip divisor with one chip of debt at `q` is reduced as soon as all
cuts have size at least two and the only cuts which contain both chips have
size at least three.  This is the exact cut-theoretic form of the remaining
case split in the paper's `SameStrand` lemma. -/
theorem q_reduced_two_chip_sub_of_cut_bounds
    (G : CFGraph) (q x y : G.V) (hqx : q ≠ x) (hqy : q ≠ y)
    (hTwo : ∀ S : Finset G.V, S ⊆ Finset.univ.filter (· ≠ q) → S.Nonempty →
      2 ≤ ∑ v ∈ S, ∑ w ∈ (Finset.univ.filter fun z => z ∉ S),
        (numEdges G v w : ℤ))
    (hThree : ∀ S : Finset G.V, S ⊆ Finset.univ.filter (· ≠ q) →
      x ∈ S → y ∈ S →
      3 ≤ ∑ v ∈ S, ∑ w ∈ (Finset.univ.filter fun z => z ∉ S),
        (numEdges G v w : ℤ)) :
    qReduced G q (oneChip x + oneChip y - oneChip q) := by
  apply q_reduced_of_sum_lt_cut G q _
  · intro v hv
    by_cases hvx : v = x <;> by_cases hvy : v = y
    · subst v
      subst y
      simp [hqx]
    · subst v
      simp [hqx, hvy]
    · subst v
      simp [hqy, hvx]
    · simp [oneChip, hv, hvx, hvy]
  · intro S hS hSNonempty
    have hqS : q ∉ S := by
      intro hq
      have := hS hq
      simp at this
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · have hBound := hThree S hS hx hy
      simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, oneChip,
        hx, hy, hqS]
      omega
    · have hBound := hTwo S hS hSNonempty
      simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, oneChip,
        hx, hy, hqS]
      omega
    · have hBound := hTwo S hS hSNonempty
      simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, oneChip,
        hx, hy, hqS]
      omega
    · have hBound := hTwo S hS hSNonempty
      simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, oneChip,
        hx, hy, hqS]
      omega

/-- The uniform part of the preceding cut hypothesis is automatic on a
bridgeless graph.  This wrapper is useful for banana graphs, where
`TwoEdgeCutCondition` is inherited from their parallel-edge core and only the
exceptional cuts containing both chips require further geometric analysis. -/
theorem q_reduced_two_chip_sub_of_twoEdgeCutCondition
    (G : CFGraph) (q x y : G.V) (hqx : q ≠ x) (hqy : q ≠ y)
    (hTwoEdge : TwoEdgeCutCondition G)
    (hThree : ∀ S : Finset G.V, S ⊆ Finset.univ.filter (· ≠ q) →
      x ∈ S → y ∈ S →
      3 ≤ ∑ v ∈ S, ∑ w ∈ (Finset.univ.filter fun z => z ∉ S),
        (numEdges G v w : ℤ)) :
    qReduced G q (oneChip x + oneChip y - oneChip q) := by
  apply q_reduced_two_chip_sub_of_cut_bounds G q x y hqx hqy
  · intro S hS hNonempty
    have hProper : S ≠ Finset.univ := by
      intro hUniv
      have hq : q ∈ S := by rw [hUniv]; simp
      have := hS hq
      simp at this
    have hCut := hTwoEdge S hNonempty hProper
    unfold cutMultiplicity at hCut
    simp_rw [outdeg_S_eq_sum_filter] at hCut
    exact hCut
  · exact hThree

end Bananas
