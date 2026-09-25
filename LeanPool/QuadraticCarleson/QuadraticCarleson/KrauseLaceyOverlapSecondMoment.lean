/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyActiveExponentialPruning

/-!
# The second moment of a finite Carleson counting function

Laminarity orders every intersecting pair. After integrating, each row
of the ordered-pair sum is exactly a descendant length sum. This proves
the second-moment bound required for the removed operator contribution.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyGenerationLayers

attribute [local instance] Classical.propDecidable

theorem overlapCount_sq_le_two_sum_descendant_counts
    (A : Finset RealInterval)
    (hlam : Set.Pairwise (↑A : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (x : ℝ) :
    (overlapCount A x : ℝ≥0∞) ^ 2 ≤
      2 * ∑ I ∈ A, (overlapCount (A.filter fun J ↦ J.carrier ⊆ I.carrier) x : ℝ≥0∞) := by
  let v := fun I : RealInterval ↦ I.carrier.indicator (fun _ ↦ (1 : ℝ≥0∞)) x
  have hpair (I : RealInterval) (hI : I ∈ A) (J : RealInterval) (hJ : J ∈ A) :
      v I * v J ≤ (if J.carrier ⊆ I.carrier then v J else 0) +
        (if I.carrier ⊆ J.carrier then v I else 0) := by
    by_cases hxI : x ∈ I.carrier
    · by_cases hxJ : x ∈ J.carrier
      · have hrel : J.carrier ⊆ I.carrier ∨ I.carrier ⊆ J.carrier := by
          by_cases he : I = J
          · exact Or.inl (he ▸ Subset.rfl)
          rcases hlam hI hJ he with h | h | hd
          · exact Or.inr h
          · exact Or.inl h
          · exact (Set.disjoint_left.mp hd hxI hxJ).elim
        rcases hrel with h | h
        · simp only [v, Set.indicator_of_mem hxI, Set.indicator_of_mem hxJ, one_mul,
            ite_eq_left h]
          exact le_self_add
        · simp only [v, Set.indicator_of_mem hxI, Set.indicator_of_mem hxJ, one_mul,
            ite_eq_left h]
          exact le_add_self
      · simp only [v, Set.indicator_of_notMem hxJ, mul_zero]
        exact zero_le
    · simp only [v, Set.indicator_of_notMem hxI, zero_mul]
      exact zero_le
  have hswap : (∑ I ∈ A, ∑ J ∈ A, if I.carrier ⊆ J.carrier then v I else 0) =
      ∑ I ∈ A, ∑ J ∈ A, if J.carrier ⊆ I.carrier then v J else 0 := Finset.sum_comm
  calc
    (overlapCount A x : ℝ≥0∞) ^ 2 = ∑ I ∈ A, ∑ J ∈ A, v I * v J := by
      rw [pow_two, overlapCount_cast_eq_sum_indicator, Finset.sum_mul_sum]
    _ ≤ ∑ I ∈ A, ∑ J ∈ A, ((if J.carrier ⊆ I.carrier then v J else 0) +
        (if I.carrier ⊆ J.carrier then v I else 0)) :=
      Finset.sum_le_sum fun I hI ↦ Finset.sum_le_sum fun J hJ ↦ hpair I hI J hJ
    _ = 2 * ∑ I ∈ A, ∑ J ∈ A, if J.carrier ⊆ I.carrier then v J else 0 := by
      simp_rw [Finset.sum_add_distrib]
      rw [hswap, two_mul]
    _ = _ := by
      simp only [overlapCount_cast_eq_sum_indicator, Finset.sum_filter, v]

theorem lintegral_overlapCount_sq_le
    (A : Finset RealInterval) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hlam : Set.Pairwise (↑A : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hpack : ∀ J : RealInterval,
      (∑ I ∈ A.filter (fun I ↦ I.carrier ⊆ J.carrier), I.length) ≤ Λ * J.length) :
    (∫⁻ x, (overlapCount A x : ℝ≥0∞) ^ 2) ≤
      2 * ENNReal.ofReal Λ * ENNReal.ofReal (∑ I ∈ A, I.length) := by
  calc
    _ ≤ ∫⁻ x, 2 * ∑ I ∈ A,
        (overlapCount (A.filter fun J ↦ J.carrier ⊆ I.carrier) x : ℝ≥0∞) :=
      lintegral_mono (overlapCount_sq_le_two_sum_descendant_counts A hlam)
    _ = 2 * ∑ I ∈ A, ENNReal.ofReal
        (∑ J ∈ A.filter (fun J ↦ J.carrier ⊆ I.carrier), J.length) := by
      rw [lintegral_const_mul _ (Finset.measurable_sum _
        (fun I _ ↦ measurable_overlapCount_cast _))]
      rw [lintegral_finsetSum _ (fun I _ ↦ measurable_overlapCount_cast _)]
      simp_rw [lintegral_overlapCount_cast]
    _ ≤ 2 * ∑ I ∈ A, ENNReal.ofReal (Λ * I.length) := by
      gcongr with I hI
      exact hpack I
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul hΛ]
      rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun I _ ↦ I.length_pos.le),
        mul_assoc]

/-- The discarded family's counting-function second moment is
exponentially small for the concrete canonical active family. -/
theorem lintegral_active_removed_overlap_sq_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    (∫⁻ x, (overlapCount (activeBadIntervals S f I₀ k₀ s scale N \
      overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N)
        (activeExponentialCutoff s)) x : ℝ≥0∞) ^ 2) ≤
      2 * ENNReal.ofReal (1 + (2 : ℝ) ^ (s : ℤ)) ^ 2 *
        ((1 / 2 : ℝ≥0∞) ^ (8 * (s + 1)) * ENNReal.ofReal K.length) := by
  let A := activeBadIntervals S f I₀ k₀ s scale N
  let R := A \ overlapPrunedFamily A (activeExponentialCutoff s)
  have hRS : R ⊆ S := Finset.sdiff_subset.trans
    ((activeBadIntervals_subset S f I₀ k₀ s scale N).trans
      (hN.trans (nonstandardIntervals_subset S f I₀ k₀ s scale)))
  have hb := lintegral_overlapCount_sq_le R (1 + (2 : ℝ) ^ (s : ℤ)) (by positivity)
    (fun I hI J hJ hne ↦ hlam (hRS hI) (hRS hJ) hne)
    (local_length_packing_mono Finset.sdiff_subset
      (sum_activeBadIntervals_descendants_length_le f I₀ k₀ s scale hlam N hN))
  apply hb.trans
  calc
    _ ≤ (2 * ENNReal.ofReal (1 + (2 : ℝ) ^ (s : ℤ))) *
        (ENNReal.ofReal (1 + (2 : ℝ) ^ (s : ℤ)) *
          ((1 / 2 : ℝ≥0∞) ^ (8 * (s + 1)) * ENNReal.ofReal K.length)) :=
      mul_le_mul_right (ofReal_sum_active_removed_length_le f I₀ k₀ s scale
        hlam N hN K hsub) _
    _ = _ := by rw [pow_two]; simp only [mul_assoc]


end KrauseLaceyBadScale
end QuadraticCarleson
