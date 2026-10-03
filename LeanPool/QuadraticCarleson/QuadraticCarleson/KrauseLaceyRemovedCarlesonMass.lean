/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyOverlapJohnNirenberg

/-!
# Exponential control of the actual removed interval mass

Local Carleson packing converts the exceptional-set measure to the sum
of lengths of all removed intervals. This is stronger than just a weak
bound for the overlap counting function and is the quantity used for the
discarded contribution in KL18.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyGenerationLayers

attribute [local instance] Classical.propDecidable

theorem sum_removed_length_le_carleson_mul_stoppingLength
    (A : Finset RealInterval) (M : ℕ) (Λ : ℝ)
    (hpack : ∀ J : RealInterval,
      (∑ I ∈ A.filter (fun I ↦ I.carrier ⊆ J.carrier), I.length) ≤ Λ * J.length) :
    (∑ I ∈ A \ overlapPrunedFamily A M, I.length) ≤
      Λ * ∑ I ∈ overlapStoppingIntervals A M, I.length := by
  let R := A \ overlapPrunedFamily A M
  let C := overlapStoppingIntervals A M
  calc
    (∑ J ∈ R, J.length) ≤
        ∑ J ∈ R, ∑ I ∈ C, if J.carrier ⊆ I.carrier then J.length else 0 := by
      apply Finset.sum_le_sum
      intro J hJ
      obtain ⟨I, hI, hJI⟩ := exists_maximalInterval_containing hJ
      have hsingle := Finset.single_le_sum
        (fun K (_ : K ∈ C) ↦ show 0 ≤ if J.carrier ⊆ K.carrier then J.length else 0 by
          split_ifs
          · exact J.length_pos.le
          · exact le_rfl) hI
      simpa only [ite_eq_left hJI] using hsingle
    _ = ∑ I ∈ C, ∑ J ∈ R.filter (fun J ↦ J.carrier ⊆ I.carrier), J.length := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ ∑ I ∈ C, Λ * I.length := by
      apply Finset.sum_le_sum
      intro I hI
      exact local_length_packing_mono Finset.sdiff_subset hpack I
    _ = Λ * ∑ I ∈ C, I.length := (Finset.mul_sum _ _ _).symm

theorem ofReal_sum_removed_length_le_carleson_mul_highOverlap
    (A : Finset RealInterval) (M : ℕ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hlam : Set.Pairwise (↑A : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hpack : ∀ J : RealInterval,
      (∑ I ∈ A.filter (fun I ↦ I.carrier ⊆ J.carrier), I.length) ≤ Λ * J.length) :
    ENNReal.ofReal (∑ I ∈ A \ overlapPrunedFamily A M, I.length) ≤
      ENNReal.ofReal Λ * volume {x | M < overlapCount A x} := by
  apply (ENNReal.ofReal_le_ofReal
    (sum_removed_length_le_carleson_mul_stoppingLength A M Λ hpack)).trans_eq
  rw [ENNReal.ofReal_mul hΛ,
    ENNReal.ofReal_sum_of_nonneg (fun I _ ↦ I.length_pos.le),
    sum_volume_overlapStoppingIntervals A M hlam]

/-- All discarded lengths enjoy exponential decay at block cutoffs. -/
theorem ofReal_sum_removed_length_blocks_le
    (t : ℕ) (A : Finset RealInterval) (K : RealInterval) (M : ℕ) (Λ : ℝ)
    (hΛ : 0 ≤ Λ) (hblock : 2 * Λ ≤ M + 1)
    (hlam : Set.Pairwise (↑A : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ A, I.carrier ⊆ K.carrier)
    (hpack : ∀ J : RealInterval,
      (∑ I ∈ A.filter (fun I ↦ I.carrier ⊆ J.carrier), I.length) ≤ Λ * J.length) :
    ENNReal.ofReal (∑ I ∈ A \ overlapPrunedFamily A (t * (M + 1)), I.length) ≤
      ENNReal.ofReal Λ * ((1 / 2 : ℝ≥0∞) ^ t * ENNReal.ofReal K.length) :=
  (ofReal_sum_removed_length_le_carleson_mul_highOverlap A (t * (M + 1)) Λ hΛ
    hlam hpack).trans (mul_le_mul_right
      (volume_overlap_blocks_le_half_pow t A K M Λ hblock hlam hsub hpack) _)


end KrauseLaceyBadScale
end QuadraticCarleson
