/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyEnergyClassification
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardCrossRows

/-!
# Cross-row aggregation for the scalar-standard family

The scalar-standard diagonal estimate has an inverse parent-length factor.
This file shows that the same factor persists after summing all separated
smaller-scale rows in one physical tail.  The proof uses the actual
two-scale correlation estimate and the restricted bad-input packing lemma;
in particular, neither the number of intervals nor the number of scales is
charged to the estimate.
-/

open Function MeasureTheory Set
open scoped ComplexConjugate

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction

attribute [local instance] Classical.propDecidable

theorem energyStandardIntervals_subset
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) :
    energyStandardIntervals S f I₀ k₀ s scale ⊆ S := by
  intro I hI
  exact energyEligibleIntervals_subset S f I₀ k₀ s scale
    (Finset.mem_filter.mp hI).1

/-- One separated cross row for the scalar-standard family.  The only
classification use is membership in the actual good collection; the row
itself follows from kernel separation and local bad-input mass packing. -/
theorem sum_energyStandard_crossPairing_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hsmall : ∀ J ∈ N, 1 ≤ scale J)
    {I : RealInterval} (hI : I ∈ energyStandardIntervals S f I₀ k₀ s scale) :
    (∑ J ∈ N.filter (fun J ↦ scale J + 3 ≤ scale I),
      ‖∫ x, krauseLaceyLocalizedPiece 1 (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x *
        conj (krauseLaceyLocalizedPiece 1 (scale J) J
          (badScaleInput S f I₀ k₀ (scale J + 2 - s)) x)‖) ≤
      (3840 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ / I.length) *
        intervalBadMass S f I₀ k₀ s scale I := by
  let T := N.filter fun J ↦ scale J + 3 ≤ scale I
  let U := T.filter fun J ↦ J.carrier ⊆ I.carrier
  have hS := energyStandardIntervals_subset S f I₀ k₀ s scale
  have hlenI := (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2.1
  have hlenJ (J : RealInterval) (hJ : J ∈ N) :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hN hJ)).1).2.1
  let P (J : RealInterval) := ‖∫ x, krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x *
    conj (krauseLaceyLocalizedPiece 1 (scale J) J
      (badScaleInput S f I₀ k₀ (scale J + 2 - s)) x)‖
  have hrestrict : (∑ J ∈ T, P J) = ∑ J ∈ U, P J := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ T)
    intro J hJT hJU
    have hJ := Finset.mem_filter.mp hJT
    have hnot : ¬ J.carrier ⊆ I.carrier := by
      intro hs
      exact hJU (Finset.mem_filter.mpr ⟨hJT, hs⟩)
    have hd := (carrier_subset_or_disjoint_of_scale_lt scale hlam (hS hI)
      (hS (hN hJ.1)) hlenI (hlenJ J hJ.1) (by omega)).resolve_left hnot
    dsimp [P]
    rw [integral_localizedPiece_cross_eq_zero_of_disjoint _ _ _ _ _ _ hlenI
      (hlenJ J hJ.1) hd, norm_zero]
  have hUS : U ⊆ S := (Finset.filter_subset _ T).trans
    ((Finset.filter_subset _ N).trans (hN.trans hS))
  have hUN : U ⊆ N := (Finset.filter_subset _ T).trans (Finset.filter_subset _ N)
  have hmass : (∑ J ∈ U, intervalBadMass S f I₀ k₀ s scale J) ≤
      10 * intervalL1Average f I₀ * I.length := by
    apply (sum_intervalBadInput_mass_le_local hf I₀ k₀ s scale hlam U hUS
      (fun J hJ ↦ hlenJ J (hUN hJ)) I
      (fun J hJ ↦ (Finset.mem_filter.mp hJ).2)).trans
    rw [← intervalL1Average_mul_length]
    exact mul_le_mul_of_nonneg_right
      (goodCollection_averages_le hsub
        (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).1).1 I.length_pos.le
  have hm := intervalBadMass_nonneg S f I₀ k₀ s scale I
  have hC : 0 ≤ 384 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2 := by
    positivity
  change (∑ J ∈ T, P J) ≤ _
  rw [hrestrict]
  calc
    _ ≤ ∑ J ∈ U, (384 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2) *
        intervalBadMass S f I₀ k₀ s scale I * intervalBadMass S f I₀ k₀ s scale J := by
      apply Finset.sum_le_sum
      intro J hJ
      exact krauseLaceyLocalizedPiece_crossPairing_le_length _ _ (hsmall J (hUN hJ))
        (Finset.mem_filter.mp ((Finset.filter_subset _ T) hJ)).2 I J hlenI
        (integrable_badScaleInput S hf I₀ k₀ _) (integrable_badScaleInput S hf I₀ k₀ _)
    _ = (384 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2) *
        intervalBadMass S f I₀ k₀ s scale I *
          ∑ J ∈ U, intervalBadMass S f I₀ k₀ s scale J := (Finset.mul_sum _ _ _).symm
    _ ≤ (384 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2) *
        intervalBadMass S f I₀ k₀ s scale I *
          (10 * intervalL1Average f I₀ * I.length) :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg hC hm)
    _ = _ := by field_simp; ring

theorem sum_abs_inner_energyStandard_crossRow_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hsmall : ∀ J ∈ N, 1 ≤ scale J)
    {I : RealInterval} (hI : I ∈ energyStandardIntervals S f I₀ k₀ s scale) :
    (∑ J ∈ N.filter (fun J ↦ scale J + 3 ≤ scale I),
      |inner ℝ (badPieceLp S f hf I₀ k₀ s scale I)
        (badPieceLp S f hf I₀ k₀ s scale J)|) ≤
      (3840 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ / I.length) *
        intervalBadMass S f I₀ k₀ s scale I := by
  apply le_trans _ (sum_energyStandard_crossPairing_le hf I₀ k₀ s scale hlam hsub
    N hN hsmall hI)
  apply Finset.sum_le_sum
  intro J hJ
  exact abs_inner_localizedPieceLp_le_crossPairing _ _ _ _ _ _ _ _

/-- All separated cross rows inside one physical suffix.  The inverse
physical length survives the finite double sum, by restricted local packing
followed by the global bad-input mass estimate. -/
theorem sum_energyStandard_physicalTail_crossRows_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s ell : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hsmall : ∀ J ∈ N, 1 ≤ scale J) :
    (∑ I ∈ N.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length),
      ∑ J ∈ (N.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length)).filter
        (fun J ↦ scale J + 3 ≤ scale I),
        |inner ℝ (badPieceLp S f hf I₀ k₀ s scale I)
          (badPieceLp S f hf I₀ k₀ s scale J)|) ≤
      (3840 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
        (2 : ℝ) ^ ell) * ∫ x, ‖f x‖ := by
  let T := N.filter fun I ↦ (2 : ℝ) ^ ell ≤ I.length
  have hT : T ⊆ energyStandardIntervals S f I₀ k₀ s scale :=
    (Finset.filter_subset _ N).trans hN
  have hTS : T ⊆ S := hT.trans (energyStandardIntervals_subset S f I₀ k₀ s scale)
  have hrow (I : RealInterval) (hI : I ∈ T) :
      (∑ J ∈ T.filter (fun J ↦ scale J + 3 ≤ scale I),
        |inner ℝ (badPieceLp S f hf I₀ k₀ s scale I)
          (badPieceLp S f hf I₀ k₀ s scale J)|) ≤
        (3840 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
          (2 : ℝ) ^ ell) * intervalBadMass S f I₀ k₀ s scale I := by
    apply (sum_abs_inner_energyStandard_crossRow_le hf I₀ k₀ s scale hlam hsub T hT
      (fun J hJ ↦ hsmall J (Finset.mem_filter.mp hJ).1) (hT hI)).trans
    apply mul_le_mul_of_nonneg_right _ (intervalBadMass_nonneg S f I₀ k₀ s scale I)
    exact div_le_div_of_nonneg_left
      (by positivity [intervalL1Average_nonneg f I₀])
      (by positivity : 0 < (2 : ℝ) ^ ell) (Finset.mem_filter.mp hI).2
  calc
    _ = ∑ I ∈ T, ∑ J ∈ T.filter (fun J ↦ scale J + 3 ≤ scale I),
        |inner ℝ (badPieceLp S f hf I₀ k₀ s scale I)
          (badPieceLp S f hf I₀ k₀ s scale J)| := rfl
    _ ≤ ∑ I ∈ T, (3840 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
        (2 : ℝ) ^ ell) * intervalBadMass S f I₀ k₀ s scale I := by
      exact Finset.sum_le_sum hrow
    _ = (3840 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
        (2 : ℝ) ^ ell) * ∑ I ∈ T, intervalBadMass S f I₀ k₀ s scale I :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_intervalBadInput_mass_le hf I₀ k₀ s scale hlam T hTS
        (fun I hI ↦ (Finset.mem_filter.mp (Finset.mem_filter.mp (hT hI)).1).2.1))
      (by positivity [intervalL1Average_nonneg f I₀])


end KrauseLaceyBadScale
end QuadraticCarleson
