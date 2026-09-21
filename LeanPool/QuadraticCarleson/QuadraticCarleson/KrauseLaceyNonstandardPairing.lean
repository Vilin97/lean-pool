/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardPhysicalL2

/-!
# The actual nonstandard local pairing bound (KL18 Proposition 4.7)

The amplitude estimate gives the exact interval-average majorant for
every physical truncation. Integration and the proved no-loss bad-input
mass packing yield the source pairing bound, independently of the scale
gap. No linearization or sparse estimate is assumed.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyGenerationLayers KrauseLaceyStoppingExtraction

attribute [local instance] Classical.propDecidable

theorem norm_localizedBadPiece_le_mass
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    {I : RealInterval} (hI : I ∈ nonstandardIntervals S f I₀ k₀ s scale) (x : ℝ) :
    ‖krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x‖ ≤
      (8 * positiveDyadicAmplitudeBound / I.length) * intervalBadMass S f I₀ k₀ s scale I := by
  have hb := integrable_badScaleInput S hf I₀ k₀ (scale I + 2 - s)
  have h := (krauseLaceyPositiveKernel (scale I)).norm_applyIntegral_le
    (hb.indicator I.measurableSet_centralThird) x
  simp only [FiniteRangeKernel.applyIntegral, krauseLaceyPositiveKernel_apply,
    ← krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution] at h
  have hid : (∫ t, ‖I.centralThird.indicator
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) t‖) = intervalBadMass S f I₀ k₀ s scale I := by
    simp only [norm_indicator_eq_indicator_norm, intervalBadMass]
    exact integral_indicator I.measurableSet_centralThird
  rw [hid] at h
  apply h.trans_eq
  change (positiveDyadicAmplitudeBound / (2 : ℝ) ^ (scale I - 1)) * _ = _
  rw [(Finset.mem_filter.mp hI).2.1, krauseLacey_scale_eq_eight_mul_radius]
  ring

theorem badLengthTailMaximal_le_massMajorant
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (x : ℝ) :
    badLengthTailMaximal S f I₀ k₀ s scale N x ≤
      ∑ I ∈ N, I.carrier.indicator (fun _ ↦
        (8 * positiveDyadicAmplitudeBound / I.length) * intervalBadMass S f I₀ k₀ s scale I) x := by
  apply ciSup_le
  intro ell
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  by_cases hx : x ∈ I.carrier
  · rw [Set.indicator_of_mem hx]
    split_ifs
    · exact norm_localizedBadPiece_le_mass hf I₀ k₀ s scale (hN hI) x
    · rw [norm_zero]
      exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num)
        positiveDyadicAmplitudeBound_nonneg) I.length_pos.le)
        (intervalBadMass_nonneg S f I₀ k₀ s scale I)
  · rw [Set.indicator_of_notMem hx, krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 (scale I) I _
      (Finset.mem_filter.mp (hN hI)).2.1 hx]
    simp

theorem lintegral_nonstandard_pairing_le_sum_local_averages
    {S : Finset RealInterval} {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) :
    (∫⁻ x, ‖badLengthTailMaximal S f I₀ k₀ s scale N x‖ₑ * ‖g x‖ₑ) ≤
      ENNReal.ofReal (∑ I ∈ N, 8 * positiveDyadicAmplitudeBound *
        intervalBadMass S f I₀ k₀ s scale I * intervalL1Average g I) := by
  let C := fun I : RealInterval ↦
    (8 * positiveDyadicAmplitudeBound / I.length) * intervalBadMass S f I₀ k₀ s scale I
  have hC (I : RealInterval) : 0 ≤ C I := mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg) I.length_pos.le)
    (intervalBadMass_nonneg S f I₀ k₀ s scale I)
  have hind (I : RealInterval) (x : ℝ) :
      ENNReal.ofReal (I.carrier.indicator (fun _ ↦ C I) x) * ‖g x‖ₑ =
        ENNReal.ofReal (C I) * I.carrier.indicator (fun x ↦ ‖g x‖ₑ) x := by
    by_cases hx : x ∈ I.carrier <;> simp [hx]
  calc
    _ ≤ ∫⁻ x, ∑ I ∈ N,
        ENNReal.ofReal (C I) * I.carrier.indicator (fun x ↦ ‖g x‖ₑ) x := by
      apply lintegral_mono
      intro x
      dsimp only
      simp_rw [← hind]
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
        (fun I _ ↦ Set.indicator_nonneg (fun _ _ ↦ hC I) x),
        Real.enorm_of_nonneg (badLengthTailMaximal_nonneg f I₀ k₀ s scale hlam N hN x)]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (badLengthTailMaximal_le_massMajorant hf I₀ k₀ s scale N hN x)) _
    _ = ∑ I ∈ N, ENNReal.ofReal (C I) * ∫⁻ x in I.carrier, ‖g x‖ₑ := by
      have hm (I : RealInterval) : AEMeasurable (fun x ↦
          ENNReal.ofReal (C I) * I.carrier.indicator (fun x ↦ ‖g x‖ₑ) x) volume :=
        aemeasurable_const.mul (hg.aestronglyMeasurable.enorm.indicator I.measurableSet_carrier)
      rw [lintegral_finsetSum' _ (fun I _ ↦ hm I)]
      apply Finset.sum_congr rfl
      intro I hI
      rw [lintegral_const_mul'' _
        (hg.aestronglyMeasurable.enorm.indicator I.measurableSet_carrier),
        lintegral_indicator I.measurableSet_carrier]
    _ = ∑ I ∈ N, ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
        intervalBadMass S f I₀ k₀ s scale I * intervalL1Average g I) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [← ofReal_integral_norm_eq_lintegral_enorm hg.integrableOn,
        ← ENNReal.ofReal_mul (hC I), ← intervalL1Average_mul_length g I]
      congr 1
      dsimp [C]
      field_simp [I.length_pos.ne']
    _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun I _ ↦ mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
        (intervalBadMass_nonneg S f I₀ k₀ s scale I)) (intervalL1Average_nonneg g I))).symm

/-- Exact Proposition 4.7 with the actual interval-average hypothesis. -/
theorem lintegral_nonstandard_pairing_le_of_averages_le
    {S : Finset RealInterval} {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    {G : ℝ} (hG : 0 ≤ G) (hgavg : ∀ I ∈ N, intervalL1Average g I ≤ G) :
    (∫⁻ x, ‖badLengthTailMaximal S f I₀ k₀ s scale N x‖ₑ * ‖g x‖ₑ) ≤
      ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * G * ∫ x, ‖f x‖) := by
  apply (lintegral_nonstandard_pairing_le_sum_local_averages hf hg I₀ k₀ s scale hlam N hN).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ I ∈ N, 8 * positiveDyadicAmplitudeBound *
        intervalBadMass S f I₀ k₀ s scale I * G := by
      apply Finset.sum_le_sum
      intro I hI
      exact mul_le_mul_of_nonneg_left (hgavg I hI) (mul_nonneg
        (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
        (intervalBadMass_nonneg S f I₀ k₀ s scale I))
    _ = 8 * positiveDyadicAmplitudeBound * G * ∑ I ∈ N, intervalBadMass S f I₀ k₀ s scale I := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_intervalBadInput_mass_le hf I₀ k₀ s scale hlam N
        (hN.trans (nonstandardIntervals_subset S f I₀ k₀ s scale))
        (fun I hI ↦ (Finset.mem_filter.mp (hN hI)).2.1))
      (mul_nonneg (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg) hG)

/-- The genuine two-function good collection supplies the needed
averages itself, so the source local bound has no average hypothesis. -/
theorem lintegral_nonstandard_good_pairing_le
    {S : Finset RealInterval} {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier) :
    (∫⁻ x, ‖badLengthTailMaximal S f I₀ k₀ s scale
      (nonstandardIntervals S f I₀ k₀ s scale ∩ goodCollection S f g I₀) x‖ₑ * ‖g x‖ₑ) ≤
      ENNReal.ofReal (80 * positiveDyadicAmplitudeBound * intervalL1Average g I₀ *
        ∫ x, ‖f x‖) := by
  have h := lintegral_nonstandard_pairing_le_of_averages_le hf hg I₀ k₀ s scale hlam
    (nonstandardIntervals S f I₀ k₀ s scale ∩ goodCollection S f g I₀) Finset.inter_subset_left
    (mul_nonneg (by norm_num) (intervalL1Average_nonneg g I₀))
    (fun I hI ↦ (goodCollection_averages_le hsub (Finset.mem_inter.mp hI).2).2)
  convert h using 1; congr 1; ring


end KrauseLaceyBadScale
end QuadraticCarleson
