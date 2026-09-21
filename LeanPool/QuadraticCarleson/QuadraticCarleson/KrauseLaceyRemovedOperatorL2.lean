/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyOverlapSecondMoment

/-!
# The genuine removed bad-input operator

The kernel amplitude and actual stopping-cell averages give a uniform
bound on each localized piece. The finite Carleson second-moment estimate
then controls the entire removed-family maximal operator in `L²`.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyGenerationLayers

attribute [local instance] Classical.propDecidable

noncomputable def badPieceUniformBound (f : ℝ → ℂ) (I₀ : RealInterval) : ℝ :=
  80 * positiveDyadicAmplitudeBound * intervalL1Average f I₀

theorem badPieceUniformBound_nonneg (f : ℝ → ℂ) (I₀ : RealInterval) :
    0 ≤ badPieceUniformBound f I₀ := by
  unfold badPieceUniformBound
  exact mul_nonneg (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
    (intervalL1Average_nonneg f I₀)

theorem norm_localizedBadPiece_le_uniform
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    {I : RealInterval} (hI : I ∈ nonstandardIntervals S f I₀ k₀ s scale) (x : ℝ) :
    ‖krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x‖ ≤ badPieceUniformBound f I₀ := by
  let b := badScaleInput S f I₀ k₀ (scale I + 2 - s)
  have hb : Integrable b := integrable_badScaleInput S hf I₀ k₀ (scale I + 2 - s)
  have h := (krauseLaceyPositiveKernel (scale I)).norm_applyIntegral_le
    (hb.indicator I.measurableSet_centralThird) x
  simp only [FiniteRangeKernel.applyIntegral, krauseLaceyPositiveKernel_apply,
    ← krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution] at h
  have hmass := badScaleInput_localMass_le hf I₀ k₀ (scale I + 2 - s)
    hlam hsub (Finset.mem_filter.mp hI).1
  have hid : (∫ t, ‖I.centralThird.indicator b t‖) = ∫ t in I.centralThird, ‖b t‖ := by
    simp only [norm_indicator_eq_indicator_norm]
    exact integral_indicator I.measurableSet_centralThird
  rw [hid] at h
  have hscale := (Finset.mem_filter.mp hI).2.1
  calc
    _ ≤ (positiveDyadicAmplitudeBound / (2 : ℝ) ^ (scale I - 1)) *
        (∫ t in I.centralThird, ‖b t‖) := h
    _ ≤ (positiveDyadicAmplitudeBound / (2 : ℝ) ^ (scale I - 1)) *
        (10 * intervalL1Average f I₀ * I.length) :=
      mul_le_mul_of_nonneg_left hmass (div_nonneg positiveDyadicAmplitudeBound_nonneg
        (by positivity))
    _ = badPieceUniformBound f I₀ := by
      rw [hscale, krauseLacey_scale_eq_eight_mul_radius]
      unfold badPieceUniformBound
      field_simp
      <;> ring

theorem badLengthTailMaximal_le_uniform_mul_overlapCount
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (x : ℝ) :
    badLengthTailMaximal S f I₀ k₀ s scale N x ≤
      badPieceUniformBound f I₀ * overlapCount N x := by
  apply ciSup_le
  intro ell
  calc
    _ ≤ ∑ I ∈ N, ‖if (2 : ℝ) ^ ell ≤ I.length then
        krauseLaceyLocalizedPiece 1 (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x else 0‖ := norm_sum_le _ _
    _ ≤ ∑ I ∈ N, if x ∈ I.carrier then badPieceUniformBound f I₀ else 0 := by
      apply Finset.sum_le_sum
      intro I hI
      by_cases hx : x ∈ I.carrier
      · rw [ite_eq_left hx]
        split_ifs
        · exact norm_localizedBadPiece_le_uniform hf I₀ k₀ s scale hlam hsub (hN hI) x
        · simpa only [norm_zero] using badPieceUniformBound_nonneg f I₀
      · rw [ite_eq_right hx, krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 (scale I) I _
          (Finset.mem_filter.mp (hN hI)).2.1 hx]
        simp
    _ = badPieceUniformBound f I₀ * overlapCount N x := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, overlapCount, mul_comm]

/-- This squared extended `L²` estimate concerns the actual all-threshold
maximal action of the removed intervals, not a formal counting operator. -/
theorem eLpNorm_removed_badLengthTailMaximal_sq_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) :
    eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale
      (activeBadIntervals S f I₀ k₀ s scale N \
        overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N)
          (activeExponentialCutoff s))) 2 volume ^ 2 ≤
      ENNReal.ofReal (badPieceUniformBound f I₀) ^ 2 *
        (2 * ENNReal.ofReal (1 + (2 : ℝ) ^ (s : ℤ)) ^ 2 *
          ((1 / 2 : ℝ≥0∞) ^ (8 * (s + 1)) * ENNReal.ofReal I₀.length)) := by
  let R := activeBadIntervals S f I₀ k₀ s scale N \
    overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) (activeExponentialCutoff s)
  have hR : R ⊆ nonstandardIntervals S f I₀ k₀ s scale :=
    Finset.sdiff_subset.trans ((activeBadIntervals_subset S f I₀ k₀ s scale N).trans hN)
  have heq : eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale R) 2 volume ^ 2 =
      ∫⁻ x, ‖badLengthTailMaximal S f I₀ k₀ s scale R x‖ₑ ^ 2 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    rw [← ENNReal.rpow_mul_natCast]
    norm_num
  rw [heq]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (badPieceUniformBound f I₀) ^ 2 *
        (overlapCount R x : ℝ≥0∞) ^ 2 := by
      apply lintegral_mono
      intro x
      have hpoint := badLengthTailMaximal_le_uniform_mul_overlapCount hf I₀ k₀ s scale
        hlam hsub R hR x
      have he : ‖badLengthTailMaximal S f I₀ k₀ s scale R x‖ₑ ≤
          ENNReal.ofReal (badPieceUniformBound f I₀) * (overlapCount R x : ℝ≥0∞) := by
        rw [Real.enorm_of_nonneg (badLengthTailMaximal_nonneg f I₀ k₀ s scale hlam R hR x),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (badPieceUniformBound_nonneg f I₀)]
        exact ENNReal.ofReal_le_ofReal hpoint
      simpa only [mul_pow] using pow_le_pow_left' he 2
    _ = ENNReal.ofReal (badPieceUniformBound f I₀) ^ 2 *
        (∫⁻ x, (overlapCount R x : ℝ≥0∞) ^ 2) := by
      rw [lintegral_const_mul _ ((measurable_overlapCount_cast R).pow_const 2)]
    _ ≤ _ := mul_le_mul_right (lintegral_active_removed_overlap_sq_le f I₀ k₀ s scale
      hlam N hN I₀ (fun I hI ↦ hsub I (nonstandardIntervals_subset S f I₀ k₀ s scale (hN hI)))) _


end KrauseLaceyBadScale
end QuadraticCarleson
