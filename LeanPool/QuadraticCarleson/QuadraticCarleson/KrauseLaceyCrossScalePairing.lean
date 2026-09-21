/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyCrossScaleCorrelation

/-!
# Actual cross pairings of the separated quadratic pieces

The mixed integral composition is justified on `L¹` inputs using the
bounded finite-range kernels. The resulting cross-pairing estimate keeps
the two actual central-third restricted input masses.
-/

open Function MeasureTheory Set
open scoped ComplexConjugate

namespace QuadraticCarleson


namespace FiniteRangeKernel

theorem integrable_mixedComposition_integrand (K L : FiniteRangeKernel)
    {g : ℝ → ℂ} (hg : Integrable g) (x : ℝ) :
    Integrable (fun z : ℝ × ℝ ↦ K x z.1 * L z.1 z.2 * g z.2)
      (volume.prod volume) := by
  have hi := (K.integrable_row x).mul_prod hg
  have hb : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖L z.1 z.2‖ ≤ L.bound :=
    Filter.Eventually.of_forall (fun z ↦ L.norm_le z.1 z.2)
  convert hi.mul_bdd L.measurable_toFun.aestronglyMeasurable hb using 1
  funext z
  dsimp only [Function.uncurry]
  ring

/-- Exact mixed composition; all Fubini integrability is derived. -/
theorem applyIntegral_comp_eq_mixed (K L : FiniteRangeKernel)
    {g : ℝ → ℂ} (hg : Integrable g) (x : ℝ) :
    K.applyIntegral (L.applyIntegral g) x =
      ∫ y, (∫ t, K x t * L t y) * g y := by
  unfold applyIntegral
  simp_rw [← integral_const_mul]
  have hswap := integral_integral_swap
    (f := fun t y ↦ K x t * L t y * g y)
    (K.integrable_mixedComposition_integrand L hg x)
  calc
    _ = ∫ t, ∫ y, K x t * L t y * g y := by
      apply integral_congr_ae
      filter_upwards with t
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = ∫ y, ∫ t, K x t * L t y * g y := hswap
    _ = _ := by simp_rw [integral_mul_const]

/-- The mixed composition norm is bounded by its genuine mixed kernel. -/
theorem norm_applyIntegral_comp_le (K L : FiniteRangeKernel)
    {g : ℝ → ℂ} (hg : Integrable g) {C : ℝ} (_hC : 0 ≤ C)
    (hbound : ∀ x y, ‖∫ t, K x t * L t y‖ ≤ C) (x : ℝ) :
    ‖K.applyIntegral (L.applyIntegral g) x‖ ≤ C * ∫ y, ‖g y‖ := by
  rw [K.applyIntegral_comp_eq_mixed L hg x]
  have hi : Integrable (fun y ↦ (∫ t, K x t * L t y) * g y) := by
    simpa only [integral_mul_const] using
      (K.integrable_mixedComposition_integrand L hg x).integral_prod_right
  calc
    _ ≤ ∫ y, ‖(∫ t, K x t * L t y) * g y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, C * ‖g y‖ := by
      apply integral_mono hi.norm (hg.norm.const_mul C)
      intro y
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound x y) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- An actual two-operator cross pairing, controlled by the mixed
adjoint kernel and the two `L¹` masses. -/
theorem norm_crossPairing_le (K L : FiniteRangeKernel)
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x y, ‖∫ t, conj (K t x) * L t y‖ ≤ C) :
    ‖∫ x, K.applyIntegral f x * conj (L.applyIntegral g x)‖ ≤
      C * (∫ x, ‖f x‖) * ∫ x, ‖g x‖ := by
  rw [K.integral_pairing_adjoint hf (L.integrable_applyIntegral hg)]
  have hnorm := K.adjoint.norm_applyIntegral_comp_le L hg hC hbound
  have hm := (K.adjoint.integrable_applyIntegral
    (L.integrable_applyIntegral hg)).aestronglyMeasurable
  have hb : ∀ᵐ x ∂volume,
      ‖conj (K.adjoint.applyIntegral (L.applyIntegral g) x)‖ ≤ C * ∫ y, ‖g y‖ := by
    · filter_upwards with x
      simpa only [RCLike.norm_conj] using hnorm x
  have hi := hf.mul_bdd (Complex.continuous_conj.comp_aestronglyMeasurable hm) hb
  calc
    _ ≤ ∫ x, ‖f x * conj (K.adjoint.applyIntegral (L.applyIntegral g) x)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x‖ * (C * ∫ y, ‖g y‖) := by
      apply integral_mono hi.norm (hf.norm.mul_const _)
      intro x
      dsimp only
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left (hnorm x) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const]; ring

end FiniteRangeKernel

/-- The actual positive quadratic convolution as a bounded finite-range
kernel, with its proved cutoff constant and support radius. -/
noncomputable def krauseLaceyPositiveKernel (j : ℤ) : FiniteRangeKernel where
  toFun x t := annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t)
  measurable_toFun := by
    have ha : Continuous (positiveDyadicAmplitude j) :=
      continuous_iff_continuousAt.mpr
        (fun t ↦ (hasDerivAt_positiveDyadicAmplitude j t).continuousAt)
    unfold annularQuadraticKernel phase
    fun_prop
  radius := (2 : ℝ) ^ (j - 1)
  radius_pos := by positivity
  bound := positiveDyadicAmplitudeBound / (2 : ℝ) ^ (j - 1)
  bound_nonneg := div_nonneg positiveDyadicAmplitudeBound_nonneg (by positivity)
  norm_le x t := by
    simp only [annularQuadraticKernel, norm_mul, norm_phase, mul_one]
    exact norm_positiveDyadicAmplitude_le j (x - t)
  eq_zero x t ht := by
    have hz : positiveDyadicAmplitude j (x - t) = 0 := by
      by_contra hn
      have hs := positiveDyadicAmplitude_support_subset j hn
      have hnonneg : 0 ≤ x - t := (by positivity : 0 ≤ (2 : ℝ) ^ (j - 1) / 4).trans hs.1
      rw [abs_of_nonneg hnonneg] at ht
      exact (not_lt_of_ge hs.2) ht
    simp [annularQuadraticKernel, hz]

@[simp] theorem krauseLaceyPositiveKernel_apply (j : ℤ) (x t : ℝ) :
    krauseLaceyPositiveKernel j x t =
      annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) := rfl

theorem krauseLaceyPositiveKernel_mixed_adjoint_le
    (j k : ℤ) (hj : 1 ≤ j) (hjk : j + 3 ≤ k) (x y : ℝ) :
    ‖∫ t, conj (krauseLaceyPositiveKernel k t x) * krauseLaceyPositiveKernel j t y‖ ≤
      6 * positiveDyadicAmplitudeBound ^ 2 / ((2 : ℝ) ^ (k - 1)) ^ 2 := by
  have h := krauseLacey_crossScalePositiveDyadicCorrelation_le j k hj hjk (-x) (-y)
  dsimp only at h
  have heq : ‖∫ t, conj (krauseLaceyPositiveKernel k t x) *
      krauseLaceyPositiveKernel j t y‖ =
      ‖∫ t, annularQuadraticKernel (positiveDyadicAmplitude k) 1 (-x - t) *
        conj (annularQuadraticKernel (positiveDyadicAmplitude j) 1 (-y - t))‖ := by
    rw [← RCLike.norm_conj, ← integral_conj]
    simp only [map_mul, starRingEnd_self_apply, krauseLaceyPositiveKernel_apply]
    rw [← MeasureTheory.integral_sub_left_eq_self
      (fun t ↦ annularQuadraticKernel (positiveDyadicAmplitude k) 1 (-x - t) *
        conj (annularQuadraticKernel (positiveDyadicAmplitude j) 1 (-y - t))) volume 0]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    simp only [zero_sub]
    rw [show -x - -t = t - x by ring, show -y - -t = t - y by ring]
  rw [heq]
  apply h.trans
  split_ifs
  · exact le_rfl
  · positivity

/-- The separated-scale localized cross term used in KL18 (4.20).
The two masses are the actual restricted inputs, not assumed budgets. -/
theorem krauseLaceyLocalizedPiece_crossPairing_le
    (j k : ℤ) (hj : 1 ≤ j) (hjk : j + 3 ≤ k) (I J : RealInterval)
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ‖∫ x, krauseLaceyLocalizedPiece 1 k I f x *
      conj (krauseLaceyLocalizedPiece 1 j J g x)‖ ≤
      (6 * positiveDyadicAmplitudeBound ^ 2 / ((2 : ℝ) ^ (k - 1)) ^ 2) *
        (∫ x in I.centralThird, ‖f x‖) * ∫ x in J.centralThird, ‖g x‖ := by
  have h := (krauseLaceyPositiveKernel k).norm_crossPairing_le (krauseLaceyPositiveKernel j)
    (hf.indicator I.measurableSet_centralThird) (hg.indicator J.measurableSet_centralThird)
    (by positivity : 0 ≤ 6 * positiveDyadicAmplitudeBound ^ 2 /
      ((2 : ℝ) ^ (k - 1)) ^ 2)
    (krauseLaceyPositiveKernel_mixed_adjoint_le j k hj hjk)
  simp only [FiniteRangeKernel.applyIntegral, krauseLaceyPositiveKernel_apply,
    ← krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution] at h
  simpa only [norm_indicator_eq_indicator_norm,
    integral_indicator I.measurableSet_centralThird,
    integral_indicator J.measurableSet_centralThird] using h

theorem integrable_krauseLaceyLocalizedPiece (j : ℤ) (I : RealInterval)
    {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (krauseLaceyLocalizedPiece 1 j I f) := by
  have h := (krauseLaceyPositiveKernel j).integrable_applyIntegral
    (hf.indicator I.measurableSet_centralThird)
  apply h.congr
  filter_upwards with x
  exact (krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution j I f x).symm

theorem integrable_krauseLaceyLocalizedPiece_crossPairing
    (j k : ℤ) (I J : RealInterval)
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun x ↦ krauseLaceyLocalizedPiece 1 k I f x *
      conj (krauseLaceyLocalizedPiece 1 j J g x)) := by
  have hI := integrable_krauseLaceyLocalizedPiece k I hf
  have hJ := integrable_krauseLaceyLocalizedPiece j J hg
  have hbound := (krauseLaceyPositiveKernel j).norm_applyIntegral_le
    (hg.indicator J.measurableSet_centralThird)
  simp only [FiniteRangeKernel.applyIntegral, krauseLaceyPositiveKernel_apply,
    ← krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution] at hbound
  exact hI.mul_bdd (Complex.continuous_conj.comp_aestronglyMeasurable hJ.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ by
      simpa only [RCLike.norm_conj] using hbound x)


end QuadraticCarleson
