/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.HilbertMaximalWeakOneOne
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Fourier formulas for the Poisson kernels

This module isolates the Fourier computation needed by the genuine Cotlar
inequality for the ordinary Hilbert maximal truncation.
-/

open Filter Function MeasureTheory Set FourierTransform
open scoped ENNReal Real Topology

namespace QuadraticCarleson
namespace HilbertPoissonFourier

open HilbertMaximalWeakOneOne


noncomputable section

/-- The Fourier-side Poisson semigroup multiplier in Mathlib's
`exp (-2π i x ξ)` convention. -/
def poissonSpectralKernel (r ξ : ℝ) : ℂ :=
  Complex.exp ((-2 * Real.pi * r * |ξ| : ℝ) : ℂ)

theorem continuous_poissonSpectralKernel (r : ℝ) :
    Continuous (poissonSpectralKernel r) := by
  unfold poissonSpectralKernel
  fun_prop

/-- The Poisson semigroup multiplier is integrable for every positive
radius.  This is the elementary two-half-line exponential estimate. -/
theorem integrable_poissonSpectralKernel {r : ℝ} (hr : 0 < r) :
    Integrable (poissonSpectralKernel r) := by
  have hpos : IntegrableOn
      (fun ξ : ℝ ↦ Complex.exp (((-2 * Real.pi * r : ℝ) : ℂ) * ξ)) (Ioi 0) := by
    apply integrableOn_exp_mul_complex_Ioi
    simp only [Complex.ofReal_re]
    nlinarith [Real.pi_pos]
  have hneg : IntegrableOn
      (fun ξ : ℝ ↦ Complex.exp (((2 * Real.pi * r : ℝ) : ℂ) * ξ)) (Iic 0) := by
    apply integrableOn_exp_mul_complex_Iic
    simp only [Complex.ofReal_re]
    positivity
  rw [← integrableOn_univ]
  rw [← Iic_union_Ioi (a := (0 : ℝ))]
  apply (hneg.congr_fun (fun ξ hξ ↦ by
      have hξ' : ξ ≤ 0 := hξ
      simp [poissonSpectralKernel, abs_of_nonpos hξ']) measurableSet_Iic).union
  exact hpos.congr_fun (fun ξ hξ ↦ by
      have hξ' : 0 < ξ := hξ
      simp [poissonSpectralKernel, abs_of_pos hξ']) measurableSet_Ioi

theorem memLp_two_poissonSpectralKernel {r : ℝ} (hr : 0 < r) :
    MemLp (poissonSpectralKernel r) 2 := by
  rw [memLp_two_iff_integrable_sq_norm
    (continuous_poissonSpectralKernel r).aestronglyMeasurable]
  apply (integrable_poissonSpectralKernel hr).norm.mono'
  · exact ((continuous_poissonSpectralKernel r).norm.pow 2).aestronglyMeasurable
  · filter_upwards with ξ
    have hnorm : ‖poissonSpectralKernel r ξ‖ ≤ 1 := by
      rw [poissonSpectralKernel, Complex.norm_exp, Complex.ofReal_re]
      have hnonneg : 0 ≤ 2 * Real.pi * r * |ξ| :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hr.le) (abs_nonneg ξ)
      have hnonpos : -2 * Real.pi * r * |ξ| ≤ 0 := by linarith
      exact Real.exp_le_one_iff.mpr hnonpos
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (poissonSpectralKernel r ξ)]

/-- The spectral kernel has the expected explicit `L¹` mass. -/
theorem integral_norm_poissonSpectralKernel {r : ℝ} (hr : 0 < r) :
    ∫ ξ : ℝ, ‖poissonSpectralKernel r ξ‖ = 1 / (Real.pi * r) := by
  have hpos := integral_exp_mul_Ioi (a := -2 * Real.pi * r)
    (by nlinarith [Real.pi_pos]) 0
  have hneg := integral_exp_mul_Iic (a := 2 * Real.pi * r) (by positivity) 0
  rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (integrable_poissonSpectralKernel hr).norm]
  simp only [compl_Ioi]
  rw [integral_congr_ae (show
      (fun ξ : ℝ ↦ ‖poissonSpectralKernel r ξ‖) =ᵐ[volume.restrict (Ioi 0)]
        (fun ξ ↦ Real.exp (-2 * Real.pi * r * ξ)) by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    have hξ' : 0 < ξ := hξ
    simp [poissonSpectralKernel, Complex.norm_exp, abs_of_pos hξ']), hpos]
  rw [integral_congr_ae (show
      (fun ξ : ℝ ↦ ‖poissonSpectralKernel r ξ‖) =ᵐ[volume.restrict (Iic 0)]
        (fun ξ ↦ Real.exp (2 * Real.pi * r * ξ)) by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with ξ hξ
    have hξ' : ξ ≤ 0 := hξ
    simp [poissonSpectralKernel, Complex.norm_exp, abs_of_nonpos hξ']), hneg]
  simp only [neg_div]
  field_simp
  norm_num

private def positiveHalfExponent (r w : ℝ) : ℂ :=
  ((-2 * Real.pi * r : ℝ) : ℂ) - ((2 * Real.pi * w : ℝ) : ℂ) * Complex.I

private def negativeHalfExponent (r w : ℝ) : ℂ :=
  ((2 * Real.pi * r : ℝ) : ℂ) - ((2 * Real.pi * w : ℝ) : ℂ) * Complex.I

private theorem positiveHalfExponent_re {r w : ℝ} :
    (positiveHalfExponent r w).re = -2 * Real.pi * r := by
  simp [positiveHalfExponent]

private theorem negativeHalfExponent_re {r w : ℝ} :
    (negativeHalfExponent r w).re = 2 * Real.pi * r := by
  simp [negativeHalfExponent]

/-- The elementary transform computation underlying the Poisson semigroup.
The normalization is Mathlib's `exp (-2π i x ξ)` convention. -/
theorem fourier_poissonSpectralKernel {r : ℝ} (hr : 0 < r) (w : ℝ) :
    𝓕 (poissonSpectralKernel r) w =
      ((cotlarPoissonKernel r w / Real.pi : ℝ) : ℂ) := by
  have hint : Integrable
      (fun ξ : ℝ ↦ Complex.exp ((↑(-2 * Real.pi * inner ℝ ξ w) * Complex.I)) •
        poissonSpectralKernel r ξ) :=
    by
      simpa only [Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul] using
        (Real.fourierIntegral_convergent_iff w).2 (integrable_poissonSpectralKernel hr)
  rw [Real.fourier_eq']
  rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hint]
  simp only [compl_Ioi]
  rw [integral_congr_ae (show
      (fun ξ : ℝ ↦ Complex.exp ((↑(-2 * Real.pi * inner ℝ ξ w) * Complex.I)) •
          poissonSpectralKernel r ξ) =ᵐ[volume.restrict (Ioi 0)]
        (fun ξ ↦ Complex.exp (positiveHalfExponent r w * ξ)) by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    have hξ' : 0 < ξ := hξ
    simp only [poissonSpectralKernel, abs_of_pos hξ', RCLike.inner_apply, conj_trivial]
    change Complex.exp (↑(-2 * Real.pi * (w * ξ)) * Complex.I) *
      Complex.exp ↑(-2 * Real.pi * r * ξ) = _
    rw [← Complex.exp_add]
    congr 1
    simp [positiveHalfExponent]
    ring)]
  rw [integral_exp_mul_complex_Ioi (by
    rw [positiveHalfExponent_re]
    nlinarith [Real.pi_pos]) 0]
  rw [integral_congr_ae (show
      (fun ξ : ℝ ↦ Complex.exp ((↑(-2 * Real.pi * inner ℝ ξ w) * Complex.I)) •
          poissonSpectralKernel r ξ) =ᵐ[volume.restrict (Iic 0)]
        (fun ξ ↦ Complex.exp (negativeHalfExponent r w * ξ)) by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with ξ hξ
    have hξ' : ξ ≤ 0 := hξ
    simp only [poissonSpectralKernel, abs_of_nonpos hξ', RCLike.inner_apply,
      conj_trivial]
    change Complex.exp (↑(-2 * Real.pi * (w * ξ)) * Complex.I) *
      Complex.exp ↑(-2 * Real.pi * r * -ξ) = _
    rw [← Complex.exp_add]
    congr 1
    simp [negativeHalfExponent]
    ring)]
  rw [integral_exp_mul_complex_Iic (by
    rw [negativeHalfExponent_re]
    positivity) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div, cotlarPoissonKernel]
  have hp : positiveHalfExponent r w ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp [positiveHalfExponent] at h'
    nlinarith [Real.pi_pos]
  have hn : negativeHalfExponent r w ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp [negativeHalfExponent] at h'
    nlinarith [Real.pi_pos]
  have hs : w ^ 2 + r ^ 2 ≠ 0 := by positivity
  simp only [positiveHalfExponent, negativeHalfExponent]
  push_cast
  field_simp [hp, hn, hs, Real.pi_ne_zero]
  have hm : (-(r : ℂ) - (w : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hn' : ((r : ℂ) - (w : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hs' : (r : ℂ) ^ 2 + (w : ℂ) ^ 2 ≠ 0 := by
    have hsr : r ^ 2 + w ^ 2 ≠ 0 := by positivity
    exact_mod_cast hsr
  field_simp [hm, hn', hs']
  have hs'' : (w : ℂ) ^ 2 + (r : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast hs
  field_simp [hs'']
  ring_nf
  simp

/-- The normalized positive Poisson kernel, whose integral and Fourier
multiplier both have mass one. -/
def normalizedPoissonKernel (r x : ℝ) : ℂ :=
  ((cotlarPoissonKernel r x / Real.pi : ℝ) : ℂ)

theorem integrable_cotlarPoissonKernel {r : ℝ} (hr : 0 < r) :
    Integrable (cotlarPoissonKernel r) := by
  have hr0 : r⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hr)
  have hbase : Integrable (fun x : ℝ ↦ (1 + (r⁻¹ * x) ^ 2)⁻¹) := by
    simpa only [smul_eq_mul] using integrable_inv_one_add_sq.comp_smul hr0
  have hscaled : Integrable (fun x : ℝ ↦ r⁻¹ * (1 + (r⁻¹ * x) ^ 2)⁻¹) :=
    hbase.const_mul r⁻¹
  apply hscaled.congr
  filter_upwards with x
  simp only [cotlarPoissonKernel]
  have hden : x ^ 2 + r ^ 2 ≠ 0 := by positivity
  field_simp [ne_of_gt hr, hden]
  ring

theorem integrable_normalizedPoissonKernel {r : ℝ} (hr : 0 < r) :
    Integrable (normalizedPoissonKernel r) := by
  exact ((integrable_cotlarPoissonKernel hr).mul_const Real.pi⁻¹).ofReal.congr
    (ae_of_all _ fun x ↦ by simp [normalizedPoissonKernel, div_eq_mul_inv])

theorem fourier_poissonSpectralKernel_eq_normalized {r : ℝ} (hr : 0 < r) :
    𝓕 (poissonSpectralKernel r) = normalizedPoissonKernel r := by
  funext w
  exact fourier_poissonSpectralKernel hr w

/-- Fourier inversion turns the preceding elementary half-line computation
into the usual Poisson multiplier formula. -/
theorem fourier_normalizedPoissonKernel {r : ℝ} (hr : 0 < r) (ξ : ℝ) :
    𝓕 (normalizedPoissonKernel r) ξ = poissonSpectralKernel r ξ := by
  have htransform : Integrable (𝓕 (poissonSpectralKernel r)) := by
    rw [fourier_poissonSpectralKernel_eq_normalized hr]
    exact integrable_normalizedPoissonKernel hr
  have hinv := (continuous_poissonSpectralKernel r).fourierInv_fourier_eq
    (integrable_poissonSpectralKernel hr) htransform
  have hpoint := congrFun hinv (-ξ)
  rw [fourier_poissonSpectralKernel_eq_normalized hr,
    Real.fourierInv_eq_fourier_neg] at hpoint
  simpa [poissonSpectralKernel] using hpoint

/-- The odd spectral multiplier whose inverse transform is the normalized
conjugate-Poisson kernel. -/
def conjugatePoissonSpectralKernel (r ξ : ℝ) : ℂ :=
  -Complex.I * (Real.sign ξ : ℂ) * poissonSpectralKernel r ξ

theorem integrable_conjugatePoissonSpectralKernel {r : ℝ} (hr : 0 < r) :
    Integrable (conjugatePoissonSpectralKernel r) := by
  have hm : AEStronglyMeasurable (fun ξ : ℝ ↦ -Complex.I * (Real.sign ξ : ℂ)) :=
    (measurable_const.mul
      (Complex.measurable_ofReal.comp HilbertL2Fourier.measurable_real_sign)).aestronglyMeasurable
  have hb : ∀ᵐ ξ : ℝ ∂volume, ‖-Complex.I * (Real.sign ξ : ℂ)‖ ≤ 1 := by
    filter_upwards with ξ
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real]
    exact HilbertL2Fourier.norm_real_sign_le_one ξ
  exact ((integrable_poissonSpectralKernel hr).bdd_mul hm hb).congr
    (ae_of_all _ fun ξ ↦ by simp [conjugatePoissonSpectralKernel])

private def positiveHalfInverseExponent (r x : ℝ) : ℂ :=
  ((-2 * Real.pi * r : ℝ) : ℂ) + ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I

private def negativeHalfInverseExponent (r x : ℝ) : ℂ :=
  ((2 * Real.pi * r : ℝ) : ℂ) + ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I

private theorem positiveHalfInverseExponent_re {r x : ℝ} :
    (positiveHalfInverseExponent r x).re = -2 * Real.pi * r := by
  simp [positiveHalfInverseExponent]

private theorem negativeHalfInverseExponent_re {r x : ℝ} :
    (negativeHalfInverseExponent r x).re = 2 * Real.pi * r := by
  simp [negativeHalfInverseExponent]

private theorem inv_I_mul_sub_real (r x : ℝ) :
    (Complex.I * (x : ℂ) - (r : ℂ))⁻¹ =
      ((-r : ℝ) : ℂ) / ((r ^ 2 + x ^ 2 : ℝ) : ℂ) -
        Complex.I * ((x : ℂ) / ((r ^ 2 + x ^ 2 : ℝ) : ℂ)) := by
  rw [Complex.inv_def]
  simp [Complex.normSq_apply]
  field_simp
  ring_nf

private theorem inv_I_mul_add_real (r x : ℝ) :
    (Complex.I * (x : ℂ) + (r : ℂ))⁻¹ =
      ((r : ℝ) : ℂ) / ((r ^ 2 + x ^ 2 : ℝ) : ℂ) -
        Complex.I * ((x : ℂ) / ((r ^ 2 + x ^ 2 : ℝ) : ℂ)) := by
  rw [Complex.inv_def]
  simp [Complex.normSq_apply]
  field_simp
  ring_nf

/-- The conjugate-Poisson kernel has an absolutely integrable *spectral*
representation even though the spatial kernel itself is not in `L¹`. -/
theorem fourierInv_conjugatePoissonSpectralKernel {r : ℝ} (hr : 0 < r) (x : ℝ) :
    𝓕⁻ (conjugatePoissonSpectralKernel r) x =
      ((cotlarConjugatePoissonKernel r x / Real.pi : ℝ) : ℂ) := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_eq']
  have hint : Integrable
      (fun ξ : ℝ ↦ Complex.exp
          ((↑(-2 * Real.pi * inner ℝ ξ (-x)) * Complex.I)) •
        conjugatePoissonSpectralKernel r ξ) := by
    simpa only [Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul] using
      (Real.fourierIntegral_convergent_iff (-x)).2
        (integrable_conjugatePoissonSpectralKernel hr)
  rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hint]
  simp only [compl_Ioi]
  rw [integral_congr_ae (show
      (fun ξ : ℝ ↦ Complex.exp
          ((↑(-2 * Real.pi * inner ℝ ξ (-x)) * Complex.I)) •
          conjugatePoissonSpectralKernel r ξ) =ᵐ[volume.restrict (Ioi 0)]
        (fun ξ ↦ -Complex.I * Complex.exp (positiveHalfInverseExponent r x * ξ)) by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    have hξ' : 0 < ξ := hξ
    rw [conjugatePoissonSpectralKernel, Real.sign_of_pos hξ']
    simp only [Complex.ofReal_one, mul_one, poissonSpectralKernel, abs_of_pos hξ',
      RCLike.inner_apply, conj_trivial]
    change Complex.exp (↑(-2 * Real.pi * (-x * ξ)) * Complex.I) *
      (-Complex.I * Complex.exp ↑(-2 * Real.pi * r * ξ)) = _
    rw [mul_assoc, mul_left_comm (Complex.exp _) (-Complex.I), ← Complex.exp_add]
    congr 1
    simp [positiveHalfInverseExponent]
    ring)]
  rw [integral_const_mul, integral_exp_mul_complex_Ioi (by
    rw [positiveHalfInverseExponent_re]
    nlinarith [Real.pi_pos]) 0]
  rw [integral_congr_ae (show
      (fun ξ : ℝ ↦ Complex.exp
          ((↑(-2 * Real.pi * inner ℝ ξ (-x)) * Complex.I)) •
          conjugatePoissonSpectralKernel r ξ) =ᵐ[volume.restrict (Iic 0)]
        (fun ξ ↦ Complex.I * Complex.exp (negativeHalfInverseExponent r x * ξ)) by
    filter_upwards [ae_restrict_mem measurableSet_Iic,
      (volume.restrict (Iic 0)).ae_ne 0] with ξ hξ hξne
    have hξ' : ξ ≤ 0 := hξ
    have hξneg : ξ < 0 := lt_of_le_of_ne hξ' hξne
    rw [conjugatePoissonSpectralKernel, Real.sign_of_neg hξneg]
    simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg, mul_one, neg_neg,
      poissonSpectralKernel, abs_of_nonpos hξ', RCLike.inner_apply, conj_trivial]
    change Complex.exp (↑(-2 * Real.pi * (-x * ξ)) * Complex.I) *
      (Complex.I * Complex.exp (-↑(-2 * Real.pi * r * ξ))) = _
    rw [mul_assoc, mul_left_comm (Complex.exp _) Complex.I, ← Complex.exp_add]
    congr 1
    simp [negativeHalfInverseExponent]
    ring)]
  rw [integral_const_mul, integral_exp_mul_complex_Iic (by
    rw [negativeHalfInverseExponent_re]
    positivity) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div,
    cotlarConjugatePoissonKernel]
  have hp : positiveHalfInverseExponent r x ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp [positiveHalfInverseExponent] at h'
    nlinarith [Real.pi_pos]
  have hn : negativeHalfInverseExponent r x ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp [negativeHalfInverseExponent] at h'
    nlinarith [Real.pi_pos]
  have hs : x ^ 2 + r ^ 2 ≠ 0 := by positivity
  simp only [positiveHalfInverseExponent, negativeHalfInverseExponent]
  push_cast
  field_simp [hp, hn, hs, Real.pi_ne_zero]
  have hsr : r ^ 2 + x ^ 2 ≠ 0 := by positivity
  simp only [div_eq_mul_inv, one_mul]
  rw [show -(r : ℂ) + Complex.I * (x : ℂ) =
      Complex.I * (x : ℂ) - (r : ℂ) by ring,
    show (r : ℂ) + Complex.I * (x : ℂ) =
      Complex.I * (x : ℂ) + (r : ℂ) by ring]
  rw [inv_I_mul_sub_real, inv_I_mul_add_real]
  push_cast
  field_simp [hsr]
  ring_nf
  simp

/-- An absolutely convergent spectral realization of the conjugate-Poisson
action on an `L¹` function.  The translated Fourier transform is retained
explicitly, which makes the Fubini step completely transparent. -/
noncomputable def cotlarShiftedSpectralAction
    (r : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.pi : ℂ) * ∫ ξ : ℝ,
    conjugatePoissonSpectralKernel r ξ * 𝓕 (fun z ↦ g (z + x)) ξ

theorem cotlarConjugatePoissonAction_eq_shiftedSpectral
    {r : ℝ} (hr : 0 < r) {g : ℝ → ℂ} (hg : Integrable g) (x : ℝ) :
    cotlarConjugatePoissonAction r g x =
      cotlarShiftedSpectralAction r g x := by
  have htranslate :
      (∫ y : ℝ, (cotlarConjugatePoissonKernel r (x - y) : ℂ) * g y) =
        ∫ z : ℝ, (cotlarConjugatePoissonKernel r (-z) : ℂ) * g (z + x) := by
    calc
      _ = ∫ z : ℝ,
          (cotlarConjugatePoissonKernel r (x - (z + x)) : ℂ) * g (z + x) :=
        (integral_add_right_eq_self
          (fun y : ℝ ↦ (cotlarConjugatePoissonKernel r (x - y) : ℂ) * g y) x).symm
      _ = _ := by
        congr 1
        funext z
        congr 2
        ring
  rw [cotlarConjugatePoissonAction, htranslate, cotlarShiftedSpectralAction]
  have hpoint : ∀ z : ℝ,
      (cotlarConjugatePoissonKernel r (-z) : ℂ) =
        (Real.pi : ℂ) * 𝓕 (conjugatePoissonSpectralKernel r) z := by
    intro z
    have h := fourierInv_conjugatePoissonSpectralKernel hr (-z)
    rw [Real.fourierInv_eq_fourier_neg] at h
    simp only [neg_neg] at h
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [h]
    push_cast
    field_simp [hpi]
  calc
    ∫ z : ℝ, (cotlarConjugatePoissonKernel r (-z) : ℂ) * g (z + x) =
        ∫ z : ℝ, (Real.pi : ℂ) *
          (𝓕 (conjugatePoissonSpectralKernel r) z * g (z + x)) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [hpoint]
      ring
    _ = (Real.pi : ℂ) * ∫ z : ℝ,
        𝓕 (conjugatePoissonSpectralKernel r) z * g (z + x) := by
      rw [integral_const_mul]
    _ = (Real.pi : ℂ) * ∫ ξ : ℝ,
        conjugatePoissonSpectralKernel r ξ * 𝓕 (fun z ↦ g (z + x)) ξ := by
      congr 1
      have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner
        (integrable_conjugatePoissonSpectralKernel hr) (hg.comp_add_right x)
      have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
        ext
        simp
      rw [hflip] at hswap
      change (∫ z : ℝ,
          VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
            (conjugatePoissonSpectralKernel r) z * g (z + x)) =
        ∫ ξ : ℝ, conjugatePoissonSpectralKernel r ξ *
          VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
            (fun z ↦ g (z + x)) ξ
      simpa only [smul_eq_mul, mul_comm] using hswap

theorem fourier_comp_add_right_real (g : ℝ → ℂ) (x ξ : ℝ) :
    𝓕 (fun z ↦ g (z + x)) ξ =
      Real.fourierChar (x * ξ) • 𝓕 g ξ := by
  have h := VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ ℝ) g x
  have hξ := congrFun h ξ
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
      (fun z ↦ g (z + x)) ξ = Real.fourierChar (x * ξ) •
        VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) g ξ
  have hi : ((innerₗ ℝ) x) ξ = x * ξ := by
    change ξ * x = x * ξ
    ring
  rw [hi] at hξ
  exact hξ

/-- The common spectral expression for the conjugate-Poisson convolution
and the Poisson smoothing of the Hilbert multiplier. -/
noncomputable def cotlarHilbertSpectralAction
    (r : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ ξ : ℝ, Real.fourierChar (x * ξ) •
    (poissonSpectralKernel r ξ *
      HilbertL2Fourier.ordinaryHilbertMultiplier ξ * 𝓕 g ξ)

theorem pi_mul_conjugatePoissonSpectralKernel (r ξ : ℝ) :
    (Real.pi : ℂ) * conjugatePoissonSpectralKernel r ξ =
      poissonSpectralKernel r ξ *
        HilbertL2Fourier.ordinaryHilbertMultiplier ξ := by
  simp only [conjugatePoissonSpectralKernel,
    HilbertL2Fourier.ordinaryHilbertMultiplier]
  ring

/-- Exact absolutely convergent Fourier intertwining on every `L¹` input:
conjugate-Poisson convolution equals the inverse spectral action obtained by
Poisson damping the ordinary Hilbert multiplier. -/
theorem cotlarConjugatePoissonAction_eq_hilbertSpectral
    {r : ℝ} (hr : 0 < r) {g : ℝ → ℂ} (hg : Integrable g) (x : ℝ) :
    cotlarConjugatePoissonAction r g x =
      cotlarHilbertSpectralAction r g x := by
  rw [cotlarConjugatePoissonAction_eq_shiftedSpectral hr hg x]
  simp only [cotlarShiftedSpectralAction, cotlarHilbertSpectralAction,
    fourier_comp_add_right_real]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [Circle.smul_def]
  rw [← pi_mul_conjugatePoissonSpectralKernel]
  ring

/-- The preceding Fourier intertwining specialized to the canonical stopping
good part used in the Cotlar reduction. -/
theorem cotlarConjugatePoissonAction_stoppingGoodPart_eq_hilbertSpectral
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {r : ℝ} (hr : 0 < r) (x : ℝ) :
    cotlarConjugatePoissonAction r
        (CalderonZygmundDyadicStopping.stoppingGoodPart f) x =
      cotlarHilbertSpectralAction r
        (CalderonZygmundDyadicStopping.stoppingGoodPart f) x :=
  cotlarConjugatePoissonAction_eq_hilbertSpectral hr
    (integrable_stoppingGoodPart_for_hilbert hf hfi) x


end
end HilbertPoissonFourier
end QuadraticCarleson
