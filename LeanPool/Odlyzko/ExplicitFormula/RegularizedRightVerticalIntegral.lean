/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedDigammaVerticalIntegral
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPrimePowerSeriesIntegral
public import LeanPool.Odlyzko.ExplicitFormula.RightVerticalExpansion

/-!
# Regularized Right Vertical Integral

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Ideal IsDedekindDomain MeasureTheory Real Set
open NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem integrable_poitouTransform_regularized_mul_neg_logDeriv_dedekindZeta
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun t : ℝ ↦
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (-logDeriv (dedekindZeta K) (σ + t * I))) := by
  let Φ : ℝ → ℂ := fun t ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I)
  let G : ℝ → ℂ := fun t ↦
    ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
      primePowerLogTerm K pe.1 pe.2 (σ + t * I)
  let b : HeightOneSpectrum (𝓞 K) × ℕ → ℝ := fun pe ↦
    ‖primePowerLogTerm K pe.1 pe.2 (σ : ℂ)‖
  have hΦ : Integrable Φ :=
    poitouTransform_regularizedScaledTartar_vertical_integrable hδ y σ
  have hGmeas : Measurable G := by
    dsimp only [G]
    apply Measurable.tsum
    intro pe
    rw [show
        (fun t : ℝ ↦ primePowerLogTerm K pe.1 pe.2 (σ + t * I)) =
          fun t : ℝ ↦
            (Real.log (primeIdealNorm K pe.1) : ℂ) *
              Complex.exp
                (-(((pe.2 + 1 : ℕ) : ℝ) *
                  Real.log (primeIdealNorm K pe.1)) * (σ + t * I)) by
      funext t
      exact primePowerLogTerm_eq_log_mul_cexp_neg K pe.1 pe.2 _]
    fun_prop
  have hGbound : ∀ t : ℝ, ‖G t‖ ≤ ∑' pe, b pe := by
    intro t
    apply (norm_tsum_le_tsum_norm
      (summable_norm_primePowerLogTerm K
        (s := (σ + t * I : ℂ)) (by simpa using hσ))).trans_eq
    congr 1
    funext pe
    dsimp only [b]
    rw [norm_primePowerLogTerm, norm_primePowerLogTerm]
    simp
  have hprod : Integrable (fun t ↦ Φ t * G t) :=
    hΦ.mul_bdd hGmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hGbound)
  apply hprod.congr
  filter_upwards [] with t
  have hst : 1 < (σ + t * I : ℂ).re := by simpa using hσ
  rw [neg_logDeriv_dedekindZeta_eq_tsum_primePower K hst]

variable [IsTotallyComplex K]

theorem integrable_poitouTransform_regularized_mul_logDeriv_sub_poles
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun t : ℝ ↦
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (σ + t * I) -
          completedZetaPoleLogDeriv (σ + t * I))) := by
  let Φ : ℝ → ℂ := fun t ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I)
  have hΦ : Integrable Φ :=
    poitouTransform_regularizedScaledTartar_vertical_integrable hδ y σ
  have hEuler :
      Integrable (fun t : ℝ ↦
        Φ t * (Complex.digamma (σ + t * I) +
          Real.eulerMascheroniConstant)) :=
    integrable_poitouTransform_regularized_mul_digamma_add_euler
      hδ y (zero_lt_one.trans hσ)
  have hDig :
      Integrable (fun t : ℝ ↦
        Φ t * (Complex.digamma (σ + t * I) -
          Complex.log (2 * (Real.pi : ℂ)))) := by
    have hconst :=
      hΦ.mul_const
        (Real.eulerMascheroniConstant +
          Complex.log (2 * (Real.pi : ℂ)))
    apply (hEuler.sub hconst).congr
    filter_upwards [] with t
    change
      Φ t * (Complex.digamma (σ + t * I) +
          Real.eulerMascheroniConstant) -
        Φ t * (Real.eulerMascheroniConstant +
          Complex.log (2 * (Real.pi : ℂ))) =
        Φ t * (Complex.digamma (σ + t * I) -
          Complex.log (2 * (Real.pi : ℂ)))
    ring
  have hdisc :
      Integrable (fun t : ℝ ↦
        Φ t * ((Real.log |(discr K : ℝ)| : ℂ) / 2)) :=
    hΦ.mul_const _
  have harch :
      Integrable (fun t : ℝ ↦
        Φ t * (nrComplexPlaces K *
          (Complex.digamma (σ + t * I) -
            Complex.log (2 * (Real.pi : ℂ))))) := by
    apply hDig.const_mul (nrComplexPlaces K) |>.congr
    filter_upwards [] with t
    ring
  have hneg :=
    integrable_poitouTransform_regularized_mul_neg_logDeriv_dedekindZeta
      K hδ y hσ
  have hzeta :
      Integrable (fun t : ℝ ↦
        Φ t * logDeriv (dedekindZeta K) (σ + t * I)) := by
    apply hneg.neg.congr
    filter_upwards [] with t
    change
      -(Φ t * (-logDeriv (dedekindZeta K) (σ + t * I))) =
        Φ t * logDeriv (dedekindZeta K) (σ + t * I)
    ring
  apply (hdisc.add harch |>.add hzeta).congr
  filter_upwards [] with t
  rw [logDeriv_poleClearedContinuation_sub_poles_eq_logDeriv_dedekindZeta
    K (by simpa using hσ)]
  change
    (Φ t * ((Real.log |(discr K : ℝ)| : ℂ) / 2) +
      Φ t * (nrComplexPlaces K *
        (Complex.digamma (σ + t * I) -
          Complex.log (2 * (Real.pi : ℂ))))) +
      Φ t * logDeriv (dedekindZeta K) (σ + t * I) = _
  grind

theorem integral_poitouTransform_regularized_mul_logDeriv_sub_poles
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (σ + t * I) -
          completedZetaPoleLogDeriv (σ + t * I))) =
      (2 * Real.pi : ℂ) *
          ((Real.log |(discr K : ℝ)| : ℂ) / 2) +
        nrComplexPlaces K *
          ((∫ x : ℝ in Ioi 0,
              ((2 * Real.pi *
                inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ)) -
            (2 * Real.pi : ℂ) *
              (Real.eulerMascheroniConstant +
                Complex.log (2 * (Real.pi : ℂ)))) -
        ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          ((2 * Real.pi *
            regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 : ℝ) : ℂ) := by
  let Φ : ℝ → ℂ := fun t ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I)
  let A : ℝ → ℂ := fun t ↦
    Φ t * ((Real.log |(discr K : ℝ)| : ℂ) / 2)
  let B : ℝ → ℂ := fun t ↦
    Φ t * (nrComplexPlaces K *
      (Complex.digamma (σ + t * I) -
        Complex.log (2 * (Real.pi : ℂ))))
  let C : ℝ → ℂ := fun t ↦
    Φ t * logDeriv (dedekindZeta K) (σ + t * I)
  have hΦ : Integrable Φ :=
    poitouTransform_regularizedScaledTartar_vertical_integrable hδ y σ
  have hEuler :
      Integrable (fun t : ℝ ↦
        Φ t * (Complex.digamma (σ + t * I) +
          Real.eulerMascheroniConstant)) :=
    integrable_poitouTransform_regularized_mul_digamma_add_euler
      hδ y (zero_lt_one.trans hσ)
  have hDig :
      Integrable (fun t : ℝ ↦
        Φ t * (Complex.digamma (σ + t * I) -
          Complex.log (2 * (Real.pi : ℂ)))) := by
    have hconst :=
      hΦ.mul_const
        (Real.eulerMascheroniConstant +
          Complex.log (2 * (Real.pi : ℂ)))
    apply (hEuler.sub hconst).congr
    filter_upwards [] with t
    change
      Φ t * (Complex.digamma (σ + t * I) +
          Real.eulerMascheroniConstant) -
        Φ t * (Real.eulerMascheroniConstant +
          Complex.log (2 * (Real.pi : ℂ))) =
        Φ t * (Complex.digamma (σ + t * I) -
          Complex.log (2 * (Real.pi : ℂ)))
    ring
  have hA : Integrable A := hΦ.mul_const _
  have hB : Integrable B := by
    apply hDig.const_mul (nrComplexPlaces K)
      |>.congr
    filter_upwards [] with t
    grind
  have hneg :=
    integrable_poitouTransform_regularized_mul_neg_logDeriv_dedekindZeta
      K hδ y hσ
  have hC : Integrable C := by
    apply hneg.neg.congr
    filter_upwards [] with t
    change
      -(Φ t * (-logDeriv (dedekindZeta K) (σ + t * I))) =
        C t
    grind
  have hdecomp :
      (fun t : ℝ ↦
        Φ t *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (σ + t * I) -
            completedZetaPoleLogDeriv (σ + t * I))) =
        fun t ↦ A t + B t + C t := by
    funext t
    rw [logDeriv_poleClearedContinuation_sub_poles_eq_logDeriv_dedekindZeta
      K (by simpa using hσ)]
    grind
  have hDigValue :
      (∫ t : ℝ,
        Φ t * (Complex.digamma (σ + t * I) -
          Complex.log (2 * (Real.pi : ℂ)))) =
        (∫ x : ℝ in Ioi 0,
          ((2 * Real.pi *
            inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ)) -
        (2 * Real.pi : ℂ) *
          (Real.eulerMascheroniConstant +
            Complex.log (2 * (Real.pi : ℂ))) := by
    have harch :=
      integral_poitouTransform_regularized_mul_digamma_add_euler
        hδ y (zero_lt_one.trans hσ)
    have hmass :=
      integral_poitouTransform_regularized_vertical hδ y σ
    have hconstValue :
        (∫ t : ℝ,
          Φ t * (Real.eulerMascheroniConstant +
            Complex.log (2 * (Real.pi : ℂ)))) =
          (2 * Real.pi : ℂ) *
            (Real.eulerMascheroniConstant +
              Complex.log (2 * (Real.pi : ℂ))) := by
      rw [integral_mul_const, hmass]
    rw [← harch, ← hconstValue, ← integral_sub hEuler
      (hΦ.mul_const
        (Real.eulerMascheroniConstant +
          Complex.log (2 * (Real.pi : ℂ))))]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  rw [show
      (fun t : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (σ + t * I) -
            completedZetaPoleLogDeriv (σ + t * I))) =
        fun t ↦ A t + B t + C t by
      grind]
  change
    (∫ t : ℝ, (A + B) t + C t) =
      (2 * Real.pi : ℂ) *
          ((Real.log |(discr K : ℝ)| : ℂ) / 2) +
        nrComplexPlaces K *
          ((∫ x : ℝ in Ioi 0,
              ((2 * Real.pi *
                inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ)) -
            (2 * Real.pi : ℂ) *
              (Real.eulerMascheroniConstant +
                Complex.log (2 * (Real.pi : ℂ)))) -
        ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          ((2 * Real.pi *
            regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 : ℝ) : ℂ)
  rw [integral_add (hA.add hB) hC]
  change
    ((∫ t : ℝ, A t + B t) + ∫ t : ℝ, C t) = _
  rw [integral_add hA hB]
  have hmass :=
    integral_poitouTransform_regularized_vertical hδ y σ
  have hprime :=
    integral_poitouTransform_regularized_mul_neg_logDeriv_dedekindZeta_eq_tsum
      K hδ y hσ
  dsimp only [A, B, C]
  rw [integral_mul_const, hmass]
  rw [show
      (fun t : ℝ ↦
        Φ t * (nrComplexPlaces K *
          (Complex.digamma (σ + t * I) -
            Complex.log (2 * (Real.pi : ℂ))))) =
        fun t ↦ (nrComplexPlaces K : ℂ) *
          (Φ t * (Complex.digamma (σ + t * I) -
            Complex.log (2 * (Real.pi : ℂ)))) by
      grind,
    integral_const_mul, hDigValue]
  have hCvalue :
      (∫ t : ℝ,
        Φ t * logDeriv (dedekindZeta K) (σ + t * I)) =
        -(∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          ((2 * Real.pi *
            regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 : ℝ) : ℂ)) := by
    rw [← hprime, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  grind

theorem re_integral_poitouTransform_regularized_mul_logDeriv_sub_poles
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (σ + t * I) -
          completedZetaPoleLogDeriv (σ + t * I))).re =
      2 * Real.pi *
        (Real.log |(discr K : ℝ)| / 2 +
          nrComplexPlaces K *
            ((∫ x : ℝ in Ioi 0,
                inverseGaussKernel (regularizedScaledTartar y δ) x) -
              Real.eulerMascheroniConstant -
              Real.log (2 * Real.pi)) -
          ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
            regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2) := by
  have h :=
    integral_poitouTransform_regularized_mul_logDeriv_sub_poles
      K hδ y hσ
  have hlog :
      Complex.log (2 * (Real.pi : ℂ)) =
        (Real.log (2 * Real.pi) : ℂ) := by
    rw [show 2 * (Real.pi : ℂ) =
        ((2 * Real.pi : ℝ) : ℂ) by
      simp]
    exact (Complex.ofReal_log (by positivity)).symm
  have hintegral :
      (∫ x : ℝ in Ioi 0,
        ((2 * Real.pi *
          inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ)) =
        ((∫ x : ℝ in Ioi 0,
          2 * Real.pi *
            inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ) :=
    integral_ofReal
  rw [hlog] at h
  rw [hintegral] at h
  rw [← Complex.ofReal_tsum
    (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
      2 * Real.pi *
        regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2)] at h
  have hscale :
      (∫ x : ℝ in Ioi 0,
        2 * Real.pi *
          inverseGaussKernel (regularizedScaledTartar y δ) x) =
        2 * Real.pi *
          ∫ x : ℝ in Ioi 0,
            inverseGaussKernel (regularizedScaledTartar y δ) x := by
    rw [integral_const_mul]
  rw [hscale, tsum_mul_left] at h
  push_cast at h
  have hre := congrArg Complex.re h
  have hweights :
      Summable (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
        regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2) :=
    summable_regularizedPrimePowerPoitouWeight K hδ y hσ
  have hweightsC :
      Summable (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
        ((regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr hweights
  simp only [mul_re, mul_im, add_re, add_im, sub_re, sub_im, div_re, ofReal_re, ofReal_im,
    mul_zero, zero_mul, sub_zero, add_zero, natCast_re, natCast_im] at hre
  rw [Complex.re_tsum hweightsC] at hre
  rw [Complex.im_tsum hweightsC] at hre
  simp only [ofReal_re, ofReal_im] at hre
  have htwoRe : (2 : ℂ).re = 2 := by norm_num
  have htwoIm : (2 : ℂ).im = 0 := by norm_num
  have htwoNormSq : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq]
  grind

end NumberField.Odlyzko
