/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaCenterLogBound
public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaRectangle
public import LeanPool.Odlyzko.ExplicitFormula.FiniteSetAvoidance
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouContourLimit
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouQuadraticDecay
public import LeanPool.Odlyzko.ExplicitFormula.ZeroFreeRectangles
public import LeanPool.Odlyzko.FromPrimeNumberTheoremAnd.RectangleIntegral
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Poitou Estimate

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

section

open Complex Filter MeasureTheory
open scoped FourierTransform Real Topology

namespace NumberField.Odlyzko

theorem sq_abs_mul_norm_poitouTransform_regularized_eq_norm_fourier_second
    {δ : ℝ} (hδ : 0 < δ) (y σ t : ℝ) :
    |t| ^ 2 *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ =
      ‖𝓕 (poitouVerticalProfileSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) σ)
        (-t / (2 * Real.pi))‖ := by
  let w : ℝ := -t / (2 * Real.pi)
  have hfourier :=
    fourier_poitouVerticalProfileSecondDerivative_regularized_eq_sq
      hδ y σ w
  have hfactor :
      ‖(((2 * Real.pi : ℂ) * I * (w : ℂ)) ^ 2)‖ = |t| ^ 2 := by
    rw [norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs]
    dsimp [w]
    norm_num
    field_simp [Real.pi_ne_zero]
    simp
  have hnorm :
      |t| ^ 2 * ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ =
        ‖𝓕 (poitouVerticalProfileSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) σ) w‖ := by simp_all
  rw [poitouTransform_regularizedScaledTartar_eq_fourier]
  grind

theorem tendsto_sq_abs_mul_norm_poitouTransform_regularized_atTop
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    Tendsto
      (fun t : ℝ ↦ |t| ^ 2 *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖)
      atTop (𝓝 0) := by
  let f : ℝ → ℂ :=
    poitouVerticalProfileSecondDerivative
      (regularizedScaledTartar y δ)
      (regularizedScaledTartarDerivative y δ)
      (regularizedScaledTartarSecondDerivative y δ) σ
  have hfourier :
      Tendsto (fun t : ℝ ↦ 𝓕 f (-t / (2 * Real.pi)))
        atTop (𝓝 0) := by
    have hzero := Real.zero_at_infty_fourier f
    have hfreq :
        Tendsto (fun t : ℝ ↦ (-1 / (2 * Real.pi)) * t)
          atTop (cocompact ℝ) :=
      (Filter.tendsto_cocompact_mul_left₀
        (show (-1 / (2 * Real.pi) : ℝ) ≠ 0 by positivity)).comp
        atTop_le_cocompact
    convert hzero.comp hfreq using 1
    grind
  have hnorm :
      Tendsto (fun t : ℝ ↦ ‖𝓕 f (-t / (2 * Real.pi))‖)
        atTop (𝓝 0) := by
    have h :=
      continuous_norm.continuousAt.tendsto.comp hfourier
    change Tendsto (fun t : ℝ ↦ ‖𝓕 f (-t / (2 * Real.pi))‖)
      atTop (𝓝 ‖(0 : ℂ)‖) at h
    simpa using h
  convert hnorm using 1
  funext t
  exact sq_abs_mul_norm_poitouTransform_regularized_eq_norm_fourier_second
    hδ y σ t

theorem tendsto_sq_abs_mul_norm_poitouTransform_regularized_atBot
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    Tendsto
      (fun t : ℝ ↦ |t| ^ 2 *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖)
      atBot (𝓝 0) := by
  let f : ℝ → ℂ :=
    poitouVerticalProfileSecondDerivative
      (regularizedScaledTartar y δ)
      (regularizedScaledTartarDerivative y δ)
      (regularizedScaledTartarSecondDerivative y δ) σ
  have hzero := Real.zero_at_infty_fourier f
  have hfreq :
      Tendsto (fun t : ℝ ↦ (-1 / (2 * Real.pi)) * t)
        atBot (cocompact ℝ) :=
    (Filter.tendsto_cocompact_mul_left₀
      (show (-1 / (2 * Real.pi) : ℝ) ≠ 0 by positivity)).comp
      atBot_le_cocompact
  have hfourier :
      Tendsto (fun t : ℝ ↦ 𝓕 f (-t / (2 * Real.pi)))
        atBot (𝓝 0) := by
    convert hzero.comp hfreq using 1
    grind
  have hnorm :
      Tendsto (fun t : ℝ ↦ ‖𝓕 f (-t / (2 * Real.pi))‖)
        atBot (𝓝 0) := by
    have h := continuous_norm.continuousAt.tendsto.comp hfourier
    change Tendsto (fun t : ℝ ↦ ‖𝓕 f (-t / (2 * Real.pi))‖)
      atBot (𝓝 ‖(0 : ℂ)‖) at h
    simpa using h
  convert hnorm using 1
  funext t
  exact sq_abs_mul_norm_poitouTransform_regularized_eq_norm_fourier_second
    hδ y σ t

end NumberField.Odlyzko

end

section

open Complex MeasureTheory Real

namespace NumberField.Odlyzko

/-- A regularized poitou profile second derivative majorant used in the Odlyzko-bound argument. -/
noncomputable def regularizedPoitouProfileSecondDerivativeMajorant
    (y δ M x : ℝ) : ℝ :=
  Real.exp (M ^ 2 / (2 * δ)) *
    ((y ^ 2 * tartarTestFunctionSecondDerivativeBound + 2 * δ +
        2 * |y| * tartarAmplitudeDerivativeBound + 3 / 4 +
        2 * M * (2 * |y| * tartarAmplitudeDerivativeBound + 1 / 2) +
        M ^ 2 +
        (8 * δ * |y| * tartarAmplitudeDerivativeBound +
          2 * δ + 4 * M * δ) * |x| +
        4 * δ ^ 2 * x ^ 2) *
      Real.exp (-(δ / 2) * x ^ 2))

/-- A regularized poitou strip quadratic decay constant used in the Odlyzko-bound argument. -/
noncomputable def regularizedPoitouStripQuadraticDecayConstant
    (y δ a b : ℝ) : ℝ :=
  ∫ x : ℝ, regularizedPoitouProfileSecondDerivativeMajorant y δ
    (max |a - 1 / 2| |b - 1 / 2|) x

theorem regularizedPoitouProfileSecondDerivativeMajorant_integrable
    {δ : ℝ} (hδ : 0 < δ) (y M : ℝ) :
    Integrable (regularizedPoitouProfileSecondDerivativeMajorant y δ M) := by
  let A :=
    y ^ 2 * tartarTestFunctionSecondDerivativeBound + 2 * δ +
      2 * |y| * tartarAmplitudeDerivativeBound + 3 / 4 +
      2 * M * (2 * |y| * tartarAmplitudeDerivativeBound + 1 / 2) +
      M ^ 2
  let B :=
    8 * δ * |y| * tartarAmplitudeDerivativeBound +
      2 * δ + 4 * M * δ
  let C := 4 * δ ^ 2
  have hquad :=
    integrable_quadratic_abs_mul_exp_neg_mul_sq
      (show 0 < δ / 2 by positivity) A B C
  have hconst :
      Integrable (fun x : ℝ ↦
        Real.exp (M ^ 2 / (2 * δ)) *
          ((A + B * |x| + C * x ^ 2) *
            Real.exp (-(δ / 2) * x ^ 2))) :=
    hquad.const_mul _
  apply hconst.congr
  filter_upwards with x
  unfold regularizedPoitouProfileSecondDerivativeMajorant
  grind

theorem norm_poitouVerticalProfileSecondDerivative_regularized_le_majorant
    {δ M : ℝ} (hδ : 0 < δ) (_hM : 0 ≤ M)
    (y : ℝ) {σ : ℝ} (hσ : |σ - 1 / 2| ≤ M) (x : ℝ) :
    ‖poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ x‖ ≤
      regularizedPoitouProfileSecondDerivativeMajorant y δ M x := by
  refine (norm_poitouVerticalProfileSecondDerivative_regularized_le
    hδ y σ x).trans ?_
  unfold regularizedPoitouProfileSecondDerivativeMajorant
  have hA := tartarAmplitudeDerivativeBound_nonneg
  have hA₂ := tartarTestFunctionSecondDerivativeBound_nonneg
  have hexp :
      Real.exp (|σ - 1 / 2| ^ 2 / (2 * δ)) ≤
        Real.exp (M ^ 2 / (2 * δ)) := by
    gcongr
  apply mul_le_mul
  · simp_all
  · gcongr
  · positivity
  · positivity

theorem sq_abs_mul_norm_poitouTransform_regularized_le_strip
    {δ a b : ℝ} (hδ : 0 < δ) (y t : ℝ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc a b) :
    |t| ^ 2 *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ ≤
      ∫ x : ℝ, regularizedPoitouProfileSecondDerivativeMajorant y δ
        (max |a - 1 / 2| |b - 1 / 2|) x := by
  refine (sq_abs_mul_norm_poitouTransform_regularized_le hδ y σ t).trans ?_
  apply integral_mono
  · exact (poitouVerticalProfileSecondDerivative_regularized_integrable
      hδ y σ).norm
  · exact regularizedPoitouProfileSecondDerivativeMajorant_integrable hδ y _
  · intro x
    apply norm_poitouVerticalProfileSecondDerivative_regularized_le_majorant
      hδ ((abs_nonneg (a - 1 / 2)).trans (le_max_left _ _)) y
    grind

end NumberField.Odlyzko

end

section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- Absolute ordinates, in prescribed bands, of zeros of the completed Dedekind zeta function. -/
noncomputable def completedDedekindZetaZeroAbsoluteOrdinatesInBands
    (a b U V : ℝ) : Finset ℝ :=
  ((completedDedekindZetaZerosInClosedRectangle K a b (-V) V).filter
      fun z ↦ U ≤ |z.im|).image fun z ↦ |z.im|

open Classical in
theorem exists_completedZeta_height_separated_from_zeros_in_bands
    (a b U : ℝ) {A L V : ℝ} (hA : 0 ≤ A) (hL : 0 < L) :
    ∃ T : ℝ, A < T ∧ T < A + L ∧
      ∀ z : ℂ,
        z.re ∈ Icc a b →
        |z.im| ∈ Icc U V →
        poleClearedCompletedDedekindZetaContinuation K z = 0 →
        finiteSetAvoidanceRadiusOnLength L
            (completedDedekindZetaZeroAbsoluteOrdinatesInBands K a b U V) ≤
          |T - z.im| ∧
        finiteSetAvoidanceRadiusOnLength L
            (completedDedekindZetaZeroAbsoluteOrdinatesInBands K a b U V) ≤
          |-T - z.im| := by
  let S := completedDedekindZetaZeroAbsoluteOrdinatesInBands K a b U V
  obtain ⟨T, hT, hsep⟩ :=
    exists_mem_Ioo_abs_sub_ge_finiteSetAvoidanceRadiusOnLength S A hL
  refine ⟨T, hT.1, hT.2, ?_⟩
  intro z hzre hzim hzzero
  have hzrect :
      z ∈ completedDedekindZetaZerosInClosedRectangle K a b (-V) V := by
    apply (mem_completedDedekindZetaZerosInClosedRectangle_iff K).mpr
    refine ⟨⟨hzre, ?_⟩,
      mem_completedDedekindZetaZeroDivisor_support_of_eq_zero K hzzero⟩
    grind
  have hzS : |z.im| ∈ S := by
    apply Finset.mem_image.mpr
    grind
  grind

end NumberField.Odlyzko

end

section

open Complex NumberField Metric Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A completed zeta selected height ordinates used in the Odlyzko-bound argument. -/
noncomputable def completedZetaSelectedHeightOrdinates (A : ℝ) : Finset ℝ :=
  completedDedekindZetaZeroAbsoluteOrdinatesInBands K (-3) 7 (A - 5) (A + 6)

open Classical in
/-- A completed zeta selected height separation used in the Odlyzko-bound argument. -/
noncomputable def completedZetaSelectedHeightSeparation (A : ℝ) : ℝ :=
  finiteSetAvoidanceRadiusOnLength 1
    (completedZetaSelectedHeightOrdinates K A)

omit [IsTotallyComplex K] in
open Classical in
theorem completedZetaSelectedHeightSeparation_pos (A : ℝ) :
    0 < completedZetaSelectedHeightSeparation K A :=
  finiteSetAvoidanceRadiusOnLength_pos one_pos _

omit [IsTotallyComplex K] in
open Classical in
private theorem horizontal_segment_separated_from_local_zeros
    {A t δ : ℝ} (hAt : A < |t|) (htA : |t| < A + 1)
    (hzeroSep : ∀ p : ℂ,
      p.re ∈ Icc (-3 : ℝ) 7 →
      |p.im| ∈ Icc (A - 5) (A + 6) →
      poleClearedCompletedDedekindZetaContinuation K p = 0 →
      δ ≤ |t - p.im|)
    {x : ℝ} (_hx : x ∈ Icc (-1 : ℝ) 5) :
    ∀ p ∈ ball (2 + t * I) 5,
      poleClearedCompletedDedekindZetaContinuation K p = 0 →
      δ ≤ ‖(x + t * I) - p‖ := by
  intro p hp hpzero
  have hdist : ‖p - (2 + t * I)‖ < 5 := by
    simpa [mem_ball, dist_eq, norm_sub_rev] using hp
  have hreDist : |p.re - 2| < 5 := by
    simpa using
      (Complex.abs_re_le_norm (p - (2 + t * I))).trans_lt hdist
  have himDist : |p.im - t| < 5 := by
    simpa using
      (Complex.abs_im_le_norm (p - (2 + t * I))).trans_lt hdist
  have hpRe : p.re ∈ Icc (-3 : ℝ) 7 := by
    grind
  have habsLower : A - 5 ≤ |p.im| := by
    grind
  have habsUpper : |p.im| ≤ A + 6 := by grind
  have hvertical : δ ≤ |t - p.im| :=
    hzeroSep p hpRe ⟨habsLower, habsUpper⟩ hpzero
  exact hvertical.trans (by
    have himNorm := Complex.abs_im_le_norm ((x + t * I : ℂ) - p)
    simpa using himNorm)

open Classical in
theorem exists_height_norm_logDeriv_poleClearedCompletedZeta_le
    {A : ℝ} (hA : 6 ≤ A) :
    ∃ T : ℝ, A < T ∧ T < A + 1 ∧
      ∀ x ∈ Icc (-1 : ℝ) 5,
        (poleClearedCompletedDedekindZetaContinuation K (x + T * I) ≠ 0 ∧
        ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
            (x + T * I)‖ ≤
          (completedZetaCenterLogLinearBound K T *
                completedZetaCanonicalJensenCoefficient /
              completedZetaSelectedHeightSeparation K A +
            completedZetaCenterLogLinearBound K T *
              completedZetaCanonicalJensenCoefficient) +
            32 * completedZetaCenterLogLinearBound K T) ∧
        (poleClearedCompletedDedekindZetaContinuation K (x - T * I) ≠ 0 ∧
        ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
            (x - T * I)‖ ≤
          (completedZetaCenterLogLinearBound K (-T) *
                completedZetaCanonicalJensenCoefficient /
              completedZetaSelectedHeightSeparation K A +
            completedZetaCenterLogLinearBound K (-T) *
              completedZetaCanonicalJensenCoefficient) +
            32 * completedZetaCenterLogLinearBound K (-T)) := by
  let δ := completedZetaSelectedHeightSeparation K A
  obtain ⟨T, hAT, hTA, hsep⟩ :=
    exists_completedZeta_height_separated_from_zeros_in_bands
      K (-3) 7 (A - 5) (A := A) (L := 1) (V := A + 6)
      (by linarith) one_pos
  have hδ : 0 < δ := completedZetaSelectedHeightSeparation_pos K A
  have hsepPlus :
      ∀ p : ℂ, p.re ∈ Icc (-3 : ℝ) 7 →
        |p.im| ∈ Icc (A - 5) (A + 6) →
        poleClearedCompletedDedekindZetaContinuation K p = 0 →
        δ ≤ |T - p.im| := by
    intro p hpRe hpIm hpzero
    exact (hsep p hpRe hpIm hpzero).1
  have hsepMinus :
      ∀ p : ℂ, p.re ∈ Icc (-3 : ℝ) 7 →
        |p.im| ∈ Icc (A - 5) (A + 6) →
        poleClearedCompletedDedekindZetaContinuation K p = 0 →
        δ ≤ |-T - p.im| := by
    intro p hpRe hpIm hpzero
    exact (hsep p hpRe hpIm hpzero).2
  refine ⟨T, hAT, hTA, ?_⟩
  intro x hx
  have hxabs : |x - 2| ≤ 3 := by grind
  have hnormPlus :
      ‖(x + T * I : ℂ) - (2 + T * I)‖ ≤ 3 := by
    rw [show (x + T * I : ℂ) - (2 + T * I) = ((x - 2 : ℝ) : ℂ) by
      simp, Complex.norm_real]
    exact hxabs
  have hnormMinus :
      ‖(x - T * I : ℂ) - (2 + ((-T : ℝ) : ℂ) * I)‖ ≤ 3 := by
    rw [show (x - T * I : ℂ) - (2 + ((-T : ℝ) : ℂ) * I) =
        ((x - 2 : ℝ) : ℂ) by
      push_cast
      ring, Complex.norm_real]
    exact hxabs
  have hzPlus : x + T * I ∈ closedBall (2 + T * I) 3 := by
    rw [mem_closedBall, dist_eq]
    simp_all
  have hzMinus :
      x - T * I ∈ closedBall (2 + ((-T : ℝ) : ℂ) * I) 3 := by simp_all
  have hlocalPlus :=
    horizontal_segment_separated_from_local_zeros K
      (A := A) (t := T) (δ := δ)
      (by grind) (by grind)
      hsepPlus hx
  have hlocalMinus :=
    horizontal_segment_separated_from_local_zeros K
      (A := A) (t := -T) (δ := δ)
      (by grind)
      (by grind)
      hsepMinus hx
  have hlocalMinus' :
      ∀ p ∈ ball (2 + ((-T : ℝ) : ℂ) * I) 5,
        poleClearedCompletedDedekindZetaContinuation K p = 0 →
        δ ≤ ‖(x - T * I) - p‖ := by
    intro p hp hpzero
    (convert hlocalMinus p hp hpzero using 1; push_cast; ring_nf)
  have hfPlus :
      poleClearedCompletedDedekindZetaContinuation K (x + T * I) ≠ 0 := by
    intro hzero
    have := hlocalPlus (x + T * I)
      (by
        rw [mem_ball, dist_eq]
        linarith)
      hzero
    rw [sub_self, norm_zero] at this
    grind
  have hfMinus :
      poleClearedCompletedDedekindZetaContinuation K (x - T * I) ≠ 0 := by
    intro hzero
    have := hlocalMinus' (x - T * I)
      (by
        rw [mem_ball, dist_eq]
        linarith)
      hzero
    rw [sub_self, norm_zero] at this
    grind
  refine ⟨⟨hfPlus, ?_⟩, ⟨hfMinus, ?_⟩⟩
  · exact norm_logDeriv_poleClearedCompletedZeta_le_of_local_separation K
      hδ (lt_of_lt_of_le zero_lt_one
        (one_le_completedZetaCenterLogLinearBound K T))
      (completedZeta_center_log_gap_le K (by
        grind))
      hzPlus hfPlus hlocalPlus
  · have hbound :=
      norm_logDeriv_poleClearedCompletedZeta_le_of_local_separation K
        hδ (lt_of_lt_of_le zero_lt_one
          (one_le_completedZetaCenterLogLinearBound K (-T)))
        (completedZeta_center_log_gap_le K (by
          grind))
        hzMinus hfMinus hlocalMinus'
    grind

end NumberField.Odlyzko

end

section

open Complex NumberField NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- A completed zeta moving vertical coefficient used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingVerticalCoefficient (R : ℝ) : ℝ :=
  max 1
    (poleClearedCompletedDedekindZetaVerticalBound K
      (2 - |R|) (2 + |R|))

omit [IsTotallyComplex K] in
theorem one_le_completedZetaMovingVerticalCoefficient (R : ℝ) :
    1 ≤ completedZetaMovingVerticalCoefficient K R :=
  le_max_left _ _

/-- A completed zeta moving center log linear bound used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingCenterLogLinearBound
    (R t : ℝ) : ℝ :=
  max 1 <|
    completedZetaMovingVerticalCoefficient K R +
      2 * (1 + |t| + |R|) +
      Real.log (dedekindZetaInverseVerticalMajorant K) -
      (nrComplexPlaces K : ℝ) / 2 *
        Real.log complexPlaceGammaVerticalLowerConstant +
      (nrComplexPlaces K : ℝ) / 2 * Real.pi * |t|

omit [IsTotallyComplex K] in
theorem log_completedZetaMovingCircleBound_le
    (R t : ℝ) :
    Real.log (completedZetaMovingCircleBound K R t) ≤
      completedZetaMovingVerticalCoefficient K R +
        2 * (1 + |t| + |R|) := by
  let V : ℝ :=
    poleClearedCompletedDedekindZetaVerticalBound K
      (2 - |R|) (2 + |R|)
  let D : ℝ := completedZetaMovingVerticalCoefficient K R
  let Q : ℝ := 1 + |t| + |R|
  have hD : 1 ≤ D := one_le_completedZetaMovingVerticalCoefficient K R
  have hVD : V ≤ D := le_max_right _ _
  have hQ : 1 ≤ Q := by grind
  have hmajor :
      completedZetaMovingCircleBound K R t ≤ D * Q ^ 2 := by
    change max 1 (V * Q ^ 2) ≤ D * Q ^ 2
    apply max_le
    · nlinarith [sq_nonneg Q]
    · exact mul_le_mul_of_nonneg_right hVD (sq_nonneg Q)
  calc
    Real.log (completedZetaMovingCircleBound K R t) ≤
        Real.log (D * Q ^ 2) :=
      Real.log_le_log
        (lt_of_lt_of_le zero_lt_one
          (one_le_completedZetaMovingCircleBound K R t)) hmajor
    _ = Real.log D + 2 * Real.log Q := by
      rw [Real.log_mul (ne_of_gt (lt_of_lt_of_le zero_lt_one hD))
        (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one hQ))),
        Real.log_pow]
      norm_num
    _ ≤ D + 2 * Q := by
      gcongr
      · exact Real.log_le_self (zero_le_one.trans hD)
      · exact Real.log_le_self (zero_le_one.trans hQ)
    _ = completedZetaMovingVerticalCoefficient K R +
          2 * (1 + |t| + |R|) := rfl

theorem completedZeta_moving_center_log_gap_le
    {R t : ℝ} (ht : 1 ≤ |t|) :
    Real.log (completedZetaMovingCircleBound K R t) -
        Real.log
          ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ ≤
      completedZetaMovingCenterLogLinearBound K R t := by
  apply le_trans ?_ (le_max_right _ _)
  linarith [log_completedZetaMovingCircleBound_le K R t,
    neg_log_norm_poleClearedCompletedZeta_two_add_mul_I_le K ht]

/-- A completed zeta moving center constant part used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingCenterConstantPart (R : ℝ) : ℝ :=
  completedZetaMovingVerticalCoefficient K R +
    2 * (1 + |R|) +
    |Real.log (dedekindZetaInverseVerticalMajorant K)| +
    (nrComplexPlaces K : ℝ) / 2 *
      |Real.log complexPlaceGammaVerticalLowerConstant|

/-- A completed zeta moving center slope used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingCenterSlope : ℝ :=
  2 + (nrComplexPlaces K : ℝ) / 2 * Real.pi

/-- A completed zeta moving center linear coefficient used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingCenterLinearCoefficient (R : ℝ) : ℝ :=
  1 + completedZetaMovingCenterConstantPart K R +
    completedZetaMovingCenterSlope K

omit [IsTotallyComplex K] in
theorem one_le_completedZetaMovingCenterLinearCoefficient (R : ℝ) :
    1 ≤ completedZetaMovingCenterLinearCoefficient K R := by
  have hD : 0 ≤ completedZetaMovingVerticalCoefficient K R :=
    zero_le_one.trans (one_le_completedZetaMovingVerticalCoefficient K R)
  unfold completedZetaMovingCenterLinearCoefficient
  unfold completedZetaMovingCenterConstantPart
  unfold completedZetaMovingCenterSlope
  nlinarith [abs_nonneg R,
    abs_nonneg (Real.log (dedekindZetaInverseVerticalMajorant K)),
    mul_nonneg (by positivity : 0 ≤ (nrComplexPlaces K : ℝ) / 2)
      (abs_nonneg (Real.log complexPlaceGammaVerticalLowerConstant)),
    mul_nonneg (by positivity : 0 ≤ (nrComplexPlaces K : ℝ) / 2)
      Real.pi_pos.le]

omit [IsTotallyComplex K] in
theorem completedZetaMovingCenterLogLinearBound_le
    (R t : ℝ) :
    completedZetaMovingCenterLogLinearBound K R t ≤
      completedZetaMovingCenterLinearCoefficient K R * (1 + |t|) := by
  let P := completedZetaMovingCenterConstantPart K R
  let S := completedZetaMovingCenterSlope K
  let C := completedZetaMovingCenterLinearCoefficient K R
  have hP : 0 ≤ P := by
    dsimp [P, completedZetaMovingCenterConstantPart]
    have hD : 0 ≤ completedZetaMovingVerticalCoefficient K R :=
      zero_le_one.trans (one_le_completedZetaMovingVerticalCoefficient K R)
    positivity
  have hS : 0 ≤ S := by
    dsimp [S, completedZetaMovingCenterSlope]
    positivity
  have hC : C = 1 + P + S := by rfl
  have hraw :
      completedZetaMovingVerticalCoefficient K R +
          2 * (1 + |t| + |R|) +
          Real.log (dedekindZetaInverseVerticalMajorant K) -
          (nrComplexPlaces K : ℝ) / 2 *
            Real.log complexPlaceGammaVerticalLowerConstant +
          (nrComplexPlaces K : ℝ) / 2 * Real.pi * |t| ≤
        P + S * |t| := by
    dsimp [P, S, completedZetaMovingCenterConstantPart,
      completedZetaMovingCenterSlope]
    have hlogC :
        Real.log (dedekindZetaInverseVerticalMajorant K) ≤
          |Real.log (dedekindZetaInverseVerticalMajorant K)| :=
      le_abs_self _
    have hlogG :
        -Real.log complexPlaceGammaVerticalLowerConstant ≤
          |Real.log complexPlaceGammaVerticalLowerConstant| := by grind
    nlinarith [mul_le_mul_of_nonneg_left hlogG (by positivity :
      0 ≤ (nrComplexPlaces K : ℝ) / 2)]
  unfold completedZetaMovingCenterLogLinearBound
  change max 1 _ ≤ C * (1 + |t|)
  apply max_le
  · rw [hC]
    nlinarith [abs_nonneg t]
  · rw [hC]
    calc
      _ ≤ P + S * |t| := hraw
      _ ≤ (1 + P + S) * (1 + |t|) := by
        nlinarith [abs_nonneg t, mul_nonneg hP (abs_nonneg t)]

omit [IsTotallyComplex K] in
theorem completedZetaCenterLogLinearBound_eq_moving (t : ℝ) :
    completedZetaCenterLogLinearBound K t =
      completedZetaMovingCenterLogLinearBound K 6 t := by
  unfold completedZetaCenterLogLinearBound
  unfold completedZetaCenterLogLinearExpression
  unfold completedZetaRadiusSixVerticalCoefficient
  unfold completedZetaMovingCenterLogLinearBound
  unfold completedZetaMovingVerticalCoefficient
  grind

end NumberField.Odlyzko

end

section

open Complex NumberField Metric Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A completed zeta selected height zero count bound used in the Odlyzko-bound argument. -/
noncomputable def completedZetaSelectedHeightZeroCountBound (A : ℝ) : ℝ :=
  2 * completedZetaMovingCenterLogLinearBound K 9 (A + 1 / 2) /
    Real.log (9 / 8)

open Classical in
private theorem selected_height_positive_rectangle_subset_disk
    (A : ℝ) :
    Icc (-3 : ℝ) 7 ×ℂ Icc (A - 5) (A + 6) ⊆
      closedBall (2 + ((A + 1 / 2 : ℝ) : ℂ) * I) 8 := by
  intro z hz
  rw [mem_closedBall, dist_eq]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : -5 ≤ z.re - 2 ∧ z.re - 2 ≤ 5 := by
    exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  have him :
      -(11 / 2 : ℝ) ≤ z.im - (A + 1 / 2) ∧
        z.im - (A + 1 / 2) ≤ 11 / 2 := by
    exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, mul_one, sub_im, add_im]
  norm_num
  nlinarith [sq_nonneg (z.re - 2 + 5), sq_nonneg (5 - (z.re - 2)),
    sq_nonneg (z.im - (A + 1 / 2) + 11 / 2),
    sq_nonneg (11 / 2 - (z.im - (A + 1 / 2)))]

open Classical in
private theorem selected_height_negative_rectangle_subset_disk
    (A : ℝ) :
    Icc (-3 : ℝ) 7 ×ℂ Icc (-(A + 6)) (-(A - 5)) ⊆
      closedBall (2 + ((-(A + 1 / 2) : ℝ) : ℂ) * I) 8 := by
  intro z hz
  rw [mem_closedBall, dist_eq]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : -5 ≤ z.re - 2 ∧ z.re - 2 ≤ 5 := by
    exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  have him :
      -(11 / 2 : ℝ) ≤ z.im - (-(A + 1 / 2)) ∧
        z.im - (-(A + 1 / 2)) ≤ 11 / 2 := by
    exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, mul_one, sub_im, add_im]
  norm_num
  nlinarith [sq_nonneg (z.re - 2 + 5), sq_nonneg (5 - (z.re - 2)),
    sq_nonneg (z.im - (-(A + 1 / 2)) + 11 / 2),
    sq_nonneg (11 / 2 - (z.im - (-(A + 1 / 2))))]

open Classical in
private theorem card_selected_height_positive_rectangle_le
    {A : ℝ} (hA : 6 ≤ A) :
    ((completedDedekindZetaZerosInClosedRectangle K
        (-3) 7 (A - 5) (A + 6)).card : ℝ) ≤
      completedZetaMovingCenterLogLinearBound K 9 (A + 1 / 2) /
        Real.log (9 / 8) := by
  let t : ℝ := A + 1 / 2
  have ht : 1 ≤ |t| := by grind
  have hc :
      poleClearedCompletedDedekindZetaContinuation K (2 + t * I) ≠ 0 :=
    poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
      (by simp)
  have hJ :=
    card_completedDedekindZetaZerosInClosedRectangle_le_movingJensen
      K (r := 8) (R := 9) (t := t)
      (by norm_num) (by norm_num) hc
      (by simpa [t] using selected_height_positive_rectangle_subset_disk A)
  have hMpos : 0 < completedZetaMovingCircleBound K 9 t :=
    lt_of_lt_of_le zero_lt_one
      (one_le_completedZetaMovingCircleBound K 9 t)
  have hcenterPos :
      0 < ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ :=
    norm_pos_iff.mpr hc
  rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hcenterPos)] at hJ
  exact hJ.trans (div_le_div_of_nonneg_right
    (completedZeta_moving_center_log_gap_le K ht)
    (Real.log_pos (by norm_num : (1 : ℝ) < 9 / 8)).le)

open Classical in
private theorem card_selected_height_negative_rectangle_le
    {A : ℝ} (hA : 6 ≤ A) :
    ((completedDedekindZetaZerosInClosedRectangle K
        (-3) 7 (-(A + 6)) (-(A - 5))).card : ℝ) ≤
      completedZetaMovingCenterLogLinearBound K 9 (A + 1 / 2) /
        Real.log (9 / 8) := by
  let t : ℝ := -(A + 1 / 2)
  have ht : 1 ≤ |t| := by grind
  have hc :
      poleClearedCompletedDedekindZetaContinuation K (2 + t * I) ≠ 0 :=
    poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
      (by simp)
  have hJ :=
    card_completedDedekindZetaZerosInClosedRectangle_le_movingJensen
      K (r := 8) (R := 9) (t := t)
      (by norm_num) (by norm_num) hc
      (by simpa [t] using selected_height_negative_rectangle_subset_disk A)
  have hMpos : 0 < completedZetaMovingCircleBound K 9 t :=
    lt_of_lt_of_le zero_lt_one
      (one_le_completedZetaMovingCircleBound K 9 t)
  have hcenterPos :
      0 < ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ :=
    norm_pos_iff.mpr hc
  rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hcenterPos)] at hJ
  have hbound := hJ.trans (div_le_div_of_nonneg_right
    (completedZeta_moving_center_log_gap_le K ht)
    (Real.log_pos (by norm_num : (1 : ℝ) < 9 / 8)).le)
  have habs : |t| = |A + 1 / 2| := by grind
  simpa [completedZetaMovingCenterLogLinearBound, habs] using hbound

open Classical in
theorem card_completedZetaSelectedHeightOrdinates_le
    {A : ℝ} (hA : 6 ≤ A) :
    ((completedZetaSelectedHeightOrdinates K A).card : ℝ) ≤
      completedZetaSelectedHeightZeroCountBound K A := by
  let Z :=
    completedDedekindZetaZerosInClosedRectangle K
      (-3) 7 (-(A + 6)) (A + 6)
  let F := Z.filter fun z ↦ A - 5 ≤ |z.im|
  let P :=
    completedDedekindZetaZerosInClosedRectangle K
      (-3) 7 (A - 5) (A + 6)
  let N :=
    completedDedekindZetaZerosInClosedRectangle K
      (-3) 7 (-(A + 6)) (-(A - 5))
  have hFsubset : F ⊆ P ∪ N := by
    intro z hz
    have hzF := Finset.mem_filter.mp hz
    have hzRect :=
      (mem_completedDedekindZetaZerosInClosedRectangle_iff K).mp hzF.1
    rcases le_total 0 z.im with hpos | hneg
    · apply Finset.mem_union_left
      apply (mem_completedDedekindZetaZerosInClosedRectangle_iff K).mpr
      refine ⟨⟨hzRect.1.1, ?_⟩, hzRect.2⟩
      rw [abs_of_nonneg hpos] at hzF
      exact ⟨hzF.2, hzRect.1.2.2⟩
    · apply Finset.mem_union_right
      apply (mem_completedDedekindZetaZerosInClosedRectangle_iff K).mpr
      refine ⟨⟨hzRect.1.1, ?_⟩, hzRect.2⟩
      rw [abs_of_nonpos hneg] at hzF
      exact ⟨by linarith [hzRect.1.2.1], by grind⟩
  have hcardNat :
      (completedZetaSelectedHeightOrdinates K A).card ≤ P.card + N.card := by
    calc
      (completedZetaSelectedHeightOrdinates K A).card ≤ F.card := by
        exact Finset.card_image_le
      _ ≤ (P ∪ N).card := Finset.card_le_card hFsubset
      _ ≤ P.card + N.card := Finset.card_union_le P N
  have hcardReal :
      ((completedZetaSelectedHeightOrdinates K A).card : ℝ) ≤
        (P.card : ℝ) + (N.card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((completedZetaSelectedHeightOrdinates K A).card : ℝ) ≤
        (P.card : ℝ) + (N.card : ℝ) := hcardReal
    _ ≤
        completedZetaMovingCenterLogLinearBound K 9 (A + 1 / 2) /
            Real.log (9 / 8) +
          completedZetaMovingCenterLogLinearBound K 9 (A + 1 / 2) /
            Real.log (9 / 8) := by
      gcongr
      · simpa [P] using card_selected_height_positive_rectangle_le K hA
      · simpa [N] using card_selected_height_negative_rectangle_le K hA
    _ = completedZetaSelectedHeightZeroCountBound K A := by
      unfold completedZetaSelectedHeightZeroCountBound
      ring

open Classical in
theorem inv_completedZetaSelectedHeightSeparation_le
    {A : ℝ} (hA : 6 ≤ A) :
    (completedZetaSelectedHeightSeparation K A)⁻¹ ≤
      4 * (completedZetaSelectedHeightZeroCountBound K A + 1) := by
  rw [completedZetaSelectedHeightSeparation,
    finiteSetAvoidanceRadiusOnLength]
  have hcard :=
    card_completedZetaSelectedHeightOrdinates_le K hA
  simp_all

end NumberField.Odlyzko

end

section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- The linear coefficient controlling the completed-zeta zero count at a selected height. -/
noncomputable def completedZetaSelectedHeightZeroCountLinearCoefficient : ℝ :=
  4 * completedZetaMovingCenterLinearCoefficient K 9 / Real.log (9 / 8)

omit [IsTotallyComplex K] in
private theorem completedZetaSelectedHeightZeroCountLinearCoefficient_nonneg :
    0 ≤ completedZetaSelectedHeightZeroCountLinearCoefficient K := by
  unfold completedZetaSelectedHeightZeroCountLinearCoefficient
  exact div_nonneg
    (mul_nonneg (by norm_num)
      (zero_le_one.trans
        (one_le_completedZetaMovingCenterLinearCoefficient K 9)))
    (Real.log_pos (by norm_num : (1 : ℝ) < 9 / 8)).le

omit [IsTotallyComplex K] in
theorem completedZetaSelectedHeightZeroCountBound_le_linear
    {A : ℝ} (hA : 6 ≤ A) :
    completedZetaSelectedHeightZeroCountBound K A ≤
      completedZetaSelectedHeightZeroCountLinearCoefficient K * (A + 1) := by
  have hcenter :=
    completedZetaMovingCenterLogLinearBound_le K 9 (A + 1 / 2)
  have habs : |A + 1 / 2| = A + 1 / 2 := abs_of_pos (by linarith)
  rw [habs] at hcenter
  have hlogpos : 0 < Real.log (9 / 8) := Real.log_pos (by norm_num)
  unfold completedZetaSelectedHeightZeroCountBound
  unfold completedZetaSelectedHeightZeroCountLinearCoefficient
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right hlogpos).2
  nlinarith [mul_nonneg
    (zero_le_one.trans (one_le_completedZetaMovingCenterLinearCoefficient K 9))
    (show 0 ≤ A + 1 by linarith)]

/-- The linear coefficient controlling inverse zero separation at a selected height. -/
noncomputable def completedZetaSelectedHeightSeparationInvLinearCoefficient : ℝ :=
  4 * (completedZetaSelectedHeightZeroCountLinearCoefficient K + 1)

omit [IsTotallyComplex K] in
private theorem completedZetaSelectedHeightSeparationInvLinearCoefficient_nonneg :
    0 ≤ completedZetaSelectedHeightSeparationInvLinearCoefficient K := by
  unfold completedZetaSelectedHeightSeparationInvLinearCoefficient
  exact mul_nonneg (by norm_num)
    (by
      have :=
        completedZetaSelectedHeightZeroCountLinearCoefficient_nonneg K
      linarith)

theorem inv_completedZetaSelectedHeightSeparation_le_linear
    {A : ℝ} (hA : 6 ≤ A) :
    (completedZetaSelectedHeightSeparation K A)⁻¹ ≤
      completedZetaSelectedHeightSeparationInvLinearCoefficient K * (A + 1) := by
  have hInv := inv_completedZetaSelectedHeightSeparation_le K hA
  have hCount :=
    completedZetaSelectedHeightZeroCountBound_le_linear K hA
  unfold completedZetaSelectedHeightSeparationInvLinearCoefficient
  grind

/-- The linear coefficient controlling the completed zeta function at a selected center. -/
noncomputable def completedZetaSelectedHeightCenterLinearCoefficient : ℝ :=
  2 * completedZetaMovingCenterLinearCoefficient K 6

omit [IsTotallyComplex K] in
theorem completedZetaSelectedHeightCenterLinearCoefficient_nonneg :
    0 ≤ completedZetaSelectedHeightCenterLinearCoefficient K := by
  unfold completedZetaSelectedHeightCenterLinearCoefficient
  exact mul_nonneg (by norm_num)
    (zero_le_one.trans
      (one_le_completedZetaMovingCenterLinearCoefficient K 6))

omit [IsTotallyComplex K] in
private theorem completedZetaCenterLogLinearBound_selected_le
    {A T : ℝ} (hA : 6 ≤ A) (hAT : A < T) (hTA : T < A + 1) :
    completedZetaCenterLogLinearBound K T ≤
        completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1) ∧
      completedZetaCenterLogLinearBound K (-T) ≤
        completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1) := by
  have hTpos : 0 < T := by linarith
  have hplus :=
    completedZetaMovingCenterLogLinearBound_le K 6 T
  have hminus :=
    completedZetaMovingCenterLogLinearBound_le K 6 (-T)
  rw [← completedZetaCenterLogLinearBound_eq_moving K] at hplus hminus
  rw [abs_of_pos hTpos] at hplus
  rw [abs_neg, abs_of_pos hTpos] at hminus
  unfold completedZetaSelectedHeightCenterLinearCoefficient
  constructor
  · exact hplus.trans (by
      rw [show
        2 * completedZetaMovingCenterLinearCoefficient K 6 * (A + 1) =
          completedZetaMovingCenterLinearCoefficient K 6 * (2 * (A + 1)) by
        ring]
      apply mul_le_mul_of_nonneg_left
      · linarith
      · exact (zero_le_one.trans
          (one_le_completedZetaMovingCenterLinearCoefficient K 6)))
  · exact hminus.trans (by
      rw [show
        2 * completedZetaMovingCenterLinearCoefficient K 6 * (A + 1) =
          completedZetaMovingCenterLinearCoefficient K 6 * (2 * (A + 1)) by
        ring]
      apply mul_le_mul_of_nonneg_left
      · linarith
      · exact (zero_le_one.trans
          (one_le_completedZetaMovingCenterLinearCoefficient K 6)))

/-- The quadratic coefficient controlling the completed-zeta logarithmic derivative
at a selected height. -/
noncomputable def completedZetaSelectedHeightLogDerivativeQuadraticCoefficient : ℝ :=
  completedZetaSelectedHeightCenterLinearCoefficient K *
    (completedZetaCanonicalJensenCoefficient *
        completedZetaSelectedHeightSeparationInvLinearCoefficient K +
      completedZetaCanonicalJensenCoefficient + 32)

omit [IsTotallyComplex K] in
theorem completedZetaSelectedHeightLogDerivativeQuadraticCoefficient_nonneg :
    0 ≤ completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K := by
  unfold completedZetaSelectedHeightLogDerivativeQuadraticCoefficient
  exact mul_nonneg
    (completedZetaSelectedHeightCenterLinearCoefficient_nonneg K)
    (by
      have hJ := completedZetaCanonicalJensenCoefficient_pos.le
      have hD :=
        completedZetaSelectedHeightSeparationInvLinearCoefficient_nonneg K
      positivity)

theorem exists_height_norm_logDeriv_poleClearedCompletedZeta_le_quadratic
    {A : ℝ} (hA : 6 ≤ A) :
    ∃ T : ℝ, A < T ∧ T < A + 1 ∧
      ∀ x ∈ Icc (-1 : ℝ) 5,
        (poleClearedCompletedDedekindZetaContinuation K (x + T * I) ≠ 0 ∧
        ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
            (x + T * I)‖ ≤
          completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K *
            (A + 1) ^ 2) ∧
        (poleClearedCompletedDedekindZetaContinuation K (x - T * I) ≠ 0 ∧
        ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
            (x - T * I)‖ ≤
          completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K *
            (A + 1) ^ 2) := by
  obtain ⟨T, hAT, hTA, hbound⟩ :=
    exists_height_norm_logDeriv_poleClearedCompletedZeta_le K hA
  refine ⟨T, hAT, hTA, ?_⟩
  have hCenter :=
    completedZetaCenterLogLinearBound_selected_le K hA hAT hTA
  have hInv :=
    inv_completedZetaSelectedHeightSeparation_le_linear K hA
  have hSepPos :=
    completedZetaSelectedHeightSeparation_pos K A
  have hJ :
      0 ≤ completedZetaCanonicalJensenCoefficient :=
    completedZetaCanonicalJensenCoefficient_pos.le
  have hC :
      0 ≤ completedZetaSelectedHeightCenterLinearCoefficient K :=
    completedZetaSelectedHeightCenterLinearCoefficient_nonneg K
  intro x hx
  rcases hbound x hx with ⟨⟨hfplus, hplus⟩, ⟨hfminus, hminus⟩⟩
  have hA1 : 1 ≤ A + 1 := by linarith
  have hCenterUpper :
      0 ≤ completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1) :=
    mul_nonneg hC (zero_le_one.trans hA1)
  have hInvNonneg :
      0 ≤ (completedZetaSelectedHeightSeparation K A)⁻¹ :=
    inv_nonneg.mpr hSepPos.le
  refine ⟨⟨hfplus, ?_⟩, ⟨hfminus, ?_⟩⟩
  · apply hplus.trans
    rw [div_eq_mul_inv]
    have hprod :
        completedZetaCenterLogLinearBound K T *
              completedZetaCanonicalJensenCoefficient *
            (completedZetaSelectedHeightSeparation K A)⁻¹ ≤
          (completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1)) *
              completedZetaCanonicalJensenCoefficient *
            (completedZetaSelectedHeightSeparationInvLinearCoefficient K *
              (A + 1)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hCenter.1 hJ
      · grind
      · simp_all
      · exact mul_nonneg hCenterUpper hJ
    have hlinJ :
        completedZetaCenterLogLinearBound K T *
            completedZetaCanonicalJensenCoefficient ≤
          completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1) *
            completedZetaCanonicalJensenCoefficient :=
      mul_le_mul_of_nonneg_right hCenter.1 hJ
    have hlin32 :
        32 * completedZetaCenterLogLinearBound K T ≤
          32 *
            (completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1)) :=
      mul_le_mul_of_nonneg_left hCenter.1 (by norm_num)
    have hu : A + 1 ≤ (A + 1) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ A + 1 by linarith)
        (show 0 ≤ A by linarith)]
    have hlinJQ :
        completedZetaCenterLogLinearBound K T *
            completedZetaCanonicalJensenCoefficient ≤
          completedZetaSelectedHeightCenterLinearCoefficient K *
            completedZetaCanonicalJensenCoefficient * (A + 1) ^ 2 := by
      calc
        _ ≤ completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1) *
            completedZetaCanonicalJensenCoefficient := hlinJ
        _ = completedZetaSelectedHeightCenterLinearCoefficient K *
            completedZetaCanonicalJensenCoefficient * (A + 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hu (mul_nonneg hC hJ)
    have hlin32Q :
        32 * completedZetaCenterLogLinearBound K T ≤
          32 * completedZetaSelectedHeightCenterLinearCoefficient K *
            (A + 1) ^ 2 := by
      calc
        _ ≤ 32 *
            (completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1)) :=
          hlin32
        _ = (32 * completedZetaSelectedHeightCenterLinearCoefficient K) *
            (A + 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hu (mul_nonneg (by norm_num) hC)
    unfold completedZetaSelectedHeightLogDerivativeQuadraticCoefficient
    grind
  · apply hminus.trans
    rw [div_eq_mul_inv]
    have hprod :
        completedZetaCenterLogLinearBound K (-T) *
              completedZetaCanonicalJensenCoefficient *
            (completedZetaSelectedHeightSeparation K A)⁻¹ ≤
          (completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1)) *
              completedZetaCanonicalJensenCoefficient *
            (completedZetaSelectedHeightSeparationInvLinearCoefficient K *
              (A + 1)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hCenter.2 hJ
      · grind
      · simp_all
      · exact mul_nonneg hCenterUpper hJ
    have hlinJ :
        completedZetaCenterLogLinearBound K (-T) *
            completedZetaCanonicalJensenCoefficient ≤
          completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1) *
            completedZetaCanonicalJensenCoefficient :=
      mul_le_mul_of_nonneg_right hCenter.2 hJ
    have hlin32 :
        32 * completedZetaCenterLogLinearBound K (-T) ≤
          32 *
            (completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1)) :=
      mul_le_mul_of_nonneg_left hCenter.2 (by norm_num)
    have hu : A + 1 ≤ (A + 1) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ A + 1 by linarith)
        (show 0 ≤ A by linarith)]
    have hlinJQ :
        completedZetaCenterLogLinearBound K (-T) *
            completedZetaCanonicalJensenCoefficient ≤
          completedZetaSelectedHeightCenterLinearCoefficient K *
            completedZetaCanonicalJensenCoefficient * (A + 1) ^ 2 := by
      calc
        _ ≤ completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1) *
            completedZetaCanonicalJensenCoefficient := hlinJ
        _ = completedZetaSelectedHeightCenterLinearCoefficient K *
            completedZetaCanonicalJensenCoefficient * (A + 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hu (mul_nonneg hC hJ)
    have hlin32Q :
        32 * completedZetaCenterLogLinearBound K (-T) ≤
          32 * completedZetaSelectedHeightCenterLinearCoefficient K *
            (A + 1) ^ 2 := by
      calc
        _ ≤ 32 *
            (completedZetaSelectedHeightCenterLinearCoefficient K * (A + 1)) :=
          hlin32
        _ = (32 * completedZetaSelectedHeightCenterLinearCoefficient K) *
            (A + 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hu (mul_nonneg (by norm_num) hC)
    unfold completedZetaSelectedHeightLogDerivativeQuadraticCoefficient
    grind

end NumberField.Odlyzko

end

section

open Complex Filter NumberField Set
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A completed zeta selected height used in the Odlyzko-bound argument. -/
noncomputable def completedZetaSelectedHeight (n : ℕ) : ℝ :=
  Classical.choose
    (exists_height_norm_logDeriv_poleClearedCompletedZeta_le_quadratic
      K (A := (n : ℝ) + 6) (by norm_num))

open Classical in
theorem completedZetaSelectedHeight_spec (n : ℕ) :
    (n : ℝ) + 6 < completedZetaSelectedHeight K n ∧
      completedZetaSelectedHeight K n < (n : ℝ) + 7 ∧
      ∀ x ∈ Icc (-1 : ℝ) 5,
        (poleClearedCompletedDedekindZetaContinuation K
            (x + completedZetaSelectedHeight K n * I) ≠ 0 ∧
          ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
              (x + completedZetaSelectedHeight K n * I)‖ ≤
            completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K *
              ((n : ℝ) + 7) ^ 2) ∧
        (poleClearedCompletedDedekindZetaContinuation K
            (x - completedZetaSelectedHeight K n * I) ≠ 0 ∧
          ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
              (x - completedZetaSelectedHeight K n * I)‖ ≤
            completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K *
              ((n : ℝ) + 7) ^ 2) := by
  simpa [completedZetaSelectedHeight,
    show (n : ℝ) + 6 + 1 = (n : ℝ) + 7 by ring] using
      (Classical.choose_spec
        (exists_height_norm_logDeriv_poleClearedCompletedZeta_le_quadratic
          K (A := (n : ℝ) + 6) (by norm_num)))

open Classical in
theorem completedZetaSelectedHeight_pos (n : ℕ) :
    0 < completedZetaSelectedHeight K n := by
  linarith [(completedZetaSelectedHeight_spec K n).1]

open Classical in
theorem tendsto_completedZetaSelectedHeight_atTop :
    Tendsto (completedZetaSelectedHeight K) atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall fun n ↦
      (completedZetaSelectedHeight_spec K n).1.le)
    (tendsto_atTop_add_const_right atTop 6
      (tendsto_natCast_atTop_atTop (R := ℝ)))

end NumberField.Odlyzko

end

section

open Complex Filter MeasureTheory NumberField Real Set
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
private theorem norm_completedZetaPoleLogDeriv_le_two
    {σ t : ℝ} (ht : 1 ≤ |t|) :
    ‖completedZetaPoleLogDeriv (σ + t * I)‖ ≤ 2 := by
  have hnorm₀ : 1 ≤ ‖(σ + t * I : ℂ)‖ := by
    exact ht.trans (by
      simpa using Complex.abs_im_le_norm (σ + t * I))
  have hnorm₁ : 1 ≤ ‖(σ + t * I : ℂ) - 1‖ := by
    exact ht.trans (by
      simpa using Complex.abs_im_le_norm ((σ + t * I : ℂ) - 1))
  unfold completedZetaPoleLogDeriv
  rw [one_div, one_div]
  calc
    ‖(σ + t * I : ℂ)⁻¹ + ((σ + t * I : ℂ) - 1)⁻¹‖ ≤
        ‖(σ + t * I : ℂ)⁻¹‖ + ‖((σ + t * I : ℂ) - 1)⁻¹‖ :=
      norm_add_le _ _
    _ ≤ 1 + 1 := by
      gcongr
      · rw [norm_inv]
        exact (inv_le_one₀ (by positivity)).2 hnorm₀
      · rw [norm_inv]
        exact (inv_le_one₀ (by positivity)).2 hnorm₁
    _ = 2 := by norm_num

open Classical in
private theorem selected_positive_integrand_norm_le_weighted
    {y δ σ : ℝ} (_hδ : 0 < δ) (n : ℕ)
    (hσ : σ ∈ Icc (-1 : ℝ) 2) :
    ‖poitouTransform (regularizedScaledTartar y δ)
          (σ + completedZetaSelectedHeight K n * I) *
        (logDeriv (poleClearedCompletedDedekindZetaContinuation K)
              (σ + completedZetaSelectedHeight K n * I) -
          completedZetaPoleLogDeriv
            (σ + completedZetaSelectedHeight K n * I))‖ ≤
      (4 * completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K + 2) *
        (|completedZetaSelectedHeight K n| ^ 2 *
          ‖poitouTransform (regularizedScaledTartar y δ)
            (σ + completedZetaSelectedHeight K n * I)‖) := by
  let T := completedZetaSelectedHeight K n
  let Q := completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K
  have hTlow := (completedZetaSelectedHeight_spec K n).1
  have hTpos : 0 < T := completedZetaSelectedHeight_pos K n
  have hQ : 0 ≤ Q :=
    completedZetaSelectedHeightLogDerivativeQuadraticCoefficient_nonneg K
  have hσ' : σ ∈ Icc (-1 : ℝ) 5 := ⟨hσ.1, hσ.2.trans (by norm_num)⟩
  have hlog :=
    ((completedZetaSelectedHeight_spec K n).2.2 σ hσ').1.2
  have hpole :
      ‖completedZetaPoleLogDeriv (σ + T * I)‖ ≤ 2 :=
    norm_completedZetaPoleLogDeriv_le_two
      (by grind)
  have hheight : ((n : ℝ) + 7) ^ 2 ≤ 4 * |T| ^ 2 := by
    rw [abs_of_pos hTpos]
    nlinarith [sq_nonneg ((n : ℝ) + 7), sq_nonneg T]
  rw [norm_mul]
  calc
    ‖poitouTransform (regularizedScaledTartar y δ) (σ + T * I)‖ *
        ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
              (σ + T * I) -
            completedZetaPoleLogDeriv (σ + T * I)‖ ≤
      ‖poitouTransform (regularizedScaledTartar y δ) (σ + T * I)‖ *
        (Q * ((n : ℝ) + 7) ^ 2 + 2) := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add hlog hpole)
    _ ≤ ‖poitouTransform (regularizedScaledTartar y δ) (σ + T * I)‖ *
        ((4 * Q + 2) * |T| ^ 2) := by
      gcongr
      nlinarith [mul_le_mul_of_nonneg_left hheight hQ,
        sq_nonneg |T|]
    _ = (4 * Q + 2) *
        (|T| ^ 2 *
          ‖poitouTransform (regularizedScaledTartar y δ) (σ + T * I)‖) := by
      ring

open Classical in
private theorem selected_negative_integrand_norm_le_weighted
    {y δ σ : ℝ} (_hδ : 0 < δ) (n : ℕ)
    (hσ : σ ∈ Icc (-1 : ℝ) 2) :
    ‖poitouTransform (regularizedScaledTartar y δ)
          (σ - completedZetaSelectedHeight K n * I) *
        (logDeriv (poleClearedCompletedDedekindZetaContinuation K)
              (σ - completedZetaSelectedHeight K n * I) -
          completedZetaPoleLogDeriv
            (σ - completedZetaSelectedHeight K n * I))‖ ≤
      (4 * completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K + 2) *
        (|-(completedZetaSelectedHeight K n)| ^ 2 *
          ‖poitouTransform (regularizedScaledTartar y δ)
            (σ - completedZetaSelectedHeight K n * I)‖) := by
  let T := completedZetaSelectedHeight K n
  let Q := completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K
  have hTlow := (completedZetaSelectedHeight_spec K n).1
  have hTpos : 0 < T := completedZetaSelectedHeight_pos K n
  have hQ : 0 ≤ Q :=
    completedZetaSelectedHeightLogDerivativeQuadraticCoefficient_nonneg K
  have hσ' : σ ∈ Icc (-1 : ℝ) 5 := ⟨hσ.1, hσ.2.trans (by norm_num)⟩
  have hlog :=
    ((completedZetaSelectedHeight_spec K n).2.2 σ hσ').2.2
  have hpole :
      ‖completedZetaPoleLogDeriv (σ - T * I)‖ ≤ 2 := by
    (convert norm_completedZetaPoleLogDeriv_le_two
      (σ := σ) (t := -T)
      (by grind) using 1; push_cast; ring_nf)
  have hheight : ((n : ℝ) + 7) ^ 2 ≤ 4 * |-T| ^ 2 := by
    rw [abs_neg, abs_of_pos hTpos]
    nlinarith [sq_nonneg ((n : ℝ) + 7), sq_nonneg T]
  rw [norm_mul]
  calc
    ‖poitouTransform (regularizedScaledTartar y δ) (σ - T * I)‖ *
        ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
              (σ - T * I) -
            completedZetaPoleLogDeriv (σ - T * I)‖ ≤
      ‖poitouTransform (regularizedScaledTartar y δ) (σ - T * I)‖ *
        (Q * ((n : ℝ) + 7) ^ 2 + 2) := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add hlog hpole)
    _ ≤ ‖poitouTransform (regularizedScaledTartar y δ) (σ - T * I)‖ *
        ((4 * Q + 2) * |-T| ^ 2) := by
      gcongr
      nlinarith [mul_le_mul_of_nonneg_left hheight hQ,
        sq_nonneg |-T|]
    _ = (4 * Q + 2) *
        (|-T| ^ 2 *
          ‖poitouTransform (regularizedScaledTartar y δ)
            (σ - T * I)‖) := by ring

open Classical in
private theorem continuousOn_selected_positive_integrand
    {y δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ContinuousOn
      (fun σ : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ)
            (σ + completedZetaSelectedHeight K n * I) *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K)
                (σ + completedZetaSelectedHeight K n * I) -
            completedZetaPoleLogDeriv
              (σ + completedZetaSelectedHeight K n * I)))
      (Icc (-1) 2) := by
  intro σ hσ
  let s : ℂ := σ + completedZetaSelectedHeight K n * I
  have hσ' : σ ∈ Icc (-1 : ℝ) 5 := ⟨hσ.1, hσ.2.trans (by norm_num)⟩
  have hsne :
      poleClearedCompletedDedekindZetaContinuation K s ≠ 0 := by
    simpa [s] using
      ((completedZetaSelectedHeight_spec K n).2.2 σ hσ').1.1
  have hs0 : s ≠ 0 := by
    intro hs
    have := congrArg Complex.im hs
    dsimp [s] at this
    simp only [ofReal_im, ofReal_re, mul_im, I_re, I_im, zero_mul, mul_one,
      zero_add] at this
    linarith [completedZetaSelectedHeight_pos K n]
  have hs1 : s - 1 ≠ 0 := by
    intro hs
    have := congrArg Complex.im hs
    dsimp [s] at this
    simp only [ofReal_im, ofReal_re, mul_im, I_re, I_im, zero_mul,
      mul_one, zero_add, sub_zero] at this
    linarith [completedZetaSelectedHeight_pos K n]
  have hsMap :
      ContinuousAt (fun x : ℝ ↦ (x : ℂ) +
        completedZetaSelectedHeight K n * I) σ := by fun_prop
  have hΦ :
      ContinuousAt
        (fun x : ℝ ↦ poitouTransform (regularizedScaledTartar y δ)
          (x + completedZetaSelectedHeight K n * I)) σ :=
    by
      simpa [Function.comp_def, s] using
        (analyticOnNhd_poitouTransform_regularizedScaledTartar hδ
          s (mem_univ s)).continuousAt.comp_of_eq hsMap (by simp [s])
  have hΞ :=
    analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K
      s (mem_univ s)
  have hlog :
      ContinuousAt
        (fun x : ℝ ↦ logDeriv
          (poleClearedCompletedDedekindZetaContinuation K)
          (x + completedZetaSelectedHeight K n * I)) σ := by
    unfold logDeriv
    simpa [Function.comp_def, s] using
      (hΞ.deriv.continuousAt.div hΞ.continuousAt hsne).comp_of_eq
        hsMap (by simp [s])
  have hpole :
      ContinuousAt
        (fun x : ℝ ↦ completedZetaPoleLogDeriv
          (x + completedZetaSelectedHeight K n * I)) σ := by
    unfold completedZetaPoleLogDeriv
    have hone : ContinuousAt (fun _ : ℝ ↦ (1 : ℂ)) σ :=
      continuousAt_const
    exact (hone.div hsMap hs0).add
      (hone.div (hsMap.sub continuousAt_const) hs1)
  exact (hΦ.mul (hlog.sub hpole)).continuousWithinAt

open Classical in
private theorem continuousOn_selected_negative_integrand
    {y δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ContinuousOn
      (fun σ : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ)
            (σ - completedZetaSelectedHeight K n * I) *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K)
                (σ - completedZetaSelectedHeight K n * I) -
            completedZetaPoleLogDeriv
              (σ - completedZetaSelectedHeight K n * I)))
      (Icc (-1) 2) := by
  intro σ hσ
  let s : ℂ := σ - completedZetaSelectedHeight K n * I
  have hσ' : σ ∈ Icc (-1 : ℝ) 5 := ⟨hσ.1, hσ.2.trans (by norm_num)⟩
  have hsne :
      poleClearedCompletedDedekindZetaContinuation K s ≠ 0 := by
    simpa [s] using
      ((completedZetaSelectedHeight_spec K n).2.2 σ hσ').2.1
  have hs0 : s ≠ 0 := by
    intro hs
    have := congrArg Complex.im hs
    dsimp [s] at this
    simp only [ofReal_im, ofReal_re, mul_im, I_re, I_im, zero_mul, mul_one,
      zero_sub] at this
    linarith [completedZetaSelectedHeight_pos K n]
  have hs1 : s - 1 ≠ 0 := by
    intro hs
    have := congrArg Complex.im hs
    dsimp [s] at this
    simp only [ofReal_im, ofReal_re, mul_im, I_re, I_im, zero_mul, mul_one,
      zero_sub, sub_zero] at this
    linarith [completedZetaSelectedHeight_pos K n]
  have hsMap :
      ContinuousAt (fun x : ℝ ↦ (x : ℂ) -
        completedZetaSelectedHeight K n * I) σ := by fun_prop
  have hΦ :
      ContinuousAt
        (fun x : ℝ ↦ poitouTransform (regularizedScaledTartar y δ)
          (x - completedZetaSelectedHeight K n * I)) σ :=
    by
      simpa [Function.comp_def, s] using
        (analyticOnNhd_poitouTransform_regularizedScaledTartar hδ
          s (mem_univ s)).continuousAt.comp_of_eq hsMap (by simp [s])
  have hΞ :=
    analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K
      s (mem_univ s)
  have hlog :
      ContinuousAt
        (fun x : ℝ ↦ logDeriv
          (poleClearedCompletedDedekindZetaContinuation K)
          (x - completedZetaSelectedHeight K n * I)) σ := by
    unfold logDeriv
    simpa [Function.comp_def, s] using
      (hΞ.deriv.continuousAt.div hΞ.continuousAt hsne).comp_of_eq
        hsMap (by simp [s])
  have hpole :
      ContinuousAt
        (fun x : ℝ ↦ completedZetaPoleLogDeriv
          (x - completedZetaSelectedHeight K n * I)) σ := by
    unfold completedZetaPoleLogDeriv
    have hone : ContinuousAt (fun _ : ℝ ↦ (1 : ℂ)) σ :=
      continuousAt_const
    exact (hone.div hsMap hs0).add
      (hone.div (hsMap.sub continuousAt_const) hs1)
  exact (hΦ.mul (hlog.sub hpole)).continuousWithinAt

open Classical in
theorem tendsto_selected_positive_horizontalIntegral
    {y δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun n ↦ horizontalIntegral
        (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
            completedZetaPoleLogDeriv s))
        (-1) 2 (completedZetaSelectedHeight K n))
      atTop (𝓝 0) := by
  let Q := completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K
  let C := regularizedPoitouStripQuadraticDecayConstant y δ (-1) 2
  let B : ℝ := (4 * Q + 2) * C
  let F : ℕ → ℝ → ℂ := fun n σ ↦
    poitouTransform (regularizedScaledTartar y δ)
        (σ + completedZetaSelectedHeight K n * I) *
      (logDeriv (poleClearedCompletedDedekindZetaContinuation K)
            (σ + completedZetaSelectedHeight K n * I) -
        completedZetaPoleLogDeriv
          (σ + completedZetaSelectedHeight K n * I))
  have hDCT :
      Tendsto (fun n ↦ ∫ σ in (-1 : ℝ)..2, F n σ) atTop (𝓝 0) := by
    have hmeas :
        ∀ᶠ n : ℕ in atTop,
          AEStronglyMeasurable (F n) (volume.restrict (uIoc (-1) 2)) :=
      Filter.Eventually.of_forall fun n ↦
        ((continuousOn_selected_positive_integrand K hδ n).mono
          (by
            grind)).aestronglyMeasurable measurableSet_uIoc
    have hbound :
        ∀ᶠ n : ℕ in atTop, ∀ᵐ σ : ℝ,
          σ ∈ uIoc (-1) 2 → ‖F n σ‖ ≤ B :=
      Filter.Eventually.of_forall fun n ↦
        Filter.Eventually.of_forall fun σ hσ ↦ by
          have hσIcc : σ ∈ Icc (-1 : ℝ) 2 := by grind
          apply (selected_positive_integrand_norm_le_weighted K hδ n
            hσIcc).trans
          have hw :=
            sq_abs_mul_norm_poitouTransform_regularized_le_strip
              hδ y (completedZetaSelectedHeight K n) hσIcc
          dsimp [B, C, Q]
          apply mul_le_mul_of_nonneg_left hw
          have hQ :=
            completedZetaSelectedHeightLogDerivativeQuadraticCoefficient_nonneg K
          linarith
    have hlim :
        ∀ᵐ σ : ℝ, σ ∈ uIoc (-1) 2 →
          Tendsto (fun n ↦ F n σ) atTop (𝓝 0) :=
      Filter.Eventually.of_forall fun σ hσ ↦ by
        have hσIcc : σ ∈ Icc (-1 : ℝ) 2 := by grind
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hweighted :=
          (tendsto_sq_abs_mul_norm_poitouTransform_regularized_atTop
            hδ y σ).comp (tendsto_completedZetaSelectedHeight_atTop K)
        have hmajor :
            Tendsto
              (fun n ↦ (4 * Q + 2) *
                (|completedZetaSelectedHeight K n| ^ 2 *
                  ‖poitouTransform (regularizedScaledTartar y δ)
                    (σ + completedZetaSelectedHeight K n * I)‖))
              atTop (𝓝 0) := by
          simpa [Q] using (tendsto_const_nhds.mul hweighted)
        simpa [F] using squeeze_zero'
          (Filter.Eventually.of_forall fun n ↦ norm_nonneg _)
          (Filter.Eventually.of_forall fun n ↦
            selected_positive_integrand_norm_le_weighted K hδ n hσIcc)
          hmajor
    have h :=
      intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (a := (-1 : ℝ)) (b := 2) (μ := volume)
        (l := atTop) (f := fun _ ↦ (0 : ℂ)) (fun _ ↦ B)
        hmeas hbound intervalIntegrable_const hlim
    simpa using h
  simpa [horizontalIntegral, F] using hDCT

open Classical in
theorem tendsto_selected_negative_horizontalIntegral
    {y δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun n ↦ horizontalIntegral
        (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
            completedZetaPoleLogDeriv s))
        (-1) 2 (-(completedZetaSelectedHeight K n)))
      atTop (𝓝 0) := by
  let Q := completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K
  let C := regularizedPoitouStripQuadraticDecayConstant y δ (-1) 2
  let B : ℝ := (4 * Q + 2) * C
  let F : ℕ → ℝ → ℂ := fun n σ ↦
    poitouTransform (regularizedScaledTartar y δ)
        (σ - completedZetaSelectedHeight K n * I) *
      (logDeriv (poleClearedCompletedDedekindZetaContinuation K)
            (σ - completedZetaSelectedHeight K n * I) -
        completedZetaPoleLogDeriv
          (σ - completedZetaSelectedHeight K n * I))
  have hDCT :
      Tendsto (fun n ↦ ∫ σ in (-1 : ℝ)..2, F n σ) atTop (𝓝 0) := by
    have hmeas :
        ∀ᶠ n : ℕ in atTop,
          AEStronglyMeasurable (F n) (volume.restrict (uIoc (-1) 2)) :=
      Filter.Eventually.of_forall fun n ↦
        ((continuousOn_selected_negative_integrand K hδ n).mono
          (by
            grind)).aestronglyMeasurable measurableSet_uIoc
    have hbound :
        ∀ᶠ n : ℕ in atTop, ∀ᵐ σ : ℝ,
          σ ∈ uIoc (-1) 2 → ‖F n σ‖ ≤ B :=
      Filter.Eventually.of_forall fun n ↦
        Filter.Eventually.of_forall fun σ hσ ↦ by
          have hσIcc : σ ∈ Icc (-1 : ℝ) 2 := by grind
          apply (selected_negative_integrand_norm_le_weighted K hδ n
            hσIcc).trans
          have hw :=
            sq_abs_mul_norm_poitouTransform_regularized_le_strip
              hδ y (-(completedZetaSelectedHeight K n)) hσIcc
          dsimp [B, C, Q]
          have hw' :
              |-(completedZetaSelectedHeight K n)| ^ 2 *
                  ‖poitouTransform (regularizedScaledTartar y δ)
                    (σ - completedZetaSelectedHeight K n * I)‖ ≤
                regularizedPoitouStripQuadraticDecayConstant y δ (-1) 2 := by
            simpa [sub_eq_add_neg,
              regularizedPoitouStripQuadraticDecayConstant] using hw
          exact mul_le_mul_of_nonneg_left hw' (by
            have hQ :=
              completedZetaSelectedHeightLogDerivativeQuadraticCoefficient_nonneg K
            linarith)
    have hlim :
        ∀ᵐ σ : ℝ, σ ∈ uIoc (-1) 2 →
          Tendsto (fun n ↦ F n σ) atTop (𝓝 0) :=
      Filter.Eventually.of_forall fun σ hσ ↦ by
        have hσIcc : σ ∈ Icc (-1 : ℝ) 2 := by grind
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hneg :
            Tendsto (fun n ↦ -(completedZetaSelectedHeight K n))
              atTop atBot := by
          simpa [Function.comp_def] using
            tendsto_neg_atTop_atBot.comp
              (tendsto_completedZetaSelectedHeight_atTop K)
        have hweighted :=
          (tendsto_sq_abs_mul_norm_poitouTransform_regularized_atBot
            hδ y σ).comp hneg
        have hmajor :
            Tendsto
              (fun n ↦ (4 * Q + 2) *
                (|-(completedZetaSelectedHeight K n)| ^ 2 *
                  ‖poitouTransform (regularizedScaledTartar y δ)
                    (σ - completedZetaSelectedHeight K n * I)‖))
              atTop (𝓝 0) := by
          simpa [Q, sub_eq_add_neg] using
            (tendsto_const_nhds.mul hweighted)
        simpa [F] using squeeze_zero'
          (Filter.Eventually.of_forall fun n ↦ norm_nonneg _)
          (Filter.Eventually.of_forall fun n ↦
            selected_negative_integrand_norm_le_weighted K hδ n hσIcc)
          hmajor
    have h :=
      intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (a := (-1 : ℝ)) (b := 2) (μ := volume)
        (l := atTop) (f := fun _ ↦ (0 : ℂ)) (fun _ ↦ B)
        hmeas hbound intervalIntegrable_const hlim
    simpa using h
  simpa [horizontalIntegral, F, sub_eq_add_neg] using hDCT

open Classical in
theorem regularizedSubtractedHorizontalVanishing_two
    (y : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    RegularizedSubtractedHorizontalVanishing K y δ 2 := by
  let T := completedZetaSelectedHeight K
  let q : ℂ → ℂ := fun s ↦
    poitouTransform (regularizedScaledTartar y δ) s *
      (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
        completedZetaPoleLogDeriv s)
  refine ⟨T, tendsto_completedZetaSelectedHeight_atTop K, ?_, ?_⟩
  · intro n
    refine ⟨completedZetaSelectedHeight_pos K n, ?_⟩
    intro z hz hside
    rcases hside with hleft | hright | hbottom | htop
    · apply poleClearedCompletedDedekindZetaContinuation_ne_zero_of_re_lt_zero K
      simp_all
    · apply poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
      simp_all
    · have hzRe : z.re ∈ Icc (-1 : ℝ) 5 :=
        ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
      have hne :=
        ((completedZetaSelectedHeight_spec K n).2.2 z.re hzRe).2.1
      rw [show z =
          (z.re : ℂ) - completedZetaSelectedHeight K n * I by
        apply Complex.ext
        · simp
        · simpa [T] using hbottom]
      simp_all
    · have hzRe : z.re ∈ Icc (-1 : ℝ) 5 :=
        ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
      have hne :=
        ((completedZetaSelectedHeight_spec K n).2.2 z.re hzRe).1.1
      rw [show z =
          (z.re : ℂ) + completedZetaSelectedHeight K n * I by
        apply Complex.ext
        · simp
        · simpa [T] using htop]
      simp_all
  · have hneg :=
      tendsto_selected_negative_horizontalIntegral K (y := y) hδ
    have hpos :=
      tendsto_selected_positive_horizontalIntegral K (y := y) hδ
    simpa [q, T, show (1 : ℝ) - 2 = -1 by norm_num] using hneg.sub hpos

open Classical in
theorem regularizedRightVerticalLowerBound_two
    {y : ℝ} (hy : y ≠ 0) :
    RegularizedRightVerticalLowerBound K y 2 := by
  apply regularizedRightVerticalLowerBound_of_forall_horizontalVanishing
    K hy (by norm_num)
  intro δ hδ
  exact regularizedSubtractedHorizontalVanishing_two K y hδ

end NumberField.Odlyzko

end

section

open NumberField

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem totallyComplexPoitouEstimate :
    TotallyComplexPoitouEstimate K := by
  apply totallyComplexPoitouEstimate_of_regularizedRightVerticalLowerBound
    K (σ := 2) (by norm_num)
  exact regularizedRightVerticalLowerBound_two K odlyzkoScale_pos.ne'

theorem odlyzkoBound
    (hdim : 18 ≤ Module.finrank ℚ K) :
    |(discr K : ℝ)| ≥ (8.25 : ℝ) ^ Module.finrank ℚ K :=
  odlyzkoBound_of_poitouEstimate K hdim (totallyComplexPoitouEstimate K)

end NumberField.Odlyzko

end
