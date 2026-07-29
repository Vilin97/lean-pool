/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouQuadraticDecay
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Regularized Poitou Fourier Integrable

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace

namespace NumberField.Odlyzko

theorem norm_fourier_regularizedPoitouVerticalProfile_le_integral
    {δ : ℝ} (_hδ : 0 < δ) (y σ w : ℝ) :
    ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ ≤
      ∫ x : ℝ, ‖regularizedPoitouVerticalProfile y δ σ x‖ := by
  rw [Real.fourier_real_eq]
  calc
    ‖∫ x : ℝ, 𝐞 (-(x * w)) •
        regularizedPoitouVerticalProfile y δ σ x‖ ≤
      ∫ x : ℝ, ‖𝐞 (-(x * w)) •
        regularizedPoitouVerticalProfile y δ σ x‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by simp

theorem sq_mul_norm_fourier_regularizedPoitouVerticalProfile_le_integral
    {δ : ℝ} (hδ : 0 < δ) (y σ w : ℝ) :
    w ^ 2 * ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ ≤
      ∫ x : ℝ,
        ‖poitouVerticalProfileSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) σ x‖ := by
  let q : ℂ := (2 * Real.pi : ℂ) * I * (w : ℂ)
  have hfourier :=
    fourier_poitouVerticalProfileSecondDerivative_regularized_eq_sq
      hδ y σ w
  have hfactor :
      ‖q ^ 2‖ = (2 * Real.pi) ^ 2 * w ^ 2 := by
    dsimp [q]
    rw [norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs]
    norm_num
    grind
  have hscale : w ^ 2 ≤ (2 * Real.pi) ^ 2 * w ^ 2 := by
    have hp : 1 ≤ (2 * Real.pi) ^ 2 := by
      nlinarith [Real.pi_gt_three]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hp (sq_nonneg w)
  calc
    w ^ 2 * ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ ≤
        ((2 * Real.pi) ^ 2 * w ^ 2) *
          ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ :=
      mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
    _ =
        ‖𝓕 (poitouVerticalProfileSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) σ) w‖ := by
      rw [hfourier, norm_smul, hfactor]
    _ ≤ _ := by
      rw [Real.fourier_real_eq]
      calc
        ‖∫ v : ℝ, 𝐞 (-(v * w)) •
            poitouVerticalProfileSecondDerivative
              (regularizedScaledTartar y δ)
              (regularizedScaledTartarDerivative y δ)
              (regularizedScaledTartarSecondDerivative y δ) σ v‖ ≤
          ∫ v : ℝ, ‖𝐞 (-(v * w)) •
            poitouVerticalProfileSecondDerivative
              (regularizedScaledTartar y δ)
              (regularizedScaledTartarDerivative y δ)
              (regularizedScaledTartarSecondDerivative y δ) σ v‖ :=
            norm_integral_le_integral_norm _
        _ = _ := by simp

theorem fourier_regularizedPoitouVerticalProfile_integrable
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    Integrable (𝓕 (regularizedPoitouVerticalProfile y δ σ)) := by
  let M : ℝ :=
    ∫ x : ℝ, ‖regularizedPoitouVerticalProfile y δ σ x‖
  let N : ℝ :=
    ∫ x : ℝ,
      ‖poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ x‖
  have hmajor :
      Integrable (fun w : ℝ ↦ (M + N) * (1 + w ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (M + N)
  apply hmajor.mono'
  · exact
      (VectorFourier.fourierIntegral_continuous
        Real.continuous_fourierChar (innerSL ℝ).continuous₂
        (regularizedPoitouVerticalProfile_integrable hδ σ))
        |>.aestronglyMeasurable
  · filter_upwards [] with w
    have hzero :
        ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ ≤ M :=
      norm_fourier_regularizedPoitouVerticalProfile_le_integral
        hδ y σ w
    have htwo :
        w ^ 2 * ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ ≤ N :=
      sq_mul_norm_fourier_regularizedPoitouVerticalProfile_le_integral
        hδ y σ w
    rw [← div_eq_mul_inv,
      le_div_iff₀ (by positivity : 0 < 1 + w ^ 2)]
    nlinarith

theorem poitouTransform_regularizedScaledTartar_vertical_integrable
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    Integrable (fun t : ℝ ↦
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I)) := by
  let F : ℝ → ℂ := 𝓕 (regularizedPoitouVerticalProfile y δ σ)
  have hF : Integrable F :=
    fourier_regularizedPoitouVerticalProfile_integrable hδ y σ
  have hscale : (-1 / (2 * Real.pi) : ℝ) ≠ 0 := by
    positivity
  have hcomp : Integrable (fun t : ℝ ↦
      F ((-1 / (2 * Real.pi)) * t)) :=
    hF.comp_mul_left' hscale
  apply (integrable_congr (ae_of_all _ fun t ↦ ?_)).mpr hcomp
  rw [poitouTransform_regularizedScaledTartar_eq_fourier]
  grind

end NumberField.Odlyzko
