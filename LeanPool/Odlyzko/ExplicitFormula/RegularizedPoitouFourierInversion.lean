/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouFourierIntegrable

/-!
# Regularized Poitou Fourier Inversion

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace

namespace NumberField.Odlyzko

theorem integral_fourier_regularizedPoitouVerticalProfile
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    (∫ w : ℝ, 𝓕 (regularizedPoitouVerticalProfile y δ σ) w) =
      regularizedPoitouVerticalProfile y δ σ 0 := by
  have hinv :=
    (regularizedPoitouVerticalProfile_integrable hδ σ).fourierInv_fourier_eq
      (fourier_regularizedPoitouVerticalProfile_integrable hδ y σ)
      (differentiable_regularizedPoitouVerticalProfile y δ σ 0
        |>.continuousAt)
  simpa [Real.fourierInv_eq] using hinv

theorem integral_poitouTransform_regularized_vertical
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I)) =
      (2 * Real.pi : ℂ) := by
  let F : ℝ → ℂ := 𝓕 (regularizedPoitouVerticalProfile y δ σ)
  have hscale := Measure.integral_comp_mul_left
    F (-1 / (2 * Real.pi))
  have harg :
      (fun t : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I)) =
      fun t : ℝ ↦ F ((-1 / (2 * Real.pi)) * t) := by
    funext t
    rw [poitouTransform_regularizedScaledTartar_eq_fourier]
    grind
  rw [harg, hscale,
    integral_fourier_regularizedPoitouVerticalProfile hδ y σ]
  have habs :
      |(-1 / (2 * Real.pi))⁻¹| = 2 * Real.pi := by
    rw [inv_div, div_neg, div_one, abs_neg,
      abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  rw [habs]
  unfold regularizedPoitouVerticalProfile poitouKernel
  simp

end NumberField.Odlyzko
