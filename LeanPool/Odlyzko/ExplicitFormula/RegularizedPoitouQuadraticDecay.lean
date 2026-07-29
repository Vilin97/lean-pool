/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouProfileSecondDerivative

/-!
# Regularized Poitou Quadratic Decay

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory
open scoped FourierTransform Real

namespace NumberField.Odlyzko

theorem fourier_poitouVerticalProfileSecondDerivative_regularized
    {δ : ℝ} (hδ : 0 < δ) (y σ w : ℝ) :
    𝓕 (poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ) w =
      (2 * Real.pi * I * w) •
        𝓕 (poitouVerticalProfileDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ) σ) w := by
  have hderiv :
      deriv
        (poitouVerticalProfileDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ) σ) =
        poitouVerticalProfileSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) σ := by
    funext x
    exact deriv_regularizedPoitouVerticalProfileDerivative y δ σ x
  have h :=
    congrFun (Real.fourier_deriv
      (poitouVerticalProfileDerivative_regularized_integrable hδ y σ)
      (differentiable_regularizedPoitouVerticalProfileDerivative y δ σ)
      (by
        rw [hderiv]
        exact
          poitouVerticalProfileSecondDerivative_regularized_integrable
            hδ y σ)) w
  simp_all

theorem fourier_poitouVerticalProfileSecondDerivative_regularized_eq_sq
    {δ : ℝ} (hδ : 0 < δ) (y σ w : ℝ) :
    𝓕 (poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ) w =
      ((2 * Real.pi * I * w) ^ 2) •
        𝓕 (regularizedPoitouVerticalProfile y δ σ) w := by
  rw [fourier_poitouVerticalProfileSecondDerivative_regularized hδ,
    fourier_poitouVerticalProfileDerivative_regularized hδ]
  simp only [smul_smul]
  ring

theorem sq_abs_mul_norm_poitouTransform_regularized_le
    {δ : ℝ} (hδ : 0 < δ) (y σ t : ℝ) :
    |t| ^ 2 *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ ≤
      ∫ x : ℝ,
        ‖poitouVerticalProfileSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) σ x‖ := by
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
  change |t| ^ 2 *
      ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ ≤ _
  rw [hnorm, Real.fourier_real_eq]
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

end NumberField.Odlyzko
