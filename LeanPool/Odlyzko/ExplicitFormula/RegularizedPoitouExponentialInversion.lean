/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouFourierInversion

/-!
# Regularized Poitou Exponential Inversion

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace

namespace NumberField.Odlyzko

theorem integral_fourier_mul_cexp_regularizedPoitouVerticalProfile
    {δ : ℝ} (hδ : 0 < δ) (y σ a : ℝ) :
    (∫ w : ℝ,
      Complex.exp (2 * Real.pi * I * w * a) *
        𝓕 (regularizedPoitouVerticalProfile y δ σ) w) =
      regularizedPoitouVerticalProfile y δ σ a := by
  have hinv :=
    (regularizedPoitouVerticalProfile_integrable hδ σ).fourierInv_fourier_eq
      (fourier_regularizedPoitouVerticalProfile_integrable hδ y σ)
      (differentiable_regularizedPoitouVerticalProfile y δ σ a
        |>.continuousAt)
  rw [Real.fourierInv_eq'] at hinv
  convert hinv using 1
  apply integral_congr_ae
  filter_upwards [] with w
  rw [smul_eq_mul]
  congr 2
  norm_num
  ring

theorem integral_poitouTransform_regularized_mul_exp_neg
    {δ : ℝ} (hδ : 0 < δ) (y σ a : ℝ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        Complex.exp (-a * (σ + t * I))) =
      (2 * Real.pi *
        (poitouKernel (regularizedScaledTartar y δ) a : ℂ) *
          Complex.exp (-a / 2)) := by
  let F : ℝ → ℂ := 𝓕 (regularizedPoitouVerticalProfile y δ σ)
  let Q : ℝ → ℂ := fun w ↦
    Complex.exp (2 * Real.pi * I * w * a) * F w *
      Complex.exp (-a * σ)
  have hscale := Measure.integral_comp_mul_left
    Q (-1 / (2 * Real.pi))
  have harg :
      (fun t : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          Complex.exp (-a * (σ + t * I))) =
      fun t : ℝ ↦ Q ((-1 / (2 * Real.pi)) * t) := by
    funext t
    rw [poitouTransform_regularizedScaledTartar_eq_fourier]
    dsimp [F, Q]
    have hexp :
      Complex.exp (-a * (σ + t * I)) =
          Complex.exp
              (2 * Real.pi * I *
                (((-1 / (2 * Real.pi)) * t : ℝ) : ℂ) * (a : ℂ)) *
            Complex.exp (-a * σ) := by
      rw [← Complex.exp_add]
      push_cast
      field_simp [Real.pi_ne_zero]
      ring_nf
    grind
  have habs :
      |(-1 / (2 * Real.pi))⁻¹| = 2 * Real.pi := by
    rw [inv_div, div_neg, div_one, abs_neg,
      abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  rw [harg, hscale, habs]
  rw [show (∫ w : ℝ, Q w) =
      (∫ w : ℝ,
        Complex.exp (2 * Real.pi * I * w * a) * F w) *
          Complex.exp (-a * σ) by
    dsimp [Q]
    rw [integral_mul_const]]
  rw [show (∫ w : ℝ,
      Complex.exp (2 * Real.pi * I * w * a) * F w) =
        regularizedPoitouVerticalProfile y δ σ a by
    dsimp [F]
    exact
      integral_fourier_mul_cexp_regularizedPoitouVerticalProfile
        hδ y σ a]
  unfold regularizedPoitouVerticalProfile
  rw [Complex.real_smul]
  push_cast
  calc
    (2 * Real.pi : ℂ) *
          ((poitouKernel (regularizedScaledTartar y δ) a : ℂ) *
            Complex.exp ((σ - 1 / 2) * a) *
            Complex.exp (-a * σ)) =
        (2 * Real.pi : ℂ) *
          (poitouKernel (regularizedScaledTartar y δ) a : ℂ) *
          (Complex.exp ((σ - 1 / 2) * a) *
            Complex.exp (-a * σ)) := by
      ring
    _ = _ := by
      rw [← Complex.exp_add]
      grind

end NumberField.Odlyzko
