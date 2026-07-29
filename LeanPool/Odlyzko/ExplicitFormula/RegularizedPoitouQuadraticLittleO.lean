/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouQuadraticDecay
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Regularized Poitou Quadratic Little O

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

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
