/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedArchimedeanKernel

/-!
# Regularized Gauss Kernel Integral

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

theorem norm_gaussDigammaIntegrand_vertical_le
    (σ t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖gaussDigammaIntegrand (σ + t * I) x‖ ≤
      (Real.exp (-x) + Real.exp (-σ * x)) /
        (1 - Real.exp (-x)) := by
  have hdenPos : 0 < 1 - Real.exp (-x) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))
  have hden :
      ‖(1 : ℂ) - Complex.exp (-x)‖ =
        1 - Real.exp (-x) := by
    rw [show Complex.exp (-x) = (Real.exp (-x) : ℝ) by
      simp]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenPos]
  have hnum :
      ‖Complex.exp (-x) -
          Complex.exp (-(σ + t * I) * x)‖ ≤
        Real.exp (-x) + Real.exp (-σ * x) := by
    calc
      _ ≤ ‖Complex.exp (-x)‖ +
          ‖Complex.exp (-(σ + t * I) * x)‖ :=
        norm_sub_le _ _
      _ = _ := by
        rw [Complex.norm_exp, Complex.norm_exp]
        simp
  rw [gaussDigammaIntegrand, norm_div, hden]
  exact div_le_div_of_nonneg_right hnum hdenPos.le

theorem integrable_poitouTransform_regularized_mul_cexp_neg
    {δ : ℝ} (hδ : 0 < δ) (y σ x : ℝ) :
    Integrable (fun t : ℝ ↦
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        Complex.exp (-(σ + t * I) * x)) := by
  have hΦ :=
    poitouTransform_regularizedScaledTartar_vertical_integrable hδ y σ
  apply hΦ.mul_bdd
  · fun_prop
  · filter_upwards [] with t
    rw [Complex.norm_exp]
    have hre : (-(σ + t * I) * (x : ℂ)).re = -σ * x := by
      simp
    rw [hre]

theorem integral_poitouTransform_regularized_mul_gaussDigammaIntegrand
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        gaussDigammaIntegrand (σ + t * I) x) =
      ((2 * Real.pi *
        inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ) := by
  let Φ : ℝ → ℂ := fun t ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I)
  let d : ℂ := 1 - Complex.exp (-x)
  have hΦ : Integrable Φ :=
    poitouTransform_regularizedScaledTartar_vertical_integrable hδ y σ
  have hfirst : Integrable (fun t : ℝ ↦
      Φ t * Complex.exp (-x)) :=
    hΦ.mul_const _
  have hsecond : Integrable (fun t : ℝ ↦
      Φ t * Complex.exp (-(σ + t * I) * x)) :=
    integrable_poitouTransform_regularized_mul_cexp_neg
      hδ y σ x
  have hintegrand :
      (fun t : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          gaussDigammaIntegrand (σ + t * I) x) =
        fun t : ℝ ↦
          (Φ t * Complex.exp (-x) -
            Φ t * Complex.exp (-(σ + t * I) * x)) / d := by
    funext t
    unfold gaussDigammaIntegrand
    grind
  have hsecondValue :
      (∫ t : ℝ,
        Φ t * Complex.exp (-(σ + t * I) * x)) =
        2 * Real.pi *
          (poitouKernel (regularizedScaledTartar y δ) x : ℂ) *
            Complex.exp (-x / 2) := by
    rw [show
        (fun t : ℝ ↦
          Φ t * Complex.exp (-(σ + t * I) * x)) =
          fun t : ℝ ↦
            poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
              Complex.exp (-x * (σ + t * I)) by
      grind]
    exact integral_poitouTransform_regularized_mul_exp_neg
      hδ y σ x
  rw [hintegrand, integral_div, integral_sub hfirst hsecond,
    integral_mul_const,
    integral_poitouTransform_regularized_vertical hδ y σ,
    hsecondValue]
  have hkernel :=
    exp_sub_regularizedPoitouKernel_mul_exp_neg_half_div y δ hx
  have hkernelC := congrArg (fun r : ℝ ↦ (r : ℂ)) hkernel
  simp only [Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_exp, Complex.ofReal_mul] at hkernelC
  norm_num at hkernelC
  dsimp only [d]
  push_cast
  grind

end NumberField.Odlyzko
