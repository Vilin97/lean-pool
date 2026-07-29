/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.PoitouTransform
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Tartar Poitou Transform

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set

namespace NumberField.Odlyzko

/-- A scaled tartar test function used in the Odlyzko-bound argument. -/
noncomputable def scaledTartarTestFunction (y : ℝ) (x : ℝ) : ℝ :=
  Tartar.testFunction (y * x)

theorem scaledTartarTestFunction_nonneg (y x : ℝ) :
    0 ≤ scaledTartarTestFunction y x :=
  tartarTestFunction_nonneg _

theorem scaledTartarTestFunction_even (y x : ℝ) :
    scaledTartarTestFunction y (-x) = scaledTartarTestFunction y x := by
  rw [scaledTartarTestFunction, scaledTartarTestFunction,
    mul_neg, tartarTestFunction_neg]

theorem scaledTartarTestFunction_integrable {y : ℝ} (hy : y ≠ 0) :
    Integrable (scaledTartarTestFunction y) := by
  change Integrable (fun x : ℝ ↦ Tartar.testFunction (y * x))
  exact tartarTestFunction_integrable.comp_mul_left' hy

theorem exp_sub_half_mul_div_cosh_le_two
    {σ x : ℝ} (hσ : σ ∈ Icc 0 1) :
    Real.exp ((σ - 1 / 2) * x) / Real.cosh (x / 2) ≤ 2 := by
  have hcosh : 0 < Real.cosh (x / 2) := Real.cosh_pos _
  rw [div_le_iff₀ hcosh]
  rw [Real.cosh_eq]
  by_cases hx : 0 ≤ x
  · have hexp :
        Real.exp ((σ - 1 / 2) * x) ≤ Real.exp (x / 2) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right
        (show σ - 1 / 2 ≤ 1 / 2 by grind) hx
      linarith
    nlinarith [Real.exp_pos (-(x / 2))]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hexp :
        Real.exp ((σ - 1 / 2) * x) ≤ Real.exp (-(x / 2)) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonpos_right
        (show -(1 / 2) ≤ σ - 1 / 2 by simp_all) hx'
      linarith
    nlinarith [Real.exp_pos (x / 2)]

theorem norm_poitouTransformIntegrand_scaledTartar_le
    {y : ℝ} {s : ℂ} (hs : s.re ∈ Icc 0 1) (x : ℝ) :
    ‖poitouTransformIntegrand (scaledTartarTestFunction y) s x‖ ≤
      2 * scaledTartarTestFunction y x := by
  rw [poitouTransformIntegrand, norm_mul, Complex.norm_real,
    poitouKernel, Real.norm_eq_abs]
  have hcosh : 0 < Real.cosh (x / 2) := Real.cosh_pos _
  rw [abs_div, abs_of_nonneg (scaledTartarTestFunction_nonneg y x),
    abs_of_nonneg hcosh.le, Complex.norm_exp, mul_re, ofReal_re,
    ofReal_im, mul_zero, sub_zero, sub_re]
  norm_num
  calc
    scaledTartarTestFunction y x / Real.cosh (x / 2) *
          Real.exp ((s.re - 1 / 2) * x) =
        scaledTartarTestFunction y x *
          (Real.exp ((s.re - 1 / 2) * x) / Real.cosh (x / 2)) := by ring
    _ ≤ scaledTartarTestFunction y x * 2 := by
      exact mul_le_mul_of_nonneg_left
        (exp_sub_half_mul_div_cosh_le_two (x := x) hs)
        (scaledTartarTestFunction_nonneg y x)
    _ = _ := by ring

theorem continuous_poitouTransformIntegrand_scaledTartar
    (y : ℝ) (s : ℂ) :
    Continuous (poitouTransformIntegrand (scaledTartarTestFunction y) s) := by
  change Continuous (fun x : ℝ ↦
    ((Tartar.testFunction (y * x) / Real.cosh (x / 2) : ℝ) : ℂ) *
      Complex.exp ((s - 1 / 2) * x))
  have hquot : Continuous (fun x : ℝ ↦
      Tartar.testFunction (y * x) / Real.cosh (x / 2)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    exact (Real.cosh_pos _).ne'
  exact (Complex.continuous_ofReal.comp hquot).mul (by fun_prop)

theorem poitouTransformIntegrand_scaledTartar_integrable
    {y : ℝ} (hy : y ≠ 0) {s : ℂ} (hs : s.re ∈ Icc 0 1) :
    Integrable (poitouTransformIntegrand (scaledTartarTestFunction y) s) := by
  have hmajor :
      Integrable (fun x : ℝ ↦ (2 : ℝ) * scaledTartarTestFunction y x) :=
    (scaledTartarTestFunction_integrable hy).const_mul 2
  apply hmajor.mono'
  · exact (continuous_poitouTransformIntegrand_scaledTartar y s).aestronglyMeasurable
  · filter_upwards [] with x
    exact
      norm_poitouTransformIntegrand_scaledTartar_le (y := y) hs x

theorem integral_scaledTartarTestFunction
    {y : ℝ} (hy : 0 < y) :
    (∫ x : ℝ, scaledTartarTestFunction y x) =
      6 * Real.pi / (5 * y) := by
  have hchange := Measure.integral_comp_mul_left Tartar.testFunction y
  rw [abs_of_pos (inv_pos.mpr hy), smul_eq_mul,
    integral_tartarTestFunction] at hchange
  change (∫ x : ℝ, Tartar.testFunction (y * x)) = _ at hchange
  change (∫ x : ℝ, Tartar.testFunction (y * x)) =
    6 * Real.pi / (5 * y)
  grind

theorem poitouTransform_scaledTartar_one
    {y : ℝ} (hy : 0 < y) :
    poitouTransform (scaledTartarTestFunction y) 1 =
      (6 * Real.pi / (5 * y) : ℝ) := by
  rw [poitouTransform_one_eq_integral
    (scaledTartarTestFunction_even y)
    (poitouTransformIntegrand_scaledTartar_integrable hy.ne' (by simp)),
    integral_scaledTartarTestFunction hy]

/-- A poitou transform derivative integrand used in the Odlyzko-bound argument. -/
noncomputable def poitouTransformDerivativeIntegrand
    (f : ℝ → ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  x * poitouTransformIntegrand f s x

theorem hasDerivAt_poitouTransformIntegrand
    (f : ℝ → ℝ) (s : ℂ) (x : ℝ) :
    HasDerivAt (fun z ↦ poitouTransformIntegrand f z x)
      (poitouTransformDerivativeIntegrand f s x) s := by
  unfold poitouTransformDerivativeIntegrand poitouTransformIntegrand
  have hlin :
      HasDerivAt (fun z : ℂ ↦ (z - 1 / 2) * (x : ℂ)) x s := by
    simpa using
      ((hasDerivAt_id s).sub_const ((2 : ℂ)⁻¹)).mul_const (x : ℂ)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    hlin.cexp.const_mul (poitouKernel f x : ℂ)

end NumberField.Odlyzko
