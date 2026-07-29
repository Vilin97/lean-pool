/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.TestFunction.Differentiability
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedTartar
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Tartar Derivative Bounds

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real

namespace NumberField.Odlyzko

/-- A tartar amplitude derivative bound used in the Odlyzko-bound argument. -/
noncomputable def tartarAmplitudeDerivativeBound : ℝ :=
  (3 / 4 : ℝ) * ∫ t : ℝ, |t| * Tartar.weight t

theorem tartarAmplitudeDerivativeBound_nonneg :
    0 ≤ tartarAmplitudeDerivativeBound := by
  unfold tartarAmplitudeDerivativeBound
  exact mul_nonneg (by norm_num) (integral_nonneg fun t ↦
    mul_nonneg (abs_nonneg t) (tartarWeight_nonneg t))

theorem abs_deriv_tartarAmplitude_le (x : ℝ) :
    |deriv Tartar.amplitude x| ≤ tartarAmplitudeDerivativeBound := by
  rw [deriv_tartarAmplitude, tartarAmplitudeDerivativeBound, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  gcongr
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le abs_mul_tartarWeight_integrable
    (.of_forall fun t ↦ norm_tartarAmplitudeDerivativeIntegrand_le x t)

theorem hasDerivAt_tartarTestFunction (x : ℝ) :
    HasDerivAt Tartar.testFunction
      (2 * Tartar.amplitude x * deriv Tartar.amplitude x) x := by
  change HasDerivAt (fun z ↦ Tartar.amplitude z ^ 2)
    (2 * Tartar.amplitude x * deriv Tartar.amplitude x) x
  have h := (hasDerivAt_tartarAmplitude x).mul
    (hasDerivAt_tartarAmplitude x)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ by
    simp only [Pi.mul_apply, pow_two])).congr_deriv ?_
  rw [deriv_tartarAmplitude]
  ring

theorem deriv_tartarTestFunction (x : ℝ) :
    deriv Tartar.testFunction x =
      2 * Tartar.amplitude x * deriv Tartar.amplitude x :=
  (hasDerivAt_tartarTestFunction x).deriv

theorem abs_deriv_tartarTestFunction_le (x : ℝ) :
    |deriv Tartar.testFunction x| ≤
      2 * tartarAmplitudeDerivativeBound := by
  rw [deriv_tartarTestFunction, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    2 * |Tartar.amplitude x| * |deriv Tartar.amplitude x| ≤
        2 * 1 * tartarAmplitudeDerivativeBound := by
      gcongr
      · exact abs_tartarAmplitude_le_one x
      · exact abs_deriv_tartarAmplitude_le x
    _ = _ := by ring

theorem hasDerivAt_scaledTartarTestFunction (y x : ℝ) :
    HasDerivAt (scaledTartarTestFunction y)
      (y * deriv Tartar.testFunction (y * x)) x := by
  unfold scaledTartarTestFunction
  have h := (hasDerivAt_tartarTestFunction (y * x)).comp x
    ((hasDerivAt_id x).const_mul y)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦
    rfl)).congr_deriv ?_
  rw [deriv_tartarTestFunction]
  ring

/-- A regularized scaled tartar derivative used in the Odlyzko-bound argument. -/
noncomputable def regularizedScaledTartarDerivative
    (y δ x : ℝ) : ℝ :=
  (y * deriv Tartar.testFunction (y * x) -
      2 * δ * x * scaledTartarTestFunction y x) *
    Real.exp (-δ * x ^ 2)

theorem hasDerivAt_regularizedScaledTartar (y δ x : ℝ) :
    HasDerivAt (regularizedScaledTartar y δ)
      (regularizedScaledTartarDerivative y δ x) x := by
  unfold regularizedScaledTartar regularizedScaledTartarDerivative
  have hgauss :
      HasDerivAt (fun z : ℝ ↦ Real.exp (-δ * z ^ 2))
        (-2 * δ * x * Real.exp (-δ * x ^ 2)) x := by
    have h := (((hasDerivAt_id x).pow 2).const_mul (-δ)).exp
    convert h using 1 <;>
      simp only [Pi.pow_apply, id_eq]
    ring
  have hprod :=
    (hasDerivAt_scaledTartarTestFunction y x).mul hgauss
  exact hprod.congr_deriv (by ring)

theorem continuous_regularizedScaledTartarDerivative (y δ : ℝ) :
    Continuous (regularizedScaledTartarDerivative y δ) := by
  have hderivTest : Continuous (deriv Tartar.testFunction) := by
    rw [show deriv Tartar.testFunction = fun x ↦
        2 * Tartar.amplitude x * deriv Tartar.amplitude x by
      funext x
      exact deriv_tartarTestFunction x]
    exact (continuous_const.mul differentiable_tartarAmplitude.continuous).mul
      continuous_deriv_tartarAmplitude
  have hscaled : Continuous (scaledTartarTestFunction y) := by
    unfold scaledTartarTestFunction
    exact tartarTestFunction_continuous.comp
      (continuous_const.mul continuous_id)
  unfold regularizedScaledTartarDerivative
  exact ((continuous_const.mul
    (hderivTest.comp (continuous_const.mul continuous_id))).sub
      ((continuous_const.mul continuous_id).mul hscaled)).mul
        (by fun_prop : Continuous
          (fun x : ℝ ↦ Real.exp (-δ * x ^ 2)))

theorem abs_regularizedScaledTartarDerivative_le
    {δ : ℝ} (hδ : 0 ≤ δ) (y x : ℝ) :
    |regularizedScaledTartarDerivative y δ x| ≤
      (2 * |y| * tartarAmplitudeDerivativeBound + 2 * δ * |x|) *
        Real.exp (-δ * x ^ 2) := by
  unfold regularizedScaledTartarDerivative
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    |y * deriv Tartar.testFunction (y * x) -
        2 * δ * x * scaledTartarTestFunction y x| *
          Real.exp (-δ * x ^ 2) ≤
      (|y * deriv Tartar.testFunction (y * x)| +
        |2 * δ * x * scaledTartarTestFunction y x|) *
          Real.exp (-δ * x ^ 2) := by
      gcongr
      grind
    _ ≤ (2 * |y| * tartarAmplitudeDerivativeBound + 2 * δ * |x|) *
          Real.exp (-δ * x ^ 2) := by
      gcongr
      · rw [abs_mul]
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left
            (abs_deriv_tartarTestFunction_le (y * x)) (abs_nonneg y)
      · rw [abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg hδ,
          abs_of_nonneg (scaledTartarTestFunction_nonneg y x)]
        have hcoef : 0 ≤ 2 * δ * |x| :=
          mul_nonneg (mul_nonneg (by norm_num) hδ) (abs_nonneg x)
        change 2 * δ * |x| * Tartar.testFunction (y * x) ≤
          2 * δ * |x|
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (tartarTestFunction_le_one (y * x)) hcoef

end NumberField.Odlyzko
