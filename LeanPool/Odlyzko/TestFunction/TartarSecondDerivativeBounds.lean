/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.TestFunction.TartarDerivativeBounds

/-!
# Tartar Second Derivative Bounds

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A tartar amplitude second derivative integrand used in the Odlyzko-bound argument. -/
noncomputable def tartarAmplitudeSecondDerivativeIntegrand (x t : ℝ) : ℝ :=
  -(t ^ 2) * Tartar.weight t * Real.cos (x * t)

theorem hasDerivAt_tartarAmplitudeDerivativeIntegrand (x t : ℝ) :
    HasDerivAt (fun z : ℝ ↦ tartarAmplitudeDerivativeIntegrand z t)
      (tartarAmplitudeSecondDerivativeIntegrand x t) x := by
  unfold tartarAmplitudeDerivativeIntegrand
    tartarAmplitudeSecondDerivativeIntegrand
  have h := (((hasDerivAt_id x).mul_const t).sin.const_mul
    (-t * Tartar.weight t))
  grind

theorem sq_mul_tartarWeight_integrable :
    Integrable (fun t : ℝ ↦ t ^ 2 * Tartar.weight t) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_id.pow 2).mul tartarWeight_continuous
  · exact tartarWeight_hasCompactSupport.mul_left

theorem norm_tartarAmplitudeSecondDerivativeIntegrand_le (x t : ℝ) :
    ‖tartarAmplitudeSecondDerivativeIntegrand x t‖ ≤
      t ^ 2 * Tartar.weight t := by
  rw [tartarAmplitudeSecondDerivativeIntegrand, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_neg, abs_pow,
    abs_of_nonneg (tartarWeight_nonneg t), sq_abs]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (x * t))
      (mul_nonneg (sq_nonneg t) (tartarWeight_nonneg t))

theorem hasDerivAt_integral_tartarAmplitudeDerivativeIntegrand (x : ℝ) :
    HasDerivAt
      (fun z : ℝ ↦ ∫ t : ℝ, tartarAmplitudeDerivativeIntegrand z t)
      (∫ t : ℝ, tartarAmplitudeSecondDerivativeIntegrand x t) x := by
  exact
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (x₀ := x) (s := Set.univ)
      (F := tartarAmplitudeDerivativeIntegrand)
      (F' := tartarAmplitudeSecondDerivativeIntegrand)
      (bound := fun t : ℝ ↦ t ^ 2 * Tartar.weight t)
      univ_mem
      (by
        filter_upwards [] with z
        exact
          ((continuous_id.neg.mul tartarWeight_continuous).mul
            (Real.continuous_sin.comp
              (continuous_const.mul continuous_id))).aestronglyMeasurable)
      (by
        exact abs_mul_tartarWeight_integrable.mono'
          (by
            exact
              ((continuous_id.neg.mul tartarWeight_continuous).mul
                (Real.continuous_sin.comp
                  (continuous_const.mul continuous_id))).aestronglyMeasurable)
          (by
            filter_upwards [] with t
            exact norm_tartarAmplitudeDerivativeIntegrand_le x t))
      (by
        exact
          (((continuous_id.pow 2).neg.mul tartarWeight_continuous).mul
            (Real.continuous_cos.comp
              (continuous_const.mul continuous_id))).aestronglyMeasurable)
      (by
        filter_upwards [] with t z _
        exact norm_tartarAmplitudeSecondDerivativeIntegrand_le z t)
      sq_mul_tartarWeight_integrable
      (by
        filter_upwards [] with t z _
        exact hasDerivAt_tartarAmplitudeDerivativeIntegrand z t)).2

/-- A tartar amplitude second derivative used in the Odlyzko-bound argument. -/
noncomputable def tartarAmplitudeSecondDerivative (x : ℝ) : ℝ :=
  (3 / 4 : ℝ) *
    ∫ t : ℝ, tartarAmplitudeSecondDerivativeIntegrand x t

theorem hasDerivAt_deriv_tartarAmplitude (x : ℝ) :
    HasDerivAt (deriv Tartar.amplitude)
      (tartarAmplitudeSecondDerivative x) x := by
  rw [show deriv Tartar.amplitude =
      fun z : ℝ ↦ (3 / 4 : ℝ) *
        ∫ t : ℝ, tartarAmplitudeDerivativeIntegrand z t by
    funext z
    exact deriv_tartarAmplitude z]
  exact (hasDerivAt_integral_tartarAmplitudeDerivativeIntegrand x).const_mul _

theorem abs_tartarAmplitudeSecondDerivative_le (x : ℝ) :
    |tartarAmplitudeSecondDerivative x| ≤
      (3 / 4 : ℝ) * ∫ t : ℝ, t ^ 2 * Tartar.weight t := by
  unfold tartarAmplitudeSecondDerivative
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  gcongr
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le sq_mul_tartarWeight_integrable
    (.of_forall fun t ↦ norm_tartarAmplitudeSecondDerivativeIntegrand_le x t)

/-- A tartar test function second derivative bound used in the Odlyzko-bound argument. -/
noncomputable def tartarTestFunctionSecondDerivativeBound : ℝ :=
  2 * tartarAmplitudeDerivativeBound ^ 2 +
    2 * ((3 / 4 : ℝ) * ∫ t : ℝ, t ^ 2 * Tartar.weight t)

theorem tartarTestFunctionSecondDerivativeBound_nonneg :
    0 ≤ tartarTestFunctionSecondDerivativeBound := by
  unfold tartarTestFunctionSecondDerivativeBound
  have hint : 0 ≤ ∫ t : ℝ, t ^ 2 * Tartar.weight t :=
    integral_nonneg fun t ↦
      mul_nonneg (sq_nonneg t) (tartarWeight_nonneg t)
  positivity

/-- A tartar test function second derivative used in the Odlyzko-bound argument. -/
noncomputable def tartarTestFunctionSecondDerivative (x : ℝ) : ℝ :=
  2 * deriv Tartar.amplitude x ^ 2 +
    2 * Tartar.amplitude x * tartarAmplitudeSecondDerivative x

theorem hasDerivAt_deriv_tartarTestFunction (x : ℝ) :
    HasDerivAt (deriv Tartar.testFunction)
      (tartarTestFunctionSecondDerivative x) x := by
  rw [show deriv Tartar.testFunction =
      fun z : ℝ ↦ 2 * Tartar.amplitude z * deriv Tartar.amplitude z by
    funext z
    exact deriv_tartarTestFunction z]
  unfold tartarTestFunctionSecondDerivative
  have ha : HasDerivAt Tartar.amplitude (deriv Tartar.amplitude x) x := by
    convert hasDerivAt_tartarAmplitude x using 1
    exact deriv_tartarAmplitude x
  have h := (ha.const_mul 2).mul
    (hasDerivAt_deriv_tartarAmplitude x)
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun z ↦ rfl)).congr_deriv ?_
  ring

theorem abs_tartarTestFunctionSecondDerivative_le (x : ℝ) :
    |tartarTestFunctionSecondDerivative x| ≤
      tartarTestFunctionSecondDerivativeBound := by
  unfold tartarTestFunctionSecondDerivative
    tartarTestFunctionSecondDerivativeBound
  calc
    |2 * deriv Tartar.amplitude x ^ 2 +
        2 * Tartar.amplitude x * tartarAmplitudeSecondDerivative x| ≤
      |2 * deriv Tartar.amplitude x ^ 2| +
        |2 * Tartar.amplitude x * tartarAmplitudeSecondDerivative x| :=
      abs_add_le _ _
    _ ≤ 2 * tartarAmplitudeDerivativeBound ^ 2 +
        2 * ((3 / 4 : ℝ) * ∫ t : ℝ, t ^ 2 * Tartar.weight t) := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      apply add_le_add
      · gcongr
        exact abs_deriv_tartarAmplitude_le x
      · calc
          2 * |Tartar.amplitude x| *
              |tartarAmplitudeSecondDerivative x| ≤
            2 * 1 *
              ((3 / 4 : ℝ) * ∫ t : ℝ, t ^ 2 * Tartar.weight t) := by
                gcongr
                · exact abs_tartarAmplitude_le_one x
                · exact abs_tartarAmplitudeSecondDerivative_le x
          _ = _ := by ring

end NumberField.Odlyzko
