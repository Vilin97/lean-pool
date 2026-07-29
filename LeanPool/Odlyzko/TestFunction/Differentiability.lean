/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.TestFunction.Fourier
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiability

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A tartar amplitude derivative integrand used in the Odlyzko-bound argument. -/
noncomputable def tartarAmplitudeDerivativeIntegrand (x t : ℝ) : ℝ :=
  -t * Tartar.weight t * Real.sin (x * t)

theorem hasDerivAt_tartarWeight_mul_cos (x t : ℝ) :
    HasDerivAt (fun z : ℝ ↦ Tartar.weight t * Real.cos (z * t))
      (tartarAmplitudeDerivativeIntegrand x t) x := by
  unfold tartarAmplitudeDerivativeIntegrand
  have hcos :=
    ((hasDerivAt_id x).mul_const t).cos.const_mul (Tartar.weight t)
  grind

theorem abs_mul_tartarWeight_integrable :
    Integrable (fun t : ℝ ↦ |t| * Tartar.weight t) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact continuous_abs.mul tartarWeight_continuous
  · exact tartarWeight_hasCompactSupport.mul_left

theorem norm_tartarAmplitudeDerivativeIntegrand_le (x t : ℝ) :
    ‖tartarAmplitudeDerivativeIntegrand x t‖ ≤
      |t| * Tartar.weight t := by
  rw [tartarAmplitudeDerivativeIntegrand, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (tartarWeight_nonneg t)]
  calc
    |t| * Tartar.weight t * |Real.sin (x * t)| ≤
        |t| * Tartar.weight t * 1 := by
      exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
        (mul_nonneg (abs_nonneg _) (tartarWeight_nonneg t))
    _ = _ := mul_one _

theorem hasDerivAt_integral_tartarWeight_mul_cos (x : ℝ) :
    HasDerivAt
      (fun z : ℝ ↦ ∫ t : ℝ,
        Tartar.weight t * Real.cos (z * t))
      (∫ t : ℝ, tartarAmplitudeDerivativeIntegrand x t) x := by
  have hresult :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (x₀ := x) (s := Set.univ)
      (F := fun z t : ℝ ↦ Tartar.weight t * Real.cos (z * t))
      (F' := tartarAmplitudeDerivativeIntegrand)
      (bound := fun t : ℝ ↦ |t| * Tartar.weight t)
      univ_mem
      (by
        filter_upwards [] with z
        exact (tartarWeight_continuous.mul
          (by fun_prop : Continuous (fun t : ℝ ↦ Real.cos (z * t))))
          |>.aestronglyMeasurable)
      (tartarWeight_mul_cos_integrable x)
      (by
        have hc : Continuous
            (tartarAmplitudeDerivativeIntegrand x) := by
          unfold tartarAmplitudeDerivativeIntegrand
          exact (continuous_id.neg.mul tartarWeight_continuous).mul
            (Real.continuous_sin.comp
              (continuous_const.mul continuous_id))
        exact hc.aestronglyMeasurable)
      (by
        filter_upwards [] with t z _
        exact norm_tartarAmplitudeDerivativeIntegrand_le z t)
      abs_mul_tartarWeight_integrable
      (by
        filter_upwards [] with t z _
        exact hasDerivAt_tartarWeight_mul_cos z t)
  simp_all

theorem hasDerivAt_tartarAmplitude (x : ℝ) :
    HasDerivAt Tartar.amplitude
      ((3 / 4 : ℝ) *
        ∫ t : ℝ, tartarAmplitudeDerivativeIntegrand x t) x := by
  have h :=
    (hasDerivAt_integral_tartarWeight_mul_cos x).const_mul (3 / 4 : ℝ)
  have heq :
      Tartar.amplitude =
        fun z : ℝ ↦ (3 / 4 : ℝ) *
          ∫ t : ℝ, Tartar.weight t * Real.cos (z * t) := by
    funext z
    exact tartarAmplitude_eq_cosineTransform z
  simp_all

theorem differentiable_tartarAmplitude :
    Differentiable ℝ Tartar.amplitude :=
  fun x ↦ (hasDerivAt_tartarAmplitude x).differentiableAt

theorem continuous_integral_tartarAmplitudeDerivativeIntegrand :
    Continuous
      (fun x : ℝ ↦
        ∫ t : ℝ, tartarAmplitudeDerivativeIntegrand x t) := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto
    (fun z : ℝ ↦ ∫ t : ℝ, tartarAmplitudeDerivativeIntegrand z t)
    (𝓝 x)
    (𝓝 (∫ t : ℝ, tartarAmplitudeDerivativeIntegrand x t))
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun t : ℝ ↦ |t| * Tartar.weight t)
  · filter_upwards [] with z
    have hc : Continuous
        (tartarAmplitudeDerivativeIntegrand z) := by
      unfold tartarAmplitudeDerivativeIntegrand
      exact (continuous_id.neg.mul tartarWeight_continuous).mul
        (Real.continuous_sin.comp
          (continuous_const.mul continuous_id))
    exact hc.aestronglyMeasurable
  · filter_upwards [] with z
    filter_upwards [] with t
    exact norm_tartarAmplitudeDerivativeIntegrand_le z t
  · exact abs_mul_tartarWeight_integrable
  · filter_upwards [] with t
    unfold tartarAmplitudeDerivativeIntegrand
    exact (by fun_prop : Continuous
      (fun z : ℝ ↦ -t * Tartar.weight t * Real.sin (z * t))).continuousAt

theorem deriv_tartarAmplitude (x : ℝ) :
    deriv Tartar.amplitude x =
      (3 / 4 : ℝ) *
        ∫ t : ℝ, tartarAmplitudeDerivativeIntegrand x t :=
  (hasDerivAt_tartarAmplitude x).deriv

theorem continuous_deriv_tartarAmplitude :
    Continuous (deriv Tartar.amplitude) := by
  rw [show deriv Tartar.amplitude =
      fun x : ℝ ↦ (3 / 4 : ℝ) *
        ∫ t : ℝ, tartarAmplitudeDerivativeIntegrand x t by
    funext x
    exact deriv_tartarAmplitude x]
  exact continuous_const.mul
    continuous_integral_tartarAmplitudeDerivativeIntegrand

end NumberField.Odlyzko
