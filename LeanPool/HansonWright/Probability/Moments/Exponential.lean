/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Exponential-Moment Bounds

Jensen and logarithmic moment-generating-function bounds for real random variables.

## Main definitions

This module introduces no new definitions.

## Main results

* `jensen_exp`: Jensen's inequality for the exponential function.
* `mean_le_log_mgf`: an expectation bound through a positive exponential moment.
-/

open MeasureTheory Set Real Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Jensen's inequality for exp: exp(E[X]) ≤ E[exp(X)].
    This uses ConvexOn.map_integral_le from Mathlib.Analysis.Convex.Integral. -/
theorem jensen_exp {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_int : Integrable X μ) (hexpX_int : Integrable (fun ω => exp (X ω)) μ) :
    exp (∫ ω, X ω ∂μ) ≤ ∫ ω, exp (X ω) ∂μ := by
  have hconv : ConvexOn ℝ Set.univ exp := convexOn_exp
  have hcont : ContinuousOn exp Set.univ := continuous_exp.continuousOn
  have hclosed : IsClosed (Set.univ : Set ℝ) := isClosed_univ
  exact hconv.map_integral_le hcont hclosed (by simp) hX_int hexpX_int

/-- MGF bound: E[X] ≤ (1/t) · log E[exp(tX)] for t > 0.
    This follows from Jensen's inequality for the convex function exp. -/
theorem mean_le_log_mgf {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_int : Integrable X μ)
    {t : ℝ} (ht : 0 < t) (hexpX_int : Integrable (fun ω => exp (t * X ω)) μ) :
    ∫ ω, X ω ∂μ ≤ (1/t) * log (∫ ω, exp (t * X ω) ∂μ) := by
  have hconv : ConvexOn ℝ Set.univ exp := convexOn_exp
  have hcont : ContinuousOn exp Set.univ := continuous_exp.continuousOn
  have hclosed : IsClosed (Set.univ : Set ℝ) := isClosed_univ
  have htX_int : Integrable (fun ω => t * X ω) μ := hX_int.const_mul t
  have h := hconv.map_integral_le hcont hclosed (by simp) htX_int hexpX_int
  have h1 : ∫ ω, t * X ω ∂μ = t * ∫ ω, X ω ∂μ := integral_const_mul t X
  -- h : exp (∫ x, t * X x ∂μ) ≤ ∫ x, exp (t * X x) ∂μ
  have h2 : t * ∫ ω, X ω ∂μ ≤ log (∫ ω, exp (t * X ω) ∂μ) := by
    have hexp_bound : exp (t * ∫ ω, X ω ∂μ) ≤ ∫ ω, exp (t * X ω) ∂μ := h1 ▸ h
    calc t * ∫ ω, X ω ∂μ = log (exp (t * ∫ ω, X ω ∂μ)) := (log_exp _).symm
      _ ≤ log (∫ ω, exp (t * X ω) ∂μ) := log_le_log (exp_pos _) hexp_bound
  have h3 : ∫ ω, X ω ∂μ ≤ (1/t) * log (∫ ω, exp (t * X ω) ∂μ) := by
    have h2' : (∫ ω, X ω ∂μ) * t ≤ log (∫ ω, exp (t * X ω) ∂μ) := by linarith
    calc ∫ ω, X ω ∂μ = (∫ ω, X ω ∂μ) * t / t := by field_simp
      _ ≤ log (∫ ω, exp (t * X ω) ∂μ) / t := by apply div_le_div_of_nonneg_right h2' (le_of_lt ht)
      _ = (1/t) * log (∫ ω, exp (t * X ω) ∂μ) := by ring
  exact h3


end
