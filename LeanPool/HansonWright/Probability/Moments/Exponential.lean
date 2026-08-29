/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponential-Moment Bounds

Jensen and logarithmic moment-generating-function bounds for real random variables.

## Main definitions

This module introduces no new definitions.

## Main results

* `jensen_exp`: Jensen's inequality for the exponential function.
* `mean_le_log_mgf`: an expectation bound through a positive exponential moment.
-/

namespace LeanPool

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
  have htX_int : Integrable (fun ω => t * X ω) μ := hX_int.const_mul t
  have h := jensen_exp htX_int hexpX_int
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

/-- Integrability of all real exponential moments implies integrability of the variable. -/
lemma integrable_of_integrable_exp_all {Y : Ω → ℝ} {μ : Measure Ω}
    (h : ∀ t : ℝ, Integrable (fun ω => exp (t * Y ω)) μ) :
    Integrable Y μ := by
  have h_set_eq : ProbabilityTheory.integrableExpSet Y μ = Set.univ := by
    ext t
    simp only [ProbabilityTheory.integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact h t
  have h_interior : (0 : ℝ) ∈ interior (ProbabilityTheory.integrableExpSet Y μ) := by
    rw [h_set_eq, interior_univ]
    exact Set.mem_univ _
  exact ProbabilityTheory.integrable_of_mem_interior_integrableExpSet h_interior


end

end LeanPool
