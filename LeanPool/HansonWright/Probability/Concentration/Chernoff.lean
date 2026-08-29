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
# Chernoff Bounds

Exponential-moment tail bounds, including the optimized sub-Gaussian tail estimate.

## Main definitions

This module introduces no new definitions.

## Main results

* `chernoff_bound_cgf`: a tail bound expressed through the cumulant generating function.
* `chernoff_bound_subGaussian`: the optimized sub-Gaussian specialization.
-/

open MeasureTheory Set Real Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Chernoff bound via cgf: For any t ≥ 0, P(X ≥ ε) ≤ exp(cgf(t) - t·ε). -/
theorem chernoff_bound_cgf {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} {ε t : ℝ} (ht : 0 ≤ t)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    (μ {ω | ε ≤ X ω}).toReal ≤ exp (-t * ε + ProbabilityTheory.cgf X μ t) :=
  ProbabilityTheory.measure_ge_le_exp_cgf ε ht h_int

/-- Chernoff bound optimized for sub-Gaussian random variables.
    If cgf(X, t) ≤ t²σ²/2, then P(X ≥ u) ≤ exp(-u²/(2σ²)). -/
theorem chernoff_bound_subGaussian {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ u : ℝ} (hσ : 0 < σ) (hu : 0 < u)
    (h_sgb : ∀ t : ℝ, ProbabilityTheory.cgf X μ t ≤ t^2 * σ^2 / 2)
    (h_int : ∀ t : ℝ, Integrable (fun ω => exp (t * X ω)) μ) :
    (μ {ω | u ≤ X ω}).toReal ≤ exp (-u^2 / (2 * σ^2)) := by
  -- Choose optimal t = u/σ²
  set t_opt := u / σ^2 with ht_def
  have ht_pos : 0 < t_opt := div_pos hu (sq_pos_of_pos hσ)
  have ht_nonneg : 0 ≤ t_opt := le_of_lt ht_pos
  -- Apply Chernoff bound
  have h1 : (μ {ω | u ≤ X ω}).toReal ≤ exp (-t_opt * u + ProbabilityTheory.cgf X μ t_opt) :=
    chernoff_bound_cgf ht_nonneg (h_int t_opt)
  have h2 : ProbabilityTheory.cgf X μ t_opt ≤ t_opt^2 * σ^2 / 2 := h_sgb t_opt
  have h3 : -t_opt * u + t_opt^2 * σ^2 / 2 = -u^2 / (2 * σ^2) := by
    rw [ht_def]
    field_simp
    ring
  calc (μ {ω | u ≤ X ω}).toReal
    _ ≤ exp (-t_opt * u + ProbabilityTheory.cgf X μ t_opt) := h1
    _ ≤ exp (-t_opt * u + t_opt^2 * σ^2 / 2) := exp_le_exp.mpr (by linarith)
    _ = exp (-u^2 / (2 * σ^2)) := congrArg exp h3


end
