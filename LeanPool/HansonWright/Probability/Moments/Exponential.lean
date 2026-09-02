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
* `integrable_exp_add_and_integral_le`: combines exponential-moment bounds for two
  summands without requiring independence.
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

/-- Convexity bounds the exponential of a sum by the average of doubled exponentials. -/
lemma exp_add_le_average_exp_two (a b : ℝ) :
    exp (a + b) ≤ (exp (2 * a) + exp (2 * b)) / 2 := by
  have hconv := convexOn_exp.2 (Set.mem_univ (2 * a)) (Set.mem_univ (2 * b))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  calc
    exp (a + b) = exp ((1 / 2 : ℝ) • (2 * a) + (1 / 2 : ℝ) • (2 * b)) := by
      congr 1
      norm_num
      ring
    _ ≤ (1 / 2 : ℝ) * exp (2 * a) + (1 / 2 : ℝ) * exp (2 * b) := hconv
    _ = (exp (2 * a) + exp (2 * b)) / 2 := by ring

/-- Combine equal exponential-moment bounds for two summands.

This is the integral form of `exp_add_le_average_exp_two`: integrability and an
upper bound at the doubled parameter for each summand give the same upper bound
for their sum at the original parameter. No independence assumption is needed. -/
lemma integrable_exp_add_and_integral_le {μ : Measure Ω} {Y Z : Ω → ℝ} {l B : ℝ}
    (hY_ae : AEMeasurable Y μ) (hZ_ae : AEMeasurable Z μ)
    (hY_int : Integrable (fun ω => exp ((2 * l) * Y ω)) μ)
    (hZ_int : Integrable (fun ω => exp ((2 * l) * Z ω)) μ)
    (hY_le : ∫ ω, exp ((2 * l) * Y ω) ∂μ ≤ B)
    (hZ_le : ∫ ω, exp ((2 * l) * Z ω) ∂μ ≤ B) :
    Integrable (fun ω => exp (l * (Y ω + Z ω))) μ ∧
      ∫ ω, exp (l * (Y ω + Z ω)) ∂μ ≤ B := by
  let majorant : Ω → ℝ :=
    fun ω => (exp ((2 * l) * Y ω) + exp ((2 * l) * Z ω)) / 2
  have hmajorant_int : Integrable majorant μ := by
    dsimp [majorant]
    exact (hY_int.add hZ_int).div_const 2
  have hsum_aesm :
      AEStronglyMeasurable (fun ω => exp (l * (Y ω + Z ω))) μ :=
    (((hY_ae.add hZ_ae).const_mul l).exp).aestronglyMeasurable
  have hpoint :
      (fun ω => exp (l * (Y ω + Z ω))) ≤ᵐ[μ] majorant := by
    filter_upwards with ω
    dsimp [majorant]
    convert exp_add_le_average_exp_two (l * Y ω) (l * Z ω) using 1 <;> ring_nf
  have hsum_int : Integrable (fun ω => exp (l * (Y ω + Z ω))) μ := by
    refine Integrable.mono' hmajorant_int hsum_aesm ?_
    filter_upwards [hpoint] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
    exact hω
  have hmajorant_integral :
      ∫ ω, majorant ω ∂μ =
        (∫ ω, exp ((2 * l) * Y ω) ∂μ +
          ∫ ω, exp ((2 * l) * Z ω) ∂μ) / 2 := by
    dsimp [majorant]
    rw [integral_div, integral_add hY_int hZ_int]
  refine ⟨hsum_int, (integral_mono_ae hsum_int hmajorant_int hpoint).trans ?_⟩
  rw [hmajorant_integral]
  calc
    (∫ ω, exp ((2 * l) * Y ω) ∂μ +
        ∫ ω, exp ((2 * l) * Z ω) ∂μ) / 2
        ≤ (B + B) / 2 :=
      div_le_div_of_nonneg_right (add_le_add hY_le hZ_le) (by norm_num)
    _ = B := by ring


end

end LeanPool
