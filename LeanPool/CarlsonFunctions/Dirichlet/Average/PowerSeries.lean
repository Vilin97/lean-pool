/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Basic

import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Averages of uniformly summable series

This file supplies the dominated-convergence form of Carlson's Representation 5.7-2.  A
summable numerical majorant, uniform on the standard simplex, permits termwise application of
the regularized Carlson Dirichlet average.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Section 5.7,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical

@[expose] public noncomputable section CarlsonPowerSeries

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- A uniformly summably dominated series may be averaged term by term with respect to the
regularized Dirichlet density.  This is the general analytic core of Carlson's
Representation 5.7-2. -/
theorem hasSum_regCarlsonDirichletAverage
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (z : ι → ℂ)
    (g : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (M : ℕ → ℝ)
    (hg : ∀ n, ContinuousOn (fun u : ι → ℝ ↦ g n (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι))
    (hM : Summable M)
    (hbound : ∀ n u, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι → ‖g n (carlsonAffineForm z u)‖ ≤ M n)
    (hsum : ∀ u, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι →
      HasSum (fun n ↦ g n (carlsonAffineForm z u)) (f (carlsonAffineForm z u))) :
    HasSum (fun n ↦ regCarlsonDirichletAverage b z (g n))
      (regCarlsonDirichletAverage b z f) := by
  let μ := (MeasureTheory.Measure.stdSimplexMeasure (ι := ι)).restrict (Convexity.StdSimplex.coordinateSet ℝ ι)
  let F : ℕ → (ι → ℝ) → ℂ := fun n u ↦
    regDirichletDensity b u * g n (carlsonAffineForm z u)
  let G : (ι → ℝ) → ℂ := fun u ↦
    regDirichletDensity b u * f (carlsonAffineForm z u)
  let B : ℕ → (ι → ℝ) → ℝ := fun n u ↦ M n * ‖regDirichletDensity b u‖
  have hdens : Integrable (fun u ↦ regDirichletDensity b u) μ := by
    change IntegrableOn (fun u ↦ regDirichletDensity b u)
      (Convexity.StdSimplex.coordinateSet ℝ ι) MeasureTheory.Measure.stdSimplexMeasure
    simpa only [mul_one] using integrableOn_regDirichletDensity_mul b hb
      (continuousOn_const : ContinuousOn (fun _ : ι → ℝ ↦ (1 : ℂ))
        (Convexity.StdSimplex.coordinateSet ℝ ι))
  have hF_meas (n : ℕ) : AEStronglyMeasurable (F n) μ := by
    exact (integrableOn_regDirichletDensity_mul b hb (hg n)).1
  have hB (n : ℕ) : ∀ᵐ u ∂μ, ‖F n u‖ ≤ B n u := by
    filter_upwards [self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    simp only [F, B, norm_mul]
    rw [mul_comm (M n)]
    exact mul_le_mul_of_nonneg_left (hbound n u hu) (norm_nonneg _)
  have hB_summable : ∀ᵐ u ∂μ, Summable fun n ↦ B n u := by
    filter_upwards with u
    exact hM.mul_right _
  have hB_integrable : Integrable (fun u ↦ ∑' n, B n u) μ := by
    have heq : (fun u ↦ ∑' n, B n u) =
        fun u ↦ (∑' n, M n) * ‖regDirichletDensity b u‖ := by
      funext u
      simp only [B]
      rw [tsum_mul_right]
    rw [heq]
    exact hdens.norm.const_mul _
  have hlim : ∀ᵐ u ∂μ, HasSum (fun n ↦ F n u) (G u) := by
    filter_upwards [self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    exact (hsum u hu).mul_left (regDirichletDensity b u)
  simpa [F, G, μ, regCarlsonDirichletAverage, regDirichletIntegral] using
    hasSum_integral_of_dominated_convergence B hF_meas hB hB_summable hB_integrable hlim

end DirichletTransform

end CarlsonPowerSeries
