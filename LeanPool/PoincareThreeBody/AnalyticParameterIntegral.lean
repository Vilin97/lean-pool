/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrating a uniformly controlled analytic power series

This file provides the power-series core of analyticity under a parameter integral.  The
compactness argument used later supplies a common radius and the summable integral bound on the
coefficients.
-/

namespace LeanPool.PoincareThreeBody

open Filter MeasureTheory Topology

variable {α : Type*} [MeasurableSpace α]

/-- Integrate every coefficient of a measurable family of scalar formal power series. -/
noncomputable def integralFormalMultilinearSeries
    (μ : Measure α) (series : α → FormalMultilinearSeries ℝ ℝ ℝ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  fun degree ↦ ∫ parameter, series parameter degree ∂μ

/-- A parameter integral has the coefficientwise-integrated power series whenever all fibers
share a positive radius and the integrated coefficient norms are summable at that radius. -/
theorem hasFPowerSeriesOnBall_integral_of_uniform
    (μ : Measure α) {integrand : ℝ → α → ℝ} {center : ℝ} {radius : NNReal}
    {series : α → FormalMultilinearSeries ℝ ℝ ℝ}
    (hradius : 0 < radius)
    (hseries : ∀ parameter,
      HasFPowerSeriesOnBall (fun value ↦ integrand value parameter)
        (series parameter) center radius)
    (hcoeffIntegrable : ∀ degree, Integrable (fun parameter ↦ series parameter degree) μ)
    (hcoeffSummable : Summable (fun degree ↦
      (∫ parameter, ‖series parameter degree‖ ∂μ) * (radius : ℝ) ^ degree)) :
    HasFPowerSeriesOnBall (fun value ↦ ∫ parameter, integrand value parameter ∂μ)
      (integralFormalMultilinearSeries μ series) center radius := by
  refine ⟨?_, by exact_mod_cast hradius, ?_⟩
  · apply FormalMultilinearSeries.le_radius_of_summable_norm
    apply hcoeffSummable.of_nonneg_of_le
    · intro degree
      positivity
    · intro degree
      exact mul_le_mul_of_nonneg_right
        (norm_integral_le_integral_norm (fun parameter ↦ series parameter degree))
        (pow_nonneg radius.2 degree)
  · intro displacement hdisplacement
    have hnorm : ‖displacement‖ < (radius : ℝ) := by
      simpa [Metric.mem_eball, edist_dist] using hdisplacement
    let term : ℕ → α → ℝ := fun degree parameter ↦
      series parameter degree (fun _ : Fin degree ↦ displacement)
    have htermIntegrable : ∀ degree, Integrable (term degree) μ := by
      intro degree
      let evaluation :
          (ℝ [×degree]→L[ℝ] ℝ) →L[ℝ] ℝ :=
        ContinuousMultilinearMap.apply ℝ (fun _ : Fin degree ↦ ℝ) ℝ
          (fun _ ↦ displacement)
      exact evaluation.integrable_comp (hcoeffIntegrable degree)
    have htermNormSummable : Summable (fun degree ↦
        ∫ parameter, ‖term degree parameter‖ ∂μ) := by
      apply hcoeffSummable.of_nonneg_of_le
      · intro degree
        exact integral_nonneg (fun _ ↦ norm_nonneg _)
      · intro degree
        calc
          (∫ parameter, ‖term degree parameter‖ ∂μ) ≤
              ∫ parameter,
                ‖series parameter degree‖ * ‖displacement‖ ^ degree ∂μ := by
            apply integral_mono (htermIntegrable degree).norm
              ((hcoeffIntegrable degree).norm.mul_const _)
            intro parameter
            apply (series parameter degree).le_opNorm_mul_pow_of_le
            change ‖fun _ : Fin degree ↦ displacement‖ ≤ ‖displacement‖
            exact (pi_norm_le_iff_of_nonneg (norm_nonneg displacement)).2
              (fun _ ↦ le_rfl)
          _ = (∫ parameter, ‖series parameter degree‖ ∂μ) *
                ‖displacement‖ ^ degree := by
            rw [integral_mul_const]
          _ ≤ (∫ parameter, ‖series parameter degree‖ ∂μ) *
                (radius : ℝ) ^ degree := by
            gcongr
    have hintegralSum :=
      hasSum_integral_of_summable_integral_norm htermIntegrable htermNormSummable
    have hcoefficientIntegral : ∀ degree,
        integralFormalMultilinearSeries μ series degree
            (fun _ : Fin degree ↦ displacement) =
          ∫ parameter, term degree parameter ∂μ := by
      intro degree
      unfold integralFormalMultilinearSeries term
      exact ContinuousMultilinearMap.integral_apply
        (hcoeffIntegrable degree) (fun _ : Fin degree ↦ displacement)
    have hpointwiseSum : ∀ parameter,
        ∑' degree, term degree parameter = integrand (center + displacement) parameter := by
      intro parameter
      exact ((hseries parameter).hasSum hdisplacement).tsum_eq
    convert hintegralSum using 1
    · ext degree
      exact hcoefficientIntegral degree
    · exact integral_congr_ae
        (Filter.Eventually.of_forall fun parameter ↦ (hpointwiseSum parameter).symm)

end LeanPool.PoincareThreeBody
