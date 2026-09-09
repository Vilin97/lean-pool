/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryOperator
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SpatialCutoffs
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-! The actual source outer cutoff in rescaled particle labels. -/

@[expose] public section


noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerGevrey
open scoped ContDiff

/-- Scaled cutoff, bundling `field`, `smooth`, `compact`. -/
def scaledCutoff (ℓ : ℝ) (hℓ : 0 < ℓ) : Cutoff where
  field := fun x => EulerSpatialCutoffs.outerCutoff (ℓ • x)
  smooth := EulerSpatialCutoffs.outerCutoff_contDiff.comp (contDiff_id.const_smul ℓ)
  compact := EulerSpatialCutoffs.outerCutoff_compactSupport.comp_smul hℓ.ne'

theorem scaledCutoff_one (ℓ : ℝ) (hℓ : 0 < ℓ) (x : Space) (hx : ‖ℓ • x‖ ≤ 1) :
    (scaledCutoff ℓ hℓ).field x = 1 := EulerSpatialCutoffs.outerCutoff_one _ hx

theorem scaledCutoff_one_on_ball (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∀ x ∈ Metric.ball (0 : Space) ℓ⁻¹, (scaledCutoff ℓ hℓ).field x = 1 := by
  intro x hx
  apply scaledCutoff_one ℓ hℓ
  simp only [Metric.mem_ball, dist_zero_right] at hx
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
  have H := mul_le_mul_of_nonneg_left hx.le hℓ.le
  rwa [mul_inv_cancel₀ hℓ.ne'] at H

theorem scaledCutoff_support (ℓ : ℝ) (hℓ : 0 < ℓ) :
    tsupport (scaledCutoff ℓ hℓ).field ⊆ {x : Space | ‖ℓ • x‖ ≤ 2} := by
  intro x hx
  have H : ℓ • x ∈ tsupport EulerSpatialCutoffs.outerCutoff :=
    tsupport_comp_subset_preimage EulerSpatialCutoffs.outerCutoff (continuous_const_smul ℓ) hx
  change ‖ℓ • x‖ ≤ 2
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    EulerSpatialCutoffs.outerCutoff_support H

theorem scaledCutoff_even (ℓ : ℝ) (hℓ : 0 < ℓ) (x : Space) :
    (scaledCutoff ℓ hℓ).field (-x) = (scaledCutoff ℓ hℓ).field x := by
  change EulerSpatialCutoffs.outerCutoff (ℓ • (-x)) = _
  rw [smul_neg, EulerSpatialCutoffs.outerCutoff_even]
  rfl

theorem physical_ball_eq (ℓ r : ℝ) (hℓ : 0 < ℓ) :
    {x : Space | ‖ℓ • x‖ < r} = Metric.ball (0 : Space) (ℓ⁻¹*r) := by
  ext x
  simp only [Set.mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ,
    Metric.mem_ball, dist_zero_right]
  constructor
  · intro h
    have H := mul_lt_mul_of_pos_left h (inv_pos.mpr hℓ)
    simpa only [← mul_assoc, inv_mul_cancel₀ hℓ.ne', one_mul] using H
  · intro h
    have H := mul_lt_mul_of_pos_left h hℓ
    simpa only [← mul_assoc, mul_inv_cancel₀ hℓ.ne', one_mul] using H

/-- Rescaling by at most one preserves the fixed factorial derivative bound. -/
theorem scaledCutoff_gevrey (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (scaledCutoff ℓ hℓ).field x‖ ≤
      (9 * (1 + 3 / EulerGevreyCutoff.bumpMass)^2)^3 * majorant 256 0 n := by
  change ‖iteratedFDeriv ℝ n (fun y => EulerSpatialCutoffs.outerCutoff (ℓ • y)) x‖ ≤ _
  rw [iteratedFDeriv_comp_const_smul ℓ
    (EulerSpatialCutoffs.outerCutoff_contDiff.of_le (by simp)), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hℓ.le n)]
  have hpow : ℓ^n ≤ 1 := pow_le_one₀ hℓ.le hℓ1
  calc
    _ ≤ 1 * ‖iteratedFDeriv ℝ n EulerSpatialCutoffs.outerCutoff (ℓ • x)‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using EulerSpatialCutoffs.outerCutoff_gevrey n (ℓ • x)

end EulerMeanBoundary
