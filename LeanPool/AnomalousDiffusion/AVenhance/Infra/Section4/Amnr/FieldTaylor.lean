/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CurveDifferentiability

/-! Uniform Taylor estimates for Banach-valued primitive fields. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- A primitive second derivative bound gives a uniform quadratic Taylor
remainder in any real normed domain and target. The target may itself be a
higher derivative operator space. -/
theorem amnr_field_quadratic_remainder {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C) (x h : E) :
    ‖f (x + h) - f x - fderiv ℝ f x h‖ ≤ C * ‖h‖ * ‖h‖ := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by simp)).differentiable (by norm_num)
  have hd : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C := by
    intro z
    rw [← norm_iteratedFDeriv_one (fderiv ℝ f), norm_iteratedFDeriv_fderiv]
    exact hbound z
  have hLip (z : E) : ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C * ‖z - x‖ := by
    have hh := convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hdf z) (fun z _ => hd z) (mem_univ x) (mem_univ z)
    exact hh
  let S := Metric.closedBall x ‖h‖
  have hS : Convex ℝ S := convex_closedBall _ _
  have hx : x ∈ S := by simp [S, Metric.mem_closedBall]
  have hy : x + h ∈ S := by simp [S, Metric.mem_closedBall, dist_eq_norm]
  have hderiv : ∀ z ∈ S, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C * ‖h‖ := by
    intro z hz
    have hh : ‖z - x‖ ≤ ‖h‖ := by simpa only [S, Metric.mem_closedBall, dist_eq_norm] using hz
    exact (hLip z).trans (mul_le_mul_of_nonneg_left hh hC)
  have hh := hS.norm_image_sub_le_of_norm_fderiv_le' (f := f) (φ := fderiv ℝ f x)
    (fun z _ => hf.differentiable (by simp) z) hderiv hx hy
  simpa only [add_sub_cancel_left, mul_assoc] using hh

/-- Joint primitive Taylor control restricts to state perturbations at a
fixed time, with no extra norm cost from the time coordinate. -/
theorem amnr_joint_field_state_quadratic_remainder {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ C) (t : ℝ) (x h : E) :
    ‖f (t, x + h) - f (t, x) -
      ((fderiv ℝ f (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) h‖ ≤ C * ‖h‖ * ‖h‖ := by
  have hh := amnr_field_quadratic_remainder hf hC hbound (t, x) (0, h)
  simpa only [Prod.mk_add_mk, add_zero, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg h)] using hh

end AVenhance.Infra.Section4
