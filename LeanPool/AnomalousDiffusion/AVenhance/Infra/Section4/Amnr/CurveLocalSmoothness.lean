/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowGradientSpatialRates
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Smooth substitution on compact trajectories from local primitive smoothness. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set Filter
open scoped Topology
namespace AVenhance.Infra.Section4

/-- On a compact time domain, finite-dimensional state substitution is smooth
for every smooth joint field. Localization proves the needed uniform Taylor
bounds; no global primitive derivative hypothesis is required. -/
theorem amnrCurveJointCompose_contDiff_infty_local {K E F : Type}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (η : C(K, ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞) (amnrCurveJointCompose f hf.continuous η) := by
  apply contDiff_iff_contDiffAt.mpr
  intro u
  let R := ‖η‖ + ‖u‖ + 2
  have hR : 0 < R := by dsimp [R]; positivity
  let χ : ContDiffBump (0 : ℝ × E) := ⟨R, R + 1, hR, by linarith⟩
  let g := fun z : ℝ × E => χ z • f z
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := χ.contDiff.smul hf
  have hsupport : HasCompactSupport g := χ.hasCompactSupport.smul_right
  have hbound : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖iteratedFDeriv ℝ j g z‖ ≤ C := by
    intro j
    obtain ⟨C, hC, hCb⟩ := hsupport.exists_bound_iteratedFDeriv hg j
    exact ⟨C, hC, hCb j le_rfl⟩
  have hnear : amnrCurveJointCompose f hf.continuous η =ᶠ[𝓝 u]
      amnrCurveJointCompose g hg.continuous η := by
    filter_upwards [Metric.ball_mem_nhds u (by norm_num : (0 : ℝ) < 1)] with v hv
    apply ContinuousMap.ext
    intro t
    have hvu : ‖v - u‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hv
    have hvnorm : ‖v‖ ≤ ‖u‖ + ‖v - u‖ := by
      have hh := norm_add_le u (v - u)
      rw [add_sub_cancel] at hh
      exact hh
    have hpair : ‖(η t, v t)‖ ≤ R := by
      rw [Prod.norm_def, max_le_iff]
      constructor
      · exact (η.norm_coe_le_norm t).trans (by dsimp [R]; linarith [norm_nonneg u])
      · exact (v.norm_coe_le_norm t).trans (by dsimp [R]; linarith [norm_nonneg η])
    have hχ : χ (η t, v t) = 1 := χ.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hpair)
    change f (η t, v t) = χ (η t, v t) • f (η t, v t)
    rw [hχ, one_smul]
  exact ((amnrCurveJointCompose_contDiff_infty hg hbound η).contDiffAt (x :=
      u)).congr_of_eventuallyEq hnear

/-- Evaluation determines the actual derivative operator of substitution
from local smoothness alone. -/
theorem amnrCurveJointCompose_fderiv_eval_local {K E F : Type}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (η : C(K, ℝ))
    (u v : C(K, E)) (t : K) :
    (fderiv ℝ (amnrCurveJointCompose f hf.continuous η) u v) t =
      (amnrStateDerivative f (η t, u t)) (v t) := by
  let N := amnrCurveJointCompose f hf.continuous η
  let P := ContinuousMap.evalCLM ℝ (M := F) t
  let S := ContinuousMap.evalCLM ℝ (M := E) t
  have hN := amnrCurveJointCompose_contDiff_infty_local hf η
  have hs : HasFDerivAt (fun x : E => f (η t, x)) (amnrStateDerivative f (η t, u t)) (u t) := by
    exact (hf.differentiable (by simp) (η t, u t)).hasFDerivAt.comp (u t)
      (hasFDerivAt_prodMk_right (η t) (u t))
  have h₁ := P.hasFDerivAt.comp u (hN.differentiable (by simp) u).hasFDerivAt
  have h₂ := hs.comp u S.hasFDerivAt
  have he : P ∘ N = (fun x => f (η t, x)) ∘ S := rfl
  rw [he] at h₁
  have hd := h₁.unique h₂
  exact congrArg (fun L => L v) hd

end AVenhance.Infra.Section4
