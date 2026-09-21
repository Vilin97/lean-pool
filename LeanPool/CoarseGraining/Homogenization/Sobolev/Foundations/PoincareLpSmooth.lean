/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareSegment
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Poincare Lp Smooth -/

namespace Homogenization

/-!
# Smooth segment estimates for convex-domain Poincare

This file begins the genuinely analytic side of the convex-domain Poincare
proof. The first step is the fundamental theorem of calculus along the affine
segment joining `y` to `x`, expressed with the project-local map
`segmentBlend x t y = y + t • (x - y)`.

Unlike the ball proof in the De Giorgi development, these lemmas are not tied
to any radial parametrization. They are the smooth, domain-agnostic segment
estimates that the later convex-domain `L^p` argument will integrate in `y` and
then in `x`.
-/

private theorem hasDerivAt_segmentBlend {d : ℕ} (x y : Vec d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => segmentBlend x s y) (x - y) t := by
  have hsmul : HasDerivAt (fun s : ℝ => s • (x - y)) (x - y) t := by
    simpa using (hasDerivAt_id t).smul_const (x - y)
  have hadd : HasDerivAt (fun s : ℝ => y + s • (x - y)) (x - y) t :=
    hsmul.const_add y
  convert hadd using 1
  funext s
  exact segmentBlend_eq_add_smul_sub x y s

theorem sub_eq_integral_fderiv_along_segment {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x y : Vec d) :
    u x - u y = ∫ t in (0 : ℝ)..1, (fderiv ℝ u (segmentBlend x t y)) (x - y) := by
  let γ : ℝ → Vec d := fun t => segmentBlend x t y
  have hγ : ∀ t : ℝ, HasDerivAt γ (x - y) t := by
    intro t
    simpa [γ] using hasDerivAt_segmentBlend x y t
  have huγ :
      ∀ t : ℝ, HasDerivAt (u ∘ γ) ((fderiv ℝ u (γ t)) (x - y)) t := by
    intro t
    exact ((hu.differentiable (by norm_num)).differentiableAt).hasFDerivAt.comp_hasDerivAt t
      (hγ t)
  have hγ_cont : Continuous γ :=
    continuous_iff_continuousAt.2 fun t => (hγ t).continuousAt
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hint :
      IntervalIntegrable (fun t => (fderiv ℝ u (γ t)) (x - y)) MeasureTheory.volume 0 1 := by
    have hcont : Continuous (fun t => (fderiv ℝ u (γ t)) (x - y)) :=
      (hfderiv_cont.comp hγ_cont).clm_apply continuous_const
    exact hcont.intervalIntegrable _ _
  have hftc :
      ∫ t in (0 : ℝ)..1, (fderiv ℝ u (γ t)) (x - y) = u x - u y := by
    simpa [Function.comp, γ] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => huγ t) hint)
  exact hftc.symm

theorem norm_sub_le_integral_fderiv_along_segment {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x y : Vec d) :
    ‖u x - u y‖ ≤
      ∫ t in (0 : ℝ)..1, ‖(fderiv ℝ u (segmentBlend x t y)) (x - y)‖ := by
  let γ : ℝ → Vec d := fun t => segmentBlend x t y
  have hγ : ∀ t : ℝ, HasDerivAt γ (x - y) t := by
    intro t
    simpa [γ] using hasDerivAt_segmentBlend x y t
  have hγ_cont : Continuous γ :=
    continuous_iff_continuousAt.2 fun t => (hγ t).continuousAt
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hint :
      IntervalIntegrable (fun t => (fderiv ℝ u (γ t)) (x - y)) MeasureTheory.volume 0 1 := by
    have hcont : Continuous (fun t => (fderiv ℝ u (γ t)) (x - y)) :=
      (hfderiv_cont.comp hγ_cont).clm_apply continuous_const
    exact hcont.intervalIntegrable _ _
  have hint_norm :
      IntervalIntegrable (fun t => ‖(fderiv ℝ u (γ t)) (x - y)‖) MeasureTheory.volume 0 1 := by
    have hcont : Continuous (fun t => ‖(fderiv ℝ u (γ t)) (x - y)‖) :=
      continuous_norm.comp ((hfderiv_cont.comp hγ_cont).clm_apply continuous_const)
    exact hcont.intervalIntegrable _ _
  calc
    ‖u x - u y‖ =
        ‖∫ t in (0 : ℝ)..1, (fderiv ℝ u (segmentBlend x t y)) (x - y)‖ := by
          rw [sub_eq_integral_fderiv_along_segment hu x y]
    _ ≤ ∫ t in (0 : ℝ)..1, ‖(fderiv ℝ u (segmentBlend x t y)) (x - y)‖ := by
          exact intervalIntegral.norm_integral_le_integral_norm zero_le_one

theorem norm_sub_le_integral_norm_fderiv_mul_norm_sub_along_segment
    {d : ℕ} {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x y : Vec d) :
    ‖u x - u y‖ ≤
      ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ := by
  let γ : ℝ → Vec d := fun t => segmentBlend x t y
  have hγ : Continuous γ := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    have hderiv : HasDerivAt γ (x - y) t := by
      simpa [γ] using hasDerivAt_segmentBlend x y t
    exact hderiv.continuousAt
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hint_eval :
      IntervalIntegrable (fun t => ‖(fderiv ℝ u (γ t)) (x - y)‖) MeasureTheory.volume 0 1 := by
    have hcont : Continuous (fun t => ‖(fderiv ℝ u (γ t)) (x - y)‖) :=
      continuous_norm.comp ((hfderiv_cont.comp hγ).clm_apply continuous_const)
    exact hcont.intervalIntegrable _ _
  have hint_op :
      IntervalIntegrable (fun t => ‖fderiv ℝ u (γ t)‖ * ‖x - y‖)
        MeasureTheory.volume 0 1 := by
    have hcont : Continuous (fun t => ‖fderiv ℝ u (γ t)‖ * ‖x - y‖) :=
      (continuous_norm.comp (hfderiv_cont.comp hγ)).mul continuous_const
    exact hcont.intervalIntegrable _ _
  calc
    ‖u x - u y‖ ≤
        ∫ t in (0 : ℝ)..1, ‖(fderiv ℝ u (segmentBlend x t y)) (x - y)‖ :=
      norm_sub_le_integral_fderiv_along_segment hu x y
    _ ≤ ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ := by
          refine intervalIntegral.integral_mono_on zero_le_one hint_eval hint_op ?_
          intro t ht
          exact ContinuousLinearMap.le_opNorm _ _

theorem integral_norm_fderiv_mul_norm_sub_along_segment_le_two_mul_choose_mul_integral_norm_fderiv_along_segment
    {d : ℕ} {U : Set (Vec d)} (hU : IsBoundedDomain U)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) {x y : Vec d}
    (hx : x ∈ U) (hy : y ∈ U) :
    ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ≤
      (2 * Classical.choose hU) *
        ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (segmentBlend x t y)‖ := by
  let g : ℝ → ℝ := fun t => ‖fderiv ℝ u (segmentBlend x t y)‖
  have hg_cont : Continuous g := by
    have hfderiv_cont : Continuous (fderiv ℝ u) := by
      have h1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
      exact h1.continuous_fderiv (by norm_num)
    have hsegment_cont : Continuous (fun t : ℝ => segmentBlend x t y) := by
      refine continuous_iff_continuousAt.2 ?_
      intro t
      exact (hasDerivAt_segmentBlend x y t).continuousAt
    exact continuous_norm.comp (hfderiv_cont.comp hsegment_cont)
  have hg_int : IntervalIntegrable g MeasureTheory.volume 0 1 := by
    exact hg_cont.intervalIntegrable _ _
  have hg_mul_int :
      IntervalIntegrable (fun t => g t * ‖x - y‖) MeasureTheory.volume 0 1 :=
    hg_int.mul_const _
  have hg_bound_int :
      IntervalIntegrable (fun t => g t * (2 * Classical.choose hU))
        MeasureTheory.volume 0 1 :=
    hg_int.mul_const _
  have hdist_bound : ‖x - y‖ ≤ 2 * Classical.choose hU :=
    hU.norm_sub_le_two_mul_choose hx hy
  calc
    ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖
        = ∫ t in (0 : ℝ)..1, g t * ‖x - y‖ := by
            rfl
    _ ≤ ∫ t in (0 : ℝ)..1, g t * (2 * Classical.choose hU) := by
          refine intervalIntegral.integral_mono_on zero_le_one hg_mul_int hg_bound_int ?_
          intro t ht
          exact mul_le_mul_of_nonneg_left hdist_bound (by positivity)
    _ = (2 * Classical.choose hU) * ∫ t in (0 : ℝ)..1, g t := by
          rw [intervalIntegral.integral_mul_const]
          ring
    _ = (2 * Classical.choose hU) *
          ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (segmentBlend x t y)‖ := by
            rfl

end Homogenization
