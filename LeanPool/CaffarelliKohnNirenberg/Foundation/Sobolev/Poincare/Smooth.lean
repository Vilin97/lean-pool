/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.Geometry
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Smooth segment estimates

Adapted from CoarseGraining (LeanIntoHomogenization, 2026) with the author's
permission.  These are the smooth one-dimensional estimates used by the
unit-ball Poincare proof.
-/

public section

namespace CKN

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
    (hu : ContDiff ℝ 1 u) (x y : Vec d) :
    u x - u y = ∫ t in (0 : ℝ)..1,
      (fderiv ℝ u (segmentBlend x t y)) (x - y) := by
  let γ : ℝ → Vec d := fun t => segmentBlend x t y
  have hγ : ∀ t : ℝ, HasDerivAt γ (x - y) t := by
    intro t
    simpa [γ] using hasDerivAt_segmentBlend x y t
  have huγ :
      ∀ t : ℝ, HasDerivAt (u ∘ γ)
        ((fderiv ℝ u (γ t)) (x - y)) t := by
    intro t
    exact
      ((hu.differentiable (by norm_num)).differentiableAt).hasFDerivAt.comp_hasDerivAt t
        (hγ t)
  have hγ_cont : Continuous γ :=
    continuous_iff_continuousAt.2 fun t => (hγ t).continuousAt
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hint :
      IntervalIntegrable (fun t => (fderiv ℝ u (γ t)) (x - y))
        MeasureTheory.volume 0 1 := by
    have hcont : Continuous (fun t => (fderiv ℝ u (γ t)) (x - y)) :=
      (hfderiv_cont.comp hγ_cont).clm_apply continuous_const
    exact hcont.intervalIntegrable _ _
  have hftc :
      ∫ t in (0 : ℝ)..1, (fderiv ℝ u (γ t)) (x - y) = u x - u y := by
    simpa [Function.comp, γ] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => huγ t) hint
  exact hftc.symm

theorem norm_sub_le_integral_fderiv_along_segment {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ 1 u) (x y : Vec d) :
    ‖u x - u y‖ ≤
      ∫ t in (0 : ℝ)..1,
        ‖(fderiv ℝ u (segmentBlend x t y)) (x - y)‖ := by
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
      IntervalIntegrable (fun t => (fderiv ℝ u (γ t)) (x - y))
        MeasureTheory.volume 0 1 := by
    have hcont : Continuous (fun t => (fderiv ℝ u (γ t)) (x - y)) :=
      (hfderiv_cont.comp hγ_cont).clm_apply continuous_const
    exact hcont.intervalIntegrable _ _
  have hint_norm :
      IntervalIntegrable (fun t => ‖(fderiv ℝ u (γ t)) (x - y)‖)
        MeasureTheory.volume 0 1 := by
    have hcont : Continuous (fun t => ‖(fderiv ℝ u (γ t)) (x - y)‖) :=
      continuous_norm.comp ((hfderiv_cont.comp hγ_cont).clm_apply continuous_const)
    exact hcont.intervalIntegrable _ _
  calc
    ‖u x - u y‖ =
        ‖∫ t in (0 : ℝ)..1, (fderiv ℝ u (segmentBlend x t y)) (x - y)‖ := by
          rw [sub_eq_integral_fderiv_along_segment hu x y]
    _ ≤ ∫ t in (0 : ℝ)..1,
        ‖(fderiv ℝ u (segmentBlend x t y)) (x - y)‖ := by
          exact intervalIntegral.norm_integral_le_integral_norm zero_le_one

theorem norm_sub_le_integral_norm_fderiv_mul_norm_sub_along_segment
    {d : ℕ} {u : Vec d → ℝ} (hu : ContDiff ℝ 1 u) (x y : Vec d) :
    ‖u x - u y‖ ≤
      ∫ t in (0 : ℝ)..1,
        ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ := by
  let γ : ℝ → Vec d := fun t => segmentBlend x t y
  have hγ_cont : Continuous γ := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    exact (hasDerivAt_segmentBlend x y t).continuousAt
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hint_eval :
      IntervalIntegrable (fun t => ‖(fderiv ℝ u (γ t)) (x - y)‖)
        MeasureTheory.volume 0 1 := by
    have hcont : Continuous (fun t => ‖(fderiv ℝ u (γ t)) (x - y)‖) :=
      continuous_norm.comp ((hfderiv_cont.comp hγ_cont).clm_apply continuous_const)
    exact hcont.intervalIntegrable _ _
  have hint_op :
      IntervalIntegrable (fun t => ‖fderiv ℝ u (γ t)‖ * ‖x - y‖)
        MeasureTheory.volume 0 1 := by
    have hcont : Continuous (fun t => ‖fderiv ℝ u (γ t)‖ * ‖x - y‖) :=
      (continuous_norm.comp (hfderiv_cont.comp hγ_cont)).mul continuous_const
    exact hcont.intervalIntegrable _ _
  calc
    ‖u x - u y‖ ≤
        ∫ t in (0 : ℝ)..1, ‖(fderiv ℝ u (segmentBlend x t y)) (x - y)‖ :=
      norm_sub_le_integral_fderiv_along_segment hu x y
    _ ≤ ∫ t in (0 : ℝ)..1,
        ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ := by
          refine intervalIntegral.integral_mono_on zero_le_one hint_eval hint_op ?_
          intro t ht
          exact ContinuousLinearMap.le_opNorm _ _

end CKN
