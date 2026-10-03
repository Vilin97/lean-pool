/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenFlowRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms
public import Mathlib.Analysis.Matrix.Normed

/-! Spatial regularity of the pulled flow-gradient matrices in the
Section 4 definitions. -/

@[expose] public section

open Homogenization
open scoped ContDiff Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem FlowGradientRegularity.gradMatrix_contDiff_one_of_contDiff_two
    {X : Vec 2 → Vec 2} (hX : ContDiff ℝ 2 X) :
    ContDiff ℝ 1 (fun x => gradMatrix X x) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ X) := hX.fderiv_right (by norm_num)
  apply contDiff_pi.2
  intro i
  apply contDiff_pi.2
  intro j
  have hi : ContDiff ℝ 1
      (fun x => fderiv ℝ X x (basisVec i)) := hD.clm_apply contDiff_const
  have hij := contDiff_pi.1 hi j
  have heq : (fun x => gradMatrix X x i j) =
      fun x => fderiv ℝ X x (basisVec i) j := by
    funext x
    rw [gradMatrix, Matrix.of_apply]
    change fderiv ℝ (fun y => X y j) x (basisVec i) = _
    have hdiff : DifferentiableAt ℝ X x := hX.differentiable (by norm_num) x
    rw [fderiv_apply hdiff j]
    simp
  rw [heq]
  exact hij

theorem FlowGradientRegularity.gradMatrix_contDiff_two_of_contDiff_three
    {X : Vec 2 → Vec 2} (hX : ContDiff ℝ 3 X) :
    ContDiff ℝ 2 (fun x => gradMatrix X x) := by
  have hD : ContDiff ℝ 2 (fderiv ℝ X) := hX.fderiv_right (by norm_num)
  apply contDiff_pi.2
  intro i
  apply contDiff_pi.2
  intro j
  have hi : ContDiff ℝ 2
      (fun x => fderiv ℝ X x (basisVec i)) := hD.clm_apply contDiff_const
  have hij := contDiff_pi.1 hi j
  have heq : (fun x => gradMatrix X x i j) =
      fun x => fderiv ℝ X x (basisVec i) j := by
    funext x
    rw [gradMatrix, Matrix.of_apply]
    change fderiv ℝ (fun y => X y j) x (basisVec i) = _
    have hdiff : DifferentiableAt ℝ X x := hX.differentiable (by norm_num) x
    rw [fderiv_apply hdiff j]
    simp
  rw [heq]
  exact hij

/-- The pulled gradient matrix `∇X_l ∘ X_l⁻¹` is C¹ in the spatial
variable, by the C² spatial regularity of both flow slices. -/
theorem flowGrad_spatial_contDiff_one
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    ContDiff ℝ 1 (fun x => I.flowGrad hΦ m l t x) := by
  have hX : ContDiff ℝ 2 (I.xFlow hΦ m l t) :=
    xFlow_spatial_contDiff_two I hΦ m l t
  have hgrad : ContDiff ℝ 1
      (fun z => gradMatrix (I.xFlow hΦ m l t) z) :=
    FlowGradientRegularity.gradMatrix_contDiff_one_of_contDiff_two hX
  have hInv : ContDiff ℝ 1 (I.xFlowInv hΦ m l t) :=
    (xFlowInv_spatial_contDiff_two I hΦ m l t).of_le (by norm_num)
  have hcomp := hgrad.comp hInv
  simpa only [Ingredients.flowGrad, Function.comp_def] using hcomp

/-- The pulled gradient matrix is C² in space, using C³ regularity of
the forward and inverse flow slices. -/
theorem flowGrad_spatial_contDiff_two
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    ContDiff ℝ 2 (fun x => I.flowGrad hΦ m l t x) := by
  have hX : ContDiff ℝ 3 (I.xFlow hΦ m l t) :=
    xFlow_spatial_contDiff_three I hΦ m l t
  have hgrad : ContDiff ℝ 2
      (fun z => gradMatrix (I.xFlow hΦ m l t) z) :=
    FlowGradientRegularity.gradMatrix_contDiff_two_of_contDiff_three hX
  have hInv : ContDiff ℝ 2 (I.xFlowInv hΦ m l t) :=
    (xFlowInv_spatial_contDiff_three I hΦ m l t).of_le (by norm_num)
  have hcomp := hgrad.comp hInv
  simpa only [Ingredients.flowGrad, Function.comp_def] using hcomp

end AVenhance.Infra.Section5
