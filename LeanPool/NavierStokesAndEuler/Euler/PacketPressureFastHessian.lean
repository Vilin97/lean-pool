/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketGraphHessian
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! The leading angular pressure force gives its actual rank-one Hessian.
Only first slow derivatives occur in the remainder. -/

@[expose] public section


noncomputable section

namespace EulerPacketGraphHessian

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerGraphPullback
  EulerLiftedGradientSpace
open scoped ContDiff

/-- Fast force, given by `k⁻¹ • (a (graphMap k m (Y x)) • transportedNormal m J x)`. -/
def fastForce (a : LiftTangent → ℝ) (k : ℝ) (m : Space) (Y : Space → Space)
    (J : Space → Space →L[ℝ] Space) (x : Space) : Space :=
  k⁻¹ • (a (graphMap k m (Y x)) • transportedNormal m J x)

/-- Fast hessian remainder as an element of `Space →L[ℝ] Space`. -/
def fastHessianRemainder (a : LiftTangent → ℝ) (k : ℝ) (m : Space) (Y : Space → Space)
    (J : Space → Space →L[ℝ] Space) (x : Space) : Space →L[ℝ] Space :=
  k⁻¹ • (a (graphMap k m (Y x)) • fderiv ℝ (transportedNormal m J) x +
    (((fderiv ℝ a (graphMap k m (Y x))).comp (inl ℝ Space ℝ)).comp (J x)).smulRight
      (transportedNormal m J x))

theorem fastForce_hasFDerivAt (a : LiftTangent → ℝ) (k : ℝ) (hk : k ≠ 0)
    (m : Space) (Y : Space → Space) (J : Space → Space →L[ℝ] Space)
    (x : Space) (hY : HasFDerivAt Y (J x) x) (hJ : DifferentiableAt ℝ J x)
    (ha : DifferentiableAt ℝ a (graphMap k m (Y x))) :
    HasFDerivAt (fastForce a k m Y J)
      (angularDerivative a (graphMap k m (Y x)) •
        rankOne ℝ (transportedNormal m J x) (transportedNormal m J x) +
          fastHessianRemainder a k m Y J x) x := by
  have hgraph : HasFDerivAt (fun y => graphMap k m (Y y)) ((graphMap k m).comp (J x)) x :=
    (graphMap k m).hasFDerivAt.comp x hY
  have hcomp := ha.hasFDerivAt.comp x hgraph
  have hn : DifferentiableAt ℝ (transportedNormal m J) x :=
    (adjoint.differentiableAt.comp x hJ).clm_apply (differentiableAt_const m)
  convert! (hcomp.smul hn.hasFDerivAt).const_smul k⁻¹ using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [fastHessianRemainder,angularDerivative,add_apply,smul_apply,comp_apply,
    smulRight_apply,rankOne_apply,graph_decomposition,map_add,map_smul,smul_eq_mul,inl_apply,
    Function.comp_apply]
  rw [← (J x).adjoint_inner_left v m]
  dsimp only [transportedNormal]
  match_scalars <;> field_simp
  all_goals ring

theorem fastHessianRemainder_norm_le (a : LiftTangent → ℝ) (k : ℝ) (m : Space)
    (Y : Space → Space) (J : Space → Space →L[ℝ] Space) (x : Space) :
    ‖fastHessianRemainder a k m Y J x‖ ≤
      |k⁻¹| * (|a (graphMap k m (Y x))| * ‖fderiv ℝ (transportedNormal m J) x‖ +
        ‖fderiv ℝ a (graphMap k m (Y x))‖ * ‖J x‖ * ‖transportedNormal m J x‖) := by
  unfold fastHessianRemainder
  rw [norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_eq_abs,norm_smulRight_apply]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (opNorm_comp_le _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [norm_inl, mul_one] using
    opNorm_comp_le (fderiv ℝ a (graphMap k m (Y x))) (inl ℝ Space ℝ)

theorem norm_fderiv_smul_unit (a : LiftTangent → ℝ) (m : Space) (hm : ‖m‖ = 1)
    (z : LiftTangent) (ha : DifferentiableAt ℝ a z) :
    ‖fderiv ℝ (fun y => a y • m) z‖ = ‖fderiv ℝ a z‖ := by
  rw [(ha.hasFDerivAt.smul_const m).fderiv,norm_smulRight_apply,hm,mul_one]

theorem norm_fderiv_clm_apply_le (A : Space → Space →L[ℝ] Space) (u : Space → Space)
    (x : Space) (hA : DifferentiableAt ℝ A x) (hu : DifferentiableAt ℝ u x) :
    ‖fderiv ℝ (fun y => A y (u y)) x‖ ≤
      ‖A x‖*‖fderiv ℝ u x‖+‖fderiv ℝ A x‖*‖u x‖ := by
  rw [fderiv_clm_apply hA hu]
  exact (norm_add_le _ _).trans (add_le_add (opNorm_comp_le _ _)
    (by simpa only [opNorm_flip] using (fderiv ℝ A x).flip.le_opNorm (u x)))

end EulerPacketGraphHessian
