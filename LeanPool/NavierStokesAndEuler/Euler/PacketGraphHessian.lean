/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPressureLocality

@[expose] public section

/-! Differentiating an actual oscillatory scalar pressure through the
inverse flow. The principal Hessian is the angular second derivative
times the square of the transported normal. -/

noncomputable section

namespace EulerPacketGraphHessian

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerGraphPullback
  EulerLiftedGradientSpace
open scoped ContDiff

def spatialGradient (q : LiftTangent → ℝ) (z : LiftTangent) : Space :=
  (toDual ℝ Space).symm ((fderiv ℝ q z).comp (inl ℝ Space ℝ))

def angularDerivative (q : LiftTangent → ℝ) (z : LiftTangent) : ℝ :=
  fderiv ℝ q z (0,1)

theorem spatialGradient_contDiff {q : LiftTangent → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (spatialGradient q) :=
  (toDual ℝ Space).symm.toContinuousLinearMap.contDiff.comp
    ((contDiff_infty_iff_fderiv.mp hq).2.clm_comp contDiff_const)

theorem angularDerivative_contDiff {q : LiftTangent → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (angularDerivative q) :=
  (contDiff_infty_iff_fderiv.mp hq).2.clm_apply contDiff_const

theorem angularDerivative_eq_deriv {q : LiftTangent → ℝ} {z : LiftTangent}
    (hq : DifferentiableAt ℝ q z) :
    angularDerivative q z = deriv (fun θ => q (z.1,θ)) z.2 := by
  exact ((hq.hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv).symm

theorem angularSecond_eq_deriv {q : LiftTangent → ℝ} (hq : ContDiff ℝ ∞ q)
    (z : LiftTangent) :
    angularDerivative (angularDerivative q) z =
      deriv (deriv (fun θ => q (z.1,θ))) z.2 := by
  rw [angularDerivative_eq_deriv ((angularDerivative_contDiff hq).differentiable (by simp) z)]
  congr 1
  funext θ
  exact angularDerivative_eq_deriv (hq.differentiable (by simp) (z.1,θ))

theorem graph_decomposition (k : ℝ) (m v : Space) :
    graphMap k m v = (v,0)+(k*⟪m,v⟫_ℝ) • (0,1) := by
  ext i <;> simp [graphMap_apply]

theorem gradient_graph {q : LiftTangent → ℝ} (k : ℝ) (m x : Space)
    (hq : DifferentiableAt ℝ q (graphMap k m x)) :
    gradient (fun y => q (graphMap k m y)) x =
      spatialGradient q (graphMap k m x)+
        (k*angularDerivative q (graphMap k m x)) • m := by
  apply ext_inner_right ℝ
  intro v
  have hd : fderiv ℝ (fun y => q (graphMap k m y)) x =
      (fderiv ℝ q (graphMap k m x)).comp (graphMap k m) :=
    (hq.hasFDerivAt.comp x (graphMap k m).hasFDerivAt).fderiv
  rw [inner_gradient_left,hd]
  simp only [comp_apply,inner_add_left,real_inner_smul_left,spatialGradient,toDual_symm_apply,
    inl_apply,graph_decomposition,map_add,map_smul,smul_eq_mul,angularDerivative]
  ring

theorem gradient_physical {q : LiftTangent → ℝ} (k : ℝ) (m : Space)
    (Y : Space → Space) (J : Space →L[ℝ] Space) (x : Space)
    (hY : HasFDerivAt Y J x) (hq : DifferentiableAt ℝ q (graphMap k m (Y x))) :
    gradient (fun y => k⁻¹^2 * q (graphMap k m (Y y))) x =
      k⁻¹^2 • J.adjoint (spatialGradient q (graphMap k m (Y x)))+
        (k⁻¹^2*k*angularDerivative q (graphMap k m (Y x))) • J.adjoint m := by
  have hg := hq.hasFDerivAt.comp (Y x) (graphMap k m).hasFDerivAt
  have hc := (hg.comp x hY).const_smul (k⁻¹^2)
  have hd : fderiv ℝ (fun y => k⁻¹^2 * q (graphMap k m (Y y))) x =
      k⁻¹^2 • ((fderiv ℝ q (graphMap k m (Y x))).comp (graphMap k m)).comp J := hc.fderiv
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,hd]
  simp only [smul_apply,comp_apply,smul_eq_mul,inner_add_left,real_inner_smul_left,
    adjoint_inner_left,spatialGradient,toDual_symm_apply,inl_apply,
    graph_decomposition,map_add,map_smul,smul_eq_mul,angularDerivative]
  ring

def transportedNormal (m : Space) (J : Space → Space →L[ℝ] Space) (x : Space) : Space :=
  (J x).adjoint m

def slowForce (q : LiftTangent → ℝ) (k : ℝ) (m : Space)
    (Y : Space → Space) (J : Space → Space →L[ℝ] Space) (x : Space) : Space :=
  (J x).adjoint (spatialGradient q (graphMap k m (Y x)))

def lowerHessian (q : LiftTangent → ℝ) (k : ℝ) (m : Space)
    (Y : Space → Space) (J : Space → Space →L[ℝ] Space) (x : Space) : Space →L[ℝ] Space :=
  k⁻¹^2 • fderiv ℝ (slowForce q k m Y J) x +
    k⁻¹ • (angularDerivative q (graphMap k m (Y x)) • fderiv ℝ (transportedNormal m J) x +
      (((fderiv ℝ (angularDerivative q) (graphMap k m (Y x))).comp (inl ℝ Space ℝ)).comp
        (J x)).smulRight (transportedNormal m J x))

theorem hessian_physical {q : LiftTangent → ℝ} (hq : ContDiff ℝ ∞ q)
    (k : ℝ) (hk : k ≠ 0) (m : Space) (Y : Space → Space)
    (J : Space → Space →L[ℝ] Space) (hY : ∀ x, HasFDerivAt Y (J x) x)
    (x : Space) (hJ : DifferentiableAt ℝ J x) :
    fderiv ℝ (gradient (fun y => k⁻¹^2 * q (graphMap k m (Y y)))) x =
      angularDerivative (angularDerivative q) (graphMap k m (Y x)) •
        rankOne ℝ (transportedNormal m J x) (transportedNormal m J x) +
      lowerHessian q k m Y J x := by
  let z := graphMap k m (Y x)
  let n := transportedNormal m J
  let a := fun y => angularDerivative q (graphMap k m (Y y))
  have hgraph : HasFDerivAt (fun y => graphMap k m (Y y))
      ((graphMap k m).comp (J x)) x := (graphMap k m).hasFDerivAt.comp x (hY x)
  have hang : HasFDerivAt (angularDerivative q) (fderiv ℝ (angularDerivative q) z) z :=
    ((angularDerivative_contDiff hq).differentiable (by simp) z).hasFDerivAt
  have ha : HasFDerivAt a
      (((fderiv ℝ (angularDerivative q) z).comp (graphMap k m)).comp (J x)) x := by
    convert! hang.comp x hgraph using 1
  have hn : DifferentiableAt ℝ n x :=
    (adjoint.differentiableAt.comp x hJ).clm_apply (differentiableAt_const m)
  have hsp : DifferentiableAt ℝ (spatialGradient q) z :=
    (spatialGradient_contDiff hq).differentiable (by simp) z
  have hspg : DifferentiableAt ℝ (fun y => spatialGradient q (graphMap k m (Y y))) x := by
    have hcomp := hsp.comp x hgraph.differentiableAt
    exact hcomp
  have hs : DifferentiableAt ℝ (slowForce q k m Y J) x :=
    (adjoint.differentiableAt.comp x hJ).clm_apply hspg
  have hg : gradient (fun y => k⁻¹^2 * q (graphMap k m (Y y))) =
      fun y => k⁻¹^2 • slowForce q k m Y J y + k⁻¹ • (a y • n y) := by
    funext y
    rw [gradient_physical k m Y (J y) y (hY y)
      (hq.differentiable (by simp) (graphMap k m (Y y)))]
    simp only [slowForce,a,n,transportedNormal,smul_smul]
    congr 1
    congr 1
    field_simp
  rw [hg]
  have hd : fderiv ℝ (fun y => k⁻¹^2 • slowForce q k m Y J y + k⁻¹ • (a y • n y)) x =
      k⁻¹^2 • fderiv ℝ (slowForce q k m Y J) x +
        k⁻¹ • (a x • fderiv ℝ n x +
          (((fderiv ℝ (angularDerivative q) z).comp (graphMap k m)).comp (J x)).smulRight
            (n x)) :=
    ((hs.hasFDerivAt.const_smul (k⁻¹^2)).add
      ((ha.smul hn.hasFDerivAt).const_smul k⁻¹)).fderiv
  rw [hd]
  apply ContinuousLinearMap.ext
  intro v
  simp only [lowerHessian,add_apply,smul_apply,comp_apply,smulRight_apply,rankOne_apply,
    graph_decomposition,map_add,map_smul,smul_eq_mul,angularDerivative]
  have hm : ⟪m,J x v⟫_ℝ = ⟪n x,v⟫_ℝ := ((J x).adjoint_inner_left v m).symm
  rw [hm]
  dsimp only [z,a,n]
  simp only [angularDerivative,graph_decomposition,inl_apply]
  match_scalars <;> field_simp
  all_goals ring

theorem lowerHessian_norm_le (q : LiftTangent → ℝ) (k : ℝ) (m : Space)
    (Y : Space → Space) (J : Space → Space →L[ℝ] Space) (x : Space) :
    ‖lowerHessian q k m Y J x‖ ≤
      |k⁻¹|^2 * ‖fderiv ℝ (slowForce q k m Y J) x‖ +
      |k⁻¹| * (|angularDerivative q (graphMap k m (Y x))| *
        ‖fderiv ℝ (transportedNormal m J) x‖ +
        ‖(fderiv ℝ (angularDerivative q) (graphMap k m (Y x))).comp (inl ℝ Space ℝ)‖ *
          ‖J x‖ * ‖transportedNormal m J x‖) := by
  unfold lowerHessian
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,abs_pow]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs]
  apply add_le_add le_rfl
  rw [norm_smulRight_apply]
  exact mul_le_mul_of_nonneg_right (opNorm_comp_le _ _) (norm_nonneg _)

end EulerPacketGraphHessian
