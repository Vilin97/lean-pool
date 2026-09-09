/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointLabels
public import LeanPool.NavierStokesAndEuler.Euler.TransverseActivationSelection
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryData
import LeanPool.NavierStokesAndEuler.Euler.PacketActivationData

/-! Source activation in the actual physical tangent plane.  Ambient
strain error and compression bounds imply the compressed terminal-matrix
hypotheses, so no abstract endpoint matrix or plane isometry is supplied. -/

@[expose] public section


noncomputable section

namespace EulerPacketActivationHistory

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerTransverseFrameCoordinates EulerTransverseSourceCoefficientPath
  EulerTransverseActivationSelection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem terminalPerturbation_compression (T : ℝ) (hT : 0 ≤ T)
    (R : V →ₗᵢ[ℝ] Space) (M : C(Icc (0 : ℝ) T, Space →L[ℝ] Space)) (p q : V) (h : ℝ) :
    terminalPerturbation T hT R M p q h =
      R.toContinuousLinearMap.adjoint.comp
        ((M ⟨T,hT,le_rfl⟩-h • rankOne ℝ (R q) (R p)).comp R.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  simp only [terminalPerturbation,sub_apply,comp_apply,smul_apply,rankOne_apply,
    inner_sub_left,real_inner_smul_left,adjoint_inner_left,
    LinearIsometry.coe_toContinuousLinearMap,R.inner_map_map]

theorem terminalPerturbation_norm_le (T : ℝ) (hT : 0 ≤ T)
    (R : V →ₗᵢ[ℝ] Space) (M : C(Icc (0 : ℝ) T, Space →L[ℝ] Space)) (p q : V) (h : ℝ) :
    ‖terminalPerturbation T hT R M p q h‖ ≤ ‖M ⟨T,hT,le_rfl⟩-h • rankOne ℝ (R q) (R p)‖ := by
  rw [terminalPerturbation_compression]
  have hR := R.norm_toContinuousLinearMap_le
  have hRa : ‖R.toContinuousLinearMap.adjoint‖ ≤ 1 := by rwa [LinearIsometryEquiv.norm_map]
  refine (opNorm_comp_le _ _).trans ?_
  calc
    _ ≤ 1*‖(M ⟨T,hT,le_rfl⟩-h • rankOne ℝ (R q) (R p)).comp R.toContinuousLinearMap‖ :=
      mul_le_mul_of_nonneg_right hRa (norm_nonneg _)
    _ = _ := one_mul _
    _ ≤ ‖M ⟨T,hT,le_rfl⟩-h • rankOne ℝ (R q) (R p)‖*‖R.toContinuousLinearMap‖ := opNorm_comp_le _ _
    _ ≤ ‖M ⟨T,hT,le_rfl⟩-h • rankOne ℝ (R q) (R p)‖*1 :=
      mul_le_mul_of_nonneg_left hR (norm_nonneg _)
    _ = _ := mul_one _

theorem terminalPerturbation_diagonal (T : ℝ) (hT : 0 ≤ T)
    (R : V →ₗᵢ[ℝ] Space) (M : C(Icc (0 : ℝ) T, Space →L[ℝ] Space)) (p q : V) (h : ℝ)
    (hpq : ⟪p, q⟫_ℝ = 0) :
    ⟪terminalPerturbation T hT R M p q h p,p⟫_ℝ = ⟪M ⟨T,hT,le_rfl⟩ (R p),R p⟫_ℝ := by
  have hqp : ⟪q,p⟫_ℝ=0 := by rwa [real_inner_comm]
  simp only [terminalPerturbation,sub_apply,comp_apply,smul_apply,rankOne_apply,
    inner_sub_left,real_inner_smul_left,adjoint_inner_left,hqp,mul_zero,sub_zero,
    LinearIsometry.coe_toContinuousLinearMap]

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D)

theorem select_physical_history_coordinate
    (hHs : ∀ t, (B.H.field t 0).IsSymmetric)
    (h CM CH ε : ℝ) (hh : 0 < h) (hLayer : 1 ≤ h * D.T)
    (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (hε : 0 ≤ ε)
    (hM : ∀ t, ‖D.M.field t 0‖ ≤ CM * h)
    (hHnorm : ‖B.coefficients.labelHessian 0‖ ≤ CH * h ^ 2)
    (p q : Space) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : ⟪p, q⟫_ℝ = 0)
    (hpm : ⟪D.normal.field ⟨D.T, D.T_pos.le, le_rfl⟩ 0, p⟫_ℝ = 0)
    (hqm : ⟪D.normal.field ⟨D.T, D.T_pos.le, le_rfl⟩ 0, q⟫_ℝ = 0)
    (hεsmall : 16 * (activationConstant CM CH + 1) * ε ≤ 1)
    (hB : ‖D.M.field ⟨D.T, D.T_pos.le, le_rfl⟩ 0 - h • rankOne ℝ q p‖ ≤ ε * h)
    (hBpp : ⟪D.M.field ⟨D.T, D.T_pos.le, le_rfl⟩ 0 p, p⟫_ℝ < 0) :
    ∃ ξ : U, ξ ≠ 0 ∧
      ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,q⟫_ℝ=1 ∧
      -8*(activationConstant CM CH+1) ≤
        ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,p⟫_ℝ ∧
      ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,p⟫_ℝ ≤ 0 ∧
      ‖ξ‖ ≤ (8*(activationConstant CM CH+1)*D.inverseBound)/h := by
  let P := referencePlane (D.normal.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0)
  let R : P →ₗᵢ[ℝ] Space := P.subtypeₗᵢ
  let p' : P := ⟨p,Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hpm⟩
  let q' : P := ⟨q,Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hqm⟩
  have hR : ∀ Y : P, ⟪D.normal.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0,R Y⟫_ℝ=0 :=
    fun Y => Submodule.mem_orthogonal_singleton_iff_inner_right.mp Y.property
  have he : ‖terminalPerturbation D.T D.T_pos.le R (pathEvaluation 0 D.M.field) p' q' h‖ ≤ ε*h :=
    (terminalPerturbation_norm_le D.T D.T_pos.le R (pathEvaluation 0 D.M.field) p' q' h).trans hB
  have hc : ⟪terminalPerturbation D.T D.T_pos.le R (pathEvaluation 0 D.M.field) p' q' h p',p'⟫_ℝ <
      0 := by
    rw [terminalPerturbation_diagonal D.T D.T_pos.le R (pathEvaluation 0 D.M.field) p' q' h hpq]
    exact hBpp
  exact select_history_coordinate B R hR hHs h CM CH ε hh hLayer hCM hCH hε hM hHnorm
    p' q' hp hq hpq hεsmall he hc

end EulerPacketActivationHistory
