/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationRay
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryData

@[expose] public section

/-! The source deformation can be equipped with the actual activation
normal.  The new reference plane is the literal orthogonal complement,
and the history hypotheses are inherited without any new analytic input. -/

noncomputable section

namespace EulerTransversePacketProvider

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransverseFrameCoordinates EulerPacketMovingFrame

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

def Data.reframe (D : Data U) (m : Space) (hm : ‖m‖=1) : Data (referencePlane m) where
  T := D.T
  T_pos := D.T_pos
  support := D.support
  support_compact := D.support_compact
  m₀ := m
  m₀_unit := hm
  R := LinearIsometryEquiv.refl ℝ (referencePlane m)
  F := D.F
  F₁ := D.F₁
  FInv := D.FInv
  M := D.M
  inverse_left := D.inverse_left
  inverse_right := D.inverse_right
  frame_time := D.frame_time
  strain_equation := D.strain_equation

def HistoryData.reframe {D : Data U} (B : HistoryData D) (m : Space) (hm : ‖m‖=1) :
    HistoryData (D.reframe m hm) where
  H := B.H
  jacobi := B.jacobi
  potential := B.potential
  potential_nonneg := B.potential_nonneg
  potential_bound := B.potential_bound
  small := B.small

def Data.activation (D : Data U) (t₀ : Icc (0 : ℝ) D.T) (n : Space) (hn : n ≠ 0) :
    Data (referencePlane (activationDirection (D.deformationEquiv t₀ 0) n)) :=
  D.reframe (activationDirection (D.deformationEquiv t₀ 0) n)
    (activationDirection_unit _ hn)

theorem Data.activation_normal (D : Data U) (t₀ : Icc (0 : ℝ) D.T) (n : Space) (hn : n ≠ 0) :
    (D.activation t₀ n hn).normal.field t₀ 0 = activationRayScale (D.deformationEquiv t₀ 0) n • n
      := by
  exact activationDirection_transport (D.deformationEquiv t₀ 0) n

def HistoryData.activation {D : Data U} (B : HistoryData D)
    (t₀ : Icc (0 : ℝ) D.T) (n : Space) (hn : n ≠ 0) : HistoryData (D.activation t₀ n hn) :=
  B.reframe (activationDirection (D.deformationEquiv t₀ 0) n) (activationDirection_unit _ hn)

theorem Data.activationRayScale_bounds (D : Data U) (t₀ : Icc (0 : ℝ) D.T) (n : Space)
    (hn : ‖n‖=1) :
    0 < activationRayScale (D.deformationEquiv t₀ 0) n ∧
      activationRayScale (D.deformationEquiv t₀ 0) n ≤ D.inverseBound ∧
      (activationRayScale (D.deformationEquiv t₀ 0) n)⁻¹ ≤ D.frameBound := by
  have hn0 : n ≠ 0 := by intro hz; rw [hz,norm_zero] at hn; norm_num at hn
  let F := D.deformationEquiv t₀ 0
  have hpos : 0 < ‖F.toContinuousLinearMap.adjoint n‖ :=
    norm_pos_iff.mpr (forward_adjoint_ne_zero F hn0)
  have hlo : 1 ≤ D.inverseBound*‖F.toContinuousLinearMap.adjoint n‖ := by
    calc
      1 = ‖F.symm.toContinuousLinearMap.adjoint (F.toContinuousLinearMap.adjoint n)‖ := by
        rw [inverse_adjoint_forward_adjoint,hn]
      _ ≤ ‖F.symm.toContinuousLinearMap.adjoint‖*‖F.toContinuousLinearMap.adjoint n‖ :=
        F.symm.toContinuousLinearMap.adjoint.le_opNorm _
      _ ≤ D.inverseBound*‖F.toContinuousLinearMap.adjoint n‖ := by
        rw [LinearIsometryEquiv.norm_map]
        exact mul_le_mul_of_nonneg_right (D.inverse_norm t₀ 0) (norm_nonneg _)
  have hhi : ‖F.toContinuousLinearMap.adjoint n‖ ≤ D.frameBound := by
    calc
      _ ≤ ‖F.toContinuousLinearMap.adjoint‖*‖n‖ := F.toContinuousLinearMap.adjoint.le_opNorm n
      _ = ‖D.F.field t₀ 0‖ := by rw [LinearIsometryEquiv.norm_map,hn,mul_one]; rfl
      _ ≤ D.frameBound := D.frame_norm t₀ 0
  refine ⟨activationRayScale_pos F hn0,?_,?_⟩
  · simpa only [activationRayScale,one_div] using (div_le_iff₀ hpos).mpr hlo
  · simpa only [activationRayScale,inv_inv] using hhi

end EulerTransversePacketProvider
