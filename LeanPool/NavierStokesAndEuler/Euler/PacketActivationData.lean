/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationHistory
public import LeanPool.NavierStokesAndEuler.Euler.TransverseActivationSelection
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistory
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketTimeData

/-! Actual activation data for the packet's own stationary history.  The
terminal coordinate and its signed velocity components are constructed
from the source Dirichlet-to-Neumann argument. -/

@[expose] public section


noncomputable section

namespace EulerPacketActivationHistory

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerTimeLp EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTransverseEndpointEnergy EulerTransverseEndpointVelocity
   EulerTransverseEndpointParameter
      EulerTransverseEndpointCoordinates
  EulerTransverseInitialCoordinates EulerTransverseFrameCoordinates
      EulerTransverseSourceCoefficientPath
  EulerTransverseActivationSelection EulerTransverseActivationTrial

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {D : Data U} (B : HistoryData D)

theorem select_history_coordinate
    (R : V →ₗᵢ[ℝ] Space)
    (hR : ∀ Y, ⟪D.normal.field ⟨D.T, D.T_pos.le, le_rfl⟩ 0, R Y⟫_ℝ = 0)
    (hHs : ∀ t, (B.H.field t 0).IsSymmetric)
    (h CM CH ε : ℝ) (hh : 0 < h) (hLayer : 1 ≤ h * D.T)
    (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (hε : 0 ≤ ε)
    (hM : ∀ t, ‖D.M.field t 0‖ ≤ CM * h)
    (hHnorm : ‖B.coefficients.labelHessian 0‖ ≤ CH * h ^ 2)
    (p q : V) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : ⟪p, q⟫_ℝ = 0)
    (hεsmall : 16 * (activationConstant CM CH + 1) * ε ≤ 1)
    (hB : ‖terminalPerturbation D.T D.T_pos.le R (pathEvaluation 0 D.M.field) p q h‖ ≤ ε * h)
    (hBpp : ⟪terminalPerturbation D.T D.T_pos.le R (pathEvaluation 0 D.M.field) p q h p, p⟫_ℝ < 0) :
    ∃ ξ : U, ξ ≠ 0 ∧
      ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,R q⟫_ℝ=1 ∧
      -8*(activationConstant CM CH+1) ≤
        ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,R p⟫_ℝ ∧
      ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,R p⟫_ℝ ≤ 0 ∧
      ‖ξ‖ ≤ (8*(activationConstant CM CH+1)*D.inverseBound)/h := by
  let C := B.coefficients
  let m : C(Icc (0 : ℝ) D.T,Space) := pathEvaluation 0 D.normal.field
  let m₁ : C(Icc (0 : ℝ) D.T,Space) := pathEvaluation 0 D.normalDerivative
  let M : C(Icc (0 : ℝ) D.T,Space →L[ℝ] Space) := pathEvaluation 0 D.M.field
  have hne : ∀ t, m t ≠ 0 := fun t => HistoryData.normal_ne_zero t 0
  have hdm : ∀ t : Icc (0 : ℝ) D.T,
      HasDerivWithinAt (extendPath D.T D.T_pos.le m) (m₁ t) (Icc (0 : ℝ) D.T) t := by
    intro t
    have hd := D.normal_hasDerivWithinAt t t.property 0
    convert! hd using 1
    simp only [extendPath,projIcc_of_mem D.T_pos.le t.property]
    rfl
  have hRay : ∀ t, m₁ t = -(M t).adjoint (m t) := fun t => D.normalDerivative_apply t 0
  have hm : ∀ t v, ⟪m t,C.labelFrame 0 t v⟫_ℝ=0 := fun t v => D.frame_tangent t 0 v
  have hRange : ∀ t η, ⟪m t,η⟫_ℝ=0 → ∃ v : U, C.labelFrame 0 t v=η :=
    fun t η ht => D.frame_range t 0 η ht
  obtain ⟨Y,hY⟩ := select_actual_activation D.T D.T_pos (C.labelFrame 0) (C.labelFrameDerivative 0)
    C.lower C.lower_pos (C.labelFrame_lower 0) (C.labelFrame_derivative 0)
    m m₁ hne hdm hm hRange R hR (C.labelHessian 0) hHs
    B.potential B.potential_nonneg (C.labelHessian_upper 0) B.small M hRay
    h CM CH ε hh hLayer hCM hCH hε hM hHnorm p q hp hq hpq hεsmall hB hBpp
  let L := activationTrial D.T D.T_pos.le m m₁ hne R.toContinuousLinearMap h
  have hL : ∀ Z t, ⟪D.normal.field t 0,initialPrimitive D.T D.T_pos.le (L Z) t⟫_ℝ=0 :=
    activationTrial_tangent D.T D.T_pos.le m m₁ hne R.toContinuousLinearMap hdm h
  have hLT : ∀ Z, initialPrimitive D.T D.T_pos.le (L Z) ⟨D.T,D.T_pos.le,le_rfl⟩=R Z :=
    activationTrial_terminal D.T D.T_pos.le m m₁ hne R.toContinuousLinearMap hdm h hLayer hR
  obtain ⟨ξ,hξ⟩ := D.frame_range ⟨D.T,D.T_pos.le,le_rfl⟩ 0 (R Y) (hR Y)
  have ht : initialRealPrimitive D.T (L Y) D.T =
      D.frame.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0 ξ := (hLT Y).trans hξ.symm
  have hw := history_eq_stationary_of_terminal B 0 L hL Y ξ ht ⟨D.T,D.T_pos.le,le_rfl⟩
  rcases hY with ⟨_,_,_,_,_,hwq,hwpl,hwpu,hsize⟩
  have hqv : ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,R q⟫_ℝ=1 := by
    rw [hw]
    convert! hwq using 1
    simp only [stationaryCorrectedVelocity,stationaryDerivative,L,C,m,M,
      extendPath,projIcc_of_mem D.T_pos.le (show D.T ∈ Icc (0 : ℝ) D.T from ⟨D.T_pos.le,le_rfl⟩)]
    rfl
  have hpl : -8*(activationConstant CM CH+1) ≤
      ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,R p⟫_ℝ := by
    rw [hw]
    convert! hwpl using 1
    simp only [stationaryCorrectedVelocity,stationaryDerivative,L,C,m,M,
      extendPath,projIcc_of_mem D.T_pos.le (show D.T ∈ Icc (0 : ℝ) D.T from ⟨D.T_pos.le,le_rfl⟩)]
    rfl
  have hpu : ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,R p⟫_ℝ ≤ 0 := by
    rw [hw]
    convert! hwpu using 1
    simp only [stationaryCorrectedVelocity,stationaryDerivative,L,C,m,M,
      extendPath,projIcc_of_mem D.T_pos.le (show D.T ∈ Icc (0 : ℝ) D.T from ⟨D.T_pos.le,le_rfl⟩)]
    rfl
  have hnonzero : ξ ≠ 0 := by
    intro hz
    rw [hz,map_zero,ContinuousMap.zero_apply,inner_zero_left] at hqv
    norm_num at hqv
  have hleft : (D.R ξ : Space) = D.FInv.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0 (R Y) := by
    have hv := congrArg (D.FInv.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0) hξ
    change D.FInv.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0
      (D.F.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0 (D.R ξ : Space)) = _ at hv
    rwa [D.inverse_left] at hv
  have hnorm : ‖ξ‖ ≤ D.inverseBound*‖Y‖ := by
    calc
      _ = ‖(D.R ξ : Space)‖ := (D.R.norm_map ξ).symm
      _ = ‖D.FInv.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0 (R Y)‖ := congrArg norm hleft
      _ ≤ ‖D.FInv.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0‖*‖R Y‖ := le_opNorm _ _
      _ ≤ D.inverseBound*‖R Y‖ := mul_le_mul_of_nonneg_right (D.inverse_norm _ _) (norm_nonneg _)
      _ = D.inverseBound*‖Y‖ := by rw [R.norm_map]
  refine ⟨ξ,hnonzero,hqv,hpl,hpu,hnorm.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hsize D.inverseBound_pos.le).trans_eq (by ring)

end EulerPacketActivationHistory
