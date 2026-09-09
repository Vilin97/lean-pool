/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationRay
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryUncut
public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocity
public import LeanPool.NavierStokesAndEuler.Euler.TransverseActivationSelection
import LeanPool.NavierStokesAndEuler.Euler.PacketActivationFrame
import LeanPool.NavierStokesAndEuler.Euler.PacketInitialGeometry

/-! Actual center initial data for the geometric propagation theorem.
The selected terminal coordinate drives the same stationary history and
homogeneous continuation used in the constructed packet. -/

@[expose] public section


noncomputable section

namespace EulerPacketActivationHistory

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerTransverseActivationSelection
  EulerPacketMovingFrame EulerPacketNormalizedPrimary EulerPacketCrossProduct
  EulerPacketPrimaryFactorization

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))

theorem exists_activated_primary
    (m v : ℝ → Space) (hm : m τ ≠ 0) (hv : v τ ≠ 0) (hmv : ⟪m τ, v τ⟫_ℝ = 0)
    (hchoice : D.m₀ = activationDirection (D.deformationEquiv ⟨τ, hτ.le, hτT.le⟩ 0)
      (cross (unit (m τ)) (unit (v τ))))
    (hHs : ∀ t, (B.H.field t 0).IsSymmetric)
    (h CM CH ζ a ε : ℝ) (hh : 0 < h) (hLayer : 1 ≤ h * τ)
    (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (hζ : 0 ≤ ζ) (hε : 0 < ε)
    (hM : ∀ t : Icc (0 : ℝ) τ, ‖(D.initial τ hτ hτT.le).M.field t 0‖ ≤ CM*h)
    (hHnorm : ‖B.coefficients.labelHessian 0‖ ≤ CH*h^2)
    (hζsmall : 16*(activationConstant CM CH+1)*ζ ≤ 1)
    (hB : ‖D.M.field ⟨τ,hτ.le,hτT.le⟩ 0 -
      h • rankOne ℝ (unit (v τ)) (unit (m τ))‖ ≤ ζ*h)
    (hBpp : ⟪D.M.field ⟨τ,hτ.le,hτT.le⟩ 0 (unit (m τ)),unit (m τ)⟫_ℝ < 0) :
    let s₀ := activationRayScale (D.deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
      (cross (unit (m τ)) (unit (v τ)))
    0 < s₀ ∧
      scaledRay m v (fun s => D.normal.field (D.clamp s) 0) s₀ τ a ε 0 = ![0,0,1] ∧
      ∃ ξ : U, ∃ lam : ℝ, ξ ≠ 0 ∧ 0 ≤ lam ∧
        lam ≤ 8*(activationConstant CM CH+1)/ε ∧
        ‖ξ‖ ≤ (8*(activationConstant CM CH+1)*D.inverseBound)/h ∧
        scaledVelocity m v (fun s => uncutVelocity τ hτ hτT B ξ s 0) τ a ε 0 0 = -lam ∧
        scaledVelocity m v (fun s => uncutVelocity τ hτ hτT B ξ s 0) τ a ε 0 1 = 1 := by
  dsimp only
  have hnormal := actual_normal_of_activation_choice D ⟨τ,hτ.le,hτT.le⟩ 0 _ hchoice
  have hp : ⟪(D.initial τ hτ hτT.le).normal.field ⟨τ,hτ.le,le_rfl⟩ 0,unit (m τ)⟫_ℝ=0 := by
    change ⟪D.normal.field ⟨τ,hτ.le,hτT.le⟩ 0,unit (m τ)⟫_ℝ=0
    rw [hnormal,real_inner_smul_left,real_inner_comm,inner_cross_first,mul_zero]
  have hq : ⟪(D.initial τ hτ hτT.le).normal.field ⟨τ,hτ.le,le_rfl⟩ 0,unit (v τ)⟫_ℝ=0 := by
    change ⟪D.normal.field ⟨τ,hτ.le,hτT.le⟩ 0,unit (v τ)⟫_ℝ=0
    rw [hnormal,real_inner_smul_left,real_inner_comm,inner_cross_second,mul_zero]
  obtain ⟨ξ,hξ,hqξ,hplo,hphi,hξnorm⟩ := select_physical_history_coordinate B hHs
    h CM CH ζ hh hLayer hCM hCH hζ hM hHnorm
    (unit (m τ)) (unit (v τ)) (unit_norm hm) (unit_norm hv) (unit_inner_zero hmv)
    hp hq hζsmall hB hBpp
  have hs := actual_activation_scaled_ray D m v ⟨τ,hτ.le,hτT.le⟩ a ε hm hv hmv hchoice
  refine ⟨hs.1,hs.2,ξ,-⟪B.coefficients.labelVelocity 0 ξ ⟨τ,hτ.le,le_rfl⟩,unit (m τ)⟫_ℝ/ε,
    hξ,?_⟩
  have hw : uncutVelocity τ hτ hτT B ξ τ 0 = B.coefficients.labelVelocity 0 ξ ⟨τ,hτ.le,le_rfl⟩ :=
    uncutVelocity_history τ hτ hτT B ξ ⟨τ,hτ.le,le_rfl⟩ 0
  have hpw : ⟪unit (m τ),uncutVelocity τ hτ hτT B ξ τ 0⟫_ℝ =
      ⟪B.coefficients.labelVelocity 0 ξ ⟨τ,hτ.le,le_rfl⟩,unit (m τ)⟫_ℝ := by
    rw [hw,real_inner_comm]
  have hqw : ⟪unit (v τ),uncutVelocity τ hτ hτT B ξ τ 0⟫_ℝ=1 := by
    rw [hw,real_inner_comm]
    exact hqξ
  have hplo' : -(8*(activationConstant CM CH+1)) ≤
      ⟪B.coefficients.labelVelocity 0 ξ ⟨τ,hτ.le,le_rfl⟩,unit (m τ)⟫_ℝ := by
    convert! hplo using 1
    ring
  have hvinit := activation_scaled_velocity (a := a) hε hplo' hphi hpw hqw
  refine ⟨hvinit.1,hvinit.2.1,?_,hvinit.2.2.1,hvinit.2.2.2⟩
  apply hξnorm.trans
  apply div_le_div_of_nonneg_right _ hh.le
  exact mul_le_mul_of_nonneg_left (D.initial_inverseBound_le τ hτ hτT.le) (by
    unfold activationConstant
    positivity)

end EulerPacketActivationHistory
