/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationInitial
public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationSourceData

@[expose] public section

/-! A fully constructed normal and terminal coordinate for a positive
activation time.  The initial matching statements concern the actual
source history and its continuation, with no normal-choice premise. -/

noncomputable section

namespace EulerPacketActivationHistory

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerTransverseActivationSelection
  EulerTransverseFrameCoordinates EulerPacketMovingFrame EulerPacketNormalizedPrimary
  EulerPacketCrossProduct EulerPacketPrimaryFactorization

theorem activation_cross_ne_zero (m v : Space) (hm : m ≠ 0) (hv : v ≠ 0)
    (hmv : ⟪m,v⟫_ℝ=0) : cross (unit m) (unit v) ≠ 0 := by
  have h := (frame_orthonormal (unit m) (unit v)
    (unit_inner_self hm) (unit_inner_self hv) (unit_inner_zero hmv)).norm_eq_one 2
  change ‖cross (unit m) (unit v)‖=1 at h
  intro hz
  rw [hz,norm_zero] at h
  norm_num at h

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : Data U) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))

def activatedData (m v : ℝ → Space) (hm : m τ ≠ 0) (hv : v τ ≠ 0)
    (hmv : ⟪m τ,v τ⟫_ℝ=0) :
    Data (referencePlane (activationDirection (D.deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
      (cross (unit (m τ)) (unit (v τ))))) :=
  D.activation ⟨τ,hτ.le,hτT.le⟩ (cross (unit (m τ)) (unit (v τ)))
    (activation_cross_ne_zero _ _ hm hv hmv)

def activatedHistory (m v : ℝ → Space) (hm : m τ ≠ 0) (hv : v τ ≠ 0)
    (hmv : ⟪m τ,v τ⟫_ℝ=0) :
    HistoryData ((activatedData D τ hτ hτT m v hm hv hmv).initial τ hτ hτT.le) :=
  B.reframe (activationDirection (D.deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
    (cross (unit (m τ)) (unit (v τ))))
    (activationDirection_unit _ (activation_cross_ne_zero _ _ hm hv hmv))

theorem constructed_initial_matching
    (m v : ℝ → Space) (hm : m τ ≠ 0) (hv : v τ ≠ 0) (hmv : ⟪m τ,v τ⟫_ℝ=0)
    (hHs : ∀ t, (B.H.field t 0).IsSymmetric)
    (h CM CH ζ a ε : ℝ) (hh : 0 < h) (hLayer : 1 ≤ h*τ)
    (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (hζ : 0 ≤ ζ) (hε : 0 < ε)
    (hM : ∀ t : Icc (0 : ℝ) τ, ‖(D.initial τ hτ hτT.le).M.field t 0‖ ≤ CM*h)
    (hHnorm : ‖B.coefficients.labelHessian 0‖ ≤ CH*h^2)
    (hζsmall : 16*(activationConstant CM CH+1)*ζ ≤ 1)
    (hB : ‖D.M.field ⟨τ,hτ.le,hτT.le⟩ 0-
      h • rankOne ℝ (unit (v τ)) (unit (m τ))‖ ≤ ζ*h)
    (hBpp : ⟪D.M.field ⟨τ,hτ.le,hτT.le⟩ 0 (unit (m τ)),unit (m τ)⟫_ℝ < 0) :
    let Da := activatedData D τ hτ hτT m v hm hv hmv
    let Ba := activatedHistory D τ hτ hτT B m v hm hv hmv
    let s₀ := activationRayScale (D.deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
      (cross (unit (m τ)) (unit (v τ)))
    0 < s₀ ∧
      scaledRay m v (fun s => Da.normal.field (Da.clamp s) 0) s₀ τ a ε 0 = ![0,0,1] ∧
      ∃ ξ : referencePlane Da.m₀, ∃ lam : ℝ, ξ ≠ 0 ∧ 0 ≤ lam ∧
        lam ≤ 8*(activationConstant CM CH+1)/ε ∧
        ‖ξ‖ ≤ (8*(activationConstant CM CH+1)*D.inverseBound)/h ∧
        scaledVelocity m v (fun s => uncutVelocity (D := Da) τ hτ hτT Ba ξ s 0) τ a ε 0 0 = -lam ∧
        scaledVelocity m v (fun s => uncutVelocity (D := Da) τ hτ hτT Ba ξ s 0) τ a ε 0 1 = 1 := by
  exact exists_activated_primary (D := activatedData D τ hτ hτT m v hm hv hmv)
    τ hτ hτT (activatedHistory D τ hτ hτT B m v hm hv hmv)
    m v hm hv hmv rfl hHs h CM CH ζ a ε hh hLayer hCM hCH hζ hε hM hHnorm hζsmall hB hBpp

end EulerPacketActivationHistory
