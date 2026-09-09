/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentFrameReframe
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketJoinedInput

/-! The source direction at a stage is constructed from the actual
parent deformation and older frame. Both branch-specific normal-choice
identities are conclusions, and the reference plane is literal. -/

@[expose] public section


noncomputable section

namespace EulerPacketSourceGeometry.ParentFrame

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerParentPacketFrames EulerTransversePacketProvider EulerTransverseFrameCoordinates
  EulerPacketMovingFrame EulerPacketNormalizedPrimary EulerPacketCrossProduct

variable {A : Parent} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {m : Space} {hm : ‖m‖ = 1} {R : U ≃ₗᵢ[ℝ] referencePlane m}
  {S : Set Space} {hS : IsCompact S} {τ : ℝ}
  (P : ParentFrame (A.transverseData m hm R S hS) τ)

/-- Cross direction, given by `cross (unit (P.m τ)) (unit (P.v τ))`. -/
def crossDirection : Space := cross (unit (P.m τ)) (unit (P.v τ))

theorem crossDirection_unit (hτT : τ ≤ A.T) : ‖P.crossDirection‖=1 := by
  exact (frame_orthonormal (unit (P.m τ)) (unit (P.v τ))
    (unit_inner_self (P.ray_nonzero τ ⟨le_rfl,hτT⟩))
    (unit_inner_self (P.velocity_nonzero τ ⟨le_rfl,hτT⟩))
    (unit_inner_zero (P.tangent τ ⟨le_rfl,hτT⟩))).norm_eq_one 2

theorem crossDirection_ne_zero (hτT : τ ≤ A.T) : P.crossDirection ≠ 0 := by
  intro hz
  have h := P.crossDirection_unit hτT
  rw [hz,norm_zero] at h
  norm_num at h

variable (hτ : 0 < τ) (hτT : τ < A.T)

/-- Activation normal, given by `activationDirection ((A.transverseData m hm R S
hS).deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0) P.crossDirection`. -/
def activationNormal : Space :=
  activationDirection ((A.transverseData m hm R S hS).deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
    P.crossDirection

theorem activationNormal_unit : ‖P.activationNormal hτ hτT‖=1 :=
  activationDirection_unit _ (P.crossDirection_ne_zero hτT.le)

/-- Activation data, constructed using `A.transverseData`. -/
def activationData : Data (referencePlane (P.activationNormal hτ hτT)) :=
  A.transverseData (P.activationNormal hτ hτT) (P.activationNormal_unit hτ hτT)
    (LinearIsometryEquiv.refl ℝ (referencePlane (P.activationNormal hτ hτT))) S hS

/-- Activation frame, constructed using `P.reframe`. -/
def activationFrame : ParentFrame (P.activationData hτ hτT) τ :=
  P.reframe (P.activationNormal hτ hτT) (P.activationNormal_unit hτ hτT)
    (LinearIsometryEquiv.refl ℝ (referencePlane (P.activationNormal hτ hτT)))

theorem activation_normal_choice :
    (P.activationData hτ hτT).m₀ =
      activationDirection ((P.activationData hτ hτT).deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
        (cross (unit ((P.activationFrame hτ hτT).m τ))
          (unit ((P.activationFrame hτ hτT).v τ))) := rfl

theorem activation_parameters :
    (P.activationFrame hτ hτT).a=P.a ∧ (P.activationFrame hτ hτT).sigma=P.sigma ∧
      (P.activationFrame hτ hτT).shear=P.shear ∧ (P.activationFrame hτ hτT).epsilon=P.epsilon ∧
      (P.activationFrame hτ hτT).horizon=P.horizon ∧ (P.activationFrame hτ hτT).G=P.G ∧
      (P.activationFrame hτ hτT).error=P.error := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The new covector really transports to the old frame's cross
direction, with the same strictly positive ray scale used by Guards. -/
theorem activation_ray :
    (P.activationData hτ hτT).normal.field ⟨τ,hτ.le,hτT.le⟩ 0 =
      P.rayScale hτ hτT • P.crossDirection :=
  activationDirection_transport
    ((A.transverseData m hm R S hS).deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0) P.crossDirection

theorem activation_scaled_ray :
    0 < P.rayScale hτ hτT ∧
      scaledRay P.m P.v
        (fun t => (P.activationData hτ hτT).normal.field ((P.activationData hτ hτT).clamp t) 0)
        (P.rayScale hτ hτT) τ P.a P.epsilon 0=![0,0,1] := by
  exact actual_activation_scaled_ray (P.activationData hτ hτT) P.m P.v
    ⟨τ,hτ.le,hτT.le⟩ P.a P.epsilon
    (P.ray_nonzero τ ⟨le_rfl,hτT.le⟩) (P.velocity_nonzero τ ⟨le_rfl,hτT.le⟩)
    (P.tangent τ ⟨le_rfl,hτT.le⟩) (P.activation_normal_choice hτ hτT)

/-- Activation history, constructed using `A.historyOn`. -/
def activationHistory (H : LowBounds A) :
    HistoryData ((P.activationData hτ hτT).initial τ hτ hτT.le) :=
  A.historyOn H (P.activationNormal hτ hτT) (P.activationNormal_unit hτ hτT)
    (LinearIsometryEquiv.refl ℝ (referencePlane (P.activationNormal hτ hτT))) S hS τ hτ hτT

theorem activation_history_eq (H : LowBounds A) :
    P.activationHistory hτ hτT H =
      (A.historyOn H m hm R S hS τ hτ hτT).reframe
        (P.activationNormal hτ hτT) (P.activationNormal_unit hτ hτT) := rfl

end EulerPacketSourceGeometry.ParentFrame

namespace EulerPacketSourceGeometry.ParentFrame

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerParentPacketFrames EulerTransversePacketProvider EulerTransverseFrameCoordinates
  EulerPacketMovingFrame EulerPacketNormalizedPrimary EulerPacketCrossProduct

variable {A : Parent} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {m : Space} {hm : ‖m‖ = 1} {R : U ≃ₗᵢ[ℝ] referencePlane m}
  {S : Set Space} {hS : IsCompact S}
  (P : ParentFrame (A.transverseData m hm R S hS) 0)

/-- Forward data, constructed using `A.transverseData`. -/
def forwardData : Data (referencePlane P.crossDirection) :=
  A.transverseData P.crossDirection (P.crossDirection_unit A.T_pos.le)
    (LinearIsometryEquiv.refl ℝ (referencePlane P.crossDirection)) S hS

/-- Forward frame, given by `P.reframe P.crossDirection (P.crossDirection_unit A.T_pos.le)
(LinearIsometryEquiv.refl ℝ (referencePlane P.crossDirection))`. -/
def forwardFrame : ParentFrame P.forwardData 0 :=
  P.reframe P.crossDirection (P.crossDirection_unit A.T_pos.le)
    (LinearIsometryEquiv.refl ℝ (referencePlane P.crossDirection))

theorem forward_normal_choice : P.forwardData.m₀ =
    cross (unit (P.forwardFrame.m 0)) (unit (P.forwardFrame.v 0)) := rfl

theorem forward_initial_frame (x : Space) :
    P.forwardData.F.field ⟨0,le_rfl,A.T_pos.le⟩ x=ContinuousLinearMap.id ℝ Space :=
  A.frame_initial x

theorem forward_initial_normal (x : Space) :
    P.forwardData.normal.field ⟨0,le_rfl,A.T_pos.le⟩ x=P.crossDirection := by
  change (A.inverse.field A.zeroTime x).adjoint P.crossDirection=P.crossDirection
  have h : A.inverse.field A.zeroTime x=ContinuousLinearMap.id ℝ Space := by
    apply ContinuousLinearMap.ext
    intro v
    exact A.inverse_initial x v
  rw [h,adjoint_id,id_apply]

theorem forward_parameters :
    P.forwardFrame.a=P.a ∧ P.forwardFrame.sigma=P.sigma ∧
      P.forwardFrame.shear=P.shear ∧ P.forwardFrame.epsilon=P.epsilon ∧
      P.forwardFrame.horizon=P.horizon ∧ P.forwardFrame.G=P.G ∧ P.forwardFrame.error=P.error :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end EulerPacketSourceGeometry.ParentFrame
