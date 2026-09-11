/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketGeometryGuards
public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionScaleBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketNestedHorizons
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleActual
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketNeighborPolynomial
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceParameterScales
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryData
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketNeighborBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleGuards
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketScaleGeometry
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageRestriction
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketJoinedInput
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketSourceData
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceGeometryData
public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationSourceData

/-! Literal forward and joined source guards for the next packet of an
actual finite stage. The radius is one, the spike and target shear are
the prescribed source scales, and the physical target is nextTime. -/

section

/-! The actual next packet geometry is constructed from the current
finite stage. Source normals, history bounds and the neighboring-label
guards are derived from its state and the one fixed scale choice. -/

section

/-! The source direction at a stage is constructed from the actual
parent deformation and older frame. Both branch-specific normal-choice
identities are conclusions, and the reference plane is literal. -/

section

/-! Changing the source normal and reference plane leaves the older
physical frame and its scalar parameters unchanged. The source strain
and time interval are the actual fields of the same parent. -/

@[expose] public section

noncomputable section

namespace EulerPacketSourceGeometry.ParentFrame

open Set EulerSmoothLimit EulerParentPacketFrames EulerTransversePacketProvider
  EulerTransverseFrameCoordinates

variable {A : Parent} {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {m : Space} {hm : ‖m‖ = 1} {R : U ≃ₗᵢ[ℝ] referencePlane m}
  {S : Set Space} {hS : IsCompact S} {τ : ℝ}
  (P : ParentFrame (A.transverseData m hm R S hS) τ)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (m' : Space) (hm' : ‖m'‖ = 1) (R' : V ≃ₗᵢ[ℝ] referencePlane m')

/-- Reframe, bundling `B`, `B₁`, `m`, `v` and the required compatibility proofs. -/
def reframe : ParentFrame (A.transverseData m' hm' R' S hS) τ where
  B := P.B
  B₁ := P.B₁
  m := P.m
  v := P.v
  c := P.c
  G := P.G
  error := P.error
  G_lower := P.G_lower
  error_nonneg := P.error_nonneg
  B_derivative := P.B_derivative
  ray_equation := P.ray_equation
  velocity_equation := P.velocity_equation
  ray_nonzero := P.ray_nonzero
  velocity_nonzero := P.velocity_nonzero
  tangent := P.tangent
  B_bound := P.B_bound
  B₁_bound := P.B₁_bound
  remainder_bound := P.remainder_bound

@[simp] theorem reframe_B : (P.reframe m' hm' R').B=P.B := rfl
@[simp] theorem reframe_B₁ : (P.reframe m' hm' R').B₁=P.B₁ := rfl
@[simp] theorem reframe_m : (P.reframe m' hm' R').m=P.m := rfl
@[simp] theorem reframe_v : (P.reframe m' hm' R').v=P.v := rfl
@[simp] theorem reframe_c : (P.reframe m' hm' R').c=P.c := rfl
@[simp] theorem reframe_G : (P.reframe m' hm' R').G=P.G := rfl
@[simp] theorem reframe_error : (P.reframe m' hm' R').error=P.error := rfl
@[simp] theorem reframe_a : (P.reframe m' hm' R').a=P.a := rfl
@[simp] theorem reframe_sigma : (P.reframe m' hm' R').sigma=P.sigma := rfl
@[simp] theorem reframe_shear : (P.reframe m' hm' R').shear=P.shear := rfl
@[simp] theorem reframe_epsilon : (P.reframe m' hm' R').epsilon=P.epsilon := rfl
@[simp] theorem reframe_horizon : (P.reframe m' hm' R').horizon=P.horizon := rfl

@[simp] theorem reframe_rayScale (hτ : 0 < τ) (hτT : τ < A.T) :
    (P.reframe m' hm' R').rayScale hτ hτT=P.rayScale hτ hτT := rfl

@[simp] theorem reframe_terminalBound (CM CH : ℝ) :
    (P.reframe m' hm' R').terminalBound CM CH=P.terminalBound CM CH := rfl

end EulerPacketSourceGeometry.ParentFrame

namespace EulerParentPacketFrames.Parent

open Set EulerSmoothLimit EulerTransversePacketProvider EulerTransverseFrameCoordinates

variable (A : Parent) {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (m' : Space) (hm' : ‖m'‖ = 1) (R' : V ≃ₗᵢ[ℝ] referencePlane m')

theorem transverse_deformation_reframe (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.transverseData m' hm' R' S hS).deformationEquiv t x =
      (A.transverseData m hm R S hS).deformationEquiv t x := rfl

theorem transverse_reframe :
    (A.transverseData m hm R S hS).reframe m' hm' =
      A.transverseData m' hm' (LinearIsometryEquiv.refl ℝ (referencePlane m')) S hS := rfl

end EulerParentPacketFrames.Parent

end
end

end

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

end
end

end

@[expose] public section

noncomputable section

open scoped ContDiff

namespace EulerParentPacketFrames.Evolution

open Set InnerProductSpace EulerSmoothLimit

theorem pressure_smooth {A : Parent} (E : Evolution A) (t : Icc (0 : ℝ) A.T) :
    ContDiff ℝ ∞ (fun x => E.pressure (t,x)) := by
  apply contDiff_infty_iff_fderiv.mpr
  refine ⟨fun x => E.pressure_differentiable t x, ?_⟩
  have he : fderiv ℝ (fun x => E.pressure (t,x)) =
      (toDual ℝ Space).toContinuousLinearMap ∘ E.force t := by
    funext x
    change fderiv ℝ (fun y => E.pressure (t,y)) x=(toDual ℝ Space) (E.force t x)
    rw [← toDual_gradient,E.pressure_gradient]
  rw [he]
  exact (toDual ℝ Space).toContinuousLinearMap.contDiff.comp (E.force_smooth t)

end EulerParentPacketFrames.Evolution

namespace EulerPacketSourceGeometry.ParentFrame

open EulerTransversePacketProvider

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U} {s t : ℝ} (P : ParentFrame D s) (h : s = t)

/-- Change activation, given by `h ▸ P`. -/
def changeActivation : ParentFrame D t := h ▸ P

@[simp] theorem changeActivation_a : (P.changeActivation h).a=P.a := by cases h; rfl
@[simp] theorem changeActivation_sigma : (P.changeActivation h).sigma=P.sigma := by cases h; rfl
@[simp] theorem changeActivation_shear : (P.changeActivation h).shear=P.shear := by cases h; rfl
@[simp] theorem changeActivation_G : (P.changeActivation h).G=P.G := by cases h; rfl
@[simp] theorem changeActivation_error : (P.changeActivation h).error=P.error := by cases h; rfl
@[simp] theorem changeActivation_horizon : (P.changeActivation h).horizon=P.horizon := by
    cases h; rfl
@[simp] theorem changeActivation_B : (P.changeActivation h).B=P.B := by cases h; rfl
@[simp] theorem changeActivation_m : (P.changeActivation h).m=P.m := by cases h; rfl
@[simp] theorem changeActivation_v : (P.changeActivation h).v=P.v := by cases h; rfl

end EulerPacketSourceGeometry.ParentFrame

namespace EulerPacketInductionScales.Scales

open Real EulerPacketSourceScaleSequence

variable {c B : ℝ} (S : Scales c B)

theorem previousShear_monotone : Monotone (previousShear S.J S.X) := by
  apply monotone_nat_of_le_succ
  intro n
  have hp := S.previousShear_one n
  have hs := S.shear_separation n
  change previousShear S.J S.X n ≤ shear S.J S.X n
  nlinarith only [hp,hs,sq_nonneg (previousShear S.J S.X n-1)]

theorem previousShear_double_base {n : ℕ} (hn : n ≠ 0) :
    2*S.X^1000 ≤ previousShear S.J S.X n := by
  have hm := S.previousShear_monotone (show 1 ≤ n by omega)
  have hs := S.shear_separation 0
  have hp := S.previousShear_one 0
  change shear S.J S.X 0 ≤ previousShear S.J S.X n at hm
  change (S.X^1000)^2 ≤ shear S.J S.X 0/4 at hs
  change 1 ≤ S.X^1000 at hp
  nlinarith only [hm,hs,hp,sq_nonneg (S.X^1000-1)]

end EulerPacketInductionScales.Scales

namespace EulerPacketInduction.Stage

open Set Real InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerParentPacketFrames
  EulerPacketSourceGeometry EulerTransversePacketProvider EulerTransverseFrameCoordinates
  EulerPacketInductionScales EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketSourceScaleActual EulerPacketBaseGuardScales EulerPacketLowConstants
  EulerPacketNormalizedPrimary
  EulerPacketSupport EulerTimeIntervalRestriction

section General

variable {c B : ℝ} {S : Scales c B} {n : ℕ} (P : Stage S n)

theorem history_layer (hn : n ≠ 0) : 1 ≤ previousShear S.J S.X n*P.time := by
  have hi : P.time⁻¹ ≤ previousShear S.J S.X n :=
    (P.time_reciprocal hn).trans
      ((EulerPacketSourceParameterScales.base_inverse_time_le S.J S.j_one S.X S.x_one).trans
        (S.previousShear_double_base hn))
  exact (div_le_iff₀ (P.time_pos hn)).mp (by simpa only [one_div] using hi)

/-- Joined normal, given by `P.restrictedFrame.activationNormal (P.time_pos hn)
P.time_lt_nextHorizon`. -/
def joinedNormal (hn : n ≠ 0) : Space :=
  P.restrictedFrame.activationNormal (P.time_pos hn) P.time_lt_nextHorizon

theorem joinedNormal_unit (hn : n ≠ 0) : ‖P.joinedNormal hn‖=1 :=
  P.restrictedFrame.activationNormal_unit (P.time_pos hn) P.time_lt_nextHorizon

/-- Joined data, given by `P.restrictedFrame.activationData (P.time_pos hn)
P.time_lt_nextHorizon`. -/
def joinedData (hn : n ≠ 0) : Data (referencePlane (P.joinedNormal hn)) :=
  P.restrictedFrame.activationData (P.time_pos hn) P.time_lt_nextHorizon

/-- Joined frame, given by `P.restrictedFrame.activationFrame (P.time_pos hn)
P.time_lt_nextHorizon`. -/
def joinedFrame (hn : n ≠ 0) : ParentFrame (P.joinedData hn) P.time :=
  P.restrictedFrame.activationFrame (P.time_pos hn) P.time_lt_nextHorizon

/-- Joined history, given by `P.restrictedFrame.activationHistory (P.time_pos hn)
P.time_lt_nextHorizon P.restrictedLow`. -/
def joinedHistory (hn : n ≠ 0) :
    HistoryData ((P.joinedData hn).initial P.time (P.time_pos hn) P.time_lt_nextHorizon.le) :=
  P.restrictedFrame.activationHistory (P.time_pos hn) P.time_lt_nextHorizon P.restrictedLow

@[simp] theorem joinedFrame_a (hn : n ≠ 0) : (P.joinedFrame hn).a=P.frame.a :=
  (P.restrictedFrame.activation_parameters (P.time_pos hn) P.time_lt_nextHorizon).1.trans
    P.restrictedFrame_a
@[simp] theorem joinedFrame_sigma (hn : n ≠ 0) : (P.joinedFrame hn).sigma=P.frame.sigma :=
  (P.restrictedFrame.activation_parameters (P.time_pos hn) P.time_lt_nextHorizon).2.1.trans
    P.restrictedFrame_sigma
@[simp] theorem joinedFrame_shear (hn : n ≠ 0) : (P.joinedFrame hn).shear=P.frame.shear :=
  (P.restrictedFrame.activation_parameters (P.time_pos hn) P.time_lt_nextHorizon).2.2.1.trans
    P.restrictedFrame_shear
@[simp] theorem joinedFrame_G (hn : n ≠ 0) : (P.joinedFrame hn).G=P.frame.G :=
  (P.restrictedFrame.activation_parameters (P.time_pos hn) P.time_lt_nextHorizon).2.2.2.2.2.1.trans
    P.restrictedFrame_G
@[simp] theorem joinedFrame_error (hn : n ≠ 0) : (P.joinedFrame hn).error=P.frame.error :=
  (P.restrictedFrame.activation_parameters (P.time_pos hn) P.time_lt_nextHorizon).2.2.2.2.2.2.trans
    P.restrictedFrame_error
@[simp] theorem joinedFrame_horizon (hn : n ≠ 0) :
    (P.joinedFrame hn).horizon=P.restrictedFrame.horizon :=
  (P.restrictedFrame.activation_parameters (P.time_pos hn) P.time_lt_nextHorizon).2.2.2.2.1

theorem joined_history_strain (hn : n ≠ 0) :
    ‖EulerTransverseSourceCoefficientPath.pathEvaluation 0
      ((P.joinedData hn).initial P.time (P.time_pos hn) P.time_lt_nextHorizon.le).M.field‖ ≤
      gradientConstant*previousShear S.J S.X n := by
  apply (ContinuousMap.norm_le _ (mul_nonneg gradient_nonneg
    (zero_le_one.trans (S.previousShear_one n)))).2
  intro t
  change ‖P.restrictedParent.strain.field
    (initialInclusion P.restrictedParent.T P.time P.time_lt_nextHorizon.le t) 0‖ ≤ _
  exact P.restricted_strain_bound
    (initialInclusion P.restrictedParent.T P.time P.time_lt_nextHorizon.le t) 0

theorem joined_history_hessian (hn : n ≠ 0) :
    ‖(P.joinedHistory hn).coefficients.labelHessian 0‖ ≤
      hessianConstant*(previousShear S.J S.X n)^2 := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hessian_nonneg (sq_nonneg _))).2
  intro t
  change ‖P.restrictedParent.curvature.field
    (initialInclusion P.restrictedParent.T P.time P.time_lt_nextHorizon.le t) 0‖ ≤ _
  have hp := P.restricted_curvature_bound
    (initialInclusion P.restrictedParent.T P.time P.time_lt_nextHorizon.le t) 0
  have hm := mul_le_mul_of_nonneg_left (S.olderShear_le n)
    (mul_nonneg hessian_nonneg (zero_le_one.trans (S.previousShear_one n)))
  exact hp.trans (by nlinarith only [hm])

end General

section ForwardData

variable {c B : ℝ} {S : Scales c B} (P : Stage S 0)

/-- Zero frame, given by `P.restrictedFrame.changeActivation (P.time_zero rfl)`. -/
def zeroFrame : ParentFrame (frameData P.restrictedParent) 0 :=
  P.restrictedFrame.changeActivation (P.time_zero rfl)

/-- Forward normal, given by `P.zeroFrame.crossDirection`. -/
def forwardNormal : Space := P.zeroFrame.crossDirection

theorem forwardNormal_unit : ‖P.forwardNormal‖=1 :=
  P.zeroFrame.crossDirection_unit P.restrictedParent.T_pos.le

/-- Forward data, given by `P.zeroFrame.forwardData`. -/
def forwardData : Data (referencePlane P.forwardNormal) := P.zeroFrame.forwardData

/-- Forward frame, given by `P.zeroFrame.forwardFrame`. -/
def forwardFrame : ParentFrame P.forwardData 0 := P.zeroFrame.forwardFrame

@[simp] theorem forwardFrame_a : P.forwardFrame.a=P.frame.a :=
  P.zeroFrame.forward_parameters.1.trans
    ((P.restrictedFrame.changeActivation_a (P.time_zero rfl)).trans P.restrictedFrame_a)

@[simp] theorem forwardFrame_sigma : P.forwardFrame.sigma=P.frame.sigma :=
  P.zeroFrame.forward_parameters.2.1.trans
    ((P.restrictedFrame.changeActivation_sigma (P.time_zero rfl)).trans P.restrictedFrame_sigma)

@[simp] theorem forwardFrame_shear : P.forwardFrame.shear=P.frame.shear :=
  P.zeroFrame.forward_parameters.2.2.1.trans
    ((P.restrictedFrame.changeActivation_shear (P.time_zero rfl)).trans P.restrictedFrame_shear)

@[simp] theorem forwardFrame_G : P.forwardFrame.G=P.frame.G :=
  P.zeroFrame.forward_parameters.2.2.2.2.2.1.trans
    ((P.restrictedFrame.changeActivation_G (P.time_zero rfl)).trans P.restrictedFrame_G)

@[simp] theorem forwardFrame_error : P.forwardFrame.error=P.frame.error :=
  P.zeroFrame.forward_parameters.2.2.2.2.2.2.trans
    ((P.restrictedFrame.changeActivation_error (P.time_zero rfl)).trans P.restrictedFrame_error)

@[simp] theorem forwardFrame_horizon : P.forwardFrame.horizon=P.restrictedFrame.horizon :=
  P.zeroFrame.forward_parameters.2.2.2.2.1.trans
    (P.restrictedFrame.changeActivation_horizon (P.time_zero rfl))

end ForwardData

end EulerPacketInduction.Stage

end
end

end

section

/-! Reciprocal history times fit the literal previous-frequency budget.
Only the first geometric step needs coupling and tilt bounds. All later
step lengths are nonnegative independently of any future frame invariant. -/

@[expose] public section

noncomputable section

namespace EulerParentHistoryFrequency

open Real EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketSourceParameterScales EulerPacketSourceScaleActual
  EulerPacketNestedHorizons EulerPacketBaseGuardScales

theorem frequency_monotone (J : ℕ) (hJ : 2 ≤ J) (X : ℝ) (hX : 0 ≤ X) :
    Monotone (frequency J X) := by
  apply monotone_nat_of_le_succ
  intro n
  let j : ℝ := (J+n : ℕ)
  have hj2 : (2 : ℝ) ≤ j := by
    dsimp [j]
    exact_mod_cast (show 2 ≤ J+n by omega)
  have hj0 : 0 < j := by linarith only [hj2]
  have hx : 0 ≤ scaleSequence J X n :=
    hX.trans (sequence_initial_le J (by omega) X hX n)
  have hadd : ((J+(n+1) : ℕ) : ℝ)=j+1 := by
    dsimp [j]
    push_cast
    ring
  have hstep : j+1 ≤ j^2 := by nlinarith only [hj2,sq_nonneg (j-2)]
  have hsq : (j+1)^2 ≤ (j^2)^2 := pow_le_pow_left₀ (by positivity) hstep 2
  apply exp_le_exp.mpr
  change scaleSequence J X n/j^2 ≤ scaleSequence J X (n+1)/((J+(n+1) : ℕ) : ℝ)^2
  rw [scaleSequence_succ,hadd]
  apply (div_le_div_iff₀ (sq_pos_of_pos hj0) (sq_pos_of_pos (by positivity))).2
  calc
    scaleSequence J X n*(j+1)^2 ≤ scaleSequence J X n*(j^2)^2 :=
      mul_le_mul_of_nonneg_left hsq hx
    _ = (j^2*scaleSequence J X n)*j^2 := by ring

theorem initial_frequency_le_first (J D : ℕ) (hJ : 3 ≤ J) (X : ℝ) (hX : 0 ≤ X)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) :
    X^D ≤ frequency J X 0 := by
  let j : ℝ := (J-1 : ℕ)
  have hj2 : (2 : ℝ) ≤ j := by
    dsimp [j]
    exact_mod_cast (show 2 ≤ J-1 by omega)
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hadd : (J : ℝ)=j+1 := by
    dsimp [j]
    exact_mod_cast (show J=J-1+1 by omega)
  have hstep : j+1 ≤ j^2 := by nlinarith only [hj2,sq_nonneg (j-2)]
  have hsq : (J : ℝ)^2 ≤ j^4 := by
    rw [hadd]
    simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity) hstep 2
  apply hbase.trans
  change exp (X/j^4) ≤ exp (X/(J : ℝ)^2)
  exact exp_le_exp.mpr (div_le_div_of_nonneg_left hX (sq_pos_of_pos hJ0) hsq)

theorem initial_frequency_le_previous (J D : ℕ) (hJ : 3 ≤ J) (X : ℝ) (hX : 0 ≤ X)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n : ℕ) :
    X^D ≤ previousFrequency J D X n := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
    exact (initial_frequency_le_first J D hJ X hX hbase).trans
      (frequency_monotone J (by omega) X hX (Nat.zero_le n))

theorem previousFrequency_one_le (J D : ℕ) (hJ : 3 ≤ J) (X : ℝ) (hX : 1 ≤ X)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n : ℕ) :
    1 ≤ previousFrequency J D X n :=
  (one_le_pow₀ hX).trans
    (initial_frequency_le_previous J D hJ X (zero_le_one.trans hX) hbase n)

theorem base_inverse_le_initial_frequency (J D : ℕ) (hJ : 1 ≤ J) (hD : 2000 ≤ D)
    (X : ℝ) (hX : 2 ≤ X) : 12/baseHorizon J X ≤ X^D := by
  have hx1 : 1 ≤ X := by linarith only [hX]
  have hx0 : 0 ≤ X := zero_le_one.trans hx1
  have hxpow : 2 ≤ X^1000 := hX.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hx1 (by decide : 1 ≤ 1000))
  calc
    12/baseHorizon J X ≤ 2*X^1000 := base_inverse_time_le J hJ X hx1
    _ ≤ X^1000*X^1000 := mul_le_mul_of_nonneg_right hxpow (pow_nonneg hx0 1000)
    _ = X^2000 := by rw [← pow_add]
    _ ≤ X^D := pow_le_pow_right₀ hx1 hD

theorem base_inverse_le_previous_frequency (J D : ℕ) (hJ : 3 ≤ J) (hD : 2000 ≤ D)
    (X : ℝ) (hX : 2 ≤ X)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n : ℕ) :
    12/baseHorizon J X ≤ previousFrequency J D X n :=
  (base_inverse_le_initial_frequency J D (by omega) hD X hX).trans
    (initial_frequency_le_previous J D hJ X (by linarith only [hX]) hbase n)

theorem base_inverse_le_previous_frequency_pow80 (J D : ℕ) (hJ : 3 ≤ J) (hD : 2000 ≤ D)
    (X : ℝ) (hX : 2 ≤ X)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n : ℕ) :
    12/baseHorizon J X ≤ previousFrequency J D X n^80 := by
  have hk := previousFrequency_one_le J D hJ X (by linarith only [hX]) hbase n
  exact (base_inverse_le_previous_frequency J D hJ hD X hX hbase n).trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hk (by decide : 1 ≤ 80))

theorem stepLength_nonneg (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 ≤ X)
    (a β : ℕ → ℝ) (n : ℕ) : 0 ≤ stepLength J X a β n :=
  div_nonneg (hX.trans (sequence_initial_le J hJ X hX (n+1))) (sqrt_nonneg _)

theorem activation_lower_of_initial (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 < X)
    (a β : ℕ → ℝ) (ha : 1 / 2 ≤ a 0) (ha₂ : a 0 ≤ 2)
    (hβ : 1 / 2 ≤ β 0 * X ^ 2) (hβ₂ : β 0 * X ^ 2 ≤ 2) {n : ℕ} (hn : 1 ≤ n) :
    baseHorizon J X/12 ≤ activationTime J X a β n := by
  have hxnext : 0 ≤ scaleSequence J X 1 :=
    hX.le.trans (sequence_initial_le J hJ X hX.le 1)
  have hfirst : timeWidth J X 0/6 ≤ stepLength J X a β 0 :=
    (EulerPacketScaleGeometry.activation_time_bounds ha ha₂
      (previousShear_pos J hX 0) hX hxnext hβ hβ₂).1
  have hsum : stepLength J X a β 0 ≤ activationTime J X a β n := by
    apply Finset.single_le_sum
    · intro i _
      exact stepLength_nonneg J hJ X hX.le a β i
    · exact Finset.mem_range.mpr (by omega)
  rw [baseHorizon_eq_timeWidth J hX]
  linarith only [hfirst,hsum]

theorem reciprocal_activation_le_base (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 < X)
    (a β : ℕ → ℝ) (ha : 1 / 2 ≤ a 0) (ha₂ : a 0 ≤ 2)
    (hβ : 1 / 2 ≤ β 0 * X ^ 2) (hβ₂ : β 0 * X ^ 2 ≤ 2) {n : ℕ} (hn : 1 ≤ n) :
    (activationTime J X a β n)⁻¹ ≤ 12/baseHorizon J X := by
  have hb := baseHorizon_pos J hJ hX
  have hs := activation_lower_of_initial J hJ X hX a β ha ha₂ hβ hβ₂ hn
  have hi := one_div_le_one_div_of_le (div_pos hb (by norm_num)) hs
  simpa only [one_div,inv_div] using hi

theorem actual_reciprocal_activation (J D : ℕ) (hJ : 3 ≤ J) (hD : 2000 ≤ D)
    (C c X δ : ℝ) (hX : 2 ≤ X) (hb : ActualBounds J D C c X δ)
    (a β : ℕ → ℝ) (ha : 1 / 2 ≤ a 0) (ha₂ : a 0 ≤ 2)
    (hβ : 1 / 2 ≤ β 0 * X ^ 2) (hβ₂ : β 0 * X ^ 2 ≤ 2) {n : ℕ} (hn : 1 ≤ n) :
    (activationTime J X a β n)⁻¹ ≤ 12/baseHorizon J X ∧
      12/baseHorizon J X ≤ previousFrequency J D X n^80 :=
  ⟨reciprocal_activation_le_base J (by omega) X (by linarith only [hX])
      a β ha ha₂ hβ hβ₂ hn,
    base_inverse_le_previous_frequency_pow80 J D hJ hD X hX hb.initial_frequency n⟩

end EulerParentHistoryFrequency

end
end

end

section

/-! The literal numerical scale guards also initialize the zero-history
amplification stage. Its new ray and velocity start exactly in the old
frame, so only the actual strain's spatial variation enters the error. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set InnerProductSpace EulerSmoothLimit EulerPacketSourceGeometry
  EulerPacketMovingFrame EulerPacketNormalizedPrimary EulerPacketCrossProduct
  EulerPacketSourceScaleSequence EulerPacketSourceScaleChoice EulerPacketSourceScaleActual
  EulerPacketSourceScaleGuards EulerPacketSourceScales

variable {A : Parent} (L : LabelData A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1)
  (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  (P : ParentFrame (A.transverseData m hm R support hSupport) 0)

theorem forwardError_bound (ρ E N : ℝ) (hρ : 0 ≤ ρ) (hE : P.error ≤ E)
    (hN : L.strainDifferenceCost * A.ell * ρ ≤ N) : P.forwardError ρ ≤ E+N := by
  unfold ParentFrame.forwardError
  exact add_le_add hE
    ((mul_le_mul_of_nonneg_right (L.source_strain_derivative_norm m hm R support hSupport)
        hρ).trans hN)

/-- Forward geometry guards of stage as an element of `ForwardGuards P`. -/
def forwardGeometryGuardsOfStage
    (J D : ℕ) (C c X : ℝ) (a β : ℕ → ℝ) (n : ℕ)
    (CF : ℝ) (hCF : 1 ≤ CF)
    (stage : StageGuards J D C c X (neighborStabilityConstant * CF ^ 2) a β n)
    (ha : 1 / 2 ≤ a n) (ha_match : P.a = a n)
    (hshear : P.shear = previousShear J X n)
    (hsigma : P.sigma = Real.sqrt (β n))
    (htime : P.horizon = EulerPacketSourceScaleGuards.horizon J X (a n) (β n) n)
    (hG : P.G ≤ CF * (1 + olderShear J X n))
    (herr : P.error ≤ priorError J D X n)
    (ρ δ hchild : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hhchild : 0 ≤ hchild)
    (hneighbor : L.strainDifferenceCost * A.ell * ρ ≤ neighborError J D X c n)
    (hnormal : m = cross (unit (P.m 0)) (unit (P.v 0))) : ForwardGuards P := by
  have hepsilon : P.epsilon=epsilon J X (a n) n := by
    simp only [ParentFrame.epsilon,epsilon,ha_match,hshear]
  have heps : 0 < P.epsilon := by simpa only [hepsilon] using stage.epsilon_pos
  have htarget : ((scaleSequence J X (n+1))⁻¹)⁻¹/P.sigma=targetTime J X (β n) n := by
    simp only [inv_inv,hsigma,targetTime]
  have htarget1 : 1 ≤ targetTime J X (β n) n := by
    have hh : 1 ≤ 1/Real.sqrt (β n) :=
      (le_div_iff₀ stage.sigma_pos).2 (by nlinarith only [stage.sigma_small])
    exact hh.trans stage.target_from_sigma
  have htH : targetTime J X (β n) n ≤ P.horizon := by
    rw [htime]
    exact stage.target_le_horizon
  have hH : 1 ≤ P.horizon := htarget1.trans htH
  have hHθ : P.horizon ≤ sourceTheta J C (scaleSequence J X) n := by
    rw [htime]
    exact stage.horizon_le_Theta
  have hθ : 1 ≤ sourceTheta J C (scaleSequence J X) n := hH.trans hHθ
  have hshort : P.horizon-targetTime J X (β n) n ≤ 1 := by
    rw [htime]
    apply stage.extra_time.trans
    exact (div_le_iff₀ (pow_pos (zero_lt_one.trans_le hθ) 60)).2
      (by simpa only [one_mul] using one_le_pow₀ hθ (n := 60))
  have herror := L.forwardError_bound m hm R support hSupport P ρ
    (priorError J D X n) (neighborError J D X c n) hρ herr hneighbor
  have herror0 : 0 ≤ P.forwardError ρ :=
    add_nonneg P.error_nonneg (mul_nonneg (norm_nonneg _) hρ)
  have hcoef : 16*(P.epsilon*P.horizon*(4*P.G)^2+P.forwardError ρ) ≤
      CF^2*geometryError J D C c X a n := by
    have hmain : P.epsilon*P.horizon*(4*P.G)^2 ≤
        CF^2*(epsilon J X (a n) n*sourceTheta J C (scaleSequence J X) n *
          (4*(1+olderShear J X n))^2) := by
      rw [hepsilon]
      calc
        _ ≤ epsilon J X (a n) n*sourceTheta J C (scaleSequence J X) n *
            (4*(CF*(1+olderShear J X n)))^2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hHθ stage.epsilon_pos.le)
            (pow_le_pow_left₀ (by positivity [P.G_lower])
              (mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 4)) 2)
            (sq_nonneg _) (mul_nonneg stage.epsilon_pos.le (zero_le_one.trans hθ))
        _ = _ := by ring
    have hE := herror.trans (le_mul_of_one_le_left (herror0.trans herror)
      (one_le_pow₀ hCF : 1 ≤ CF^2))
    calc
      _ ≤ 16*(CF^2*(epsilon J X (a n) n*sourceTheta J C (scaleSequence J X) n *
          (4*(1+olderShear J X n))^2)+CF^2*(priorError J D X n+neighborError J D X c n)) :=
        mul_le_mul_of_nonneg_left (add_le_add hmain hE) (by norm_num)
      _ = _ := by unfold geometryError; ring
  have hcoef0 : 0 ≤ 16*(P.epsilon*P.horizon*(4*P.G)^2+P.forwardError ρ) := by
    positivity
  have hN1 : 1 ≤ 1000000*neighborStabilityConstant := by
    nlinarith only [neighborStabilityConstant_ge]
  have hN : 0 ≤ 1000000*neighborStabilityConstant := zero_le_one.trans hN1
  have hsmall : 1000000*neighborStabilityConstant *
      (16*(P.epsilon*P.horizon*(4*P.G)^2+P.forwardError ρ))*P.horizon^40 ≤ 1 := by
    calc
      _ ≤ 1000000*neighborStabilityConstant*(CF^2*geometryError J D C c X a n) *
          sourceTheta J C (scaleSequence J X) n^40 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcoef hN)
          (pow_le_pow_left₀ (zero_le_one.trans hH) hHθ 40)
          (pow_nonneg (zero_le_one.trans hH) 40) (mul_nonneg hN (hcoef0.trans hcoef))
      _ = 1000000*(neighborStabilityConstant*CF^2)*geometryError J D C c X a n *
          sourceTheta J C (scaleSequence J X) n^40 := by ring
      _ ≤ 1 := stage.geometry_small
  have hplain : 16*(P.epsilon*P.horizon*(4*P.G)^2+P.forwardError ρ) ≤ 1 := by
    have hh : 1 ≤ 1000000*neighborStabilityConstant*P.horizon^40 :=
      one_le_mul_of_one_le_of_one_le hN1 (one_le_pow₀ hH)
    have hh' := mul_le_mul_of_nonneg_right hh hcoef0
    nlinarith only [hh',hsmall]
  refine {
    radius := ρ, y := (scaleSequence J X (n+1))⁻¹, δ := δ, hchild := hchild,
    radius_nonneg := hρ, delta_nonneg := hδ, child_nonneg := hhchild,
    coupling_lower := by simpa only [ha_match] using ha,
    shear_pos := ?_, sigma_pos := by simpa only [hsigma] using stage.sigma_pos,
    sigma_small := by simpa only [hsigma] using stage.sigma_small,
    y_pos := stage.reciprocal_pos, y_small := stage.reciprocal_small,
    target_le_horizon := by simpa only [htarget] using htH,
    horizon_lower := hH, short_extension := by simpa only [htarget] using hshort,
    small := hsmall, compression_guard := ?_, initial_frame := A.frame_initial,
    normal_choice := hnormal }
  · have haP : 0 < P.a := by rw [ha_match]; linarith only [ha]
    have hdiv : 0 < P.a/P.shear := Real.sqrt_pos.mp heps
    exact (div_pos_iff.mp hdiv).resolve_right (by intro h; exact (not_lt_of_ge haP.le) h.1) |>.2
  · rw [htarget]
    exact compression_of_error_small (by simpa only [ha_match] using ha) heps.le
      (zero_le_one.trans hH) htH P.G_lower herror0 hplain

end EulerParentPacketFrames.LabelData

end
end

end

section

/-! The computed neighboring-label cost fits the source's monomial
majorant under fixed degree and constant guards. Thus the small support
scale discharges the literal neighbor comparison in the geometry step. -/

@[expose] public section

noncomputable section

namespace EulerParentNeighborCost

theorem polynomial_le_monomial (A K Ti H k h : ℝ) (n q c : ℕ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hTi : 0 ≤ Ti) (hH : 0 ≤ H)
    (hk : 1 ≤ k) (hh : 1 ≤ h) (hKk : K ≤ k ^ q) (hTik : Ti ≤ k ^ q) (hHh : H ≤ h)
    (hcost : A * 4 ^ n ≤ k) (hc : q * n + 1 ≤ c) (hn : n ≤ c) :
    A*(1+K+Ti+H)^n ≤ k^c*h^c := by
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hh0 : 0 ≤ h := zero_le_one.trans hh
  have hkq : 1 ≤ k^q := one_le_pow₀ hk
  have hkq0 : 0 ≤ k^q := zero_le_one.trans hkq
  have hkh : 1 ≤ k^q*h := one_le_mul_of_one_le_of_one_le hkq hh
  have hkk : k^q ≤ k^q*h := le_mul_of_one_le_right hkq0 hh
  have hhh : h ≤ k^q*h := le_mul_of_one_le_left hh0 hkq
  have hb : 1+K+Ti+H ≤ 4*k^q*h := by
    nlinarith only [hkh,hKk.trans hkk,hTik.trans hkk,hHh.trans hhh]
  calc
    _ ≤ A*(4*k^q*h)^n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb n) hA
    _ = (A*4^n)*(k^(q*n)*h^n) := by simp only [mul_pow,← pow_mul]; ring
    _ ≤ k*(k^(q*n)*h^n) := mul_le_mul_of_nonneg_right hcost (by positivity)
    _ = k^(q*n+1)*h^n := by rw [pow_succ]; ring
    _ ≤ k^c*h^c := mul_le_mul (pow_le_pow_right₀ hk hc) (pow_le_pow_right₀ hh hn)
      (pow_nonneg hh0 n) (pow_nonneg hk0 c)

end EulerParentNeighborCost

namespace EulerParentPacketFrames.LabelData

open Set EulerSmoothLimit EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerParentNeighborCost EulerPacketSourceScaleSequence
  EulerPacketSourceScaleActual

variable {G : Parent} (L : LabelData G)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S) (H : LowBounds G)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (P : ParentFrame (G.transverseData m hm R S hS) τ)
  (Ti CM CH : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti)
  (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (ha : 1 / 2 ≤ P.a) (hH : 1 ≤ P.shear)

include hτ1 hTi hCM hCH ha hH in
theorem neighborScaleCost_monomial (k : ℝ) (q c : ℕ)
    (hk : 1 ≤ k) (hKk : L.K ≤ k ^ q) (hTik : Ti ≤ k ^ q)
    (hcost : (EulerParentNeighborCost.boundConstant * (2 * (1 + CM + CH)) ^ degree) * 4 ^ degree
        ≤ k)
    (hc : q * degree + 1 ≤ c) (hn : degree ≤ c) :
    L.neighborScaleCost m hm R S hS H τ hτ hτT P CM CH ≤ k^c*P.shear^c := by
  have hconst := EulerParentNeighborCost.constant_pos
  exact (L.neighborScaleCost_low_polynomial m hm R S hS H τ hτ hτT P Ti CM CH
    hτ1 hTi hCM hCH ha hH).trans
      (polynomial_le_monomial
        (EulerParentNeighborCost.boundConstant * (2*(1+CM+CH))^degree)
        L.K Ti P.shear k P.shear degree q c (by positivity)
        (zero_le_one.trans L.K_one) ((inv_pos.mpr hτ).le.trans hTi)
        (zero_le_one.trans hH) hk hH hKk hTik le_rfl hcost hc hn)

include hτ1 hTi hCM hCH ha hH in
theorem neighbor_error_of_source_scales (J D : ℕ) (X ρ : ℝ) (j q c : ℕ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hshear : P.shear = previousShear J X j)
    (hk : 1 ≤ previousFrequency J D X j)
    (hKk : L.K ≤ previousFrequency J D X j ^ q) (hTik : Ti ≤ previousFrequency J D X j ^ q)
    (hcost : (EulerParentNeighborCost.boundConstant * (2 * (1 + CM + CH)) ^ degree) * 4 ^ degree
        ≤ previousFrequency J D X j)
    (hc : q * degree + 1 ≤ c) (hn : degree ≤ c)
    (hscale : G.ell ≤ supportScale J X j) :
    L.neighborScaleCost m hm R S hS H τ hτ hτT P CM CH*G.ell*ρ ≤
      neighborError J D X (c : ℝ) j := by
  have hbound := L.neighborScaleCost_monomial m hm R S hS H τ hτ hτT P Ti CM CH
    hτ1 hTi hCM hCH ha hH (previousFrequency J D X j) q c hk hKk hTik hcost hc hn
  have hmono : 0 ≤ previousFrequency J D X j^c*P.shear^c :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hk) c) (pow_nonneg (zero_le_one.trans hH) c)
  calc
    _ ≤ (previousFrequency J D X j^c*P.shear^c)*G.ell*ρ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbound G.ell_pos.le) hρ
    _ ≤ (previousFrequency J D X j^c*P.shear^c)*G.ell := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hρ1 (mul_nonneg hmono G.ell_pos.le)
    _ ≤ (previousFrequency J D X j^c*P.shear^c)*supportScale J X j :=
      mul_le_mul_of_nonneg_left hscale hmono
    _ = neighborError J D X (c : ℝ) j := by
      simp only [neighborError,Real.rpow_natCast,hshear]
      ring

end EulerParentPacketFrames.LabelData

end
end

end

section

/-! Fixed coefficient thresholds for the literal neighboring-label guard.
The history reciprocal is derived from the initial geometric step, and
the only parent size input is the already constructed parent's label bound. -/

@[expose] public section

noncomputable section

namespace EulerParentNeighborThreshold

open Real EulerParentNeighborCost EulerPacketSourceScaleSequence
  EulerParentHistoryFrequency

/-- Forward threshold, given by `boundConstant*4^degree`. -/
def forwardThreshold : ℝ := boundConstant*4^degree

/-- Joined threshold, given by `(boundConstant*(2*(1+CM+CH))^degree)*4^degree`. -/
def joinedThreshold (CM CH : ℝ) : ℝ :=
  (boundConstant*(2*(1+CM+CH))^degree)*4^degree

/-- Common threshold, given by `max forwardThreshold (joinedThreshold CM CH)`. -/
def commonThreshold (CM CH : ℝ) : ℝ :=
  max forwardThreshold (joinedThreshold CM CH)

/-- Required exponent, given by `80*degree+1`. -/
def requiredExponent : ℕ := 80*degree+1

theorem degree_le_requiredExponent : degree ≤ requiredExponent := by
  unfold requiredExponent
  omega

theorem forwardThreshold_le_common (CM CH : ℝ) :
    forwardThreshold ≤ commonThreshold CM CH := le_max_left _ _

theorem joinedThreshold_le_common (CM CH : ℝ) :
    joinedThreshold CM CH ≤ commonThreshold CM CH := le_max_right _ _

theorem threshold_le_previous (J D : ℕ) (hJ : 3 ≤ J) (X : ℝ) (hX : 0 ≤ X)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (B : ℝ) (hB : B ≤ X ^ D)
    (n : ℕ) : B ≤ previousFrequency J D X n :=
  hB.trans (initial_frequency_le_previous J D hJ X hX hbase n)

end EulerParentNeighborThreshold

namespace EulerParentPacketFrames.LabelData

open Set Real EulerSmoothLimit EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerParentNeighborCost EulerPacketSourceScaleSequence
  EulerPacketSourceScaleActual EulerParentNeighborThreshold EulerParentHistoryFrequency
  EulerPacketNestedHorizons EulerPacketBaseGuardScales

variable {G : Parent} (L : LabelData G)

theorem strainDifferenceCost_power :
    L.strainDifferenceCost ≤ boundConstant*(1+L.K)^degree := by
  simpa only [envelope,formula,strainDifferenceCost,mul_zero,add_zero] using
    envelope_power L.K 0 0 0 0 0 (zero_le_one.trans L.K_one)
      le_rfl le_rfl le_rfl le_rfl le_rfl

theorem strainDifferenceCost_monomial (k : ℝ) (c : ℕ)
    (hk : 1 ≤ k) (hKk : L.K ≤ k ^ 80)
    (hcost : forwardThreshold ≤ k) (hc : requiredExponent ≤ c) :
    L.strainDifferenceCost ≤ k^c := by
  have hconst := constant_pos
  have hn : degree ≤ c := degree_le_requiredExponent.trans hc
  have he : 80*degree+1 ≤ c := hc
  have hb := polynomial_le_monomial boundConstant L.K 0 0 k 1 degree 80 c
    hconst.le (zero_le_one.trans L.K_one) le_rfl le_rfl hk le_rfl hKk
    (pow_nonneg (zero_le_one.trans hk) 80) zero_le_one hcost he hn
  exact L.strainDifferenceCost_power.trans (by
    simpa only [add_zero,one_pow,mul_one] using hb)

theorem forward_neighbor_error_of_source_scales (J D : ℕ) (hJ : 3 ≤ J)
    (X ρ : ℝ) (hX : 1 ≤ X)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n c : ℕ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hKk : L.K ≤ previousFrequency J D X n ^ 80)
    (hcost : forwardThreshold ≤ previousFrequency J D X n)
    (hc : requiredExponent ≤ c) (hscale : G.ell ≤ supportScale J X n) :
    L.strainDifferenceCost*G.ell*ρ ≤ neighborError J D X (c : ℝ) n := by
  have hk := previousFrequency_one_le J D hJ X hX hbase n
  have hh : 1 ≤ previousShear J X n := by
    cases n with
    | zero => exact one_le_pow₀ hX
    | succ n =>
      apply one_le_exp
      exact div_nonneg
        ((zero_le_one.trans hX).trans
          (EulerPacketSourceParameterScales.sequence_initial_le J (by omega) X
            (zero_le_one.trans hX) n)) (by positivity)
  have hb := L.strainDifferenceCost_monomial (previousFrequency J D X n) c hk hKk hcost hc
  have hkn : 0 ≤ previousFrequency J D X n^c := pow_nonneg (zero_le_one.trans hk) c
  have hhn : 0 ≤ previousShear J X n^c := pow_nonneg (zero_le_one.trans hh) c
  have hb' : L.strainDifferenceCost ≤ previousFrequency J D X n^c*previousShear J X n^c :=
    hb.trans (le_mul_of_one_le_right hkn (one_le_pow₀ hh))
  have hprod : 0 ≤ previousFrequency J D X n^c*previousShear J X n^c := mul_nonneg hkn hhn
  calc
    _ ≤ (previousFrequency J D X n^c*previousShear J X n^c)*G.ell*ρ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb' G.ell_pos.le) hρ
    _ ≤ (previousFrequency J D X n^c*previousShear J X n^c)*G.ell := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hρ1
        (mul_nonneg hprod G.ell_pos.le)
    _ ≤ (previousFrequency J D X n^c*previousShear J X n^c)*supportScale J X n :=
      mul_le_mul_of_nonneg_left hscale hprod
    _ = neighborError J D X (c : ℝ) n := by
      simp only [neighborError,rpow_natCast]
      ring

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S) (H : LowBounds G)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (P : ParentFrame (G.transverseData m hm R S hS) τ)

theorem joined_neighbor_error_of_literal_scales
    (J D : ℕ) (hJ : 3 ≤ J) (hD : 2000 ≤ D) (X ρ CM CH : ℝ)
    (hX : 2 ≤ X) (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4))
    (a β : ℕ → ℝ) (ha₀ : 1 / 2 ≤ a 0) (ha₀₂ : a 0 ≤ 2)
    (hβ₀ : 1 / 2 ≤ β 0 * X ^ 2) (hβ₀₂ : β 0 * X ^ 2 ≤ 2)
    (n c : ℕ) (hn : 1 ≤ n) (hτliteral : τ = activationTime J X a β n)
    (hτ1 : τ ≤ 1) (hCM : 0 ≤ CM) (hCH : 0 ≤ CH)
    (ha : 1 / 2 ≤ P.a) (hH : 1 ≤ P.shear)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hshear : P.shear = previousShear J X n)
    (hKk : L.K ≤ previousFrequency J D X n ^ 80)
    (hcost : joinedThreshold CM CH ≤ previousFrequency J D X n)
    (hc : requiredExponent ≤ c) (hscale : G.ell ≤ supportScale J X n) :
    L.neighborScaleCost m hm R S hS H τ hτ hτT P CM CH*G.ell*ρ ≤
      neighborError J D X (c : ℝ) n := by
  have hx0 : 0 < X := by linarith only [hX]
  have hx1 : 1 ≤ X := by linarith only [hX]
  have hTi : τ⁻¹ ≤ 12/baseHorizon J X := by
    rw [hτliteral]
    exact reciprocal_activation_le_base J (by omega) X hx0 a β ha₀ ha₀₂ hβ₀ hβ₀₂ hn
  have hTik := base_inverse_le_previous_frequency_pow80 J D hJ hD X hX hbase n
  have hk := previousFrequency_one_le J D hJ X hx1 hbase n
  exact L.neighbor_error_of_source_scales m hm R S hS H τ hτ hτT P
    (12/baseHorizon J X) CM CH hτ1 hTi hCM hCH ha hH J D X ρ n 80 c
    hρ hρ1 hshear hk hKk hTik hcost hc (degree_le_requiredExponent.trans hc) hscale

end EulerParentPacketFrames.LabelData

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketInduction.Stage

open Set Real InnerProductSpace EulerSmoothLimit EulerParentPacketFrames
  EulerPacketSourceGeometry EulerTransversePacketProvider EulerTransverseFrameCoordinates
  EulerPacketInductionScales EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketSourceScaleActual EulerPacketBaseGuardScales EulerPacketLowConstants
  EulerPacketNormalizedPrimary EulerParentNeighborThreshold EulerParentHistoryFrequency
  EulerPacketSupport EulerPacketMovingFrame

section Joined

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} {n : ℕ} (P : Stage S n)
  (hn : n ≠ 0) (hq : requiredExponent ≤ q)
  (hB : commonThreshold gradientConstant hessianConstant ≤ B)

include hq hB in
theorem joined_neighbor :
    P.restrictedState.labels.neighborScaleCost (P.joinedNormal hn) (P.joinedNormal_unit hn)
      (LinearIsometryEquiv.refl ℝ (referencePlane (P.joinedNormal hn))) support compact
      P.restrictedLow P.time (P.time_pos hn) P.time_lt_nextHorizon (P.joinedFrame hn)
      gradientConstant hessianConstant*P.restrictedParent.ell*1 ≤
      neighborError S.J S.D S.X (q : ℝ) n := by
  have htime := base_inverse_le_previous_frequency_pow80 S.J S.D S.stage_large S.base_power
    S.X (by linarith only [S.x_large]) S.actual.initial_frequency n
  have hcost : joinedThreshold gradientConstant hessianConstant ≤ previousFrequency S.J S.D S.X n :=
    (joinedThreshold_le_common _ _).trans (hB.trans (S.previous_floor n))
  exact P.restrictedState.labels.neighbor_error_of_source_scales
    (P.joinedNormal hn) (P.joinedNormal_unit hn)
    (LinearIsometryEquiv.refl ℝ (referencePlane (P.joinedNormal hn))) support compact
    P.restrictedLow P.time (P.time_pos hn) P.time_lt_nextHorizon (P.joinedFrame hn)
    (12/baseHorizon S.J S.X) gradientConstant hessianConstant P.time_one (P.time_reciprocal hn)
    gradient_nonneg hessian_nonneg
    (by erw [P.joinedFrame_a]; exact P.coupling_bounds.1)
    (by erw [P.joinedFrame_shear,P.frame_shear]; exact S.previousShear_one n)
    S.J S.D S.X 1 n 80 q zero_le_one le_rfl ((P.joinedFrame_shear hn).trans P.frame_shear)
    (S.previousFrequency_one n)
    P.label_eq.le htime hcost hq (degree_le_requiredExponent.trans hq) P.scale_eq.le

/-- Joined guards, constructed using `P.restrictedState.labels.geometryGuardsOfStage`. -/
def joinedGuards : Guards (P.time_pos hn) P.time_lt_nextHorizon (P.joinedFrame hn) (P.joinedHistory
    hn) :=
  P.restrictedState.labels.geometryGuardsOfStage
    (P.joinedNormal hn) (P.joinedNormal_unit hn)
    (LinearIsometryEquiv.refl ℝ (referencePlane (P.joinedNormal hn))) support compact
    P.restrictedLow P.time (P.time_pos hn) P.time_lt_nextHorizon (P.joinedFrame hn)
    (fun t x => P.restrictedState.evolution.pressure (t,x))
        P.restrictedState.evolution.pressure_smooth
    (by
      intro t x
      rw [P.restrictedState.evolution.pressure_gradient]
      exact P.restrictedState.evolution.acceleration_match t x)
    S.J S.D 4 (q : ℝ) S.X (fun _ => P.frame.a) (fun _ => P.frame.sigma^2) n S.x_pos
    frameConstant frame_properties.1 P.source_stage P.coupling_bounds.1 (P.joinedFrame_a hn)
    ((P.joinedFrame_shear hn).trans P.frame_shear)
    ((P.joinedFrame_sigma hn).trans (sqrt_sq P.sigma_nonneg).symm)
    ((P.joinedFrame_horizon hn).trans P.restrictedFrame_horizon)
    ((P.joinedFrame_G hn).le.trans P.frame_bound) ((P.joinedFrame_error hn).le.trans P.frame_error)
    gradientConstant hessianConstant activationMargin 1 (spike S.J S.X n) (shear S.J S.X n)
    gradient_nonneg hessian_nonneg activationMargin_pos.le zero_le_one (S.spike_pos n).le
    (zero_le_one.trans (S.shear_one n)) (P.joined_neighbor hn hq hB)
    (P.restrictedFrame.activation_normal_choice (P.time_pos hn) P.time_lt_nextHorizon)
    (P.history_layer hn) (P.joined_history_strain hn) (P.joined_history_hessian hn)
    activationMargin_small (S.activation_small hn) (P.compression hn)

@[simp] theorem joinedGuards_radius : (P.joinedGuards hn hq hB).radius=1 := rfl
@[simp] theorem joinedGuards_y : (P.joinedGuards hn hq hB).y=(scaleSequence S.J S.X (n+1))⁻¹ := rfl
@[simp] theorem joinedGuards_delta : (P.joinedGuards hn hq hB).δ=spike S.J S.X n := rfl
@[simp] theorem joinedGuards_shear : (P.joinedGuards hn hq hB).hchild=shear S.J S.X n := rfl
@[simp] theorem joinedGuards_CM : (P.joinedGuards hn hq hB).CM=gradientConstant := rfl
@[simp] theorem joinedGuards_CH : (P.joinedGuards hn hq hB).CH=hessianConstant := rfl

theorem joined_source_neighbor :
    (P.joinedFrame hn).neighborCost (P.time_pos hn) P.time_lt_nextHorizon
      (P.joinedHistory hn) (P.joinedGuards hn hq hB).CM (P.joinedGuards hn hq hB).CH *
        (P.joinedGuards hn hq hB).radius ≤ neighborError S.J S.D S.X (q : ℝ) n := by
  have hs := P.restrictedState.labels.source_neighbor_scale
    (P.joinedNormal hn) (P.joinedNormal_unit hn)
    (LinearIsometryEquiv.refl ℝ (referencePlane (P.joinedNormal hn))) support compact
    P.restrictedLow P.time (P.time_pos hn) P.time_lt_nextHorizon (P.joinedFrame hn)
    gradientConstant hessianConstant gradient_nonneg hessian_nonneg
    (P.joinedGuards hn hq hB).shear_pos (P.joinedGuards hn hq hB).epsilon_pos
  exact (mul_le_mul_of_nonneg_right hs zero_le_one).trans (P.joined_neighbor hn hq hB)

/-- Joined geometry, given by `(P.joinedGuards hn hq hB).lowGeometry (by rw
[P.joinedGuards_radius]; norm_num)`. -/
def joinedGeometry : PhysicalGeometryData {x : Space // ‖x‖ ≤ (1/2 : ℝ)} :=
  (P.joinedGuards hn hq hB).lowGeometry (by rw [P.joinedGuards_radius]; norm_num)

theorem joinedGeometry_targetTime : (P.joinedGeometry hn hq hB).targetTime=P.nextTime := by
  change physicalTime P.time (P.joinedFrame hn).a (P.joinedFrame hn).epsilon
    (((P.joinedGuards hn hq hB).y)⁻¹/(P.joinedFrame hn).sigma)=P.nextTime
  have he : (P.joinedFrame hn).epsilon=P.frame.epsilon := by
    simp only [ParentFrame.epsilon,P.joinedFrame_a,P.joinedFrame_shear]
  rw [P.joinedGuards_y,inv_inv,P.joinedFrame_a,P.joinedFrame_sigma,he]
  exact P.physical_target_eq_nextTime

end Joined

section Forward

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} (P : Stage S 0)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)

include hq hB in
theorem forward_neighbor : P.restrictedState.labels.strainDifferenceCost*P.restrictedParent.ell*1 ≤
    neighborError S.J S.D S.X (q : ℝ) 0 :=
  P.restrictedState.labels.forward_neighbor_error_of_source_scales S.J S.D S.stage_large
    S.X 1 S.x_one S.actual.initial_frequency 0 q zero_le_one le_rfl P.label_eq.le
    ((forwardThreshold_le_common _ _).trans (hB.trans (S.previous_floor 0))) hq P.scale_eq.le

/-- Forward guards, constructed using `P.restrictedState.labels.forwardGeometryGuardsOfStage`. -/
def forwardGuards : ForwardGuards P.forwardFrame :=
  P.restrictedState.labels.forwardGeometryGuardsOfStage P.forwardNormal P.forwardNormal_unit
    (LinearIsometryEquiv.refl ℝ (referencePlane P.forwardNormal)) support compact P.forwardFrame
    S.J S.D 4 (q : ℝ) S.X (fun _ => P.frame.a) (fun _ => P.frame.sigma^2) 0
    frameConstant frame_properties.1 P.source_stage P.coupling_bounds.1 P.forwardFrame_a
    (P.forwardFrame_shear.trans P.frame_shear)
    (P.forwardFrame_sigma.trans (sqrt_sq P.sigma_nonneg).symm)
    (P.forwardFrame_horizon.trans P.restrictedFrame_horizon)
    (P.forwardFrame_G.le.trans P.frame_bound) (P.forwardFrame_error.le.trans P.frame_error)
    1 (spike S.J S.X 0) (shear S.J S.X 0) zero_le_one (S.spike_pos 0).le
    (zero_le_one.trans (S.shear_one 0)) (P.forward_neighbor hq hB) P.zeroFrame.forward_normal_choice

@[simp] theorem forwardGuards_radius : (P.forwardGuards hq hB).radius=1 := rfl
@[simp] theorem forwardGuards_y : (P.forwardGuards hq hB).y=(scaleSequence S.J S.X 1)⁻¹ := rfl
@[simp] theorem forwardGuards_delta : (P.forwardGuards hq hB).δ=spike S.J S.X 0 := rfl
@[simp] theorem forwardGuards_shear : (P.forwardGuards hq hB).hchild=shear S.J S.X 0 := rfl

theorem forward_source_neighbor :
    ‖P.forwardData.M.derivative.field‖*(P.forwardGuards hq hB).radius ≤
      neighborError S.J S.D S.X (q : ℝ) 0 := by
  have hs := P.restrictedState.labels.source_strain_derivative_norm
    P.forwardNormal P.forwardNormal_unit
    (LinearIsometryEquiv.refl ℝ (referencePlane P.forwardNormal)) support compact
  exact (mul_le_mul_of_nonneg_right hs zero_le_one).trans (P.forward_neighbor hq hB)

/-- Forward geometry, given by `(P.forwardGuards hq hB).lowGeometry (by rw
[P.forwardGuards_radius]; norm_num)`. -/
def forwardGeometry : PhysicalGeometryData {x : Space // ‖x‖ ≤ (1/2 : ℝ)} :=
  (P.forwardGuards hq hB).lowGeometry (by rw [P.forwardGuards_radius]; norm_num)

theorem forwardGeometry_targetTime : (P.forwardGeometry hq hB).targetTime=P.nextTime := by
  change physicalTime 0 P.forwardFrame.a P.forwardFrame.epsilon
    (((P.forwardGuards hq hB).y)⁻¹/P.forwardFrame.sigma)=P.nextTime
  rw [P.forwardGuards_y,inv_inv,P.forwardFrame_a,P.forwardFrame_sigma]
  have he : P.forwardFrame.epsilon=P.frame.epsilon := by
    simp only [ParentFrame.epsilon,P.forwardFrame_a,P.forwardFrame_shear]
  rw [he]
  simpa only [P.time_zero rfl] using P.physical_target_eq_nextTime

end Forward

end EulerPacketInduction.Stage
