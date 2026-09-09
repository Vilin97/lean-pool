/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketStageRestriction
public import LeanPool.NavierStokesAndEuler.Euler.ParentStageDirection
import LeanPool.NavierStokesAndEuler.Euler.PacketInductionScaleBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceParameterScales

/-! The actual next packet geometry is constructed from the current
finite stage. Source normals, history bounds and the neighboring-label
guards are derived from its state and the one fixed scale choice. -/

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
