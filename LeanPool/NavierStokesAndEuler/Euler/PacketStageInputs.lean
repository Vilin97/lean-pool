/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketStageGuards
public import LeanPool.NavierStokesAndEuler.Euler.PacketStagePhysicalBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryForwardChoice
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialInput
public import LeanPool.NavierStokesAndEuler.Euler.ParentForwardNormalParameters

@[expose] public section

/-! Actual packet inputs at every finite stage, together with the
source-only parameter cap and the chosen frequency guard. -/

noncomputable section

namespace EulerParentPacketFrames.GeometryForwardInput

open Real EulerParentInitializedRadius EulerMeanHarmonic

theorem parameterSize_one {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [CompleteSpace U] (I : GeometryForwardInput U) : 1 ≤ I.parameterSize := by
  have hL : 0 ≤ I.low.L :=
    (mul_nonneg boundaryLocalizationC1_nonneg I.low.Bc_nonneg).trans I.low.L_lower
  have hb := parameterSize_bounds I.label.K 0 I.parent.T⁻¹
    (560*I.frame.horizon^10/I.frame.epsilon) I.low.L I.geometry.δ ‖I.geometry.initialCoordinate‖
    (zero_le_one.trans I.label.K_one) le_rfl (inv_nonneg.mpr I.parent.T_pos.le)
    I.geometry.growth_constant_pos.le hL I.delta_pos (norm_nonneg _)
  exact hb.1.trans (le_add_of_nonneg_right I.geometry.child_nonneg)

end EulerParentPacketFrames.GeometryForwardInput

namespace EulerPacketInduction.Stage

open Set Real EulerSmoothLimit EulerParentPacketFrames EulerTransverseFrameCoordinates
  EulerPacketSourceGeometry EulerPacketSupport EulerPacketLowConstants
  EulerPacketInductionScales EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerParentNeighborThreshold EulerNormalPacketParameters

section Joined

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} {n : ℕ} (P : Stage S n)
  (hn : n ≠ 0) (hq : requiredExponent ≤ q)
  (hB : commonThreshold gradientConstant hessianConstant ≤ B)

def joinedInput : EulerPacketInitial.Input (referencePlane (P.joinedNormal hn)) where
  parent := P.restrictedParent
  label := P.restrictedState.labels
  low := P.restrictedLow
  normal := P.joinedNormal hn
  normal_unit := P.joinedNormal_unit hn
  coordinates := LinearIsometryEquiv.refl ℝ (referencePlane (P.joinedNormal hn))
  support := support
  support_compact := compact
  historyTime := P.time
  history_pos := P.time_pos hn
  history_lt := P.time_lt_nextHorizon
  total_le_one := P.nextHorizon_one
  frame := P.joinedFrame hn
  geometry := P.joinedGuards hn hq hB
  halfBall := by rw [P.joinedGuards_radius]; norm_num
  neighborhood := Metric.ball 0 (1/2 : ℝ)
  neighborhood_measurable := Metric.isOpen_ball.measurableSet
  neighborhood_open := Metric.isOpen_ball
  support_subset := subset_halfBall
  neighborhood_bound := fun x hx => le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using
    hx)
  terminal := (P.joinedGuards hn hq hB).terminal
  cutoff_support := subset_rfl
  delta_pos := by rw [P.joinedGuards_delta]; exact S.spike_pos n
  delta_le_one := by rw [P.joinedGuards_delta]; exact S.spike_one n
  child_pos := by rw [P.joinedGuards_shear]; exact zero_lt_one.trans_le (S.shear_one n)

@[simp] theorem joinedInput_parent : (P.joinedInput hn hq hB).parent=P.restrictedParent := rfl
@[simp] theorem joinedInput_label : (P.joinedInput hn hq hB).label=P.restrictedState.labels := rfl
@[simp] theorem joinedInput_low : (P.joinedInput hn hq hB).low=P.restrictedLow := rfl
@[simp] theorem joinedInput_frame : (P.joinedInput hn hq hB).frame=P.joinedFrame hn := rfl
@[simp] theorem joinedInput_geometry : (P.joinedInput hn hq hB).geometry=P.joinedGuards hn hq hB :=
  rfl
@[simp] theorem joinedInput_terminal :
    (P.joinedInput hn hq hB).terminal=(P.joinedGuards hn hq hB).terminal := rfl

theorem joinedInput_parameterSize : (P.joinedInput hn hq hB).parameterSize ≤ envelope S.J 4 S.X n :=
  P.restrictedState.labels.normalParameterSize_bound P.restrictedLow
    (P.joinedNormal hn) (P.joinedNormal_unit hn)
    (LinearIsometryEquiv.refl ℝ (referencePlane (P.joinedNormal hn))) support compact
    P.time (P.time_pos hn) P.time_lt_nextHorizon (P.joinedFrame hn) (P.joinedGuards hn hq hB)
    S.J S.D (by have h := S.stage_large; omega) 4 S.X (by norm_num) S.x_one n
    P.time⁻¹ P.restrictedParent.T⁻¹ S.actual.initial_shear S.actual.initial_frequency P.label_eq.le
    (P.time_reciprocal hn) P.restricted_horizon_reciprocal P.core_cap P.boundary_eq rfl rfl
    (((P.joinedFrame_horizon hn).trans P.restrictedFrame_horizon).le.trans
      P.source_stage.horizon_le_Theta)
    (P.joinedGuards_delta hn hq hB) (P.joinedGuards_shear hn hq hB)
    ((P.joinedFrame_shear hn).trans P.frame_shear)

theorem joinedInput_frequency : (P.joinedInput hn hq hB).frequencyGuard (frequency S.J S.X n) :=
  S.source_frequency n _ (P.joinedInput hn hq hB).parameterSize_one
    (P.joinedInput_parameterSize hn hq hB)

theorem joinedInput_targetTime :
    ((P.joinedInput hn hq hB).geometry.lowGeometry (P.joinedInput hn hq
      hB).halfBall).targetTime=P.nextTime :=
  P.joinedGeometry_targetTime hn hq hB

theorem joinedInput_sigma_bound :
    (P.joinedInput hn hq hB).frame.sigma*scaleSequence S.J S.X n ≤ 2 := by
  change (P.joinedFrame hn).sigma*scaleSequence S.J S.X n ≤ 2
  rw [P.joinedFrame_sigma]
  exact P.normalized_sigma

theorem joinedInput_scale : (P.joinedInput hn hq hB).parent.ell=supportScale S.J S.X n := P.scale_eq

end Joined

section Forward

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} (P : Stage S 0)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)

def forwardInput : GeometryForwardInput (referencePlane P.forwardNormal) where
  parent := P.restrictedParent
  label := P.restrictedState.labels
  low := P.restrictedLow
  normal := P.forwardNormal
  normal_unit := P.forwardNormal_unit
  coordinates := LinearIsometryEquiv.refl ℝ (referencePlane P.forwardNormal)
  support := support
  support_compact := compact
  total_le_one := P.nextHorizon_one
  frame := P.forwardFrame
  geometry := P.forwardGuards hq hB
  halfBall := by rw [P.forwardGuards_radius]; norm_num
  neighborhood := Metric.ball 0 (1/2 : ℝ)
  neighborhood_measurable := Metric.isOpen_ball.measurableSet
  neighborhood_open := Metric.isOpen_ball
  support_subset := subset_halfBall
  neighborhood_bound := fun x hx => le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using
    hx)
  cutoff_support := subset_rfl
  delta_pos := by rw [P.forwardGuards_delta]; exact S.spike_pos 0
  delta_le_one := by rw [P.forwardGuards_delta]; exact S.spike_one 0
  child_pos := by rw [P.forwardGuards_shear]; exact zero_lt_one.trans_le (S.shear_one 0)

@[simp] theorem forwardInput_parent : (P.forwardInput hq hB).parent=P.restrictedParent := rfl
@[simp] theorem forwardInput_label : (P.forwardInput hq hB).label=P.restrictedState.labels := rfl
@[simp] theorem forwardInput_low : (P.forwardInput hq hB).low=P.restrictedLow := rfl
@[simp] theorem forwardInput_frame : (P.forwardInput hq hB).frame=P.forwardFrame := rfl
@[simp] theorem forwardInput_geometry : (P.forwardInput hq hB).geometry=P.forwardGuards hq hB := rfl

theorem forwardInput_parameterSize : (P.forwardInput hq hB).parameterSize ≤ envelope S.J 4 S.X 0 :=
  P.restrictedState.labels.forwardNormalParameterSize_bound P.restrictedLow
    P.forwardNormal P.forwardNormal_unit
    (LinearIsometryEquiv.refl ℝ (referencePlane P.forwardNormal)) support compact
    P.forwardFrame (P.forwardGuards hq hB) S.J S.D (by have h := S.stage_large; omega)
    4 S.X (by norm_num) S.x_one 0 P.restrictedParent.T⁻¹
    S.actual.initial_shear S.actual.initial_frequency P.label_eq.le P.restricted_horizon_reciprocal
    P.core_cap P.boundary_eq
    ((P.forwardFrame_horizon.trans P.restrictedFrame_horizon).le.trans
      P.source_stage.horizon_le_Theta)
    (P.forwardGuards_delta hq hB) (P.forwardGuards_shear hq hB)
    (P.forwardFrame_shear.trans P.frame_shear)

theorem forwardInput_frequency : (P.forwardInput hq hB).frequencyGuard (frequency S.J S.X 0) :=
  S.source_frequency 0 _ (P.forwardInput hq hB).parameterSize_one (P.forwardInput_parameterSize hq
    hB)

theorem forwardInput_targetTime :
    ((P.forwardInput hq hB).geometry.lowGeometry (P.forwardInput hq
      hB).halfBall).targetTime=P.nextTime :=
  P.forwardGeometry_targetTime hq hB

theorem forwardInput_sigma_bound : (P.forwardInput hq hB).frame.sigma*scaleSequence S.J S.X 0 ≤ 2
  := by
  change P.forwardFrame.sigma*scaleSequence S.J S.X 0 ≤ 2
  rw [P.forwardFrame_sigma]
  exact P.normalized_sigma

theorem forwardInput_scale : (P.forwardInput hq hB).parent.ell=supportScale S.J S.X 0 := P.scale_eq

end Forward

end EulerPacketInduction.Stage
