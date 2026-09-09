/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketStageGeometry
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryLowBounds

@[expose] public section

/-! Literal forward and joined source guards for the next packet of an
actual finite stage. The radius is one, the spike and target shear are
the prescribed source scales, and the physical target is nextTime. -/

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
      (P.joinedHistory hn) (P.joinedGuards hn hq hB).CM (P.joinedGuards hn hq hB).CH*
        (P.joinedGuards hn hq hB).radius ≤ neighborError S.J S.D S.X (q : ℝ) n := by
  have hs := P.restrictedState.labels.source_neighbor_scale
    (P.joinedNormal hn) (P.joinedNormal_unit hn)
    (LinearIsometryEquiv.refl ℝ (referencePlane (P.joinedNormal hn))) support compact
    P.restrictedLow P.time (P.time_pos hn) P.time_lt_nextHorizon (P.joinedFrame hn)
    gradientConstant hessianConstant gradient_nonneg hessian_nonneg
    (P.joinedGuards hn hq hB).shear_pos (P.joinedGuards hn hq hB).epsilon_pos
  exact (mul_le_mul_of_nonneg_right hs zero_le_one).trans (P.joined_neighbor hn hq hB)

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
