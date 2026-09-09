/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionStage

@[expose] public section

/-! The next literal activation and horizon are constructed from the
current actual frame. Restriction preserves the actual Euler state,
low bounds and frame before the next packet is added. -/

noncomputable section

namespace EulerPacketInduction.Stage

open Set Real EulerSmoothLimit EulerParentPacketFrames EulerPacketSourceGeometry
  EulerPacketInductionScales EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketNestedHorizons EulerPacketBaseGuardScales EulerPacketScaleGeometry
  EulerPacketMovingFrame EulerTimeIntervalRestriction

variable {c B : ℝ} {S : Scales c B} {n : ℕ} (P : Stage S n)

def step : ℝ :=
  stepLength S.J S.X (fun _ => P.frame.a) (fun _ => P.frame.sigma^2) n

def nextTime : ℝ := P.time+P.step

def nextHorizon : ℝ := P.nextTime+2*timeWidth S.J S.X (n+1)

theorem step_bounds : timeWidth S.J S.X n/6 ≤ P.step ∧
    P.step ≤ 2*timeWidth S.J S.X n/3 :=
  activation_time_bounds P.coupling_bounds.1 P.coupling_bounds.2
    (previousShear_pos S.J S.x_pos n) (zero_lt_one.trans_le (S.sequence_one n))
    (zero_le_one.trans (S.sequence_one (n+1))) P.tilt_lower P.tilt_upper

theorem step_pos : 0 < P.step :=
  (div_pos (timeWidth_pos S.J S.j_one S.x_pos n) (by norm_num)).trans_le P.step_bounds.1

theorem time_lt_nextTime : P.time < P.nextTime := lt_add_of_pos_right _ P.step_pos

theorem nextTime_pos : 0 < P.nextTime := P.time_nonneg.trans_lt P.time_lt_nextTime

theorem nextTime_lt_nextHorizon : P.nextTime < P.nextHorizon :=
  lt_add_of_pos_right _ (mul_pos (by norm_num) (timeWidth_pos S.J S.j_one S.x_pos (n+1)))

theorem time_lt_nextHorizon : P.time < P.nextHorizon :=
  P.time_lt_nextTime.trans P.nextTime_lt_nextHorizon

theorem nextHorizon_pos : 0 < P.nextHorizon :=
  P.nextTime_pos.trans P.nextTime_lt_nextHorizon

theorem nextHorizon_lt : P.nextHorizon < P.parent.T := by
  have hstep := P.step_bounds.2
  have hwidth := P.source_stage.next_width
  have hpos := timeWidth_pos S.J S.j_one S.x_pos n
  rw [P.horizon_eq]
  dsimp only [nextHorizon,nextTime]
  linarith only [hstep,hwidth,hpos]

theorem nextHorizon_le : P.nextHorizon ≤ P.parent.T := P.nextHorizon_lt.le

theorem nextHorizon_le_base : P.nextHorizon ≤ baseHorizon S.J S.X :=
  P.nextHorizon_le.trans P.horizon_le

theorem nextHorizon_one : P.nextHorizon ≤ 1 := P.nextHorizon_le_base.trans S.time_small

theorem nextTime_lower : baseHorizon S.J S.X/12 ≤ P.nextTime := by
  by_cases hn : n=0
  · subst n
    have ht := P.time_zero rfl
    have hs := P.step_bounds.1
    rw [baseHorizon_eq_timeWidth S.J S.x_pos]
    dsimp only [nextTime]
    linarith only [ht,hs]
  · exact (P.time_lower hn).trans P.time_lt_nextTime.le

theorem nextHorizon_common : baseHorizon S.J S.X/12 < P.nextHorizon :=
  P.nextTime_lower.trans_lt P.nextTime_lt_nextHorizon

theorem physical_target_eq_nextTime :
    physicalTime P.time P.frame.a P.frame.epsilon
      (scaleSequence S.J S.X (n+1)/P.frame.sigma)=P.nextTime := by
  exact P.frame.target_on_scales S.J S.X (fun _ => P.frame.a) (fun _ => P.frame.sigma^2) n
    P.coupling_pos.le (sq_nonneg _) rfl P.frame_shear
    (sqrt_sq P.sigma_nonneg).symm

def restrictedParent : Parent :=
  P.parent.restrictTime P.nextHorizon P.nextHorizon_pos P.nextHorizon_le

def restrictedState : SmoothState P.restrictedParent :=
  P.state.restrictTime P.nextHorizon P.nextHorizon_pos P.nextHorizon_le

def restrictedLow : LowBounds P.restrictedParent :=
  P.low.restrictTime P.nextHorizon P.nextHorizon_pos P.nextHorizon_le

def restrictedFrame : ParentFrame (frameData P.restrictedParent) P.time :=
  P.frame.restrictTime P.nextHorizon P.nextHorizon_pos P.nextHorizon_le P.time_nonneg

@[simp] theorem restrictedParent_time : P.restrictedParent.T=P.nextHorizon := rfl
@[simp] theorem restrictedParent_scale : P.restrictedParent.ell=P.parent.ell := rfl
@[simp] theorem restrictedState_label : P.restrictedState.labels.K=P.state.labels.K := rfl
@[simp] theorem restrictedLow_exterior : P.restrictedLow.Be=P.low.Be := rfl
@[simp] theorem restrictedLow_core : P.restrictedLow.Bc=P.low.Bc := rfl
@[simp] theorem restrictedLow_pressure : P.restrictedLow.K=P.low.K := rfl
@[simp] theorem restrictedLow_boundary : P.restrictedLow.L=P.low.L := rfl
@[simp] theorem restrictedLow_radius : P.restrictedLow.r=P.low.r := rfl
@[simp] theorem restrictedFrame_a : P.restrictedFrame.a=P.frame.a := rfl
@[simp] theorem restrictedFrame_sigma : P.restrictedFrame.sigma=P.frame.sigma := rfl
@[simp] theorem restrictedFrame_shear : P.restrictedFrame.shear=P.frame.shear := rfl
@[simp] theorem restrictedFrame_G : P.restrictedFrame.G=P.frame.G := rfl
@[simp] theorem restrictedFrame_error : P.restrictedFrame.error=P.frame.error := rfl
@[simp] theorem restrictedFrame_B : P.restrictedFrame.B=P.frame.B := rfl
@[simp] theorem restrictedFrame_m : P.restrictedFrame.m=P.frame.m := rfl
@[simp] theorem restrictedFrame_v : P.restrictedFrame.v=P.frame.v := rfl

theorem restrictedFrame_horizon :
    P.restrictedFrame.horizon=EulerPacketSourceScaleGuards.horizon S.J S.X
      P.frame.a (P.frame.sigma^2) n :=
  P.frame.restricted_horizon_on_scales S.J S.X S.x_pos
    (fun _ => P.frame.a) (fun _ => P.frame.sigma^2) n P.coupling_pos
    (sq_pos_of_pos P.sigma_pos) rfl P.frame_shear
    P.nextHorizon P.nextHorizon_pos P.nextHorizon_le P.time_nonneg rfl

theorem restricted_strain_bound (t : Icc (0 : ℝ) P.restrictedParent.T) (x : Space) :
    ‖P.restrictedParent.strain.field t x‖ ≤
      EulerPacketLowConstants.gradientConstant*previousShear S.J S.X n := by
  rw [show P.restrictedParent.strain.field t x=P.parent.strain.field
    (initialInclusion P.parent.T P.nextHorizon P.nextHorizon_le t) x from
      P.parent.restrictTime_strain P.nextHorizon P.nextHorizon_pos P.nextHorizon_le t x]
  exact P.strain_bound _ _

theorem restricted_curvature_bound (t : Icc (0 : ℝ) P.restrictedParent.T) (x : Space) :
    ‖P.restrictedParent.curvature.field t x‖ ≤
      EulerPacketLowConstants.hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n := by
  rw [show P.restrictedParent.curvature.field t x=P.parent.curvature.field
    (initialInclusion P.parent.T P.nextHorizon P.nextHorizon_le t) x from
      P.parent.restrictTime_curvature P.nextHorizon P.nextHorizon_pos P.nextHorizon_le t x]
  exact P.curvature_bound _ _

end EulerPacketInduction.Stage
