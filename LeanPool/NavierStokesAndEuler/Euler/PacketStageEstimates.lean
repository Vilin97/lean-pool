/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketStageGuards
import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryPressureCosts
import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalScaleApplication

/-! The actual stage guards satisfy the fixed pressure, initial-gradient
and frame-renewal budgets used by the induction. -/

@[expose] public section


noncomputable section

namespace EulerPacketInduction.Stage

open Set Real EulerSmoothLimit EulerParentPacketFrames EulerPacketSourceGeometry
  EulerTransverseFrameCoordinates EulerPacketInductionScales EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual EulerPacketSourceScales
  EulerPacketLowConstants EulerPacketPressureScale EulerPacketGeometryLowBounds
  EulerParentRenewalScale EulerParentNeighborThreshold EulerPacketSupport

section Joined

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} {n : ℕ} (P : Stage S n)
  (hn : n ≠ 0) (hq : requiredExponent ≤ q)
  (hB : commonThreshold gradientConstant hessianConstant ≤ B)

local notation "G" => P.joinedGuards hn hq hB
local notation "R" => LinearIsometryEquiv.refl ℝ (referencePlane (P.joinedNormal hn))

theorem joined_horizon_bound :
    (P.joinedFrame hn).horizon ≤ sourceTheta S.J 4 (scaleSequence S.J S.X) n := by
  rw [P.joinedFrame_horizon,P.restrictedFrame_horizon]
  exact P.source_stage.horizon_le_Theta

include hn in
theorem history_inverse_shear : P.time⁻¹ ≤ previousShear S.J S.X n := by
  rw [← one_div]
  exact (div_le_iff₀ (P.time_pos hn)).mpr (P.history_layer hn)

theorem joined_bad_cost :
    2*(gradientConstant*previousShear S.J S.X n)*(G).hchild*(G).badRatio ≤
      badCost S.J 4 gradientConstant gradientConstant hessianConstant 80 (scaleSequence S.J S.X) n
          :=
  P.restrictedState.labels.joined_bad_pressure_cost_bound (P.joinedNormal hn) (P.joinedNormal_unit
      hn)
    R support compact P.restrictedLow P.time (P.time_pos hn) P.time_lt_nextHorizon (P.joinedFrame
        hn)
    G P.time⁻¹ P.time_one le_rfl S.J S.D S.stage_large S.X 4 gradientConstant gradientConstant
    hessianConstant 80 S.x_one (by
        norm_num) gradient_nonneg gradient_nonneg hessian_nonneg (by norm_num)
    S.actual.initial_shear S.actual.initial_frequency n (gradientConstant*previousShear S.J S.X n)
    (by
        rw [rpow_ofNat]; exact P.label_eq.le) (P.history_inverse_shear hn) (P.joinedGuards_CM hn hq
            hB).le
    (P.joinedGuards_CH hn hq hB).le (P.joined_horizon_bound hn)
    (by
        erw [P.joinedFrame_sigma]; exact P.normalized_sigma) (P.joinedGuards_shear hn hq hB).le
            le_rfl

theorem joined_initial_cost :
    (G).hchild*(G).badRatio+(frequency S.J S.X n)^(-(1/4 : ℝ)) ≤ initialIncrement S.J S.X n := by
  have hb := P.joined_bad_cost hn hq hB
  have hm : 1 ≤ 2*(gradientConstant*previousShear S.J S.X n) := by
    have h := mul_le_mul_of_nonneg_left (S.previousShear_one n) gradient_nonneg
    nlinarith only [gradient_properties.1,h]
  have hn0 := mul_nonneg (G).child_nonneg (G).badRatio_nonneg
  have hh := mul_le_mul_of_nonneg_right hm hn0
  unfold initialIncrement
  nlinarith only [hb,hh]

theorem joined_pressure_cost :
    2*(gradientConstant*previousShear S.J S.X n)*(G).hchild*((G).δ*goodRatio+(G).badRatio) +
      (frequency S.J S.X n)^(-(1/4 : ℝ)) ≤ pressureIncrement S.J S.X n := by
  have h := P.restrictedState.labels.joined_upper_pressure_cost_bound
    (P.joinedNormal hn) (P.joinedNormal_unit hn) R support compact P.restrictedLow P.time
    (P.time_pos hn) P.time_lt_nextHorizon (P.joinedFrame hn) G P.time⁻¹ P.time_one le_rfl
    S.J S.D S.stage_large S.X 4 gradientConstant gradientConstant hessianConstant 80 S.x_one
    (by norm_num) gradient_nonneg gradient_nonneg hessian_nonneg (by norm_num)
    S.actual.initial_shear S.actual.initial_frequency n (gradientConstant*previousShear S.J S.X n)
    (by
        rw [rpow_ofNat]; exact P.label_eq.le) (P.history_inverse_shear hn) (P.joinedGuards_CM hn hq
            hB).le
    (P.joinedGuards_CH hn hq hB).le (P.joined_horizon_bound hn)
    (by erw [P.joinedFrame_sigma]; exact P.normalized_sigma)
    (P.joinedGuards_shear hn hq hB).le le_rfl (P.joinedGuards_delta hn hq hB).le
  unfold pressureIncrement initialIncrement
  exact (add_le_add h (le_refl ((frequency S.J S.X n)^(-(1/4 : ℝ))))).trans_eq
    (add_assoc _ _ _)

theorem joined_renewal_errors :
    (P.joinedGeometry hn hq hB).couplingError ≤ renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X n ∧
    (P.joinedGeometry hn hq hB).tiltError ≤ renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X n := by
  exact (G).renewal_errors_on_scales (by change (1/2 : ℝ) ≤ 1; norm_num)
    S.J S.D (by have h := S.stage_large; omega) 4 (q : ℝ) frameConstant S.X P.frame.a
    (by norm_num) frame_properties.1 S.x_one P.coupling_bounds.2 n (P.joinedFrame_a hn)
    ((P.joinedFrame_shear hn).trans P.frame_shear) (P.joined_horizon_bound hn)
    ((P.joinedFrame_G hn).le.trans P.frame_bound) ((P.joinedFrame_error hn).le.trans P.frame_error)
    (P.joined_source_neighbor hn hq hB) (P.joinedGuards_y hn hq hB)
    (by erw [P.joinedFrame_sigma]; exact P.tilt_upper)

end Joined

section Forward

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} (P : Stage S 0)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)

local notation "G" => P.forwardGuards hq hB

theorem forward_horizon_bound : P.forwardFrame.horizon ≤ sourceTheta S.J 4 (scaleSequence S.J S.X)
    0 := by
  rw [P.forwardFrame_horizon,P.restrictedFrame_horizon]
  exact P.source_stage.horizon_le_Theta

theorem forward_bad_cost :
    2*(gradientConstant*previousShear S.J S.X 0)*(G).hchild*(G).earlyRatio ≤
      badCost S.J 4 gradientConstant gradientConstant hessianConstant 80 (scaleSequence S.J S.X) 0
          := by
  apply (G).bad_pressure_cost_bound S.J S.stage_large S.X 4 gradientConstant gradientConstant
    hessianConstant 80 S.x_one (by
        norm_num) gradient_nonneg gradient_nonneg hessian_nonneg (by norm_num)
    S.actual.initial_shear 0 (gradientConstant*previousShear S.J S.X 0) P.forward_horizon_bound
    _ le_rfl le_rfl
  rw [P.forwardFrame_sigma]
  exact P.normalized_sigma

theorem forward_initial_cost :
    (G).hchild*(G).earlyRatio+(frequency S.J S.X 0)^(-(1/4 : ℝ)) ≤ initialIncrement S.J S.X 0 := by
  have hb := P.forward_bad_cost hq hB
  have hm : 1 ≤ 2*(gradientConstant*previousShear S.J S.X 0) := by
    have h := mul_le_mul_of_nonneg_left (S.previousShear_one 0) gradient_nonneg
    nlinarith only [gradient_properties.1,h]
  have hn0 := mul_nonneg (G).child_nonneg (G).earlyRatio_nonneg
  have hh := mul_le_mul_of_nonneg_right hm hn0
  unfold initialIncrement
  nlinarith only [hb,hh]

theorem forward_pressure_cost :
    2*(gradientConstant*previousShear S.J S.X 0)*(G).hchild*((G).δ*goodRatio+(G).earlyRatio) +
      (frequency S.J S.X 0)^(-(1/4 : ℝ)) ≤ pressureIncrement S.J S.X 0 := by
  have h := (G).upper_pressure_cost_bound S.J S.stage_large S.X 4 gradientConstant gradientConstant
    hessianConstant 80 S.x_one (by
        norm_num) gradient_nonneg gradient_nonneg hessian_nonneg (by norm_num)
    S.actual.initial_shear 0 (gradientConstant*previousShear S.J S.X 0) P.forward_horizon_bound
    (by rw [P.forwardFrame_sigma]; exact P.normalized_sigma) le_rfl le_rfl le_rfl
  unfold pressureIncrement initialIncrement
  linarith only [h]

theorem forward_renewal_errors :
    (P.forwardGeometry hq hB).couplingError ≤ renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X 0 ∧
    (P.forwardGeometry hq hB).tiltError ≤ renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X 0 := by
  exact (G).renewal_errors_on_scales (by change (1/2 : ℝ) ≤ 1; norm_num)
    S.J S.D (by have h := S.stage_large; omega) 4 (q : ℝ) frameConstant S.X P.frame.a
    (by norm_num) frame_properties.1 S.x_one P.coupling_bounds.2 0 P.forwardFrame_a
    (P.forwardFrame_shear.trans P.frame_shear) P.forward_horizon_bound
    (P.forwardFrame_G.le.trans P.frame_bound) (P.forwardFrame_error.le.trans P.frame_error)
    (P.forward_source_neighbor hq hB) rfl (by rw [P.forwardFrame_sigma]; exact P.tilt_upper)

end Forward
end EulerPacketInduction.Stage
