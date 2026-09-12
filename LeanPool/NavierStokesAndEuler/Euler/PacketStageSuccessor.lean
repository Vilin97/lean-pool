/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Code4me2
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketStageRestriction
public import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalParameters
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageGuards
import LeanPool.NavierStokesAndEuler.Euler.PacketStageLowPropagation
import LeanPool.NavierStokesAndEuler.Euler.PacketInductionScaleBounds
import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalScaleApplication

/-! # The successor step, written once

The forward step (stage `0`, no history) and the joined step (positive
history) build stage `n + 1` from stage `n` by the same assembly. They differ in
the analytic pipeline that constructs the packet and in the ratio, `earlyRatio`
or `badRatio`, by which its guards measure the source error. `Step` records
what either pipeline delivers, phrased against the scale sequences, and `next`
is the one assembly of the `Stage` invariant from it. `PacketForwardSuccessor`
and `PacketInfiniteConstruction` instantiate `Step`; nothing below reads a guard.

Adapted from Code4me2/NavierStokesAndEuler, commit
`26e896edbdbe1215c0d50ddba24b2b6453646f5f`, `Euler/PacketStageSuccessor.lean`.
-/

public section

noncomputable section

namespace EulerPacketInduction.Stage

open Set Finset Real InnerProductSpace EulerSmoothLimit EulerParentPacketFrames
  EulerBaseDatum EulerPacketBaseGuardScales
  EulerPacketSourceGeometry EulerPacketNormalizedPrimary EulerPacketMovingFrame
  EulerPacketInductionScales EulerPacketLowConstants EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual EulerPacketPressureScale
  EulerParentRenewalScale EulerPacketGeometryLowBounds EulerMeanHarmonic

variable {c B : ℝ} {S : Scales c B} {n : ℕ} (P : Stage S n)

local notation "k" => frequency S.J S.X n

/-- The initial-gradient increment of the next packet, `h·r` for its target
shear `h` and error ratio `r` plus the frequency error, fits the stage's
`initialIncrement` budget once its bad-pressure cost does. -/
theorem initial_cost_of_bad_cost (h r : ℝ) (hh : 0 ≤ h) (hr : 0 ≤ r)
    (hbad : 2 * (gradientConstant * previousShear S.J S.X n) * h * r ≤
      badCost S.J 4 gradientConstant gradientConstant hessianConstant 80
        (scaleSequence S.J S.X) n) :
    h * r + (frequency S.J S.X n) ^ (-(1 / 4 : ℝ)) ≤ initialIncrement S.J S.X n := by
  have hm : 1 ≤ 2 * (gradientConstant * previousShear S.J S.X n) := by
    have h := mul_le_mul_of_nonneg_left (S.previousShear_one n) gradient_nonneg
    nlinarith only [gradient_properties.1, h]
  have hproduct : h * r ≤ 2 * (gradientConstant * previousShear S.J S.X n) * h * r := by
    simpa only [one_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right hm (mul_nonneg hh hr)
  exact add_le_add (hproduct.trans hbad) le_rfl

/-- The coercivity guard of the next parent's low bounds, from the packet's
budgets: `h` is the packet's target shear, `d` its spike and `r` its error
ratio. The parent's cumulative bounds absorb the increments (`next_localized`). -/
theorem successor_smallness (h d r : ℝ) (hh : 0 ≤ h) (hd : 0 ≤ d) (hr : 0 ≤ r)
    (hinit : h * r + k ^ (-(1 / 4 : ℝ)) ≤ initialIncrement S.J S.X n)
    (hpress : 2 * (gradientConstant * previousShear S.J S.X n) * h * (d * goodRatio + r) +
      k ^ (-(1 / 4 : ℝ)) ≤
      pressureIncrement S.J S.X n) :
    (P.restrictedLow.K +
      2 * (gradientConstant * previousShear S.J S.X n) * h * (d * goodRatio + r) +
          k ^ (-(1 / 4 : ℝ))) * (P.nextHorizon ^ 2 / 2) +
        (P.restrictedLow.Be + (h * r + k ^ (-(1 / 4 : ℝ)))) * P.nextHorizon +
        boundaryLocalizationC2 * (P.restrictedLow.Bc + (h * r + k ^ (-(1 / 4 : ℝ)))) *
          P.restrictedLow.r ^ 3 * P.nextHorizon ≤ 1 / 2 := by
  have he : 0 ≤ k ^ (-(1 / 4 : ℝ)) := rpow_nonneg (S.normal_frequency n).pos.le _
  have hc := P.next_localized P.nextHorizon (h * r + k ^ (-(1 / 4 : ℝ)))
    (2 * (gradientConstant * previousShear S.J S.X n) * h * (d * goodRatio + r) +
      k ^ (-(1 / 4 : ℝ)))
    P.nextHorizon_pos.le P.nextHorizon_le_base (by positivity [hh, hr])
    (by positivity [gradient_nonneg, S.previousShear_one n, hh, hd, goodRatio_pos, hr]) hinit hpress
  rw [restrictedLow_pressure, restrictedLow_exterior, restrictedLow_core, restrictedLow_radius]
  convert hc using 1; ring

/-- What one chosen packet delivers to the successor assembly at stage `n`.

The scalars `targetShear`, `spikeAmplitude`, `errorRatio` are the packet's target shear, spike and
error ratio as its guards name them. `targetShear_eq` identifies the shear with the
scale sequence; the ratio is `earlyRatio` in the forward step and `badRatio`
in the joined step. The rest is what the packet choice
produces on the restricted parent: the new parent and state (`parent_horizon`,
`parent_scale`, `label_eq`), the parent's low bounds updated by the packet's
error terms (`low_*`), the whole-horizon physical bounds, the pressure
budgets that the scale choice makes summable, and the renewed frame matched
to the packet's `lowGeometry` at its target time `nextTime`. -/
structure Step where
  /-- The parent particle map carrying the new packet. -/
  parent : Parent
  /-- The Euler state constructed on the new parent. -/
  state : SmoothState parent
  /-- The target shear of the packet. -/
  targetShear : ℝ
  /-- The spike amplitude appearing in the pressure increment. -/
  spikeAmplitude : ℝ
  /-- The error ratio of the selected packet pipeline. -/
  errorRatio : ℝ
  /-- The error ratio is nonnegative. -/
  errorRatio_nonneg : 0 ≤ errorRatio
  /-- The target shear agrees with the next prescribed shear level. -/
  targetShear_eq : targetShear = shear S.J S.X n
  /-- The child uses the shortened horizon of the current stage. -/
  parent_horizon : parent.T = P.nextHorizon
  /-- The child uses the next prescribed support scale. -/
  parent_scale : parent.ell = supportScale S.J S.X (n + 1)
  /-- The child labels obey the next frequency bound. -/
  label_eq : state.labels.K = k ^ 80
  /-- The updated source bounds of the new parent. -/
  low : LowBounds parent
  /-- The exterior source bound increases by the initial-gradient error. -/
  low_exterior : low.Be = P.low.Be + (targetShear * errorRatio + k ^ (-(1 / 4 : ℝ)))
  /-- The core source bound increases by the same initial-gradient error. -/
  low_core : low.Bc = P.low.Bc + (targetShear * errorRatio + k ^ (-(1 / 4 : ℝ)))
  /-- The curvature bound includes the packet pressure error. -/
  low_pressure : low.K = P.low.K + 2 * (gradientConstant * previousShear S.J S.X n) * targetShear *
    (spikeAmplitude * goodRatio + errorRatio) + k ^ (-(1 / 4 : ℝ))
  /-- The localization length is determined by the updated core bound. -/
  low_boundary : low.L = boundaryLocalizationC1 * low.Bc + 1
  /-- The source core keeps the current radius. -/
  low_radius : low.r = P.low.r
  /-- The new velocity gradient and pressure Hessian satisfy the packet estimates. -/
  physical_bounds : ∀ (t : Icc (0 : ℝ) parent.T) x,
    ‖fderiv ℝ (fun y => state.evolution.velocity (t, y)) x‖ ≤
        gradientConstant * previousShear S.J S.X n + targetShear * (goodRatio + errorRatio) +
          k ^ (-(1 / 4 : ℝ)) ∧
      ‖fderiv ℝ (state.evolution.force t) x‖ ≤
        hessianConstant * previousShear S.J S.X n * olderShear S.J S.X n +
          2 * (gradientConstant * previousShear S.J S.X n) * targetShear *
            (goodRatio + errorRatio) + k ^ (-(1 / 4 : ℝ))
  /-- The ratio-dependent pressure error fits the bad-cost budget. -/
  bad_cost : 2 * (gradientConstant * previousShear S.J S.X n) * targetShear * errorRatio ≤
    badCost S.J 4 gradientConstant gradientConstant hessianConstant 80 (scaleSequence S.J S.X) n
  /-- The complete pressure error fits the summable pressure budget. -/
  pressure_cost : 2 * (gradientConstant * previousShear S.J S.X n) * targetShear *
    (spikeAmplitude * goodRatio + errorRatio) + k ^ (-(1 / 4 : ℝ)) ≤ pressureIncrement S.J S.X n
  /-- The physical geometry to which the renewed frame is matched. -/
  geometry : PhysicalGeometryData {x : Space // ‖x‖ ≤ (1 / 2 : ℝ)}
  /-- The geometric target time is the next activation time. -/
  geometry_targetTime : geometry.targetTime = P.nextTime
  /-- The geometry uses the current frame coupling. -/
  geometry_coupling : geometry.a = P.frame.a
  /-- The geometric tilt scale agrees with the next scale level. -/
  geometry_y : geometry.y = (scaleSequence S.J S.X (n + 1))⁻¹
  /-- The geometric spike is positive, as required for shear renewal. -/
  geometry_delta_pos : 0 < geometry.δ
  /-- The geometric target shear is the packet shear. -/
  geometry_shear : geometry.hchild = targetShear
  /-- Coupling and tilt errors fit the common summable renewal budget. -/
  renewal_errors : geometry.couplingError ≤ renewalCost S.J S.D 4 c frameConstant S.X n ∧
    geometry.tiltError ≤ renewalCost S.J S.D 4 c frameConstant S.X n
  /-- The renewed frame on the new parent at the geometric target time. -/
  renewal : ParentFrame (frameData parent) geometry.targetTime
  /-- The renewed frame satisfies the selected geometry. -/
  renewal_matches : RenewalAtTarget geometry renewal
  /-- The renewed background is controlled by the current shear level. -/
  renewal_G : renewal.G = frameConstant * (1 + previousShear S.J S.X n)
  /-- The renewed remainder is the inverse fourth root of the frequency. -/
  renewal_error : renewal.error = k ^ (-(1 / 4 : ℝ))

/-- The selected error ratio fits the next global gradient and Hessian bounds. -/
theorem Step.absorbed_bounds (D : P.Step) :
    gradientConstant * previousShear S.J S.X n + shear S.J S.X n * (goodRatio + D.errorRatio) +
        k ^ (-(1 / 4 : ℝ)) ≤ gradientConstant * shear S.J S.X n ∧
      hessianConstant * previousShear S.J S.X n * olderShear S.J S.X n +
        2 * gradientConstant * previousShear S.J S.X n * shear S.J S.X n *
          (goodRatio + D.errorRatio) + k ^ (-(1 / 4 : ℝ)) ≤
        hessianConstant * shear S.J S.X n * previousShear S.J S.X n := by
  apply ratio_absorption D.errorRatio D.errorRatio_nonneg
  simpa only [D.targetShear_eq, mul_assoc] using D.bad_cost

/-- Renewal preserves the prescribed coupling and tilt budgets. -/
theorem Step.renewal_parameters (D : P.Step) :
    |D.renewal.a / P.frame.a - 1| ≤ renewalCost S.J S.D 4 c frameConstant S.X n ∧
      1 / 2 ≤ D.renewal.sigma ^ 2 * (scaleSequence S.J S.X (n + 1)) ^ 2 ∧
      D.renewal.sigma ^ 2 * (scaleSequence S.J S.X (n + 1)) ^ 2 ≤ 2 := by
  have h := literal_step D.renewal_matches S.J S.X n S.renewal_series (by norm_num)
    D.renewal_errors D.geometry_y
  simpa only [D.geometry_coupling] using h

/-- One initial-gradient increment extends both cumulative source bounds. -/
theorem Step.initial_bounds (D : P.Step) :
    D.low.Be ≤ initialCoefficientCost + ∑ i ∈ range (n + 1), initialIncrement S.J S.X i ∧
      D.low.Bc ≤ gradientConstant * S.X ^ 1000 +
        ∑ i ∈ range (n + 1), initialIncrement S.J S.X i := by
  have h := initial_cost_of_bad_cost D.targetShear D.errorRatio
    (by rw [D.targetShear_eq]; exact zero_le_one.trans (S.shear_one n))
    D.errorRatio_nonneg D.bad_cost
  rw [D.low_exterior, D.low_core]
  exact P.initial_step_bound _ h

/-- One pressure increment extends the cumulative curvature bound. -/
theorem Step.pressure_bound (D : P.Step) :
    D.low.K ≤ initialCoefficientCost + literalInitialPressureCost S.D S.X +
      ∑ i ∈ range (n + 1), pressureIncrement S.J S.X i := by
  rw [D.low_pressure, add_assoc]
  exact P.pressure_step_bound _ D.pressure_cost

/-- The renewed coupling lies in the next cumulative error budget. -/
theorem Step.coupling_bound (D : P.Step) :
    |D.renewal.a - 1| ≤ 2 * ∑ i ∈ range (n + 1),
      renewalCost S.J S.D 4 c frameConstant S.X i :=
  P.coupling_step _ D.renewal_parameters.1

/-- The renewed background compresses with the next stage's remainder margin. -/
theorem Step.background_compression (D : P.Step) :
    ⟪D.renewal.B P.nextTime (unit (D.renewal.m P.nextTime)),
      unit (D.renewal.m P.nextTime)⟫_ℝ + priorError S.J S.D S.X (n + 1) < 0 := by
  have h := D.renewal_matches.background_compression_of_error_le_one
    (priorError S.J S.D S.X (n + 1)) (S.priorError_one (n + 1))
  simpa only [← D.geometry_targetTime] using h

/-- Assemble the successor from the packet bounds and renewed frame. The analytic
estimates are opaque theorems; the supplied parent, state, low bounds and frame
remain available by reduction. -/
@[expose] def next (D : P.Step) : Stage S (n + 1) where
  parent := D.parent
  state := D.state
  low := D.low
  time := P.nextTime
  time_nonneg := P.nextTime_pos.le
  time_zero := fun h => by omega
  time_lower := fun _ => P.nextTime_lower
  horizon_eq := D.parent_horizon
  horizon_le := by rw [D.parent_horizon]; exact P.nextHorizon_le_base
  scale_eq := D.parent_scale
  label_eq := D.label_eq
  gradient_bound := by
    intro t x
    refine (D.physical_bounds t x).1.trans ?_
    rw [D.targetShear_eq]
    exact D.absorbed_bounds.1
  hessian_bound := by
    intro t x
    refine (D.physical_bounds t x).2.trans ?_
    rw [D.targetShear_eq]
    change _ ≤ hessianConstant * shear S.J S.X n * previousShear S.J S.X n
    simpa only [mul_assoc] using D.absorbed_bounds.2
  exterior_bound := D.initial_bounds.1
  core_bound := D.initial_bounds.2
  pressure_bound := D.pressure_bound
  boundary_eq := D.low_boundary
  radius_eq := D.low_radius.trans P.radius_eq
  frame := D.renewal.changeActivation D.geometry_targetTime
  frame_shear := by
    rw [ParentFrame.changeActivation_shear, D.renewal_matches.shear_eq D.geometry_delta_pos,
      D.geometry_shear]
    exact D.targetShear_eq
  frame_bound := by rw [ParentFrame.changeActivation_G, D.renewal_G]; exact le_rfl
  frame_error := by rw [ParentFrame.changeActivation_error, D.renewal_error]; exact le_rfl
  coupling_error := by rw [ParentFrame.changeActivation_a]; exact D.coupling_bound
  tilt_lower := by rw [ParentFrame.changeActivation_sigma]; exact D.renewal_parameters.2.1
  tilt_upper := by rw [ParentFrame.changeActivation_sigma]; exact D.renewal_parameters.2.2
  compression := by
    intro _
    rw [ParentFrame.changeActivation_B, ParentFrame.changeActivation_m]
    exact D.background_compression

/-- The successor uses the parent supplied by the packet step. -/
@[simp] theorem next_parent (D : P.Step) : (P.next D).parent = D.parent := rfl

/-- The successor uses the Euler state supplied by the packet step. -/
@[simp] theorem next_state (D : P.Step) : (P.next D).state = D.state := rfl

/-- The successor uses the updated source bounds supplied by the packet step. -/
@[simp] theorem next_low (D : P.Step) : (P.next D).low = D.low := rfl

/-- The successor activates at the current stage's next packet time. -/
@[simp] theorem next_time (D : P.Step) : (P.next D).time = P.nextTime := rfl

/-- The successor uses the renewed frame, reindexed to the next activation time. -/
@[simp] theorem next_frame (D : P.Step) :
    (P.next D).frame = D.renewal.changeActivation D.geometry_targetTime := rfl

end EulerPacketInduction.Stage
