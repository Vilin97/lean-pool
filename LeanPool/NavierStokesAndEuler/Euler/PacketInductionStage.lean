/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionScales
import LeanPool.NavierStokesAndEuler.Euler.PacketInductionScaleBounds
import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalPrefix

/-!
# The packet stage invariant

`GrowthData` contains the Euler state, activation time and strain decomposition used to
prove gradient growth. `Stage` adds the source bounds and frame guards needed to construct
the next packet. Separating them lets the growth theorem apply without assuming the
successor construction's hypotheses. All cumulative bounds use only earlier indices.
-/

public section


noncomputable section

namespace EulerPacketInduction

open Set Finset Real InnerProductSpace EulerSmoothLimit EulerParentPacketFrames
  EulerBaseDatum EulerPacketSupport EulerPacketSourceGeometry EulerPacketNormalizedPrimary
  EulerPacketLowConstants EulerPacketInductionScales EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual EulerPacketBaseGuardScales
  EulerParentRenewalScale EulerMeanHarmonic

/-- The transverse packet data of a parent in the fixed reference plane: its
frame, inverse frame and strain along the centre trajectory, against which a
stage's `ParentFrame` is measured. -/
@[expose] def frameData (A : Parent) : EulerTransversePacketProvider.Data FirstPlane :=
  A.transverseData firstNormal firstNormal_unit firstFrame support compact

/-- The state, activation and strain bounds used by the growth argument. The common
horizon and Sobolev realisation also support comparison with other Euler evolutions.
These data impose no hypotheses on a successor packet. -/
structure GrowthData {c B : ℝ} (S : Scales c B) (n : ℕ) where
  /-- The parent: the volume-preserving particle map, with its velocity and
  acceleration, that carries the current Euler state on `[0, parent.T]`. Its
  frame, strain and curvature are the coefficients every estimate reads. -/
  parent : Parent
  /-- The current Euler solution on the parent: a pointwise classical
  `Evolution`, its Sobolev realisation `regularity` (converted to an ordinary
  evolution by the contradiction), its label bounds, and its odd symmetry, which
  makes the strain at the origin equal to the velocity gradient there
  (`strain_origin`). -/
  state : SmoothState parent
  /-- The activation time of the most recently added packet (`0` at the base
  stage). The divergent quantity `activationGradient` is the velocity gradient
  at `(time, 0)`. -/
  time : ℝ
  /-- The activation time is a time of the stage solution. -/
  time_nonneg : 0 ≤ time
  /-- The stage solution lives exactly `2·timeWidth n` beyond the activation.
  This gives `time < parent.T`, so the activation is an interior time, and it
  lets the next stage's horizon nest strictly inside this one. -/
  horizon_eq : parent.T=time+2*timeWidth S.J S.X n
  /-- Every stage horizon lies inside the base horizon, so all stage solutions
  can be compared with one hypothetical evolution on `[0, baseHorizon]`. -/
  horizon_le : parent.T ≤ baseHorizon S.J S.X
  /-- The frame of the parent strain along the centre trajectory at the
  activation time: background `B`, ray `m`, velocity `v`, shear coefficient,
  and the bounds `G` on `B` and `error` on the remainder. -/
  frame : ParentFrame (frameData parent) time
  /-- The leading rank-one part of the strain at the centre has shear
  `previousShear n`, the target shear of the latest packet. This is the term
  the growth argument isolates. -/
  frame_shear : frame.shear=previousShear S.J S.X n
  /-- The background `B` is bounded one shear level lower, by
  `frameConstant·(1 + olderShear n)`, so that the leading term dominates it. -/
  frame_bound : frame.G ≤ frameConstant*(1+olderShear S.J S.X n)
  /-- The remainder after `B` and the rank-one shear are removed is at most
  `priorError n`, an inverse fourth root of the previous frequency, which is
  negligible against the leading shear. -/
  frame_error : frame.error ≤ priorError S.J S.D S.X n

/-- A full packet stage, including the induction hypotheses needed by the successor
construction. `Stage.toGrowthData` retains only the state, activation and frame bounds
needed for gradient growth. The full record keeps its original projection interface. -/
structure Stage {c B : ℝ} (S : Scales c B) (n : ℕ) where
  /-- The parent: the volume-preserving particle map, with its velocity and
  acceleration, that carries the current Euler state on `[0, parent.T]`. Its
  frame, strain and curvature are the coefficients every estimate reads. -/
  parent : Parent
  /-- The current Euler solution on the parent: a pointwise classical
  `Evolution`, its Sobolev realisation `regularity` (converted to an ordinary
  evolution by the contradiction), its label bounds, and its odd symmetry, which
  makes the strain at the origin equal to the velocity gradient there
  (`strain_origin`). -/
  state : SmoothState parent
  /-- The low-frequency source bounds of the parent: exterior and core lower
  bounds `Be`, `Bc` on the initial strain, the curvature bound `K`, the
  localization length `L` and the core radius `r`. They feed the coercivity
  guard `small` of the next parent. -/
  low : LowBounds parent
  /-- The activation time of the most recently added packet (`0` at the base
  stage). The divergent quantity `activationGradient` is the velocity gradient
  at `(time, 0)`. -/
  time : ℝ
  /-- The activation time is a time of the stage solution. -/
  time_nonneg : 0 ≤ time
  /-- The base stage is activated at time `0`; the forward step poses its
  packet there. -/
  time_zero : n=0 → time=0
  /-- After the first step the activation time is at least a twelfth of the
  base horizon. This bounds `time⁻¹`, and through it the history terms of the
  joined step (`history_layer`). -/
  time_lower : n ≠ 0 → baseHorizon S.J S.X/12 ≤ time
  /-- The stage solution lives exactly `2·timeWidth n` beyond the activation.
  This gives `time < parent.T`, so the activation is an interior time, and it
  lets the next stage's horizon nest strictly inside this one. -/
  horizon_eq : parent.T=time+2*timeWidth S.J S.X n
  /-- Every stage horizon lies inside the base horizon, so all stage solutions
  can be compared with one hypothetical evolution on `[0, baseHorizon]`. -/
  horizon_le : parent.T ≤ baseHorizon S.J S.X
  /-- The parent's scale is `supportScale n`: the next increment is supported
  in a ball of radius half this scale. -/
  scale_eq : parent.ell=supportScale S.J S.X n
  /-- The label constant of the state (the Sobolev size of the parent's
  displacement, velocity and acceleration) is `previousFrequency n ^ 80`; the
  next packet's frequency guard must dominate it. -/
  label_eq : state.labels.K=(previousFrequency S.J S.D S.X n)^80
  /-- The velocity gradient is bounded on the whole horizon by
  `gradientConstant·previousShear n`: the upper bound matching the lower bound
  at the centre, consumed by the next step's low bounds and history data. -/
  gradient_bound : ∀ (t : Icc (0 : ℝ) parent.T) x,
    ‖fderiv ℝ (fun y => state.evolution.velocity (t,y)) x‖ ≤
      gradientConstant*previousShear S.J S.X n
  /-- The pressure Hessian (the gradient of the force) is bounded by
  `hessianConstant·previousShear n·olderShear n`. -/
  hessian_bound : ∀ (t : Icc (0 : ℝ) parent.T) x,
    ‖fderiv ℝ (state.evolution.force t) x‖ ≤
      hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n
  /-- Cumulative bound on the exterior strain constant: the base cost plus the
  summable per-stage increments of the scale choice. -/
  exterior_bound : low.Be ≤ initialCoefficientCost+∑ i ∈ range n, initialIncrement S.J S.X i
  /-- Cumulative bound on the core strain constant, starting from the base
  shear `X^1000`. -/
  core_bound : low.Bc ≤ gradientConstant*S.X^1000+∑ i ∈ range n, initialIncrement S.J S.X i
  /-- Cumulative bound on the curvature constant, starting from the base
  pressure cost. Together with the two bounds above it keeps the coercivity
  guard `small` true at every stage. -/
  pressure_bound : low.K ≤ initialCoefficientCost+literalInitialPressureCost S.D S.X +
    ∑ i ∈ range n, pressureIncrement S.J S.X i
  /-- The localization length is determined by the core bound. -/
  boundary_eq : low.L=boundaryLocalizationC1*low.Bc+1
  /-- The core radius is the base radius `X^(-1000)` at every stage. -/
  radius_eq : low.r=baseRadius S.X
  /-- The frame of the parent strain along the centre trajectory at the
  activation time: background `B`, ray `m`, velocity `v`, shear coefficient,
  and the bounds `G` on `B` and `error` on the remainder. -/
  frame : ParentFrame (frameData parent) time
  /-- The leading rank-one part of the strain at the centre has shear
  `previousShear n`, the target shear of the latest packet. This is the term
  the growth argument isolates. -/
  frame_shear : frame.shear=previousShear S.J S.X n
  /-- The background `B` is bounded one shear level lower, by
  `frameConstant·(1 + olderShear n)`, so that the leading term dominates it. -/
  frame_bound : frame.G ≤ frameConstant*(1+olderShear S.J S.X n)
  /-- The remainder after `B` and the rank-one shear are removed is at most
  `priorError n`, an inverse fourth root of the previous frequency, which is
  negligible against the leading shear. -/
  frame_error : frame.error ≤ priorError S.J S.D S.X n
  /-- The normalised coupling `a = ⟨m̂, B v̂⟩` stays within a summable distance
  of `1`; each renewal moves it by at most `renewalCost i`. This gives
  `1/2 ≤ a ≤ 2` (`coupling_bounds`). -/
  coupling_error : |frame.a-1| ≤ 2*∑ i ∈ range n, renewalCost S.J S.D 4 c frameConstant S.X i
  /-- The normalised tilt `σ² = ⟨m̂ × v̂, B v̂⟩/a` is at least `1/(2 x_n²)`. -/
  tilt_lower : 1/2 ≤ frame.sigma^2*(scaleSequence S.J S.X n)^2
  /-- The normalised tilt is at most `2/x_n²`: the renewed frame is nearly
  untilted, at the scale of the sequence. -/
  tilt_upper : frame.sigma^2*(scaleSequence S.J S.X n)^2 ≤ 2
  /-- After the first step the background strain compresses along the ray with
  a margin exceeding `priorError n`. Since `m' = -Bᵀm`, this makes `‖m‖`, and
  with it the shear `c‖m‖‖v‖` of the next packet, grow; the joined guards take
  it as input and the renewal re-establishes it. -/
  compression : n ≠ 0 →
    ⟪frame.B time (unit (frame.m time)),unit (frame.m time)⟫_ℝ+priorError S.J S.D S.X n < 0

namespace GrowthData

variable {c B : ℝ} {S : Scales c B} {n : ℕ} (P : GrowthData S n)

/-- The positive post-activation time width puts activation inside the horizon. -/
theorem time_lt : P.time < P.parent.T := by
  rw [P.horizon_eq]
  exact lt_add_of_pos_right _ (mul_pos (by norm_num) (timeWidth_pos S.J S.j_one S.x_pos n))

/-- The common base horizon bounds every activation time by one. -/
theorem time_one : P.time ≤ 1 := P.time_lt.le.trans (P.horizon_le.trans S.time_small)

end GrowthData

namespace Stage

variable {c B : ℝ} {S : Scales c B} {n : ℕ} (P : Stage S n)

/-- Forget the source bounds and frame guards that only the successor construction needs. -/
@[expose] def toGrowthData : GrowthData S n where
  parent := P.parent
  state := P.state
  time := P.time
  time_nonneg := P.time_nonneg
  horizon_eq := P.horizon_eq
  horizon_le := P.horizon_le
  frame := P.frame
  frame_shear := P.frame_shear
  frame_bound := P.frame_bound
  frame_error := P.frame_error

theorem coupling_bounds : 1/2 ≤ P.frame.a ∧ P.frame.a ≤ 2 :=
  EulerParentRenewalPrefix.bounds_of_accumulated_error S.renewal_series le_rfl n P.coupling_error

theorem coupling_pos : 0 < P.frame.a := by linarith only [P.coupling_bounds.1]

theorem sigma_nonneg : 0 ≤ P.frame.sigma := sqrt_nonneg _

theorem sigma_pos : 0 < P.frame.sigma := by
  by_contra h
  have hz := le_antisymm (le_of_not_gt h) P.sigma_nonneg
  have ht := P.tilt_lower
  rw [hz,zero_pow (by decide : 2 ≠ 0),zero_mul] at ht
  norm_num at ht

/-- The activation time is strictly inside the stage horizon. -/
theorem time_lt : P.time < P.parent.T := P.toGrowthData.time_lt

/-- Every activation occurs before time one. -/
theorem time_one : P.time ≤ 1 := P.toGrowthData.time_one

theorem horizon_lower : baseHorizon S.J S.X/12 < P.parent.T := by
  by_cases hn : n=0
  · have ht := P.time_zero hn
    have heq : P.parent.T=baseHorizon S.J S.X := by
      rw [P.horizon_eq,ht,zero_add,hn,← baseHorizon_eq_timeWidth S.J S.x_pos]
    rw [heq]
    have hp := baseHorizon_pos S.J S.j_one S.x_pos
    linarith only [hp]
  · exact (P.time_lower hn).trans_lt P.time_lt

theorem horizon_reciprocal : P.parent.T⁻¹ ≤ 12/baseHorizon S.J S.X := by
  have hp := div_pos (baseHorizon_pos S.J S.j_one S.x_pos) (by norm_num : (0 : ℝ) < 12)
  have h := one_div_le_one_div_of_le hp P.horizon_lower.le
  simpa only [one_div,inv_div] using h

theorem time_pos (hn : n ≠ 0) : 0 < P.time :=
  (div_pos (baseHorizon_pos S.J S.j_one S.x_pos) (by norm_num)).trans_le (P.time_lower hn)

theorem time_reciprocal (hn : n ≠ 0) : P.time⁻¹ ≤ 12/baseHorizon S.J S.X := by
  have hp := div_pos (baseHorizon_pos S.J S.j_one S.x_pos) (by norm_num : (0 : ℝ) < 12)
  have h := one_div_le_one_div_of_le hp (P.time_lower hn)
  simpa only [one_div,inv_div] using h

theorem exterior_cap : P.low.Be ≤ initialCoefficientCost+1 := by
  have h := P.exterior_bound
  have hs := S.initial_partial_sum n
  have hd := S.delta_small
  linarith only [h,hs,hd]

theorem core_cap : P.low.Bc ≤ gradientConstant*S.X^1000+2 := by
  have h := P.core_bound
  have hs := S.initial_partial_sum n
  have hd := S.delta_small
  linarith only [h,hs,hd]

theorem pressure_cap : P.low.K ≤ initialCoefficientCost+1 := by
  have h := P.pressure_bound
  have hs := S.pressure_partial_sum n
  have hd := S.delta_small
  have hb := S.first.pressure_small
  linarith only [h,hs,hd,hb]

theorem source_stage : EulerPacketSourceScaleGuards.StageGuards S.J S.D 4 c S.X
    geometryConstant (fun _ => P.frame.a) (fun _ => P.frame.sigma^2) n :=
  S.stage _ _ n P.coupling_bounds.1 P.coupling_bounds.2 P.tilt_lower P.tilt_upper

theorem normalized_sigma : P.frame.sigma*scaleSequence S.J S.X n ≤ 2 := by
  have h := P.tilt_upper
  have hx := S.sequence_one n
  have hp := mul_nonneg P.sigma_nonneg (zero_le_one.trans hx)
  nlinarith only [h,hp,sq_nonneg (P.frame.sigma*scaleSequence S.J S.X n-1)]

theorem strain_bound (t : Icc (0 : ℝ) P.parent.T) (x : Space) :
    ‖P.parent.strain.field t x‖ ≤ gradientConstant*previousShear S.J S.X n := by
  rw [P.state.evolution.strain_eq]
  exact P.gradient_bound _ _

theorem curvature_bound (t : Icc (0 : ℝ) P.parent.T) (x : Space) :
    ‖P.parent.curvature.field t x‖ ≤
      hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n := by
  rw [P.state.evolution.curvature_eq]
  exact P.hessian_bound _ _

end Stage
end EulerPacketInduction
