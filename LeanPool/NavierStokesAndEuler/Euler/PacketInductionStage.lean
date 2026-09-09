/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionScaleBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentStageHorizon
public import LeanPool.NavierStokesAndEuler.Euler.ParentStageDirection
public import LeanPool.NavierStokesAndEuler.Euler.BaseFirstPacketFrame

@[expose] public section

/-! The invariant for a finite, actually constructed packet stage.
All fields refer to its genuine Euler state, source guards and frame.
The cumulative bounds use only earlier indices. -/

noncomputable section

namespace EulerPacketInduction

open Set Finset Real InnerProductSpace EulerSmoothLimit EulerParentPacketFrames
  EulerBaseDatum EulerPacketSupport EulerPacketSourceGeometry EulerPacketNormalizedPrimary
  EulerPacketLowConstants EulerPacketInductionScales EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual EulerPacketBaseGuardScales
  EulerParentRenewalScale EulerMeanHarmonic

def frameData (A : Parent) : EulerTransversePacketProvider.Data FirstPlane :=
  A.transverseData firstNormal firstNormal_unit firstFrame support compact

structure Stage {c B : ℝ} (S : Scales c B) (n : ℕ) where
  parent : Parent
  state : SmoothState parent
  low : LowBounds parent
  time : ℝ
  time_nonneg : 0 ≤ time
  time_zero : n=0 → time=0
  time_lower : n ≠ 0 → baseHorizon S.J S.X/12 ≤ time
  horizon_eq : parent.T=time+2*timeWidth S.J S.X n
  horizon_le : parent.T ≤ baseHorizon S.J S.X
  scale_eq : parent.ell=supportScale S.J S.X n
  label_eq : state.labels.K=(previousFrequency S.J S.D S.X n)^80
  gradient_bound : ∀ (t : Icc (0 : ℝ) parent.T) x,
    ‖fderiv ℝ (fun y => state.evolution.velocity (t,y)) x‖ ≤
      gradientConstant*previousShear S.J S.X n
  hessian_bound : ∀ (t : Icc (0 : ℝ) parent.T) x,
    ‖fderiv ℝ (state.evolution.force t) x‖ ≤
      hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n
  exterior_bound : low.Be ≤ initialCoefficientCost+∑ i ∈ range n, initialIncrement S.J S.X i
  core_bound : low.Bc ≤ gradientConstant*S.X^1000+∑ i ∈ range n, initialIncrement S.J S.X i
  pressure_bound : low.K ≤ initialCoefficientCost+literalInitialPressureCost S.D S.X+
    ∑ i ∈ range n, pressureIncrement S.J S.X i
  boundary_eq : low.L=boundaryLocalizationC1*low.Bc+1
  radius_eq : low.r=baseRadius S.X
  frame : ParentFrame (frameData parent) time
  frame_shear : frame.shear=previousShear S.J S.X n
  frame_bound : frame.G ≤ frameConstant*(1+olderShear S.J S.X n)
  frame_error : frame.error ≤ priorError S.J S.D S.X n
  coupling_error : |frame.a-1| ≤ 2*∑ i ∈ range n, renewalCost S.J S.D 4 c frameConstant S.X i
  tilt_lower : 1/2 ≤ frame.sigma^2*(scaleSequence S.J S.X n)^2
  tilt_upper : frame.sigma^2*(scaleSequence S.J S.X n)^2 ≤ 2
  compression : n ≠ 0 →
    ⟪frame.B time (unit (frame.m time)),unit (frame.m time)⟫_ℝ+priorError S.J S.D S.X n < 0

namespace Stage

variable {c B : ℝ} {S : Scales c B} {n : ℕ} (P : Stage S n)

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

theorem time_lt : P.time < P.parent.T := by
  rw [P.horizon_eq]
  exact lt_add_of_pos_right _ (mul_pos (by norm_num) (timeWidth_pos S.J S.j_one S.x_pos n))

theorem time_one : P.time ≤ 1 := P.time_lt.le.trans (P.horizon_le.trans S.time_small)

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
