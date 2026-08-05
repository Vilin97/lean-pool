/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DelaunayChart
import LeanPool.PoincareThreeBody.KeplerHamiltonian
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The unperturbed Hamiltonian flow in lifted Delaunay variables

The lifted Delaunay chart evolves by advancing the mean anomaly at rate `I₁⁻³` and decreasing the
rotating periapsis angle at unit speed.  Here we verify directly that this curve satisfies all four
Hamilton equations for the mass-zero rotating Kepler Hamiltonian.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- Mean anomaly along a general lifted Delaunay flow line. -/
noncomputable def liftedDelaunayMeanAnomalyAlongFlow
    (firstAction meanAnomaly time : ℝ) : ℝ :=
  meanAnomaly + time / firstAction ^ 3

/-- Eccentric anomaly along a general lifted Delaunay flow line. -/
noncomputable def liftedDelaunayEccentricAnomalyAlongFlow
    (firstAction eccentricity meanAnomaly time : ℝ) : ℝ :=
  eccentricAnomaly eccentricity
    (liftedDelaunayMeanAnomalyAlongFlow firstAction meanAnomaly time)

@[simp] lemma liftedDelaunayEccentricAnomaly_flow_argument
    (firstAction eccentricity meanAnomaly time : ℝ) :
    liftedDelaunayEccentricAnomaly eccentricity
        (meanAnomaly + time / firstAction ^ 3) =
      liftedDelaunayEccentricAnomalyAlongFlow
        firstAction eccentricity meanAnomaly time := rfl

theorem hasDerivAt_liftedDelaunayMeanAnomalyAlongFlow
    (firstAction meanAnomaly time : ℝ) :
    HasDerivAt (liftedDelaunayMeanAnomalyAlongFlow firstAction meanAnomaly)
      (1 / firstAction ^ 3) time := by
  have hraw := (hasDerivAt_const time meanAnomaly).add
    ((hasDerivAt_id time).div_const (firstAction ^ 3))
  apply (hraw.congr_deriv (by ring)).congr_of_eventuallyEq
  filter_upwards [] with argument
  rfl

theorem hasDerivAt_liftedDelaunayEccentricAnomalyAlongFlow
    {firstAction eccentricity meanAnomaly time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    HasDerivAt
      (liftedDelaunayEccentricAnomalyAlongFlow firstAction eccentricity meanAnomaly)
      ((1 / firstAction ^ 3) /
        (1 - eccentricity * Real.cos
          (liftedDelaunayEccentricAnomalyAlongFlow firstAction eccentricity meanAnomaly time)))
      time := by
  have h := (hasDerivAt_eccentricAnomaly heccentricity heccentricityOne).comp time
    (hasDerivAt_liftedDelaunayMeanAnomalyAlongFlow firstAction meanAnomaly time)
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards [] with argument
    rfl
  · simp [liftedDelaunayEccentricAnomalyAlongFlow, div_eq_mul_inv, mul_comm]

/-- The position coordinates of a general Delaunay flow line satisfy the first two Hamilton
equations. -/
theorem hasDerivAt_liftedDelaunayFlowLine_position
    {firstAction eccentricity meanAnomaly periapsisAngle time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    HasDerivAt
        (fun t ↦ liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle t 0)
        (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 2 +
          liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 1) time ∧
      HasDerivAt
        (fun t ↦ liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle t 1)
        (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 3 -
          liftedDelaunayFlowLine firstAction eccentricity meanAnomaly
            periapsisAngle time 0) time := by
  let anomaly : ℝ → ℝ :=
    liftedDelaunayEccentricAnomalyAlongFlow firstAction eccentricity meanAnomaly
  let denominator : ℝ → ℝ := fun t ↦ 1 - eccentricity * Real.cos (anomaly t)
  let meanMotion : ℝ := 1 / firstAction ^ 3
  let xInertial : ℝ → ℝ := fun t ↦
    firstAction ^ 2 * (Real.cos (anomaly t) - eccentricity)
  let yInertial : ℝ → ℝ := fun t ↦
    firstAction ^ 2 * Real.sqrt (1 - eccentricity ^ 2) * Real.sin (anomaly t)
  let vxInertial : ℝ → ℝ := fun t ↦
    -firstAction ^ 2 * meanMotion * Real.sin (anomaly t) / denominator t
  let vyInertial : ℝ → ℝ := fun t ↦
    firstAction ^ 2 * meanMotion * Real.sqrt (1 - eccentricity ^ 2) *
      Real.cos (anomaly t) / denominator t
  let angle : ℝ → ℝ := fun t ↦ t - periapsisAngle
  have hdenominator : denominator time ≠ 0 :=
    (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne).ne'
  have hanomaly : HasDerivAt anomaly (meanMotion / denominator time) time := by
    simpa [anomaly, meanMotion, denominator] using
      (hasDerivAt_liftedDelaunayEccentricAnomalyAlongFlow
        (firstAction := firstAction) (meanAnomaly := meanAnomaly)
        heccentricity heccentricityOne)
  have hxInertial : HasDerivAt xInertial (vxInertial time) time := by
    have hraw := ((Real.hasDerivAt_cos (anomaly time)).comp time hanomaly
      |>.sub_const eccentricity).const_mul (firstAction ^ 2)
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      dsimp [xInertial]
    · dsimp [vxInertial, denominator]
      field_simp [hdenominator]
  have hyInertial : HasDerivAt yInertial (vyInertial time) time := by
    have hraw := ((Real.hasDerivAt_sin (anomaly time)).comp time hanomaly).const_mul
      (firstAction ^ 2 * Real.sqrt (1 - eccentricity ^ 2))
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      dsimp [yInertial]
    · dsimp [vyInertial, denominator]
      field_simp [hdenominator]
  have hangle : HasDerivAt angle 1 time := by
    simpa [angle] using (hasDerivAt_id time).sub_const periapsisAngle
  have hcos := (Real.hasDerivAt_cos (angle time)).comp time hangle
  have hsin := (Real.hasDerivAt_sin (angle time)).comp time hangle
  constructor
  · have hraw := (hcos.mul hxInertial).add (hsin.mul hyInertial)
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      simp only [liftedDelaunayFlowLine, liftedDelaunayPhasePoint,
        liftedDelaunayPosition, liftedDelaunayMomentum,
        liftedDelaunayEccentricAnomaly_flow_argument,
        positionMomentumPhasePoint, positionInRotatingFrame, inertialEllipsePosition,
        inertialEllipseVelocity, Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, anomaly, angle]
      congr 3 <;> ring
    · simp only [liftedDelaunayFlowLine, liftedDelaunayPhasePoint,
        liftedDelaunayPosition, liftedDelaunayMomentum,
        liftedDelaunayEccentricAnomaly_flow_argument,
        positionMomentumPhasePoint, positionInRotatingFrame, inertialEllipsePosition,
        inertialEllipseVelocity, Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, vxInertial, vyInertial, denominator,
        anomaly, angle, meanMotion]
      ring
  · have hraw := (hsin.neg.mul hxInertial).add (hcos.mul hyInertial)
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      simp only [liftedDelaunayFlowLine, liftedDelaunayPhasePoint,
        liftedDelaunayPosition, liftedDelaunayMomentum,
        liftedDelaunayEccentricAnomaly_flow_argument,
        positionMomentumPhasePoint, positionInRotatingFrame, inertialEllipsePosition,
        inertialEllipseVelocity, Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, anomaly, angle]
      congr 3 <;> ring
    · simp only [liftedDelaunayFlowLine, liftedDelaunayPhasePoint,
        liftedDelaunayPosition, liftedDelaunayMomentum,
        liftedDelaunayEccentricAnomaly_flow_argument,
        positionMomentumPhasePoint, positionInRotatingFrame, inertialEllipsePosition,
        inertialEllipseVelocity, Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, vxInertial, vyInertial, denominator,
        anomaly, angle, meanMotion]
      ring

/-- In inertial coordinates, a general Delaunay ellipse satisfies the inverse-square acceleration
law. -/
theorem hasDerivAt_inertialEllipseVelocity_liftedDelaunayFlow
    {firstAction eccentricity meanAnomaly time : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (coordinate : Fin 2) :
    HasDerivAt
      (fun t ↦ inertialEllipseVelocity firstAction eccentricity (1 / firstAction ^ 3)
        (liftedDelaunayEccentricAnomalyAlongFlow
          firstAction eccentricity meanAnomaly t) coordinate)
      (-inertialEllipsePosition firstAction eccentricity
          (liftedDelaunayEccentricAnomalyAlongFlow
            firstAction eccentricity meanAnomaly time) coordinate /
        eccentricRadius firstAction eccentricity
          (liftedDelaunayEccentricAnomalyAlongFlow
            firstAction eccentricity meanAnomaly time) ^ 3) time := by
  let meanMotion : ℝ := 1 / firstAction ^ 3
  let anomaly : ℝ → ℝ :=
    liftedDelaunayEccentricAnomalyAlongFlow firstAction eccentricity meanAnomaly
  let denominator : ℝ → ℝ := fun t ↦ 1 - eccentricity * Real.cos (anomaly t)
  have hdenominator : denominator time ≠ 0 :=
    (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne).ne'
  have hanomaly : HasDerivAt anomaly (meanMotion / denominator time) time := by
    simpa [anomaly, meanMotion, denominator] using
      (hasDerivAt_liftedDelaunayEccentricAnomalyAlongFlow
        (firstAction := firstAction) (meanAnomaly := meanAnomaly)
        heccentricity heccentricityOne)
  have hsin := (Real.hasDerivAt_sin (anomaly time)).comp time hanomaly
  have hcos := (Real.hasDerivAt_cos (anomaly time)).comp time hanomaly
  have hdenominatorDeriv : HasDerivAt denominator
      (eccentricity * Real.sin (anomaly time) * (meanMotion / denominator time)) time := by
    have hraw := (hasDerivAt_const time 1).sub (hcos.const_mul eccentricity)
    apply (hraw.congr_deriv (by ring)).congr_of_eventuallyEq
    filter_upwards [] with t
    simp [denominator]
  fin_cases coordinate
  · have hnumerator := hsin.const_mul (-firstAction ^ 2 * meanMotion)
    have hquotient := hnumerator.div hdenominatorDeriv hdenominator
    apply (hquotient.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      rfl
    · have halgebra :
          ((-firstAction ^ 2 * meanMotion *
                (Real.cos (anomaly time) * (meanMotion / denominator time)) *
              denominator time -
            (-firstAction ^ 2 * meanMotion * Real.sin (anomaly time)) *
              (eccentricity * Real.sin (anomaly time) *
                (meanMotion / denominator time))) / denominator time ^ 2) =
            -(firstAction ^ 2 * (Real.cos (anomaly time) - eccentricity)) /
              (firstAction ^ 2 * denominator time) ^ 3 := by
        dsimp [meanMotion]
        field_simp [hfirstAction, hdenominator]
        dsimp [denominator]
        nlinarith [Real.sin_sq_add_cos_sq (anomaly time)]
      simpa [meanMotion, anomaly, denominator, inertialEllipsePosition,
        eccentricRadius] using halgebra
  · have hnumerator := hcos.const_mul
      (firstAction ^ 2 * meanMotion * Real.sqrt (1 - eccentricity ^ 2))
    have hquotient := hnumerator.div hdenominatorDeriv hdenominator
    apply (hquotient.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      rfl
    · have halgebra :
          ((firstAction ^ 2 * meanMotion * Real.sqrt (1 - eccentricity ^ 2) *
                (-Real.sin (anomaly time) * (meanMotion / denominator time)) *
              denominator time -
            (firstAction ^ 2 * meanMotion * Real.sqrt (1 - eccentricity ^ 2) *
              Real.cos (anomaly time)) *
              (eccentricity * Real.sin (anomaly time) *
                (meanMotion / denominator time))) / denominator time ^ 2) =
            -(firstAction ^ 2 * Real.sqrt (1 - eccentricity ^ 2) *
                Real.sin (anomaly time)) /
              (firstAction ^ 2 * denominator time) ^ 3 := by
        dsimp [meanMotion]
        field_simp [hfirstAction, hdenominator]
        ring
      simpa [meanMotion, anomaly, denominator, inertialEllipsePosition,
        eccentricRadius] using halgebra

/-- The momentum coordinates of a general Delaunay flow line satisfy the remaining two Hamilton
equations. -/
theorem hasDerivAt_liftedDelaunayFlowLine_momentum
    {firstAction eccentricity meanAnomaly periapsisAngle time : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    let radius := eccentricRadius firstAction eccentricity
      (liftedDelaunayEccentricAnomalyAlongFlow
        firstAction eccentricity meanAnomaly time)
    HasDerivAt
        (fun t ↦ liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle t 2)
        (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 3 -
          liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 0 /
            radius ^ 3) time ∧
      HasDerivAt
        (fun t ↦ liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle t 3)
        (-liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 2 -
          liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 1 /
            radius ^ 3) time := by
  let anomaly : ℝ → ℝ :=
    liftedDelaunayEccentricAnomalyAlongFlow firstAction eccentricity meanAnomaly
  let xInertial : ℝ → ℝ := fun t ↦
    inertialEllipsePosition firstAction eccentricity (anomaly t) 0
  let yInertial : ℝ → ℝ := fun t ↦
    inertialEllipsePosition firstAction eccentricity (anomaly t) 1
  let vxInertial : ℝ → ℝ := fun t ↦
    inertialEllipseVelocity firstAction eccentricity (1 / firstAction ^ 3) (anomaly t) 0
  let vyInertial : ℝ → ℝ := fun t ↦
    inertialEllipseVelocity firstAction eccentricity (1 / firstAction ^ 3) (anomaly t) 1
  let radius : ℝ := eccentricRadius firstAction eccentricity (anomaly time)
  let angle : ℝ → ℝ := fun t ↦ t - periapsisAngle
  have hvx : HasDerivAt vxInertial (-xInertial time / radius ^ 3) time :=
    hasDerivAt_inertialEllipseVelocity_liftedDelaunayFlow hfirstAction
      heccentricity heccentricityOne 0
  have hvy : HasDerivAt vyInertial (-yInertial time / radius ^ 3) time :=
    hasDerivAt_inertialEllipseVelocity_liftedDelaunayFlow hfirstAction
      heccentricity heccentricityOne 1
  have hangle : HasDerivAt angle 1 time := by
    simpa [angle] using (hasDerivAt_id time).sub_const periapsisAngle
  have hcos := (Real.hasDerivAt_cos (angle time)).comp time hangle
  have hsin := (Real.hasDerivAt_sin (angle time)).comp time hangle
  constructor
  · have hraw := (hcos.mul hvx).add (hsin.mul hvy)
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      simp only [liftedDelaunayFlowLine, liftedDelaunayPhasePoint,
        liftedDelaunayPosition, liftedDelaunayMomentum,
        liftedDelaunayEccentricAnomaly_flow_argument,
        positionMomentumPhasePoint, positionInRotatingFrame,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [vxInertial, vyInertial, anomaly, angle]
      congr 3 <;> ring
    · simp only [liftedDelaunayFlowLine, liftedDelaunayPhasePoint,
        liftedDelaunayPosition, liftedDelaunayMomentum,
        liftedDelaunayEccentricAnomaly_flow_argument,
        positionMomentumPhasePoint, positionInRotatingFrame,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, vxInertial, vyInertial, anomaly, radius, angle]
      ring
  · have hraw := (hsin.neg.mul hvx).add (hcos.mul hvy)
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      simp only [liftedDelaunayFlowLine, liftedDelaunayPhasePoint,
        liftedDelaunayPosition, liftedDelaunayMomentum,
        liftedDelaunayEccentricAnomaly_flow_argument,
        positionMomentumPhasePoint, positionInRotatingFrame,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [vxInertial, vyInertial, anomaly, angle]
      congr 3 <;> ring
    · simp only [liftedDelaunayFlowLine, liftedDelaunayPhasePoint,
        liftedDelaunayPosition, liftedDelaunayMomentum,
        liftedDelaunayEccentricAnomaly_flow_argument,
        positionMomentumPhasePoint, positionInRotatingFrame,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, vxInertial, vyInertial, anomaly, radius, angle]
      ring

/-- The position norm of a lifted Delaunay flow point is its eccentric radius. -/
lemma sqrt_positionSq_liftedDelaunayFlowLine
    {firstAction eccentricity meanAnomaly periapsisAngle time : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    Real.sqrt
        ((liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 0) ^ 2 +
          (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 1) ^ 2) =
      eccentricRadius firstAction eccentricity
        (liftedDelaunayEccentricAnomalyAlongFlow
          firstAction eccentricity meanAnomaly time) := by
  have hradius := eccentricRadius_pos
    (anomaly := liftedDelaunayEccentricAnomalyAlongFlow
      firstAction eccentricity meanAnomaly time)
    hfirstAction heccentricity heccentricityOne
  rw [show
    (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 0) ^ 2 +
        (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 1) ^ 2 =
      eccentricRadius firstAction eccentricity
        (liftedDelaunayEccentricAnomalyAlongFlow
          firstAction eccentricity meanAnomaly time) ^ 2 by
      unfold liftedDelaunayFlowLine liftedDelaunayPhasePoint liftedDelaunayPosition
      simp only [positionMomentumPhasePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
        liftedDelaunayEccentricAnomaly_flow_argument]
      rw [positionInRotatingFrame_sq,
        inertialEllipsePosition_sq heccentricity heccentricityOne.le]]
  exact (Real.sqrt_sq_eq_abs _).trans (abs_of_pos hradius)

/-- A general lifted Delaunay flow line has derivative equal to the rotating Kepler vector field. -/
theorem hasDerivAt_liftedDelaunayFlowLine
    {firstAction eccentricity meanAnomaly periapsisAngle time : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    HasDerivAt (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle)
      (rotatingKeplerVectorField
        (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly
          periapsisAngle time)) time := by
  have hposition := hasDerivAt_liftedDelaunayFlowLine_position
    (firstAction := firstAction) (meanAnomaly := meanAnomaly)
    (periapsisAngle := periapsisAngle) (time := time)
    heccentricity heccentricityOne
  have hmomentum := hasDerivAt_liftedDelaunayFlowLine_momentum hfirstAction
    heccentricity heccentricityOne (meanAnomaly := meanAnomaly)
    (periapsisAngle := periapsisAngle) (time := time)
  have hradius := sqrt_positionSq_liftedDelaunayFlowLine hfirstAction
    heccentricity heccentricityOne (meanAnomaly := meanAnomaly)
    (periapsisAngle := periapsisAngle) (time := time)
  rw [hasDerivAt_pi]
  intro coordinate
  fin_cases coordinate
  · exact hposition.1
  · exact hposition.2
  · change HasDerivAt
      (fun t ↦ liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle t 2)
      (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 3 -
        liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 0 /
          Real.sqrt
            ((liftedDelaunayFlowLine firstAction eccentricity meanAnomaly
                periapsisAngle time 0) ^ 2 +
              (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly
                periapsisAngle time 1) ^ 2) ^ 3)
      time
    rw [hradius]
    exact hmomentum.1
  · change HasDerivAt
      (fun t ↦ liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle t 3)
      (-liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 2 -
        liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 1 /
          Real.sqrt
            ((liftedDelaunayFlowLine firstAction eccentricity meanAnomaly
                periapsisAngle time 0) ^ 2 +
              (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly
                periapsisAngle time 1) ^ 2) ^ 3)
      time
    rw [hradius]
    exact hmomentum.2

/-- Along a general lifted Delaunay flow line, the derivative of any differentiable observable is
its Poisson bracket with the mass-zero Hamiltonian. -/
theorem DifferentiableAt.hasDerivAt_comp_liftedDelaunayFlowLine
    {F : PhaseSpace → ℝ}
    {firstAction eccentricity meanAnomaly periapsisAngle time : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hF : DifferentiableAt ℝ F
      (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time)) :
    HasDerivAt
      (fun t ↦ F (liftedDelaunayFlowLine
        firstAction eccentricity meanAnomaly periapsisAngle t))
      (poissonBracket F (hamiltonian 0)
        (liftedDelaunayFlowLine
          firstAction eccentricity meanAnomaly periapsisAngle time)) time := by
  let state := liftedDelaunayFlowLine
    firstAction eccentricity meanAnomaly periapsisAngle time
  have horigin : state 0 ^ 2 + state 1 ^ 2 ≠ 0 := by
    have hradius := eccentricRadius_pos
      (anomaly := liftedDelaunayEccentricAnomalyAlongFlow
        firstAction eccentricity meanAnomaly time)
      hfirstAction heccentricity heccentricityOne
    have hsquare : state 0 ^ 2 + state 1 ^ 2 =
        eccentricRadius firstAction eccentricity
          (liftedDelaunayEccentricAnomalyAlongFlow
            firstAction eccentricity meanAnomaly time) ^ 2 := by
      dsimp only [state]
      unfold liftedDelaunayFlowLine liftedDelaunayPhasePoint liftedDelaunayPosition
      simp only [positionMomentumPhasePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
        liftedDelaunayEccentricAnomaly_flow_argument]
      rw [positionInRotatingFrame_sq,
        inertialEllipsePosition_sq heccentricity heccentricityOne.le]
    rw [hsquare]
    exact (sq_pos_of_pos hradius).ne'
  have hchain := hF.hasFDerivAt.comp_hasDerivAt time
    (hasDerivAt_liftedDelaunayFlowLine hfirstAction heccentricity heccentricityOne)
  apply hchain.congr_deriv
  exact (poissonBracket_hamiltonian_zero_eq_fderiv_apply F horigin).symm

/-- A lifted Delaunay ellipse lying strictly inside the unit primary's orbit is collision-free at
mass zero for all time. -/
lemma liftedDelaunayFlowLine_collisionFree_mass_zero
    {firstAction eccentricity meanAnomaly periapsisAngle time : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1) :
    (0, liftedDelaunayFlowLine
      firstAction eccentricity meanAnomaly periapsisAngle time) ∈ collisionFree := by
  let anomaly := liftedDelaunayEccentricAnomalyAlongFlow
    firstAction eccentricity meanAnomaly time
  let angle := time - periapsisAngle
  constructor
  · unfold firstPrimaryDistanceSq
    simp only [add_zero]
    change
      (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 0 - 1) ^ 2 +
        (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 1) ^ 2 ≠ 0
    have hprimary := rotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one
      (firstAction := firstAction) (eccentricity := eccentricity)
      (anomaly := anomaly) (time := angle)
      heccentricity heccentricityOne hapoapsis
    simpa [liftedDelaunayFlowLine, liftedDelaunayPhasePoint,
      liftedDelaunayPosition, positionMomentumPhasePoint,
      rotatingEllipsePosition, anomaly, angle] using hprimary
  · unfold secondPrimaryDistanceSq
    simp only [add_zero]
    have hradius := eccentricRadius_pos (anomaly := anomaly)
      hfirstAction heccentricity heccentricityOne
    have hpositionSq :
        (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 0) ^ 2 +
          (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 1) ^ 2 =
        eccentricRadius firstAction eccentricity anomaly ^ 2 := by
      unfold liftedDelaunayFlowLine liftedDelaunayPhasePoint liftedDelaunayPosition
      simp only [positionMomentumPhasePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
        liftedDelaunayEccentricAnomaly_flow_argument]
      rw [positionInRotatingFrame_sq,
        inertialEllipsePosition_sq heccentricity heccentricityOne.le]
    change
      (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 0) ^ 2 +
        (liftedDelaunayFlowLine firstAction eccentricity meanAnomaly periapsisAngle time 1) ^ 2 ≠ 0
    rw [hpositionSq]
    exact (sq_pos_of_pos hradius).ne'

/-- Collision-freeness of a static lifted Delaunay chart point. -/
lemma liftedDelaunayPhasePoint_collisionFree_mass_zero
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1) :
    (0, liftedDelaunayPhasePoint
      firstAction eccentricity meanAnomaly periapsisAngle) ∈ collisionFree := by
  simpa [liftedDelaunayFlowLine] using
    (liftedDelaunayFlowLine_collisionFree_mass_zero
      (firstAction := firstAction) (eccentricity := eccentricity)
      (meanAnomaly := meanAnomaly) (periapsisAngle := periapsisAngle) (time := 0)
      hfirstAction heccentricity heccentricityOne hapoapsis)

/-- Positive first actions whose Kepler ellipses stay strictly inside the unit primary orbit. -/
abbrev InteriorPositiveAction (eccentricity : ℝ) :=
  {action : PositiveAction // action.1 ^ 2 * (1 + eccentricity) < 1}

/-- The interior actions with irrational Kepler frequency. -/
def irrationalFrequencyInteriorPositiveActions (eccentricity : ℝ) :
    Set (InteriorPositiveAction eccentricity) :=
  {action | Irrational (1 / action.1.1 ^ 3)}

/-- Irrational Kepler tori are dense among the ellipses staying inside the primary orbit. -/
theorem irrationalFrequencyInteriorPositiveActions_dense
    (eccentricity : ℝ) :
    Dense (irrationalFrequencyInteriorPositiveActions eccentricity) := by
  apply Subtype.dense_iff.mpr
  intro action haction
  have hopen : IsOpen
      {candidate : PositiveAction |
        candidate.1 ^ 2 * (1 + eccentricity) < 1} := by
    exact isOpen_lt ((continuous_subtype_val.pow 2).mul continuous_const)
      continuous_const
  have hclosure :=
    irrationalFrequencyPositiveActions_dense.open_subset_closure_inter hopen haction
  have himage :
      ((↑) : InteriorPositiveAction eccentricity → PositiveAction) ''
          irrationalFrequencyInteriorPositiveActions eccentricity =
        {candidate : PositiveAction |
            candidate.1 ^ 2 * (1 + eccentricity) < 1} ∩
          irrationalFrequencyPositiveActions := by
    ext candidate
    constructor
    · rintro ⟨interiorAction, hirrational, rfl⟩
      exact ⟨interiorAction.2, hirrational⟩
    · rintro ⟨hinterior, hirrational⟩
      exact ⟨⟨candidate, hinterior⟩, hirrational, rfl⟩
  have hclosures := congrArg closure himage
  exact hclosures.symm ▸ hclosure

/-- The mass-zero member of an exact analytic first-integral family is invariant along every
interior lifted Delaunay flow line. -/
theorem IsFirstIntegralFamily.liftedDelaunayFlowLine_invariant
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1)
    (time : ℝ) :
    F 0 (liftedDelaunayFlowLine
        firstAction eccentricity meanAnomaly periapsisAngle time) =
      F 0 (liftedDelaunayFlowLine
        firstAction eccentricity meanAnomaly periapsisAngle 0) := by
  let orbit := liftedDelaunayFlowLine
    firstAction eccentricity meanAnomaly periapsisAngle
  let observable : ℝ → ℝ := fun t ↦ F 0 (orbit t)
  have hderiv : ∀ t, HasDerivAt observable 0 t := by
    intro t
    have hcollision : (0, orbit t) ∈ collisionFree :=
      liftedDelaunayFlowLine_collisionFree_mass_zero hfirstAction heccentricity
        heccentricityOne hapoapsis
    have hdomain : (0, orbit t) ∈ parameterDomain δ :=
      ⟨by simpa using hδ, hcollision⟩
    have hslice : DifferentiableAt ℝ (F 0) (orbit t) := by
      have hjoint := hanalytic (0, orbit t) hdomain
      have hembedding : AnalyticAt ℝ
          (fun phase : PhaseSpace ↦ ((0 : ℝ), phase)) (orbit t) :=
        analyticAt_const.prod analyticAt_id
      exact (hjoint.comp hembedding).differentiableAt
    have hflowDerivative :=
      DifferentiableAt.hasDerivAt_comp_liftedDelaunayFlowLine
        (firstAction := firstAction) (eccentricity := eccentricity)
        (meanAnomaly := meanAnomaly) (periapsisAngle := periapsisAngle)
        (time := t) hfirstAction heccentricity heccentricityOne hslice
    have hbracket := IsFirstIntegralFamily.poissonBracket_zero_at_mass_zero
      hδ hfirstIntegral hcollision
    exact hflowDerivative.congr_deriv hbracket
  have hdifferentiable : Differentiable ℝ observable :=
    fun t ↦ (hderiv t).differentiableAt
  have hderivativeZero : ∀ t, deriv observable t = 0 :=
    fun t ↦ (hderiv t).deriv
  exact is_const_of_deriv_eq_zero hdifferentiable hderivativeZero time 0

/-- On every irrational interior Kepler torus, the mass-zero term of a candidate exact analytic
first integral is independent of both Delaunay angles. -/
theorem IsFirstIntegralFamily.mass_zero_liftedDelaunayPhasePoint_eq_of_irrational
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {firstAction eccentricity : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1)
    (hirrational : Irrational (1 / firstAction ^ 3))
    (firstAngles secondAngles : ℝ × ℝ) :
    F 0 (liftedDelaunayPhasePoint
        firstAction eccentricity firstAngles.1 firstAngles.2) =
      F 0 (liftedDelaunayPhasePoint
        firstAction eccentricity secondAngles.1 secondAngles.2) := by
  let pullback : ℝ × ℝ → ℝ := fun angles ↦
    F 0 (liftedDelaunayPhasePoint
      firstAction eccentricity angles.1 angles.2)
  have hpullback : Continuous pullback := by
    rw [continuous_iff_continuousAt]
    intro angles
    let state := liftedDelaunayPhasePoint
      firstAction eccentricity angles.1 angles.2
    have hcollision : (0, state) ∈ collisionFree :=
      liftedDelaunayPhasePoint_collisionFree_mass_zero hfirstAction
        heccentricity heccentricityOne hapoapsis
    have hdomain : (0, state) ∈ parameterDomain δ :=
      ⟨by simpa using hδ, hcollision⟩
    have hcandidate : ContinuousAt (F 0) state := by
      have hjoint := hanalytic (0, state) hdomain
      have hembedding : AnalyticAt ℝ
          (fun phase : PhaseSpace ↦ ((0 : ℝ), phase)) state :=
        analyticAt_const.prod analyticAt_id
      exact (hjoint.comp hembedding).continuousAt
    exact hcandidate.comp
      (continuous_liftedDelaunayPhasePoint_angles
        heccentricity heccentricityOne).continuousAt
  have hmeanPeriod : ∀ mean periapsis,
      pullback (mean + 2 * Real.pi, periapsis) = pullback (mean, periapsis) := by
    intro mean periapsis
    unfold pullback
    rw [liftedDelaunayPhasePoint_add_mean_period heccentricity heccentricityOne]
  have hperiapsisPeriod : ∀ mean periapsis,
      pullback (mean, periapsis + 2 * Real.pi) = pullback (mean, periapsis) := by
    intro mean periapsis
    unfold pullback
    rw [liftedDelaunayPhasePoint_add_periapsis_period]
  have hinvariant : ∀ mean periapsis time,
      pullback (mean + (1 / firstAction ^ 3) * time, periapsis - time) =
        pullback (mean, periapsis) := by
    intro mean periapsis time
    have hflow := IsFirstIntegralFamily.liftedDelaunayFlowLine_invariant
      hδ hanalytic hfirstIntegral hfirstAction heccentricity heccentricityOne
      hapoapsis (meanAnomaly := mean) (periapsisAngle := periapsis) time
    simpa [pullback, liftedDelaunayFlowLine, div_eq_mul_inv,
      mul_comm] using hflow
  exact eq_of_continuous_periodic_rotatingFlow_invariant hirrational hpullback
    hmeanPeriod hperiapsisPeriod hinvariant firstAngles secondAngles

/-- On every interior Kepler torus, including the rationally resonant ones, the mass-zero term of
an exact analytic first-integral family is independent of both Delaunay angles.  This is the
continuity extension of the irrational-torus theorem. -/
theorem IsFirstIntegralFamily.mass_zero_liftedDelaunayPhasePoint_eq
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {firstAction eccentricity : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1)
    (firstAngles secondAngles : ℝ × ℝ) :
    F 0 (liftedDelaunayPhasePoint
        firstAction eccentricity firstAngles.1 firstAngles.2) =
      F 0 (liftedDelaunayPhasePoint
        firstAction eccentricity secondAngles.1 secondAngles.2) := by
  let left : InteriorPositiveAction eccentricity → ℝ := fun action ↦
    F 0 (liftedDelaunayPhasePoint
      action.1.1 eccentricity firstAngles.1 firstAngles.2)
  let right : InteriorPositiveAction eccentricity → ℝ := fun action ↦
    F 0 (liftedDelaunayPhasePoint
      action.1.1 eccentricity secondAngles.1 secondAngles.2)
  have hcontinuous : ∀ angles : ℝ × ℝ, Continuous
      (fun action : InteriorPositiveAction eccentricity ↦
        F 0 (liftedDelaunayPhasePoint
          action.1.1 eccentricity angles.1 angles.2)) := by
    intro angles
    rw [continuous_iff_continuousAt]
    intro action
    let state := liftedDelaunayPhasePoint
      action.1.1 eccentricity angles.1 angles.2
    have hcollision : (0, state) ∈ collisionFree :=
      liftedDelaunayPhasePoint_collisionFree_mass_zero action.1.2.ne'
        heccentricity heccentricityOne action.2
    have hdomain : (0, state) ∈ parameterDomain δ :=
      ⟨by simpa using hδ, hcollision⟩
    have hcandidate : ContinuousAt (F 0) state := by
      have hjoint := hanalytic (0, state) hdomain
      have hembedding : AnalyticAt ℝ
          (fun phase : PhaseSpace ↦ ((0 : ℝ), phase)) state :=
        analyticAt_const.prod analyticAt_id
      exact (hjoint.comp hembedding).continuousAt
    have haction : ContinuousAt
        (fun candidate : InteriorPositiveAction eccentricity ↦ candidate.1.1)
        action := by
      fun_prop
    have hchart : ContinuousAt
        (fun candidate : InteriorPositiveAction eccentricity ↦
          liftedDelaunayPhasePoint
            candidate.1.1 eccentricity angles.1 angles.2) action :=
      (continuousAt_liftedDelaunayPhasePoint_firstAction action.1.2.ne').comp haction
    exact hcandidate.comp hchart
  have hleft : Continuous left := hcontinuous firstAngles
  have hright : Continuous right := hcontinuous secondAngles
  have heq : left = right := by
    apply hleft.ext_on
      (irrationalFrequencyInteriorPositiveActions_dense eccentricity) hright
    intro action hirrational
    exact IsFirstIntegralFamily.mass_zero_liftedDelaunayPhasePoint_eq_of_irrational
      hδ hanalytic hfirstIntegral action.1.2.ne' heccentricity
      heccentricityOne action.2 hirrational firstAngles secondAngles
  let action : InteriorPositiveAction eccentricity :=
    ⟨⟨firstAction, hfirstAction⟩, hapoapsis⟩
  simpa [left, right, action] using congrFun heq action

end LeanPool.PoincareThreeBody
