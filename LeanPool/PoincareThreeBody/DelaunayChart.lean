/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.IrrationalTorusFlow
import LeanPool.PoincareThreeBody.KeplerPhaseOrbit

/-!
# The lifted planar Delaunay chart

This file packages the position and canonical rotating-frame momentum as a function of the first
action, eccentricity, mean anomaly, and rotating periapsis angle.  The angles are initially lifted
to real numbers; periodicity will allow the chart to descend to the angle torus.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- Eccentric anomaly in the lifted Delaunay chart. -/
noncomputable def liftedDelaunayEccentricAnomaly
    (eccentricity meanAnomaly : ℝ) : ℝ :=
  eccentricAnomaly eccentricity meanAnomaly

/-- Position in rotating Cartesian coordinates in the lifted Delaunay chart. -/
noncomputable def liftedDelaunayPosition
    (firstAction eccentricity meanAnomaly periapsisAngle : ℝ) : ActionSpace :=
  positionInRotatingFrame (-periapsisAngle)
    (inertialEllipsePosition firstAction eccentricity
      (liftedDelaunayEccentricAnomaly eccentricity meanAnomaly))

/-- Canonical rotating-frame momentum in the lifted Delaunay chart. -/
noncomputable def liftedDelaunayMomentum
    (firstAction eccentricity meanAnomaly periapsisAngle : ℝ) : ActionSpace :=
  positionInRotatingFrame (-periapsisAngle)
    (inertialEllipseVelocity firstAction eccentricity (1 / firstAction ^ 3)
      (liftedDelaunayEccentricAnomaly eccentricity meanAnomaly))

/-- Full phase-space point in lifted Delaunay variables. -/
noncomputable def liftedDelaunayPhasePoint
    (firstAction eccentricity meanAnomaly periapsisAngle : ℝ) : PhaseSpace :=
  positionMomentumPhasePoint
    (liftedDelaunayPosition firstAction eccentricity meanAnomaly periapsisAngle)
    (liftedDelaunayMomentum firstAction eccentricity meanAnomaly periapsisAngle)

/-- The chart agrees exactly with the previously constructed resonant Kepler orbit. -/
theorem liftedDelaunayPhasePoint_resonant
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (eccentricity orientation time : ℝ) :
    liftedDelaunayPhasePoint (resonantFirstAction p q) eccentricity
        (resonantMeanAnomaly p q time) (orientation - time) =
      orientedResonantKeplerPhasePoint p q eccentricity orientation time := by
  have hmotion : 1 / resonantFirstAction p q ^ 3 = resonantMeanMotion p q := by
    simpa [delaunayFrequency] using
      (resonantMeanMotion_eq_delaunayFrequency hp hq).symm
  simp only [liftedDelaunayPhasePoint, liftedDelaunayPosition,
    liftedDelaunayMomentum, liftedDelaunayEccentricAnomaly,
    orientedResonantKeplerPhasePoint, orientedResonantEllipsePosition,
    orientedResonantEllipseMomentum, resonantEccentricAnomaly,
    positionMomentumPhasePoint]
  rw [hmotion]
  congr 2 <;> ring_nf

/-- The lifted chart is periodic in mean anomaly. -/
lemma liftedDelaunayPhasePoint_add_mean_period
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    liftedDelaunayPhasePoint firstAction eccentricity
        (meanAnomaly + 2 * Real.pi) periapsisAngle =
      liftedDelaunayPhasePoint firstAction eccentricity meanAnomaly periapsisAngle := by
  unfold liftedDelaunayPhasePoint liftedDelaunayPosition liftedDelaunayMomentum
    liftedDelaunayEccentricAnomaly
  rw [eccentricAnomaly_add_two_pi heccentricity heccentricityOne]
  funext coordinate
  fin_cases coordinate <;>
    simp [positionMomentumPhasePoint, positionInRotatingFrame, inertialEllipsePosition,
      inertialEllipseVelocity]

/-- Rotating a vector through a negated angle is unchanged when a full turn is added to that
angle. -/
lemma positionInRotatingFrame_neg_add_two_pi
    (periapsisAngle : ℝ) (vector : ActionSpace) :
    positionInRotatingFrame (-(periapsisAngle + 2 * Real.pi)) vector =
      positionInRotatingFrame (-periapsisAngle) vector := by
  have hcos : Real.cos (-(periapsisAngle + 2 * Real.pi)) =
      Real.cos (-periapsisAngle) := by
    rw [show -(periapsisAngle + 2 * Real.pi) = -periapsisAngle - 2 * Real.pi by ring,
      Real.cos_sub_two_pi]
  have hsin : Real.sin (-(periapsisAngle + 2 * Real.pi)) =
      Real.sin (-periapsisAngle) := by
    rw [show -(periapsisAngle + 2 * Real.pi) = -periapsisAngle - 2 * Real.pi by ring,
      Real.sin_sub_two_pi]
  funext coordinate
  fin_cases coordinate
  · change Real.cos (-(periapsisAngle + 2 * Real.pi)) * vector 0 +
      Real.sin (-(periapsisAngle + 2 * Real.pi)) * vector 1 =
        Real.cos (-periapsisAngle) * vector 0 + Real.sin (-periapsisAngle) * vector 1
    rw [hcos, hsin]
  · change -Real.sin (-(periapsisAngle + 2 * Real.pi)) * vector 0 +
      Real.cos (-(periapsisAngle + 2 * Real.pi)) * vector 1 =
        -Real.sin (-periapsisAngle) * vector 0 + Real.cos (-periapsisAngle) * vector 1
    rw [hcos, hsin]

/-- The lifted chart is periodic in the rotating periapsis angle. -/
lemma liftedDelaunayPhasePoint_add_periapsis_period
    (firstAction eccentricity meanAnomaly periapsisAngle : ℝ) :
    liftedDelaunayPhasePoint firstAction eccentricity meanAnomaly
        (periapsisAngle + 2 * Real.pi) =
      liftedDelaunayPhasePoint firstAction eccentricity meanAnomaly periapsisAngle := by
  unfold liftedDelaunayPhasePoint liftedDelaunayPosition liftedDelaunayMomentum
  rw [positionInRotatingFrame_neg_add_two_pi,
    positionInRotatingFrame_neg_add_two_pi]

/-- Along the unperturbed flow, the first Delaunay angle advances with frequency `I₁⁻³` and the
rotating periapsis angle decreases with unit speed. -/
noncomputable def liftedDelaunayFlowLine
    (firstAction eccentricity meanAnomaly periapsisAngle time : ℝ) : PhaseSpace :=
  liftedDelaunayPhasePoint firstAction eccentricity
    (meanAnomaly + time / firstAction ^ 3) (periapsisAngle - time)

/-- At a rational Kepler resonance and zero initial mean anomaly, the general lifted flow line is
the previously verified resonant trajectory. -/
theorem liftedDelaunayFlowLine_resonant
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (eccentricity orientation time : ℝ) :
    liftedDelaunayFlowLine (resonantFirstAction p q) eccentricity 0 orientation time =
      orientedResonantKeplerPhasePoint p q eccentricity orientation time := by
  have hmotion : time / resonantFirstAction p q ^ 3 = resonantMeanAnomaly p q time := by
    have hfrequency := resonantMeanMotion_eq_delaunayFrequency hp hq
    simp only [resonantMeanAnomaly, delaunayFrequency, Matrix.cons_val_zero] at hfrequency ⊢
    rw [hfrequency]
    ring
  unfold liftedDelaunayFlowLine
  rw [zero_add, hmotion]
  exact liftedDelaunayPhasePoint_resonant hp hq eccentricity orientation time

/-- For fixed elliptic actions, the lifted Delaunay chart is jointly analytic in its two angle
variables. -/
theorem analyticAt_liftedDelaunayPhasePoint_angles
    {firstAction eccentricity : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (angles : ℝ × ℝ) :
    AnalyticAt ℝ
      (fun angle : ℝ × ℝ ↦
        liftedDelaunayPhasePoint firstAction eccentricity angle.1 angle.2) angles := by
  let anomaly : ℝ × ℝ → ℝ := fun angle ↦ eccentricAnomaly eccentricity angle.1
  let denominator : ℝ × ℝ → ℝ := fun angle ↦
    1 - eccentricity * Real.cos (anomaly angle)
  let xInertial : ℝ × ℝ → ℝ := fun angle ↦
    firstAction ^ 2 * (Real.cos (anomaly angle) - eccentricity)
  let yInertial : ℝ × ℝ → ℝ := fun angle ↦
    firstAction ^ 2 * Real.sqrt (1 - eccentricity ^ 2) * Real.sin (anomaly angle)
  let vxInertial : ℝ × ℝ → ℝ := fun angle ↦
    -firstAction ^ 2 * (1 / firstAction ^ 3) * Real.sin (anomaly angle) /
      denominator angle
  let vyInertial : ℝ × ℝ → ℝ := fun angle ↦
    firstAction ^ 2 * (1 / firstAction ^ 3) * Real.sqrt (1 - eccentricity ^ 2) *
      Real.cos (anomaly angle) / denominator angle
  have hanomaly : AnalyticAt ℝ anomaly angles :=
    (analyticAt_eccentricAnomaly heccentricity heccentricityOne).comp analyticAt_fst
  have hsinAnomaly : AnalyticAt ℝ (fun angle ↦ Real.sin (anomaly angle)) angles :=
    Real.analyticAt_sin.comp hanomaly
  have hcosAnomaly : AnalyticAt ℝ (fun angle ↦ Real.cos (anomaly angle)) angles :=
    Real.analyticAt_cos.comp hanomaly
  have hdenominator : AnalyticAt ℝ denominator angles :=
    analyticAt_const.sub (analyticAt_const.mul hcosAnomaly)
  have hdenominatorNe : denominator angles ≠ 0 :=
    (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne).ne'
  have hinverseDenominator : AnalyticAt ℝ
      (fun angle ↦ (denominator angle)⁻¹) angles :=
    hdenominator.inv hdenominatorNe
  have heccentricityConstant : AnalyticAt ℝ
      (fun _ : ℝ × ℝ ↦ eccentricity) angles := analyticAt_const
  have hx : AnalyticAt ℝ xInertial angles := by
    dsimp only [xInertial]
    exact (hcosAnomaly.sub heccentricityConstant).const_smul (c := firstAction ^ 2)
      |>.congr (by filter_upwards [] with angle; simp [smul_eq_mul])
  have hy : AnalyticAt ℝ yInertial angles := by
    dsimp only [yInertial]
    exact hsinAnomaly.const_smul
      (c := firstAction ^ 2 * Real.sqrt (1 - eccentricity ^ 2))
      |>.congr (by filter_upwards [] with angle; simp [smul_eq_mul])
  have hvx : AnalyticAt ℝ vxInertial angles := by
    dsimp only [vxInertial]
    exact (hsinAnomaly.const_smul
      (c := -firstAction ^ 2 * (1 / firstAction ^ 3))
      |>.congr (by filter_upwards [] with angle; simp [smul_eq_mul])).mul
        hinverseDenominator
  have hvy : AnalyticAt ℝ vyInertial angles := by
    dsimp only [vyInertial]
    exact (hcosAnomaly.const_smul
      (c := firstAction ^ 2 * (1 / firstAction ^ 3) * Real.sqrt (1 - eccentricity ^ 2))
      |>.congr (by filter_upwards [] with angle; simp [smul_eq_mul])).mul
        hinverseDenominator
  have hnegPeriapsis : AnalyticAt ℝ (fun angle : ℝ × ℝ ↦ -angle.2) angles :=
    analyticAt_snd.neg
  have hcosPeriapsis : AnalyticAt ℝ
      (fun angle : ℝ × ℝ ↦ Real.cos (-angle.2)) angles :=
    Real.analyticAt_cos.comp hnegPeriapsis
  have hsinPeriapsis : AnalyticAt ℝ
      (fun angle : ℝ × ℝ ↦ Real.sin (-angle.2)) angles :=
    Real.analyticAt_sin.comp hnegPeriapsis
  rw [analyticAt_pi_iff]
  intro coordinate
  fin_cases coordinate
  · change AnalyticAt ℝ (fun angle ↦
      Real.cos (-angle.2) * xInertial angle +
        Real.sin (-angle.2) * yInertial angle) angles
    exact (hcosPeriapsis.mul hx).add (hsinPeriapsis.mul hy)
  · change AnalyticAt ℝ (fun angle ↦
      -Real.sin (-angle.2) * xInertial angle +
        Real.cos (-angle.2) * yInertial angle) angles
    exact (hsinPeriapsis.neg.mul hx).add (hcosPeriapsis.mul hy)
  · change AnalyticAt ℝ (fun angle ↦
      Real.cos (-angle.2) * vxInertial angle +
        Real.sin (-angle.2) * vyInertial angle) angles
    exact (hcosPeriapsis.mul hvx).add (hsinPeriapsis.mul hvy)
  · change AnalyticAt ℝ (fun angle ↦
      -Real.sin (-angle.2) * vxInertial angle +
        Real.cos (-angle.2) * vyInertial angle) angles
    exact (hsinPeriapsis.neg.mul hvx).add (hcosPeriapsis.mul hvy)

/-- Continuity form of the angle chart. -/
theorem continuous_liftedDelaunayPhasePoint_angles
    {firstAction eccentricity : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    Continuous (fun angle : ℝ × ℝ ↦
      liftedDelaunayPhasePoint firstAction eccentricity angle.1 angle.2) := by
  rw [continuous_iff_continuousAt]
  intro angles
  exact (analyticAt_liftedDelaunayPhasePoint_angles
    heccentricity heccentricityOne angles).continuousAt

/-- Away from the degenerate value `I₁ = 0`, the lifted chart varies continuously with the
first Delaunay action. -/
theorem continuousAt_liftedDelaunayPhasePoint_firstAction
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : firstAction ≠ 0) :
    ContinuousAt
      (fun action ↦ liftedDelaunayPhasePoint
        action eccentricity meanAnomaly periapsisAngle) firstAction := by
  have hcube : firstAction ^ 3 ≠ 0 := pow_ne_zero 3 hfirstAction
  have hinverseCube : ContinuousAt (fun action : ℝ ↦ (action ^ 3)⁻¹) firstAction :=
    (continuousAt_id.pow 3).inv₀ hcube
  rw [continuousAt_pi]
  intro coordinate
  fin_cases coordinate <;>
    simp only [liftedDelaunayPhasePoint, liftedDelaunayPosition,
      liftedDelaunayMomentum, liftedDelaunayEccentricAnomaly,
      positionMomentumPhasePoint, positionInRotatingFrame,
      inertialEllipsePosition, inertialEllipseVelocity,
      Matrix.cons_val_zero, Matrix.cons_val_one, div_eq_mul_inv] <;>
    fun_prop

end LeanPool.PoincareThreeBody
