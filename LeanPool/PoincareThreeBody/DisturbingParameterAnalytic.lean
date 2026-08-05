/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DisturbingFunction
import LeanPool.PoincareThreeBody.JointEccentricAnomaly

/-!
# Analytic eccentricity dependence of the disturbing function

Away from collisions, the Newtonian disturbing function along a fixed point of a resonant orbit
is real analytic in eccentricity.  This is the pointwise analytic input for the subsequent
parameter-integral argument.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

theorem analyticAt_resonantEccentricAnomaly_eccentricity
    (p q : ℕ) {eccentricity time : ℝ}
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1) :
    AnalyticAt ℝ (fun candidate ↦
      resonantEccentricAnomaly p q candidate time) eccentricity := by
  unfold resonantEccentricAnomaly
  have hparameters : AnalyticAt ℝ (fun candidate : ℝ ↦
      (candidate, resonantMeanAnomaly p q time)) eccentricity :=
    analyticAt_id.prod analyticAt_const
  exact (analyticAt_eccentricAnomaly_joint heccentricity heccentricityOne).comp
    (f := fun candidate : ℝ ↦ (candidate, resonantMeanAnomaly p q time)) hparameters

/-- Each rotating Cartesian coordinate of the oriented resonant ellipse is analytic in
eccentricity. -/
theorem analyticAt_orientedResonantEllipsePosition_eccentricity_coordinate
    (p q : ℕ) {eccentricity orientation time : ℝ}
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (coordinate : Fin 2) :
    AnalyticAt ℝ (fun candidate ↦
      orientedResonantEllipsePosition p q candidate orientation time coordinate)
      eccentricity := by
  let anomaly : ℝ → ℝ := fun candidate ↦
    resonantEccentricAnomaly p q candidate time
  have hanomaly : AnalyticAt ℝ anomaly eccentricity :=
    analyticAt_resonantEccentricAnomaly_eccentricity p q
      heccentricity heccentricityOne
  have heccentricityId : AnalyticAt ℝ (fun candidate : ℝ ↦ candidate) eccentricity :=
    analyticAt_id
  have hsqrt : AnalyticAt ℝ (fun candidate : ℝ ↦
      Real.sqrt (1 - candidate ^ 2)) eccentricity := by
    exact (analyticAt_sqrt_of_pos (by nlinarith)).comp
      (analyticAt_const.sub (heccentricityId.pow 2))
  let inertialX : ℝ → ℝ := fun candidate ↦
    resonantFirstAction p q ^ 2 *
      (Real.cos (anomaly candidate) - candidate)
  let inertialY : ℝ → ℝ := fun candidate ↦
    resonantFirstAction p q ^ 2 * Real.sqrt (1 - candidate ^ 2) *
      Real.sin (anomaly candidate)
  have hx : AnalyticAt ℝ inertialX eccentricity := by
    exact analyticAt_const.mul
      ((Real.analyticAt_cos.comp hanomaly).sub heccentricityId)
  have hy : AnalyticAt ℝ inertialY eccentricity := by
    exact (analyticAt_const.mul hsqrt).mul (Real.analyticAt_sin.comp hanomaly)
  fin_cases coordinate
  · change AnalyticAt ℝ (fun candidate ↦
      Real.cos (time - orientation) * inertialX candidate +
        Real.sin (time - orientation) * inertialY candidate) eccentricity
    exact (analyticAt_const.mul hx).add (analyticAt_const.mul hy)
  · change AnalyticAt ℝ (fun candidate ↦
      -Real.sin (time - orientation) * inertialX candidate +
        Real.cos (time - orientation) * inertialY candidate) eccentricity
    exact (analyticAt_const.mul hx).add (analyticAt_const.mul hy)

/-- At every fixed orientation and time, the resonant disturbing function is analytic in
eccentricity throughout the collision-free interior range. -/
theorem analyticAt_resonantDisturbingFunction_eccentricity
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    AnalyticAt ℝ (fun candidate ↦
      resonantDisturbingFunction p q candidate orientation time) eccentricity := by
  let x : ℝ → ℝ := fun candidate ↦
    orientedResonantEllipsePosition p q candidate orientation time 0
  let y : ℝ → ℝ := fun candidate ↦
    orientedResonantEllipsePosition p q candidate orientation time 1
  have hx : AnalyticAt ℝ x eccentricity :=
    analyticAt_orientedResonantEllipsePosition_eccentricity_coordinate p q
      heccentricity heccentricityOne 0
  have hy : AnalyticAt ℝ y eccentricity :=
    analyticAt_orientedResonantEllipsePosition_eccentricity_coordinate p q
      heccentricity heccentricityOne 1
  have horiginSq : AnalyticAt ℝ
      (fun candidate ↦ x candidate ^ 2 + y candidate ^ 2) eccentricity :=
    (hx.pow 2).add (hy.pow 2)
  have hfirstAction : resonantFirstAction p q ≠ 0 :=
    (resonantFirstAction_pos hp hq).ne'
  have horiginPositive : 0 < x eccentricity ^ 2 + y eccentricity ^ 2 := by
    change 0 <
      (orientedResonantEllipsePosition p q eccentricity orientation time 0) ^ 2 +
        (orientedResonantEllipsePosition p q eccentricity orientation time 1) ^ 2
    rw [orientedResonantEllipsePosition_sq heccentricity.le heccentricityOne.le]
    exact sq_pos_of_pos
      (eccentricRadius_pos hfirstAction heccentricity.le heccentricityOne)
  have hinverseOrigin : AnalyticAt ℝ
      (fun candidate ↦ 1 / Real.sqrt (x candidate ^ 2 + y candidate ^ 2))
      eccentricity :=
    (analyticAt_inv_sqrt horiginPositive).comp
      (f := fun candidate ↦ x candidate ^ 2 + y candidate ^ 2) horiginSq
  have hprimarySq : AnalyticAt ℝ
      (fun candidate ↦ (x candidate - 1) ^ 2 + y candidate ^ 2) eccentricity :=
    ((hx.sub analyticAt_const).pow 2).add (hy.pow 2)
  have hprimaryNe :
      (x eccentricity - 1) ^ 2 + y eccentricity ^ 2 ≠ 0 := by
    exact rotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one
      heccentricity.le heccentricityOne hapoapsis
  have hprimaryPositive :
      0 < (x eccentricity - 1) ^ 2 + y eccentricity ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm hprimaryNe)
  have hinversePrimary : AnalyticAt ℝ
      (fun candidate ↦
        1 / Real.sqrt ((x candidate - 1) ^ 2 + y candidate ^ 2)) eccentricity :=
    (analyticAt_inv_sqrt hprimaryPositive).comp
      (f := fun candidate ↦ (x candidate - 1) ^ 2 + y candidate ^ 2) hprimarySq
  have hraw := hinverseOrigin.add (hx.mul (hinverseOrigin.pow 3)) |>.sub hinversePrimary
  apply hraw.congr
  filter_upwards [] with candidate
  simp [x, y, resonantDisturbingFunction, orientedResonantEllipsePhasePoint,
    positionPhasePoint, firstMassPerturbation, div_eq_mul_inv]

/-- Pointwise analyticity assembled over the whole collision-free eccentricity interval. -/
theorem analyticOnNhd_resonantDisturbingFunction_eccentricity
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (orientation time : ℝ) :
    AnalyticOnNhd ℝ
      (fun eccentricity ↦
        resonantDisturbingFunction p q eccentricity orientation time)
      {eccentricity | 0 < eccentricity ∧ eccentricity < 1 ∧
        resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1} := by
  intro eccentricity heccentricity
  exact analyticAt_resonantDisturbingFunction_eccentricity hp hq
    heccentricity.1 heccentricity.2.1 heccentricity.2.2

end LeanPool.PoincareThreeBody
