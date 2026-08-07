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

/-- The resonant eccentric anomaly is jointly analytic in eccentricity and physical time. -/
theorem analyticAt_resonantEccentricAnomaly_eccentricity_time
    (p q : ℕ) {eccentricity time : ℝ}
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1) :
    AnalyticAt ℝ (fun parameters : ℝ × ℝ ↦
      resonantEccentricAnomaly p q parameters.1 parameters.2)
      (eccentricity, time) := by
  have hmean : AnalyticAt ℝ (fun parameters : ℝ × ℝ ↦
      resonantMeanAnomaly p q parameters.2) (eccentricity, time) := by
    unfold resonantMeanAnomaly
    exact analyticAt_const.mul analyticAt_snd
  have hparameters : AnalyticAt ℝ (fun parameters : ℝ × ℝ ↦
      (parameters.1, resonantMeanAnomaly p q parameters.2))
      (eccentricity, time) := analyticAt_fst.prod hmean
  unfold resonantEccentricAnomaly
  exact (analyticAt_eccentricAnomaly_joint heccentricity heccentricityOne).comp
    (f := fun parameters : ℝ × ℝ ↦
      (parameters.1, resonantMeanAnomaly p q parameters.2)) hparameters

/-- Each Cartesian coordinate of the oriented resonant ellipse is jointly analytic in
eccentricity and time. -/
theorem analyticAt_orientedResonantEllipsePosition_eccentricity_time_coordinate
    (p q : ℕ) {eccentricity orientation time : ℝ}
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (coordinate : Fin 2) :
    AnalyticAt ℝ (fun parameters : ℝ × ℝ ↦
      orientedResonantEllipsePosition p q parameters.1 orientation parameters.2 coordinate)
      (eccentricity, time) := by
  let anomaly : ℝ × ℝ → ℝ := fun parameters ↦
    resonantEccentricAnomaly p q parameters.1 parameters.2
  have hanomaly : AnalyticAt ℝ anomaly (eccentricity, time) :=
    analyticAt_resonantEccentricAnomaly_eccentricity_time p q
      heccentricity heccentricityOne
  have heccentricityCoordinate : AnalyticAt ℝ
      (fun parameters : ℝ × ℝ ↦ parameters.1) (eccentricity, time) := analyticAt_fst
  have htime : AnalyticAt ℝ
      (fun parameters : ℝ × ℝ ↦ parameters.2 - orientation) (eccentricity, time) :=
    analyticAt_snd.sub analyticAt_const
  have hsqrt : AnalyticAt ℝ (fun parameters : ℝ × ℝ ↦
      Real.sqrt (1 - parameters.1 ^ 2)) (eccentricity, time) := by
    exact (analyticAt_sqrt_of_pos (by nlinarith)).comp
      (f := fun parameters : ℝ × ℝ ↦ 1 - parameters.1 ^ 2)
      (analyticAt_const.sub (heccentricityCoordinate.pow 2))
  let inertialX : ℝ × ℝ → ℝ := fun parameters ↦
    resonantFirstAction p q ^ 2 *
      (Real.cos (anomaly parameters) - parameters.1)
  let inertialY : ℝ × ℝ → ℝ := fun parameters ↦
    resonantFirstAction p q ^ 2 * Real.sqrt (1 - parameters.1 ^ 2) *
      Real.sin (anomaly parameters)
  have hx : AnalyticAt ℝ inertialX (eccentricity, time) :=
    analyticAt_const.mul
      ((Real.analyticAt_cos.comp hanomaly).sub heccentricityCoordinate)
  have hy : AnalyticAt ℝ inertialY (eccentricity, time) :=
    (analyticAt_const.mul hsqrt).mul (Real.analyticAt_sin.comp hanomaly)
  fin_cases coordinate
  · change AnalyticAt ℝ (fun parameters : ℝ × ℝ ↦
      Real.cos (parameters.2 - orientation) * inertialX parameters +
        Real.sin (parameters.2 - orientation) * inertialY parameters)
      (eccentricity, time)
    exact ((Real.analyticAt_cos.comp htime).mul hx).add
      ((Real.analyticAt_sin.comp htime).mul hy)
  · change AnalyticAt ℝ (fun parameters : ℝ × ℝ ↦
      -Real.sin (parameters.2 - orientation) * inertialX parameters +
        Real.cos (parameters.2 - orientation) * inertialY parameters)
      (eccentricity, time)
    exact ((Real.analyticAt_sin.comp htime).neg.mul hx).add
      ((Real.analyticAt_cos.comp htime).mul hy)

/-- The disturbing function is jointly analytic at every point away from the unit primary. -/
theorem analyticAt_resonantDisturbingFunction_eccentricity_time_of_primaryDistance_ne_zero
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hprimaryNe :
      (orientedResonantEllipsePosition p q eccentricity orientation time 0 - 1) ^ 2 +
        orientedResonantEllipsePosition p q eccentricity orientation time 1 ^ 2 ≠ 0) :
    AnalyticAt ℝ (fun parameters : ℝ × ℝ ↦
      resonantDisturbingFunction p q parameters.1 orientation parameters.2)
      (eccentricity, time) := by
  let x : ℝ × ℝ → ℝ := fun parameters ↦
    orientedResonantEllipsePosition p q parameters.1 orientation parameters.2 0
  let y : ℝ × ℝ → ℝ := fun parameters ↦
    orientedResonantEllipsePosition p q parameters.1 orientation parameters.2 1
  have hx : AnalyticAt ℝ x (eccentricity, time) :=
    analyticAt_orientedResonantEllipsePosition_eccentricity_time_coordinate p q
      heccentricity heccentricityOne 0
  have hy : AnalyticAt ℝ y (eccentricity, time) :=
    analyticAt_orientedResonantEllipsePosition_eccentricity_time_coordinate p q
      heccentricity heccentricityOne 1
  have horiginSq : AnalyticAt ℝ
      (fun parameters ↦ x parameters ^ 2 + y parameters ^ 2) (eccentricity, time) :=
    (hx.pow 2).add (hy.pow 2)
  have hfirstAction : resonantFirstAction p q ≠ 0 :=
    (resonantFirstAction_pos hp hq).ne'
  have horiginPositive : 0 <
      x (eccentricity, time) ^ 2 + y (eccentricity, time) ^ 2 := by
    change 0 <
      (orientedResonantEllipsePosition p q eccentricity orientation time 0) ^ 2 +
        (orientedResonantEllipsePosition p q eccentricity orientation time 1) ^ 2
    rw [orientedResonantEllipsePosition_sq heccentricity.le heccentricityOne.le]
    exact sq_pos_of_pos
      (eccentricRadius_pos hfirstAction heccentricity.le heccentricityOne)
  have hinverseOrigin : AnalyticAt ℝ
      (fun parameters ↦ 1 / Real.sqrt (x parameters ^ 2 + y parameters ^ 2))
      (eccentricity, time) :=
    (analyticAt_inv_sqrt horiginPositive).comp
      (f := fun parameters ↦ x parameters ^ 2 + y parameters ^ 2) horiginSq
  have hprimarySq : AnalyticAt ℝ
      (fun parameters ↦ (x parameters - 1) ^ 2 + y parameters ^ 2)
      (eccentricity, time) := ((hx.sub analyticAt_const).pow 2).add (hy.pow 2)
  have hprimaryPositive : 0 <
      (x (eccentricity, time) - 1) ^ 2 + y (eccentricity, time) ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm hprimaryNe)
  have hinversePrimary : AnalyticAt ℝ
      (fun parameters ↦
        1 / Real.sqrt ((x parameters - 1) ^ 2 + y parameters ^ 2))
      (eccentricity, time) :=
    (analyticAt_inv_sqrt hprimaryPositive).comp
      (f := fun parameters ↦ (x parameters - 1) ^ 2 + y parameters ^ 2) hprimarySq
  have hraw := hinverseOrigin.add (hx.mul (hinverseOrigin.pow 3)) |>.sub hinversePrimary
  apply hraw.congr
  filter_upwards [] with parameters
  simp [x, y, resonantDisturbingFunction, orientedResonantEllipsePhasePoint,
    positionPhasePoint, firstMassPerturbation, div_eq_mul_inv]

/-- The collision-free disturbing function is jointly analytic in eccentricity and time. -/
theorem analyticAt_resonantDisturbingFunction_eccentricity_time
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    AnalyticAt ℝ (fun parameters : ℝ × ℝ ↦
      resonantDisturbingFunction p q parameters.1 orientation parameters.2)
      (eccentricity, time) := by
  apply analyticAt_resonantDisturbingFunction_eccentricity_time_of_primaryDistance_ne_zero
    hp hq heccentricity heccentricityOne
  exact orientedResonantEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one
    heccentricity.le heccentricityOne hapoapsis

/-- Joint analyticity assembled over the full admissible eccentricity/time cylinder. -/
theorem analyticOnNhd_resonantDisturbingFunction_eccentricity_time
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (orientation : ℝ) :
    AnalyticOnNhd ℝ
      (fun parameters : ℝ × ℝ ↦
        resonantDisturbingFunction p q parameters.1 orientation parameters.2)
      {parameters | 0 < parameters.1 ∧ parameters.1 < 1 ∧
        resonantFirstAction p q ^ 2 * (1 + parameters.1) < 1} := by
  intro parameters hparameters
  exact analyticAt_resonantDisturbingFunction_eccentricity_time hp hq
    hparameters.1 hparameters.2.1 hparameters.2.2

end LeanPool.PoincareThreeBody
