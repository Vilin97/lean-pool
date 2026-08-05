/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.Averaging
import LeanPool.PoincareThreeBody.ResonantOrbit
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring

/-!
# The resonant disturbing average

Rotating the inertial ellipse by an orientation phase produces the phase family on a resonant
torus. We define the first-order disturbing function on this family and its average over the common
period. Nonconstancy of this average is the concrete perturbative input in Poincaré's argument.
-/

namespace LeanPool.PoincareThreeBody

open MeasureTheory

/-- A resonant Kepler ellipse with an arbitrary inertial orientation phase. -/
noncomputable def orientedResonantEllipsePosition
    (p q : ℕ) (eccentricity orientation time : ℝ) : ActionSpace :=
  positionInRotatingFrame (time - orientation)
    (inertialEllipsePosition (resonantFirstAction p q) eccentricity
      (resonantEccentricAnomaly p q eccentricity time))

/-- The oriented resonant position embedded in phase space. -/
noncomputable def orientedResonantEllipsePhasePoint
    (p q : ℕ) (eccentricity orientation time : ℝ) :
    Challenge.PoincareThreeBody.PhaseSpace :=
  positionPhasePoint (orientedResonantEllipsePosition p q eccentricity orientation time)

/-- The first-order disturbing function along an oriented resonant ellipse. -/
noncomputable def resonantDisturbingFunction
    (p q : ℕ) (eccentricity orientation time : ℝ) : ℝ :=
  firstMassPerturbation
    (orientedResonantEllipsePhasePoint p q eccentricity orientation time)

/-- The disturbing function averaged over one common resonant period. -/
noncomputable def resonantDisturbingAverage
    (p q : ℕ) (eccentricity orientation : ℝ) : ℝ :=
  ∫ time in 0..resonantOrbitPeriod p,
    resonantDisturbingFunction p q eccentricity orientation time

/-- Orientation derivative of the disturbing function along a resonant ellipse. -/
noncomputable def resonantDisturbingOrientationDerivative
    (p q : ℕ) (eccentricity orientation time : ℝ) : ℝ :=
  let position := orientedResonantEllipsePosition p q eccentricity orientation time;
  -position 1 / (Real.sqrt ((position 0) ^ 2 + (position 1) ^ 2)) ^ 3 +
    position 1 /
      (Real.sqrt ((position 0 - 1) ^ 2 + (position 1) ^ 2)) ^ 3

lemma orientedResonantEllipsePosition_zero_orientation
    (p q : ℕ) (eccentricity time : ℝ) :
    orientedResonantEllipsePosition p q eccentricity 0 time =
      resonantRotatingEllipsePosition p q eccentricity time := by
  simp [orientedResonantEllipsePosition, resonantRotatingEllipsePosition,
    rotatingEllipsePosition]

lemma orientedResonantEllipsePosition_eq_fixedRotation
    (p q : ℕ) (eccentricity orientation time : ℝ) :
    orientedResonantEllipsePosition p q eccentricity orientation time =
      positionInRotatingFrame (-orientation)
        (resonantRotatingEllipsePosition p q eccentricity time) := by
  unfold orientedResonantEllipsePosition resonantRotatingEllipsePosition
    rotatingEllipsePosition
  rw [← positionInRotatingFrame_add]
  congr 1
  ring

theorem analyticAt_orientedResonantEllipsePosition_coordinate
    (p q : ℕ) {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (coordinate : Fin 2) :
    AnalyticAt ℝ (fun argument ↦
      orientedResonantEllipsePosition p q eccentricity orientation argument coordinate) time := by
  have hx := analyticAt_resonantRotatingEllipsePosition_coordinate p q
    (time := time) heccentricity heccentricityOne 0
  have hy := analyticAt_resonantRotatingEllipsePosition_coordinate p q
    (time := time) heccentricity heccentricityOne 1
  have hfunction :
      (fun argument ↦
        orientedResonantEllipsePosition p q eccentricity orientation argument coordinate) =
      (fun argument ↦ positionInRotatingFrame (-orientation)
        (resonantRotatingEllipsePosition p q eccentricity argument) coordinate) := by
    funext argument
    rw [orientedResonantEllipsePosition_eq_fixedRotation]
  rw [hfunction]
  fin_cases coordinate
  · change AnalyticAt ℝ (fun argument ↦
      Real.cos (-orientation) *
          resonantRotatingEllipsePosition p q eccentricity argument 0 +
        Real.sin (-orientation) *
          resonantRotatingEllipsePosition p q eccentricity argument 1) time
    exact (hx.const_smul (c := Real.cos (-orientation))).add
      (hy.const_smul (c := Real.sin (-orientation))) |>.congr (by
        filter_upwards [] with argument
        simp [smul_eq_mul])
  · change AnalyticAt ℝ (fun argument ↦
      -Real.sin (-orientation) *
          resonantRotatingEllipsePosition p q eccentricity argument 0 +
        Real.cos (-orientation) *
          resonantRotatingEllipsePosition p q eccentricity argument 1) time
    exact (hx.const_smul (c := -Real.sin (-orientation))).add
      (hy.const_smul (c := Real.cos (-orientation))) |>.congr (by
        filter_upwards [] with argument
        simp [smul_eq_mul])

theorem continuous_orientedResonantEllipsePosition_coordinate
    (p q : ℕ) {eccentricity : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (coordinate : Fin 2) :
    Continuous (fun parameters : ℝ × ℝ ↦
      orientedResonantEllipsePosition p q eccentricity parameters.1 parameters.2 coordinate) := by
  have hmean : Continuous (fun parameters : ℝ × ℝ ↦
      resonantMeanAnomaly p q parameters.2) := by
    unfold resonantMeanAnomaly resonantMeanMotion
    fun_prop
  have hanomaly : Continuous (fun parameters : ℝ × ℝ ↦
      resonantEccentricAnomaly p q eccentricity parameters.2) := by
    unfold resonantEccentricAnomaly
    exact (continuous_eccentricAnomaly heccentricity heccentricityOne).comp hmean
  unfold orientedResonantEllipsePosition positionInRotatingFrame inertialEllipsePosition
  fin_cases coordinate
  · simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, neg_mul, Fin.zero_eta]
    fun_prop
  · simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, neg_mul, Fin.mk_one]
    fun_prop

lemma orientedResonantEllipsePosition_sq {p q : ℕ} {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity ≤ 1) :
    (orientedResonantEllipsePosition p q eccentricity orientation time 0) ^ 2 +
        (orientedResonantEllipsePosition p q eccentricity orientation time 1) ^ 2 =
      (eccentricRadius (resonantFirstAction p q) eccentricity
        (resonantEccentricAnomaly p q eccentricity time)) ^ 2 := by
  rw [orientedResonantEllipsePosition, positionInRotatingFrame_sq,
    inertialEllipsePosition_sq heccentricity heccentricityOne]

theorem continuous_resonantDisturbingOrientationDerivative
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    Continuous (fun parameters : ℝ × ℝ ↦
      resonantDisturbingOrientationDerivative p q eccentricity parameters.1 parameters.2) := by
  let x : ℝ × ℝ → ℝ := fun parameters ↦
    orientedResonantEllipsePosition p q eccentricity parameters.1 parameters.2 0
  let y : ℝ × ℝ → ℝ := fun parameters ↦
    orientedResonantEllipsePosition p q eccentricity parameters.1 parameters.2 1
  have hx : Continuous x :=
    continuous_orientedResonantEllipsePosition_coordinate p q heccentricity
      heccentricityOne 0
  have hy : Continuous y :=
    continuous_orientedResonantEllipsePosition_coordinate p q heccentricity
      heccentricityOne 1
  have horiginSq : Continuous (fun parameters ↦ x parameters ^ 2 + y parameters ^ 2) :=
    (hx.pow 2).add (hy.pow 2)
  have hfirstAction : resonantFirstAction p q ≠ 0 :=
    (resonantFirstAction_pos hp hq).ne'
  have horiginPositive : ∀ parameters, 0 < x parameters ^ 2 + y parameters ^ 2 := by
    intro parameters
    change 0 <
      (orientedResonantEllipsePosition p q eccentricity parameters.1 parameters.2 0) ^ 2 +
        (orientedResonantEllipsePosition p q eccentricity parameters.1 parameters.2 1) ^ 2
    rw [orientedResonantEllipsePosition_sq heccentricity heccentricityOne.le]
    exact sq_pos_of_pos (eccentricRadius_pos hfirstAction heccentricity heccentricityOne)
  have hinverseOrigin : Continuous
      (fun parameters ↦ 1 / Real.sqrt (x parameters ^ 2 + y parameters ^ 2)) := by
    have hroot := horiginSq.sqrt
    have hrootNe : ∀ parameters,
        Real.sqrt (x parameters ^ 2 + y parameters ^ 2) ≠ 0 := fun parameters ↦
      Real.sqrt_ne_zero'.mpr (horiginPositive parameters)
    apply hroot.inv₀ hrootNe |>.congr
    intro parameters
    simp [one_div]
  have hone : Continuous (fun _ : ℝ × ℝ ↦ (1 : ℝ)) := continuous_const
  have hprimarySq : Continuous
      (fun parameters ↦ (x parameters - 1) ^ 2 + y parameters ^ 2) :=
    ((hx.sub hone).pow 2).add (hy.pow 2)
  have hprimaryNe : ∀ parameters,
      (x parameters - 1) ^ 2 + y parameters ^ 2 ≠ 0 := by
    intro parameters
    exact rotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one heccentricity
      heccentricityOne hapoapsis
  have hinversePrimary : Continuous
      (fun parameters ↦ 1 / Real.sqrt ((x parameters - 1) ^ 2 + y parameters ^ 2)) := by
    have hroot := hprimarySq.sqrt
    have hrootNe : ∀ parameters,
        Real.sqrt ((x parameters - 1) ^ 2 + y parameters ^ 2) ≠ 0 := fun parameters ↦
      Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (by positivity)
        (Ne.symm (hprimaryNe parameters)))
    apply hroot.inv₀ hrootNe |>.congr
    intro parameters
    simp [one_div]
  have hraw := (hy.neg.mul (hinverseOrigin.pow 3)).add
    (hy.mul (hinversePrimary.pow 3))
  apply hraw.congr
  intro parameters
  simp [resonantDisturbingOrientationDerivative, x, y, div_eq_mul_inv]

theorem hasDerivAt_orientedResonantEllipsePosition_zero_orientation
    (p q : ℕ) (eccentricity orientation time : ℝ) :
    HasDerivAt
      (fun phase ↦ orientedResonantEllipsePosition p q eccentricity phase time 0)
      (-orientedResonantEllipsePosition p q eccentricity orientation time 1) orientation := by
  let position := inertialEllipsePosition (resonantFirstAction p q) eccentricity
    (resonantEccentricAnomaly p q eccentricity time)
  have hangle : HasDerivAt (fun phase : ℝ ↦ time - phase) (-1) orientation := by
    have hraw := (hasDerivAt_const orientation time).sub (hasDerivAt_id orientation)
    exact hraw.congr_deriv (by ring)
  have hcos := (Real.hasDerivAt_cos (time - orientation)).comp orientation hangle
  have hsin := (Real.hasDerivAt_sin (time - orientation)).comp orientation hangle
  have hraw := (hcos.mul_const (position 0)).add (hsin.mul_const (position 1))
  apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards [] with phase
    rfl
  · unfold orientedResonantEllipsePosition positionInRotatingFrame
    dsimp [position]
    ring

theorem hasDerivAt_orientedResonantEllipsePosition_one_orientation
    (p q : ℕ) (eccentricity orientation time : ℝ) :
    HasDerivAt
      (fun phase ↦ orientedResonantEllipsePosition p q eccentricity phase time 1)
      (orientedResonantEllipsePosition p q eccentricity orientation time 0) orientation := by
  let position := inertialEllipsePosition (resonantFirstAction p q) eccentricity
    (resonantEccentricAnomaly p q eccentricity time)
  have hangle : HasDerivAt (fun phase : ℝ ↦ time - phase) (-1) orientation := by
    have hraw := (hasDerivAt_const orientation time).sub (hasDerivAt_id orientation)
    exact hraw.congr_deriv (by ring)
  have hcos := (Real.hasDerivAt_cos (time - orientation)).comp orientation hangle
  have hsin := (Real.hasDerivAt_sin (time - orientation)).comp orientation hangle
  have hraw := (hsin.neg.mul_const (position 0)).add (hcos.mul_const (position 1))
  apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards [] with phase
    rfl
  · unfold orientedResonantEllipsePosition positionInRotatingFrame
    dsimp [position]
    ring

/-- Differentiating the disturbing function with respect to the ellipse orientation gives the
explicit rotational derivative. -/
theorem hasDerivAt_resonantDisturbingFunction_orientation
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    HasDerivAt
      (fun phase ↦ resonantDisturbingFunction p q eccentricity phase time)
      (resonantDisturbingOrientationDerivative p q eccentricity orientation time)
      orientation := by
  let x : ℝ → ℝ := fun phase ↦
    orientedResonantEllipsePosition p q eccentricity phase time 0
  let y : ℝ → ℝ := fun phase ↦
    orientedResonantEllipsePosition p q eccentricity phase time 1
  have hx : HasDerivAt x (-y orientation) orientation :=
    hasDerivAt_orientedResonantEllipsePosition_zero_orientation p q eccentricity
      orientation time
  have hy : HasDerivAt y (x orientation) orientation :=
    hasDerivAt_orientedResonantEllipsePosition_one_orientation p q eccentricity
      orientation time
  have horiginRaw := (hx.pow 2).add (hy.pow 2)
  have horigin : HasDerivAt (fun phase ↦ x phase ^ 2 + y phase ^ 2) 0 orientation := by
    apply (horiginRaw.congr_deriv (by ring)).congr_of_eventuallyEq
    filter_upwards [] with phase
    simp
  have hprimaryRaw := ((hx.sub_const 1).pow 2).add (hy.pow 2)
  have hprimary : HasDerivAt
      (fun phase ↦ (x phase - 1) ^ 2 + y phase ^ 2) (2 * y orientation)
      orientation := by
    apply (hprimaryRaw.congr_deriv (by ring)).congr_of_eventuallyEq
    filter_upwards [] with phase
    simp
  have hfirstAction : resonantFirstAction p q ≠ 0 :=
    (resonantFirstAction_pos hp hq).ne'
  have hradius := eccentricRadius_pos (anomaly :=
      resonantEccentricAnomaly p q eccentricity time) hfirstAction heccentricity
    heccentricityOne
  have horiginPositive : 0 < x orientation ^ 2 + y orientation ^ 2 := by
    change 0 <
      (orientedResonantEllipsePosition p q eccentricity orientation time 0) ^ 2 +
        (orientedResonantEllipsePosition p q eccentricity orientation time 1) ^ 2
    rw [orientedResonantEllipsePosition_sq heccentricity heccentricityOne.le]
    exact sq_pos_of_pos hradius
  have hprimaryNe : (x orientation - 1) ^ 2 + y orientation ^ 2 ≠ 0 :=
    rotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one heccentricity
      heccentricityOne hapoapsis
  have hprimaryPositive : 0 < (x orientation - 1) ^ 2 + y orientation ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm hprimaryNe)
  have hinverseOriginRaw := hasDerivAt_inverseSqrt_comp horigin horiginPositive
  have hinverseOrigin : HasDerivAt
      (fun phase ↦ 1 / Real.sqrt (x phase ^ 2 + y phase ^ 2)) 0 orientation := by
    exact hinverseOriginRaw.congr_deriv (by simp)
  have hinversePrimaryRaw := hasDerivAt_inverseSqrt_comp hprimary hprimaryPositive
  have hprimaryRoot : Real.sqrt ((x orientation - 1) ^ 2 + y orientation ^ 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hprimaryPositive
  have hinversePrimary : HasDerivAt
      (fun phase ↦ 1 / Real.sqrt ((x phase - 1) ^ 2 + y phase ^ 2))
      (-y orientation /
        (Real.sqrt ((x orientation - 1) ^ 2 + y orientation ^ 2)) ^ 3) orientation := by
    apply hinversePrimaryRaw.congr_deriv
    field_simp [hprimaryRoot]
  have hxOverOriginCubeRaw := hx.mul (hinverseOrigin.pow 3)
  have hxOverOriginCube : HasDerivAt
      (fun phase ↦ x phase /
        (Real.sqrt (x phase ^ 2 + y phase ^ 2)) ^ 3)
      (-y orientation /
        (Real.sqrt (x orientation ^ 2 + y orientation ^ 2)) ^ 3) orientation := by
    apply (hxOverOriginCubeRaw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with phase
      simp [div_eq_mul_inv]
    · simp [div_eq_mul_inv]
  have hraw := hinverseOrigin.add hxOverOriginCube |>.sub hinversePrimary
  apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards [] with phase
    simp [resonantDisturbingFunction, orientedResonantEllipsePhasePoint,
      positionPhasePoint, firstMassPerturbation, x, y]
  · simp [resonantDisturbingOrientationDerivative, x, y]
    ring

theorem analyticAt_resonantDisturbingOrientationDerivative
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    AnalyticAt ℝ
      (resonantDisturbingOrientationDerivative p q eccentricity orientation) time := by
  let x : ℝ → ℝ := fun argument ↦
    orientedResonantEllipsePosition p q eccentricity orientation argument 0
  let y : ℝ → ℝ := fun argument ↦
    orientedResonantEllipsePosition p q eccentricity orientation argument 1
  have hx : AnalyticAt ℝ x time :=
    analyticAt_orientedResonantEllipsePosition_coordinate p q heccentricity
      heccentricityOne 0
  have hy : AnalyticAt ℝ y time :=
    analyticAt_orientedResonantEllipsePosition_coordinate p q heccentricity
      heccentricityOne 1
  have horiginSq : AnalyticAt ℝ (fun argument ↦ x argument ^ 2 + y argument ^ 2)
      time := (hx.pow 2).add (hy.pow 2)
  have hfirstAction : resonantFirstAction p q ≠ 0 :=
    (resonantFirstAction_pos hp hq).ne'
  have hradius := eccentricRadius_pos (anomaly :=
      resonantEccentricAnomaly p q eccentricity time) hfirstAction heccentricity
    heccentricityOne
  have horiginPositive : 0 < x time ^ 2 + y time ^ 2 := by
    change 0 <
      (orientedResonantEllipsePosition p q eccentricity orientation time 0) ^ 2 +
        (orientedResonantEllipsePosition p q eccentricity orientation time 1) ^ 2
    rw [orientedResonantEllipsePosition_sq heccentricity heccentricityOne.le]
    exact sq_pos_of_pos hradius
  have hinverseOrigin : AnalyticAt ℝ
      (fun argument ↦ 1 / Real.sqrt (x argument ^ 2 + y argument ^ 2)) time := by
    change AnalyticAt ℝ
      ((fun value : ℝ ↦ 1 / Real.sqrt value) ∘
        (fun argument ↦ x argument ^ 2 + y argument ^ 2)) time
    exact (analyticAt_inv_sqrt horiginPositive).comp
      (f := fun argument ↦ x argument ^ 2 + y argument ^ 2) horiginSq
  have hone : AnalyticAt ℝ (fun _ : ℝ ↦ (1 : ℝ)) time := analyticAt_const
  have hprimarySq : AnalyticAt ℝ
      (fun argument ↦ (x argument - 1) ^ 2 + y argument ^ 2) time :=
    ((hx.sub hone).pow 2).add (hy.pow 2)
  have hprimaryNe : (x time - 1) ^ 2 + y time ^ 2 ≠ 0 :=
    rotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one heccentricity
      heccentricityOne hapoapsis
  have hprimaryPositive : 0 < (x time - 1) ^ 2 + y time ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm hprimaryNe)
  have hinversePrimary : AnalyticAt ℝ
      (fun argument ↦ 1 / Real.sqrt ((x argument - 1) ^ 2 + y argument ^ 2)) time := by
    change AnalyticAt ℝ
      ((fun value : ℝ ↦ 1 / Real.sqrt value) ∘
        (fun argument ↦ (x argument - 1) ^ 2 + y argument ^ 2)) time
    exact (analyticAt_inv_sqrt hprimaryPositive).comp
      (f := fun argument ↦ (x argument - 1) ^ 2 + y argument ^ 2) hprimarySq
  have hraw := (hy.neg.mul (hinverseOrigin.pow 3)).add
    (hy.mul (hinversePrimary.pow 3))
  apply hraw.congr
  filter_upwards [] with argument
  simp [resonantDisturbingOrientationDerivative, x, y, div_eq_mul_inv]

theorem intervalIntegrable_resonantDisturbingOrientationDerivative
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation start finish : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    IntervalIntegrable
      (resonantDisturbingOrientationDerivative p q eccentricity orientation)
      volume start finish := by
  apply Continuous.intervalIntegrable _ start finish
  rw [continuous_iff_continuousAt]
  intro time
  exact (analyticAt_resonantDisturbingOrientationDerivative hp hq heccentricity
    heccentricityOne hapoapsis).continuousAt

theorem analyticAt_resonantDisturbingFunction_time
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    AnalyticAt ℝ (resonantDisturbingFunction p q eccentricity orientation) time := by
  let x : ℝ → ℝ := fun argument ↦
    orientedResonantEllipsePosition p q eccentricity orientation argument 0
  let y : ℝ → ℝ := fun argument ↦
    orientedResonantEllipsePosition p q eccentricity orientation argument 1
  have hx : AnalyticAt ℝ x time :=
    analyticAt_orientedResonantEllipsePosition_coordinate p q heccentricity
      heccentricityOne 0
  have hy : AnalyticAt ℝ y time :=
    analyticAt_orientedResonantEllipsePosition_coordinate p q heccentricity
      heccentricityOne 1
  have horiginSq : AnalyticAt ℝ (fun argument ↦ x argument ^ 2 + y argument ^ 2)
      time := (hx.pow 2).add (hy.pow 2)
  have hfirstAction : resonantFirstAction p q ≠ 0 :=
    (resonantFirstAction_pos hp hq).ne'
  have hradius := eccentricRadius_pos (anomaly :=
      resonantEccentricAnomaly p q eccentricity time) hfirstAction heccentricity
    heccentricityOne
  have horiginPositive : 0 < x time ^ 2 + y time ^ 2 := by
    change 0 <
      (orientedResonantEllipsePosition p q eccentricity orientation time 0) ^ 2 +
        (orientedResonantEllipsePosition p q eccentricity orientation time 1) ^ 2
    rw [orientedResonantEllipsePosition_sq heccentricity heccentricityOne.le]
    exact sq_pos_of_pos hradius
  have hinverseOrigin : AnalyticAt ℝ
      (fun argument ↦ 1 / Real.sqrt (x argument ^ 2 + y argument ^ 2)) time := by
    change AnalyticAt ℝ
      ((fun value : ℝ ↦ 1 / Real.sqrt value) ∘
        (fun argument ↦ x argument ^ 2 + y argument ^ 2)) time
    exact (analyticAt_inv_sqrt horiginPositive).comp
      (f := fun argument ↦ x argument ^ 2 + y argument ^ 2) horiginSq
  have hone : AnalyticAt ℝ (fun _ : ℝ ↦ (1 : ℝ)) time := analyticAt_const
  have hprimarySq : AnalyticAt ℝ
      (fun argument ↦ (x argument - 1) ^ 2 + y argument ^ 2) time :=
    ((hx.sub hone).pow 2).add (hy.pow 2)
  have hprimaryNe : (x time - 1) ^ 2 + y time ^ 2 ≠ 0 :=
    rotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one heccentricity
      heccentricityOne hapoapsis
  have hprimaryPositive : 0 < (x time - 1) ^ 2 + y time ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm hprimaryNe)
  have hinversePrimary : AnalyticAt ℝ
      (fun argument ↦ 1 / Real.sqrt ((x argument - 1) ^ 2 + y argument ^ 2)) time := by
    change AnalyticAt ℝ
      ((fun value : ℝ ↦ 1 / Real.sqrt value) ∘
        (fun argument ↦ (x argument - 1) ^ 2 + y argument ^ 2)) time
    exact (analyticAt_inv_sqrt hprimaryPositive).comp
      (f := fun argument ↦ (x argument - 1) ^ 2 + y argument ^ 2) hprimarySq
  have hraw := hinverseOrigin.add (hx.mul (hinverseOrigin.pow 3)) |>.sub hinversePrimary
  apply hraw.congr
  filter_upwards [] with argument
  simp [resonantDisturbingFunction, orientedResonantEllipsePhasePoint,
    positionPhasePoint, firstMassPerturbation, x, y, div_eq_mul_inv]

theorem intervalIntegrable_resonantDisturbingFunction
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation start finish : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    IntervalIntegrable (resonantDisturbingFunction p q eccentricity orientation)
      volume start finish := by
  apply Continuous.intervalIntegrable _ start finish
  rw [continuous_iff_continuousAt]
  intro time
  exact (analyticAt_resonantDisturbingFunction_time hp hq heccentricity
    heccentricityOne hapoapsis).continuousAt

lemma orientedResonantEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one
    {p q : ℕ} {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    (orientedResonantEllipsePosition p q eccentricity orientation time 0 - 1) ^ 2 +
        (orientedResonantEllipsePosition p q eccentricity orientation time 1) ^ 2 ≠ 0 := by
  exact rotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one heccentricity
    heccentricityOne hapoapsis

lemma orientedResonantEllipsePosition_add_orientation_two_pi
    (p q : ℕ) (eccentricity orientation time : ℝ) :
    orientedResonantEllipsePosition p q eccentricity (orientation + 2 * Real.pi) time =
      orientedResonantEllipsePosition p q eccentricity orientation time := by
  have hangle : time - (orientation + 2 * Real.pi) =
      (time - orientation) - 2 * Real.pi := by ring
  unfold orientedResonantEllipsePosition positionInRotatingFrame
  rw [hangle]
  funext coordinate
  fin_cases coordinate <;> simp

lemma orientedResonantEllipsePosition_add_period {p q : ℕ} (hp : 0 < p)
    {eccentricity orientation : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) (time : ℝ) :
    orientedResonantEllipsePosition p q eccentricity orientation
        (time + resonantOrbitPeriod p) =
      orientedResonantEllipsePosition p q eccentricity orientation time := by
  unfold orientedResonantEllipsePosition positionInRotatingFrame
  rw [resonantEccentricAnomaly_add_period hp heccentricity heccentricityOne]
  unfold resonantOrbitPeriod
  have hangle : time + 2 * Real.pi * (p : ℝ) - orientation =
      (time - orientation) + (p : ℝ) * (2 * Real.pi) := by ring
  rw [hangle]
  funext coordinate
  fin_cases coordinate <;> simp [inertialEllipsePosition]

lemma resonantDisturbingFunction_add_orientation_two_pi
    (p q : ℕ) (eccentricity orientation time : ℝ) :
    resonantDisturbingFunction p q eccentricity (orientation + 2 * Real.pi) time =
      resonantDisturbingFunction p q eccentricity orientation time := by
  unfold resonantDisturbingFunction orientedResonantEllipsePhasePoint
  rw [orientedResonantEllipsePosition_add_orientation_two_pi]

lemma resonantDisturbingFunction_add_period {p q : ℕ} (hp : 0 < p)
    {eccentricity orientation : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) (time : ℝ) :
    resonantDisturbingFunction p q eccentricity orientation
        (time + resonantOrbitPeriod p) =
      resonantDisturbingFunction p q eccentricity orientation time := by
  unfold resonantDisturbingFunction orientedResonantEllipsePhasePoint
  rw [orientedResonantEllipsePosition_add_period hp heccentricity heccentricityOne]

lemma resonantDisturbingAverage_add_orientation_two_pi
    (p q : ℕ) (eccentricity orientation : ℝ) :
    resonantDisturbingAverage p q eccentricity (orientation + 2 * Real.pi) =
      resonantDisturbingAverage p q eccentricity orientation := by
  apply intervalIntegral.integral_congr
  intro time _
  exact resonantDisturbingFunction_add_orientation_two_pi p q eccentricity orientation time

/-- Differentiation under the period integral identifies the derivative of the Poincaré
disturbing average with the integral of the explicit orientation forcing. -/
theorem hasDerivAt_resonantDisturbingAverage
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity orientation : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    HasDerivAt (resonantDisturbingAverage p q eccentricity)
      (∫ time in 0..resonantOrbitPeriod p,
        resonantDisturbingOrientationDerivative p q eccentricity orientation time)
      orientation := by
  let phaseInterval : Set ℝ := Set.Icc (orientation - 1) (orientation + 1)
  let timeInterval : Set ℝ := Set.uIcc 0 (resonantOrbitPeriod p)
  let parameterRectangle : Set (ℝ × ℝ) := phaseInterval ×ˢ timeInterval
  have hrectangleCompact : IsCompact parameterRectangle :=
    isCompact_Icc.prod isCompact_uIcc
  have hforcingContinuous :=
    continuous_resonantDisturbingOrientationDerivative hp hq heccentricity
      heccentricityOne hapoapsis
  obtain ⟨bound, hbound⟩ := hrectangleCompact.bddAbove_image
    hforcingContinuous.norm.continuousOn
  have hnormBound : ∀ phase ∈ phaseInterval, ∀ time ∈ timeInterval,
      ‖resonantDisturbingOrientationDerivative p q eccentricity phase time‖ ≤ bound := by
    intro phase hphase time htime
    apply hbound
    exact ⟨⟨phase, time⟩, ⟨hphase, htime⟩, rfl⟩
  have hphaseNhd : phaseInterval ∈ nhds orientation := by
    change Set.Icc (orientation - 1) (orientation + 1) ∈ nhds orientation
    exact Icc_mem_nhds (by linarith) (by linarith)
  have hfunctionMeasurable : ∀ᶠ phase in nhds orientation,
      AEStronglyMeasurable
        (resonantDisturbingFunction p q eccentricity phase)
        (volume.restrict (Set.uIoc 0 (resonantOrbitPeriod p))) := by
    filter_upwards [] with phase
    have hcontinuous : Continuous (resonantDisturbingFunction p q eccentricity phase) := by
      rw [continuous_iff_continuousAt]
      intro time
      exact (analyticAt_resonantDisturbingFunction_time hp hq heccentricity
        heccentricityOne hapoapsis).continuousAt
    exact hcontinuous.aestronglyMeasurable.restrict
  have hfunctionIntegrable : IntervalIntegrable
      (resonantDisturbingFunction p q eccentricity orientation) volume 0
      (resonantOrbitPeriod p) :=
    intervalIntegrable_resonantDisturbingFunction hp hq heccentricity
      heccentricityOne hapoapsis
  have hderivativeMeasurable : AEStronglyMeasurable
      (resonantDisturbingOrientationDerivative p q eccentricity orientation)
      (volume.restrict (Set.uIoc 0 (resonantOrbitPeriod p))) := by
    have hcontinuous : Continuous
        (resonantDisturbingOrientationDerivative p q eccentricity orientation) := by
      rw [continuous_iff_continuousAt]
      intro time
      exact (analyticAt_resonantDisturbingOrientationDerivative hp hq heccentricity
        heccentricityOne hapoapsis).continuousAt
    exact hcontinuous.aestronglyMeasurable.restrict
  have hboundAE : ∀ᵐ time ∂volume, time ∈ Set.uIoc 0 (resonantOrbitPeriod p) →
      ∀ phase ∈ phaseInterval,
        ‖resonantDisturbingOrientationDerivative p q eccentricity phase time‖ ≤ bound := by
    filter_upwards [] with time htime phase hphase
    exact hnormBound phase hphase time (Set.uIoc_subset_uIcc htime)
  have hboundIntegrable : IntervalIntegrable (fun _ : ℝ ↦ bound) volume 0
      (resonantOrbitPeriod p) := intervalIntegrable_const
  have hderivative : ∀ᵐ time ∂volume, time ∈ Set.uIoc 0 (resonantOrbitPeriod p) →
      ∀ phase ∈ phaseInterval,
        HasDerivAt (fun parameter ↦
          resonantDisturbingFunction p q eccentricity parameter time)
          (resonantDisturbingOrientationDerivative p q eccentricity phase time) phase := by
    filter_upwards [] with time _ phase _
    exact hasDerivAt_resonantDisturbingFunction_orientation hp hq heccentricity
      heccentricityOne hapoapsis
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun phase time ↦ resonantDisturbingFunction p q eccentricity phase time)
    (F' := fun phase time ↦
      resonantDisturbingOrientationDerivative p q eccentricity phase time)
    (bound := fun _ ↦ bound) hphaseNhd hfunctionMeasurable hfunctionIntegrable
      hderivativeMeasurable hboundAE hboundIntegrable hderivative).2

theorem deriv_resonantDisturbingAverage
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity orientation : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    deriv (resonantDisturbingAverage p q eccentricity) orientation =
      ∫ time in 0..resonantOrbitPeriod p,
        resonantDisturbingOrientationDerivative p q eccentricity orientation time :=
  (hasDerivAt_resonantDisturbingAverage hp hq heccentricity heccentricityOne hapoapsis).deriv

theorem differentiable_resonantDisturbingAverage
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    Differentiable ℝ (resonantDisturbingAverage p q eccentricity) := by
  intro orientation
  exact (hasDerivAt_resonantDisturbingAverage hp hq heccentricity heccentricityOne
    hapoapsis).differentiableAt

/-- Distinct certified values of the Poincaré average imply a nonzero resonant forcing integral at
some orientation. This is the interface intended for exact analytic estimates or validated finite
computation. -/
theorem exists_deriv_resonantDisturbingAverage_ne_zero_of_values_ne
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity phaseA phaseB : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1)
    (hvalues : resonantDisturbingAverage p q eccentricity phaseA ≠
      resonantDisturbingAverage p q eccentricity phaseB) :
  ∃ orientation,
      deriv (resonantDisturbingAverage p q eccentricity) orientation ≠ 0 := by
  by_contra hderivative
  push Not at hderivative
  apply hvalues
  exact is_const_of_deriv_eq_zero
    (differentiable_resonantDisturbingAverage hp hq heccentricity heccentricityOne hapoapsis)
    hderivative phaseA phaseB

/-- The averaged homological obstruction specialized to the explicit resonant disturbing
function. The remaining concrete input is nonvanishing of its orientation derivative integral. -/
theorem resonantDisturbingAverage_obstruction
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {differential : ActionSpace}
    {eccentricity orientation : ℝ} {correction correctionDerivative : ℝ → ℝ}
    (hderiv : ∀ time ∈ Set.uIcc 0 (resonantOrbitPeriod p),
      HasDerivAt correction (correctionDerivative time) time)
    (hcorrectionIntegrable : IntervalIntegrable correctionDerivative volume 0
      (resonantOrbitPeriod p))
    (hforcingIntegrable : IntervalIntegrable
      (resonantDisturbingOrientationDerivative p q eccentricity orientation) volume 0
      (resonantOrbitPeriod p))
    (hperiodic : correction (resonantOrbitPeriod p) = correction 0)
    (hforcing : ∫ time in 0..resonantOrbitPeriod p,
      resonantDisturbingOrientationDerivative p q eccentricity orientation time ≠ 0)
    (hequation : ∀ time ∈ Set.uIcc 0 (resonantOrbitPeriod p),
      correctionDerivative time + dot (resonanceVector p q) differential *
        resonantDisturbingOrientationDerivative p q eccentricity orientation time = 0) :
    ¬LinearIndependent ℝ
      ![delaunayFrequency (resonantFirstAction p q), differential] := by
  exact averagedHomologicalEquation_obstruction (resonanceVector_ne_zero hp)
    (resonantFirstAction_is_resonant hp hq) hderiv hcorrectionIntegrable
      hforcingIntegrable hperiodic hforcing hequation

/-- Collision-free interior ellipses automatically satisfy the integrability hypothesis in the
concrete averaged obstruction. -/
theorem resonantDisturbingAverage_obstruction_of_apoapsis_lt_one
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {differential : ActionSpace}
    {eccentricity orientation : ℝ} {correction correctionDerivative : ℝ → ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1)
    (hderiv : ∀ time ∈ Set.uIcc 0 (resonantOrbitPeriod p),
      HasDerivAt correction (correctionDerivative time) time)
    (hcorrectionIntegrable : IntervalIntegrable correctionDerivative volume 0
      (resonantOrbitPeriod p))
    (hperiodic : correction (resonantOrbitPeriod p) = correction 0)
    (hforcing : ∫ time in 0..resonantOrbitPeriod p,
      resonantDisturbingOrientationDerivative p q eccentricity orientation time ≠ 0)
    (hequation : ∀ time ∈ Set.uIcc 0 (resonantOrbitPeriod p),
      correctionDerivative time + dot (resonanceVector p q) differential *
        resonantDisturbingOrientationDerivative p q eccentricity orientation time = 0) :
    ¬LinearIndependent ℝ
      ![delaunayFrequency (resonantFirstAction p q), differential] := by
  apply resonantDisturbingAverage_obstruction hp hq hderiv hcorrectionIntegrable
    (intervalIntegrable_resonantDisturbingOrientationDerivative hp hq heccentricity
      heccentricityOne hapoapsis)
    hperiodic hforcing hequation

/-- Equivalent concrete obstruction using nonvanishing of the derivative of the Poincaré
disturbing average. -/
theorem resonantDisturbingAverage_deriv_obstruction
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {differential : ActionSpace}
    {eccentricity orientation : ℝ} {correction correctionDerivative : ℝ → ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1)
    (hderiv : ∀ time ∈ Set.uIcc 0 (resonantOrbitPeriod p),
      HasDerivAt correction (correctionDerivative time) time)
    (hcorrectionIntegrable : IntervalIntegrable correctionDerivative volume 0
      (resonantOrbitPeriod p))
    (hperiodic : correction (resonantOrbitPeriod p) = correction 0)
    (haverageDeriv :
      deriv (resonantDisturbingAverage p q eccentricity) orientation ≠ 0)
    (hequation : ∀ time ∈ Set.uIcc 0 (resonantOrbitPeriod p),
      correctionDerivative time + dot (resonanceVector p q) differential *
        resonantDisturbingOrientationDerivative p q eccentricity orientation time = 0) :
    ¬LinearIndependent ℝ
      ![delaunayFrequency (resonantFirstAction p q), differential] := by
  apply resonantDisturbingAverage_obstruction_of_apoapsis_lt_one hp hq heccentricity
    heccentricityOne hapoapsis hderiv hcorrectionIntegrable hperiodic
  · rwa [← deriv_resonantDisturbingAverage hp hq heccentricity heccentricityOne
      hapoapsis]
  · exact hequation

end LeanPool.PoincareThreeBody
