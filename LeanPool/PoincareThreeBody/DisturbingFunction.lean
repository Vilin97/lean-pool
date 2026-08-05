/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.Averaging
import LeanPool.PoincareThreeBody.ResonantOrbit
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

lemma orientedResonantEllipsePosition_sq {p q : ℕ} {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity ≤ 1) :
    (orientedResonantEllipsePosition p q eccentricity orientation time 0) ^ 2 +
        (orientedResonantEllipsePosition p q eccentricity orientation time 1) ^ 2 =
      (eccentricRadius (resonantFirstAction p q) eccentricity
        (resonantEccentricAnomaly p q eccentricity time)) ^ 2 := by
  rw [orientedResonantEllipsePosition, positionInRotatingFrame_sq,
    inertialEllipsePosition_sq heccentricity heccentricityOne]

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

end LeanPool.PoincareThreeBody
