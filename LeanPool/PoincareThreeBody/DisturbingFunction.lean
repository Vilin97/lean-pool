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

end LeanPool.PoincareThreeBody
