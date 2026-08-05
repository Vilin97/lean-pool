/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.RotatingEllipse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Periodic Kepler ellipses at rational Delaunay resonances

At the action `I₁³ = p / q`, the inertial ellipse makes `q` revolutions while the rotating
frame makes `p` revolutions during the common period `2πp`. This file constructs that orbit and
proves its periodicity exactly.
-/

namespace LeanPool.PoincareThreeBody

/-- Mean motion on the `(p,q)` Kepler resonance. -/
noncomputable def resonantMeanMotion (p q : ℕ) : ℝ :=
  (q : ℝ) / (p : ℝ)

/-- Common period of the inertial ellipse and rotating frame. -/
noncomputable def resonantOrbitPeriod (p : ℕ) : ℝ :=
  2 * Real.pi * p

/-- Mean anomaly along a resonant unperturbed orbit. -/
noncomputable def resonantMeanAnomaly (p q : ℕ) (time : ℝ) : ℝ :=
  resonantMeanMotion p q * time

/-- Eccentric anomaly along a resonant unperturbed orbit. -/
noncomputable def resonantEccentricAnomaly
    (p q : ℕ) (eccentricity time : ℝ) : ℝ :=
  eccentricAnomaly eccentricity (resonantMeanAnomaly p q time)

/-- Position of the resonant Kepler ellipse in the rotating frame. -/
noncomputable def resonantRotatingEllipsePosition
    (p q : ℕ) (eccentricity time : ℝ) : ActionSpace :=
  rotatingEllipsePosition (resonantFirstAction p q) eccentricity
    (resonantEccentricAnomaly p q eccentricity time) time

/-- The resonant position embedded into the four-dimensional phase space. -/
noncomputable def resonantEllipsePhasePoint
    (p q : ℕ) (eccentricity time : ℝ) : PhaseSpace :=
  positionPhasePoint (resonantRotatingEllipsePosition p q eccentricity time)

lemma resonantMeanMotion_eq_delaunayFrequency {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    resonantMeanMotion p q =
      delaunayFrequency (resonantFirstAction p q) 0 := by
  have hpReal : (p : ℝ) ≠ 0 := by positivity
  have hqReal : (q : ℝ) ≠ 0 := by positivity
  simp only [resonantMeanMotion, delaunayFrequency, Matrix.cons_val_zero]
  rw [resonantFirstAction_cube hp hq]
  field_simp

lemma resonantMeanAnomaly_add_period {p q : ℕ} (hp : 0 < p) (time : ℝ) :
    resonantMeanAnomaly p q (time + resonantOrbitPeriod p) =
      resonantMeanAnomaly p q time + q * (2 * Real.pi) := by
  have hpReal : (p : ℝ) ≠ 0 := by positivity
  unfold resonantMeanAnomaly resonantMeanMotion resonantOrbitPeriod
  field_simp

lemma resonantEccentricAnomaly_add_period {p q : ℕ} (hp : 0 < p)
    {eccentricity : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) (time : ℝ) :
    resonantEccentricAnomaly p q eccentricity (time + resonantOrbitPeriod p) =
      resonantEccentricAnomaly p q eccentricity time + q * (2 * Real.pi) := by
  unfold resonantEccentricAnomaly
  rw [resonantMeanAnomaly_add_period hp,
    eccentricAnomaly_add_nat_mul_two_pi q heccentricity heccentricityOne]

theorem analyticAt_resonantMeanAnomaly (p q : ℕ) (time : ℝ) :
    AnalyticAt ℝ (resonantMeanAnomaly p q) time := by
  have hid : AnalyticAt ℝ id time := analyticAt_id
  have hraw := hid.const_smul (c := resonantMeanMotion p q)
  apply hraw.congr
  filter_upwards [] with argument
  simp [resonantMeanAnomaly, smul_eq_mul]

theorem analyticAt_resonantEccentricAnomaly (p q : ℕ) {eccentricity time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    AnalyticAt ℝ (resonantEccentricAnomaly p q eccentricity) time := by
  exact (analyticAt_eccentricAnomaly
    (meanAnomaly := resonantMeanAnomaly p q time) heccentricity heccentricityOne).comp
      (analyticAt_resonantMeanAnomaly p q time)

theorem analyticAt_resonantRotatingEllipsePosition_coordinate
    (p q : ℕ) {eccentricity time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (coordinate : Fin 2) :
    AnalyticAt ℝ (fun argument ↦
      resonantRotatingEllipsePosition p q eccentricity argument coordinate) time := by
  let anomaly : ℝ → ℝ := resonantEccentricAnomaly p q eccentricity
  let firstAction := resonantFirstAction p q
  have hanomaly : AnalyticAt ℝ anomaly time :=
    analyticAt_resonantEccentricAnomaly p q heccentricity heccentricityOne
  have hcosAnomaly := Real.analyticAt_cos.comp hanomaly
  have hsinAnomaly := Real.analyticAt_sin.comp hanomaly
  have heccentricityConstant : AnalyticAt ℝ (fun _ : ℝ ↦ eccentricity) time :=
    analyticAt_const
  have hxRaw := (hcosAnomaly.sub heccentricityConstant).const_smul
    (c := firstAction ^ 2)
  have hx : AnalyticAt ℝ
      (fun argument ↦ firstAction ^ 2 * (Real.cos (anomaly argument) - eccentricity))
      time := by
    apply hxRaw.congr
    filter_upwards [] with argument
    simp [smul_eq_mul]
  have hyRaw := hsinAnomaly.const_smul
    (c := firstAction ^ 2 * Real.sqrt (1 - eccentricity ^ 2))
  have hy : AnalyticAt ℝ
      (fun argument ↦ firstAction ^ 2 * Real.sqrt (1 - eccentricity ^ 2) *
        Real.sin (anomaly argument)) time := by
    apply hyRaw.congr
    filter_upwards [] with argument
    simp [smul_eq_mul]
  have hcosTime : AnalyticAt ℝ Real.cos time := Real.analyticAt_cos
  have hsinTime : AnalyticAt ℝ Real.sin time := Real.analyticAt_sin
  fin_cases coordinate
  · change AnalyticAt ℝ
      (fun argument ↦ Real.cos argument *
          (firstAction ^ 2 * (Real.cos (anomaly argument) - eccentricity)) +
        Real.sin argument *
          (firstAction ^ 2 * Real.sqrt (1 - eccentricity ^ 2) *
            Real.sin (anomaly argument))) time
    exact (hcosTime.mul hx).add (hsinTime.mul hy)
  · change AnalyticAt ℝ
      (fun argument ↦ -Real.sin argument *
          (firstAction ^ 2 * (Real.cos (anomaly argument) - eccentricity)) +
        Real.cos argument *
          (firstAction ^ 2 * Real.sqrt (1 - eccentricity ^ 2) *
            Real.sin (anomaly argument))) time
    exact (hsinTime.neg.mul hx).add (hcosTime.mul hy)

/-- Away from a collision with the unit primary, the disturbing function restricted to a resonant
ellipse is real analytic in time. -/
theorem analyticAt_firstMassPerturbation_resonantOrbit
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hprimary :
      (resonantRotatingEllipsePosition p q eccentricity time 0 - 1) ^ 2 +
          (resonantRotatingEllipsePosition p q eccentricity time 1) ^ 2 ≠ 0) :
    AnalyticAt ℝ (fun argument ↦ firstMassPerturbation
      (resonantEllipsePhasePoint p q eccentricity argument)) time := by
  let x : ℝ → ℝ := fun argument ↦
    resonantRotatingEllipsePosition p q eccentricity argument 0
  let y : ℝ → ℝ := fun argument ↦
    resonantRotatingEllipsePosition p q eccentricity argument 1
  have hx : AnalyticAt ℝ x time :=
    analyticAt_resonantRotatingEllipsePosition_coordinate p q heccentricity
      heccentricityOne 0
  have hy : AnalyticAt ℝ y time :=
    analyticAt_resonantRotatingEllipsePosition_coordinate p q heccentricity
      heccentricityOne 1
  have horiginSq : AnalyticAt ℝ (fun argument ↦ x argument ^ 2 + y argument ^ 2)
      time := (hx.pow 2).add (hy.pow 2)
  have hfirstAction : resonantFirstAction p q ≠ 0 :=
    (resonantFirstAction_pos hp hq).ne'
  have hradius := eccentricRadius_pos (anomaly :=
      resonantEccentricAnomaly p q eccentricity time) hfirstAction heccentricity
    heccentricityOne
  have horiginValue : 0 < x time ^ 2 + y time ^ 2 := by
    change 0 <
      (rotatingEllipsePosition (resonantFirstAction p q) eccentricity
          (resonantEccentricAnomaly p q eccentricity time) time 0) ^ 2 +
        (rotatingEllipsePosition (resonantFirstAction p q) eccentricity
          (resonantEccentricAnomaly p q eccentricity time) time 1) ^ 2
    rw [rotatingEllipsePosition_sq heccentricity heccentricityOne.le]
    exact sq_pos_of_pos hradius
  have hinverseOrigin : AnalyticAt ℝ
      (fun argument ↦ 1 / Real.sqrt (x argument ^ 2 + y argument ^ 2)) time := by
    change AnalyticAt ℝ
      ((fun value : ℝ ↦ 1 / Real.sqrt value) ∘
        (fun argument ↦ x argument ^ 2 + y argument ^ 2)) time
    exact (analyticAt_inv_sqrt horiginValue).comp
      (f := fun argument ↦ x argument ^ 2 + y argument ^ 2) horiginSq
  have hone : AnalyticAt ℝ (fun _ : ℝ ↦ (1 : ℝ)) time := analyticAt_const
  have hprimarySq : AnalyticAt ℝ
      (fun argument ↦ (x argument - 1) ^ 2 + y argument ^ 2) time :=
    ((hx.sub hone).pow 2).add (hy.pow 2)
  have hprimaryValue : 0 < (x time - 1) ^ 2 + y time ^ 2 := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hprimary)
  have hinversePrimary : AnalyticAt ℝ
      (fun argument ↦ 1 / Real.sqrt ((x argument - 1) ^ 2 + y argument ^ 2)) time := by
    change AnalyticAt ℝ
      ((fun value : ℝ ↦ 1 / Real.sqrt value) ∘
        (fun argument ↦ (x argument - 1) ^ 2 + y argument ^ 2)) time
    exact (analyticAt_inv_sqrt hprimaryValue).comp
      (f := fun argument ↦ (x argument - 1) ^ 2 + y argument ^ 2) hprimarySq
  have hraw := hinverseOrigin.add (hx.mul (hinverseOrigin.pow 3)) |>.sub hinversePrimary
  apply hraw.congr
  filter_upwards [] with argument
  simp [x, y, resonantEllipsePhasePoint, positionPhasePoint, firstMassPerturbation,
    div_eq_mul_inv]

theorem intervalIntegrable_firstMassPerturbation_resonantOrbit
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity start finish : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hprimary : ∀ time ∈ Set.uIcc start finish,
      (resonantRotatingEllipsePosition p q eccentricity time 0 - 1) ^ 2 +
          (resonantRotatingEllipsePosition p q eccentricity time 1) ^ 2 ≠ 0) :
    IntervalIntegrable
      (fun time ↦ firstMassPerturbation
        (resonantEllipsePhasePoint p q eccentricity time))
      MeasureTheory.volume start finish := by
  apply ContinuousOn.intervalIntegrable
  intro time htime
  exact (analyticAt_firstMassPerturbation_resonantOrbit hp hq heccentricity
    heccentricityOne (hprimary time htime)).continuousAt.continuousWithinAt

lemma resonantRotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one
    {p q : ℕ} {eccentricity time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    (resonantRotatingEllipsePosition p q eccentricity time 0 - 1) ^ 2 +
        (resonantRotatingEllipsePosition p q eccentricity time 1) ^ 2 ≠ 0 := by
  exact rotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one heccentricity
    heccentricityOne hapoapsis

theorem analyticAt_firstMassPerturbation_resonantOrbit_of_apoapsis_lt_one
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    AnalyticAt ℝ (fun argument ↦ firstMassPerturbation
      (resonantEllipsePhasePoint p q eccentricity argument)) time := by
  exact analyticAt_firstMassPerturbation_resonantOrbit hp hq heccentricity
    heccentricityOne
    (resonantRotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one
      heccentricity heccentricityOne hapoapsis)

theorem intervalIntegrable_firstMassPerturbation_resonantOrbit_of_apoapsis_lt_one
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity start finish : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    IntervalIntegrable
      (fun time ↦ firstMassPerturbation
        (resonantEllipsePhasePoint p q eccentricity time))
      MeasureTheory.volume start finish := by
  apply intervalIntegrable_firstMassPerturbation_resonantOrbit hp hq heccentricity
    heccentricityOne
  intro time _
  exact resonantRotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one
    heccentricity heccentricityOne hapoapsis

lemma resonantEllipsePhasePoint_collisionFree_mass_zero
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hprimary :
      (resonantRotatingEllipsePosition p q eccentricity time 0 - 1) ^ 2 +
          (resonantRotatingEllipsePosition p q eccentricity time 1) ^ 2 ≠ 0) :
    (0, resonantEllipsePhasePoint p q eccentricity time) ∈
      collisionFree := by
  constructor
  · simpa [firstPrimaryDistanceSq,
      resonantEllipsePhasePoint, positionPhasePoint] using hprimary
  · have hfirstAction : resonantFirstAction p q ≠ 0 :=
      (resonantFirstAction_pos hp hq).ne'
    have hradius := eccentricRadius_pos (anomaly :=
        resonantEccentricAnomaly p q eccentricity time) hfirstAction heccentricity
      heccentricityOne
    have horigin :
        (resonantRotatingEllipsePosition p q eccentricity time 0) ^ 2 +
            (resonantRotatingEllipsePosition p q eccentricity time 1) ^ 2 ≠ 0 := by
      change
        (rotatingEllipsePosition (resonantFirstAction p q) eccentricity
            (resonantEccentricAnomaly p q eccentricity time) time 0) ^ 2 +
          (rotatingEllipsePosition (resonantFirstAction p q) eccentricity
            (resonantEccentricAnomaly p q eccentricity time) time 1) ^ 2 ≠ 0
      rw [rotatingEllipsePosition_sq heccentricity heccentricityOne.le]
      exact (sq_pos_of_pos hradius).ne'
    simpa [secondPrimaryDistanceSq,
      resonantEllipsePhasePoint, positionPhasePoint] using horigin

/-- A rational Kepler resonance gives a genuinely periodic orbit in the rotating frame. -/
theorem resonantRotatingEllipsePosition_add_period {p q : ℕ} (hp : 0 < p)
    {eccentricity : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) (time : ℝ) :
    resonantRotatingEllipsePosition p q eccentricity (time + resonantOrbitPeriod p) =
      resonantRotatingEllipsePosition p q eccentricity time := by
  unfold resonantRotatingEllipsePosition rotatingEllipsePosition positionInRotatingFrame
  rw [resonantEccentricAnomaly_add_period hp heccentricity heccentricityOne]
  unfold resonantOrbitPeriod
  have hperiod : 2 * Real.pi * (p : ℝ) = (p : ℝ) * (2 * Real.pi) := by ring
  rw [hperiod]
  simp [inertialEllipsePosition]

lemma resonantEllipsePhasePoint_add_period {p q : ℕ} (hp : 0 < p)
    {eccentricity : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) (time : ℝ) :
    resonantEllipsePhasePoint p q eccentricity (time + resonantOrbitPeriod p) =
      resonantEllipsePhasePoint p q eccentricity time := by
  unfold resonantEllipsePhasePoint
  rw [resonantRotatingEllipsePosition_add_period hp heccentricity heccentricityOne]

/-- The disturbing function restricted to a resonant ellipse has the common resonant period. -/
lemma firstMassPerturbation_resonantOrbit_periodic {p q : ℕ} (hp : 0 < p)
    {eccentricity : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) (time : ℝ) :
    firstMassPerturbation
        (resonantEllipsePhasePoint p q eccentricity (time + resonantOrbitPeriod p)) =
      firstMassPerturbation (resonantEllipsePhasePoint p q eccentricity time) := by
  rw [resonantEllipsePhasePoint_add_period hp heccentricity heccentricityOne]

end LeanPool.PoincareThreeBody
