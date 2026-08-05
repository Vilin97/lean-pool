/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DisturbingFunction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Full phase-space Kepler orbits

The disturbing function only depends on position, so earlier files used zero placeholders for the
momenta.  The homological equation must instead be evaluated on a genuine Hamiltonian orbit.  This
file supplies the canonical rotating-frame momentum and embeds the resonant ellipse into the full
four-dimensional phase space.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- Inertial Cartesian velocity of the eccentric-anomaly ellipse when the mean anomaly advances
at rate `meanMotion`. -/
noncomputable def inertialEllipseVelocity
    (firstAction eccentricity meanMotion anomaly : ℝ) : ActionSpace :=
  ![-firstAction ^ 2 * meanMotion * Real.sin anomaly /
      (1 - eccentricity * Real.cos anomaly),
    firstAction ^ 2 * meanMotion * Real.sqrt (1 - eccentricity ^ 2) * Real.cos anomaly /
      (1 - eccentricity * Real.cos anomaly)]

/-- Canonical momentum of an oriented resonant ellipse in rotating coordinates. -/
noncomputable def orientedResonantEllipseMomentum
    (p q : ℕ) (eccentricity orientation time : ℝ) : ActionSpace :=
  positionInRotatingFrame (time - orientation)
    (inertialEllipseVelocity (resonantFirstAction p q) eccentricity
      (resonantMeanMotion p q)
      (resonantEccentricAnomaly p q eccentricity time))

/-- Embed planar position and canonical momentum into `(x,y,pₓ,pᵧ)` phase space. -/
def positionMomentumPhasePoint (position momentum : ActionSpace) : PhaseSpace :=
  ![position 0, position 1, momentum 0, momentum 1]

/-- The genuine full phase-space orbit underlying the oriented resonant disturbing function. -/
noncomputable def orientedResonantKeplerPhasePoint
    (p q : ℕ) (eccentricity orientation time : ℝ) : PhaseSpace :=
  positionMomentumPhasePoint
    (orientedResonantEllipsePosition p q eccentricity orientation time)
    (orientedResonantEllipseMomentum p q eccentricity orientation time)

theorem hasDerivAt_resonantMeanAnomaly (p q : ℕ) (time : ℝ) :
    HasDerivAt (resonantMeanAnomaly p q) (resonantMeanMotion p q) time := by
  have h := (hasDerivAt_id time).const_mul (resonantMeanMotion p q)
  apply (h.congr_deriv (by ring)).congr_of_eventuallyEq
  filter_upwards [] with argument
  simp [resonantMeanAnomaly]

theorem hasDerivAt_resonantEccentricAnomaly
    (p q : ℕ) {eccentricity time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    HasDerivAt (resonantEccentricAnomaly p q eccentricity)
      (resonantMeanMotion p q /
        (1 - eccentricity *
          Real.cos (resonantEccentricAnomaly p q eccentricity time))) time := by
  have h := (hasDerivAt_eccentricAnomaly
      (meanAnomaly := resonantMeanAnomaly p q time) heccentricity heccentricityOne).comp
    time (hasDerivAt_resonantMeanAnomaly p q time)
  apply h.congr_deriv
  simp [resonantEccentricAnomaly, div_eq_mul_inv, mul_comm]

/-- The position part of the full resonant state satisfies the first two canonical Hamilton
equations in the rotating frame. -/
theorem hasDerivAt_orientedResonantKeplerPhasePoint_position
    (p q : ℕ) {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    HasDerivAt
        (fun t ↦ orientedResonantKeplerPhasePoint p q eccentricity orientation t 0)
        (orientedResonantKeplerPhasePoint p q eccentricity orientation time 2 +
          orientedResonantKeplerPhasePoint p q eccentricity orientation time 1) time ∧
      HasDerivAt
        (fun t ↦ orientedResonantKeplerPhasePoint p q eccentricity orientation t 1)
        (orientedResonantKeplerPhasePoint p q eccentricity orientation time 3 -
          orientedResonantKeplerPhasePoint p q eccentricity orientation time 0) time := by
  let anomaly : ℝ → ℝ := resonantEccentricAnomaly p q eccentricity
  let denominator : ℝ → ℝ := fun t ↦ 1 - eccentricity * Real.cos (anomaly t)
  let xInertial : ℝ → ℝ := fun t ↦
    resonantFirstAction p q ^ 2 * (Real.cos (anomaly t) - eccentricity)
  let yInertial : ℝ → ℝ := fun t ↦
    resonantFirstAction p q ^ 2 * Real.sqrt (1 - eccentricity ^ 2) *
      Real.sin (anomaly t)
  let vxInertial : ℝ → ℝ := fun t ↦
    -resonantFirstAction p q ^ 2 * resonantMeanMotion p q *
      Real.sin (anomaly t) / denominator t
  let vyInertial : ℝ → ℝ := fun t ↦
    resonantFirstAction p q ^ 2 * resonantMeanMotion p q *
      Real.sqrt (1 - eccentricity ^ 2) * Real.cos (anomaly t) / denominator t
  let angle : ℝ → ℝ := fun t ↦ t - orientation
  have hdenominator : denominator time ≠ 0 :=
    (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne).ne'
  have hanomaly : HasDerivAt anomaly
      (resonantMeanMotion p q / denominator time) time :=
    hasDerivAt_resonantEccentricAnomaly p q heccentricity heccentricityOne
  have hxInertial : HasDerivAt xInertial (vxInertial time) time := by
    have hraw := ((Real.hasDerivAt_cos (anomaly time)).comp time hanomaly
      |>.sub_const eccentricity).const_mul (resonantFirstAction p q ^ 2)
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      dsimp [xInertial]
    · dsimp [vxInertial, denominator]
      field_simp [hdenominator]
  have hyInertial : HasDerivAt yInertial (vyInertial time) time := by
    have hraw := ((Real.hasDerivAt_sin (anomaly time)).comp time hanomaly).const_mul
      (resonantFirstAction p q ^ 2 * Real.sqrt (1 - eccentricity ^ 2))
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      dsimp [yInertial]
    · dsimp [vyInertial, denominator]
      field_simp [hdenominator]
  have hangle : HasDerivAt angle 1 time := by
    simpa [angle] using (hasDerivAt_id time).sub_const orientation
  have hcos := (Real.hasDerivAt_cos (angle time)).comp time hangle
  have hsin := (Real.hasDerivAt_sin (angle time)).comp time hangle
  constructor
  · have hraw := (hcos.mul hxInertial).add (hsin.mul hyInertial)
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      simp only [orientedResonantKeplerPhasePoint, positionMomentumPhasePoint,
        orientedResonantEllipsePosition, orientedResonantEllipseMomentum,
        positionInRotatingFrame, inertialEllipsePosition, inertialEllipseVelocity,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, anomaly, angle]
    · simp only [orientedResonantKeplerPhasePoint, positionMomentumPhasePoint,
        orientedResonantEllipsePosition, orientedResonantEllipseMomentum,
        positionInRotatingFrame, inertialEllipsePosition, inertialEllipseVelocity,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, vxInertial, vyInertial, denominator, anomaly, angle]
      ring
  · have hraw := (hsin.neg.mul hxInertial).add (hcos.mul hyInertial)
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      simp only [orientedResonantKeplerPhasePoint, positionMomentumPhasePoint,
        orientedResonantEllipsePosition, orientedResonantEllipseMomentum,
        positionInRotatingFrame, inertialEllipsePosition, inertialEllipseVelocity,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, anomaly, angle]
    · simp only [orientedResonantKeplerPhasePoint, positionMomentumPhasePoint,
        orientedResonantEllipsePosition, orientedResonantEllipseMomentum,
        positionInRotatingFrame, inertialEllipsePosition, inertialEllipseVelocity,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, vxInertial, vyInertial, denominator, anomaly, angle]
      ring

@[simp] lemma orientedResonantKeplerPhasePoint_position_zero
    (p q : ℕ) (eccentricity orientation time : ℝ) :
    orientedResonantKeplerPhasePoint p q eccentricity orientation time 0 =
      orientedResonantEllipsePosition p q eccentricity orientation time 0 := rfl

@[simp] lemma orientedResonantKeplerPhasePoint_position_one
    (p q : ℕ) (eccentricity orientation time : ℝ) :
    orientedResonantKeplerPhasePoint p q eccentricity orientation time 1 =
      orientedResonantEllipsePosition p q eccentricity orientation time 1 := rfl

/-- Adding the common resonant period preserves the true canonical momentum. -/
lemma orientedResonantEllipseMomentum_add_period {p q : ℕ} (hp : 0 < p)
    {eccentricity orientation : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) (time : ℝ) :
    orientedResonantEllipseMomentum p q eccentricity orientation
        (time + resonantOrbitPeriod p) =
      orientedResonantEllipseMomentum p q eccentricity orientation time := by
  unfold orientedResonantEllipseMomentum positionInRotatingFrame
  rw [resonantEccentricAnomaly_add_period hp heccentricity heccentricityOne]
  unfold resonantOrbitPeriod
  have hangle : time + 2 * Real.pi * (p : ℝ) - orientation =
      (time - orientation) + (p : ℝ) * (2 * Real.pi) := by ring
  rw [hangle]
  funext coordinate
  fin_cases coordinate <;> simp [inertialEllipseVelocity]

/-- The full resonant phase-space trajectory has the common period. -/
lemma orientedResonantKeplerPhasePoint_add_period {p q : ℕ} (hp : 0 < p)
    {eccentricity orientation : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) (time : ℝ) :
    orientedResonantKeplerPhasePoint p q eccentricity orientation
        (time + resonantOrbitPeriod p) =
      orientedResonantKeplerPhasePoint p q eccentricity orientation time := by
  unfold orientedResonantKeplerPhasePoint positionMomentumPhasePoint
  rw [orientedResonantEllipsePosition_add_period hp heccentricity heccentricityOne,
    orientedResonantEllipseMomentum_add_period hp heccentricity heccentricityOne]

/-- Replacing the momentum placeholder by the true momentum does not change the first mass
perturbation. -/
lemma firstMassPerturbation_orientedResonantKeplerPhasePoint
    (p q : ℕ) (eccentricity orientation time : ℝ) :
    firstMassPerturbation
        (orientedResonantKeplerPhasePoint p q eccentricity orientation time) =
      resonantDisturbingFunction p q eccentricity orientation time := by
  simp [firstMassPerturbation, resonantDisturbingFunction,
    orientedResonantEllipsePhasePoint, orientedResonantKeplerPhasePoint,
    positionMomentumPhasePoint, positionPhasePoint]

/-- Collision-freeness at mass zero depends only on the position, so the full phase-space orbit
inherits the collision exclusion proved for the interior ellipse. -/
lemma orientedResonantKeplerPhasePoint_collisionFree_mass_zero
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    (0, orientedResonantKeplerPhasePoint p q eccentricity orientation time) ∈
      collisionFree := by
  constructor
  · simpa [firstPrimaryDistanceSq] using
      orientedResonantEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one
        heccentricity heccentricityOne hapoapsis
  · have hfirstAction : resonantFirstAction p q ≠ 0 :=
      (resonantFirstAction_pos hp hq).ne'
    have hradius := eccentricRadius_pos (anomaly :=
        resonantEccentricAnomaly p q eccentricity time) hfirstAction heccentricity
      heccentricityOne
    have hpositionSq := orientedResonantEllipsePosition_sq
      (p := p) (q := q) (orientation := orientation) (time := time)
      heccentricity heccentricityOne.le
    unfold secondPrimaryDistanceSq
    simp only [orientedResonantKeplerPhasePoint_position_zero,
      orientedResonantKeplerPhasePoint_position_one, add_zero]
    rw [hpositionSq]
    exact (sq_pos_of_pos hradius).ne'

end LeanPool.PoincareThreeBody
