/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DelaunayChart
import LeanPool.PoincareThreeBody.KeplerHamiltonian

/-!
# Physical realization of the planar Delaunay actions

This file identifies the two actions carried by the explicit lifted ellipse.  The second action is
Cartesian angular momentum, while the first action is determined by the negative inertial Kepler
energy.  Consequently the physical mass-zero Hamiltonian pulls back to the displayed Delaunay
Hamiltonian.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- Inertial Kepler energy written in rotating Cartesian canonical variables. -/
noncomputable def cartesianKeplerEnergy (state : PhaseSpace) : ℝ :=
  ((state 2) ^ 2 + (state 3) ^ 2) / 2 -
    1 / Real.sqrt ((state 0) ^ 2 + (state 1) ^ 2)

/-- The first Delaunay action reconstructed from negative inertial Kepler energy. -/
noncomputable def cartesianFirstAction (state : PhaseSpace) : ℝ :=
  1 / Real.sqrt (-2 * cartesianKeplerEnergy state)

/-- The planar angular action `G = x pᵧ - y pₓ`. -/
def cartesianAngularAction (state : PhaseSpace) : ℝ :=
  state 0 * state 3 - state 1 * state 2

/-- Both Cartesian Delaunay actions, ordered as `(L, G)`. -/
noncomputable def cartesianDelaunayActions (state : PhaseSpace) : ActionSpace :=
  ![cartesianFirstAction state, cartesianAngularAction state]

/-- A common planar rotation preserves the determinant of two vectors. -/
lemma positionInRotatingFrame_cross
    (angle : ℝ) (first second : ActionSpace) :
    positionInRotatingFrame angle first 0 * positionInRotatingFrame angle second 1 -
        positionInRotatingFrame angle first 1 * positionInRotatingFrame angle second 0 =
      first 0 * second 1 - first 1 * second 0 := by
  have htrig := Real.sin_sq_add_cos_sq angle
  simp only [positionInRotatingFrame, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (first 0 * second 1 - first 1 * second 0) * htrig

/-- A common planar rotation preserves the squared norm. -/
lemma positionInRotatingFrame_momentum_sq
    (angle : ℝ) (momentum : ActionSpace) :
    (positionInRotatingFrame angle momentum 0) ^ 2 +
        (positionInRotatingFrame angle momentum 1) ^ 2 =
      (momentum 0) ^ 2 + (momentum 1) ^ 2 :=
  positionInRotatingFrame_sq angle momentum

/-- The eccentric-anomaly position and velocity carry angular action
`L * sqrt (1 - e²)`. -/
lemma inertialEllipsePosition_velocity_cross
    {firstAction eccentricity anomaly : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    inertialEllipsePosition firstAction eccentricity anomaly 0 *
          inertialEllipseVelocity firstAction eccentricity (1 / firstAction ^ 3) anomaly 1 -
        inertialEllipsePosition firstAction eccentricity anomaly 1 *
          inertialEllipseVelocity firstAction eccentricity (1 / firstAction ^ 3) anomaly 0 =
      angularActionFromEccentricity firstAction eccentricity := by
  have hdenominator : 1 - eccentricity * Real.cos anomaly ≠ 0 :=
    (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne).ne'
  have hdenominator' : 1 - Real.cos anomaly * eccentricity ≠ 0 := by
    simpa [mul_comm] using hdenominator
  have htrig := Real.sin_sq_add_cos_sq anomaly
  simp only [inertialEllipsePosition, inertialEllipseVelocity,
    angularActionFromEccentricity, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hfirstAction, hdenominator, hdenominator']
  ring_nf
  linear_combination Real.sqrt (1 - eccentricity ^ 2) * htrig

/-- The velocity norm on an elliptic Kepler orbit has the vis-viva value needed for its energy
shell. -/
lemma inertialEllipseVelocity_energy_identity
    {firstAction eccentricity anomaly : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    ((inertialEllipseVelocity firstAction eccentricity (1 / firstAction ^ 3) anomaly 0) ^ 2 +
          (inertialEllipseVelocity firstAction eccentricity
            (1 / firstAction ^ 3) anomaly 1) ^ 2) / 2 -
        1 / eccentricRadius firstAction eccentricity anomaly =
      -1 / (2 * firstAction ^ 2) := by
  have hdenominator : 1 - eccentricity * Real.cos anomaly ≠ 0 :=
    (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne).ne'
  have hsqrt : (Real.sqrt (1 - eccentricity ^ 2)) ^ 2 =
      1 - eccentricity ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith
  have htrig := Real.sin_sq_add_cos_sq anomaly
  simp only [inertialEllipseVelocity, eccentricRadius,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hfirstAction, hdenominator]
  nlinarith

/-- The explicit lifted Delaunay chart realizes its prescribed second action. -/
theorem cartesianAngularAction_liftedDelaunayPhasePoint
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    cartesianAngularAction
        (liftedDelaunayPhasePoint
          firstAction eccentricity meanAnomaly periapsisAngle) =
      angularActionFromEccentricity firstAction eccentricity := by
  unfold cartesianAngularAction liftedDelaunayPhasePoint liftedDelaunayPosition
    liftedDelaunayMomentum positionMomentumPhasePoint
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change
    positionInRotatingFrame (-periapsisAngle)
          (inertialEllipsePosition firstAction eccentricity
            (liftedDelaunayEccentricAnomaly eccentricity meanAnomaly)) 0 *
        positionInRotatingFrame (-periapsisAngle)
          (inertialEllipseVelocity firstAction eccentricity (1 / firstAction ^ 3)
            (liftedDelaunayEccentricAnomaly eccentricity meanAnomaly)) 1 -
      positionInRotatingFrame (-periapsisAngle)
          (inertialEllipsePosition firstAction eccentricity
            (liftedDelaunayEccentricAnomaly eccentricity meanAnomaly)) 1 *
        positionInRotatingFrame (-periapsisAngle)
          (inertialEllipseVelocity firstAction eccentricity (1 / firstAction ^ 3)
            (liftedDelaunayEccentricAnomaly eccentricity meanAnomaly)) 0 = _
  rw [positionInRotatingFrame_cross]
  exact inertialEllipsePosition_velocity_cross hfirstAction heccentricity heccentricityOne

/-- The first action of the lifted chart is its negative Kepler energy action. -/
theorem cartesianKeplerEnergy_liftedDelaunayPhasePoint
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    cartesianKeplerEnergy
        (liftedDelaunayPhasePoint
          firstAction eccentricity meanAnomaly periapsisAngle) =
      -1 / (2 * firstAction ^ 2) := by
  let anomaly := liftedDelaunayEccentricAnomaly eccentricity meanAnomaly
  have hradius : 0 < eccentricRadius firstAction eccentricity anomaly :=
    eccentricRadius_pos hfirstAction heccentricity heccentricityOne
  have hpositionSq :
      (liftedDelaunayPosition firstAction eccentricity meanAnomaly periapsisAngle 0) ^ 2 +
          (liftedDelaunayPosition firstAction eccentricity meanAnomaly periapsisAngle 1) ^ 2 =
        eccentricRadius firstAction eccentricity anomaly ^ 2 := by
    unfold liftedDelaunayPosition
    rw [positionInRotatingFrame_sq,
      inertialEllipsePosition_sq heccentricity heccentricityOne.le]
  have hmomentumSq :
      (liftedDelaunayMomentum firstAction eccentricity meanAnomaly periapsisAngle 0) ^ 2 +
          (liftedDelaunayMomentum firstAction eccentricity meanAnomaly periapsisAngle 1) ^ 2 =
        (inertialEllipseVelocity firstAction eccentricity
            (1 / firstAction ^ 3) anomaly 0) ^ 2 +
          (inertialEllipseVelocity firstAction eccentricity
            (1 / firstAction ^ 3) anomaly 1) ^ 2 := by
    exact positionInRotatingFrame_momentum_sq _ _
  unfold cartesianKeplerEnergy liftedDelaunayPhasePoint positionMomentumPhasePoint
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change
    ((liftedDelaunayMomentum firstAction eccentricity meanAnomaly periapsisAngle 0) ^ 2 +
          (liftedDelaunayMomentum firstAction eccentricity meanAnomaly periapsisAngle 1) ^ 2) /
        2 -
      1 / Real.sqrt
        ((liftedDelaunayPosition firstAction eccentricity meanAnomaly periapsisAngle 0) ^ 2 +
          (liftedDelaunayPosition firstAction eccentricity meanAnomaly periapsisAngle 1) ^ 2) = _
  rw [hpositionSq, hmomentumSq, Real.sqrt_sq_eq_abs, abs_of_pos hradius]
  exact inertialEllipseVelocity_energy_identity hfirstAction
    heccentricity heccentricityOne

/-- Reconstructing the first action from the energy of a positive-action lifted ellipse returns
the original `L`. -/
theorem cartesianFirstAction_liftedDelaunayPhasePoint
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    cartesianFirstAction
        (liftedDelaunayPhasePoint
          firstAction eccentricity meanAnomaly periapsisAngle) =
      firstAction := by
  rw [cartesianFirstAction,
    cartesianKeplerEnergy_liftedDelaunayPhasePoint hfirstAction.ne'
      heccentricity heccentricityOne]
  have hinverseSquare : -2 * (-1 / (2 * firstAction ^ 2)) =
      (1 / firstAction) ^ 2 := by
    field_simp [hfirstAction.ne']
  rw [hinverseSquare, Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hfirstAction)]
  field_simp [hfirstAction.ne']

/-- The complete Cartesian action map is a left inverse of the lifted Delaunay chart. -/
theorem cartesianDelaunayActions_liftedDelaunayPhasePoint
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    cartesianDelaunayActions
        (liftedDelaunayPhasePoint
          firstAction eccentricity meanAnomaly periapsisAngle) =
      ![firstAction, angularActionFromEccentricity firstAction eccentricity] := by
  funext coordinate
  fin_cases coordinate
  · exact cartesianFirstAction_liftedDelaunayPhasePoint hfirstAction
      heccentricity heccentricityOne
  · exact cartesianAngularAction_liftedDelaunayPhasePoint hfirstAction.ne'
      heccentricity heccentricityOne

/-- At every noncentral phase point, the zero-mass rotating Hamiltonian is inertial Kepler energy
minus angular action. -/
theorem hamiltonian_zero_eq_cartesianKeplerEnergy_sub_angularAction
    (state : PhaseSpace) :
    hamiltonian 0 state =
      cartesianKeplerEnergy state - cartesianAngularAction state := by
  rw [hamiltonian_zero]
  unfold cartesianKeplerEnergy cartesianAngularAction
  ring

/-- On the negative-energy region, the Cartesian action reconstruction puts the physical
Hamiltonian into Delaunay normal form. -/
theorem delaunayHamiltonian_cartesianDelaunayActions
    {state : PhaseSpace} (henergy : cartesianKeplerEnergy state < 0) :
    delaunayHamiltonian (cartesianDelaunayActions state) = hamiltonian 0 state := by
  have hpositive : 0 < -2 * cartesianKeplerEnergy state := by linarith
  have hroot : 0 < Real.sqrt (-2 * cartesianKeplerEnergy state) :=
    Real.sqrt_pos.mpr hpositive
  have hrootSquare : (Real.sqrt (-2 * cartesianKeplerEnergy state)) ^ 2 =
      -2 * cartesianKeplerEnergy state := Real.sq_sqrt hpositive.le
  rw [hamiltonian_zero_eq_cartesianKeplerEnergy_sub_angularAction]
  simp only [delaunayHamiltonian, cartesianDelaunayActions,
    cartesianFirstAction, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hroot.ne']
  ring_nf at hrootSquare ⊢
  nlinarith

/-- The physical zero-mass Hamiltonian pulls back to the Delaunay Hamiltonian. -/
theorem hamiltonian_zero_liftedDelaunayPhasePoint
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    hamiltonian 0
        (liftedDelaunayPhasePoint
          firstAction eccentricity meanAnomaly periapsisAngle) =
      delaunayHamiltonian
        ![firstAction, angularActionFromEccentricity firstAction eccentricity] := by
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  have hdecompose : hamiltonian 0 state =
      cartesianKeplerEnergy state - cartesianAngularAction state := by
    rw [hamiltonian_zero]
    unfold cartesianKeplerEnergy cartesianAngularAction
    ring
  have henergy := cartesianKeplerEnergy_liftedDelaunayPhasePoint
    (meanAnomaly := meanAnomaly) (periapsisAngle := periapsisAngle)
    hfirstAction heccentricity heccentricityOne
  have hangular := cartesianAngularAction_liftedDelaunayPhasePoint
    (meanAnomaly := meanAnomaly) (periapsisAngle := periapsisAngle)
    hfirstAction heccentricity heccentricityOne
  rw [hdecompose, henergy, hangular]
  rfl

end LeanPool.PoincareThreeBody
