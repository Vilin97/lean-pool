/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DisturbingFunction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
# The apoapsis collision boundary of an interior resonance

For resonant semimajor axes between `1 / 2` and `1`, increasing eccentricity reaches the unit
primary before the parabolic limit.  This file identifies the boundary eccentricity, apoapsis
time, and orientation at which the limiting ellipse meets the primary exactly.
-/

namespace LeanPool.PoincareThreeBody

/-- Semimajor axis of the normalized Kepler ellipse at the `(p,q)` resonance. -/
noncomputable def resonantSemimajorAxis (p q : ℕ) : ℝ :=
  resonantFirstAction p q ^ 2

/-- Eccentricity at which the resonant apoapsis reaches radius one. -/
noncomputable def resonantCollisionEccentricity (p q : ℕ) : ℝ :=
  1 / resonantSemimajorAxis p q - 1

/-- The first time at which the resonant orbit reaches apoapsis. -/
noncomputable def resonantApoapsisTime (p q : ℕ) : ℝ :=
  Real.pi * p / q

/-- Orientation which places that apoapsis at the unit primary. -/
noncomputable def resonantCollisionOrientation (p q : ℕ) : ℝ :=
  resonantApoapsisTime p q - Real.pi

theorem resonantSemimajorAxis_pos {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    0 < resonantSemimajorAxis p q := by
  unfold resonantSemimajorAxis
  exact sq_pos_of_pos (resonantFirstAction_pos hp hq)

theorem resonantCollisionEccentricity_pos {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisOne : resonantSemimajorAxis p q < 1) :
    0 < resonantCollisionEccentricity p q := by
  have haxisPositive := resonantSemimajorAxis_pos hp hq
  unfold resonantCollisionEccentricity
  rw [sub_pos, one_lt_div haxisPositive]
  exact haxisOne

theorem resonantCollisionEccentricity_lt_one {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisHalf : 1 / 2 < resonantSemimajorAxis p q) :
    resonantCollisionEccentricity p q < 1 := by
  have haxisPositive := resonantSemimajorAxis_pos hp hq
  unfold resonantCollisionEccentricity
  rw [sub_lt_iff_lt_add, div_lt_iff₀ haxisPositive]
  nlinarith

theorem resonantMeanAnomaly_apoapsisTime {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    resonantMeanAnomaly p q (resonantApoapsisTime p q) = Real.pi := by
  have hpReal : (p : ℝ) ≠ 0 := by positivity
  have hqReal : (q : ℝ) ≠ 0 := by positivity
  unfold resonantMeanAnomaly resonantMeanMotion resonantApoapsisTime
  field_simp

theorem resonantEccentricAnomaly_apoapsisTime
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) :
    resonantEccentricAnomaly p q eccentricity (resonantApoapsisTime p q) =
      Real.pi := by
  unfold resonantEccentricAnomaly
  rw [resonantMeanAnomaly_apoapsisTime hp hq]
  simpa [eccentricMeanAnomaly] using
    (eccentricAnomaly_eccentricMeanAnomaly
      heccentricity heccentricityOne Real.pi)

/-- At the collision-aligned orientation, every admissible ellipse places its apoapsis on the
positive rotating x-axis. -/
theorem orientedResonantEllipsePosition_alignedApoapsis
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) :
    orientedResonantEllipsePosition p q eccentricity
      (resonantCollisionOrientation p q)
      (resonantApoapsisTime p q) =
        ![resonantSemimajorAxis p q * (1 + eccentricity), (0 : ℝ)] := by
  have hanomaly := resonantEccentricAnomaly_apoapsisTime hp hq
    heccentricity heccentricityOne
  unfold orientedResonantEllipsePosition resonantCollisionOrientation
  rw [hanomaly]
  ext coordinate
  fin_cases coordinate
  · simp [positionInRotatingFrame, inertialEllipsePosition, resonantSemimajorAxis]
    ring
  · simp [positionInRotatingFrame, inertialEllipsePosition]

/-- The distance from aligned apoapsis to the unit primary is the remaining apoapsis gap. -/
theorem alignedApoapsis_primaryDistance
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantSemimajorAxis p q * (1 + eccentricity) < 1) :
    Real.sqrt
        ((orientedResonantEllipsePosition p q eccentricity
              (resonantCollisionOrientation p q) (resonantApoapsisTime p q) 0 - 1) ^ 2 +
          (orientedResonantEllipsePosition p q eccentricity
              (resonantCollisionOrientation p q) (resonantApoapsisTime p q) 1) ^ 2) =
      1 - resonantSemimajorAxis p q * (1 + eccentricity) := by
  rw [orientedResonantEllipsePosition_alignedApoapsis hp hq
    heccentricity heccentricityOne]
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_pow, add_zero]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonpos]
  · ring
  · linarith

/-- At aligned apoapsis the singular part of the disturbing function is exactly the reciprocal
of the remaining gap to collision. -/
theorem resonantDisturbingFunction_alignedApoapsis
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantSemimajorAxis p q * (1 + eccentricity) < 1) :
    resonantDisturbingFunction p q eccentricity
        (resonantCollisionOrientation p q) (resonantApoapsisTime p q) =
      let radius := resonantSemimajorAxis p q * (1 + eccentricity)
      1 / radius + 1 / radius ^ 2 - 1 / (1 - radius) := by
  let radius := resonantSemimajorAxis p q * (1 + eccentricity)
  have hradiusPositive : 0 < radius := by
    dsimp [radius]
    exact mul_pos (resonantSemimajorAxis_pos hp hq) (by linarith)
  have hposition := orientedResonantEllipsePosition_alignedApoapsis hp hq
    heccentricity heccentricityOne
  unfold resonantDisturbingFunction orientedResonantEllipsePhasePoint
    firstMassPerturbation
  rw [hposition]
  change 1 / Real.sqrt (radius ^ 2 + 0 ^ 2) +
      radius / (Real.sqrt (radius ^ 2 + 0 ^ 2)) ^ 3 -
        1 / Real.sqrt ((radius - 1) ^ 2 + 0 ^ 2) =
    1 / radius + 1 / radius ^ 2 - 1 / (1 - radius)
  norm_num only [zero_pow, add_zero]
  have hrootRadius : Real.sqrt (radius ^ 2) = radius := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hradiusPositive]
  have hrootGap : Real.sqrt ((radius - 1) ^ 2) = 1 - radius := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonpos (by linarith : radius - 1 ≤ 0)]
    ring
  rw [hrootRadius, hrootGap]
  have hgap : 1 - radius ≠ 0 := (sub_pos.mpr hapoapsis).ne'
  field_simp [hradiusPositive.ne', hgap]

/-- At the boundary eccentricity and aligned orientation, apoapsis is exactly the unit primary. -/
theorem orientedResonantEllipsePosition_collisionBoundary
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisHalf : 1 / 2 < resonantSemimajorAxis p q)
    (haxisOne : resonantSemimajorAxis p q < 1) :
    orientedResonantEllipsePosition p q
      (resonantCollisionEccentricity p q)
      (resonantCollisionOrientation p q)
      (resonantApoapsisTime p q) = ![(1 : ℝ), (0 : ℝ)] := by
  have haxisPositive := resonantSemimajorAxis_pos hp hq
  have heccentricity := resonantCollisionEccentricity_pos hp hq haxisOne
  have heccentricityOne := resonantCollisionEccentricity_lt_one hp hq haxisHalf
  rw [orientedResonantEllipsePosition_alignedApoapsis hp hq
    heccentricity.le heccentricityOne]
  ext coordinate
  fin_cases coordinate <;>
    simp [resonantCollisionEccentricity]
  field_simp [haxisPositive.ne']

end LeanPool.PoincareThreeBody
