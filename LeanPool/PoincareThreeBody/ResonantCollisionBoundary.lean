/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DisturbingParameterAnalytic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
# The apoapsis collision boundary of an interior resonance

For resonant semimajor axes between `1 / 2` and `1`, increasing eccentricity reaches the unit
primary before the parabolic limit.  This file identifies the boundary eccentricity, apoapsis
time, and orientation at which the limiting ellipse meets the primary exactly.
-/

namespace LeanPool.PoincareThreeBody

open Filter Topology

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

/-- The collision-aligned position approaches the unit primary at most linearly in the joint
eccentricity/time displacement.  This is the local estimate behind the logarithmic blowup of the
averaged Newtonian singularity. -/
theorem collisionAlignedPosition_isBigO
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisHalf : 1 / 2 < resonantSemimajorAxis p q)
    (haxisOne : resonantSemimajorAxis p q < 1) :
    (fun parameters : ℝ × ℝ ↦
      orientedResonantEllipsePosition p q parameters.1
        (resonantCollisionOrientation p q) parameters.2 - ![(1 : ℝ), (0 : ℝ)])
      =O[𝓝 (resonantCollisionEccentricity p q, resonantApoapsisTime p q)]
    (fun parameters : ℝ × ℝ ↦
      parameters -
        (resonantCollisionEccentricity p q, resonantApoapsisTime p q)) := by
  have heccentricity := resonantCollisionEccentricity_pos hp hq haxisOne
  have heccentricityOne := resonantCollisionEccentricity_lt_one hp hq haxisHalf
  have hdifferentiable : DifferentiableAt ℝ
      (fun parameters : ℝ × ℝ ↦
        orientedResonantEllipsePosition p q parameters.1
          (resonantCollisionOrientation p q) parameters.2)
      (resonantCollisionEccentricity p q, resonantApoapsisTime p q) := by
    rw [differentiableAt_pi]
    intro coordinate
    exact (analyticAt_orientedResonantEllipsePosition_eccentricity_time_coordinate
      p q heccentricity heccentricityOne coordinate).differentiableAt
  have hbound := hdifferentiable.isBigO_sub
  rw [orientedResonantEllipsePosition_collisionBoundary hp hq haxisHalf haxisOne] at hbound
  exact hbound

/-- Quantitative neighborhood form of `collisionAlignedPosition_isBigO`. -/
theorem exists_collisionAlignedPosition_local_bound
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisHalf : 1 / 2 < resonantSemimajorAxis p q)
    (haxisOne : resonantSemimajorAxis p q < 1) :
    ∃ constant : ℝ, 0 < constant ∧ ∃ radius : ℝ, 0 < radius ∧
      ∀ parameters : ℝ × ℝ,
        dist parameters
            (resonantCollisionEccentricity p q, resonantApoapsisTime p q) < radius →
        ‖orientedResonantEllipsePosition p q parameters.1
              (resonantCollisionOrientation p q) parameters.2 - ![(1 : ℝ), (0 : ℝ)]‖ ≤
          constant *
            ‖parameters -
              (resonantCollisionEccentricity p q, resonantApoapsisTime p q)‖ := by
  rcases (collisionAlignedPosition_isBigO hp hq haxisHalf haxisOne).exists_pos with
    ⟨constant, hconstant, hbound⟩
  rcases Metric.eventually_nhds_iff.mp
      (Asymptotics.isBigOWith_iff.mp hbound) with
    ⟨radius, hradius, hlocal⟩
  exact ⟨constant, hconstant, radius, hradius, fun parameters hparameters ↦
    hlocal hparameters⟩

/-- The Euclidean distance used by the Newtonian potential is controlled by twice the ambient
sup norm on the concrete two-dimensional action space. -/
theorem sqrt_sq_add_sq_le_two_norm (vector : ActionSpace) :
    Real.sqrt (vector 0 ^ 2 + vector 1 ^ 2) ≤ 2 * ‖vector‖ := by
  have hsqrt : Real.sqrt (vector 0 ^ 2 + vector 1 ^ 2) ≤
      |vector 0| + |vector 1| := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · calc
        vector 0 ^ 2 + vector 1 ^ 2 = |vector 0| ^ 2 + |vector 1| ^ 2 := by
          rw [sq_abs, sq_abs]
        _ ≤ (|vector 0| + |vector 1|) ^ 2 := by
          nlinarith [mul_nonneg (abs_nonneg (vector 0)) (abs_nonneg (vector 1))]
  have hzero : |vector 0| ≤ ‖vector‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm vector 0
  have hone : |vector 1| ≤ ‖vector‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm vector 1
  have hsum' : |vector 0| + |vector 1| ≤ 2 * ‖vector‖ := by linarith
  exact hsqrt.trans hsum'

end LeanPool.PoincareThreeBody
