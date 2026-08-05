/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.RotatingEllipse
import Mathlib.Tactic.FieldSimp
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
    (p q : ℕ) (eccentricity time : ℝ) : Challenge.PoincareThreeBody.PhaseSpace :=
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
