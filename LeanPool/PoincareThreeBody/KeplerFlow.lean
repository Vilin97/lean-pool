/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.KeplerPhaseOrbit
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases

/-!
# The resonant ellipse as a Hamiltonian flow line

This file assembles the four scalar Kepler equations into a derivative of the full phase-space
curve and provides the chain-rule interface used to differentiate a candidate first integral along
that curve.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- Explicit rotating Kepler vector field away from the origin. -/
noncomputable def rotatingKeplerVectorField (s : PhaseSpace) : PhaseSpace :=
  ![s 2 + s 1,
    s 3 - s 0,
    s 3 - s 0 / (Real.sqrt (s 0 ^ 2 + s 1 ^ 2)) ^ 3,
    -s 2 - s 1 / (Real.sqrt (s 0 ^ 2 + s 1 ^ 2)) ^ 3]

lemma sqrt_positionSq_orientedResonantKeplerPhasePoint
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    Real.sqrt
        ((orientedResonantKeplerPhasePoint p q eccentricity orientation time 0) ^ 2 +
          (orientedResonantKeplerPhasePoint p q eccentricity orientation time 1) ^ 2) =
      eccentricRadius (resonantFirstAction p q) eccentricity
        (resonantEccentricAnomaly p q eccentricity time) := by
  have hfirstAction : resonantFirstAction p q ≠ 0 :=
    (resonantFirstAction_pos hp hq).ne'
  have hradius := eccentricRadius_pos (anomaly :=
      resonantEccentricAnomaly p q eccentricity time) hfirstAction heccentricity
    heccentricityOne
  rw [show
    (orientedResonantKeplerPhasePoint p q eccentricity orientation time 0) ^ 2 +
        (orientedResonantKeplerPhasePoint p q eccentricity orientation time 1) ^ 2 =
      eccentricRadius (resonantFirstAction p q) eccentricity
        (resonantEccentricAnomaly p q eccentricity time) ^ 2 by
      simpa using orientedResonantEllipsePosition_sq
        (p := p) (q := q) (orientation := orientation) (time := time)
        heccentricity heccentricityOne.le]
  exact (Real.sqrt_sq_eq_abs _).trans (abs_of_pos hradius)

/-- The derivative of the full resonant phase-space curve is the rotating Kepler vector field. -/
theorem hasDerivAt_orientedResonantKeplerPhasePoint
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    HasDerivAt (orientedResonantKeplerPhasePoint p q eccentricity orientation)
      (rotatingKeplerVectorField
        (orientedResonantKeplerPhasePoint p q eccentricity orientation time)) time := by
  have hposition := hasDerivAt_orientedResonantKeplerPhasePoint_position
    p q heccentricity heccentricityOne (orientation := orientation) (time := time)
  have hmomentum := hasDerivAt_orientedResonantKeplerPhasePoint_momentum
    hp hq heccentricity heccentricityOne (orientation := orientation) (time := time)
  have hradius := sqrt_positionSq_orientedResonantKeplerPhasePoint
    hp hq heccentricity heccentricityOne (orientation := orientation) (time := time)
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · exact hposition.1
  · exact hposition.2
  · change HasDerivAt
      (fun t ↦ orientedResonantKeplerPhasePoint p q eccentricity orientation t 2)
      (orientedResonantKeplerPhasePoint p q eccentricity orientation time 3 -
        orientedResonantKeplerPhasePoint p q eccentricity orientation time 0 /
          Real.sqrt
            ((orientedResonantKeplerPhasePoint p q eccentricity orientation time 0) ^ 2 +
              (orientedResonantKeplerPhasePoint p q eccentricity orientation time 1) ^ 2) ^ 3)
      time
    rw [hradius]
    exact hmomentum.1
  · change HasDerivAt
      (fun t ↦ orientedResonantKeplerPhasePoint p q eccentricity orientation t 3)
      (-orientedResonantKeplerPhasePoint p q eccentricity orientation time 2 -
        orientedResonantKeplerPhasePoint p q eccentricity orientation time 1 /
          Real.sqrt
            ((orientedResonantKeplerPhasePoint p q eccentricity orientation time 0) ^ 2 +
              (orientedResonantKeplerPhasePoint p q eccentricity orientation time 1) ^ 2) ^ 3)
      time
    rw [hradius]
    exact hmomentum.2

/-- Chain rule for a scalar observable along the full resonant Kepler orbit. -/
theorem HasFDerivAt.hasDerivAt_comp_orientedResonantKeplerPhasePoint
    {F : PhaseSpace → ℝ} {F' : PhaseSpace →L[ℝ] ℝ} {s : PhaseSpace}
    (hF : HasFDerivAt F F' s)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hs : s = orientedResonantKeplerPhasePoint p q eccentricity orientation time) :
    HasDerivAt
      (fun t ↦ F (orientedResonantKeplerPhasePoint p q eccentricity orientation t))
      (F' (rotatingKeplerVectorField s)) time := by
  subst s
  exact hF.comp_hasDerivAt time
    (hasDerivAt_orientedResonantKeplerPhasePoint hp hq heccentricity heccentricityOne)

end LeanPool.PoincareThreeBody
