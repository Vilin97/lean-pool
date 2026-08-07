/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DisturbingCertificate

/-!
# A concrete interior 1:2 resonance

This file specializes the finite-certificate interface to the 1:2 Kepler resonance at
eccentricity `1 / 10`.  All geometric side conditions are proved exactly.  A generated
validated-numerics proof therefore only has to bound a second derivative and check one finite
trapezoidal inequality.
-/

namespace LeanPool.PoincareThreeBody

open scoped Interval

/-- The eccentricity selected for the concrete 1:2 resonance certificate. -/
noncomputable def oneTwoEccentricity : ℝ := 1 / 10

/-- The 1:2 resonant first action is strictly less than the rational bound `4 / 5`. -/
lemma resonantFirstAction_one_two_lt_four_fifths :
    resonantFirstAction 1 2 < (4 / 5 : ℝ) := by
  apply (show Odd 3 by decide).pow_lt_pow.mp
  rw [resonantFirstAction_cube (by norm_num) (by norm_num)]
  norm_num

/-- The selected eccentricity is physically elliptic. -/
lemma oneTwoEccentricity_nonneg : 0 ≤ oneTwoEccentricity := by
  norm_num [oneTwoEccentricity]

lemma oneTwoEccentricity_lt_one : oneTwoEccentricity < 1 := by
  norm_num [oneTwoEccentricity]

/-- The selected ellipse lies strictly inside the orbit of the unit primary. -/
lemma oneTwo_apoapsis_lt_one :
    resonantFirstAction 1 2 ^ 2 * (1 + oneTwoEccentricity) < 1 := by
  have hpos : 0 < resonantFirstAction 1 2 :=
    resonantFirstAction_pos (by norm_num) (by norm_num)
  have hlt := resonantFirstAction_one_two_lt_four_fifths
  have hsquare : resonantFirstAction 1 2 ^ 2 < (4 / 5 : ℝ) ^ 2 := by
    nlinarith
  norm_num [oneTwoEccentricity] at ⊢
  nlinarith

/-- A validated quadrature certificate for the selected phase pair gives a nonzero derivative of
the exact resonant average, and hence the Poincaré homological obstruction on this orbit. -/
theorem oneTwo_exists_average_derivative_ne_zero_of_trapezoidal_certificate
    {phaseA phaseB errorBound : ℝ} {steps : ℕ}
    (hsecondDerivative : ∀ time,
      |iteratedDerivWithin 2
        (resonantDisturbingDifference 1 2 oneTwoEccentricity phaseA phaseB)
        [[0, resonantOrbitPeriod 1]] time| ≤ errorBound)
    (hsteps : 0 < steps)
    (hcertificate : |resonantOrbitPeriod 1| ^ 3 * errorBound / (12 * steps ^ 2) <
      |trapezoidal_integral
        (resonantDisturbingDifference 1 2 oneTwoEccentricity phaseA phaseB)
        steps 0 (resonantOrbitPeriod 1)|) :
    ∃ orientation,
      deriv (resonantDisturbingAverage 1 2 oneTwoEccentricity) orientation ≠ 0 := by
  exact exists_deriv_resonantDisturbingAverage_ne_zero_of_trapezoidal_certificate
    (by norm_num) (by norm_num) oneTwoEccentricity_nonneg oneTwoEccentricity_lt_one
    oneTwo_apoapsis_lt_one hsecondDerivative hsteps hcertificate

end LeanPool.PoincareThreeBody
