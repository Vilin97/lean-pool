/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.GeneratingFunction
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Elliptic Kepler orbits in eccentric anomaly

This file gives the real elliptic Kepler orbit attached to Delaunay action `I₁` and eccentricity
`e`. It verifies the radius, radial momentum, and energy formulas directly. The mean anomaly is the
first Delaunay angle along the unperturbed flow.
-/

namespace LeanPool.PoincareThreeBody

/-- Radius of an elliptic Kepler orbit as a function of eccentric anomaly. -/
noncomputable def eccentricRadius (firstAction eccentricity anomaly : ℝ) : ℝ :=
  firstAction ^ 2 * (1 - eccentricity * Real.cos anomaly)

/-- Radial momentum of an elliptic Kepler orbit as a function of eccentric anomaly. -/
noncomputable def eccentricRadialMomentum
    (firstAction eccentricity anomaly : ℝ) : ℝ :=
  eccentricity * Real.sin anomaly /
    (firstAction * (1 - eccentricity * Real.cos anomaly))

/-- Mean anomaly as a function of eccentric anomaly (Kepler's equation). -/
noncomputable def eccentricMeanAnomaly (eccentricity anomaly : ℝ) : ℝ :=
  anomaly - eccentricity * Real.sin anomaly

/-- Physical Kepler time, normalized to vanish with the mean anomaly. -/
noncomputable def eccentricKeplerTime
    (firstAction eccentricity anomaly : ℝ) : ℝ :=
  firstAction ^ 3 * eccentricMeanAnomaly eccentricity anomaly

/-- A polar phase-space point on the elliptic Kepler orbit. Its angular coordinate is free because
the inertial Kepler energy is rotation invariant. -/
noncomputable def eccentricPolarState
    (firstAction eccentricity anomaly polarAngle : ℝ) : PolarState :=
  ![eccentricRadius firstAction eccentricity anomaly,
    polarAngle,
    eccentricRadialMomentum firstAction eccentricity anomaly,
    angularActionFromEccentricity firstAction eccentricity]

lemma one_sub_eccentricity_mul_cos_pos {eccentricity anomaly : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    0 < 1 - eccentricity * Real.cos anomaly := by
  have hcos : eccentricity * Real.cos anomaly ≤ eccentricity :=
    mul_le_of_le_one_right heccentricity (Real.cos_le_one anomaly)
  linarith

lemma eccentricRadius_pos {firstAction eccentricity anomaly : ℝ}
    (hfirstAction : firstAction ≠ 0) (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) :
    0 < eccentricRadius firstAction eccentricity anomaly := by
  unfold eccentricRadius
  exact mul_pos (sq_pos_of_ne_zero hfirstAction)
    (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne)

theorem hasDerivAt_eccentricMeanAnomaly (eccentricity anomaly : ℝ) :
    HasDerivAt (eccentricMeanAnomaly eccentricity)
      (1 - eccentricity * Real.cos anomaly) anomaly := by
  have hraw := (hasDerivAt_id anomaly).sub
    ((Real.hasDerivAt_sin anomaly).const_mul eccentricity)
  apply (hraw.congr_deriv (by ring)).congr_of_eventuallyEq
  filter_upwards [] with argument
  simp [eccentricMeanAnomaly]

theorem hasDerivAt_eccentricRadius (firstAction eccentricity anomaly : ℝ) :
    HasDerivAt (eccentricRadius firstAction eccentricity)
      (firstAction ^ 2 * eccentricity * Real.sin anomaly) anomaly := by
  have hraw := (((Real.hasDerivAt_cos anomaly).const_mul (-eccentricity)).add_const 1).const_mul
    (firstAction ^ 2)
  apply (hraw.congr_deriv (by ring)).congr_of_eventuallyEq
  filter_upwards [] with argument
  simp only [eccentricRadius]
  ring

theorem hasDerivAt_eccentricKeplerTime (firstAction eccentricity anomaly : ℝ) :
    HasDerivAt (eccentricKeplerTime firstAction eccentricity)
      (firstAction ^ 3 * (1 - eccentricity * Real.cos anomaly)) anomaly := by
  have hraw := (hasDerivAt_eccentricMeanAnomaly eccentricity anomaly).const_mul
    (firstAction ^ 3)
  apply hraw.congr_of_eventuallyEq
  filter_upwards [] with argument
  rfl

/-- The radial momentum is `dr/dt` along the eccentric-anomaly parameterization. -/
theorem eccentricRadialMomentum_eq_radiusDeriv_div_timeDeriv
    {firstAction eccentricity anomaly : ℝ} (hfirstAction : firstAction ≠ 0)
    (hdenominator : 1 - eccentricity * Real.cos anomaly ≠ 0) :
    eccentricRadialMomentum firstAction eccentricity anomaly =
      (firstAction ^ 2 * eccentricity * Real.sin anomaly) /
        (firstAction ^ 3 * (1 - eccentricity * Real.cos anomaly)) := by
  unfold eccentricRadialMomentum
  field_simp [hfirstAction, hdenominator]

theorem strictMono_eccentricMeanAnomaly {eccentricity : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    StrictMono (eccentricMeanAnomaly eccentricity) := by
  apply strictMono_of_hasDerivAt_pos (hasDerivAt_eccentricMeanAnomaly eccentricity)
  intro anomaly
  exact one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne

lemma eccentricMeanAnomaly_add_two_pi (eccentricity anomaly : ℝ) :
    eccentricMeanAnomaly eccentricity (anomaly + 2 * Real.pi) =
      eccentricMeanAnomaly eccentricity anomaly + 2 * Real.pi := by
  simp [eccentricMeanAnomaly]
  ring

/-- The eccentric-anomaly formulas lie on the inertial Kepler energy shell
`-1 / (2 * I₁²)`. -/
theorem polarKeplerEnergy_eccentricPolarState {firstAction eccentricity anomaly polarAngle : ℝ}
    (hfirstAction : firstAction ≠ 0) (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) :
    polarKeplerEnergy
        (eccentricPolarState firstAction eccentricity anomaly polarAngle) =
      -1 / (2 * firstAction ^ 2) := by
  have hdenominator : 1 - eccentricity * Real.cos anomaly ≠ 0 :=
    (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne).ne'
  have hsqrt : (Real.sqrt (1 - eccentricity ^ 2)) ^ 2 = 1 - eccentricity ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith
  have htrig := Real.sin_sq_add_cos_sq anomaly
  have hunit :
      eccentricity ^ 2 * Real.sin anomaly ^ 2 +
          eccentricity ^ 2 * Real.cos anomaly ^ 2 +
        (Real.sqrt (1 - eccentricity ^ 2)) ^ 2 = 1 := by
    rw [hsqrt]
    nlinarith
  have hscaled := congrArg (fun value : ℝ ↦ firstAction ^ 4 * value) hunit
  ring_nf at hscaled
  change
    ((eccentricRadialMomentum firstAction eccentricity anomaly) ^ 2 +
          (angularActionFromEccentricity firstAction eccentricity) ^ 2 /
            (eccentricRadius firstAction eccentricity anomaly) ^ 2) /
          2 -
        1 / eccentricRadius firstAction eccentricity anomaly =
      -1 / (2 * firstAction ^ 2)
  unfold eccentricRadialMomentum angularActionFromEccentricity eccentricRadius
  field_simp [hfirstAction, hdenominator]
  nlinarith only [hunit, hscaled]

end LeanPool.PoincareThreeBody
