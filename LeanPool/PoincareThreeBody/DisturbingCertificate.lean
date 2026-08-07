/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DisturbingFunction
import LeanPool.PoincareThreeBody.ValidatedQuadrature

/-!
# Finite certificates for nonconstant resonant averages

To prove that a Poincaré disturbing average is nonconstant, it is enough to compare its values at
two phases. This file reduces that comparison to a finite trapezoidal sum plus a certified global
bound on the second time derivative of the integrand difference.
-/

namespace LeanPool.PoincareThreeBody

open MeasureTheory
open scoped Interval

/-- Difference between the disturbing functions at two orientation phases. -/
noncomputable def resonantDisturbingDifference
    (p q : ℕ) (eccentricity phaseA phaseB time : ℝ) : ℝ :=
  resonantDisturbingFunction p q eccentricity phaseA time -
    resonantDisturbingFunction p q eccentricity phaseB time

theorem contDiffOn_resonantDisturbingDifference
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity phaseA phaseB start finish : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    ContDiffOn ℝ 2
      (resonantDisturbingDifference p q eccentricity phaseA phaseB) [[start, finish]] := by
  have hsmoothA : ContDiff ℝ 2
      (resonantDisturbingFunction p q eccentricity phaseA) := by
    rw [contDiff_iff_contDiffAt]
    intro time
    exact (analyticAt_resonantDisturbingFunction_time hp hq heccentricity
      heccentricityOne hapoapsis).contDiffAt
  have hsmoothB : ContDiff ℝ 2
      (resonantDisturbingFunction p q eccentricity phaseB) := by
    rw [contDiff_iff_contDiffAt]
    intro time
    exact (analyticAt_resonantDisturbingFunction_time hp hq heccentricity
      heccentricityOne hapoapsis).contDiffAt
  exact (hsmoothA.sub hsmoothB).contDiffOn

/-- A finite trapezoidal certificate for the phase difference proves that the exact Poincaré
averages at those phases are distinct. -/
theorem resonantDisturbingAverage_ne_of_trapezoidal_certificate
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity phaseA phaseB errorBound : ℝ} {steps : ℕ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1)
    (hsecondDerivative : ∀ time,
      |iteratedDerivWithin 2
        (resonantDisturbingDifference p q eccentricity phaseA phaseB)
        [[0, resonantOrbitPeriod p]] time| ≤ errorBound)
    (hsteps : 0 < steps)
    (hcertificate : |resonantOrbitPeriod p| ^ 3 * errorBound / (12 * steps ^ 2) <
      |trapezoidal_integral
        (resonantDisturbingDifference p q eccentricity phaseA phaseB)
        steps 0 (resonantOrbitPeriod p)|) :
    resonantDisturbingAverage p q eccentricity phaseA ≠
      resonantDisturbingAverage p q eccentricity phaseB := by
  have hnonzero := intervalIntegral_ne_zero_of_trapezoidal_certificate
    (contDiffOn_resonantDisturbingDifference hp hq heccentricity heccentricityOne
      hapoapsis) hsecondDerivative hsteps (by simpa using hcertificate)
  have hintegrableA := intervalIntegrable_resonantDisturbingFunction hp hq heccentricity
    heccentricityOne hapoapsis (orientation := phaseA) (start := 0)
      (finish := resonantOrbitPeriod p)
  have hintegrableB := intervalIntegrable_resonantDisturbingFunction hp hq heccentricity
    heccentricityOne hapoapsis (orientation := phaseB) (start := 0)
      (finish := resonantOrbitPeriod p)
  intro hvalues
  apply hnonzero
  unfold resonantDisturbingDifference
  rw [intervalIntegral.integral_sub hintegrableA hintegrableB]
  exact sub_eq_zero.mpr (by simpa [resonantDisturbingAverage] using hvalues)

/-- The same finite certificate produces an orientation with a nonzero derivative of the exact
Poincaré average. -/
theorem exists_deriv_resonantDisturbingAverage_ne_zero_of_trapezoidal_certificate
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity phaseA phaseB errorBound : ℝ} {steps : ℕ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1)
    (hsecondDerivative : ∀ time,
      |iteratedDerivWithin 2
        (resonantDisturbingDifference p q eccentricity phaseA phaseB)
        [[0, resonantOrbitPeriod p]] time| ≤ errorBound)
    (hsteps : 0 < steps)
    (hcertificate : |resonantOrbitPeriod p| ^ 3 * errorBound / (12 * steps ^ 2) <
      |trapezoidal_integral
        (resonantDisturbingDifference p q eccentricity phaseA phaseB)
        steps 0 (resonantOrbitPeriod p)|) :
    ∃ orientation,
      deriv (resonantDisturbingAverage p q eccentricity) orientation ≠ 0 := by
  apply exists_deriv_resonantDisturbingAverage_ne_zero_of_values_ne hp hq heccentricity
    heccentricityOne hapoapsis
  exact resonantDisturbingAverage_ne_of_trapezoidal_certificate hp hq heccentricity
    heccentricityOne hapoapsis hsecondDerivative hsteps hcertificate

end LeanPool.PoincareThreeBody
