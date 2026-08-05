/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.Resonance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith

/-!
# Averaging the first homological equation

On a resonant periodic orbit, the first-order correction to a putative first integral is periodic.
Integrating its derivative over one period removes that term. A nonzero averaged perturbation then
forces the leading differential of the integral to annihilate the resonance vector.
-/

namespace LeanPool.PoincareThreeBody

open MeasureTheory Set
open scoped Interval

/-- The derivative of a periodic scalar function has zero integral over a period. -/
theorem intervalIntegral_derivative_eq_zero_of_endpoints_eq
    {correction correctionDerivative : ℝ → ℝ} {period : ℝ}
    (hderiv : ∀ time ∈ uIcc 0 period,
      HasDerivAt correction (correctionDerivative time) time)
    (hintegrable : IntervalIntegrable correctionDerivative volume 0 period)
    (hperiodic : correction period = correction 0) :
    ∫ time in 0..period, correctionDerivative time = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintegrable, hperiodic, sub_self]

/-- Averaging a scalar first homological equation over a periodic orbit kills its correction
term. -/
theorem coefficient_eq_zero_of_averaged_homologicalEquation
    {correction correctionDerivative forcing : ℝ → ℝ} {coefficient period : ℝ}
    (hderiv : ∀ time ∈ uIcc 0 period,
      HasDerivAt correction (correctionDerivative time) time)
    (hcorrectionIntegrable : IntervalIntegrable correctionDerivative volume 0 period)
    (hforcingIntegrable : IntervalIntegrable forcing volume 0 period)
    (hperiodic : correction period = correction 0)
    (hforcing : ∫ time in 0..period, forcing time ≠ 0)
    (hequation : ∀ time ∈ uIcc 0 period,
      correctionDerivative time + coefficient * forcing time = 0) :
    coefficient = 0 := by
  have hderivativeIntegral : ∫ time in 0..period, correctionDerivative time = 0 :=
    intervalIntegral_derivative_eq_zero_of_endpoints_eq hderiv hcorrectionIntegrable hperiodic
  have hequationIntegral :
      ∫ time in 0..period,
          correctionDerivative time + coefficient * forcing time = 0 := by
    rw [intervalIntegral.integral_congr fun time htime ↦ hequation time htime]
    simp
  rw [intervalIntegral.integral_add hcorrectionIntegrable
      (hforcingIntegrable.const_mul coefficient),
    intervalIntegral.integral_const_mul, hderivativeIntegral, zero_add] at hequationIntegral
  exact (mul_eq_zero.mp hequationIntegral).resolve_right hforcing

/-- A nonzero averaged perturbation on a resonant orbit yields Poincaré's two-dimensional
linear-dependence obstruction. -/
theorem averagedHomologicalEquation_obstruction
    {k frequency differential : ActionSpace}
    {correction correctionDerivative forcing : ℝ → ℝ} {period : ℝ}
    (hk : k ≠ 0) (hresonance : dot k frequency = 0)
    (hderiv : ∀ time ∈ uIcc 0 period,
      HasDerivAt correction (correctionDerivative time) time)
    (hcorrectionIntegrable : IntervalIntegrable correctionDerivative volume 0 period)
    (hforcingIntegrable : IntervalIntegrable forcing volume 0 period)
    (hperiodic : correction period = correction 0)
    (hforcing : ∫ time in 0..period, forcing time ≠ 0)
    (hequation : ∀ time ∈ uIcc 0 period,
      correctionDerivative time + dot k differential * forcing time = 0) :
    ¬LinearIndependent ℝ ![frequency, differential] := by
  have hdifferential : dot k differential = 0 :=
    coefficient_eq_zero_of_averaged_homologicalEquation hderiv hcorrectionIntegrable
      hforcingIntegrable hperiodic hforcing hequation
  exact not_linearIndependent_of_common_resonance hk hresonance hdifferential

end LeanPool.PoincareThreeBody
