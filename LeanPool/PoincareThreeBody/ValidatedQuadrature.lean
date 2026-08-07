/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

/-!
# Validated quadrature certificates

These lemmas turn a finite trapezoidal sum and a certified second-derivative bound into a theorem
about the exact interval integral. They form the narrow interface through which a verified finite
computation can discharge a nonvanishing obligation in the Poincaré argument.
-/

namespace LeanPool.PoincareThreeBody

open scoped Interval

/-- If the absolute trapezoidal approximation exceeds its certified error bound, the exact
integral is nonzero. -/
theorem intervalIntegral_ne_zero_of_trapezoidal_certificate
    {f : ℝ → ℝ} {a b errorBound : ℝ} {steps : ℕ}
    (hsmooth : ContDiffOn ℝ 2 f [[a, b]])
    (hsecondDerivative : ∀ x,
      |iteratedDerivWithin 2 f [[a, b]] x| ≤ errorBound)
    (hsteps : 0 < steps)
    (hcertificate : |b - a| ^ 3 * errorBound / (12 * steps ^ 2) <
      |trapezoidal_integral f steps a b|) :
    ∫ x in a..b, f x ≠ 0 := by
  intro hintegral
  have herror := trapezoidal_error_le_of_c2 hsmooth hsecondDerivative hsteps
  unfold trapezoidal_error at herror
  rw [hintegral, sub_zero] at herror
  exact (not_le_of_gt hcertificate) herror

/-- A positive trapezoidal approximation larger than its certified error bound forces the exact
integral to be positive. -/
theorem intervalIntegral_pos_of_trapezoidal_certificate
    {f : ℝ → ℝ} {a b errorBound : ℝ} {steps : ℕ}
    (hsmooth : ContDiffOn ℝ 2 f [[a, b]])
    (hsecondDerivative : ∀ x,
      |iteratedDerivWithin 2 f [[a, b]] x| ≤ errorBound)
    (hsteps : 0 < steps)
    (hcertificate : |b - a| ^ 3 * errorBound / (12 * steps ^ 2) <
      trapezoidal_integral f steps a b) :
    0 < ∫ x in a..b, f x := by
  have herror := trapezoidal_error_le_of_c2 hsmooth hsecondDerivative hsteps
  have hupper : trapezoidal_error f steps a b ≤
      |b - a| ^ 3 * errorBound / (12 * steps ^ 2) :=
    (le_abs_self _).trans herror
  unfold trapezoidal_error at hupper
  linarith

end LeanPool.PoincareThreeBody
