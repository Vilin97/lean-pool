/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.OddSchwartzAntiderivative
import LeanPool.QuadraticCarleson.QuadraticCarleson.PVFourier

/-!
# Fourier transform of the canonical principal-value distribution

This file closes the final uniqueness step in the Fourier characterization of
`p.v. (1 / x)`. The analytic distribution identities are proved in
`PVFourier`; the required one-dimensional Schwartz antiderivative theorem is
proved in `OddSchwartzAntiderivative`.
-/

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace QuadraticCarleson

/-- With Mathlib's Fourier-transform normalization,
`𝓕 (p.v. (1 / x)) = -π i sign`. -/
theorem fourier_principalValueOneDiv :
    𝓕 principalValueOneDiv =
      (-((Real.pi : ℂ) * Complex.I)) • signTemperedDistribution :=
  fourier_principalValueOneDiv_of_odd_schwartz_antiderivatives
    exists_schwartz_antiderivative_of_odd

/-- The direct symmetric-limit construction of `p.v. (1 / x)` agrees with
the equivalent inverse-Fourier construction. -/
theorem principalValueOneDiv_eq_FourierCandidate :
    principalValueOneDiv = principalValueOneDivFourierCandidate :=
  principalValueOneDiv_eq_FourierCandidate_of_odd_schwartz_antiderivatives
    exists_schwartz_antiderivative_of_odd

end QuadraticCarleson
