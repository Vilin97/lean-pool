/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanMergelyan

/-!
# Crouzeix--Palencia assembly from smooth Jordan geometry

The unconditional Mergelyan theorem for smooth convex Jordan domains removes
the analytic approximation hypotheses from the terminal exhaustion
assemblies.  What remains is purely geometric: construct a strictly nested
smooth Jordan exhaustion, or realize the explicit convex thickenings by such
domains.
-/

open Complex Set
open scoped InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Every strict smooth-Jordan exhaustion of the closed numerical range gives
the exact Crouzeix--Palencia polynomial spectral-set bound. -/
theorem crouzeix_palencia_of_strictNestedSmoothJordanExhaustion
    (A : E →L[ℂ] E)
    (Omega : StrictNestedSmoothJordanExhaustion
      (closure (numericalRange A))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeixPalencia_of_nestedExhaustion_canonical_mergelyanApproximation
      A Omega
  intro n
  exact (Omega.domain n).hasMergelyanPolynomialApproximation

/-- Smooth Jordan realizations of the explicit metric thickenings discharge
all analytic inputs to the Crouzeix--Palencia assembly. -/
theorem crouzeix_palencia_of_convexThickening_smoothJordanRealization
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply crouzeix_palencia_of_convexThickening_hasMergelyanPolynomialApproximation
    A Omega hcarrier
  intro n
  exact (Omega n).hasMergelyanPolynomialApproximation

/-- Existence-only form of the explicit-thickening boundary: once each
thickening has a smooth Jordan realization, the sharp bound follows. -/
theorem crouzeix_palencia_of_exists_convexThickening_smoothJordanRealization
    (A : E →L[ℂ] E)
    (hrealize : ∃ Omega : ℕ → SmoothJordanDomain,
      ∀ n, (Omega n).carrier =
        convexThickeningApprox (closure (numericalRange A)) n) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  obtain ⟨Omega, hcarrier⟩ := hrealize
  exact crouzeix_palencia_of_convexThickening_smoothJordanRealization
    A Omega hcarrier

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
