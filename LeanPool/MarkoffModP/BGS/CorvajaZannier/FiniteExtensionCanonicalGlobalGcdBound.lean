/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalGcdBound
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalDifferentDivisor
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalPlaceSum
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionExceptionalPlaceBounds
import Mathlib.Tactic

/-!
# Canonical placewise bounds imply the exhaustive gcd estimate

This is the global composition boundary for Corvaja--Zannier Proposition 2.
It fixes the canonical different divisor and the direct zero-and-pole
exceptional set, discharges all support bookkeeping, performs the exhaustive
weighted place sum, and then converts the resulting Wronskian inequality into
the numerical gcd estimate.
-/

namespace BGS.CorvajaZannier

noncomputable section

open scoped BigOperators

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

attribute [local instance] Classical.decEq

/-- The four canonical local estimates, together with the logarithmic Euler
degree bound, imply the exact exhaustive weighted gcd bound of Proposition 2.
-/
theorem finiteExtensionGcdBound_of_canonicalPlacewiseBounds
    (u v W : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (huone : u ≠ 1) (hvone : v ≠ 1) (hW : W ≠ 0)
    (h k : ℕ) (hn : 0 < h * k + h + k) (chi : ℕ)
    (hEuler :
      finiteExtensionDivisorDegree K L
          (finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) +
        (∑ P ∈ propositionTwoExceptionalPlaces K L u v,
          finiteExtensionPlaceDegree K L P : ℤ) ≤ (chi : ℤ))
    (hCaseI : ∀ P,
      P ∉ propositionTwoExceptionalPlaces K L u v →
      finiteExtensionPrincipalDivisor K L ((1 - u) / (1 - v)) P < 0 →
      ((h * k + h + k : ℕ) : ℤ) *
          finiteExtensionPrincipalDivisor K L ((1 - u) / (1 - v)) P ≤
        ((h * k + h + k).choose 2 : ℤ) *
            finiteExtensionCanonicalDifferentDivisor K L
              (finiteExtensionFiniteDifferentIdeal_ne_bot K L) P +
          finiteExtensionPrincipalDivisor K L W P)
    (hCaseII : ∀ P,
      P ∉ propositionTwoExceptionalPlaces K L u v →
      0 ≤ finiteExtensionPrincipalDivisor K L ((1 - u) / (1 - v)) P →
      0 ≤ ((h * k + h + k).choose 2 : ℤ) *
          finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L) P +
        finiteExtensionPrincipalDivisor K L W P)
    (hCaseIII : ∀ P,
      P ∈ propositionTwoExceptionalPlaces K L u v →
      0 < finiteExtensionPrincipalDivisor K L v P →
      ((k * (k - 1) / 2 : ℕ) : ℤ) *
            finiteExtensionPrincipalDivisor K L u P +
          ((h * k : ℕ) : ℤ) * finiteExtensionPrincipalDivisor K L v P +
        (k : ℤ) * finiteExtensionPrincipalDivisor K L
          ((1 - u) / (1 - v)) P +
        finiteExtensionPrincipalDivisor K L
            (finiteExtensionAuxiliaryGridProduct L u v h k) P -
          ((h * k + h + k).choose 2 : ℤ) ≤
        ((h * k + h + k).choose 2 : ℤ) *
            finiteExtensionCanonicalDifferentDivisor K L
              (finiteExtensionFiniteDifferentIdeal_ne_bot K L) P +
          finiteExtensionPrincipalDivisor K L W P)
    (hCaseIV : ∀ P,
      P ∈ propositionTwoExceptionalPlaces K L u v →
      finiteExtensionPrincipalDivisor K L v P ≤ 0 →
      ((k * (k - 1) / 2 : ℕ) : ℤ) *
            finiteExtensionPrincipalDivisor K L u P +
        (k : ℤ) * finiteExtensionPrincipalDivisor K L
          ((1 - u) / (1 - v)) P +
        finiteExtensionPrincipalDivisor K L
            (finiteExtensionAuxiliaryGridProduct L u v h k) P -
          ((h * k + h + k).choose 2 : ℤ) ≤
        ((h * k + h + k).choose 2 : ℤ) *
            finiteExtensionCanonicalDifferentDivisor K L
              (finiteExtensionFiniteDifferentIdeal_ne_bot K L) P +
          finiteExtensionPrincipalDivisor K L W P) :
    (finiteExtensionGcdWeightedDegree K L (1 - u) (1 - v) : ℝ) ≤
      ((h + 2 * k : ℕ) : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
          (finiteExtensionPositiveDegree K L v : ℝ) +
        (k : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
          (finiteExtensionPositiveDegree K L u : ℝ) +
        ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * (chi : ℝ) := by
  let S := propositionTwoExceptionalPlaces K L u v
  let canonical := finiteExtensionCanonicalDifferentDivisor K L
    (finiteExtensionFiniteDifferentIdeal_ne_bot K L)
  let rho := (1 - u) / (1 - v)
  let grid := finiteExtensionAuxiliaryGridProduct L u v h k
  have hgrid : grid ≠ 0 := by
    dsimp only [grid, finiteExtensionAuxiliaryGridProduct]
    exact Finset.prod_ne_zero_iff.mpr fun rs _ =>
      mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hv)
  have hUOutside : ∀ P, P ∉ S →
      finiteExtensionPrincipalDivisor K L u P = 0 := by
    intro P hP
    exact
      finiteExtensionPrincipalDivisor_u_eq_zero_outside_propositionTwoExceptionalPlaces
        K L u v P hP
  have hGridOutside : ∀ P, P ∉ S →
      finiteExtensionPrincipalDivisor K L grid P = 0 := by
    intro P hP
    exact
      finiteExtensionPrincipalDivisor_auxiliaryGridProduct_eq_zero_outside_propositionTwoExceptionalPlaces
        K L u v hu hv h k P hP
  have hVPositiveSupport : ∀ P,
      0 < finiteExtensionPrincipalDivisor K L v P → P ∈ S := by
    intro P hP
    exact mem_propositionTwoExceptionalPlaces_of_v_order_pos K L u v P hP
  have hRhoSupport :
      -((finiteExtensionPositiveDegree K L u : ℤ) +
          (finiteExtensionPositiveDegree K L v : ℤ)) ≤
        ∑ P ∈ S, finiteExtensionPrincipalDivisor K L rho P *
          (finiteExtensionPlaceDegree K L P : ℤ) := by
    have hbound := finiteExtensionOneSubU_div_oneSubV_weightedOrder_lower_bound
      K L u v hu hv huone hvone S
    dsimp only [rho]
    linarith
  have hGlobal :=
    globalWronskianInequality_of_finiteExtensionCanonicalPlacewiseBounds
      K L S canonical u v rho grid W h k (h * k + h + k)
        ((h * k + h + k).choose 2) chi hu hgrid hW
        hUOutside hGridOutside hVPositiveSupport
        (by simpa only [S, canonical] using hEuler)
        hRhoSupport
        (by simpa only [S, canonical, rho] using hCaseI)
        (by simpa only [S, canonical, rho] using hCaseII)
        (by simpa only [S, canonical, rho, grid] using hCaseIII)
        (by simpa only [S, canonical, rho, grid] using hCaseIV)
  exact finiteExtensionGcdBound_of_canonicalWronskianInequality
    K L u v hu hv huone hvone h k hn chi (by
      simpa only [S, rho, add_comm, Int.ofNat_eq_natCast] using hGlobal)

end

end BGS.CorvajaZannier
