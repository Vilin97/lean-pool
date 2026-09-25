/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalAuxiliaryFinitePlaceNormalized
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalGlobalGcdBound

/-!
# Global canonical bound from a normalized derivation

The finite-place branch is now completely automatic: the different supplies
the canonical clearing scalar, and the four local estimates are selected after
splitting the exhaustive place type.  This module leaves only the four
corresponding infinity statements as explicit inputs.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open scoped BigOperators Polynomial

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
variable {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]

local instance (priority := 10) globalNormalizedPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance globalNormalizedPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance globalNormalizedFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance globalNormalizedFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance globalNormalizedPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance globalNormalizedFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

attribute [local instance] Classical.decEq

/-- A normalized Frobenius-constant derivation and the four infinity cases
imply the exact exhaustive Proposition 2 gcd estimate. -/
theorem finiteExtensionGcdBound_of_normalizedCanonicalInfinityPlacewiseBounds
    (D : Derivation (frobeniusSubfield L p) L L)
    (hDX : D (algebraMap (RatFunc K) L RatFunc.X) = 1)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (huone : u ≠ 1) (hvone : v ≠ 1)
    (h k : ℕ) (hn : 0 < h * k + h + k) (chi : ℕ)
    (hWronskian :
      (indexedDedekindLocalWronskian D
        (auxiliaryFamilyDerivativeOrder h k)
        (auxiliaryFamily u v h k)).det ≠ 0)
    (hEuler :
      finiteExtensionDivisorDegree K L
          (finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) +
        (∑ P ∈ propositionTwoExceptionalPlaces K L u v,
          finiteExtensionPlaceDegree K L P : ℤ) ≤ (chi : ℤ))
    (hInfinityCaseI : ∀ P : FiniteExtensionInfinityPlace K L,
      (Sum.inr P : FiniteExtensionPlace K L) ∉
        propositionTwoExceptionalPlaces K L u v →
      finiteExtensionPrincipalDivisor K L ((1 - u) / (1 - v)) (.inr P) < 0 →
      ((h * k + h + k : ℕ) : ℤ) *
          finiteExtensionPrincipalDivisor K L ((1 - u) / (1 - v)) (.inr P) ≤
        ((h * k + h + k).choose 2 : ℤ) *
            finiteExtensionCanonicalDifferentDivisor K L
              (finiteExtensionFiniteDifferentIdeal_ne_bot K L) (.inr P) +
          finiteExtensionPrincipalDivisor K L
            (indexedDedekindLocalWronskian D
              (auxiliaryFamilyDerivativeOrder h k)
              (auxiliaryFamily u v h k)).det (.inr P))
    (hInfinityCaseII : ∀ P : FiniteExtensionInfinityPlace K L,
      (Sum.inr P : FiniteExtensionPlace K L) ∉
        propositionTwoExceptionalPlaces K L u v →
      0 ≤ finiteExtensionPrincipalDivisor K L ((1 - u) / (1 - v)) (.inr P) →
      0 ≤ ((h * k + h + k).choose 2 : ℤ) *
          finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L) (.inr P) +
        finiteExtensionPrincipalDivisor K L
          (indexedDedekindLocalWronskian D
            (auxiliaryFamilyDerivativeOrder h k)
            (auxiliaryFamily u v h k)).det (.inr P))
    (hInfinityCaseIII : ∀ P : FiniteExtensionInfinityPlace K L,
      (Sum.inr P : FiniteExtensionPlace K L) ∈
        propositionTwoExceptionalPlaces K L u v →
      0 < finiteExtensionPrincipalDivisor K L v (.inr P) →
      ((k * (k - 1) / 2 : ℕ) : ℤ) *
            finiteExtensionPrincipalDivisor K L u (.inr P) +
          ((h * k : ℕ) : ℤ) * finiteExtensionPrincipalDivisor K L v (.inr P) +
        (k : ℤ) * finiteExtensionPrincipalDivisor K L
          ((1 - u) / (1 - v)) (.inr P) +
        finiteExtensionPrincipalDivisor K L
            (finiteExtensionAuxiliaryGridProduct L u v h k) (.inr P) -
          ((h * k + h + k).choose 2 : ℤ) ≤
        ((h * k + h + k).choose 2 : ℤ) *
            finiteExtensionCanonicalDifferentDivisor K L
              (finiteExtensionFiniteDifferentIdeal_ne_bot K L) (.inr P) +
          finiteExtensionPrincipalDivisor K L
            (indexedDedekindLocalWronskian D
              (auxiliaryFamilyDerivativeOrder h k)
              (auxiliaryFamily u v h k)).det (.inr P))
    (hInfinityCaseIV : ∀ P : FiniteExtensionInfinityPlace K L,
      (Sum.inr P : FiniteExtensionPlace K L) ∈
        propositionTwoExceptionalPlaces K L u v →
      finiteExtensionPrincipalDivisor K L v (.inr P) ≤ 0 →
      ((k * (k - 1) / 2 : ℕ) : ℤ) *
            finiteExtensionPrincipalDivisor K L u (.inr P) +
        (k : ℤ) * finiteExtensionPrincipalDivisor K L
          ((1 - u) / (1 - v)) (.inr P) +
        finiteExtensionPrincipalDivisor K L
            (finiteExtensionAuxiliaryGridProduct L u v h k) (.inr P) -
          ((h * k + h + k).choose 2 : ℤ) ≤
        ((h * k + h + k).choose 2 : ℤ) *
            finiteExtensionCanonicalDifferentDivisor K L
              (finiteExtensionFiniteDifferentIdeal_ne_bot K L) (.inr P) +
          finiteExtensionPrincipalDivisor K L
            (indexedDedekindLocalWronskian D
              (auxiliaryFamilyDerivativeOrder h k)
              (auxiliaryFamily u v h k)).det (.inr P)) :
    (finiteExtensionGcdWeightedDegree K L (1 - u) (1 - v) : ℝ) ≤
      ((h + 2 * k : ℕ) : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
          (finiteExtensionPositiveDegree K L v : ℝ) +
        (k : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
          (finiteExtensionPositiveDegree K L u : ℝ) +
        ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * (chi : ℝ) := by
  let W := (indexedDedekindLocalWronskian D
    (auxiliaryFamilyDerivativeOrder h k)
    (auxiliaryFamily u v h k)).det
  apply finiteExtensionGcdBound_of_canonicalPlacewiseBounds
    K L u v W hu hv huone hvone hWronskian h k hn chi hEuler
  · intro P hP hrho
    cases P with
    | inl q =>
        have huOrder : finitePlaceOrder q u = 0 := by
          simpa only [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder] using
            finiteExtensionPrincipalDivisor_u_eq_zero_outside_propositionTwoExceptionalPlaces
              K L u v (.inl q) hP
        have hvOrder : finitePlaceOrder q v = 0 := by
          simpa only [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder] using
            finiteExtensionPrincipalDivisor_v_eq_zero_outside_propositionTwoExceptionalPlaces
              K L u v (.inl q) hP
        exact finiteExtensionFinitePlace_canonicalAuxiliary_caseI_of_normalized
          K L q D hDX h k hn u v hu hv huone hvone huOrder hvOrder
            (by simpa only [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder]
              using hrho)
            hWronskian
    | inr P => exact hInfinityCaseI P hP hrho
  · intro P hP hrho
    cases P with
    | inl q =>
        have huOrder : finitePlaceOrder q u = 0 := by
          simpa only [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder] using
            finiteExtensionPrincipalDivisor_u_eq_zero_outside_propositionTwoExceptionalPlaces
              K L u v (.inl q) hP
        have hvOrder : finitePlaceOrder q v = 0 := by
          simpa only [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder] using
            finiteExtensionPrincipalDivisor_v_eq_zero_outside_propositionTwoExceptionalPlaces
              K L u v (.inl q) hP
        exact finiteExtensionFinitePlace_canonicalAuxiliary_caseII_of_normalized
          K L q D hDX h k u v hu hv huone hvone huOrder.ge hvOrder.ge
            (by simpa only [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder]
              using hrho)
            hWronskian
    | inr P => exact hInfinityCaseII P hP hrho
  · intro P hP hvP
    cases P with
    | inl q =>
        exact finiteExtensionFinitePlace_canonicalAuxiliary_caseIII_of_normalized
          K L q D hDX h k u v hu hv huone hvone hWronskian
    | inr P => exact hInfinityCaseIII P hP hvP
  · intro P hP hvP
    cases P with
    | inl q =>
        exact finiteExtensionFinitePlace_canonicalAuxiliary_caseIV_of_normalized
          K L q D hDX h k u v hu hv huone hvone hWronskian
    | inr P => exact hInfinityCaseIV P hP hvP

end

end BGS.CorvajaZannier
