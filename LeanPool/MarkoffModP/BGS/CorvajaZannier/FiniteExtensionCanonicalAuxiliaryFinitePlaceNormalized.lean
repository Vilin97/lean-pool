/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalAuxiliaryFinitePlace
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalPlacewiseScaling

/-!
# Canonical finite-place bounds for a normalized derivation

The raw local Wronskian estimates accept an arbitrary clearing scalar.  This
file chooses that scalar from the different at each finite place, so its order
is definitionally replaced by the coefficient of the canonical different
divisor.  These are the four finite-place inputs used by the exhaustive global
summation.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open scoped Polynomial

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
variable {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]

local instance (priority := 10) normalizedCasesPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance normalizedCasesPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance normalizedCasesFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance normalizedCasesFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance normalizedCasesPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance normalizedCasesFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

private abbrev canonicalDifferent : FiniteExtensionPlace K L →₀ ℤ :=
  finiteExtensionCanonicalDifferentDivisor K L
    (finiteExtensionFiniteDifferentIdeal_ne_bot K L)

/-- Canonical finite-place case (i), outside the exceptional set with a pole
of `(1-u)/(1-v)`. -/
theorem finiteExtensionFinitePlace_canonicalAuxiliary_caseI_of_normalized
    (q : FiniteExtensionFinitePlace K L)
    (D : Derivation (frobeniusSubfield L p) L L)
    (hDX : D (algebraMap (RatFunc K) L RatFunc.X) = 1)
    (h k : ℕ) (hn : 0 < h * k + h + k)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huOrder : finitePlaceOrder q u = 0)
    (hvOrder : finitePlaceOrder q v = 0)
    (hrhoOrder : finitePlaceOrder q ((1 - u) / (1 - v)) < 0)
    (hW : (indexedDedekindLocalWronskian D
      (auxiliaryFamilyDerivativeOrder h k)
      (auxiliaryFamily u v h k)).det ≠ 0) :
    ((h * k + h + k : ℕ) : ℤ) *
        finiteExtensionPrincipalDivisor K L ((1 - u) / (1 - v)) (.inl q) ≤
      ((h * k + h + k).choose 2 : ℤ) * canonicalDifferent K L (.inl q) +
        finiteExtensionPrincipalDivisor K L
          (indexedDedekindLocalWronskian D
            (auxiliaryFamilyDerivativeOrder h k)
            (auxiliaryFamily u v h k)).det (.inl q) := by
  obtain ⟨c, hc, hcOrder, hIntegral⟩ :=
    exists_finiteExtensionFinitePlace_canonicalDifferent_scaling_certificate
      K L D hDX q
  have hcase := finiteExtensionFinitePlace_canonicalAuxiliary_caseI
    K L q D c hc hIntegral h k hn u v hu hv hu1 hv1
      huOrder hvOrder hrhoOrder hW
  simpa only [canonicalDifferent, hcOrder] using hcase

/-- Canonical finite-place case (ii), outside the exceptional set without a
pole of `(1-u)/(1-v)`. -/
theorem finiteExtensionFinitePlace_canonicalAuxiliary_caseII_of_normalized
    (q : FiniteExtensionFinitePlace K L)
    (D : Derivation (frobeniusSubfield L p) L L)
    (hDX : D (algebraMap (RatFunc K) L RatFunc.X) = 1)
    (h k : ℕ) (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huOrder : 0 ≤ finitePlaceOrder q u)
    (hvOrder : 0 ≤ finitePlaceOrder q v)
    (hrhoOrder : 0 ≤ finitePlaceOrder q ((1 - u) / (1 - v)))
    (hW : (indexedDedekindLocalWronskian D
      (auxiliaryFamilyDerivativeOrder h k)
      (auxiliaryFamily u v h k)).det ≠ 0) :
    0 ≤ ((h * k + h + k).choose 2 : ℤ) * canonicalDifferent K L (.inl q) +
      finiteExtensionPrincipalDivisor K L
        (indexedDedekindLocalWronskian D
          (auxiliaryFamilyDerivativeOrder h k)
          (auxiliaryFamily u v h k)).det (.inl q) := by
  obtain ⟨c, hc, hcOrder, hIntegral⟩ :=
    exists_finiteExtensionFinitePlace_canonicalDifferent_scaling_certificate
      K L D hDX q
  have hcase := finiteExtensionFinitePlace_canonicalAuxiliary_caseII
    K L q D c hc hIntegral h k u v hu hv hu1 hv1
      huOrder hvOrder hrhoOrder hW
  simpa only [canonicalDifferent, hcOrder] using hcase

/-- Canonical finite-place case (iii), at a positive-order place of `v`. -/
theorem finiteExtensionFinitePlace_canonicalAuxiliary_caseIII_of_normalized
    (q : FiniteExtensionFinitePlace K L)
    (D : Derivation (frobeniusSubfield L p) L L)
    (hDX : D (algebraMap (RatFunc K) L RatFunc.X) = 1)
    (h k : ℕ) (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hW : (indexedDedekindLocalWronskian D
      (auxiliaryFamilyDerivativeOrder h k)
      (auxiliaryFamily u v h k)).det ≠ 0) :
    ((k * (k - 1) / 2 : ℕ) : ℤ) * finiteExtensionPrincipalDivisor K L u (.inl q) +
        ((h * k : ℕ) : ℤ) * finiteExtensionPrincipalDivisor K L v (.inl q) +
      (k : ℤ) * finiteExtensionPrincipalDivisor K L
        ((1 - u) / (1 - v)) (.inl q) +
      finiteExtensionPrincipalDivisor K L
          (finiteExtensionAuxiliaryGridProduct L u v h k) (.inl q) -
        ((h * k + h + k).choose 2 : ℤ) ≤
      ((h * k + h + k).choose 2 : ℤ) * canonicalDifferent K L (.inl q) +
        finiteExtensionPrincipalDivisor K L
          (indexedDedekindLocalWronskian D
            (auxiliaryFamilyDerivativeOrder h k)
            (auxiliaryFamily u v h k)).det (.inl q) := by
  obtain ⟨c, hc, hcOrder, hIntegral⟩ :=
    exists_finiteExtensionFinitePlace_canonicalDifferent_scaling_certificate
      K L D hDX q
  have hcase := finiteExtensionFinitePlace_canonicalAuxiliary_caseIII
    K L q D c hc hIntegral h k u v hu hv hu1 hv1 hW
  simpa only [canonicalDifferent, hcOrder] using hcase

/-- Canonical finite-place case (iv), at a nonpositive-order place of `v`. -/
theorem finiteExtensionFinitePlace_canonicalAuxiliary_caseIV_of_normalized
    (q : FiniteExtensionFinitePlace K L)
    (D : Derivation (frobeniusSubfield L p) L L)
    (hDX : D (algebraMap (RatFunc K) L RatFunc.X) = 1)
    (h k : ℕ) (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hW : (indexedDedekindLocalWronskian D
      (auxiliaryFamilyDerivativeOrder h k)
      (auxiliaryFamily u v h k)).det ≠ 0) :
    ((k * (k - 1) / 2 : ℕ) : ℤ) * finiteExtensionPrincipalDivisor K L u (.inl q) +
      (k : ℤ) * finiteExtensionPrincipalDivisor K L
        ((1 - u) / (1 - v)) (.inl q) +
      finiteExtensionPrincipalDivisor K L
          (finiteExtensionAuxiliaryGridProduct L u v h k) (.inl q) -
        ((h * k + h + k).choose 2 : ℤ) ≤
      ((h * k + h + k).choose 2 : ℤ) * canonicalDifferent K L (.inl q) +
        finiteExtensionPrincipalDivisor K L
          (indexedDedekindLocalWronskian D
            (auxiliaryFamilyDerivativeOrder h k)
            (auxiliaryFamily u v h k)).det (.inl q) := by
  obtain ⟨c, hc, hcOrder, hIntegral⟩ :=
    exists_finiteExtensionFinitePlace_canonicalDifferent_scaling_certificate
      K L D hDX q
  have hcase := finiteExtensionFinitePlace_canonicalAuxiliary_caseIV
    K L q D c hc hIntegral h k u v hu hv hu1 hv1 hW
  simpa only [canonicalDifferent, hcOrder] using hcase

end

end BGS.CorvajaZannier
