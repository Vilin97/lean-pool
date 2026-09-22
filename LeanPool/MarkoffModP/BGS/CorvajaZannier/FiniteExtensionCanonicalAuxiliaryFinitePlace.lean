/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.AuxiliaryFamilyIndexing
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryFinitePlace
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryFinitePlaceCases
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionExceptionalSupport
import LeanPool.MarkoffModP.BGS.CorvajaZannier.TorsionExhaustiveGcdDivisorBound
import Mathlib.Tactic

/-!
# Finite-place cases for the canonical auxiliary family

Prove the local auxiliary-family inequalities at finite places, including the grid-order and
derivative-order sums.
-/

namespace BGS.CorvajaZannier

noncomputable section

open scoped nonZeroDivisors Polynomial BigOperators
open IsDedekindDomain

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
variable {C : Type*} [Field C] [Algebra C L]

local instance (priority := 10) finiteCanonicalCasesPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance finiteCanonicalCasesPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance finiteCanonicalCasesFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance finiteCanonicalCasesFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance finiteCanonicalCasesPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance finiteCanonicalCasesFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

private theorem finiteExtensionFinitePlace_gridOrder_sum_eq
    (q : FiniteExtensionFinitePlace K L)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0) (h k : ℕ) :
    (∑ rs : Fin (k + 1) × Fin h,
      finitePlaceOrder q (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ))) =
      finiteExtensionPrincipalDivisor K L
        (finiteExtensionAuxiliaryGridProduct L u v h k) (.inl q) := by
  have hdiv := congrArg (fun D : FiniteExtensionPlace K L →₀ ℤ => D (.inl q))
    (finiteExtensionPrincipalDivisor_auxiliaryGridProduct K L u v hu hv h k)
  rw [hdiv]
  rw [Finset.sum_apply']
  apply Finset.sum_congr rfl
  intro rs hrs
  have hmul := congrArg (fun D : FiniteExtensionPlace K L →₀ ℤ => D (.inl q))
    (finiteExtensionPrincipalDivisor_mul K L
      (u ^ (rs.1 : ℕ)) (v ^ (rs.2 : ℕ))
      (pow_ne_zero _ hu) (pow_ne_zero _ hv))
  have hupow := congrArg (fun D : FiniteExtensionPlace K L →₀ ℤ => D (.inl q))
    (finiteExtensionPrincipalDivisor_pow K L u hu (rs.1 : ℕ))
  have hvpow := congrArg (fun D : FiniteExtensionPlace K L →₀ ℤ => D (.inl q))
    (finiteExtensionPrincipalDivisor_pow K L v hv (rs.2 : ℕ))
  simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
    finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder] at hmul hupow hvpow
  rw [hmul, hupow, hvpow]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
    finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder]

private theorem auxiliaryFamilyDerivativeOrder_sum_int (h k : ℕ) :
    (∑ i : Sum (Fin k) (Fin (k + 1) × Fin h),
      (auxiliaryFamilyDerivativeOrder h k i : ℤ)) =
      ((h * k + h + k).choose 2 : ℤ) := by
  exact_mod_cast auxiliaryFamilyDerivativeOrder_sum h k

private theorem finitePlaceOrder_gridMonomial_eq_zero
    (q : FiniteExtensionFinitePlace K L)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (huOrder : finitePlaceOrder q u = 0)
    (hvOrder : finitePlaceOrder q v = 0)
    (i j : ℕ) :
    finitePlaceOrder q (u ^ i * v ^ j) = 0 := by
  have hmul := congrArg (fun E : FiniteExtensionPlace K L →₀ ℤ => E (.inl q))
    (finiteExtensionPrincipalDivisor_mul K L
      (u ^ i) (v ^ j) (pow_ne_zero _ hu) (pow_ne_zero _ hv))
  have hupow := congrArg (fun E : FiniteExtensionPlace K L →₀ ℤ => E (.inl q))
    (finiteExtensionPrincipalDivisor_pow K L u hu i)
  have hvpow := congrArg (fun E : FiniteExtensionPlace K L →₀ ℤ => E (.inl q))
    (finiteExtensionPrincipalDivisor_pow K L v hv j)
  simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
    finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder] at hmul hupow hvpow
  rw [hmul, hupow, hvpow, huOrder, hvOrder]
  simp

/-- Finite-place source case (i), specialized to the consecutive derivative
orders on the source auxiliary family. -/
theorem finiteExtensionFinitePlace_canonicalAuxiliary_caseI
    {p : ℕ} [Fact p.Prime] [CharP L p] [Fintype K]
    (q : FiniteExtensionFinitePlace K L)
    (D : Derivation (frobeniusSubfield L p) L L)
    (c : L) (hc : c ≠ 0)
    (hScaledIntegral :
      ∀ r : FiniteExtensionFinitePlaceLocalRing K L q,
        ∃ s : FiniteExtensionFinitePlaceLocalRing K L q,
          (c • D) (finiteExtensionFinitePlaceLocalizationToField
              (K := K) (L := L) q r) =
            finiteExtensionFinitePlaceLocalizationToField
              (K := K) (L := L) q s)
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
      ((h * k + h + k).choose 2 : ℤ) * finitePlaceOrder q c +
        finiteExtensionPrincipalDivisor K L
          (indexedDedekindLocalWronskian D
            (auxiliaryFamilyDerivativeOrder h k)
            (auxiliaryFamily u v h k)).det (.inl q) := by
  let n := h * k + h + k
  have hrho : (1 - u) / (1 - v) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hu1.symm) (sub_ne_zero.mpr hv1.symm)
  have huTop :
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q u = 0 := by
    rw [finiteExtensionFinitePlaceLocalOrderTop_eq_globalOrder q u hu]
    exact_mod_cast huOrder
  have hrhoLocal :
      finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
        ((1 - u) / (1 - v)) < 0 := by
    rw [finiteExtensionFinitePlaceLocalOrder_eq_globalOrder]
    exact hrhoOrder
  have hgridRegular : ∀ rs : Fin (k + 1) × Fin h,
      (0 : WithTop ℤ) ≤
        finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q
          (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) := by
    intro rs
    have hmonomial : u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hv)
    rw [finiteExtensionFinitePlaceLocalOrderTop_eq_globalOrder q _ hmonomial]
    have hzero := finitePlaceOrder_gridMonomial_eq_zero
      K L q u v hu hv huOrder hvOrder (rs.1 : ℕ) (rs.2 : ℕ)
    rw [hzero]
    exact le_rfl
  have hepsilonMax : ∀ i, auxiliaryFamilyDerivativeOrder h k i ≤ n - 1 := by
    intro i
    exact auxiliaryFamilyDerivativeOrder_le_pred h k hn i
  have hkBound : k ≤ (n - 1) + 1 := by
    have hcancel : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [hcancel]
    exact auxiliaryFamily_k_le_card h k
  have hepsilonQ : (n - 1) + 1 ≤ n := by
    rw [Nat.sub_add_cancel hn]
  have hbound :=
    finiteExtensionFinitePlace_auxiliaryFamily_caseI_q_wronskian_bound_of_scaled_preserves
      (K := K) (L := L) (p := p) q h k
      (auxiliaryFamilyIndexEquiv h k)
      (auxiliaryFamilyDerivativeOrder h k) (fun _ => rfl)
      (n - 1) n D c hScaledIntegral u v hrho huTop hrhoLocal
      hgridRegular (auxiliaryFamilyDerivativeOrder_injective h k)
      hepsilonMax hkBound hepsilonQ
  rw [finiteExtensionFinitePlaceLocalOrder_eq_globalOrder,
    finiteExtensionFinitePlaceLocalOrderTop_eq_globalOrder q c hc,
    finiteExtensionFinitePlaceLocalOrderTop_eq_globalOrder q _ hW] at hbound
  have hboundInt :
      (n : ℤ) * finitePlaceOrder q ((1 - u) / (1 - v)) ≤
        (n.choose 2 : ℤ) * finitePlaceOrder q c +
          finitePlaceOrder q
            (indexedDedekindLocalWronskian D
              (auxiliaryFamilyDerivativeOrder h k)
              (auxiliaryFamily u v h k)).det := by
    exact_mod_cast hbound
  simpa only [n, finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder]
    using hboundInt

/-- Finite-place source case (ii), with every local order converted to the
coefficient used by the exhaustive principal divisor. -/
theorem finiteExtensionFinitePlace_canonicalAuxiliary_caseII
    (q : FiniteExtensionFinitePlace K L)
    (D : Derivation C L L) (c : L) (hc : c ≠ 0)
    (hScaledIntegral :
      ∀ r : FiniteExtensionFinitePlaceLocalRing K L q,
        ∃ s : FiniteExtensionFinitePlaceLocalRing K L q,
          (c • D) (finiteExtensionFinitePlaceLocalizationToField
              (K := K) (L := L) q r) =
            finiteExtensionFinitePlaceLocalizationToField
              (K := K) (L := L) q s)
    (h k : ℕ) (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huOrder : 0 ≤ finitePlaceOrder q u)
    (hvOrder : 0 ≤ finitePlaceOrder q v)
    (hrhoOrder : 0 ≤ finitePlaceOrder q ((1 - u) / (1 - v)))
    (hW : (indexedDedekindLocalWronskian D
      (auxiliaryFamilyDerivativeOrder h k)
      (auxiliaryFamily u v h k)).det ≠ 0) :
    0 ≤ ((h * k + h + k).choose 2 : ℤ) * finitePlaceOrder q c +
      finiteExtensionPrincipalDivisor K L
        (indexedDedekindLocalWronskian D
          (auxiliaryFamilyDerivativeOrder h k)
          (auxiliaryFamily u v h k)).det (.inl q) := by
  have hrho : (1 - u) / (1 - v) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hu1.symm) (sub_ne_zero.mpr hv1.symm)
  have huTop : (0 : WithTop ℤ) ≤
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q u := by
    rw [finiteExtensionFinitePlaceLocalOrderTop_eq_globalOrder q u hu]
    exact_mod_cast huOrder
  have hvTop : (0 : WithTop ℤ) ≤
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q v := by
    rw [finiteExtensionFinitePlaceLocalOrderTop_eq_globalOrder q v hv]
    exact_mod_cast hvOrder
  have hrhoTop : (0 : WithTop ℤ) ≤
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q
        ((1 - u) / (1 - v)) := by
    rw [finiteExtensionFinitePlaceLocalOrderTop_eq_globalOrder q _ hrho]
    exact_mod_cast hrhoOrder
  have hbound :=
    finiteExtensionFinitePlace_auxiliaryFamily_caseII_nonnegative_of_scaled_preserves
      (K := K) (L := L) q h k
      (auxiliaryFamilyIndexEquiv h k)
      (auxiliaryFamilyDerivativeOrder h k) (fun _ => rfl)
      D c hScaledIntegral u v huTop hvTop hrhoTop
  rw [finiteExtensionFinitePlaceLocalOrderTop_eq_globalOrder q c hc,
    finiteExtensionFinitePlaceLocalOrderTop_eq_globalOrder q _ hW] at hbound
  have hboundInt :
      0 ≤ ((h * k + h + k).choose 2 : ℤ) * finitePlaceOrder q c +
        finitePlaceOrder q
          (indexedDedekindLocalWronskian D
            (auxiliaryFamilyDerivativeOrder h k)
            (auxiliaryFamily u v h k)).det := by
    exact_mod_cast hbound
  simpa only [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder] using hboundInt

/-- Finite-place source case (iii), expressed directly with the global
principal divisor and the consecutive-order Wronskian. -/
theorem finiteExtensionFinitePlace_canonicalAuxiliary_caseIII
    (q : FiniteExtensionFinitePlace K L)
    (D : Derivation C L L) (c : L) (hc : c ≠ 0)
    (hScaledIntegral :
      ∀ r : FiniteExtensionFinitePlaceLocalRing K L q,
        ∃ s : FiniteExtensionFinitePlaceLocalRing K L q,
          (c • D) (finiteExtensionFinitePlaceLocalizationToField
              (K := K) (L := L) q r) =
            finiteExtensionFinitePlaceLocalizationToField
              (K := K) (L := L) q s)
    (h k : ℕ) (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hW : (indexedDedekindLocalWronskian D
      (auxiliaryFamilyDerivativeOrder h k)
      (auxiliaryFamily u v h k)).det ≠ 0) :
    ((k * (k - 1) / 2 : ℕ) : ℤ) *
          finiteExtensionPrincipalDivisor K L u (.inl q) +
        ((h * k : ℕ) : ℤ) *
          finiteExtensionPrincipalDivisor K L v (.inl q) +
        (k : ℤ) * finiteExtensionPrincipalDivisor K L
          ((1 - u) / (1 - v)) (.inl q) +
        finiteExtensionPrincipalDivisor K L
          (finiteExtensionAuxiliaryGridProduct L u v h k) (.inl q) -
        ((h * k + h + k).choose 2 : ℤ) ≤
      ((h * k + h + k).choose 2 : ℤ) * finitePlaceOrder q c +
        finiteExtensionPrincipalDivisor K L
          (indexedDedekindLocalWronskian D
            (auxiliaryFamilyDerivativeOrder h k)
            (auxiliaryFamily u v h k)).det (.inl q) := by
  have hbound :=
    finiteExtensionFinitePlace_auxiliaryFamily_caseIII_source_lower_bound_of_scaled_preserves
      (K := K) (L := L) q h k
      (auxiliaryFamilyIndexEquiv h k)
      (auxiliaryFamilyDerivativeOrder h k) (fun _ => rfl)
      D c hScaledIntegral u v hu hv hu1 hv1
  have hrho : (1 - u) / (1 - v) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hu1.symm) (sub_ne_zero.mpr hv1.symm)
  rw [finiteExtensionFinitePlaceLocalOrder_eq_globalOrder,
    finiteExtensionFinitePlaceLocalOrder_eq_globalOrder,
    finiteExtensionFinitePlaceLocalOrder_eq_globalOrder] at hbound
  simp_rw [finiteExtensionFinitePlaceLocalOrder_eq_globalOrder] at hbound
  rw [finiteExtensionFinitePlaceLocalOrderTop_eq_globalOrder q c hc,
    finiteExtensionFinitePlaceLocalOrderTop_eq_globalOrder q _ hW] at hbound
  have hboundInt :
      ((k * (k - 1) / 2 : ℕ) : ℤ) * finitePlaceOrder q u +
          ((h * k : ℕ) : ℤ) * finitePlaceOrder q v +
          (k : ℤ) * finitePlaceOrder q ((1 - u) / (1 - v)) +
          (∑ rs : Fin (k + 1) × Fin h,
            finitePlaceOrder q (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ))) -
          (∑ i : Sum (Fin k) (Fin (k + 1) × Fin h),
            (auxiliaryFamilyDerivativeOrder h k i : ℤ)) ≤
        ((h * k + h + k).choose 2 : ℤ) * finitePlaceOrder q c +
          finitePlaceOrder q
            (indexedDedekindLocalWronskian D
              (auxiliaryFamilyDerivativeOrder h k)
              (auxiliaryFamily u v h k)).det := by
    exact_mod_cast hbound
  rw [auxiliaryFamilyDerivativeOrder_sum_int,
    finiteExtensionFinitePlace_gridOrder_sum_eq K L q u v hu hv h k] at hboundInt
  simpa only [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder] using hboundInt

/-- Finite-place source case (iv), in the same global-divisor form. -/
theorem finiteExtensionFinitePlace_canonicalAuxiliary_caseIV
    (q : FiniteExtensionFinitePlace K L)
    (D : Derivation C L L) (c : L) (hc : c ≠ 0)
    (hScaledIntegral :
      ∀ r : FiniteExtensionFinitePlaceLocalRing K L q,
        ∃ s : FiniteExtensionFinitePlaceLocalRing K L q,
          (c • D) (finiteExtensionFinitePlaceLocalizationToField
              (K := K) (L := L) q r) =
            finiteExtensionFinitePlaceLocalizationToField
              (K := K) (L := L) q s)
    (h k : ℕ) (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hW : (indexedDedekindLocalWronskian D
      (auxiliaryFamilyDerivativeOrder h k)
      (auxiliaryFamily u v h k)).det ≠ 0) :
    ((k * (k - 1) / 2 : ℕ) : ℤ) *
          finiteExtensionPrincipalDivisor K L u (.inl q) +
        (k : ℤ) * finiteExtensionPrincipalDivisor K L
          ((1 - u) / (1 - v)) (.inl q) +
        finiteExtensionPrincipalDivisor K L
          (finiteExtensionAuxiliaryGridProduct L u v h k) (.inl q) -
        ((h * k + h + k).choose 2 : ℤ) ≤
      ((h * k + h + k).choose 2 : ℤ) * finitePlaceOrder q c +
        finiteExtensionPrincipalDivisor K L
          (indexedDedekindLocalWronskian D
            (auxiliaryFamilyDerivativeOrder h k)
            (auxiliaryFamily u v h k)).det (.inl q) := by
  have hbound :=
    finiteExtensionFinitePlace_auxiliaryFamily_caseIV_source_lower_bound_of_scaled_preserves
      (K := K) (L := L) q h k
      (auxiliaryFamilyIndexEquiv h k)
      (auxiliaryFamilyDerivativeOrder h k) (fun _ => rfl)
      D c hScaledIntegral u v hu hv hu1 hv1
  rw [finiteExtensionFinitePlaceLocalOrder_eq_globalOrder,
    finiteExtensionFinitePlaceLocalOrder_eq_globalOrder] at hbound
  simp_rw [finiteExtensionFinitePlaceLocalOrder_eq_globalOrder] at hbound
  rw [finiteExtensionFinitePlaceLocalOrderTop_eq_globalOrder q c hc,
    finiteExtensionFinitePlaceLocalOrderTop_eq_globalOrder q _ hW] at hbound
  have hboundInt :
      ((k * (k - 1) / 2 : ℕ) : ℤ) * finitePlaceOrder q u +
          (k : ℤ) * finitePlaceOrder q ((1 - u) / (1 - v)) +
          (∑ rs : Fin (k + 1) × Fin h,
            finitePlaceOrder q (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ))) -
          (∑ i : Sum (Fin k) (Fin (k + 1) × Fin h),
            (auxiliaryFamilyDerivativeOrder h k i : ℤ)) ≤
        ((h * k + h + k).choose 2 : ℤ) * finitePlaceOrder q c +
          finitePlaceOrder q
            (indexedDedekindLocalWronskian D
              (auxiliaryFamilyDerivativeOrder h k)
              (auxiliaryFamily u v h k)).det := by
    exact_mod_cast hbound
  rw [auxiliaryFamilyDerivativeOrder_sum_int,
    finiteExtensionFinitePlace_gridOrder_sum_eq K L q u v hu hv h k] at hboundInt
  simpa only [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder] using hboundInt

end

end BGS.CorvajaZannier
