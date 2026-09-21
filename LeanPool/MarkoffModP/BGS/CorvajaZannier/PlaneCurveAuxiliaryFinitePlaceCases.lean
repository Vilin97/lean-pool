/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryFinitePlace
import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindPerfectResidueCaseI
import LeanPool.MarkoffModP.BGS.CorvajaZannier.RatFuncExhaustiveProductFormula

/-!
# Cases I and II at actual finite extension places

This file supplies the regular-element lifting, finite/perfect residue-field
bridge, and scaled-derivation forms of the first two local
Corvaja--Zannier Wronskian estimates.
-/

open scoped nonZeroDivisors Polynomial BigOperators
open IsDedekindDomain

namespace BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) tempPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance tempPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L := .of_algebraMap_eq' rfl

local instance tempFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (FunctionField.ringOfIntegers K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance tempFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (FunctionField.ringOfIntegers K L) :=
  Module.IsNoetherian.finite K[X] (FunctionField.ringOfIntegers K L)

local instance tempPolynomialTorsionFreeTop : Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance tempFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (FunctionField.ringOfIntegers K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance tempFiniteIntegralClosureIsDedekindDomain :
    IsDedekindDomain (FunctionField.ringOfIntegers K L) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) L
    (FunctionField.ringOfIntegers K L)

variable {K L}

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
theorem finiteExtensionFinitePlace_exists_local_lift_of_orderTop_nonnegative
    (q : PlaneCurveExtensionFinitePlace K L) (x : L)
    (hx : (0 : WithTop ℤ) ≤
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q x) :
    ∃ x₀ : FiniteExtensionFinitePlaceLocalRing K L q,
      x = finiteExtensionFinitePlaceLocalizationToField
        (K := K) (L := L) q x₀ := by
  letI := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
  letI := finiteExtensionFinitePlaceLocalIsFractionRing (K := K) (L := L) q
  letI : IsDiscreteValuationRing
      (FiniteExtensionFinitePlaceLocalRing K L q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (FunctionField.ringOfIntegers K L) q.ne_bot
      (FiniteExtensionFinitePlaceLocalRing K L q)
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  have horder : 0 ≤ finitePlaceOrder
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionFinitePlaceLocalRing K L q)) x := by
    simpa only [finiteExtensionFinitePlaceLocalOrderTop,
      finitePlaceOrderTop_eq_coe _ _ hx0, WithTop.coe_nonneg] using hx
  have hval :
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionFinitePlaceLocalRing K L q)).valuation L x ≤ 1 := by
    rw [valuation_eq_exp_neg_finitePlaceOrder _ x hx0]
    simpa only [← WithZero.exp_zero] using
      (WithZero.exp_le_exp.mpr (by omega :
        -finitePlaceOrder
          (IsDiscreteValuationRing.maximalIdeal
            (FiniteExtensionFinitePlaceLocalRing K L q)) x ≤ 0))
  obtain ⟨x₀, hx₀⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hval
  exact ⟨x₀, hx₀.symm⟩

variable {C : Type*} [Field C] [Algebra C L]

omit [DecidableEq (RatFunc K)] in
theorem ratFuncFinitePlace_residueField_finite [Fintype K]
    (p : HeightOneSpectrum K[X]) :
    Finite p.asIdeal.ResidueField := by
  let r := finitePlaceNormalizedPrime p
  have hr0 : (r : K[X]) ≠ 0 := r.property.1.ne_zero
  have hrmonic : (r : K[X]).Monic :=
    (Polynomial.normalize_eq_self_iff_monic hr0).mp r.property.2
  have hp : p.asIdeal = Ideal.span ({(r : K[X])} : Set K[X]) := by
    calc
      p.asIdeal = (normalizedPrimeFinitePlace (K := K) r).asIdeal := by
        rw [normalizedPrimeFinitePlace_finitePlaceNormalizedPrime]
      _ = Ideal.span ({(r : K[X])} : Set K[X]) := rfl
  letI : Module.Finite K
      (HasQuotient.Quotient K[X] p.asIdeal) := by
    rw [hp]
    exact hrmonic.finite_quotient
  letI : Finite (HasQuotient.Quotient K[X] p.asIdeal) :=
    Module.finite_of_finite K
  infer_instance

omit [DecidableEq (RatFunc K)] in
theorem finiteExtensionFinitePlace_residueField_finite [Fintype K]
    (q : PlaneCurveExtensionFinitePlace K L) :
    Finite q.asIdeal.ResidueField := by
  let p := HeightOneSpectrum.under K[X] q
  letI : Finite p.asIdeal.ResidueField :=
    ratFuncFinitePlace_residueField_finite p
  letI : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  letI hLocalAlg :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  letI : Localization.AtPrime.IsLiesOverAlgebra p.asIdeal q.asIdeal := ⟨rfl⟩
  letI : Algebra.QuasiFiniteAt K[X] q.asIdeal := inferInstance
  letI : Module.Finite p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    inferInstance
  exact Module.finite_of_finite p.asIdeal.ResidueField

omit [DecidableEq (RatFunc K)] in
theorem finiteExtensionFinitePlaceLocal_residueField_perfect [Fintype K]
    (q : PlaneCurveExtensionFinitePlace K L) :
    letI : IsDiscreteValuationRing
      (FiniteExtensionFinitePlaceLocalRing K L q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (FunctionField.ringOfIntegers K L) q.ne_bot
      (FiniteExtensionFinitePlaceLocalRing K L q)
    PerfectField
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionFinitePlaceLocalRing K L q)).asIdeal.ResidueField := by
  letI : Finite q.asIdeal.ResidueField :=
    finiteExtensionFinitePlace_residueField_finite q
  letI : Finite (HasQuotient.Quotient
      (FunctionField.ringOfIntegers K L) q.asIdeal) :=
    Finite.of_injective
      (algebraMap
        (HasQuotient.Quotient (FunctionField.ringOfIntegers K L) q.asIdeal)
        q.asIdeal.ResidueField)
      q.asIdeal.injective_algebraMap_quotient_residueField
  letI : IsDiscreteValuationRing
      (FiniteExtensionFinitePlaceLocalRing K L q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (FunctionField.ringOfIntegers K L) q.ne_bot
      (FiniteExtensionFinitePlaceLocalRing K L q)
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal q.asIdeal
    (FiniteExtensionFinitePlaceLocalRing K L q)
  letI : Finite (HasQuotient.Quotient
      (FiniteExtensionFinitePlaceLocalRing K L q)
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionFinitePlaceLocalRing K L q)).asIdeal) :=
    Finite.of_injective e.symm e.symm.injective
  let Rq := HasQuotient.Quotient
    (FiniteExtensionFinitePlaceLocalRing K L q)
    (IsDiscreteValuationRing.maximalIdeal
      (FiniteExtensionFinitePlaceLocalRing K L q)).asIdeal
  letI : Finite
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionFinitePlaceLocalRing K L q)).asIdeal.ResidueField :=
    IsLocalization.finite Rq (nonZeroDivisors Rq)
  exact PerfectField.ofFinite

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
theorem finiteExtensionFinitePlace_auxiliaryFamily_caseII_nonnegative_of_preserves
    (q : PlaneCurveExtensionFinitePlace K L)
    (D : Derivation C L L)
    (hDIntegral : ∀ r : FiniteExtensionFinitePlaceLocalRing K L q,
      ∃ s : FiniteExtensionFinitePlaceLocalRing K L q,
        D (finiteExtensionFinitePlaceLocalizationToField
            (K := K) (L := L) q r) =
          finiteExtensionFinitePlaceLocalizationToField
            (K := K) (L := L) q s)
    (h k : ℕ) (epsilon : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v : L)
    (hu : (0 : WithTop ℤ) ≤
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q u)
    (hv : (0 : WithTop ℤ) ≤
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q v)
    (hrho : (0 : WithTop ℤ) ≤
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q
        ((1 - u) / (1 - v))) :
    (0 : WithTop ℤ) ≤
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q
        (indexedDedekindLocalWronskian D epsilon
          (auxiliaryFamily u v h k)).det := by
  letI := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
  letI := finiteExtensionFinitePlaceLocalIsFractionRing (K := K) (L := L) q
  letI : IsDiscreteValuationRing
      (FiniteExtensionFinitePlaceLocalRing K L q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (FunctionField.ringOfIntegers K L) q.ne_bot
      (FiniteExtensionFinitePlaceLocalRing K L q)
  apply finitePlaceOrderTop_auxiliaryFamily_caseII_nonnegative_of_integral
    (IsDiscreteValuationRing.maximalIdeal
      (FiniteExtensionFinitePlaceLocalRing K L q)) D hDIntegral h k epsilon u v
  · obtain ⟨u₀, hu₀⟩ :=
      finiteExtensionFinitePlace_exists_local_lift_of_orderTop_nonnegative q u hu
    exact ⟨u₀, hu₀⟩
  · obtain ⟨v₀, hv₀⟩ :=
      finiteExtensionFinitePlace_exists_local_lift_of_orderTop_nonnegative q v hv
    exact ⟨v₀, hv₀⟩
  · obtain ⟨rho₀, hrho₀⟩ :=
      finiteExtensionFinitePlace_exists_local_lift_of_orderTop_nonnegative
        q ((1 - u) / (1 - v)) hrho
    exact ⟨rho₀, hrho₀⟩

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
theorem finiteExtensionFinitePlace_auxiliaryFamily_caseII_nonnegative_of_scaled_preserves
    (q : PlaneCurveExtensionFinitePlace K L)
    (h k : ℕ) {n : ℕ}
    (e : Sum (Fin k) (Fin (k + 1) × Fin h) ≃ Fin n)
    (epsilon : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (hepsilon : ∀ i, epsilon i = (e i : ℕ))
    (D : Derivation C L L) (c : L)
    (hScaledIntegral :
      ∀ r : FiniteExtensionFinitePlaceLocalRing K L q,
        ∃ s : FiniteExtensionFinitePlaceLocalRing K L q,
          (c • D) (finiteExtensionFinitePlaceLocalizationToField
              (K := K) (L := L) q r) =
            finiteExtensionFinitePlaceLocalizationToField
              (K := K) (L := L) q s)
    (u v : L)
    (hu : (0 : WithTop ℤ) ≤
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q u)
    (hv : (0 : WithTop ℤ) ≤
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q v)
    (hrho : (0 : WithTop ℤ) ≤
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q
        ((1 - u) / (1 - v))) :
    (0 : WithTop ℤ) ≤
      n.choose 2 •
          finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q c +
        finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q
          (indexedDedekindLocalWronskian D epsilon
            (auxiliaryFamily u v h k)).det := by
  have hbound :=
    finiteExtensionFinitePlace_auxiliaryFamily_caseII_nonnegative_of_preserves
      q (c • D) hScaledIntegral h k epsilon u v hu hv hrho
  have hchange := indexedDedekindLocalWronskian_det_changeParameter
    e epsilon hepsilon (c • D) D c rfl (auxiliaryFamily u v h k)
  rw [hchange, finiteExtensionFinitePlaceLocalOrderTop_mul,
    finiteExtensionFinitePlaceLocalOrderTop_pow] at hbound
  exact hbound

variable {p : ℕ} [Fact p.Prime] [CharP L p]

omit [DecidableEq (RatFunc K)] in
theorem finiteExtensionFinitePlace_auxiliaryFamily_caseI_q_wronskian_bound_of_scaled_preserves
    [Fintype K]
    (q : PlaneCurveExtensionFinitePlace K L)
    (h k : ℕ) {n : ℕ}
    (e : Sum (Fin k) (Fin (k + 1) × Fin h) ≃ Fin n)
    (epsilonOrder : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (hepsilon : ∀ i, epsilonOrder i = (e i : ℕ))
    (epsilon qBound : ℕ)
    (D : Derivation (frobeniusSubfield L p) L L) (c : L)
    (hScaledIntegral :
      ∀ r : FiniteExtensionFinitePlaceLocalRing K L q,
        ∃ s : FiniteExtensionFinitePlaceLocalRing K L q,
          (c • D) (finiteExtensionFinitePlaceLocalizationToField
              (K := K) (L := L) q r) =
            finiteExtensionFinitePlaceLocalizationToField
              (K := K) (L := L) q s)
    (u v : L)
    (hrhoNe : (1 - u) / (1 - v) ≠ 0)
    (huOrder :
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q u = 0)
    (hrhoOrder :
      finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
        ((1 - u) / (1 - v)) < 0)
    (hgridRegular : ∀ rs : Fin (k + 1) × Fin h,
      (0 : WithTop ℤ) ≤
        finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q
          (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)))
    (hepsilonInjective : Function.Injective epsilonOrder)
    (hepsilonMax : ∀ i, epsilonOrder i ≤ epsilon)
    (hk : k ≤ epsilon + 1) (hepsilonQ : epsilon + 1 ≤ qBound) :
    (((qBound : ℤ) *
        finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
          ((1 - u) / (1 - v)) : ℤ) : WithTop ℤ) ≤
      n.choose 2 •
          finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q c +
        finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q
          (indexedDedekindLocalWronskian D epsilonOrder
            (auxiliaryFamily u v h k)).det := by
  letI := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
  letI := finiteExtensionFinitePlaceLocalIsFractionRing (K := K) (L := L) q
  letI : IsDiscreteValuationRing
      (FiniteExtensionFinitePlaceLocalRing K L q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (FunctionField.ringOfIntegers K L) q.ne_bot
      (FiniteExtensionFinitePlaceLocalRing K L q)
  letI : CharP (FiniteExtensionFinitePlaceLocalRing K L q) p := ⟨by
    intro n
    rw [← map_eq_zero_iff
      (finiteExtensionFinitePlaceLocalizationToField
        (K := K) (L := L) q)
      (by
        change Function.Injective
          (algebraMap (FiniteExtensionFinitePlaceLocalRing K L q) L)
        exact IsFractionRing.injective
          (FiniteExtensionFinitePlaceLocalRing K L q) L),
      map_natCast, CharP.cast_eq_zero_iff L p]⟩
  letI : PerfectField
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionFinitePlaceLocalRing K L q)).asIdeal.ResidueField :=
    finiteExtensionFinitePlaceLocal_residueField_perfect q
  obtain ⟨A, hAdet, hdet, hbound⟩ :=
    exists_frobeniusSubfield_dedekindAuxiliaryFamily_caseI_q_wronskian_bound_of_perfect_residue
      (p := p)
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionFinitePlaceLocalRing K L q))
      (c • D) hScaledIntegral u v h k epsilonOrder epsilon qBound
      hrhoNe huOrder hrhoOrder hgridRegular hepsilonInjective
      hepsilonMax hk hepsilonQ
  have hchange := indexedDedekindLocalWronskian_det_changeParameter
    e epsilonOrder hepsilon (c • D) D c rfl (auxiliaryFamily u v h k)
  rw [hchange, finitePlaceOrderTop_mul, finitePlaceOrderTop_pow] at hbound
  change (((qBound : ℤ) *
      finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
        ((1 - u) / (1 - v)) : ℤ) : WithTop ℤ) ≤
    n.choose 2 •
        finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q c +
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q
        (indexedDedekindLocalWronskian D epsilonOrder
          (auxiliaryFamily u v h k)).det at hbound
  exact hbound

end

end BGS.CorvajaZannier
