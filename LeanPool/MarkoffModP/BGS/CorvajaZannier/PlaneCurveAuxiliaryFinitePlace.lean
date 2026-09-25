/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindAuxiliaryLocalCases
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLocalDerivationExtension
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLocalizationOrder
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveLocalReciprocalDiscriminant
public import Mathlib.NumberTheory.FunctionField

/-!
# Auxiliary Wronskian bounds at finite plane-curve places

This file connects the uniformizer-free local Corvaja--Zannier estimates to
the actual finite primes of the integral closure in a finite extension of
`K(X)`.  The constants used for the local derivation-extension step are the
ground field `K`; the Wronskian derivation may subsequently be obtained by
restricting scalars from the Frobenius constant field.  Thus no algebra map
from the Frobenius constant field to a nontrivial DVR is required.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial BigOperators
open IsDedekindDomain

namespace BGS.CorvajaZannier

noncomputable section

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

/-! ## The unramified local-preservation bridge -/

/-- Outside the different, the ambient derivation preserves the selected
extension DVR.  This is the existential-preservation form consumed by the
uniformizer-free Wronskian estimates.  In the plane-curve application `C` is
the ground field `K` (after restricting scalars from `L^p`), so all local
algebra structures here are genuine; no map `L^p → B_Q` is requested. -/
theorem dedekindLocal_ambientDerivation_preserves_of_not_dvd_different
    {A B C U : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing U]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (p : Ideal A) (Q : Ideal B) [p.IsPrime] [Q.IsPrime] [Q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime Q)]
    [IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime Q)]
    [Algebra C (Localization.AtPrime p)]
    [Algebra C (Localization.AtPrime Q)]
    [Algebra C U]
    [Algebra (Localization.AtPrime p) U]
    [Algebra (Localization.AtPrime Q) U]
    [IsScalarTower C (Localization.AtPrime p) (Localization.AtPrime Q)]
    [IsScalarTower C (Localization.AtPrime p) U]
    [IsScalarTower C (Localization.AtPrime Q) U]
    [IsScalarTower (Localization.AtPrime p) (Localization.AtPrime Q) U]
    (hQ : ¬ Q ∣ differentIdeal A B)
    (D : Derivation C (Localization.AtPrime p) (Localization.AtPrime p))
    (E : Derivation C U U)
    (hE : ∀ s : Localization.AtPrime p,
      E (algebraMap (Localization.AtPrime p) U s) =
        algebraMap (Localization.AtPrime p) U (D s)) :
    ∀ t : Localization.AtPrime Q, ∃ t' : Localization.AtPrime Q,
      E (algebraMap (Localization.AtPrime Q) U t) =
        algebraMap (Localization.AtPrime Q) U t' := by
  obtain ⟨D', _hD', hpres⟩ :=
    dedekindLocal_derivation_preserves_of_not_dvd_different
      p Q hQ D E hE
  intro t
  exact ⟨D' t, hpres t⟩

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) auxiliaryFinitePlacePolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance auxiliaryFinitePlacePolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  .of_algebraMap_eq' rfl

local instance auxiliaryFinitePlaceFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (FunctionField.ringOfIntegers K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance auxiliaryFinitePlaceFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (FunctionField.ringOfIntegers K L) :=
  Module.IsNoetherian.finite K[X] (FunctionField.ringOfIntegers K L)

local instance auxiliaryFinitePlacePolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance auxiliaryFinitePlaceFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (FunctionField.ringOfIntegers K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance auxiliaryFinitePlaceFiniteIntegralClosureIsDedekindDomain :
    IsDedekindDomain (FunctionField.ringOfIntegers K L) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) L
    (FunctionField.ringOfIntegers K L)

/-- The actual finite places of `L / K(X)`, before adjoining the places over
infinity.  This is definitionally the finite summand used by the exhaustive
place infrastructure. -/
abbrev PlaneCurveExtensionFinitePlace :=
  HeightOneSpectrum (FunctionField.ringOfIntegers K L)

abbrev FiniteExtensionFinitePlaceBaseLocalRing
    (q : PlaneCurveExtensionFinitePlace K L) :=
  Localization.AtPrime (HeightOneSpectrum.under K[X] q).asIdeal

abbrev FiniteExtensionFinitePlaceLocalRing
    (q : PlaneCurveExtensionFinitePlace K L) :=
  Localization.AtPrime q.asIdeal

section LocalOrder

variable {K L}

/-- Canonical inclusion of the localization at an actual finite extension
place into the ambient function field. -/
noncomputable def finiteExtensionFinitePlaceLocalizationToField
    (q : PlaneCurveExtensionFinitePlace K L) :
    FiniteExtensionFinitePlaceLocalRing K L q →+* L :=
  IsLocalization.lift
    (S := FiniteExtensionFinitePlaceLocalRing K L q)
    (M := q.asIdeal.primeCompl)
    (g := algebraMap (FunctionField.ringOfIntegers K L) L) fun y =>
      IsLocalization.map_units L
        ⟨y.1, q.asIdeal.primeCompl_le_nonZeroDivisors y.2⟩

omit [DecidableEq K] [DecidableEq (RatFunc K)]
  [Algebra.IsSeparable (RatFunc K) L] in
@[simp] theorem finiteExtensionFinitePlaceLocalizationToField_comp_algebraMap
    (q : PlaneCurveExtensionFinitePlace K L) :
    (finiteExtensionFinitePlaceLocalizationToField (K := K) (L := L) q).comp
        (algebraMap (FunctionField.ringOfIntegers K L)
          (FiniteExtensionFinitePlaceLocalRing K L q)) =
      algebraMap (FunctionField.ringOfIntegers K L) L := by
  exact IsLocalization.lift_comp _

/-- The canonical algebra structure on the ambient function field from the
localized finite-place DVR. -/
@[reducible] noncomputable def finiteExtensionFinitePlaceLocalAlgebra
    (q : PlaneCurveExtensionFinitePlace K L) :
    Algebra (FiniteExtensionFinitePlaceLocalRing K L q) L :=
  (finiteExtensionFinitePlaceLocalizationToField (K := K) (L := L) q).toAlgebra

omit [DecidableEq K] [DecidableEq (RatFunc K)]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- The ambient function field is the fraction field of every finite-place
localization. -/
theorem finiteExtensionFinitePlaceLocalIsFractionRing
    (q : PlaneCurveExtensionFinitePlace K L) :
    letI := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
    IsFractionRing (FiniteExtensionFinitePlaceLocalRing K L q) L := by
  let := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
  let : IsScalarTower (FunctionField.ringOfIntegers K L)
      (FiniteExtensionFinitePlaceLocalRing K L q) L := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (finiteExtensionFinitePlaceLocalizationToField_comp_algebraMap
      (K := K) (L := L) q).symm
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    q.asIdeal.primeCompl (FiniteExtensionFinitePlaceLocalRing K L q) L

/-- The normalized order on the localization at an actual finite place of
`L / K(X)`.  Keeping this definition attached to `q` avoids introducing a
spurious algebra structure from the Frobenius constant field to the DVR. -/
noncomputable def finiteExtensionFinitePlaceLocalOrderTop
    (q : PlaneCurveExtensionFinitePlace K L)
    (x : L) : WithTop ℤ := by
  letI := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
  letI := finiteExtensionFinitePlaceLocalIsFractionRing (K := K) (L := L) q
  letI : IsDiscreteValuationRing
      (FiniteExtensionFinitePlaceLocalRing K L q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (FunctionField.ringOfIntegers K L) q.ne_bot
      (FiniteExtensionFinitePlaceLocalRing K L q)
  exact finitePlaceOrderTop
    (IsDiscreteValuationRing.maximalIdeal
      (FiniteExtensionFinitePlaceLocalRing K L q)) x

/-- Integer-valued form of the localized order. -/
noncomputable def finiteExtensionFinitePlaceLocalOrder
    (q : PlaneCurveExtensionFinitePlace K L)
    (x : L) : ℤ := by
  letI := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
  letI := finiteExtensionFinitePlaceLocalIsFractionRing (K := K) (L := L) q
  letI : IsDiscreteValuationRing
      (FiniteExtensionFinitePlaceLocalRing K L q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (FunctionField.ringOfIntegers K L) q.ne_bot
      (FiniteExtensionFinitePlaceLocalRing K L q)
  exact finitePlaceOrder
    (IsDiscreteValuationRing.maximalIdeal
      (FiniteExtensionFinitePlaceLocalRing K L q)) x

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- The order used by the actual localized DVR bound is exactly the global
height-one order of the same finite place. -/
theorem finiteExtensionFinitePlaceLocalOrder_eq_globalOrder
    (q : PlaneCurveExtensionFinitePlace K L) (x : L) :
    finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q x =
      finitePlaceOrder q x := by
  let := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
  let := finiteExtensionFinitePlaceLocalIsFractionRing (K := K) (L := L) q
  let : IsDiscreteValuationRing
      (FiniteExtensionFinitePlaceLocalRing K L q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (FunctionField.ringOfIntegers K L) q.ne_bot
      (FiniteExtensionFinitePlaceLocalRing K L q)
  let : IsScalarTower (FunctionField.ringOfIntegers K L)
      (FiniteExtensionFinitePlaceLocalRing K L q) L := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (finiteExtensionFinitePlaceLocalizationToField_comp_algebraMap
      (K := K) (L := L) q).symm
  change finitePlaceOrder
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionFinitePlaceLocalRing K L q)) x = _
  exact localizationAtPrime_finitePlaceOrder_eq q x

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- Nonzero localized `WithTop` orders are the corresponding global
height-one orders. -/
theorem finiteExtensionFinitePlaceLocalOrderTop_eq_globalOrder
    (q : PlaneCurveExtensionFinitePlace K L) (x : L) (hx : x ≠ 0) :
    finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q x =
      (finitePlaceOrder q x : WithTop ℤ) := by
  let := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
  let := finiteExtensionFinitePlaceLocalIsFractionRing (K := K) (L := L) q
  let : IsDiscreteValuationRing
      (FiniteExtensionFinitePlaceLocalRing K L q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (FunctionField.ringOfIntegers K L) q.ne_bot
      (FiniteExtensionFinitePlaceLocalRing K L q)
  simp only [finiteExtensionFinitePlaceLocalOrderTop]
  rw [finitePlaceOrderTop_eq_coe _ _ hx]
  exact_mod_cast
    finiteExtensionFinitePlaceLocalOrder_eq_globalOrder
      (K := K) (L := L) q x

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
@[simp] theorem finiteExtensionFinitePlaceLocalOrderTop_mul
    (q : PlaneCurveExtensionFinitePlace K L) (x y : L) :
    finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q (x * y) =
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q x +
        finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q y := by
  simp only [finiteExtensionFinitePlaceLocalOrderTop,
    finitePlaceOrderTop_mul]

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
@[simp] theorem finiteExtensionFinitePlaceLocalOrderTop_pow
    (q : PlaneCurveExtensionFinitePlace K L) (x : L) (n : ℕ) :
    finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q (x ^ n) =
      n • finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q x := by
  simp only [finiteExtensionFinitePlaceLocalOrderTop,
    finitePlaceOrderTop_pow]

variable {C : Type*} [Field C] [Algebra C L]

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- Source case (iii), now indexed by an actual finite place of the integral
closure.  The sole local hypothesis says that the derivation preserves the
localized DVR; it does not ask for an algebra map `C → R_q`. -/
theorem finiteExtensionFinitePlace_auxiliaryFamily_caseIII_source_lower_bound_of_preserves
    (q : PlaneCurveExtensionFinitePlace K L)
    (D : Derivation C L L)
    (hDIntegral : ∀ r : FiniteExtensionFinitePlaceLocalRing K L q,
      ∃ s : FiniteExtensionFinitePlaceLocalRing K L q,
        D (finiteExtensionFinitePlaceLocalizationToField
            (K := K) (L := L) q r) =
          finiteExtensionFinitePlaceLocalizationToField
            (K := K) (L := L) q s)
    (h k : ℕ) (epsilon : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    (((k * (k - 1) / 2 : ℕ) •
          finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q u +
        (h * k) • finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q v +
        k • finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
          ((1 - u) / (1 - v)) +
        ∑ rs : Fin (k + 1) × Fin h,
          finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
            (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) -
        ∑ i, (epsilon i : ℤ) : ℤ) : WithTop ℤ) ≤
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q
        (indexedDedekindLocalWronskian D epsilon
          (auxiliaryFamily u v h k)).det := by
  let := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
  let := finiteExtensionFinitePlaceLocalIsFractionRing (K := K) (L := L) q
  let : IsDiscreteValuationRing
      (FiniteExtensionFinitePlaceLocalRing K L q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (FunctionField.ringOfIntegers K L) q.ne_bot
      (FiniteExtensionFinitePlaceLocalRing K L q)
  have hDIntegral' : ∀ r : FiniteExtensionFinitePlaceLocalRing K L q,
      ∃ s : FiniteExtensionFinitePlaceLocalRing K L q,
        D (algebraMap (FiniteExtensionFinitePlaceLocalRing K L q) L r) =
          algebraMap (FiniteExtensionFinitePlaceLocalRing K L q) L s := by
    intro r
    obtain ⟨s, hs⟩ := hDIntegral r
    exact ⟨s, hs⟩
  exact finitePlaceOrderTop_auxiliaryFamily_caseIII_source_lower_bound_of_preserves
    (IsDiscreteValuationRing.maximalIdeal
      (FiniteExtensionFinitePlaceLocalRing K L q))
    D hDIntegral' h k epsilon u v hu hv hu1 hv1

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- Source case (iv), indexed by an actual finite place of the integral
closure and requiring only preservation of its localized DVR. -/
theorem finiteExtensionFinitePlace_auxiliaryFamily_caseIV_source_lower_bound_of_preserves
    (q : PlaneCurveExtensionFinitePlace K L)
    (D : Derivation C L L)
    (hDIntegral : ∀ r : FiniteExtensionFinitePlaceLocalRing K L q,
      ∃ s : FiniteExtensionFinitePlaceLocalRing K L q,
        D (finiteExtensionFinitePlaceLocalizationToField
            (K := K) (L := L) q r) =
          finiteExtensionFinitePlaceLocalizationToField
            (K := K) (L := L) q s)
    (h k : ℕ) (epsilon : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    (((k * (k - 1) / 2 : ℕ) •
          finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q u +
        k • finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
          ((1 - u) / (1 - v)) +
        ∑ rs : Fin (k + 1) × Fin h,
          finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
            (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) -
        ∑ i, (epsilon i : ℤ) : ℤ) : WithTop ℤ) ≤
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q
        (indexedDedekindLocalWronskian D epsilon
          (auxiliaryFamily u v h k)).det := by
  let := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
  let := finiteExtensionFinitePlaceLocalIsFractionRing (K := K) (L := L) q
  let : IsDiscreteValuationRing
      (FiniteExtensionFinitePlaceLocalRing K L q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (FunctionField.ringOfIntegers K L) q.ne_bot
      (FiniteExtensionFinitePlaceLocalRing K L q)
  have hDIntegral' : ∀ r : FiniteExtensionFinitePlaceLocalRing K L q,
      ∃ s : FiniteExtensionFinitePlaceLocalRing K L q,
        D (algebraMap (FiniteExtensionFinitePlaceLocalRing K L q) L r) =
          algebraMap (FiniteExtensionFinitePlaceLocalRing K L q) L s := by
    intro r
    obtain ⟨s, hs⟩ := hDIntegral r
    exact ⟨s, hs⟩
  exact finitePlaceOrderTop_auxiliaryFamily_caseIV_source_lower_bound_of_preserves
    (IsDiscreteValuationRing.maximalIdeal
      (FiniteExtensionFinitePlaceLocalRing K L q))
    D hDIntegral' h k epsilon u v hu hv hu1 hv1

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- Source case (iii) for a global derivation after multiplying it by the
local correction factor `c`.  The displayed right side has been transported
back to the original global Wronskian and records the exact triangular
correction `choose(n,2) * ord_q(c)`. -/
theorem finiteExtensionFinitePlace_auxiliaryFamily_caseIII_source_lower_bound_of_scaled_preserves
    (q : PlaneCurveExtensionFinitePlace K L)
    (h k : ℕ)
    {n : ℕ} (e : Sum (Fin k) (Fin (k + 1) × Fin h) ≃ Fin n)
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
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    (((k * (k - 1) / 2 : ℕ) •
          finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q u +
        (h * k) • finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q v +
        k • finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
          ((1 - u) / (1 - v)) +
        ∑ rs : Fin (k + 1) × Fin h,
          finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
            (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) -
        ∑ i, (epsilon i : ℤ) : ℤ) : WithTop ℤ) ≤
      n.choose 2 •
          finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q c +
        finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q
          (indexedDedekindLocalWronskian D epsilon
            (auxiliaryFamily u v h k)).det := by
  have hbound :=
    finiteExtensionFinitePlace_auxiliaryFamily_caseIII_source_lower_bound_of_preserves
      (K := K) (L := L) q (c • D) hScaledIntegral
      h k epsilon u v hu hv hu1 hv1
  have hchange := indexedDedekindLocalWronskian_det_changeParameter
    e epsilon hepsilon (c • D) D c rfl (auxiliaryFamily u v h k)
  rw [hchange, finiteExtensionFinitePlaceLocalOrderTop_mul,
    finiteExtensionFinitePlaceLocalOrderTop_pow] at hbound
  exact hbound

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- Source case (iv) with the same exact local correction term. -/
theorem finiteExtensionFinitePlace_auxiliaryFamily_caseIV_source_lower_bound_of_scaled_preserves
    (q : PlaneCurveExtensionFinitePlace K L)
    (h k : ℕ)
    {n : ℕ} (e : Sum (Fin k) (Fin (k + 1) × Fin h) ≃ Fin n)
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
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    (((k * (k - 1) / 2 : ℕ) •
          finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q u +
        k • finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
          ((1 - u) / (1 - v)) +
        ∑ rs : Fin (k + 1) × Fin h,
          finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
            (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) -
        ∑ i, (epsilon i : ℤ) : ℤ) : WithTop ℤ) ≤
      n.choose 2 •
          finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q c +
        finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q
          (indexedDedekindLocalWronskian D epsilon
            (auxiliaryFamily u v h k)).det := by
  have hbound :=
    finiteExtensionFinitePlace_auxiliaryFamily_caseIV_source_lower_bound_of_preserves
      (K := K) (L := L) q (c • D) hScaledIntegral
      h k epsilon u v hu hv hu1 hv1
  have hchange := indexedDedekindLocalWronskian_det_changeParameter
    e epsilon hepsilon (c • D) D c rfl (auxiliaryFamily u v h k)
  rw [hchange, finiteExtensionFinitePlaceLocalOrderTop_mul,
    finiteExtensionFinitePlaceLocalOrderTop_pow] at hbound
  exact hbound

section RestrictConstants

variable [Algebra K C] [Algebra K L] [IsScalarTower K C L]

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- Case (iii) for a derivation over a larger constant field (in the
application, `C = L^p`).  The proof restricts scalars to `K` before invoking
the local DVR theorem, while the displayed Wronskian is still the original
`C`-derivation Wronskian because restriction does not change its function. -/
theorem finiteExtensionFinitePlace_auxiliaryFamily_caseIII_source_lower_bound_of_restrictScalars_preserves
    (q : PlaneCurveExtensionFinitePlace K L)
    (D : Derivation C L L)
    (hDIntegral : ∀ r : FiniteExtensionFinitePlaceLocalRing K L q,
      ∃ s : FiniteExtensionFinitePlaceLocalRing K L q,
        D (finiteExtensionFinitePlaceLocalizationToField
            (K := K) (L := L) q r) =
          finiteExtensionFinitePlaceLocalizationToField
            (K := K) (L := L) q s)
    (h k : ℕ) (epsilon : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    (((k * (k - 1) / 2 : ℕ) •
          finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q u +
        (h * k) • finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q v +
        k • finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
          ((1 - u) / (1 - v)) +
        ∑ rs : Fin (k + 1) × Fin h,
          finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
            (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) -
        ∑ i, (epsilon i : ℤ) : ℤ) : WithTop ℤ) ≤
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q
          (indexedDedekindLocalWronskian D epsilon
          (auxiliaryFamily u v h k)).det := by
  have hbound :=
    finiteExtensionFinitePlace_auxiliaryFamily_caseIII_source_lower_bound_of_preserves
      (K := K) (L := L) q (D.restrictScalars K) hDIntegral
      h k epsilon u v hu hv hu1 hv1
  have hmatrix :
      indexedDedekindLocalWronskian (D.restrictScalars K) epsilon
          (auxiliaryFamily u v h k) =
        indexedDedekindLocalWronskian D epsilon
          (auxiliaryFamily u v h k) := by
    ext i j
    rfl
  rw [hmatrix] at hbound
  exact hbound

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- Case (iv) after the same honest restriction of constants from `C` to
the ground field `K`. -/
theorem finiteExtensionFinitePlace_auxiliaryFamily_caseIV_source_lower_bound_of_restrictScalars_preserves
    (q : PlaneCurveExtensionFinitePlace K L)
    (D : Derivation C L L)
    (hDIntegral : ∀ r : FiniteExtensionFinitePlaceLocalRing K L q,
      ∃ s : FiniteExtensionFinitePlaceLocalRing K L q,
        D (finiteExtensionFinitePlaceLocalizationToField
            (K := K) (L := L) q r) =
          finiteExtensionFinitePlaceLocalizationToField
            (K := K) (L := L) q s)
    (h k : ℕ) (epsilon : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    (((k * (k - 1) / 2 : ℕ) •
          finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q u +
        k • finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
          ((1 - u) / (1 - v)) +
        ∑ rs : Fin (k + 1) × Fin h,
          finiteExtensionFinitePlaceLocalOrder (K := K) (L := L) q
            (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) -
        ∑ i, (epsilon i : ℤ) : ℤ) : WithTop ℤ) ≤
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q
          (indexedDedekindLocalWronskian D epsilon
          (auxiliaryFamily u v h k)).det := by
  have hbound :=
    finiteExtensionFinitePlace_auxiliaryFamily_caseIV_source_lower_bound_of_preserves
      (K := K) (L := L) q (D.restrictScalars K) hDIntegral
      h k epsilon u v hu hv hu1 hv1
  have hmatrix :
      indexedDedekindLocalWronskian (D.restrictScalars K) epsilon
          (auxiliaryFamily u v h k) =
        indexedDedekindLocalWronskian D epsilon
          (auxiliaryFamily u v h k) := by
    ext i j
    rfl
  rw [hmatrix] at hbound
  exact hbound

end RestrictConstants

end LocalOrder

/-! ## Plane-curve reciprocal normalization at a selected extension place -/

section PlaneCurve

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- The reciprocal minimal-polynomial normalization, with the base prime
selected as the prime lying below an actual finite place of the plane-curve
function field.  This is the local primitive-element/different certificate
paired with the Wronskian estimates above. -/
theorem planeCurve_minpoly_reciprocal_local_normalization_at_finiteExtensionPlace
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hcardK : MvPolynomial.degreeOf 1 f < Fintype.card K) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    ∀ q : PlaneCurveExtensionFinitePlace K (PlaneCurveFunctionField f),
      let p := HeightOneSpectrum.under K[X] q
      let A := Localization.AtPrime p.asIdeal
      let ι := localizationAtPrimeToRatFunc p
      ∃ (a : Polynomial K) (u : Aˣ),
        let c := algebraMap (Polynomial K) A a
        let G := (planeCurvePolynomialInSecondCoordinate f).map
          (algebraMap (Polynomial K) A)
        minpoly (RatFunc K)
            ((planeCurveFunction f 1 -
              algebraMap (RatFunc K) (PlaneCurveFunctionField f) (ι c))⁻¹) =
          (unitNormalizedReciprocalTranslate G c u).map ι := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  exact fun q =>
    planeCurve_minpoly_reciprocal_local_normalization_of_degreeOf_second_lt_fintypeCard
      hf hpartialSecond hcardK (HeightOneSpectrum.under K[X] q)

end PlaneCurve

end

end BGS.CorvajaZannier
