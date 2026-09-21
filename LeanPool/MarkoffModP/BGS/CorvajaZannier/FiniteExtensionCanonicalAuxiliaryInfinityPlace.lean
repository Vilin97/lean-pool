/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.AuxiliaryFamilyIndexing
import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindCanonicalDifferentScaling
import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLocalizationDerivationPreservation
import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindAuxiliaryLocalCases
import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindPerfectResidueCaseI
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalDifferentDivisor
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionExceptionalSupport
import LeanPool.MarkoffModP.BGS.CorvajaZannier.TorsionExhaustiveGcdDivisorBound
import Mathlib.Tactic

/-!
# Canonical auxiliary bounds at infinity places

This module transports the four local Corvaja--Zannier auxiliary-family cases to
branches above the infinity place of a finite separable extension of `RatFunc K`.
The scaling supplied by the canonical different identifies its local order with
the coefficient of `finiteExtensionCanonicalDifferentDivisor` at `.inr P`.
-/

namespace BGS.CorvajaZannier

noncomputable section


open scoped nonZeroDivisors Polynomial BigOperators
open IsDedekindDomain

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance infinityAuxiliaryBaseConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

local instance infinityAuxiliaryBaseConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K) (RatFunc K) :=
  .of_algebraMap_eq' rfl

local instance infinityAuxiliaryIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance infinityAuxiliaryIntegralClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance infinityAuxiliaryBaseTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance infinityAuxiliaryIntegralClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance infinityAuxiliaryIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance infinityAuxiliaryIntegralClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance infinityAuxiliaryIntegralClosureConstantAlgebra :
    Algebra K (RatFuncInfinityIntegralClosure K L) :=
  RingHom.toAlgebra
    ((algebraMap (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L)).comp
      (algebraMap K (RatFuncInfinityIntegers K)))

local instance infinityAuxiliaryIntegralClosureConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  .of_algebraMap_eq' rfl

local instance infinityAuxiliaryBaseFaithfulSmulFractionRing :
    FaithfulSMul (RatFuncInfinityIntegers K)
      (FractionRing (RatFuncInfinityIntegralClosure K L)) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  have hT := IsFractionRing.injective (RatFuncInfinityIntegralClosure K L)
    (FractionRing (RatFuncInfinityIntegralClosure K L)) hxy
  have hL := congrArg Subtype.val hT
  apply Subtype.ext
  apply (algebraMap (RatFunc K) L).injective
  exact hL

local instance infinityAuxiliaryFractionRingAlgebra :
    Algebra (FractionRing (RatFuncInfinityIntegers K))
      (FractionRing (RatFuncInfinityIntegralClosure K L)) :=
  FractionRing.liftAlgebra (RatFuncInfinityIntegers K)
    (FractionRing (RatFuncInfinityIntegralClosure K L))

local instance infinityAuxiliaryFractionRingSeparable :
    Algebra.IsSeparable (FractionRing (RatFuncInfinityIntegers K))
      (FractionRing (RatFuncInfinityIntegralClosure K L)) := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (ratFuncInfinityFractionRingEquiv K).symm.toRingEquiv
    (FractionRing.algEquiv (RatFuncInfinityIntegralClosure K L) L).symm.toRingEquiv ?_
  ext z
  exact IsFractionRing.algEquiv_commutes
    (ratFuncInfinityFractionRingEquiv K).symm
    (FractionRing.algEquiv (RatFuncInfinityIntegralClosure K L) L).symm z

local instance infinityAuxiliaryPlaceIsPrime
    (P : FiniteExtensionInfinityPlace K L) : P.1.IsPrime :=
  Ideal.primesOver.isPrime (ratFuncInfinityPlace K).asIdeal P

local instance infinityAuxiliaryPlaceLiesOver
    (P : FiniteExtensionInfinityPlace K L) :
    P.1.LiesOver (ratFuncInfinityPlace K).asIdeal :=
  Ideal.primesOver.liesOver (ratFuncInfinityPlace K).asIdeal P

/-- The localization of the infinity integral closure at one branch. -/
abbrev FiniteExtensionInfinityPlaceLocalRing
    (P : FiniteExtensionInfinityPlace K L) :=
  Localization.AtPrime
    (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal

section InfinityLocalOrder

variable {K L}

noncomputable def finiteExtensionInfinityPlaceLocalizationToField
    (P : FiniteExtensionInfinityPlace K L) :
    FiniteExtensionInfinityPlaceLocalRing K L P →+* L :=
  IsLocalization.lift
    (S := FiniteExtensionInfinityPlaceLocalRing K L P)
    (M := (primeOverHeightOne
      (ratFuncInfinityPlace K) P).asIdeal.primeCompl)
    (g := algebraMap (RatFuncInfinityIntegralClosure K L) L) fun y =>
      IsLocalization.map_units L
        ⟨y.1, (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal.primeCompl_le_nonZeroDivisors
          y.2⟩

omit [DecidableEq K] in
@[simp] theorem finiteExtensionInfinityPlaceLocalizationToField_comp_algebraMap
    (P : FiniteExtensionInfinityPlace K L) :
    (finiteExtensionInfinityPlaceLocalizationToField
      (K := K) (L := L) P).comp
        (algebraMap (RatFuncInfinityIntegralClosure K L)
          (FiniteExtensionInfinityPlaceLocalRing K L P)) =
      algebraMap (RatFuncInfinityIntegralClosure K L) L := by
  exact IsLocalization.lift_comp _

@[reducible] noncomputable def finiteExtensionInfinityPlaceLocalAlgebra
    (P : FiniteExtensionInfinityPlace K L) :
    Algebra (FiniteExtensionInfinityPlaceLocalRing K L P) L :=
  (finiteExtensionInfinityPlaceLocalizationToField
    (K := K) (L := L) P).toAlgebra

omit [DecidableEq K] in
theorem finiteExtensionInfinityPlaceLocalIsFractionRing
    (P : FiniteExtensionInfinityPlace K L) :
    let _ := finiteExtensionInfinityPlaceLocalAlgebra
      (K := K) (L := L) P
    IsFractionRing (FiniteExtensionInfinityPlaceLocalRing K L P) L := by
  let hIntegralClosureLocalAlgebra :
      Algebra (RatFuncInfinityIntegralClosure K L)
        (FiniteExtensionInfinityPlaceLocalRing K L P) := inferInstance
  let _ := finiteExtensionInfinityPlaceLocalAlgebra
    (K := K) (L := L) P
  let _ : SMul (RatFuncInfinityIntegralClosure K L)
      (FiniteExtensionInfinityPlaceLocalRing K L P) := Algebra.toSMul
  let _ : SMul (FiniteExtensionInfinityPlaceLocalRing K L P) L := Algebra.toSMul
  let _ : SMul (RatFuncInfinityIntegralClosure K L) L := Algebra.toSMul
  letI : IsScalarTower (RatFuncInfinityIntegralClosure K L)
      (FiniteExtensionInfinityPlaceLocalRing K L P) L := by
    have htower := IsScalarTower.of_algebraMap_eq'
      (R := RatFuncInfinityIntegralClosure K L)
      (S := FiniteExtensionInfinityPlaceLocalRing K L P) (A := L)
      (finiteExtensionInfinityPlaceLocalizationToField_comp_algebraMap
        (K := K) (L := L) P).symm
    exact htower
  have hFraction := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (R := RatFuncInfinityIntegralClosure K L)
    (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal.primeCompl
      (FiniteExtensionInfinityPlaceLocalRing K L P) L
  exact hFraction

noncomputable def finiteExtensionInfinityPlaceLocalOrderTop
    (P : FiniteExtensionInfinityPlace K L) (x : L) : WithTop ℤ := by
  let _ := finiteExtensionInfinityPlaceLocalAlgebra
    (K := K) (L := L) P
  letI := finiteExtensionInfinityPlaceLocalIsFractionRing
    (K := K) (L := L) P
  letI : IsDiscreteValuationRing
      (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (RatFuncInfinityIntegralClosure K L)
      (primeOverHeightOne (ratFuncInfinityPlace K) P).ne_bot
      (FiniteExtensionInfinityPlaceLocalRing K L P)
  exact finitePlaceOrderTop
    (IsDiscreteValuationRing.maximalIdeal
      (FiniteExtensionInfinityPlaceLocalRing K L P)) x

noncomputable def finiteExtensionInfinityPlaceLocalOrder
    (P : FiniteExtensionInfinityPlace K L) (x : L) : ℤ := by
  let _ := finiteExtensionInfinityPlaceLocalAlgebra
    (K := K) (L := L) P
  letI := finiteExtensionInfinityPlaceLocalIsFractionRing
    (K := K) (L := L) P
  letI : IsDiscreteValuationRing
      (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (RatFuncInfinityIntegralClosure K L)
      (primeOverHeightOne (ratFuncInfinityPlace K) P).ne_bot
      (FiniteExtensionInfinityPlaceLocalRing K L P)
  exact finitePlaceOrder
    (IsDiscreteValuationRing.maximalIdeal
      (FiniteExtensionInfinityPlaceLocalRing K L P)) x

omit [DecidableEq K] in
theorem finiteExtensionInfinityPlaceLocalOrder_eq_globalOrder
    (P : FiniteExtensionInfinityPlace K L) (x : L) :
    finiteExtensionInfinityPlaceLocalOrder (K := K) (L := L) P x =
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) x := by
  let _ := finiteExtensionInfinityPlaceLocalAlgebra
    (K := K) (L := L) P
  letI := finiteExtensionInfinityPlaceLocalIsFractionRing
    (K := K) (L := L) P
  letI : IsDiscreteValuationRing
      (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (RatFuncInfinityIntegralClosure K L)
      (primeOverHeightOne (ratFuncInfinityPlace K) P).ne_bot
      (FiniteExtensionInfinityPlaceLocalRing K L P)
  let _ : SMul (RatFuncInfinityIntegralClosure K L)
      (FiniteExtensionInfinityPlaceLocalRing K L P) := Algebra.toSMul
  let _ : SMul (FiniteExtensionInfinityPlaceLocalRing K L P) L := Algebra.toSMul
  let _ : SMul (RatFuncInfinityIntegralClosure K L) L := Algebra.toSMul
  letI : IsScalarTower (RatFuncInfinityIntegralClosure K L)
      (FiniteExtensionInfinityPlaceLocalRing K L P) L := by
    have htower := IsScalarTower.of_algebraMap_eq'
      (R := RatFuncInfinityIntegralClosure K L)
      (S := FiniteExtensionInfinityPlaceLocalRing K L P) (A := L)
      (finiteExtensionInfinityPlaceLocalizationToField_comp_algebraMap
        (K := K) (L := L) P).symm
    exact htower
  change finitePlaceOrder
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionInfinityPlaceLocalRing K L P)) x = _
  have hOrder := localizationAtPrime_finitePlaceOrder_eq
    (S := FiniteExtensionInfinityPlaceLocalRing K L P)
    (primeOverHeightOne (ratFuncInfinityPlace K) P) x
  exact hOrder

omit [DecidableEq K] in
theorem finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder
    (P : FiniteExtensionInfinityPlace K L) (x : L) (hx : x ≠ 0) :
    finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P x =
      (finitePlaceOrder
        (primeOverHeightOne (ratFuncInfinityPlace K) P) x : WithTop ℤ) := by
  let _ := finiteExtensionInfinityPlaceLocalAlgebra
    (K := K) (L := L) P
  letI := finiteExtensionInfinityPlaceLocalIsFractionRing
    (K := K) (L := L) P
  letI : IsDiscreteValuationRing
      (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (RatFuncInfinityIntegralClosure K L)
      (primeOverHeightOne (ratFuncInfinityPlace K) P).ne_bot
      (FiniteExtensionInfinityPlaceLocalRing K L P)
  simp only [finiteExtensionInfinityPlaceLocalOrderTop]
  rw [finitePlaceOrderTop_eq_coe _ _ hx]
  exact_mod_cast finiteExtensionInfinityPlaceLocalOrder_eq_globalOrder
    (K := K) (L := L) P x

omit [DecidableEq K] in
@[simp] theorem finiteExtensionInfinityPlaceLocalOrderTop_mul
    (P : FiniteExtensionInfinityPlace K L) (x y : L) :
    finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P (x * y) =
      finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P x +
        finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P y := by
  simp only [finiteExtensionInfinityPlaceLocalOrderTop,
    finitePlaceOrderTop_mul]

omit [DecidableEq K] in
@[simp] theorem finiteExtensionInfinityPlaceLocalOrderTop_pow
    (P : FiniteExtensionInfinityPlace K L) (x : L) (n : ℕ) :
    finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P (x ^ n) =
      n • finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P x := by
  simp only [finiteExtensionInfinityPlaceLocalOrderTop,
    finitePlaceOrderTop_pow]

end InfinityLocalOrder

section InfinityLocalAuxiliaryBounds

variable {K L}
variable {C : Type*} [Field C] [Algebra C L]

omit [DecidableEq K] in
/-- Preservation of the infinity integral closure propagates to the selected
localized branch. -/
theorem finiteExtensionInfinityPlace_local_preserves_of_global_preserves
    (P : FiniteExtensionInfinityPlace K L)
    (E : Derivation C L L)
    (hE : ∀ t : RatFuncInfinityIntegralClosure K L,
      ∃ t' : RatFuncInfinityIntegralClosure K L,
        E (algebraMap (RatFuncInfinityIntegralClosure K L) L t) =
          algebraMap (RatFuncInfinityIntegralClosure K L) L t') :
    ∀ r : FiniteExtensionInfinityPlaceLocalRing K L P,
      ∃ s : FiniteExtensionInfinityPlaceLocalRing K L P,
        E (finiteExtensionInfinityPlaceLocalizationToField
            (K := K) (L := L) P r) =
          finiteExtensionInfinityPlaceLocalizationToField
            (K := K) (L := L) P s := by
  let hLocalAlgebra := finiteExtensionInfinityPlaceLocalAlgebra
    (K := K) (L := L) P
  letI hLocalFraction := finiteExtensionInfinityPlaceLocalIsFractionRing
    (K := K) (L := L) P
  let _ : SMul (RatFuncInfinityIntegralClosure K L)
      (FiniteExtensionInfinityPlaceLocalRing K L P) := Algebra.toSMul
  let _ : SMul (FiniteExtensionInfinityPlaceLocalRing K L P) L := Algebra.toSMul
  let _ : SMul (RatFuncInfinityIntegralClosure K L) L := Algebra.toSMul
  letI : IsScalarTower (RatFuncInfinityIntegralClosure K L)
      (FiniteExtensionInfinityPlaceLocalRing K L P) L := by
    have htower := IsScalarTower.of_algebraMap_eq'
      (R := RatFuncInfinityIntegralClosure K L)
      (S := FiniteExtensionInfinityPlaceLocalRing K L P) (A := L)
      (finiteExtensionInfinityPlaceLocalizationToField_comp_algebraMap
        (K := K) (L := L) P).symm
    exact htower
  have hPreserves := ambientDerivation_preserves_localizationAtPrime_of_preserves
    (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal E hE
  exact hPreserves

/-- The infinity different supplies the exact canonical scaling coefficient.
The reciprocal-parameter derivations are explicit inputs: `Es` preserves the
infinity valuation ring and `D = -s² Es` after restricting constants. -/
theorem exists_finiteExtensionInfinityPlace_canonicalDifferent_scaling_certificate
    [Algebra K L] [IsScalarTower K (RatFunc K) L]
    [IsScalarTower K (RatFuncInfinityIntegers K) L]
    [IsScalarTower K (RatFuncInfinityIntegralClosure K L) L]
    [IsScalarTower (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) L]
    [Algebra K C] [IsScalarTower K C L]
    (D : Derivation C L L)
    (Ds : Derivation K (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegers K))
    (Es : Derivation K L L)
    (hEs : ∀ r : RatFuncInfinityIntegers K,
      Es (algebraMap (RatFuncInfinityIntegers K) L r) =
        algebraMap (RatFuncInfinityIntegers K) L (Ds r))
    (hDX : D.restrictScalars K =
      (-(algebraMap (RatFuncInfinityIntegers K) L
        (ratFuncInfinityUniformizer K)) ^ 2) • Es)
    (P : FiniteExtensionInfinityPlace K L) :
    ∃ c : L, c ≠ 0 ∧
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) c =
        finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L) (.inr P) ∧
      ∀ r : FiniteExtensionInfinityPlaceLocalRing K L P,
        ∃ s : FiniteExtensionInfinityPlaceLocalRing K L P,
          (c • D) (finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P r) =
            finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P s := by
  let q := primeOverHeightOne (ratFuncInfinityPlace K) P
  letI : q.asIdeal.LiesOver (ratFuncInfinityPlace K).asIdeal := by
    simpa [q] using
      (Ideal.primesOver.liesOver (ratFuncInfinityPlace K).asIdeal P)
  have hs : ratFuncInfinityUniformizer K ≠ 0 := by
    intro hsZero
    have hcoe : (ratFuncInfinityUniformizer K : RatFunc K) = 0 :=
      congrArg Subtype.val hsZero
    exact (ratFuncInfinityUniformizer_isUniformizer K).ne_zero hcoe
  obtain ⟨δ, hδ, _hδmem, _hδmult, hOrder, hPreserves⟩ :=
    exists_infinity_different_localGenerator_scaling_certificate
      (C := K) (S := RatFuncInfinityIntegers K)
      (T := RatFuncInfinityIntegralClosure K L) (L := L)
      (ratFuncInfinityPlace K) q (ratFuncInfinityUniformizer K) hs
      (ratFuncInfinityPlace_span_uniformizer K) Ds Es
      (D.restrictScalars K) hEs hDX
  let c : L :=
    -(algebraMap (RatFuncInfinityIntegralClosure K L) L δ) /
      (algebraMap (RatFuncInfinityIntegers K) L
        (ratFuncInfinityUniformizer K)) ^ 2
  have hδL : algebraMap (RatFuncInfinityIntegralClosure K L) L δ ≠ 0 := by
    simpa using
      (IsFractionRing.injective (RatFuncInfinityIntegralClosure K L) L).ne hδ
  have hsL : algebraMap (RatFuncInfinityIntegers K) L
      (ratFuncInfinityUniformizer K) ≠ 0 := by
    have hsT : algebraMap (RatFuncInfinityIntegers K)
        (RatFuncInfinityIntegralClosure K L)
        (ratFuncInfinityUniformizer K) ≠ 0 := by
      simpa using (FaithfulSMul.algebraMap_injective
        (RatFuncInfinityIntegers K)
        (RatFuncInfinityIntegralClosure K L)).ne hs
    rw [IsScalarTower.algebraMap_apply (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) L]
    exact (IsFractionRing.injective
      (RatFuncInfinityIntegralClosure K L) L).ne hsT
  have hc : c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hδL) (pow_ne_zero 2 hsL)
  have hGlobal : ∀ t : RatFuncInfinityIntegralClosure K L,
      ∃ t' : RatFuncInfinityIntegralClosure K L,
        (c • D) (algebraMap (RatFuncInfinityIntegralClosure K L) L t) =
          algebraMap (RatFuncInfinityIntegralClosure K L) L t' := by
    intro t
    obtain ⟨t', ht'⟩ := hPreserves t
    refine ⟨t', ?_⟩
    simpa only [c, Derivation.smul_apply, Algebra.smul_def,
      Algebra.algebraMap_self_apply, Derivation.restrictScalars_apply] using ht'
  refine ⟨c, hc, ?_, ?_⟩
  · rw [primeOverHeightOne_asIdeal] at hOrder
    simpa only [c, finiteExtensionCanonicalDifferentDivisor_inr] using hOrder
  · exact finiteExtensionInfinityPlace_local_preserves_of_global_preserves
      (K := K) (L := L) P (c • D) hGlobal

omit [DecidableEq K] in
/-- Infinity-place source case (iii), after scaling a global derivation by a
factor preserving the infinity integral closure. -/
theorem finiteExtensionInfinityPlace_auxiliaryFamily_caseIII_of_scaled_preserves
    (P : FiniteExtensionInfinityPlace K L)
    (h k : ℕ) {n : ℕ}
    (e : Sum (Fin k) (Fin (k + 1) × Fin h) ≃ Fin n)
    (epsilon : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (hepsilon : ∀ i, epsilon i = (e i : ℕ))
    (D : Derivation C L L) (c : L)
    (hScaledLocal :
      ∀ r : FiniteExtensionInfinityPlaceLocalRing K L P,
        ∃ s : FiniteExtensionInfinityPlaceLocalRing K L P,
          (c • D) (finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P r) =
            finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P s)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    (((k * (k - 1) / 2 : ℕ) *
          finiteExtensionInfinityPlaceLocalOrder (K := K) (L := L) P u +
        (h * k) *
          finiteExtensionInfinityPlaceLocalOrder (K := K) (L := L) P v +
        k * finiteExtensionInfinityPlaceLocalOrder (K := K) (L := L) P
          ((1 - u) / (1 - v)) +
        ∑ rs : Fin (k + 1) × Fin h,
          finiteExtensionInfinityPlaceLocalOrder (K := K) (L := L) P
            (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) -
        ∑ i, (epsilon i : ℤ) : ℤ) : WithTop ℤ) ≤
      n.choose 2 •
          finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P c +
        finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P
          (indexedDedekindLocalWronskian D epsilon
            (auxiliaryFamily u v h k)).det := by
  let hLocalAlgebra := finiteExtensionInfinityPlaceLocalAlgebra
    (K := K) (L := L) P
  letI hLocalFraction := finiteExtensionInfinityPlaceLocalIsFractionRing
    (K := K) (L := L) P
  letI : IsDiscreteValuationRing
      (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (RatFuncInfinityIntegralClosure K L)
      (primeOverHeightOne (ratFuncInfinityPlace K) P).ne_bot
      (FiniteExtensionInfinityPlaceLocalRing K L P)
  have hbound :=
    finitePlaceOrderTop_auxiliaryFamily_caseIII_source_lower_bound_of_preserves
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionInfinityPlaceLocalRing K L P))
      (c • D) hScaledLocal h k epsilon u v hu hv hu1 hv1
  have hchange := indexedDedekindLocalWronskian_det_changeParameter
    e epsilon hepsilon (c • D) D c rfl (auxiliaryFamily u v h k)
  change (((_ : ℤ) : WithTop ℤ) ≤ _) at hbound
  rw [hchange, finitePlaceOrderTop_mul, finitePlaceOrderTop_pow] at hbound
  exact hbound

omit [DecidableEq K] in
/-- Infinity-place source case (iv), with the same exact scaling correction. -/
theorem finiteExtensionInfinityPlace_auxiliaryFamily_caseIV_of_scaled_preserves
    (P : FiniteExtensionInfinityPlace K L)
    (h k : ℕ) {n : ℕ}
    (e : Sum (Fin k) (Fin (k + 1) × Fin h) ≃ Fin n)
    (epsilon : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (hepsilon : ∀ i, epsilon i = (e i : ℕ))
    (D : Derivation C L L) (c : L)
    (hScaledLocal :
      ∀ r : FiniteExtensionInfinityPlaceLocalRing K L P,
        ∃ s : FiniteExtensionInfinityPlaceLocalRing K L P,
          (c • D) (finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P r) =
            finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P s)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    (((k * (k - 1) / 2 : ℕ) *
          finiteExtensionInfinityPlaceLocalOrder (K := K) (L := L) P u +
        k * finiteExtensionInfinityPlaceLocalOrder (K := K) (L := L) P
          ((1 - u) / (1 - v)) +
        ∑ rs : Fin (k + 1) × Fin h,
          finiteExtensionInfinityPlaceLocalOrder (K := K) (L := L) P
            (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) -
        ∑ i, (epsilon i : ℤ) : ℤ) : WithTop ℤ) ≤
      n.choose 2 •
          finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P c +
        finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P
          (indexedDedekindLocalWronskian D epsilon
            (auxiliaryFamily u v h k)).det := by
  let hLocalAlgebra := finiteExtensionInfinityPlaceLocalAlgebra
    (K := K) (L := L) P
  letI hLocalFraction := finiteExtensionInfinityPlaceLocalIsFractionRing
    (K := K) (L := L) P
  letI : IsDiscreteValuationRing
      (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (RatFuncInfinityIntegralClosure K L)
      (primeOverHeightOne (ratFuncInfinityPlace K) P).ne_bot
      (FiniteExtensionInfinityPlaceLocalRing K L P)
  have hbound :=
    finitePlaceOrderTop_auxiliaryFamily_caseIV_source_lower_bound_of_preserves
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionInfinityPlaceLocalRing K L P))
      (c • D) hScaledLocal h k epsilon u v hu hv hu1 hv1
  have hchange := indexedDedekindLocalWronskian_det_changeParameter
    e epsilon hepsilon (c • D) D c rfl (auxiliaryFamily u v h k)
  change (((_ : ℤ) : WithTop ℤ) ≤ _) at hbound
  rw [hchange, finitePlaceOrderTop_mul, finitePlaceOrderTop_pow] at hbound
  exact hbound

end InfinityLocalAuxiliaryBounds

section InfinityGlobalOrderHelpers

variable {K L}

@[simp] theorem finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder
    (x : L) (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionPrincipalDivisor K L x (.inr P) =
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) x := by
  rw [finiteExtensionPrincipalDivisor_inr]
  symm
  simpa [ratFuncInfinityIntegralClosureFractionRingEquiv] using
    fractionRingAlgEquiv_finitePlaceOrder_eq
    (R := RatFuncInfinityIntegralClosure K L) (L := L)
    (primeOverHeightOne (ratFuncInfinityPlace K) P)
    ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x)

private theorem finiteExtensionInfinityPlace_gridOrder_sum_eq
    (P : FiniteExtensionInfinityPlace K L)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0) (h k : ℕ) :
    (∑ rs : Fin (k + 1) × Fin h,
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
        (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ))) =
      finiteExtensionPrincipalDivisor K L
        (finiteExtensionAuxiliaryGridProduct L u v h k) (.inr P) := by
  have hdiv := congrArg
    (fun D : FiniteExtensionPlace K L →₀ ℤ => D (.inr P))
    (finiteExtensionPrincipalDivisor_auxiliaryGridProduct K L u v hu hv h k)
  rw [hdiv]
  rw [Finset.sum_apply']
  apply Finset.sum_congr rfl
  intro rs hrs
  have hmul := congrArg
    (fun D : FiniteExtensionPlace K L →₀ ℤ => D (.inr P))
    (finiteExtensionPrincipalDivisor_mul K L
      (u ^ (rs.1 : ℕ)) (v ^ (rs.2 : ℕ))
      (pow_ne_zero _ hu) (pow_ne_zero _ hv))
  have hupow := congrArg
    (fun D : FiniteExtensionPlace K L →₀ ℤ => D (.inr P))
    (finiteExtensionPrincipalDivisor_pow K L u hu (rs.1 : ℕ))
  have hvpow := congrArg
    (fun D : FiniteExtensionPlace K L →₀ ℤ => D (.inr P))
    (finiteExtensionPrincipalDivisor_pow K L v hv (rs.2 : ℕ))
  simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
    finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder] at hmul hupow hvpow
  rw [hmul, hupow, hvpow]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
    finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder]

private theorem infinityAuxiliaryFamilyDerivativeOrder_sum_int (h k : ℕ) :
    (∑ i : Sum (Fin k) (Fin (k + 1) × Fin h),
      (auxiliaryFamilyDerivativeOrder h k i : ℤ)) =
      ((h * k + h + k).choose 2 : ℤ) := by
  exact_mod_cast auxiliaryFamilyDerivativeOrder_sum h k

end InfinityGlobalOrderHelpers

section InfinityCanonicalAuxiliaryCases

variable {K L}
variable {C : Type*} [Field C] [Algebra C L]

/-- Infinity source case (iii), expressed with the actual canonical different
coefficient and exhaustive principal divisors. -/
theorem finiteExtensionInfinityPlace_canonicalAuxiliary_caseIII_of_scaling
    (P : FiniteExtensionInfinityPlace K L)
    (D : Derivation C L L) (c : L) (hc : c ≠ 0)
    (hcOrder :
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) c =
        finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L) (.inr P))
    (hScaledLocal :
      ∀ r : FiniteExtensionInfinityPlaceLocalRing K L P,
        ∃ s : FiniteExtensionInfinityPlaceLocalRing K L P,
          (c • D) (finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P r) =
            finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P s)
    (h k : ℕ) (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hW : (indexedDedekindLocalWronskian D
      (auxiliaryFamilyDerivativeOrder h k)
      (auxiliaryFamily u v h k)).det ≠ 0) :
    ((k * (k - 1) / 2 : ℕ) : ℤ) *
          finiteExtensionPrincipalDivisor K L u (.inr P) +
        ((h * k : ℕ) : ℤ) *
          finiteExtensionPrincipalDivisor K L v (.inr P) +
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
            (auxiliaryFamily u v h k)).det (.inr P) := by
  have hbound :=
    finiteExtensionInfinityPlace_auxiliaryFamily_caseIII_of_scaled_preserves
      (K := K) (L := L) P h k
      (auxiliaryFamilyIndexEquiv h k)
      (auxiliaryFamilyDerivativeOrder h k) (fun _ => rfl)
      D c hScaledLocal u v hu hv hu1 hv1
  rw [finiteExtensionInfinityPlaceLocalOrder_eq_globalOrder,
    finiteExtensionInfinityPlaceLocalOrder_eq_globalOrder,
    finiteExtensionInfinityPlaceLocalOrder_eq_globalOrder] at hbound
  simp_rw [finiteExtensionInfinityPlaceLocalOrder_eq_globalOrder] at hbound
  rw [finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P c hc,
    finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P _ hW] at hbound
  have hboundInt :
      ((k * (k - 1) / 2 : ℕ) : ℤ) *
          finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) u +
        ((h * k : ℕ) : ℤ) *
          finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) v +
        (k : ℤ) *
          finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
            ((1 - u) / (1 - v)) +
        ∑ rs : Fin (k + 1) × Fin h,
          finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
            (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) -
        ∑ i : Sum (Fin k) (Fin (k + 1) × Fin h),
          (auxiliaryFamilyDerivativeOrder h k i : ℤ) ≤
      (h * k + h + k).choose 2 •
          finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) c +
        finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
          (indexedDedekindLocalWronskian D
            (auxiliaryFamilyDerivativeOrder h k)
            (auxiliaryFamily u v h k)).det := by
    exact_mod_cast hbound
  rw [infinityAuxiliaryFamilyDerivativeOrder_sum_int,
    finiteExtensionInfinityPlace_gridOrder_sum_eq P u v hu hv h k,
    hcOrder] at hboundInt
  simpa only [nsmul_eq_mul,
    finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder] using
    hboundInt

/-- Infinity source case (iv), in the same canonical global-divisor form. -/
theorem finiteExtensionInfinityPlace_canonicalAuxiliary_caseIV_of_scaling
    (P : FiniteExtensionInfinityPlace K L)
    (D : Derivation C L L) (c : L) (hc : c ≠ 0)
    (hcOrder :
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) c =
        finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L) (.inr P))
    (hScaledLocal :
      ∀ r : FiniteExtensionInfinityPlaceLocalRing K L P,
        ∃ s : FiniteExtensionInfinityPlaceLocalRing K L P,
          (c • D) (finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P r) =
            finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P s)
    (h k : ℕ) (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hW : (indexedDedekindLocalWronskian D
      (auxiliaryFamilyDerivativeOrder h k)
      (auxiliaryFamily u v h k)).det ≠ 0) :
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
            (auxiliaryFamily u v h k)).det (.inr P) := by
  have hbound :=
    finiteExtensionInfinityPlace_auxiliaryFamily_caseIV_of_scaled_preserves
      (K := K) (L := L) P h k
      (auxiliaryFamilyIndexEquiv h k)
      (auxiliaryFamilyDerivativeOrder h k) (fun _ => rfl)
      D c hScaledLocal u v hu hv hu1 hv1
  rw [finiteExtensionInfinityPlaceLocalOrder_eq_globalOrder,
    finiteExtensionInfinityPlaceLocalOrder_eq_globalOrder] at hbound
  simp_rw [finiteExtensionInfinityPlaceLocalOrder_eq_globalOrder] at hbound
  rw [finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P c hc,
    finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P _ hW] at hbound
  have hboundInt :
      ((k * (k - 1) / 2 : ℕ) : ℤ) *
          finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) u +
        (k : ℤ) *
          finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
            ((1 - u) / (1 - v)) +
        ∑ rs : Fin (k + 1) × Fin h,
          finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
            (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) -
        ∑ i : Sum (Fin k) (Fin (k + 1) × Fin h),
          (auxiliaryFamilyDerivativeOrder h k i : ℤ) ≤
      (h * k + h + k).choose 2 •
          finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) c +
        finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
          (indexedDedekindLocalWronskian D
            (auxiliaryFamilyDerivativeOrder h k)
            (auxiliaryFamily u v h k)).det := by
    exact_mod_cast hbound
  rw [infinityAuxiliaryFamilyDerivativeOrder_sum_int,
    finiteExtensionInfinityPlace_gridOrder_sum_eq P u v hu hv h k,
    hcOrder] at hboundInt
  simpa only [nsmul_eq_mul,
    finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder] using
    hboundInt

end InfinityCanonicalAuxiliaryCases

section InfinityCaseII

variable {K L}
variable {C : Type*} [Field C] [Algebra C L]

omit [DecidableEq K] in
theorem finiteExtensionInfinityPlace_exists_local_lift_of_orderTop_nonnegative
    (P : FiniteExtensionInfinityPlace K L) (x : L)
    (hx : (0 : WithTop ℤ) ≤
      finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P x) :
    ∃ x₀ : FiniteExtensionInfinityPlaceLocalRing K L P,
      x = finiteExtensionInfinityPlaceLocalizationToField
        (K := K) (L := L) P x₀ := by
  let _ := finiteExtensionInfinityPlaceLocalAlgebra (K := K) (L := L) P
  letI := finiteExtensionInfinityPlaceLocalIsFractionRing
    (K := K) (L := L) P
  letI : IsDiscreteValuationRing
      (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (RatFuncInfinityIntegralClosure K L)
      (primeOverHeightOne (ratFuncInfinityPlace K) P).ne_bot
      (FiniteExtensionInfinityPlaceLocalRing K L P)
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  have horder : 0 ≤ finitePlaceOrder
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionInfinityPlaceLocalRing K L P)) x := by
    simpa only [finiteExtensionInfinityPlaceLocalOrderTop,
      finitePlaceOrderTop_eq_coe _ _ hx0, WithTop.coe_nonneg] using hx
  have hval :
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionInfinityPlaceLocalRing K L P)).valuation L x ≤ 1 := by
    rw [valuation_eq_exp_neg_finitePlaceOrder _ x hx0]
    simpa only [← WithZero.exp_zero] using
      (WithZero.exp_le_exp.mpr (by omega :
        -finitePlaceOrder
          (IsDiscreteValuationRing.maximalIdeal
            (FiniteExtensionInfinityPlaceLocalRing K L P)) x ≤ 0))
  obtain ⟨x₀, hx₀⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hval
  exact ⟨x₀, hx₀.symm⟩

omit [DecidableEq K] in
theorem finiteExtensionInfinityPlace_auxiliaryFamily_caseII_of_scaled_preserves
    (P : FiniteExtensionInfinityPlace K L)
    (h k : ℕ) {n : ℕ}
    (e : Sum (Fin k) (Fin (k + 1) × Fin h) ≃ Fin n)
    (epsilon : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (hepsilon : ∀ i, epsilon i = (e i : ℕ))
    (D : Derivation C L L) (c : L)
    (hScaledLocal :
      ∀ r : FiniteExtensionInfinityPlaceLocalRing K L P,
        ∃ s : FiniteExtensionInfinityPlaceLocalRing K L P,
          (c • D) (finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P r) =
            finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P s)
    (u v : L)
    (hu : (0 : WithTop ℤ) ≤
      finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P u)
    (hv : (0 : WithTop ℤ) ≤
      finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P v)
    (hrho : (0 : WithTop ℤ) ≤
      finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P
        ((1 - u) / (1 - v))) :
    (0 : WithTop ℤ) ≤
      n.choose 2 •
          finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P c +
        finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P
          (indexedDedekindLocalWronskian D epsilon
            (auxiliaryFamily u v h k)).det := by
  let _ := finiteExtensionInfinityPlaceLocalAlgebra (K := K) (L := L) P
  letI := finiteExtensionInfinityPlaceLocalIsFractionRing
    (K := K) (L := L) P
  letI : IsDiscreteValuationRing
      (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (RatFuncInfinityIntegralClosure K L)
      (primeOverHeightOne (ratFuncInfinityPlace K) P).ne_bot
      (FiniteExtensionInfinityPlaceLocalRing K L P)
  have hbound := finitePlaceOrderTop_auxiliaryFamily_caseII_nonnegative_of_integral
    (IsDiscreteValuationRing.maximalIdeal
      (FiniteExtensionInfinityPlaceLocalRing K L P))
    (c • D) hScaledLocal h k epsilon u v
    (by
      obtain ⟨u₀, hu₀⟩ :=
        finiteExtensionInfinityPlace_exists_local_lift_of_orderTop_nonnegative
          P u hu
      exact ⟨u₀, hu₀⟩)
    (by
      obtain ⟨v₀, hv₀⟩ :=
        finiteExtensionInfinityPlace_exists_local_lift_of_orderTop_nonnegative
          P v hv
      exact ⟨v₀, hv₀⟩)
    (by
      obtain ⟨rho₀, hrho₀⟩ :=
        finiteExtensionInfinityPlace_exists_local_lift_of_orderTop_nonnegative
          P ((1 - u) / (1 - v)) hrho
      exact ⟨rho₀, hrho₀⟩)
  have hchange := indexedDedekindLocalWronskian_det_changeParameter
    e epsilon hepsilon (c • D) D c rfl (auxiliaryFamily u v h k)
  rw [hchange, finitePlaceOrderTop_mul, finitePlaceOrderTop_pow] at hbound
  exact hbound

theorem finiteExtensionInfinityPlace_canonicalAuxiliary_caseII_of_scaling
    (P : FiniteExtensionInfinityPlace K L)
    (D : Derivation C L L) (c : L) (hc : c ≠ 0)
    (hcOrder :
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) c =
        finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L) (.inr P))
    (hScaledLocal :
      ∀ r : FiniteExtensionInfinityPlaceLocalRing K L P,
        ∃ s : FiniteExtensionInfinityPlaceLocalRing K L P,
          (c • D) (finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P r) =
            finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P s)
    (h k : ℕ) (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huOrder : 0 ≤
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) u)
    (hvOrder : 0 ≤
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) v)
    (hrhoOrder : 0 ≤
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
        ((1 - u) / (1 - v)))
    (hW : (indexedDedekindLocalWronskian D
      (auxiliaryFamilyDerivativeOrder h k)
      (auxiliaryFamily u v h k)).det ≠ 0) :
    0 ≤ ((h * k + h + k).choose 2 : ℤ) *
        finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L) (.inr P) +
      finiteExtensionPrincipalDivisor K L
        (indexedDedekindLocalWronskian D
          (auxiliaryFamilyDerivativeOrder h k)
          (auxiliaryFamily u v h k)).det (.inr P) := by
  have hrho : (1 - u) / (1 - v) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hu1.symm) (sub_ne_zero.mpr hv1.symm)
  have huTop : (0 : WithTop ℤ) ≤
      finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P u := by
    rw [finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P u hu]
    exact_mod_cast huOrder
  have hvTop : (0 : WithTop ℤ) ≤
      finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P v := by
    rw [finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P v hv]
    exact_mod_cast hvOrder
  have hrhoTop : (0 : WithTop ℤ) ≤
      finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P
        ((1 - u) / (1 - v)) := by
    rw [finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P _ hrho]
    exact_mod_cast hrhoOrder
  have hbound :=
    finiteExtensionInfinityPlace_auxiliaryFamily_caseII_of_scaled_preserves
      (K := K) (L := L) P h k
      (auxiliaryFamilyIndexEquiv h k)
      (auxiliaryFamilyDerivativeOrder h k) (fun _ => rfl)
      D c hScaledLocal u v huTop hvTop hrhoTop
  rw [finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P c hc,
    finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P _ hW] at hbound
  have hboundInt :
      0 ≤ (h * k + h + k).choose 2 •
          finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) c +
        finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
          (indexedDedekindLocalWronskian D
            (auxiliaryFamilyDerivativeOrder h k)
            (auxiliaryFamily u v h k)).det := by
    exact_mod_cast hbound
  rw [hcOrder] at hboundInt
  simpa only [nsmul_eq_mul,
    finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder] using hboundInt

end InfinityCaseII

section InfinityResiduePerfect

variable {K L}

theorem ratFuncInfinityPlace_residueField_finite [Fintype K] :
    Finite (ratFuncInfinityPlace K).asIdeal.ResidueField := by
  exact Finite.of_injective (ratFuncInfinityPlaceResidueEquiv K)
    (ratFuncInfinityPlaceResidueEquiv K).injective

theorem finiteExtensionInfinityPlace_residueField_finite [Fintype K]
    (P : FiniteExtensionInfinityPlace K L) : Finite P.1.ResidueField := by
  let p := (ratFuncInfinityPlace K).asIdeal
  letI : Finite p.ResidueField :=
    ratFuncInfinityPlace_residueField_finite (K := K)
  letI : P.1.LiesOver p := by
    simpa [p] using Ideal.primesOver.liesOver
      (ratFuncInfinityPlace K).asIdeal P
  letI hLocalAlg := Localization.AtPrime.algebraOfLiesOver p P.1
  have : IsScalarTower (RatFuncInfinityIntegers K) (Localization.AtPrime p)
      (Localization.AtPrime P.1) := inferInstance
  letI : Algebra.QuasiFiniteAt (RatFuncInfinityIntegers K) P.1 := inferInstance
  letI : Module.Finite p.ResidueField P.1.ResidueField := inferInstance
  exact Module.finite_of_finite p.ResidueField

theorem finiteExtensionInfinityPlaceLocal_residueField_perfect [Fintype K]
    (P : FiniteExtensionInfinityPlace K L) :
    letI : IsDiscreteValuationRing
      (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (RatFuncInfinityIntegralClosure K L)
      (primeOverHeightOne (ratFuncInfinityPlace K) P).ne_bot
      (FiniteExtensionInfinityPlaceLocalRing K L P)
    PerfectField
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionInfinityPlaceLocalRing K L P)).asIdeal.ResidueField := by
  let q := (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal
  letI : Finite q.ResidueField := by
    simpa [q, primeOverHeightOne_asIdeal] using
      finiteExtensionInfinityPlace_residueField_finite (K := K) (L := L) P
  letI : Finite (HasQuotient.Quotient
      (RatFuncInfinityIntegralClosure K L) q) :=
    Finite.of_injective
      (algebraMap (HasQuotient.Quotient
        (RatFuncInfinityIntegralClosure K L) q) q.ResidueField)
      q.injective_algebraMap_quotient_residueField
  letI : IsDiscreteValuationRing
      (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (RatFuncInfinityIntegralClosure K L)
      (primeOverHeightOne (ratFuncInfinityPlace K) P).ne_bot
      (FiniteExtensionInfinityPlaceLocalRing K L P)
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal q
    (FiniteExtensionInfinityPlaceLocalRing K L P)
  letI : Finite (HasQuotient.Quotient
      (FiniteExtensionInfinityPlaceLocalRing K L P)
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionInfinityPlaceLocalRing K L P)).asIdeal) :=
    Finite.of_injective e.symm e.symm.injective
  let Rq := HasQuotient.Quotient
    (FiniteExtensionInfinityPlaceLocalRing K L P)
    (IsDiscreteValuationRing.maximalIdeal
      (FiniteExtensionInfinityPlaceLocalRing K L P)).asIdeal
  letI : Finite
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionInfinityPlaceLocalRing K L P)).asIdeal.ResidueField :=
    IsLocalization.finite Rq (nonZeroDivisors Rq)
  exact PerfectField.ofFinite

end InfinityResiduePerfect

section InfinityCaseI

variable {K L}
variable {p : ℕ} [Fact p.Prime] [CharP L p]

private theorem infinityPlaceOrder_gridMonomial_eq_zero
    (P : FiniteExtensionInfinityPlace K L)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (huOrder : finitePlaceOrder
      (primeOverHeightOne (ratFuncInfinityPlace K) P) u = 0)
    (hvOrder : finitePlaceOrder
      (primeOverHeightOne (ratFuncInfinityPlace K) P) v = 0)
    (i j : ℕ) :
    finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
      (u ^ i * v ^ j) = 0 := by
  have hmul := congrArg
    (fun E : FiniteExtensionPlace K L →₀ ℤ => E (.inr P))
    (finiteExtensionPrincipalDivisor_mul K L
      (u ^ i) (v ^ j) (pow_ne_zero _ hu) (pow_ne_zero _ hv))
  have hupow := congrArg
    (fun E : FiniteExtensionPlace K L →₀ ℤ => E (.inr P))
    (finiteExtensionPrincipalDivisor_pow K L u hu i)
  have hvpow := congrArg
    (fun E : FiniteExtensionPlace K L →₀ ℤ => E (.inr P))
    (finiteExtensionPrincipalDivisor_pow K L v hv j)
  simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
    finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder] at hmul hupow hvpow
  rw [hmul, hupow, hvpow, huOrder, hvOrder]
  simp

theorem finiteExtensionInfinityPlace_auxiliaryFamily_caseI_of_scaled_preserves
    [Fintype K]
    (P : FiniteExtensionInfinityPlace K L)
    (h k : ℕ) {n : ℕ}
    (e : Sum (Fin k) (Fin (k + 1) × Fin h) ≃ Fin n)
    (epsilonOrder : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (hepsilon : ∀ i, epsilonOrder i = (e i : ℕ))
    (epsilon qBound : ℕ)
    (D : Derivation (frobeniusSubfield L p) L L) (c : L)
    (hScaledLocal :
      ∀ r : FiniteExtensionInfinityPlaceLocalRing K L P,
        ∃ s : FiniteExtensionInfinityPlaceLocalRing K L P,
          (c • D) (finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P r) =
            finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P s)
    (u v : L)
    (hrhoNe : (1 - u) / (1 - v) ≠ 0)
    (huOrder :
      finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P u = 0)
    (hrhoOrder :
      finiteExtensionInfinityPlaceLocalOrder (K := K) (L := L) P
        ((1 - u) / (1 - v)) < 0)
    (hgridRegular : ∀ rs : Fin (k + 1) × Fin h,
      (0 : WithTop ℤ) ≤
        finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P
          (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)))
    (hepsilonInjective : Function.Injective epsilonOrder)
    (hepsilonMax : ∀ i, epsilonOrder i ≤ epsilon)
    (hk : k ≤ epsilon + 1) (hepsilonQ : epsilon + 1 ≤ qBound) :
    (((qBound : ℤ) *
        finiteExtensionInfinityPlaceLocalOrder (K := K) (L := L) P
          ((1 - u) / (1 - v)) : ℤ) : WithTop ℤ) ≤
      n.choose 2 •
          finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P c +
        finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P
          (indexedDedekindLocalWronskian D epsilonOrder
            (auxiliaryFamily u v h k)).det := by
  let _ := finiteExtensionInfinityPlaceLocalAlgebra (K := K) (L := L) P
  letI := finiteExtensionInfinityPlaceLocalIsFractionRing
    (K := K) (L := L) P
  letI : IsDiscreteValuationRing
      (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (RatFuncInfinityIntegralClosure K L)
      (primeOverHeightOne (ratFuncInfinityPlace K) P).ne_bot
      (FiniteExtensionInfinityPlaceLocalRing K L P)
  letI : CharP (FiniteExtensionInfinityPlaceLocalRing K L P) p := ⟨by
    intro m
    rw [← map_eq_zero_iff
      (finiteExtensionInfinityPlaceLocalizationToField
        (K := K) (L := L) P)
      (by
        change Function.Injective
          (algebraMap (FiniteExtensionInfinityPlaceLocalRing K L P) L)
        exact IsFractionRing.injective
          (FiniteExtensionInfinityPlaceLocalRing K L P) L),
      map_natCast, CharP.cast_eq_zero_iff L p]⟩
  letI : PerfectField
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionInfinityPlaceLocalRing K L P)).asIdeal.ResidueField :=
    finiteExtensionInfinityPlaceLocal_residueField_perfect
      (K := K) (L := L) P
  obtain ⟨A, hAdet, hdet, hbound⟩ :=
    exists_frobeniusSubfield_dedekindAuxiliaryFamily_caseI_q_wronskian_bound_of_perfect_residue
      (p := p)
      (IsDiscreteValuationRing.maximalIdeal
        (FiniteExtensionInfinityPlaceLocalRing K L P))
      (c • D) hScaledLocal u v h k epsilonOrder epsilon qBound
      hrhoNe huOrder hrhoOrder hgridRegular hepsilonInjective
      hepsilonMax hk hepsilonQ
  have hchange := indexedDedekindLocalWronskian_det_changeParameter
    e epsilonOrder hepsilon (c • D) D c rfl (auxiliaryFamily u v h k)
  rw [hchange, finitePlaceOrderTop_mul, finitePlaceOrderTop_pow] at hbound
  change (((qBound : ℤ) *
      finiteExtensionInfinityPlaceLocalOrder (K := K) (L := L) P
        ((1 - u) / (1 - v)) : ℤ) : WithTop ℤ) ≤
    n.choose 2 •
        finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P c +
      finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P
        (indexedDedekindLocalWronskian D epsilonOrder
          (auxiliaryFamily u v h k)).det at hbound
  exact hbound

theorem finiteExtensionInfinityPlace_canonicalAuxiliary_caseI_of_scaling
    [Fintype K]
    (P : FiniteExtensionInfinityPlace K L)
    (D : Derivation (frobeniusSubfield L p) L L)
    (c : L) (hc : c ≠ 0)
    (hcOrder :
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) c =
        finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L) (.inr P))
    (hScaledLocal :
      ∀ r : FiniteExtensionInfinityPlaceLocalRing K L P,
        ∃ s : FiniteExtensionInfinityPlaceLocalRing K L P,
          (c • D) (finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P r) =
            finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P s)
    (h k : ℕ) (hn : 0 < h * k + h + k)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huOrder : finitePlaceOrder
      (primeOverHeightOne (ratFuncInfinityPlace K) P) u = 0)
    (hvOrder : finitePlaceOrder
      (primeOverHeightOne (ratFuncInfinityPlace K) P) v = 0)
    (hrhoOrder : finitePlaceOrder
      (primeOverHeightOne (ratFuncInfinityPlace K) P)
        ((1 - u) / (1 - v)) < 0)
    (hW : (indexedDedekindLocalWronskian D
      (auxiliaryFamilyDerivativeOrder h k)
      (auxiliaryFamily u v h k)).det ≠ 0) :
    ((h * k + h + k : ℕ) : ℤ) *
        finiteExtensionPrincipalDivisor K L
          ((1 - u) / (1 - v)) (.inr P) ≤
      ((h * k + h + k).choose 2 : ℤ) *
          finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L) (.inr P) +
        finiteExtensionPrincipalDivisor K L
          (indexedDedekindLocalWronskian D
            (auxiliaryFamilyDerivativeOrder h k)
            (auxiliaryFamily u v h k)).det (.inr P) := by
  let n := h * k + h + k
  have hrho : (1 - u) / (1 - v) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hu1.symm) (sub_ne_zero.mpr hv1.symm)
  have huTop :
      finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P u = 0 := by
    rw [finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P u hu]
    exact_mod_cast huOrder
  have hrhoLocal :
      finiteExtensionInfinityPlaceLocalOrder (K := K) (L := L) P
        ((1 - u) / (1 - v)) < 0 := by
    rw [finiteExtensionInfinityPlaceLocalOrder_eq_globalOrder]
    exact hrhoOrder
  have hgridRegular : ∀ rs : Fin (k + 1) × Fin h,
      (0 : WithTop ℤ) ≤
        finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P
          (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) := by
    intro rs
    have hmonomial : u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hv)
    rw [finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P _ hmonomial]
    have hzero := infinityPlaceOrder_gridMonomial_eq_zero
      (K := K) (L := L) P u v hu hv huOrder hvOrder
        (rs.1 : ℕ) (rs.2 : ℕ)
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
    finiteExtensionInfinityPlace_auxiliaryFamily_caseI_of_scaled_preserves
      (K := K) (L := L) (p := p) P h k
      (auxiliaryFamilyIndexEquiv h k)
      (auxiliaryFamilyDerivativeOrder h k) (fun _ => rfl)
      (n - 1) n D c hScaledLocal u v hrho huTop hrhoLocal
      hgridRegular (auxiliaryFamilyDerivativeOrder_injective h k)
      hepsilonMax hkBound hepsilonQ
  rw [finiteExtensionInfinityPlaceLocalOrder_eq_globalOrder,
    finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P c hc,
    finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P _ hW] at hbound
  have hboundInt :
      (n : ℤ) *
          finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
            ((1 - u) / (1 - v)) ≤
        n.choose 2 •
            finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) c +
          finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
            (indexedDedekindLocalWronskian D
              (auxiliaryFamilyDerivativeOrder h k)
              (auxiliaryFamily u v h k)).det := by
    exact_mod_cast hbound
  rw [hcOrder] at hboundInt
  simpa only [n, nsmul_eq_mul,
    finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder] using hboundInt

end InfinityCaseI

end

end BGS.CorvajaZannier
