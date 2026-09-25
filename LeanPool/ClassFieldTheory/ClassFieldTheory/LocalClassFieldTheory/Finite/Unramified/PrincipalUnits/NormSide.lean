/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.Basic
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois
/-! Provides the public declarations in the
  `LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.NormSide` Lean module. -/

@[expose] public section

noncomputable
section

universe u

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- States the theorem `normIntegerUnits_to_fieldUnits`. -/
theorem normIntegerUnits_to_fieldUnits (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [LocalFieldTheory.ValuativeExtension K L] (u : 𝒪[L]ˣ) :
    integerUnitsToFieldUnits K (normIntegerUnits K L u) =
      LocalFieldTheory.normUnits K L (integerUnitsToFieldUnits L u) := by
  ext
  rfl

/-- Actual integral-closure version of the integer-unit norm product formula.

This is the unramified norm calculation input that embeds `N(u)` back into `𝒪[L]` and
identifies it with the product of Galois conjugates of `u`; the Galois action
on `𝒪[L]` is produced from integral closure, not from a valuation-invariance
certificate. -/
theorem integerUnitsMap_normIntegerUnits_eq_galoisGroup_prod_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (u : 𝒪[L]ˣ) :
    integerUnitsMapOfValuationExtension K L (normIntegerUnits K L u) =
      Finset.univ.prod (fun σ : Gal(L/K) =>
        Units.mapEquiv
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u) := by
  ext
  have hfield := mapBaseUnits_normUnits_eq_prod_gal (K := K) (L := L)
    (integerUnitsToFieldUnits L u)
  have hfield' := congrArg (fun z : Lˣ => (z : L)) hfield
  simp only [mapBaseUnitsToExtensionUnits_apply_coe, normUnits_apply_coe,
    integerUnitsToFieldUnits_apply] at hfield'
  change (algebraMap K L (((normIntegerUnits K L u : 𝒪[K]ˣ) : 𝒪[K]) : K)) =
      (((Finset.univ.prod (fun σ : Gal(L/K) =>
        Units.mapEquiv
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u) : 𝒪[L]ˣ) :
          𝒪[L]) : L)
  rw [normIntegerUnits_apply_coe]
  simpa [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply] using hfield'

/-- The product of actual integral-closure Galois conjugates preserves every
principal-unit level. -/
theorem galoisGroup_prod_mem_principalUnits_of_isIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (u : 𝒪[L]ˣ) (hu : u ∈ principalUnits L n) :
    Finset.univ.prod (fun σ : Gal(L/K) =>
      Units.mapEquiv
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u) ∈
        principalUnits L n := by
  simpa using (Subgroup.prod_mem (principalUnits L n) (t := Finset.univ)
    (f := fun σ : Gal(L/K) =>
      Units.mapEquiv
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u)
    (fun σ _ =>
      principalUnits_integerRingEquiv_mem_self L n
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) u hu))

/-- Actual integral-closure version: after embedding `N(u)` back into `𝒪[L]`,
the result remains in the same principal-unit level. -/
theorem integerUnitsMap_normIntegerUnits_mem_principalUnits_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (u : 𝒪[L]ˣ) (hu : u ∈ principalUnits L n) :
    integerUnitsMapOfValuationExtension K L (normIntegerUnits K L u) ∈
      principalUnits L n := by
  rw [integerUnitsMap_normIntegerUnits_eq_galoisGroup_prod_of_isIntegralClosure K L u]
  exact galoisGroup_prod_mem_principalUnits_of_isIntegralClosure K L n u hu

/-- Actual integral-closure version of the base-extended norm on `U_L^n`.

This is the source map for the unramified norm product calculation; it
asserts only that the embedded norm remains in `U_L^n`. -/
noncomputable def principalUnitsNormExtensionSideOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L] (n : Nat) :
    principalUnits L n →* principalUnits L n where
  toFun u :=
    ⟨integerUnitsMapOfValuationExtension K L (normIntegerUnits K L u.1),
      integerUnitsMap_normIntegerUnits_mem_principalUnits_of_isIntegralClosure
        K L n u.1 u.2⟩
  map_one' := by
    ext
    simp [integerUnitsMapOfValuationExtension]
  map_mul' := by
    intro u v
    ext
    simp [integerUnitsMapOfValuationExtension]

/-- States the theorem `principalUnitsNormExtensionSideOfIsIntegralClosure_apply`. -/
@[simp]
theorem principalUnitsNormExtensionSideOfIsIntegralClosure_apply (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (u : principalUnits L n) :
    ((principalUnitsNormExtensionSideOfIsIntegralClosure K L n u :
        principalUnits L n) : 𝒪[L]ˣ) =
      integerUnitsMapOfValuationExtension K L (normIntegerUnits K L u.1) :=
  rfl

/-- Actual integral-closure version: the base-extended norm on `U_L^n` is the
product of the actual integral-closure real Galois actions. -/
theorem principalUnitsNormExtensionSideOfIsIntegralClosure_eq_galoisGroup_prod
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (u : principalUnits L n) :
    principalUnitsNormExtensionSideOfIsIntegralClosure K L n u =
      Finset.univ.prod (fun σ : Gal(L/K) =>
        galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ u) := by
  apply Subtype.ext
  simpa [principalUnitsNormExtensionSideOfIsIntegralClosure_apply,
    galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure_apply] using
    integerUnitsMap_normIntegerUnits_eq_galoisGroup_prod_of_isIntegralClosure K L u.1

/-- Actual integral-closure version of the first-order norm-product
calculation before residue trace identification. -/
theorem
  principalUnitsNormExtensionSideOfIsIntegralClosure_oneAdd_sub_one_sub_sum_mem_maximalIdeal_pow_succ
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[L] ^ n : Ideal 𝒪[L])) :
    (((principalUnitsNormExtensionSideOfIsIntegralClosure K L n
          (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2) :
        principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]) - 1 -
      (Finset.univ.sum fun σ : Gal(L/K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) ∈
        (𝓂[L] ^ (n + 1) : Ideal 𝒪[L]) := by
  classical
  rw [principalUnitsNormExtensionSideOfIsIntegralClosure_eq_galoisGroup_prod K L n
    (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)]
  simpa [galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure,
    principalUnitsMapEquivOfIntegerRingEquiv,
    principalUnitOneAddOfMemPowSubgroup, principalUnitOneAddOfMemPow_val]
    using
      galoisGroup_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ_of_isIntegralClosure
        K L n hn a

/-- Actual integral-closure version of the base-extended norm on successive
principal-unit quotients. -/
def principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L] (n : Nat) :
    PrincipalUnitsSuccQuot L n →* PrincipalUnitsSuccQuot L n :=
  QuotientGroup.map
    ((principalUnits L (n + 1)).subgroupOf (principalUnits L n))
    ((principalUnits L (n + 1)).subgroupOf (principalUnits L n))
    (principalUnitsNormExtensionSideOfIsIntegralClosure K L n)
    (by
      intro u hu
      change ((principalUnitsNormExtensionSideOfIsIntegralClosure K L n u :
          principalUnits L n) : 𝒪[L]ˣ) ∈ principalUnits L (n + 1)
      simpa [principalUnitsNormExtensionSideOfIsIntegralClosure_apply] using
        integerUnitsMap_normIntegerUnits_mem_principalUnits_of_isIntegralClosure
          K L (n + 1) u.1 hu)

/-- States the theorem `principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure_mk`. -/
@[simp]
theorem principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure_mk
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (u : principalUnits L n) :
    principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure K L n
        (QuotientGroup.mk u) =
      QuotientGroup.mk
        (principalUnitsNormExtensionSideOfIsIntegralClosure K L n u) :=
  rfl

/-- Actual integral-closure version: on `U_L^n/U_L^(n+1)`, the base-extended
norm is the product of the induced actual real Galois actions. -/
theorem principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure_eq_galoisGroup_prod
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (x : PrincipalUnitsSuccQuot L n) :
    principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure K L n x =
      Finset.univ.prod (fun σ : Gal(L/K) =>
        galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ x) := by
  refine QuotientGroup.induction_on x ?_
  intro u
  rw [principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure_mk,
    principalUnitsNormExtensionSideOfIsIntegralClosure_eq_galoisGroup_prod]
  change (principalUnitsSuccQuotMk L n)
      (Finset.univ.prod (fun σ : Gal(L/K) =>
        galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ u)) =
    Finset.univ.prod (fun σ : Gal(L/K) =>
      (principalUnitsSuccQuotMk L n)
        (galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ u))
  exact map_prod (principalUnitsSuccQuotMk L n)
    (fun σ : Gal(L/K) =>
      galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ u) Finset.univ

end LocalClassFieldTheory
