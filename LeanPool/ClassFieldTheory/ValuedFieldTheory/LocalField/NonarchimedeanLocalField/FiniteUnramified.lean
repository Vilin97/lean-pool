/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
/-!
# Finite unramified valued extensions

Develops the ideal, residue-field, Galois, trace, and norm consequences of a
finite valued extension with ramification index one and full residue degree.
-/

@[expose] public section

namespace LocalFieldTheory

noncomputable
section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel

/-- A finite valuation extension is unramified at the actual valuation-ring
frontier when the ramification index of the maximal ideals is one.

This is the concrete source needed for residue-field automorphism comparisons. -/
class IsUnramifiedValuedExtension (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop where
  /-- The maximal ideal of `𝒪[L]` has ramification index one over `𝒪[K]`. -/
  maximalIdeal_ramificationIdx_eq_one :
    (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1

/-- An unramified valued extension has ramification index one. -/
theorem unramifiedValuation_ramificationIdx_eq_one
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] [IsUnramifiedValuedExtension K L] :
    (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1 :=
  IsUnramifiedValuedExtension.maximalIdeal_ramificationIdx_eq_one
    (K := K) (L := L)

/-- For an unramified valued extension, the residue-field degree equals the field-extension degree.
For an unramified valued extension, the residue-field degree equals the field-extension degree. -/
theorem unramifiedValuation_residue_finrank_eq_finrank
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] [IsUnramifiedValuedExtension K L] :
    Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L := by
  have h :=
    LocalFieldTheory.maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank K L
  have hp : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal 𝒪[K])
      (IsDiscreteValuationRing.not_isField 𝒪[K])
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp,
    unramifiedValuation_ramificationIdx_eq_one K L, one_mul] at h
  exact h

end IsNonarchimedeanLocalField

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField
open Filter

/-- In an actual unramified valuation extension, the image of the base maximal
ideal is the maximal ideal upstairs. -/
theorem maximalIdeal_map_eq_maximalIdeal_of_unramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Ideal.map (algebraMap 𝒪[K] 𝒪[L]) (𝓂[K] : Ideal 𝒪[K]) =
      (𝓂[L] : Ideal 𝒪[L]) := by
  have hp : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ := by
    exact Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal 𝒪[K])
      (IsDiscreteValuationRing.not_isField 𝒪[K])
  have hfact := Ideal.map_algebraMap_eq_finsetProd_pow
    (R := 𝒪[L]) (S := 𝒪[K]) (p := (𝓂[K] : Ideal 𝒪[K])) hp
  have hfin : ((𝓂[K] : Ideal 𝒪[K]).primesOver 𝒪[L]).toFinset =
      ({(𝓂[L] : Ideal 𝒪[L])} : Finset (Ideal 𝒪[L])) := by
    ext P
    simp [IsLocalRing.primesOver_eq 𝒪[L] hp]
  rw [hfin] at hfact
  simpa [LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_ramificationIdx_eq_one K L]
    using hfact

/-- A base DVR uniformizer remains a DVR uniformizer after an actual
unramified valuation extension. -/
theorem integerRingMap_uniformizer_irreducible_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Irreducible (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  calc
    (𝓂[L] : Ideal 𝒪[L]) =
        Ideal.map (algebraMap 𝒪[K] 𝒪[L]) (𝓂[K] : Ideal 𝒪[K]) :=
      (maximalIdeal_map_eq_maximalIdeal_of_unramifiedValuation K L).symm
    _ = Ideal.map (algebraMap 𝒪[K] 𝒪[L])
        (Ideal.span ({chosenIntegerRingUniformizer K} : Set 𝒪[K])) := by
          rw [chosenIntegerRingUniformizer_maximalIdeal_eq K]
    _ = Ideal.span
        ({integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)} :
          Set 𝒪[L]) := by
          rw [Ideal.map_span, Set.image_singleton]
          rfl

/-- in an actual unramified valuation extension, the base
prime element remains a prime element upstairs and therefore has upstairs
normalized value `-1`.

This is the source-producing replacement for passing an upstairs
uniformizer-value input to later norm-valuation arguments. -/
theorem v_mapBaseUnitsToExtensionUnits_integerRingUniformizerFieldUnit_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    LocalFieldTheory.IsNonarchimedeanLocalField.v L
      (Additive.ofMul
        (mapBaseUnitsToExtensionUnits K L (integerRingUniformizerFieldUnit K))) = -1 := by
  let πL : 𝒪[L] := integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
  have hπL : Irreducible πL := by
    simpa [πL] using integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  exact v_integerRingIrreducibleFieldUnit L πL hπL
    (mapBaseUnitsToExtensionUnits K L (integerRingUniformizerFieldUnit K)) (by
      dsimp [πL]
      rfl)

/-- In an actual unramified valuation extension, the inverse of the base prime
element has upstairs normalized value `1`.  This is the L-side generator needed
before the local class-field norm-valuation calculation. -/
theorem v_mapBaseUnitsToExtensionUnits_inverseIntegerRingUniformizerFieldUnit_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    LocalFieldTheory.IsNonarchimedeanLocalField.v L
      (Additive.ofMul
        (mapBaseUnitsToExtensionUnits K L (inverseIntegerRingUniformizerFieldUnit K))) =
      1 := by
  rw [inverseIntegerRingUniformizerFieldUnit,
    (mapBaseUnitsToExtensionUnits K L).map_inv]
  rw [LocalFieldTheory.IsNonarchimedeanLocalField.v_inv]
  rw [v_mapBaseUnitsToExtensionUnits_integerRingUniformizerFieldUnit_of_unramifiedValuation]
  norm_num

/-- In an actual unramified valuation extension, the integer-ring map sends
`𝓂_K^n` into `𝓂_L^n`.  The proof uses the base uniformizer as an upstairs
uniformizer, which is the local source needed before comparing graded
principal-unit quotients with residue fields. -/
theorem integerRingMap_mem_maximalIdeal_pow_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) {a : 𝒪[K]} (ha : a ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) :
    integerRingMapOfValuationExtension K L a ∈ (𝓂[L] ^ n : Ideal 𝒪[L]) := by
  let πK : 𝒪[K] := chosenIntegerRingUniformizer K
  have hπL : Irreducible (integerRingMapOfValuationExtension K L πK) := by
    simpa [πK] using integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  have ha_span : a ∈ Ideal.span ({πK ^ n} : Set 𝒪[K]) := by
    simpa [πK, maximalIdeal_pow_eq_span_uniformizer_pow K n] using ha
  rcases (Ideal.mem_span_singleton.mp ha_span) with ⟨r, hr⟩
  rw [maximalIdeal_pow_eq_span_uniformizer_pow_of_irreducible L
    (integerRingMapOfValuationExtension K L πK) hπL n]
  rw [Ideal.mem_span_singleton]
  refine ⟨integerRingMapOfValuationExtension K L r, ?_⟩
  simp [integerRingMapOfValuationExtension, hr, map_pow]

/-- The additive map on `𝓂^n` induced by base extension in an actual
unramified valuation extension. -/
def maximalIdealPowMapOfUnramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) →+ ((𝓂[L] ^ n : Ideal 𝒪[L]) : Type u) where
  toFun a :=
    ⟨integerRingMapOfValuationExtension K L (a : 𝒪[K]),
      integerRingMap_mem_maximalIdeal_pow_of_unramifiedValuation K L n a.2⟩
  map_zero' := by
    ext
    simp [integerRingMapOfValuationExtension]
  map_add' a b := by
    ext
    simp [integerRingMapOfValuationExtension]

/-- The map on maximal-ideal powers induced by an unramified extension is given by the integer-ring
inclusion. -/
@[simp]
theorem maximalIdealPowMapOfUnramifiedValuation_apply (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    (maximalIdealPowMapOfUnramifiedValuation K L n a : 𝒪[L]) =
      integerRingMapOfValuationExtension K L (a : 𝒪[K]) :=
  rfl

/-- The induced additive map on `𝓂^n/𝓂^(n+1)` in an actual unramified
valuation extension. -/
def maximalIdealPowSuccQuotMapOfUnramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) :
    MaximalIdealPowSuccQuot K n →+ MaximalIdealPowSuccQuot L n :=
  QuotientAddGroup.map
    (maximalIdealPowSuccSubmodule K n).toAddSubgroup
    (maximalIdealPowSuccSubmodule L n).toAddSubgroup
    (maximalIdealPowMapOfUnramifiedValuation K L n)
    (by
      intro a ha
      exact (mem_maximalIdealPowSuccSubmodule_iff L n
        (maximalIdealPowMapOfUnramifiedValuation K L n a)).2
        (integerRingMap_mem_maximalIdeal_pow_of_unramifiedValuation K L (n + 1)
          ((mem_maximalIdealPowSuccSubmodule_iff K n a).1 ha)))

/-- The induced map on successive maximal-ideal quotients sends a representative to its image under
the integer-ring inclusion. -/
theorem maximalIdealPowSuccQuotMapOfUnramifiedValuation_mk (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n
        (maximalIdealPowSuccQuotMk K n a) =
      maximalIdealPowSuccQuotMk L n
        (maximalIdealPowMapOfUnramifiedValuation K L n a) :=
  QuotientAddGroup.map_mk _ _ _ _ a

/-- Base extension on `𝓂^n` sends the representative `r * ϖ_K^n` to the
corresponding upstairs representative using the image of the base uniformizer. -/
theorem maximalIdealPowMapOfUnramifiedValuation_mul_uniformizer_pow
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (r : 𝒪[K]) :
    maximalIdealPowMapOfUnramifiedValuation K L n
        (maximalIdealPowMulUniformizerPowMap K (chosenIntegerRingUniformizer K)
          (chosenIntegerRingUniformizer_irreducible K) n r) =
      maximalIdealPowMulUniformizerPowMap L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L) n
        (integerRingMapOfValuationExtension K L r) := by
  ext
  simp [maximalIdealPowMulUniformizerPowMap, integerRingMapOfValuationExtension, map_pow]

/-- On `𝓂^n/𝓂^(n+1)`, base extension commutes with the representative map
`r ↦ r * ϖ_K^n` when the upstairs uniformizer is the image of `ϖ_K`. -/
theorem maximalIdealPowSuccQuotMapOfUnramifiedValuation_mul_uniformizer_pow
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (r : 𝒪[K]) :
    maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n
        (maximalIdealPowSuccQuotMulUniformizerPowMap K (chosenIntegerRingUniformizer K)
          (chosenIntegerRingUniformizer_irreducible K) n r) =
      maximalIdealPowSuccQuotMulUniformizerPowMap L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L) n
        (integerRingMapOfValuationExtension K L r) := by
  rw [maximalIdealPowSuccQuotMulUniformizerPowMap_apply,
    maximalIdealPowSuccQuotMapOfUnramifiedValuation_mk,
    maximalIdealPowSuccQuotMulUniformizerPowMap_apply]
  exact congrArg (maximalIdealPowSuccQuotMk L n)
    (maximalIdealPowMapOfUnramifiedValuation_mul_uniformizer_pow K L n r)

/-- With the upstairs uniformizer chosen as the image of the base uniformizer,
the associated-graded base-extension map is compatible with reduction on
integer-ring representatives. -/
theorem residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_map_residue
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (r : 𝒪[K]) :
    maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n
        (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible K
          (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K) n
          (IsLocalRing.residue 𝒪[K] r)) =
      residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L) n
        (residueFieldMapOfValuationExtension K L (IsLocalRing.residue 𝒪[K] r)) := by
  rw [residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_residue,
    maximalIdealPowSuccQuotMapOfUnramifiedValuation_mul_uniformizer_pow]
  rw [residueFieldMapOfValuationExtension_residue]
  rw [residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_residue]

/-- The base-uniformizer comparison `𝓀[K] ≃ 𝓂_K^n/𝓂_K^(n+1)` commutes with
base extension of residue fields in an actual unramified valuation extension.

The upstairs comparison deliberately uses `algebraMap ϖ_K` as uniformizer, not
the independently chosen canonical uniformizer of `L`; this is the twist-free
form needed before the principal-unit norm/trace calculation. -/
theorem residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_map
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (x : 𝓀[K]) :
    maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n
        (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible K
          (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K) n x) =
      residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L) n
        (residueFieldMapOfValuationExtension K L x) := by
  refine Quotient.inductionOn' x ?_
  intro r
  exact residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_map_residue K L n r

/-- In an actual unramified valuation extension, base extension sends
`U_K^n` into `U_L^n`. -/
theorem integerUnitsMapOfValuationExtension_mem_principalUnits_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) {u : 𝒪[K]ˣ} (hu : u ∈ principalUnits K n) :
    integerUnitsMapOfValuationExtension K L u ∈ principalUnits L n := by
  rw [mem_principalUnits_iff] at hu ⊢
  have hmap :=
    integerRingMap_mem_maximalIdeal_pow_of_unramifiedValuation K L n hu
  simpa [integerUnitsMapOfValuationExtension_apply, integerRingMapOfValuationExtension,
    sub_eq_add_neg] using hmap

/-- Base extension restricted to the `n`-th principal-unit group in an actual
unramified valuation extension. -/
def principalUnitsMapOfUnramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) :
    principalUnits K n →* principalUnits L n where
  toFun u :=
    ⟨integerUnitsMapOfValuationExtension K L u.1,
      integerUnitsMapOfValuationExtension_mem_principalUnits_of_unramifiedValuation
        K L n u.2⟩
  map_one' := by
    ext
    simp
  map_mul' u v := by
    ext
    simp

/-- The map on principal units for an unramified extension is induced by the integer-ring inclusion.
The map on principal units for an unramified extension is induced by the integer-ring inclusion. -/
@[simp]
theorem principalUnitsMapOfUnramifiedValuation_apply (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (u : principalUnits K n) :
    ((principalUnitsMapOfUnramifiedValuation K L n u : principalUnits L n) :
        𝒪[L]ˣ) =
      integerUnitsMapOfValuationExtension K L u.1 :=
  rfl

/-- Base extension carries the concrete unit `1 + a` to the concrete upstairs
unit `1 + algebraMap a`. -/
theorem principalUnitsMapOfUnramifiedValuation_oneAdd (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    principalUnitsMapOfUnramifiedValuation K L n
        (principalUnitOneAddOfMemPowSubgroup K hn (a : 𝒪[K]) a.2) =
      principalUnitOneAddOfMemPowSubgroup L hn
        (integerRingMapOfValuationExtension K L (a : 𝒪[K]))
        (integerRingMap_mem_maximalIdeal_pow_of_unramifiedValuation K L n a.2) := by
  ext
  simp [principalUnitsMapOfUnramifiedValuation, principalUnitOneAddOfMemPowSubgroup,
    principalUnitOneAddOfMemPow_val, integerRingMapOfValuationExtension]

/-- Base extension on successive principal-unit quotients in an actual
unramified valuation extension. -/
def principalUnitsSuccQuotMapOfUnramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) :
    PrincipalUnitsSuccQuot K n →* PrincipalUnitsSuccQuot L n :=
  principalUnitsSuccQuotLift n
    ((principalUnitsSuccQuotMk L n).comp
      (principalUnitsMapOfUnramifiedValuation K L n))
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        principalUnitsSuccQuotMk_eq_one_iff]
      change ((principalUnitsMapOfUnramifiedValuation K L n u :
        principalUnits L n) : 𝒪[L]ˣ) ∈ principalUnits L (n + 1)
      simpa [principalUnitsMapOfUnramifiedValuation_apply]
        using integerUnitsMapOfValuationExtension_mem_principalUnits_of_unramifiedValuation
          K L (n + 1) (u := u.1) hu)

/-- The induced map on successive principal-unit quotients sends a class to the class of its
included representative. -/
@[simp]
theorem principalUnitsSuccQuotMapOfUnramifiedValuation_mk (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (u : principalUnits K n) :
    principalUnitsSuccQuotMapOfUnramifiedValuation K L n
        (principalUnitsSuccQuotMk K n u) =
      principalUnitsSuccQuotMk L n
        (principalUnitsMapOfUnramifiedValuation K L n u) :=
  rfl

/-- Base extension on `𝓂^n/𝓂^(n+1)` is compatible with the comparison
`a ↦ 1 + a` to successive principal-unit quotients. -/
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_map
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (x : MaximalIdealPowSuccQuot K n) :
    principalUnitsSuccQuotMapOfUnramifiedValuation K L n
        (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x) =
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot L n hn
        (maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n x) := by
  refine MaximalIdealPowSuccQuot.inductionOn n
    (motive := fun x =>
      principalUnitsSuccQuotMapOfUnramifiedValuation K L n
          (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x) =
        principalUnitsSuccQuotOfMaximalIdealPowSuccQuot L n hn
          (maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n x))
    x ?_
  intro a
  rw [maximalIdealPowSuccQuotMapOfUnramifiedValuation_mk,
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk,
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk]
  rw [principalUnitsSuccQuotOfIdealPow_apply, principalUnitsSuccQuotOfIdealPow_apply,
    principalUnitsSuccQuotMapOfUnramifiedValuation_mk]
  congr 1
  exact principalUnitsMapOfUnramifiedValuation_oneAdd K L n hn a

/-- Additive form of compatibility between base extension and the comparison
`𝓂^n/𝓂^(n+1) ≃ U^n/U^(n+1)`. -/
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_map
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (x : MaximalIdealPowSuccQuot K n) :
    MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
        (principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn x) =
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
        (maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n x) := by
  change Additive.ofMul
      (principalUnitsSuccQuotMapOfUnramifiedValuation K L n
        (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x)) =
    Additive.ofMul
      (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot L n hn
        (maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n x))
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_map]

/-- The base-uniformizer identification `U^n/U^(n+1) ≃ 𝓀` commutes with
base extension in an actual unramified valuation extension, when the upstairs
uniformizer is chosen as the image of the base uniformizer. -/
theorem principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_map
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (x : 𝓀[K]) :
    MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
        ((principalUnitsSuccQuotAddEquivResidueOfIrreducible K
          (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K)
          n hn).symm x) =
      (principalUnitsSuccQuotAddEquivResidueOfIrreducible L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L)
        n hn).symm (residueFieldMapOfValuationExtension K L x) := by
  change MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
      (principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn
        (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible K
          (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K) n x)) =
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
      (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L)
        n (residueFieldMapOfValuationExtension K L x))
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_map]
  rw [residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_map]

/-- Base extension on successive principal-unit quotients is injective in an
actual unramified valuation extension. -/
theorem principalUnitsSuccQuotMapOfUnramifiedValuation_injective
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Function.Injective (principalUnitsSuccQuotMapOfUnramifiedValuation K L n) := by
  intro x y hxy
  let eK :=
    principalUnitsSuccQuotAddEquivResidueOfIrreducible K
      (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K) n hn
  let eL :=
    principalUnitsSuccQuotAddEquivResidueOfIrreducible L
      (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
      (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L) n hn
  let xκ : 𝓀[K] := eK (Additive.ofMul x)
  let yκ : 𝓀[K] := eK (Additive.ofMul y)
  have hxmap :
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
          (Additive.ofMul x) =
        eL.symm (residueFieldMapOfValuationExtension K L xκ) := by
    simpa [eK, eL, xκ] using
      principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_map K L n hn xκ
  have hymap :
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
          (Additive.ofMul y) =
        eL.symm (residueFieldMapOfValuationExtension K L yκ) := by
    simpa [eK, eL, yκ] using
      principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_map K L n hn yκ
  have hxyAdd :
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
          (Additive.ofMul x) =
        MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
          (Additive.ofMul y) := by
    change Additive.ofMul
        (principalUnitsSuccQuotMapOfUnramifiedValuation K L n x) =
      Additive.ofMul (principalUnitsSuccQuotMapOfUnramifiedValuation K L n y)
    exact congrArg Additive.ofMul hxy
  have hres :
      residueFieldMapOfValuationExtension K L xκ =
        residueFieldMapOfValuationExtension K L yκ :=
    eL.symm.injective (hxmap.symm.trans (hxyAdd.trans hymap))
  have hκ : xκ = yκ :=
    (RingHom.injective (residueFieldMapOfValuationExtension K L)) hres
  have hadd : Additive.ofMul x = Additive.ofMul y :=
    eK.injective (by simpa [xκ, yκ] using hκ)
  exact Additive.ofMul.injective hadd

/-- Principal-unit contraction for an actual unramified valuation extension.

If a base integer unit becomes an `n`-th principal unit upstairs, then it was
already an `n`-th principal unit downstairs. -/
theorem principalUnits_of_integerUnitsMap_mem_principalUnits_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) {a : 𝒪[K]ˣ}
    (haL : integerUnitsMapOfValuationExtension K L a ∈ principalUnits L n) :
    a ∈ principalUnits K n := by
  let xK : 𝒪[K] := (a : 𝒪[K]) - 1
  let πK : 𝒪[K] := chosenIntegerRingUniformizer K
  have hxLpow : integerRingMapOfValuationExtension K L xK ∈ (𝓂[L] ^ n : Ideal 𝒪[L]) := by
    have haLpow :=
      (mem_principalUnits_iff L (integerUnitsMapOfValuationExtension K L a) n).1 haL
    simpa [xK, integerRingMapOfValuationExtension, sub_eq_add_neg] using haLpow
  have hπL : Irreducible (integerRingMapOfValuationExtension K L πK) := by
    simpa [πK] using integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  have hvalL :
      ValuativeRel.valuation L
          ((integerRingMapOfValuationExtension K L xK : 𝒪[L]) : L) ≤
        ValuativeRel.valuation L
          ((integerRingMapOfValuationExtension K L πK : 𝒪[L]) : L) ^ n := by
    have hset := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
      (ValuativeRel.valuation L) hπL n
    exact (show integerRingMapOfValuationExtension K L xK ∈
        ({y : 𝒪[L] | ValuativeRel.valuation L (y : L) ≤
          ValuativeRel.valuation L
            ((integerRingMapOfValuationExtension K L πK : 𝒪[L]) : L) ^ n}) from by
      rw [← hset]
      exact hxLpow)
  have hvalL' :
      ValuativeRel.valuation L (algebraMap K L (xK : K)) ≤
        ValuativeRel.valuation L (algebraMap K L (((πK ^ n : 𝒪[K]) : K))) := by
    simpa [integerRingMapOfValuationExtension, map_pow] using hvalL
  have hvalKpow :
      ValuativeRel.valuation K (xK : K) ≤
        ValuativeRel.valuation K (((πK ^ n : 𝒪[K]) : K)) :=
    (Valuation.HasExtension.val_map_le_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)
      (xK : K) (((πK ^ n : 𝒪[K]) : K))).1 hvalL'
  rw [mem_principalUnits_iff]
  change xK ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
  have hsetK := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
    (ValuativeRel.valuation K) (chosenIntegerRingUniformizer_irreducible K) n
  have hvalK : xK ∈
      ({y : 𝒪[K] | ValuativeRel.valuation K (y : K) ≤
        ValuativeRel.valuation K ((πK : 𝒪[K]) : K) ^ n}) := by
    simpa [πK, map_pow] using hvalKpow
  change xK ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
  rw [hsetK]
  exact hvalK


/-- The Galois group of a finite Galois extension has cardinality equal to the field-extension
degree. -/
theorem galoisGroup_card_eq_finrank (K L : Type u)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Nat.card Gal(L/K) = Module.finrank K L :=
  IsGalois.card_aut_eq_finrank (F := K) (E := L)

/-- For an unramified extension, the residue-field automorphism group has cardinality equal to the
field-extension degree. -/
theorem residueAlgEquiv_card_eq_finrank_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) = Module.finrank K L := by
  rw [residueAlgEquiv_card_eq_finrank K L,
    LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_residue_finrank_eq_finrank K L]

/-- For an unramified Galois extension, the residue automorphism group and field Galois group have
equal cardinality. -/
theorem residueAlgEquiv_card_eq_galoisGroup_card_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) = Nat.card Gal(L/K) := by
  rw [residueAlgEquiv_card_eq_finrank_of_unramifiedValuation K L,
    galoisGroup_card_eq_finrank K L]

/-- In an actual unramified valuation extension, the integral-closure inertia
subgroup has cardinality one. -/
theorem galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_one_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Nat.card (galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L) = 1 :=
  galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_one_of_ramificationIdx_eq_one K L
    (LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_ramificationIdx_eq_one K L)

/-- In an actual unramified valuation extension, the integral-closure residue
action has kernel of cardinality one. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_one_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Nat.card (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker = 1 :=
  galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_one_of_ramificationIdx_eq_one K L
    (LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_ramificationIdx_eq_one K L)

/-- In an actual unramified valuation extension, the integral-closure residue
action is injective. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Function.Injective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L) := by
  refine (MonoidHom.ker_eq_bot_iff _).mp ?_
  exact ((galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker).eq_bot_of_card_eq
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_one_of_unramifiedValuation
      K L)

/-- In an actual unramified valuation extension, the integral-closure residue
action is surjective onto the residue-field automorphism group. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_surjective_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Function.Surjective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L) := by
  exact ((Nat.bijective_iff_injective_and_card
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L)).2
      ⟨galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation
          K L,
        (residueAlgEquiv_card_eq_galoisGroup_card_of_unramifiedValuation K L).symm⟩).2

/-- In an actual unramified valuation extension, the integral-closure residue
action is bijective. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Function.Bijective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L) :=
  ⟨galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation K L,
    galoisGroupResidueAlgEquivHomOfIsIntegralClosure_surjective_of_unramifiedValuation K L⟩

/-- The actual integral-closure residue action as an isomorphism in the
unramified valuation case. -/
noncomputable def galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Gal(L/K) ≃* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
  MulEquiv.ofBijective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L)
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation K L)

/-- The unramified Galois-to-residue equivalence sends an automorphism to its induced action on
residue classes. -/
@[simp]
theorem galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_apply
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (σ : Gal(L/K)) :
    galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L σ =
      galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ :=
  rfl

/-- In the unramified valuation case, products over the actual
integral-closure real Galois residue action can be reindexed as products over
the full residue-field automorphism group. -/
theorem galoisGroupResidueAlgEquivOfIsIntegralClosure_prod_eq_prod_algEquiv_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (u : 𝓀[L]ˣ) :
    Finset.univ.prod (fun σ : Gal(L/K) =>
      Units.mapEquiv
        (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ).toMulEquiv u) =
    Finset.univ.prod (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
      Units.mapEquiv τ.toMulEquiv u) :=
  Fintype.prod_equiv
    (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).toEquiv
    (fun σ : Gal(L/K) =>
      Units.mapEquiv
        (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ).toMulEquiv u)
    (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] => Units.mapEquiv τ.toMulEquiv u)
    (by intro σ; rfl)

/-- In the unramified valuation case, sums over the actual integral-closure
real Galois residue action can be reindexed as sums over the full residue-field
automorphism group. -/
theorem galoisGroupResidueAlgEquivOfIsIntegralClosure_sum_eq_sum_algEquiv_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : 𝓀[L]) :
    Finset.univ.sum (fun σ : Gal(L/K) =>
      galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ x) =
    Finset.univ.sum (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] => τ x) :=
  Fintype.sum_equiv
    (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).toEquiv
    (fun σ : Gal(L/K) => galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ x)
    (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] => τ x)
    (by intro σ; rfl)

/-- In the unramified valuation case, reducing the actual integral-closure
Galois sum gives the base extension of the finite residue-field trace. -/
theorem galoisGroup_sum_residue_eq_algebraMap_trace_of_unramifiedValuation_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (a : 𝒪[L]) :
    IsLocalRing.residue 𝒪[L]
        (Finset.univ.sum fun σ : Gal(L/K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ a) =
      algebraMap 𝓀[K] 𝓀[L]
        (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] a)) := by
  rw [galoisGroup_sum_residue_eq_residueAlgEquiv_sum_of_isIntegralClosure K L a]
  rw [galoisGroupResidueAlgEquivOfIsIntegralClosure_sum_eq_sum_algEquiv_of_unramifiedValuation
    K L]
  exact (trace_eq_sum_automorphisms
    (K := 𝓀[K]) (L := 𝓀[L]) (IsLocalRing.residue 𝒪[L] a)).symm

/-- Actual integral-closure version of the base-uniformizer coefficient
calculation for the real Galois sum. -/
theorem galoisGroup_sum_mul_base_uniformizer_pow_eq_coeff_sum_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (r : 𝒪[L]) :
    let πL := integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
    Finset.univ.sum (fun σ : Gal(L/K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (r * πL ^ n)) =
      (Finset.univ.sum fun σ : Gal(L/K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) * πL ^ n := by
  intro πL
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [map_mul, map_pow]
  change galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r *
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))) ^ n =
    galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r * πL ^ n
  rw [galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap]

/-- On the associated graded piece defined by the base uniformizer, the
coefficient of the Galois sum is the finite residue-field trace. -/
theorem galoisSum_uniformizerGraded_eq_residueTrace
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (r : 𝒪[L]) :
    let πL := integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
    let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
    maximalIdealPowSuccQuotMulUniformizerPowMap L πL hπL n
        (Finset.univ.sum fun σ : Gal(L/K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) =
      residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L πL hπL n
        (algebraMap 𝓀[K] 𝓀[L]
          (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))) := by
  intro πL hπL
  rw [← residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_residue L πL hπL n
    (Finset.univ.sum fun σ : Gal(L/K) =>
      galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r)]
  rw [galoisGroup_sum_residue_eq_algebraMap_trace_of_unramifiedValuation_of_isIntegralClosure
    K L r]

end
end LocalFieldTheory
