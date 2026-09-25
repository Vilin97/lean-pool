/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.Basic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Basic
/-! Provides the public declarations in the
  `LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Trace` Lean module. -/

@[expose] public section

noncomputable section

universe u

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open Filter

namespace UnramifiedPrincipalUnits

/-- For the integral-closure base-uniformizer representative
`1 + rϖ_L^n`, the norm after base extension back to `L` is residue trace on
the associated graded quotient. -/
theorem quotientNorm_oneAdd_uniformizerPow_eq_trace
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (r : 𝒪[L]) :
    let πL := integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
    let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
    let a : (𝓂[L] ^ n : Ideal 𝒪[L]) :=
      maximalIdealPowMulUniformizerPowMap L πL hπL n r
    Additive.ofMul
        (principalUnitsSuccQuotMapOfUnramifiedValuation K L n
          (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
            (principalUnitsSuccQuotMk L n
              (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)))) =
      (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn).symm
        (algebraMap 𝓀[K] 𝓀[L]
          (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))) := by
  classical
  intro πL hπL a
  let b : (𝓂[L] ^ n : Ideal 𝒪[L]) :=
    ⟨Finset.univ.sum fun σ : Gal(L/K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L]),
      by
        exact Ideal.sum_mem _ fun σ _ =>
          (integerRingEquiv_mem_maximalIdeal_pow L
            (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) n
            (a : 𝒪[L])).2 a.2⟩
  have hnorm :=
    principalUnitsSuccQuotMap_normOfUnramifiedValuationOfIsIntegralClosure_oneAdd_base_eq_sum
      K L n hn a
  change Additive.ofMul
      (principalUnitsSuccQuotMapOfUnramifiedValuation K L n
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
          (principalUnitsSuccQuotMk L n
            (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)))) =
    (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn).symm
      (algebraMap 𝓀[K] 𝓀[L]
        (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r)))
  rw [hnorm]
  rw [principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_apply]
  change Additive.ofMul (principalUnitsSuccQuotOfIdealPow L n hn b) =
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
      (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L πL hπL n
        (algebraMap 𝓀[K] 𝓀[L]
          (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))))
  rw [← principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk L n hn b]
  change principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
      (maximalIdealPowSuccQuotMk L n b) =
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
      (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L πL hπL n
        (algebraMap 𝓀[K] 𝓀[L]
          (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))))
  congr 1
  have hb_eq :
      (b : 𝒪[L]) =
        (Finset.univ.sum fun σ : Gal(L/K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) * πL ^ n := by
    simpa [b, a, πL] using
      galoisGroup_sum_mul_base_uniformizer_pow_eq_coeff_sum_of_isIntegralClosure K L n r
  rw [show maximalIdealPowSuccQuotMk L n b =
      maximalIdealPowSuccQuotMulUniformizerPowMap L πL hπL n
        (Finset.univ.sum fun σ : Gal(L/K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) by
    rw [maximalIdealPowSuccQuotMulUniformizerPowMap_apply]
    apply congrArg (maximalIdealPowSuccQuotMk L n)
    apply Subtype.ext
    calc
      (b : 𝒪[L]) = (Finset.univ.sum fun σ : Gal(L/K) =>
            galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) * πL ^ n := hb_eq
      _ =
          ((maximalIdealPowMulUniformizerPowMap L πL hπL n
            (Finset.univ.sum fun σ : Gal(L/K) =>
              galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) :
            (𝓂[L] ^ n : Ideal 𝒪[L])) : 𝒪[L]) := by
        rw [maximalIdealPowMulUniformizerPowMap_apply]]
  exact
    galoisSum_uniformizerGraded_eq_residueTrace
      K L n r

end UnramifiedPrincipalUnits

/-- Actual integral-closure version: for the base-uniformizer representative
`1 + rϖ_L^n`, the norm on `U_L^n/U_L^(n+1)` is the residue-field trace class
on `U_K^n/U_K^(n+1)`. -/
theorem
  principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_oneAdd_uniformizer_pow_eq_trace
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (r : 𝒪[L]) :
    let πK := chosenIntegerRingUniformizer K
    let πL := integerRingMapOfValuationExtension K L πK
    let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
    let a : (𝓂[L] ^ n : Ideal 𝒪[L]) :=
      maximalIdealPowMulUniformizerPowMap L πL hπL n r
    Additive.ofMul
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
          (principalUnitsSuccQuotMk L n
            (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2))) =
      (principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
        (chosenIntegerRingUniformizer_irreducible K) n hn).symm
        (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r)) := by
  classical
  intro πK πL hπL a
  let x :=
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
      (principalUnitsSuccQuotMk L n
        (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2))
  let y :=
    (principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
      (chosenIntegerRingUniformizer_irreducible K) n hn).symm
      (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))
  have hxmap :
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
          (Additive.ofMul x) =
        (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn).symm
          (algebraMap 𝓀[K] 𝓀[L]
            (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))) := by
    simpa [x, πK, πL, hπL, a] using
    UnramifiedPrincipalUnits.quotientNorm_oneAdd_uniformizerPow_eq_trace
        K L n hn r
  have hymap :
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n) y =
        (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn).symm
          (algebraMap 𝓀[K] 𝓀[L]
            (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))) := by
    simpa [y, πK, πL, hπL, residueFieldMapOfValuationExtension_eq_algebraMap] using
      principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_map K L n hn
        (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))
  have hmul : x = Additive.toMul y := by
    apply principalUnitsSuccQuotMapOfUnramifiedValuation_injective K L n hn
    apply Additive.ofMul.injective
    change MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
        (Additive.ofMul x) =
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n) y
    exact hxmap.trans hymap.symm
  change Additive.ofMul x = y
  simpa using congrArg Additive.ofMul hmul

/-- Actual integral-closure version: in residue coordinates, the norm on the
successive principal-unit quotient is the finite residue-field trace. -/
theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_trace_coord
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (x : 𝓀[L]) :
    let πK := chosenIntegerRingUniformizer K
    let πL := integerRingMapOfValuationExtension K L πK
    let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
    let eK := principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
      (chosenIntegerRingUniformizer_irreducible K) n hn
    let eL := principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn
    MonoidHom.toAdditive
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n)
        (eL.symm x) =
      eK.symm (Algebra.trace 𝓀[K] 𝓀[L] x) := by
  classical
  intro πK πL hπL eK eL
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  have hrep :=
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_oneAdd_uniformizer_pow_eq_trace
      K L n hn r
  rw [principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_residue]
  change Additive.ofMul _ = _
  simpa only [eK, eL, πK, πL, hπL, toMul_ofMul] using hrep

/-- The residue-trace model for the actual unramified norm on
`U^n/U^(n+1)`, written in the base-uniformizer coordinates. -/
noncomputable def principalUnitsSuccQuotTraceOfUnramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Additive (PrincipalUnitsSuccQuot L n) →+ Additive (PrincipalUnitsSuccQuot K n) :=
  let πK := chosenIntegerRingUniformizer K
  let πL := integerRingMapOfValuationExtension K L πK
  let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  ((principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
    (chosenIntegerRingUniformizer_irreducible K) n hn).symm.toAddMonoidHom).comp
    ((Algebra.trace 𝓀[K] 𝓀[L]).toAddMonoidHom.comp
      (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn).toAddMonoidHom)

/-- States the theorem `principalUnitsSuccQuotTraceOfUnramifiedValuation_apply`. -/
theorem principalUnitsSuccQuotTraceOfUnramifiedValuation_apply
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (x : Additive (PrincipalUnitsSuccQuot L n)) :
    let πK := chosenIntegerRingUniformizer K
    let πL := integerRingMapOfValuationExtension K L πK
    let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
    principalUnitsSuccQuotTraceOfUnramifiedValuation K L n hn x =
      (principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
        (chosenIntegerRingUniformizer_irreducible K) n hn).symm
        (Algebra.trace 𝓀[K] 𝓀[L]
          (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn x)) :=
  rfl

/-- The residue-trace model on successive principal-unit quotients is
surjective in the unramified valuation case. -/
theorem principalUnitsSuccQuotTraceOfUnramifiedValuation_surjective
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Function.Surjective (principalUnitsSuccQuotTraceOfUnramifiedValuation K L n hn) := by
  classical
  intro y
  let πK := chosenIntegerRingUniformizer K
  let πL := integerRingMapOfValuationExtension K L πK
  let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  let eK := principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
    (chosenIntegerRingUniformizer_irreducible K) n hn
  let eL := principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn
  obtain ⟨x, hx⟩ :=
    residueField_trace_surjective_of_valuationExtension K L (eK y)
  refine ⟨eL.symm x, ?_⟩
  change
    (((eK.symm.toAddMonoidHom).comp
      ((Algebra.trace 𝓀[K] 𝓀[L]).toAddMonoidHom.comp eL.toAddMonoidHom))
      (eL.symm x)) = y
  simp [hx]

/-- Actual integral-closure version: the unramified norm on every successive
principal-unit quotient is the finite residue-field trace in base-uniformizer
coordinates. -/
theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_eq_trace
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    MonoidHom.toAdditive
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n) =
      principalUnitsSuccQuotTraceOfUnramifiedValuation K L n hn := by
  apply AddMonoidHom.ext
  intro x
  let πK := chosenIntegerRingUniformizer K
  let πL := integerRingMapOfValuationExtension K L πK
  let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  let eL := principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn
  have hcoord :=
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_trace_coord
      K L n hn (eL x)
  simpa [principalUnitsSuccQuotTraceOfUnramifiedValuation, πK, πL, hπL, eL]
    using hcoord

/-- Actual integral-closure version: on every successive principal-unit
quotient, the unramified norm is surjective after writing the quotient
additively. -/
theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_toAdditive_surjective
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Function.Surjective
      (MonoidHom.toAdditive
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n)) := by
  rw [principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_eq_trace
    K L n hn]
  exact principalUnitsSuccQuotTraceOfUnramifiedValuation_surjective K L n hn

/-- Actual integral-closure version: on every successive principal-unit
quotient, the unramified norm is surjective. -/
theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_surjective
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Function.Surjective
      (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n) := by
  intro y
  obtain ⟨x, hx⟩ :=
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_toAdditive_surjective
      K L n hn (Additive.ofMul y)
  refine ⟨Additive.toMul x, ?_⟩
  apply Additive.ofMul.injective
  change MonoidHom.toAdditive
      (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n)
      (Additive.ofMul (Additive.toMul x)) = Additive.ofMul y
  simpa using hx

end LocalClassFieldTheory
