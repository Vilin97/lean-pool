/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.NormSide
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Trace
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Lift
/-! Provides the public declarations in the
  `LocalClassFieldTheory.Finite.Unramified.ResidueNorm` Lean module. -/

noncomputable section

universe u

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The integral-closure quotient norm on first
principal-unit quotients in an unramified valuation extension.  This is the
the unramified norm calculation residue-unit quotient before the later `U^1` lifting. -/
noncomputable def integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    IntegerUnitsModPrincipalUnits L →* IntegerUnitsModPrincipalUnits K :=
  integerUnitsModPrincipalUnitsLift
    ((integerUnitsModPrincipalUnitsMk K).comp (normIntegerUnits K L))
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        IntegerUnitsModPrincipalUnits_mk_eq_one_iff]
      exact normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure
        K L 1 u hu)

/-- States the theorem `integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk`. -/
@[simp]
theorem integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (u : 𝒪[L]ˣ) :
    integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L
        (integerUnitsModPrincipalUnitsMk L u) =
      integerUnitsModPrincipalUnitsMk K (normIntegerUnits K L u) :=
  integerUnitsModPrincipalUnitsLift_mk
    ((integerUnitsModPrincipalUnitsMk K).comp (normIntegerUnits K L)) _ u

/-- After extending the residue of the integer-unit norm back to `𝓀[L]`, it
is the product of the integral-closure residue actions. -/
theorem residueUnitsMap_normIntegerUnits_eq_galoisGroup_residue_prod_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (u : 𝒪[L]ˣ) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsToResidueUnits K (normIntegerUnits K L u)) =
      Finset.univ.prod (fun σ : Gal(L/K) =>
        Units.mapEquiv
          (galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ).toMulEquiv
          (integerUnitsToResidueUnits L u)) := by
  rw [residueUnitsMap_integerUnitsToResidueUnits K L (normIntegerUnits K L u)]
  rw [integerUnitsMap_normIntegerUnits_eq_galoisGroup_prod_of_isIntegralClosure K L u]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro σ _
  exact
    (galoisGroupResidueFieldEquivOfIsIntegralClosure_integerUnitsToResidueUnits
      K L σ u).symm

/-- AlgEquiv-typed form of
`residueUnitsMap_normIntegerUnits_eq_galoisGroup_residue_prod_of_isIntegralClosure`. -/
theorem residueUnitsMap_normIntegerUnits_eq_galoisGroup_residue_algEquiv_prod_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (u : 𝒪[L]ˣ) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsToResidueUnits K (normIntegerUnits K L u)) =
      Finset.univ.prod (fun σ : Gal(L/K) =>
        Units.mapEquiv
          (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ).toMulEquiv
          (integerUnitsToResidueUnits L u)) := by
  rw [residueUnitsMap_normIntegerUnits_eq_galoisGroup_residue_prod_of_isIntegralClosure
    K L u]
  apply Finset.prod_congr rfl
  intro σ _
  apply Units.ext
  rfl

/-- Quotient-level form of the residue product formula for the
integer-unit norm. -/
theorem integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_residue_algEquiv_base_extend
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : IntegerUnitsModPrincipalUnits L) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsEquivResidueUnits K
          (integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L x)) =
      Finset.univ.prod (fun σ : Gal(L/K) =>
        Units.mapEquiv
          (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ).toMulEquiv
          (integerUnitsModPrincipalUnitsEquivResidueUnits L x)) := by
  refine IntegerUnitsModPrincipalUnits.inductionOn
    (motive := fun x =>
      residueUnitsMapOfValuationExtension K L
          (integerUnitsModPrincipalUnitsEquivResidueUnits K
            (integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L x)) =
        Finset.univ.prod (fun σ : Gal(L/K) =>
          Units.mapEquiv
            (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ).toMulEquiv
            (integerUnitsModPrincipalUnitsEquivResidueUnits L x)))
    x ?_
  intro u
  rw [integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk]
  rw [integerUnitsModPrincipalUnitsEquivResidueUnits_mk]
  rw [integerUnitsModPrincipalUnitsEquivResidueUnits_mk]
  exact
    residueUnitsMap_normIntegerUnits_eq_galoisGroup_residue_algEquiv_prod_of_isIntegralClosure
      K L u

/-- In the unramified valuation case, the integral-closure quotient norm
agrees after base extension with the quotient-level finite residue norm model. -/
theorem
  integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_residue_base_extend_eq_residueNorm
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : IntegerUnitsModPrincipalUnits L) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsEquivResidueUnits K
          (integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L x)) =
      residueUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsEquivResidueUnits K
          (integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L x)) := by
  rw [integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_residue_algEquiv_base_extend]
  rw [integerUnitsModPrincipalUnitsResidueNorm_base_extend_eq_prod_algEquiv]
  exact
    galoisGroupResidueAlgEquivOfIsIntegralClosure_prod_eq_prod_algEquiv_of_unramifiedValuation
      K L (integerUnitsModPrincipalUnitsEquivResidueUnits L x)

/-- In the unramified valuation case, the actual integral-closure quotient norm
on `𝒪[L]ˣ/U_L¹` is the quotient-level finite-field residue norm model. -/
theorem
  integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_eq_residueNorm_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L =
      integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L := by
  apply MonoidHom.ext
  intro x
  apply (integerUnitsModPrincipalUnitsEquivResidueUnits K).injective
  apply residueUnitsMapOfValuationExtension_injective K L
  exact
    integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_residue_base_extend_eq_residueNorm
      K L x

/-- The actual integral-closure quotient norm on `𝒪[L]ˣ/U_L¹` is surjective in
the unramified valuation case. -/
theorem
  integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_surjective_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Function.Surjective
      (integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L) := by
  rw [integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_eq_residueNorm_of_unramifiedValuation
    K L]
  exact integerUnitsModPrincipalUnitsResidueNorm_surjective_of_valuationExtension K L

end LocalClassFieldTheory
