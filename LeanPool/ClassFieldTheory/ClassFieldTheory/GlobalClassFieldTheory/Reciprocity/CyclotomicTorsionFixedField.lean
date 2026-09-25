/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicTorsionField
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicCharacterEquiv
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Basic
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Local
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FiniteFree
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Gather
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Swap
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Decomposition
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.DenseTorsion
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientEquiv
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientMk
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.CyclotomicQuotient
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FreeCoordinate
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FiniteOrder
/-!
# The cyclotomic torsion fixed field

`rationalCyclotomicField` now denotes the actual field `ℚ(μ∞)` inside
`SeparableClosure ℚ`.  Its actual Galois group is therefore the standard
mathlib type
`rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField`; its finite
cyclotomic levels form a divisibility-directed system with supremum the
whole field.  The torsion fixed field is the actual
intermediate field `rationalCyclotomicTorsionFixedField`.

The actual continuous cyclotomic character identifies the full Galois
group with `ℤ̂ˣ`.  Applying infinite Galois correspondence to the actual
torsion closure and the group-theoretic decomposition of `ℤ̂ˣ` gives the
cyclotomic `ℤ̂`-extension.
-/

@[expose] public section

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  continuousMulEquivOfCompactToT2 →
    continuousMulEquivOfCompactToT2


noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped IsMulCommutative
open KummerTheory
open ClassFormation

private noncomputable def rationalCyclotomicTorsionRestrictionEquiv :
    (rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField) ⧸
        rationalCyclotomicTorsionClosure.toSubgroup ≃ₜ*
      (rationalCyclotomicTorsionFixedField ≃ₐ[ℚ]
        rationalCyclotomicTorsionFixedField) := by
  let _ : T2Space
      (rationalCyclotomicTorsionFixedField ≃ₐ[ℚ]
        rationalCyclotomicTorsionFixedField) :=
    krullTopology_t2
  exact
    continuousMulEquivOfCompactToT2
      (InfiniteGalois.normalAutEquivQuotient
        (k := ℚ) (K := rationalCyclotomicField)
        rationalCyclotomicTorsionClosure)
      (by
        rw [←
          QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
        exact
          InfiniteGalois.restrictNormalHom_continuous
            rationalCyclotomicTorsionFixedField)

/-- The Galois group of the actual torsion fixed field in
`ℚ(μ∞)` is the additive group of the profinite integers, written
multiplicatively. -/
noncomputable def rationalCyclotomicTorsionFixedFieldGalEquivZHat :
    (rationalCyclotomicTorsionFixedField ≃ₐ[ℚ]
      rationalCyclotomicTorsionFixedField) ≃ₜ*
        Multiplicative ZHat := by
  exact rationalCyclotomicTorsionRestrictionEquiv.symm.trans <|
    torsionQuotientEquivOfZHatMulDecomposition
      (rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField)
      CyclotomicFinitePart
      (rationalCyclotomicCharacterContinuousMulEquiv.trans
        zHatUnitsDecomposition)
      dense_torsion_cyclotomicFinitePart

private theorem rationalCyclotomicTorsionRestrictionEquiv_apply_mk
    (σ :
      rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField) :
    rationalCyclotomicTorsionRestrictionEquiv
        (QuotientGroup.mk σ) =
      AlgEquiv.restrictNormalHom
        rationalCyclotomicTorsionFixedField σ := by
  exact
    InfiniteGalois.normalAutEquivQuotient_apply
      rationalCyclotomicTorsionClosure σ

private theorem rationalCyclotomicTorsionRestrictionEquiv_symm_restrictNormal
    (σ :
      rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField) :
    rationalCyclotomicTorsionRestrictionEquiv.symm
        (AlgEquiv.restrictNormalHom
          rationalCyclotomicTorsionFixedField σ) =
      QuotientGroup.mk σ := by
  apply rationalCyclotomicTorsionRestrictionEquiv.symm_apply_eq.mpr
  exact (rationalCyclotomicTorsionRestrictionEquiv_apply_mk σ).symm

private theorem rationalCyclotomicTorsionCoordinate_restrictNormal
    (σ :
      rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField) :
    torsionQuotientEquivOfZHatMulDecomposition
        (rationalCyclotomicField ≃ₐ[ℚ]
          rationalCyclotomicField)
        CyclotomicFinitePart
        (rationalCyclotomicCharacterContinuousMulEquiv.trans
          zHatUnitsDecomposition)
        dense_torsion_cyclotomicFinitePart
        (rationalCyclotomicTorsionRestrictionEquiv.symm
          (AlgEquiv.restrictNormalHom
            rationalCyclotomicTorsionFixedField σ)) =
      (zHatUnitsDecomposition
        (rationalCyclotomicCharacterContinuousMulEquiv σ)).1 := by
  rw [rationalCyclotomicTorsionRestrictionEquiv_symm_restrictNormal]
  exact
    torsionQuotientEquivOfZHatMulDecomposition_mk
      (rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField)
      CyclotomicFinitePart
      (rationalCyclotomicCharacterContinuousMulEquiv.trans
        zHatUnitsDecomposition)
      dense_torsion_cyclotomicFinitePart σ

/-- Restriction of an actual automorphism of the full rational
cyclotomic field to the torsion fixed field is sent to the genuine
torsion-free coordinate of its cyclotomic character. -/
@[simp]
theorem
    rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal
    (σ :
      rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField) :
    rationalCyclotomicTorsionFixedFieldGalEquivZHat
        (AlgEquiv.restrictNormalHom
          rationalCyclotomicTorsionFixedField σ) =
      (zHatUnitsDecomposition
        (rationalCyclotomicCharacterContinuousMulEquiv σ)).1 := by
  change
    torsionQuotientEquivOfZHatMulDecomposition
        (rationalCyclotomicField ≃ₐ[ℚ]
          rationalCyclotomicField)
        CyclotomicFinitePart
        (rationalCyclotomicCharacterContinuousMulEquiv.trans
          zHatUnitsDecomposition)
        dense_torsion_cyclotomicFinitePart
        (rationalCyclotomicTorsionRestrictionEquiv.symm
          (AlgEquiv.restrictNormalHom
            rationalCyclotomicTorsionFixedField σ)) =
      (zHatUnitsDecomposition
        (rationalCyclotomicCharacterContinuousMulEquiv σ)).1
  exact rationalCyclotomicTorsionCoordinate_restrictNormal σ

end Reciprocity
end GlobalClassFieldTheory
