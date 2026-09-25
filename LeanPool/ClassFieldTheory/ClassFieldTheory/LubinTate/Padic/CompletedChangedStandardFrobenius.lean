/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardResidue
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedResidueFrobenius
/-!
# Frobenius orientation in the completed standard/changed compositum

The finite standard/changed compositum is unramified over the completed
changed-uniformizer fixed field.  Its explicit relative Artin candidate is
the restriction of inverse completed coefficient Frobenius.

Both automorphisms can be compared faithfully on residue fields.  Completed
coefficient Frobenius and relative residue arithmetic Frobenius are the same
`p`-power map, so the explicit candidate is the inverse of the actual
arithmetic Frobenius of the finite unramified extension.
-/

@[expose] public section

noncomputable section

namespace LubinTate

open scoped ValuativeRel

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The explicit changed-uniformizer relative Artin candidate is the
inverse of the actual arithmetic Frobenius of the unramified finite
standard/changed compositum. -/
theorem
    padicCompletedChangedUniformizerRelativeArtinCandidate_eq_inverseArithmeticFrobenius
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let D := padicCompletedChangedUniformizerFixedField p u n
    let M := padicCompletedStandardChangedCompositum p u n
    let : FiniteDimensional D M :=
      FiniteDimensional.right ℚ_[p] D M
    let : IsGalois D M :=
      IsGalois.tower_top_of_isGalois ℚ_[p] D M
    letI : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField ℚ_[p] D
    letI : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel ℚ_[p] D
    let : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
    letI : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField ℚ_[p] M
    letI : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel ℚ_[p] M
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
    let :
        Valuation.HasExtension (ValuativeRel.valuation D)
          (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension_of_tower
        ℚ_[p] D M
    let :
        Module.Finite
          (ValuativeRel.valuation D).integer
          (ValuativeRel.valuation M).integer :=
      integerRing_moduleFinite_of_finite_separable D M
    let :
        IsIntegralClosure
          (ValuativeRel.valuation M).integer
          (ValuativeRel.valuation D).integer M :=
      padicCompletedStandardChangedCompositum_integerRing_isIntegralClosure
        p u n
    let :
        IsNonarchimedeanLocalField.IsUnramifiedValuedExtension D M :=
      padicCompletedStandardChangedCompositum_isUnramifiedValuedExtension
        p u n
    padicCompletedChangedUniformizerRelativeArtinCandidate p u n =
      (arithmeticFrobeniusOfUnramifiedValuation D M)⁻¹ := by
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let : FiniteDimensional D M :=
    FiniteDimensional.right ℚ_[p] D M
  let : IsGalois D M :=
    IsGalois.tower_top_of_isGalois ℚ_[p] D M
  let : NontriviallyNormedField D :=
    finiteExtensionSpectralNormedField ℚ_[p] D
  let : ValuativeRel D :=
    finiteExtensionSpectralValuativeRel ℚ_[p] D
  let : IsNonarchimedeanLocalField D :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
  let : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField ℚ_[p] M
  let : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel ℚ_[p] M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
  let :
      Valuation.HasExtension (ValuativeRel.valuation D)
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension_of_tower
      ℚ_[p] D M
  let :
      Module.Finite
        (ValuativeRel.valuation D).integer
        (ValuativeRel.valuation M).integer :=
    integerRing_moduleFinite_of_finite_separable D M
  let :
      IsIntegralClosure
        (ValuativeRel.valuation M).integer
        (ValuativeRel.valuation D).integer M :=
    padicCompletedStandardChangedCompositum_integerRing_isIntegralClosure
      p u n
  let :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension D M :=
    padicCompletedStandardChangedCompositum_isUnramifiedValuedExtension
      p u n
  have hM :
      IsLocalRing.ResidueField
          (localCompleteDVF M).valuation.valuationSubring =
        𝓀[M] := by
    rw [localCompleteDVF_valuation_eq M]
    rfl
  have hD :
      IsLocalRing.ResidueField
          (localCompleteDVF D).valuation.valuationSubring =
        𝓀[D] := by
    rw [localCompleteDVF_valuation_eq D]
    rfl
  cases hM
  cases hD
  apply
    galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation
      D M
  calc
    galoisGroupResidueAlgEquivHomOfIsIntegralClosure D M
        (padicCompletedChangedUniformizerRelativeArtinCandidate p u n) =
      (residueExtensionArithmeticFrobeniusOfValuationExtension D M)⁻¹ := by
        apply AlgEquiv.ext
        intro a
        rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_apply D M]
        let embedding :=
          padicCompletedStandardChangedCompositumResidueEmbedding p u n
        let completedFrobenius :=
          IsLocalRing.ResidueField.mapEquiv
            (padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹)
        let x :
            IsLocalRing.ResidueField
              (localCompleteDVF M).valuation.valuationSubring :=
          (residueExtensionArithmeticFrobeniusOfValuationExtension D M)⁻¹ a
        apply embedding.injective
        change
          embedding
              (galoisGroupResidueFieldEquivOfIsIntegralClosure
                D M
                (padicCompletedChangedUniformizerRelativeArtinCandidate
                  p u n) a) =
            embedding x
        rw [show
          embedding
              (galoisGroupResidueFieldEquivOfIsIntegralClosure
                D M
                (padicCompletedChangedUniformizerRelativeArtinCandidate
                  p u n) a) =
            IsLocalRing.ResidueField.mapEquiv
                (padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹).symm
              (embedding a) by
            simpa only [localCompleteDVF_valuation_eq] using
              padicCompletedStandardChangedCompositumResidueEmbedding_artinCandidate
                p u n a]
        apply completedFrobenius.symm_apply_eq.2
        symm
        calc
          completedFrobenius (embedding x) = embedding x ^ p := by
            exact
              padicCompletedUnitFrobeniusIntegerEquiv_residue_apply_eq_pow
                p n u⁻¹ (embedding x)
          _ = embedding (x ^ p) := (embedding.map_pow x p).symm
          _ =
              embedding
                (residueExtensionArithmeticFrobeniusOfValuationExtension D M x) := by
            congr 1
            exact
              (padicCompletedStandardChangedCompositum_residueArithmeticFrobenius_apply
                p u n x).symm
          _ = embedding a := by
            exact congrArg embedding
              ((residueExtensionArithmeticFrobeniusOfValuationExtension
                D M).apply_symm_apply a)
    _ =
        (galoisGroupResidueAlgEquivHomOfIsIntegralClosure D M
          (arithmeticFrobeniusOfUnramifiedValuation D M))⁻¹ := by
      apply congrArg (fun σ => σ⁻¹)
      simpa only [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_apply] using
        (galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius D M).symm

end LubinTate

end
