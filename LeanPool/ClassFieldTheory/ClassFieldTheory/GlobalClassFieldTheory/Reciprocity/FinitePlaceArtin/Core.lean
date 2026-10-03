/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlace
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Conjugation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.TowerRestriction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.CrossLocalRestriction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.NormRestriction
/-!
# Image and kernel of finite-place Artin homomorphisms

This module identifies the image with the chosen decomposition group and the kernel with the
  chosen local norm subgroup.
-/

@[expose] public section

open scoped IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

open scoped Classical in
/-- The image of the chosen finite-place Artin homomorphism is exactly
the chosen decomposition group. -/
theorem chosenFinitePlaceArtinMonoidHom_range
    (v : HeightOneSpectrum (𝓞 K)) :
    (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v).range =
      finitePlaceDecompositionGroup
        (K := K) (L := L) v := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w :=
    chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
  let :=
    LocalClassFieldTheory.localizedCompletionIsScalarTower vK w
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
  let : IsAbelianGalois vK.Completion E :=
    LocalClassFieldTheory.localizedCompletion_isAbelianGalois
      vK hvK w
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtensionCompletionNontriviallyNormedField
      vK hvK
  let : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let : IsUltrametricDist vK.Completion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
        vK
        (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
          K v))
  let : Valued vK.Completion ℝ≥0 :=
    NormedField.toValued
  let vC : Valuation vK.Completion ℝ≥0 :=
    Valued.v
  let : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vK.Completion)).IsNontrivial)
  let : ValuativeRel vK.Completion :=
    ValuativeRel.ofValuation vC
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let : ValuativeRel.IsNontrivial vK.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
      inferInstance
  let : IsValuativeTopology vK.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vK.Completion ℝ≥0
  let : IsNonarchimedeanLocalField vK.Completion :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let eD :
      absoluteValueDecompositionGroup K w.1 ≃*
        (E ≃ₐ[vK.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let eK :
      vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  have hsurjective :
      Function.Surjective
        (eD.symm.toMonoidHom.comp
          ((LocalClassFieldTheory.abelianLocalArtinMonoidHom
            vK.Completion E).comp
              eK.symm.toMonoidHom)) :=
    eD.symm.surjective.comp
      ((LocalClassFieldTheory.abelianLocalArtinMonoidHom_surjective
          vK.Completion E).comp
        eK.symm.surjective)
  change
    MonoidHom.range
        ((absoluteValueDecompositionGroup K w.1).subtype.comp
          (eD.symm.toMonoidHom.comp
            ((LocalClassFieldTheory.abelianLocalArtinMonoidHom
              vK.Completion E).comp
                eK.symm.toMonoidHom))) =
      absoluteValueDecompositionGroup K w.1
  rw [
    MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr hsurjective,
    ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

open scoped Classical in
/-- The kernel of the concrete finite-place Artin homomorphism is
exactly the chosen local norm subgroup. -/
theorem chosenFinitePlaceArtinMonoidHom_ker
    (v : HeightOneSpectrum (𝓞 K)) :
    MonoidHom.ker
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v) =
      chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w :=
    chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
  let :=
    LocalClassFieldTheory.localizedCompletionIsScalarTower vK w
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
  let : IsAbelianGalois vK.Completion E :=
    LocalClassFieldTheory.localizedCompletion_isAbelianGalois
      vK hvK w
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtensionCompletionNontriviallyNormedField
      vK hvK
  let : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let : IsUltrametricDist vK.Completion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
        vK
        (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
          K v))
  let : Valued vK.Completion ℝ≥0 :=
    NormedField.toValued
  let vC : Valuation vK.Completion ℝ≥0 :=
    Valued.v
  let : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vK.Completion)).IsNontrivial)
  let : ValuativeRel vK.Completion :=
    ValuativeRel.ofValuation vC
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let : ValuativeRel.IsNontrivial vK.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
      inferInstance
  let : IsValuativeTopology vK.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vK.Completion ℝ≥0
  let : IsNonarchimedeanLocalField vK.Completion :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let eD :
      absoluteValueDecompositionGroup K w.1 ≃*
        (E ≃ₐ[vK.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let eK :
      vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  let localArtin :=
    LocalClassFieldTheory.abelianLocalArtinMonoidHom
      vK.Completion E
  change
    MonoidHom.ker
        ((absoluteValueDecompositionGroup K w.1).subtype.comp
          (eD.symm.toMonoidHom.comp
            (localArtin.comp eK.symm.toMonoidHom))) =
      (localNormSubgroup vK.Completion E).map
        eK.toMonoidHom
  apply SetLike.ext
  intro x
  constructor
  · intro hx
    change
      (absoluteValueDecompositionGroup K w.1).subtype
          (eD.symm (localArtin (eK.symm x))) = 1 at hx
    have hxSubgroup :
        eD.symm (localArtin (eK.symm x)) = 1 := by
      apply Subtype.coe_injective
      exact hx
    have hxLocal :
        localArtin (eK.symm x) = 1 := by
      apply eD.symm.injective
      simpa only [map_one] using hxSubgroup
    have hxKer :
        eK.symm x ∈ MonoidHom.ker localArtin :=
      hxLocal
    have hxNorm :
        eK.symm x ∈ localNormSubgroup vK.Completion E := by
      rw [
        LocalClassFieldTheory.abelianLocalArtinMonoidHom_ker
      ] at hxKer
      exact hxKer
    exact
      ⟨eK.symm x, hxNorm, eK.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    have hyKer :
        y ∈ MonoidHom.ker localArtin := by
      rw [
        LocalClassFieldTheory.abelianLocalArtinMonoidHom_ker
      ]
      exact hy
    have hyArtin : localArtin y = 1 := hyKer
    change
      (absoluteValueDecompositionGroup K w.1).subtype
          (eD.symm (localArtin (eK.symm (eK y)))) = 1
    simp only [eK.symm_apply_apply, hyArtin, map_one]

end Reciprocity
end GlobalClassFieldTheory
