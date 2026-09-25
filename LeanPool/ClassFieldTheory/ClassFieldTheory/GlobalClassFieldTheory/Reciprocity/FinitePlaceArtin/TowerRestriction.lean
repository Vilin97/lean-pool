/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Conjugation
/-!
# Restriction in a finite-place Artin tower

This module restricts finite-place extensions through an intermediate field and proves
  restriction naturality for the corresponding global Artin homomorphisms.
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
/-- Restrict an extension of a finite place through an intermediate
field in a scalar tower. -/
def restrictFinitePlaceExtension
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) E where
  val :=
    w.1.comp (f := algebraMap E L)
      (algebraMap E L).injective
  property x := by
    change
      w.1 (algebraMap E L (algebraMap K E x)) =
        NumberField.HeightOneSpectrum.adicAbv K v x
    rw [← IsScalarTower.algebraMap_apply K E L]
    exact w.2 x

omit [NumberField K] [FiniteDimensional K L]
    [IsAbelianGalois K L] in
open scoped Classical in
/-- Completion maps compose along a scalar tower when the three
absolute values extend one another. -/
theorem absoluteValueCompletionMap_comp_of_isScalarTower
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    (vK : AbsoluteValue K ℝ)
    (vE : AbsoluteValue E ℝ)
    (vL : AbsoluteValue L ℝ)
    (hKE : AbsoluteValue.Extends vK vE)
    (hEL : AbsoluteValue.Extends vE vL)
    (hKL : AbsoluteValue.Extends vK vL) :
    (AbsoluteValue.completionMap vE vL hEL).comp
        (AbsoluteValue.completionMap vK vE hKE) =
      AbsoluteValue.completionMap vK vL hKL := by
  ext x
  refine
    UniformSpace.Completion.induction_on
      (α := WithAbs vK) x ?_ ?_
  · exact isClosed_eq
      ((AbsoluteValue.completionMap_isometry
          vE vL hEL).continuous.comp
        (AbsoluteValue.completionMap_isometry
          vK vE hKE).continuous)
      (AbsoluteValue.completionMap_isometry
        vK vL hKL).continuous
  · intro a
    have ha : (a : vK.Completion) =
        algebraMap K vK.Completion
          (WithAbs.equiv vK a) := by
      change (a : vK.Completion) =
        (((WithAbs.equiv vK).symm
          (WithAbs.equiv vK a) : WithAbs vK) :
            vK.Completion)
      exact congrArg
        (fun z : WithAbs vK => (z : vK.Completion))
        ((WithAbs.equiv vK).symm_apply_apply a).symm
    rw [ha]
    change
      AbsoluteValue.completionMap vE vL hEL
          (AbsoluteValue.completionMap vK vE hKE
            (algebraMap K vK.Completion
              (WithAbs.equiv vK a))) =
        AbsoluteValue.completionMap vK vL hKL
          (algebraMap K vK.Completion
            (WithAbs.equiv vK a))
    rw [AbsoluteValue.completionMap_coe,
      AbsoluteValue.toCompletion_eq_algebraMap,
      AbsoluteValue.completionMap_coe,
      AbsoluteValue.completionMap_coe,
      IsScalarTower.algebraMap_apply K E L]

open scoped Classical in
/-- The completion map in a number-field tower restricts to the
corresponding algebraic localizations. -/
noncomputable def finitePlaceRestrictedLocalizedCompletionAlgHom
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E]
    (v : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wE :=
      restrictFinitePlaceExtension
        (K := K) (L := L) (E := E) v wL
    let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
    let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
    letI : Algebra vK.Completion EL :=
      finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := E) v wE
    letI : Algebra vK.Completion LL :=
      finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := L) v wL
    EL →ₐ[vK.Completion] LL := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let wE :=
    restrictFinitePlaceExtension
      (K := K) (L := L) (E := E) v wL
  letI hEK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wE.1
  letI : SMul K wE.1.Completion := hEK.toSMul
  letI : Algebra vK.Completion wE.1.Completion :=
    AbsoluteValue.completionAlgebra vK wE.1 wE.2
  letI hLK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wL.1
  letI : SMul K wL.1.Completion := hLK.toSMul
  letI : Algebra vK.Completion wL.1.Completion :=
    AbsoluteValue.completionAlgebra vK wL.1 wL.2
  let hwEL : AbsoluteValue.Extends wE.1 wL.1 := by
    intro x
    rfl
  letI : Algebra wE.1.Completion wL.1.Completion :=
    AbsoluteValue.completionAlgebra wE.1 wL.1 hwEL
  have hcompletion :
      (AbsoluteValue.completionMap wE.1 wL.1 hwEL).comp
          (AbsoluteValue.completionMap vK wE.1 wE.2) =
        AbsoluteValue.completionMap vK wL.1 wL.2 :=
    absoluteValueCompletionMap_comp_of_isScalarTower
      (K := K) (L := L) (E := E)
      vK wE.1 wL.1 wE.2 hwEL wL.2
  let completionAlgHom :
      wE.1.Completion →ₐ[vK.Completion]
        wL.1.Completion :=
    { __ := AbsoluteValue.completionMap wE.1 wL.1 hwEL
      commutes' := fun x => by
        change
          AbsoluteValue.completionMap wE.1 wL.1 hwEL
              (AbsoluteValue.completionMap
                vK wE.1 wE.2 x) =
            AbsoluteValue.completionMap
              vK wL.1 wL.2 x
        exact DFunLike.congr_fun hcompletion x }
  let EL :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
  let LL :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
  let eE :
      EL ≃ₐ[vK.Completion] wE.1.Completion :=
    AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
      vK hvK wE
  let eL :
      LL ≃ₐ[vK.Completion] wL.1.Completion :=
    AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
      vK hvK wL
  let localizationAlgHom :
      EL →ₐ[vK.Completion] LL :=
    eL.symm.toAlgHom.comp
      (completionAlgHom.comp eE.toAlgHom)
  exact localizationAlgHom

omit [IsAbelianGalois K L] in
open scoped Classical in
/-- The restricted-localization map agrees with the original
number-field embedding on the intermediate field. -/
theorem finitePlaceRestrictedLocalizedCompletionAlgHom_toAlgebraicLocalization
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : E) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wE :=
      restrictFinitePlaceExtension
        (K := K) (L := L) (E := E) v wL
    let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
    let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
    letI : Algebra vK.Completion EL :=
      finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := E) v wE
    letI : Algebra vK.Completion LL :=
      finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := L) v wL
    finitePlaceRestrictedLocalizedCompletionAlgHom
        (K := K) (L := L) (E := E) v wL
        (AbsoluteValue.toAlgebraicLocalization
          vK wE.1 wE.2 x) =
      AbsoluteValue.toAlgebraicLocalization
        vK wL.1 wL.2 (algebraMap E L x) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let wE :=
    restrictFinitePlaceExtension
      (K := K) (L := L) (E := E) v wL
  let hEK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wE.1
  let : SMul K wE.1.Completion := hEK.toSMul
  let : Algebra vK.Completion wE.1.Completion :=
    AbsoluteValue.completionAlgebra vK wE.1 wE.2
  let hLK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wL.1
  let : SMul K wL.1.Completion := hLK.toSMul
  let : Algebra vK.Completion wL.1.Completion :=
    AbsoluteValue.completionAlgebra vK wL.1 wL.2
  let hwEL : AbsoluteValue.Extends wE.1 wL.1 := by
    intro z
    rfl
  let : Algebra wE.1.Completion wL.1.Completion :=
    AbsoluteValue.completionAlgebra wE.1 wL.1 hwEL
  let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
  let eL :
      LL ≃ₐ[vK.Completion] wL.1.Completion :=
    AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
      vK hvK wL
  apply eL.injective
  change
    AbsoluteValue.completionMap wE.1 wL.1 hwEL
        (AbsoluteValue.toCompletion wE.1 x) =
      AbsoluteValue.toCompletion wL.1
        (algebraMap E L x)
  rw [AbsoluteValue.toCompletion_eq_algebraMap,
    AbsoluteValue.completionMap_coe]

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- Compatible embeddings descend a commuting square of actions along an injective map. -/
private theorem action_commutes_of_embedding_square
    {E L EL LL : Type*} [Field E] [Field L] [Field EL] [Field LL]
    (i : E →+* L) (f : E →+* EL) (g : L →+* LL) (j : EL →+* LL)
    (sigmaE : E → E) (sigmaL : L → L) (tauE : EL → EL) (tauL : LL → LL)
    (hdiagram : ∀ z, j (f z) = g (i z))
    (htau : ∀ z, tauL (j z) = j (tauE z))
    (hE : ∀ z, tauE (f z) = f (sigmaE z))
    (hL : ∀ z, tauL (g z) = g (sigmaL z)) (z : E) :
    i (sigmaE z) = sigmaL (i z) := by
  apply g.injective
  calc
    g (i (sigmaE z)) = j (f (sigmaE z)) := (hdiagram _).symm
    _ = j (tauE (f z)) := congrArg j (hE _).symm
    _ = tauL (j (f z)) := (htau _).symm
    _ = tauL (g (i z)) := congrArg tauL (hdiagram _)
    _ = g (sigmaL (i z)) := hL _

omit [NumberField K] [FiniteDimensional K L] in
/-- A compatible embedding of algebraic localizations carries
restriction of decomposition-group elements to restriction of the
corresponding local automorphisms. -/
theorem decompositionGroupEquivAlgebraicLocalizationAut_restrict_of_commutes
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (wE : AbsoluteValueExtension vK E)
    (wL : AbsoluteValueExtension vK L) :
    letI hEK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) wE.1
    letI : SMul K wE.1.Completion := hEK.toSMul
    letI : Algebra vK.Completion wE.1.Completion :=
      AbsoluteValue.completionAlgebra vK wE.1 wE.2
    letI hLK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) wL.1
    letI : SMul K wL.1.Completion := hLK.toSMul
    letI : Algebra vK.Completion wL.1.Completion :=
      AbsoluteValue.completionAlgebra vK wL.1 wL.2
    let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
    let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
    ∀ (localizationEmbedding : EL →ₐ[vK.Completion] LL),
      letI hELL : Algebra EL LL :=
        localizationEmbedding.toRingHom.toAlgebra
      letI : SMul EL LL := hELL.toSMul
      letI : IsScalarTower vK.Completion EL LL :=
        IsScalarTower.of_algebraMap_eq' (by
          apply RingHom.ext
          intro x
          exact (localizationEmbedding.commutes x).symm)
      letI : FiniteDimensional vK.Completion EL :=
        AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
          vK hvK wE
      letI : IsAbelianGalois vK.Completion EL :=
        LocalClassFieldTheory.localizedCompletion_isAbelianGalois
          vK hvK wE
      let eDE :
          absoluteValueDecompositionGroup K wE.1 ≃*
            (EL ≃ₐ[vK.Completion] EL) :=
        decompositionGroupEquivAlgebraicLocalizationAut
          vK hvK wE
      let eDL :
          absoluteValueDecompositionGroup K wL.1 ≃*
            (LL ≃ₐ[vK.Completion] LL) :=
        decompositionGroupEquivAlgebraicLocalizationAut
          vK hvK wL
      (∀ z : E,
        localizationEmbedding
            (AbsoluteValue.toAlgebraicLocalization
              vK wE.1 wE.2 z) =
          AbsoluteValue.toAlgebraicLocalization
            vK wL.1 wL.2 (algebraMap E L z)) →
        ∀ tauL : LL ≃ₐ[vK.Completion] LL,
          AlgEquiv.restrictNormalHom E
              ((eDL.symm tauL).1 : L ≃ₐ[K] L) =
            ((eDE.symm
              (AlgEquiv.restrictNormalHom EL tauL)).1 :
                E ≃ₐ[K] E) := by
  let hEK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wE.1
  let : SMul K wE.1.Completion := hEK.toSMul
  let : Algebra vK.Completion wE.1.Completion :=
    AbsoluteValue.completionAlgebra vK wE.1 wE.2
  let hLK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wL.1
  let : SMul K wL.1.Completion := hLK.toSMul
  let : Algebra vK.Completion wL.1.Completion :=
    AbsoluteValue.completionAlgebra vK wL.1 wL.2
  let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
  let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
  change
    ∀ localizationEmbedding : EL →ₐ[vK.Completion] LL, _
  intro localizationEmbedding
  let hELL : Algebra EL LL :=
    localizationEmbedding.toRingHom.toAlgebra
  let : SMul EL LL := hELL.toSMul
  let : IsScalarTower vK.Completion EL LL :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (localizationEmbedding.commutes x).symm)
  let : FiniteDimensional vK.Completion EL :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
      vK hvK wE
  let : IsAbelianGalois vK.Completion EL :=
    LocalClassFieldTheory.localizedCompletion_isAbelianGalois
      vK hvK wE
  let eDE :
      absoluteValueDecompositionGroup K wE.1 ≃*
        (EL ≃ₐ[vK.Completion] EL) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK wE
  let eDL :
      absoluteValueDecompositionGroup K wL.1 ≃*
        (LL ≃ₐ[vK.Completion] LL) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK wL
  change
    (∀ z : E,
      localizationEmbedding
          (AbsoluteValue.toAlgebraicLocalization
            vK wE.1 wE.2 z) =
        AbsoluteValue.toAlgebraicLocalization
          vK wL.1 wL.2 (algebraMap E L z)) →
      ∀ tauL : LL ≃ₐ[vK.Completion] LL, _
  intro hlocalization tauL
  let rhoL : absoluteValueDecompositionGroup K wL.1 :=
    eDL.symm tauL
  let tauE := AlgEquiv.restrictNormalHom EL tauL
  let rhoE : absoluteValueDecompositionGroup K wE.1 :=
    eDE.symm tauE
  change
    AlgEquiv.restrictNormalHom E
        (rhoL.1 : L ≃ₐ[K] L) =
      (rhoE.1 : E ≃ₐ[K] E)
  apply AlgEquiv.ext
  intro z
  apply (algebraMap E L).injective
  refine (AlgEquiv.restrictNormal_commutes (rhoL.1 : L ≃ₐ[K] L) E z).trans ?_
  symm
  apply action_commutes_of_embedding_square
    (algebraMap E L)
    (AbsoluteValue.toAlgebraicLocalization vK wE.1 wE.2)
    (AbsoluteValue.toAlgebraicLocalization vK wL.1 wL.2)
    localizationEmbedding.toRingHom rhoE.1 rhoL.1 tauE tauL hlocalization
  · intro u
    exact (AlgEquiv.restrictNormal_commutes tauL EL u).symm
  · intro u
    change tauE _ = _
    rw [← eDE.apply_symm_apply tauE]
    exact localizationRamificationGroups_decompositionGroupEquiv_toLocalization vK hvK wE _ _
  · intro u
    change tauL _ = _
    rw [← eDL.apply_symm_apply tauL]
    exact localizationRamificationGroups_decompositionGroupEquiv_toLocalization vK hvK wL _ _

open scoped Classical in
private noncomputable def finitePlaceLocalRestrictionMonoidHom
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (v : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wE :=
      restrictFinitePlaceExtension
        (K := K) (L := L) (E := E) v wL
    let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
    let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
    letI : Algebra vK.Completion EL :=
      finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := E) v wE
    letI : Algebra vK.Completion LL :=
      finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := L) v wL
    (LL ≃ₐ[vK.Completion] LL) →*
      (EL ≃ₐ[vK.Completion] EL) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wE :=
    restrictFinitePlaceExtension
      (K := K) (L := L) (E := E) v wL
  let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
  let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
  letI : Algebra vK.Completion EL :=
    finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := E) v wE
  letI : Algebra vK.Completion LL :=
    finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := L) v wL
  let localizationAlgHom :=
    finitePlaceRestrictedLocalizedCompletionAlgHom
      (K := K) (L := L) (E := E) v wL
  letI hELL : Algebra EL LL :=
    localizationAlgHom.toRingHom.toAlgebra
  letI : SMul EL LL := hELL.toSMul
  letI : IsScalarTower vK.Completion EL LL :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (localizationAlgHom.commutes x).symm)
  letI : FiniteDimensional vK.Completion EL :=
    finitePlaceLocalArtinFiniteDimensional (K := K) (L := E) v wE
  letI : IsAbelianGalois vK.Completion EL :=
    finitePlaceLocalArtinIsAbelianGalois (K := K) (L := E) v wE
      (inferInstance : FiniteDimensional K E)
  letI hGaloisEL : IsGalois vK.Completion EL :=
    (inferInstance :
      IsAbelianGalois vK.Completion EL).toIsGalois
  letI : Normal vK.Completion EL :=
    hGaloisEL.to_normal
  exact AlgEquiv.restrictNormalHom EL

open scoped Classical in
/-- Restriction of global decomposition-group elements agrees with
restriction of the corresponding automorphisms of algebraic
localizations, pointwise on local automorphisms. -/
theorem finitePlaceDecompositionTransport_restrict_tower_apply
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (v : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let wE :=
      restrictFinitePlaceExtension
        (K := K) (L := L) (E := E) v wL
    let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
    let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
    letI : Algebra vK.Completion EL :=
      finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := E) v wE
    letI : Algebra vK.Completion LL :=
      finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := L) v wL
    let localizationAlgHom :=
      finitePlaceRestrictedLocalizedCompletionAlgHom
        (K := K) (L := L) (E := E) v wL
    letI hELL : Algebra EL LL :=
      localizationAlgHom.toRingHom.toAlgebra
    letI : SMul EL LL := hELL.toSMul
    letI : IsScalarTower vK.Completion EL LL :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        exact (localizationAlgHom.commutes x).symm)
    letI : FiniteDimensional vK.Completion EL :=
      finitePlaceLocalArtinFiniteDimensional (K := K) (L := E) v wE
    letI : IsAbelianGalois vK.Completion EL :=
      finitePlaceLocalArtinIsAbelianGalois (K := K) (L := E) v wE
        (inferInstance : FiniteDimensional K E)
    let eDE :
        absoluteValueDecompositionGroup K wE.1 ≃*
          (EL ≃ₐ[vK.Completion] EL) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK wE
    let eDL :
        absoluteValueDecompositionGroup K wL.1 ≃*
          (LL ≃ₐ[vK.Completion] LL) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK wL
    ∀ tauL : LL ≃ₐ[vK.Completion] LL,
      AlgEquiv.restrictNormalHom E
          ((eDL.symm tauL).1 : L ≃ₐ[K] L) =
        ((eDE.symm
          (AlgEquiv.restrictNormalHom EL tauL)).1 : E ≃ₐ[K] E) := by
  exact
    decompositionGroupEquivAlgebraicLocalizationAut_restrict_of_commutes
      (K := K) (L := L) (E := E)
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v)
      (restrictFinitePlaceExtension
        (K := K) (L := L) (E := E) v wL)
      wL
      (finitePlaceRestrictedLocalizedCompletionAlgHom
        (K := K) (L := L) (E := E) v wL)
      (fun z =>
        finitePlaceRestrictedLocalizedCompletionAlgHom_toAlgebraicLocalization
          (K := K) (L := L) (E := E) v wL z)

open scoped Classical in
/-- Restriction of global decomposition-group elements agrees with
restriction of the corresponding automorphisms of algebraic
localizations. -/
theorem finitePlaceDecompositionTransport_restrict_tower
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (v : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let wE :=
      restrictFinitePlaceExtension
        (K := K) (L := L) (E := E) v wL
    let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
    let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
    letI : Algebra vK.Completion EL :=
      finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := E) v wE
    letI : Algebra vK.Completion LL :=
      finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := L) v wL
    let localizationAlgHom :=
      finitePlaceRestrictedLocalizedCompletionAlgHom
        (K := K) (L := L) (E := E) v wL
    letI hELL : Algebra EL LL :=
      localizationAlgHom.toRingHom.toAlgebra
    letI : SMul EL LL := hELL.toSMul
    letI : IsScalarTower vK.Completion EL LL :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        exact (localizationAlgHom.commutes x).symm)
    letI : FiniteDimensional vK.Completion EL :=
      finitePlaceLocalArtinFiniteDimensional (K := K) (L := E) v wE
    letI : IsAbelianGalois vK.Completion EL :=
      finitePlaceLocalArtinIsAbelianGalois (K := K) (L := E) v wE
        (inferInstance : FiniteDimensional K E)
    let eDE :
        absoluteValueDecompositionGroup K wE.1 ≃*
          (EL ≃ₐ[vK.Completion] EL) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK wE
    let eDL :
        absoluteValueDecompositionGroup K wL.1 ≃*
          (LL ≃ₐ[vK.Completion] LL) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK wL
    (AlgEquiv.restrictNormalHom E).comp
        ((absoluteValueDecompositionGroup K wL.1).subtype.comp
          eDL.symm.toMonoidHom) =
      ((absoluteValueDecompositionGroup K wE.1).subtype.comp
          eDE.symm.toMonoidHom).comp
        (AlgEquiv.restrictNormalHom EL) := by
  apply MonoidHom.ext
  intro tauL
  exact
    finitePlaceDecompositionTransport_restrict_tower_apply
      (K := K) (L := L) (E := E) v wL tauL

open scoped Classical in
/-- Local Artin maps on localized completions commute with restriction
through an abelian intermediate field. -/
theorem finitePlaceLocalArtinMonoidHom_restrict_tower
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (v : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    (finitePlaceLocalRestrictionMonoidHom
        (K := K) (L := L) (E := E) v wL).comp
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v wL) =
      finitePlaceLocalArtinMonoidHom
        (K := K) (L := E) v
        (restrictFinitePlaceExtension
          (K := K) (L := L) (E := E) v wL) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wE :=
    restrictFinitePlaceExtension
      (K := K) (L := L) (E := E) v wL
  let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
  let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
  let : Algebra vK.Completion EL :=
    finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := E) v wE
  let : Algebra vK.Completion LL :=
    finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := L) v wL
  let localizationAlgHom :=
    finitePlaceRestrictedLocalizedCompletionAlgHom
      (K := K) (L := L) (E := E) v wL
  let hELL : Algebra EL LL :=
    localizationAlgHom.toRingHom.toAlgebra
  let : SMul EL LL := hELL.toSMul
  let : IsScalarTower vK.Completion EL LL :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (localizationAlgHom.commutes x).symm)
  let : FiniteDimensional vK.Completion EL :=
    finitePlaceLocalArtinFiniteDimensional (K := K) (L := E) v wE
  let : IsAbelianGalois vK.Completion EL :=
    finitePlaceLocalArtinIsAbelianGalois (K := K) (L := E) v wE
      (inferInstance : FiniteDimensional K E)
  let hGaloisEL : IsGalois vK.Completion EL :=
    (inferInstance :
      IsAbelianGalois vK.Completion EL).toIsGalois
  let : Normal vK.Completion EL :=
    hGaloisEL.to_normal
  let : FiniteDimensional vK.Completion LL :=
    finitePlaceLocalArtinFiniteDimensional (K := K) (L := L) v wL
  let : IsAbelianGalois vK.Completion LL :=
    finitePlaceLocalArtinIsAbelianGalois (K := K) (L := L) v wL
      (inferInstance : FiniteDimensional K L)
  let : ValuativeRel vK.Completion :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField vK.Completion :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let eK :
      vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  change
    (AlgEquiv.restrictNormalHom EL).comp
        ((LocalClassFieldTheory.abelianLocalArtinMonoidHom
          vK.Completion LL).comp eK.symm.toMonoidHom) =
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom
        vK.Completion EL).comp eK.symm.toMonoidHom
  apply MonoidHom.ext
  intro x
  exact
    DFunLike.congr_fun
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom_restrict_tower
        vK.Completion EL LL)
      (eK.symm x)


open scoped Classical in
/-- Finite-place Artin homomorphisms attached to specified place
extensions commute with restriction through an abelian tower. -/
theorem finitePlaceArtinMonoidHomOfExtension_restrict_tower
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (v : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    (AlgEquiv.restrictNormalHom E).comp
        (finitePlaceArtinMonoidHomOfExtension
          (K := K) (L := L) v wL) =
      finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := E) v
        (restrictFinitePlaceExtension
          (K := K) (L := L) (E := E) v wL) := by
  let wE :=
    restrictFinitePlaceExtension
      (K := K) (L := L) (E := E) v wL
  calc
    (AlgEquiv.restrictNormalHom E).comp
        (finitePlaceArtinMonoidHomOfExtension
          (K := K) (L := L) v wL) =
      (AlgEquiv.restrictNormalHom E).comp
        ((finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := L) v wL).comp
          (finitePlaceLocalArtinMonoidHom
            (K := K) (L := L) v wL)) :=
      congrArg
        (fun f => (AlgEquiv.restrictNormalHom E).comp f)
        (finitePlaceArtinMonoidHomOfExtension_factor
          (K := K) (L := L) v wL)
    _ =
        ((AlgEquiv.restrictNormalHom E).comp
          (finitePlaceLocalToGlobalMonoidHom
            (K := K) (L := L) v wL)).comp
          (finitePlaceLocalArtinMonoidHom
            (K := K) (L := L) v wL) := by
      rfl
    _ =
        ((finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := E) v wE).comp
          (finitePlaceLocalRestrictionMonoidHom
            (K := K) (L := L) (E := E) v wL)).comp
          (finitePlaceLocalArtinMonoidHom
            (K := K) (L := L) v wL) :=
      congrArg
        (fun f => f.comp
          (finitePlaceLocalArtinMonoidHom
            (K := K) (L := L) v wL))
        (finitePlaceDecompositionTransport_restrict_tower
          (K := K) (L := L) (E := E) v wL)
    _ =
        (finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := E) v wE).comp
          ((finitePlaceLocalRestrictionMonoidHom
            (K := K) (L := L) (E := E) v wL).comp
            (finitePlaceLocalArtinMonoidHom
              (K := K) (L := L) v wL)) := by
      rfl
    _ =
        (finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := E) v wE).comp
          (finitePlaceLocalArtinMonoidHom
            (K := K) (L := E) v wE) :=
      congrArg
        (fun f => (finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := E) v wE).comp f)
        (finitePlaceLocalArtinMonoidHom_restrict_tower
          (K := K) (L := L) (E := E) v wL)
    _ =
        finitePlaceArtinMonoidHomOfExtension
          (K := K) (L := E) v wE :=
      (finitePlaceArtinMonoidHomOfExtension_factor
        (K := K) (L := E) v wE).symm

open scoped Classical in
/-- Finite local factors commute with restriction in an abelian
number-field tower. -/
theorem chosenFinitePlaceArtinMonoidHom_restrict_tower
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) :
    (AlgEquiv.restrictNormalHom E).comp
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v) =
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := E) v := by
  let wL :=
    chosenFinitePlaceExtension
      (L := L) v
  let wE :=
    restrictFinitePlaceExtension
      (K := K) (L := L) (E := E) v wL
  calc
    (AlgEquiv.restrictNormalHom E).comp
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v) =
      finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := E) v wE :=
      finitePlaceArtinMonoidHomOfExtension_restrict_tower
        (K := K) (L := L) (E := E) v wL
    _ = chosenFinitePlaceArtinMonoidHom
        (K := K) (L := E) v :=
      finitePlaceArtinMonoidHomOfExtension_eq
        (K := K) (L := E) v wE
        (chosenFinitePlaceExtension
          (L := E) v)

end Reciprocity
end GlobalClassFieldTheory
