/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.TowerRestriction
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison
/-!
# Cross-base restriction of finite-place Artin homomorphisms

This module compares localized completions in a square of number fields with different base
  fields and transports restriction through the corresponding decomposition groups.
-/

open scoped IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

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
private theorem finitePlaceArtinLocalizedCompletion_algebraMap
    {F M : Type}
    [Field F] [NumberField F]
    [Field M] [NumberField M]
    [Algebra F M] [FiniteDimensional F M]
    (v : HeightOneSpectrum (𝓞 F))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v) M)
    (x : (NumberField.HeightOneSpectrum.adicAbv F v).Completion) :
    let vF := NumberField.HeightOneSpectrum.adicAbv F v
    let hvF : vF.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    letI hMF :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := F) w.1
    letI : SMul F w.1.Completion := hMF.toSMul
    letI : Algebra vF.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vF w.1 w.2
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vF w
    let U := finitePlaceExtensionEquivAbove
      (K := F) (L := M) v w
    let eF :
        vF.Completion ≃+* v.adicCompletion F :=
      (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
    let eE :
        E ≃+* U.1.adicCompletion M :=
      (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
          vF hvF w).toRingEquiv.trans
        (finitePlaceExtensionAdicCompletionRingEquiv
          (K := F) (L := M) v w)
    eE (algebraMap vF.Completion E x) =
      finitePlaceAdicCompletionMap
        F M v U (eF x) := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let hvF : vF.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hMF :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := F) w.1
  let : SMul F w.1.Completion := hMF.toSMul
  let : Algebra vF.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vF w.1 w.2
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vF w
  let U := finitePlaceExtensionEquivAbove
    (K := F) (L := M) v w
  let eF :
      vF.Completion ≃+* v.adicCompletion F :=
    (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let eE :
      E ≃+* U.1.adicCompletion M :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vF hvF w).toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := F) (L := M) v w)
  change
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := F) (L := M) v w
        (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
          vF hvF w (algebraMap vF.Completion E x)) =
      finitePlaceAdicCompletionMap
        F M v U
          (relativeFinitePlaceCompletionAlgEquiv v x)
  rw [
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
      vF hvF w).commutes]
  rw [←
    finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
      F M v w]
  change
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := F) (L := M) v w
        (algebraMap vF.Completion w.1.Completion x) =
      finitePlaceExtensionAdicCompletionRingEquiv
        (K := F) (L := M) v w
        (AbsoluteValue.completionMap vF w.1 w.2
          ((relativeFinitePlaceCompletionAlgEquiv v).symm
            (relativeFinitePlaceCompletionAlgEquiv v x)))
  rw [
    (relativeFinitePlaceCompletionAlgEquiv v).symm_apply_apply,
    AbsoluteValue.completionAlgebra_algebraMap]

open scoped Classical in
/-- The continuous ring homomorphism between base completions attached to a finite place lying
above another. -/
noncomputable def finitePlaceArtinRelativeCompletionRingHom
    {K' : Type} [Field K'] [NumberField K']
    [Algebra K K']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion →+*
      (NumberField.HeightOneSpectrum.adicAbv K' W).Completion :=
  let eC :=
    (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let eD :=
    (relativeFinitePlaceCompletionAlgEquiv W).toRingEquiv
  eD.symm.toRingHom.comp
    ((finitePlaceAdicCompletionMap
      K K' v ⟨W, hW⟩).comp eC.toRingHom)

open scoped Classical in
/-- The finite-place map between the relative base completions is continuous. -/
theorem finitePlaceArtinRelativeCompletionRingHom_continuous
    {K' : Type} [Field K'] [NumberField K']
    [Algebra K K']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v) :
    Continuous
      (finitePlaceArtinRelativeCompletionRingHom
        (K := K) (K' := K') v W hW) := by
  let eD :=
    (relativeFinitePlaceCompletionAlgEquiv W).toRingEquiv
  have hDsymm : Isometry eD.symm :=
    AddMonoidHomClass.isometry_of_norm eD.symm
      (relativeFinitePlaceCompletionAlgEquiv_symm_norm W)
  exact
    hDsymm.continuous.comp
      ((finitePlaceAdicCompletionMap_continuous
        K K' v ⟨W, hW⟩).comp
        (relativeFinitePlaceCompletionRingHom_isometry v).continuous)

open scoped Classical in
/-- The localized completion at a finite place, with its completion-algebra
tower hidden behind one named type. -/
noncomputable abbrev finitePlaceArtinLocalizedCompletion
    (F M : Type) [Field F] [NumberField F]
    [Field M] [Algebra F M]
    (v : HeightOneSpectrum (𝓞 F))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v) M) : Type :=
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vF w
  letI : Algebra vF.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra (K := F) (L := M) v w
  E

open scoped Classical in
/-- The canonical map from the base completion into the localized completion,
with its construction tower confined to the definition body. -/
noncomputable def finitePlaceArtinLocalizedCompletionBaseRingHom
    (F M : Type) [Field F] [NumberField F]
    [Field M] [NumberField M] [Algebra F M]
    (v : HeightOneSpectrum (𝓞 F))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v) M) :
    (NumberField.HeightOneSpectrum.adicAbv F v).Completion →+*
      finitePlaceArtinLocalizedCompletion F M v w := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  letI hwF :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := F) w.1
  letI : SMul F w.1.Completion := hwF.toSMul
  letI : Algebra vF.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vF w.1 w.2
  exact algebraMap vF.Completion
    (AlgebraicNumberTheory.Valuations.LocalizedCompletion vF w)

open scoped Classical in
/-- The ring homomorphism between localized completions in a finite-place scalar tower. -/
noncomputable def finitePlaceArtinLocalizedCompletionRingHom
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [NumberField L]
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [Algebra L L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w) :
    finitePlaceArtinLocalizedCompletion K L v w →+*
      finitePlaceArtinLocalizedCompletion K' L' W w' := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hvK' : vK'.IsNontrivial :=
    RayClass.adicAbv_isNontrivial W
  letI hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hwK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  letI hwK' :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K') w'.1
  letI : SMul K' w'.1.Completion := hwK'.toSMul
  letI : Algebra vK'.Completion w'.1.Completion :=
    AbsoluteValue.completionAlgebra vK' w'.1 w'.2
  let U :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v w
  let U' :=
    finitePlaceExtensionEquivAbove
      (K := K') (L := L') W w'
  have hU'L : finitePlaceBelow (K := L) U'.1 = U.1 := by
    simpa only [
      U, U',
      finitePlaceExtensionEquivAbove_coe
    ] using hcentres
  let eE :
      AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w ≃+*
        U.1.adicCompletion L :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK hvK w).toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w)
  let eE' :
      AlgebraicNumberTheory.Valuations.LocalizedCompletion vK' w' ≃+*
        U'.1.adicCompletion L' :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK' hvK' w').toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K') (L := L') W w')
  exact
    eE'.symm.toRingHom.comp
      ((finitePlaceAdicCompletionMap
        L L' U.1 ⟨U'.1, hU'L⟩).comp eE.toRingHom)

omit [IsAbelianGalois K L] in
open scoped Classical in
/-- The localized-completion map agrees with the scalar-tower embedding on global elements. -/
theorem finitePlaceArtinLocalizedCompletion_towerPoint
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [NumberField L]
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w)
    (x : (NumberField.HeightOneSpectrum.adicAbv K v).Completion) :
    finitePlaceArtinLocalizedCompletionBaseRingHom K' L' W w'
        (finitePlaceArtinRelativeCompletionRingHom
          (K := K) (K' := K') v W hW x) =
      finitePlaceArtinLocalizedCompletionRingHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W w w' hcentres
        (finitePlaceArtinLocalizedCompletionBaseRingHom K L v w x) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hvK' : vK'.IsNontrivial :=
    RayClass.adicAbv_isNontrivial W
  let hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hwK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
  let hwK' :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K') w'.1
  let : SMul K' w'.1.Completion := hwK'.toSMul
  let : Algebra vK'.Completion w'.1.Completion :=
    AbsoluteValue.completionAlgebra vK' w'.1 w'.2
  let :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK' w'
  let C := vK.Completion
  let D := vK'.Completion
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let E' := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK' w'
  let : Algebra C D :=
    (finitePlaceArtinRelativeCompletionRingHom
      (K := K) (K' := K') v W hW).toAlgebra
  let : Algebra E E' :=
    (finitePlaceArtinLocalizedCompletionRingHom
      (K := K) (L := L) (K' := K') (L' := L')
      v W w w' hcentres).toAlgebra
  let : Algebra C E' :=
    ((algebraMap D E').comp (algebraMap C D)).toAlgebra
  change algebraMap C E' x =
    algebraMap E E' (algebraMap C E x)
  let U :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v w
  let U' :=
    finitePlaceExtensionEquivAbove
      (K := K') (L := L') W w'
  have hU'L : finitePlaceBelow (K := L) U'.1 = U.1 := by
    simpa only [
      U, U',
      finitePlaceExtensionEquivAbove_coe
    ] using hcentres
  have hU'K :
      finitePlaceBelow (K := K) U'.1 = v := by
    calc
      finitePlaceBelow (K := K) U'.1 =
          finitePlaceBelow (K := K)
            (finitePlaceBelow (K := K') U'.1) := by
        rw [finitePlaceBelow_finitePlaceBelow]
      _ = finitePlaceBelow (K := K) W := by
        rw [U'.2]
      _ = v := hW
  let eC :
      C ≃+* v.adicCompletion K :=
    (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let eD :
      D ≃+* W.adicCompletion K' :=
    (relativeFinitePlaceCompletionAlgEquiv W).toRingEquiv
  let eE :
      E ≃+* U.1.adicCompletion L :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK hvK w).toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w)
  let eE' :
      E' ≃+* U'.1.adicCompletion L' :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK' hvK' w').toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K') (L := L') W w')
  have hLowerBase (y : C) :
      eE (algebraMap C E y) =
        finitePlaceAdicCompletionMap
          K L v U (eC y) :=
    finitePlaceArtinLocalizedCompletion_algebraMap
      (F := K) (M := L) v w y
  have hUpperBase (y : D) :
      eE' (algebraMap D E' y) =
        finitePlaceAdicCompletionMap
          K' L' W U' (eD y) :=
    finitePlaceArtinLocalizedCompletion_algebraMap
      (F := K') (M := L') W w' y
  have hBaseMap (y : C) :
      eD (algebraMap C D y) =
        finitePlaceAdicCompletionMap
          K K' v ⟨W, hW⟩ (eC y) := by
    change
      eD (eD.symm
        (finitePlaceAdicCompletionMap
          K K' v ⟨W, hW⟩ (eC y))) =
        finitePlaceAdicCompletionMap
          K K' v ⟨W, hW⟩ (eC y)
    rw [eD.apply_symm_apply]
  apply eE'.injective
  calc
    eE' (algebraMap C E' x) =
        finitePlaceAdicCompletionMap
          K' L' W U'
          (finitePlaceAdicCompletionMap
            K K' v ⟨W, hW⟩ (eC x)) := by
      change eE' (algebraMap D E' (algebraMap C D x)) = _
      rw [hUpperBase, hBaseMap]
    _ =
        finitePlaceAdicCompletionMap
          K L' v ⟨U'.1, hU'K⟩ (eC x) :=
      finitePlaceAdicCompletionMap_comp
        K L' (M := K') v W U'.1 hW U'.2 hU'K (eC x)
    _ =
        finitePlaceAdicCompletionMap
          L L' U.1 ⟨U'.1, hU'L⟩
          (finitePlaceAdicCompletionMap
            K L v U (eC x)) := by
      symm
      exact
        finitePlaceAdicCompletionMap_comp
          K L' (M := L) v U.1 U'.1 U.2 hU'L hU'K (eC x)
    _ = eE' (algebraMap E E' (algebraMap C E x)) := by
      change
        _ =
          eE'
            (eE'.symm
              (finitePlaceAdicCompletionMap
                L L' U.1 ⟨U'.1, hU'L⟩
                (eE (algebraMap C E x))))
      rw [eE'.apply_symm_apply, hLowerBase]

omit [IsAbelianGalois K L] in
open scoped Classical in
private theorem finitePlaceArtinLocalizedCompletion_globalEmbedding
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [NumberField L]
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w)
    (x : L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
    letI hwK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    letI : SMul K w.1.Completion := hwK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI hwK' :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K') w'.1
    letI : SMul K' w'.1.Completion := hwK'.toSMul
    letI : Algebra vK'.Completion w'.1.Completion :=
      AbsoluteValue.completionAlgebra vK' w'.1 w'.2
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let E' := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK' w'
    letI : Algebra E E' :=
      (finitePlaceArtinLocalizedCompletionRingHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W w w' hcentres).toAlgebra
    algebraMap E E'
        (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 x) =
      AbsoluteValue.toAlgebraicLocalization
        vK' w'.1 w'.2 (algebraMap L L' x) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hvK' : vK'.IsNontrivial :=
    RayClass.adicAbv_isNontrivial W
  let hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hwK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let hwK' :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K') w'.1
  let : SMul K' w'.1.Completion := hwK'.toSMul
  let : Algebra vK'.Completion w'.1.Completion :=
    AbsoluteValue.completionAlgebra vK' w'.1 w'.2
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let E' := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK' w'
  let : Algebra E E' :=
    (finitePlaceArtinLocalizedCompletionRingHom
      (K := K) (L := L) (K' := K') (L' := L')
      v W w w' hcentres).toAlgebra
  let U :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v w
  let U' :=
    finitePlaceExtensionEquivAbove
      (K := K') (L := L') W w'
  have hU'L : finitePlaceBelow (K := L) U'.1 = U.1 := by
    simpa only [U, U', finitePlaceExtensionEquivAbove_coe] using hcentres
  let eE :
      E ≃+* U.1.adicCompletion L :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK hvK w).toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w)
  let eE' :
      E' ≃+* U'.1.adicCompletion L' :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK' hvK' w').toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K') (L := L') W w')
  have hLowerConcrete :
      eE
          (AbsoluteValue.toAlgebraicLocalization
            vK w.1 w.2 x) =
        FinitePlace.embedding U.1 x := by
    exact (congrArg (finitePlaceExtensionAdicCompletionRingEquiv v w)
      (localizedCompletionEquivCompletion_coe vK hvK w _)).trans
      (finitePlaceExtensionAdicCompletionRingEquiv_toCompletion v w x)
  have hUpperConcrete :
      eE'
          (AbsoluteValue.toAlgebraicLocalization
            vK' w'.1 w'.2 (algebraMap L L' x)) =
        FinitePlace.embedding U'.1 (algebraMap L L' x) := by
    exact (congrArg (finitePlaceExtensionAdicCompletionRingEquiv W w')
      (localizedCompletionEquivCompletion_coe vK' hvK' w' _)).trans
      (finitePlaceExtensionAdicCompletionRingEquiv_toCompletion W w' (algebraMap L L' x))
  apply eE'.injective
  change
    eE'
        (eE'.symm
          (finitePlaceAdicCompletionMap
            L L' U.1 ⟨U'.1, hU'L⟩
            (eE
              (AbsoluteValue.toAlgebraicLocalization
                vK w.1 w.2 x)))) =
      eE'
        (AbsoluteValue.toAlgebraicLocalization
          vK' w'.1 w'.2 (algebraMap L L' x))
  rw [eE'.apply_symm_apply, hLowerConcrete, hUpperConcrete]
  change
    finitePlaceAdicCompletionMap
        L L' U.1 ⟨U'.1, hU'L⟩
        (x : U.1.adicCompletion L) =
      (algebraMap L L' x : U'.1.adicCompletion L')
  exact finitePlaceAdicCompletionMap_coe L L' U.1 ⟨U'.1, hU'L⟩ x

open scoped Classical in
/-- Localized automorphisms with the completion tower hidden behind one named
type. -/
noncomputable abbrev finitePlaceArtinLocalizedAutomorphism
    (F M : Type) [Field F] [NumberField F]
    [Field M] [NumberField M] [Algebra F M]
    (v : HeightOneSpectrum (𝓞 F))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v) M) : Type :=
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let E := finitePlaceArtinLocalizedCompletion F M v w
  letI : Algebra vF.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra (K := F) (L := M) v w
  E ≃ₐ[vF.Completion] E

open scoped Classical in
/-- Restriction of localized automorphisms across a finite-place square with
different base fields. -/
noncomputable def finitePlaceCrossLocalRestrictionMonoidHom
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [NumberField L]
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w) :
    finitePlaceArtinLocalizedAutomorphism K' L' W w' →*
      finitePlaceArtinLocalizedAutomorphism K L v w := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let C := vK.Completion
  let D := vK'.Completion
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let E' := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK' w'
  letI : Algebra C E :=
    finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := L) v w
  letI : Algebra D E' :=
    finitePlaceLocalArtinLocalizedAlgebra (K := K') (L := L') W w'
  let lowerGlobalAlgebra : Algebra K E :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
  let upperGlobalAlgebra : Algebra K' E' :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK' w'
  letI : Algebra C D :=
    (finitePlaceArtinRelativeCompletionRingHom
      (K := K) (K' := K') v W hW).toAlgebra
  let derivedStructures :
      PProd (Algebra E E') (Normal C E) := by
    letI : Algebra K E := lowerGlobalAlgebra
    letI : Algebra K' E' := upperGlobalAlgebra
    let upperAlgebra : Algebra E E' :=
      (finitePlaceArtinLocalizedCompletionRingHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W w w' hcentres).toAlgebra
    letI : FiniteDimensional C E :=
      finitePlaceLocalArtinFiniteDimensional (K := K) (L := L) v w
    letI : IsAbelianGalois C E :=
      finitePlaceLocalArtinIsAbelianGalois (K := K) (L := L) v w
        (inferInstance : FiniteDimensional K L)
    letI hGaloisE : IsGalois C E :=
      (inferInstance : IsAbelianGalois C E).toIsGalois
    exact ⟨upperAlgebra, hGaloisE.to_normal⟩
  letI : Algebra E E' := derivedStructures.fst
  letI : Algebra C E' :=
    ((algebraMap D E').comp (algebraMap C D)).toAlgebra
  letI : IsScalarTower C D E' :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower C E E' :=
    IsScalarTower.of_algebraMap_eq' <| by
      apply RingHom.ext
      intro x
      exact
        finitePlaceArtinLocalizedCompletion_towerPoint
          (K := K) (L := L) (K' := K') (L' := L')
          v W hW w w' hcentres x
  letI : Normal C E := derivedStructures.snd
  exact
    (AlgEquiv.restrictNormalHom E).comp
      (AlgEquiv.restrictScalarsHom C)

open scoped Classical in
private theorem finitePlaceDecompositionEquiv_symm_action
    {F M : Type}
    [Field F] [Field M] [Algebra F M] [IsGalois F M]
    (vF : AbsoluteValue F ℝ)
    (hvF : vF.IsNontrivial)
    (wF : AbsoluteValueExtension vF M)
    (tau :
      letI hwF :=
        AbsoluteValue.extensionCompletionAlgebra
          (K := F) wF.1
      letI : SMul F wF.1.Completion := hwF.toSMul
      letI : Algebra vF.Completion wF.1.Completion :=
        AbsoluteValue.completionAlgebra vF wF.1 wF.2
      let E :=
        AlgebraicNumberTheory.Valuations.LocalizedCompletion vF wF
      E ≃ₐ[vF.Completion] E)
    (z : M) :
    letI hwF :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := F) wF.1
    letI : SMul F wF.1.Completion := hwF.toSMul
    letI : Algebra vF.Completion wF.1.Completion :=
      AbsoluteValue.completionAlgebra vF wF.1 wF.2
    let E :=
      AlgebraicNumberTheory.Valuations.LocalizedCompletion vF wF
    let e :
        absoluteValueDecompositionGroup F wF.1 ≃*
          (E ≃ₐ[vF.Completion] E) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vF hvF wF
    let embedding : M →+* E :=
      AbsoluteValue.toAlgebraicLocalization vF wF.1 wF.2
    embedding (((e.symm tau).1 : M ≃ₐ[F] M) z) =
      tau (embedding z) := by
  let hwF :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := F) wF.1
  let : SMul F wF.1.Completion := hwF.toSMul
  let : Algebra vF.Completion wF.1.Completion :=
    AbsoluteValue.completionAlgebra vF wF.1 wF.2
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vF wF
  let e :
      absoluteValueDecompositionGroup F wF.1 ≃*
        (E ≃ₐ[vF.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vF hvF wF
  let embedding : M →+* E :=
    AbsoluteValue.toAlgebraicLocalization vF wF.1 wF.2
  calc
    embedding (((e.symm tau).1 : M ≃ₐ[F] M) z) =
        e (e.symm tau) (embedding z) := by
      rw [
        localizationRamificationGroups_decompositionGroupEquiv_toLocalization]
    _ = tau (embedding z) := by
      rw [e.apply_symm_apply]

open scoped Classical in
private theorem finitePlaceCrossDecompositionTransport_core
    {K K' L L' C D E E' : Type}
    [Field K] [Field K'] [Field L] [Field L']
    [Field C] [Field D] [Field E] [Field E']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra K L] [Algebra L L'] [IsScalarTower K L L']
    [Normal K L]
    [Algebra C D] [Algebra D E'] [Algebra C E']
    [IsScalarTower C D E']
    [Algebra C E] [Algebra E E'] [IsScalarTower C E E']
    [Normal C E]
    (phiLower : (E ≃ₐ[C] E) → (L ≃ₐ[K] L))
    (phiUpper : (E' ≃ₐ[D] E') → (L' ≃ₐ[K'] L'))
    (lowerEmbedding : L →+* E)
    (upperEmbedding : L' →+* E')
    (hEmbedding : ∀ z : L,
      algebraMap E E' (lowerEmbedding z) =
        upperEmbedding (algebraMap L L' z))
    (hUpperAction : ∀ (tau : E' ≃ₐ[D] E') (z : L'),
      upperEmbedding (phiUpper tau z) =
        tau (upperEmbedding z))
    (hLowerAction : ∀ (tau : E ≃ₐ[C] E) (z : L),
      tau (lowerEmbedding z) =
        lowerEmbedding (phiLower tau z))
    (tauUpper : E' ≃ₐ[D] E') :
    AlgEquiv.restrictNormalHom L
        (AlgEquiv.restrictScalarsHom K (phiUpper tauUpper)) =
      phiLower
        (AlgEquiv.restrictNormalHom E
          (AlgEquiv.restrictScalarsHom C tauUpper)) := by
  let tauLower :=
    AlgEquiv.restrictNormalHom E
      (AlgEquiv.restrictScalarsHom C tauUpper)
  apply AlgEquiv.ext
  intro z
  apply (algebraMap L L').injective
  apply upperEmbedding.injective
  calc
    upperEmbedding
        (algebraMap L L'
          ((AlgEquiv.restrictNormalHom L
            (AlgEquiv.restrictScalarsHom K
              (phiUpper tauUpper))) z)) =
      upperEmbedding
        (phiUpper tauUpper (algebraMap L L' z)) := by
      exact congrArg upperEmbedding
        (AlgEquiv.restrictNormal_commutes
          (AlgEquiv.restrictScalarsHom K
            (phiUpper tauUpper)) L z)
    _ = tauUpper
        (upperEmbedding (algebraMap L L' z)) :=
      hUpperAction tauUpper (algebraMap L L' z)
    _ = tauUpper
        (algebraMap E E' (lowerEmbedding z)) := by
      rw [hEmbedding]
    _ = algebraMap E E'
        (tauLower (lowerEmbedding z)) := by
      exact
        (AlgEquiv.restrictNormal_commutes
          (AlgEquiv.restrictScalarsHom C tauUpper)
          E (lowerEmbedding z)).symm
    _ = algebraMap E E'
        (lowerEmbedding (phiLower tauLower z)) := by
      rw [hLowerAction]
    _ = upperEmbedding
        (algebraMap L L' (phiLower tauLower z)) := by
      rw [hEmbedding]

open scoped Classical in
/-- Restriction through the completed local square agrees with restriction of
the corresponding global decomposition-group automorphisms. -/
theorem finitePlaceCrossDecompositionTransport
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [NumberField L]
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w)
    (tauUpper : finitePlaceArtinLocalizedAutomorphism K' L' W w') :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (finitePlaceLocalToGlobalMonoidHom
          (K := K') (L := L') W w' tauUpper) =
      finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w
        (finitePlaceCrossLocalRestrictionMonoidHom
          (K := K) (L := L) (K' := K') (L' := L')
          v W hW w w' hcentres tauUpper) := by
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let hvK' : vK'.IsNontrivial :=
      RayClass.adicAbv_isNontrivial W
    let C := vK.Completion
    let D := vK'.Completion
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let E' := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK' w'
    let : Algebra C E :=
      finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := L) v w
    let : Algebra D E' :=
      finitePlaceLocalArtinLocalizedAlgebra (K := K') (L := L') W w'
    let : Algebra K E :=
      LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
    let : Algebra K' E' :=
      LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK' w'
    let : Algebra C D :=
      (finitePlaceArtinRelativeCompletionRingHom
        (K := K) (K' := K') v W hW).toAlgebra
    let : Algebra E E' :=
      (finitePlaceArtinLocalizedCompletionRingHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W w w' hcentres).toAlgebra
    let : Algebra C E' :=
      ((algebraMap D E').comp (algebraMap C D)).toAlgebra
    let : IsScalarTower C D E' :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower C E E' :=
      IsScalarTower.of_algebraMap_eq' <| by
        apply RingHom.ext
        intro x
        exact
          finitePlaceArtinLocalizedCompletion_towerPoint
            (K := K) (L := L) (K' := K') (L' := L')
            v W hW w w' hcentres x
    let : FiniteDimensional C E :=
      finitePlaceLocalArtinFiniteDimensional (K := K) (L := L) v w
    let : IsAbelianGalois C E :=
      finitePlaceLocalArtinIsAbelianGalois (K := K) (L := L) v w
        (inferInstance : FiniteDimensional K L)
    let hGaloisE : IsGalois C E :=
      (inferInstance : IsAbelianGalois C E).toIsGalois
    let : Normal C E := hGaloisE.to_normal
    let eLower :
        absoluteValueDecompositionGroup K w.1 ≃*
          (E ≃ₐ[C] E) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w
    let eUpper :
        absoluteValueDecompositionGroup K' w'.1 ≃*
          (E' ≃ₐ[D] E') :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK' hvK' w'
    let lowerEmbedding : L →+* E :=
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
    let upperEmbedding : L' →+* E' :=
      AbsoluteValue.toAlgebraicLocalization vK' w'.1 w'.2
    have hEmbedding (x : L) :
        algebraMap E E' (lowerEmbedding x) =
          upperEmbedding (algebraMap L L' x) := by
      exact
        finitePlaceArtinLocalizedCompletion_globalEmbedding
          (K := K) (L := L) (K' := K') (L' := L')
          v W w w' hcentres x
    have hUpperAction
        (tau : E' ≃ₐ[D] E') (z : L') :
        upperEmbedding
            (((eUpper.symm tau).1 : L' ≃ₐ[K'] L') z) =
          tau (upperEmbedding z) := by
      exact
        finitePlaceDecompositionEquiv_symm_action
          vK' hvK' w' tau z
    have hLowerAction
        (tau : E ≃ₐ[C] E) (z : L) :
        tau (lowerEmbedding z) =
          lowerEmbedding
            (((eLower.symm tau).1 : L ≃ₐ[K] L) z) := by
      exact
        (finitePlaceDecompositionEquiv_symm_action
          vK hvK w tau z).symm
    change
      ((AlgEquiv.restrictNormalHom L)
        ((AlgEquiv.restrictScalarsHom K)
          ((eUpper.symm tauUpper).1 : L' ≃ₐ[K'] L'))) =
        ((eLower.symm
          (AlgEquiv.restrictNormalHom E
            ((AlgEquiv.restrictScalarsHom C) tauUpper))).1 :
          L ≃ₐ[K] L)
    exact
      finitePlaceCrossDecompositionTransport_core
        (fun tau => ((eLower.symm tau).1 : L ≃ₐ[K] L))
        (fun tau => ((eUpper.symm tau).1 : L' ≃ₐ[K'] L'))
        lowerEmbedding upperEmbedding hEmbedding
        hUpperAction hLowerAction tauUpper

end Reciprocity
end GlobalClassFieldTheory
