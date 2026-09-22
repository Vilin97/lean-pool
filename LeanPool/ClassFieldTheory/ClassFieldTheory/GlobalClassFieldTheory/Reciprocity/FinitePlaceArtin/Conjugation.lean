/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
/-!
# Conjugation of finite-place Artin homomorphisms

This module identifies localized completions associated with conjugate extensions and proves
  conjugation invariance of the resulting finite-place Artin map.
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
/-- The algebraic localizations belonging to conjugate extensions of a
finite place are identified by the induced equivalence of completions. -/
noncomputable def finitePlaceConjugateLocalizedCompletionAlgEquiv
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    Ewc ≃ₐ[vK.Completion] Ew := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wc := absoluteValueExtensionConjugate vK w g
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  letI hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hwK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  letI hwcK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wc.1
  letI : SMul K wc.1.Completion := hwcK.toSMul
  letI : Algebra vK.Completion wc.1.Completion :=
    AbsoluteValue.completionAlgebra vK wc.1 wc.2
  let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
  let eCompletion : wc.1.Completion ≃ₐ[vK.Completion]
      w.1.Completion :=
    { LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv
        vK w g with
      commutes' :=
        LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_algebraMap
          vK w g }
  let e : Ewc ≃ₐ[vK.Completion] Ew :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK hvK wc).trans
      (eCompletion.trans
        (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
          vK hvK w).symm)
  exact e

omit [IsAbelianGalois K L] in
open scoped Classical in
/-- The conjugate-localization equivalence carries the canonical
embedding of `L` to the conjugate of that embedding. -/
theorem finitePlaceConjugateLocalizedCompletionAlgEquiv_toAlgebraicLocalization
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) (x : L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g
        (AbsoluteValue.toAlgebraicLocalization
          vK wc.1 wc.2 x) =
      AbsoluteValue.toAlgebraicLocalization
        vK w.1 w.2 (g x) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wc := absoluteValueExtensionConjugate vK w g
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hwK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let hwcK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wc.1
  let : SMul K wc.1.Completion := hwcK.toSMul
  let : Algebra vK.Completion wc.1.Completion :=
    AbsoluteValue.completionAlgebra vK wc.1 wc.2
  apply
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
      vK hvK w).injective
  change
    LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv
        vK w g
        (AbsoluteValue.toCompletion wc.1 x) =
      AbsoluteValue.toCompletion w.1 (g x)
  exact
    LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_toCompletion
      vK w g x

omit [IsAbelianGalois K L] in
open scoped Classical in
/-- The inverse conjugate-localization equivalence carries the
canonical embedding back along the inverse global automorphism. -/
theorem
    finitePlaceConjugateLocalizedCompletionAlgEquiv_symm_toAlgebraicLocalization
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) (x : L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    (finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g).symm
        (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 x) =
      AbsoluteValue.toAlgebraicLocalization
        vK wc.1 wc.2 (g.symm x) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wc := absoluteValueExtensionConjugate vK w g
  let hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hwK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let hwcK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wc.1
  let : SMul K wc.1.Completion := hwcK.toSMul
  let : Algebra vK.Completion wc.1.Completion :=
    AbsoluteValue.completionAlgebra vK wc.1 wc.2
  let e :=
    finitePlaceConjugateLocalizedCompletionAlgEquiv
      (K := K) (L := L) v w g
  apply e.injective
  rw [e.apply_symm_apply,
    finitePlaceConjugateLocalizedCompletionAlgEquiv_toAlgebraicLocalization,
    g.apply_symm_apply]

open scoped Classical in
/-- Conjugation of a place intertwines the two localization
decomposition-group identifications on each local automorphism. -/
theorem finitePlaceDecompositionTransport_conjugate_apply
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    let e :=
      finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g
    let eDw :
        absoluteValueDecompositionGroup K w.1 ≃*
          (Ew ≃ₐ[vK.Completion] Ew) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w
    let eDwc :
        absoluteValueDecompositionGroup K wc.1 ≃*
          (Ewc ≃ₐ[vK.Completion] Ewc) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK wc
    ∀ tauC : Ewc ≃ₐ[vK.Completion] Ewc,
      (absoluteValueDecompositionGroup K wc.1).subtype
          (eDwc.symm tauC) =
        (absoluteValueDecompositionGroup K w.1).subtype
          (eDw.symm (AlgEquiv.autCongr e tauC)) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wc := absoluteValueExtensionConjugate vK w g
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hwK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let hwcK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wc.1
  let : SMul K wc.1.Completion := hwcK.toSMul
  let : Algebra vK.Completion wc.1.Completion :=
    AbsoluteValue.completionAlgebra vK wc.1 wc.2
  let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
  let e :=
    finitePlaceConjugateLocalizedCompletionAlgEquiv
      (K := K) (L := L) v w g
  let eDw :
      absoluteValueDecompositionGroup K w.1 ≃*
        (Ew ≃ₐ[vK.Completion] Ew) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let eDwc :
      absoluteValueDecompositionGroup K wc.1 ≃*
        (Ewc ≃ₐ[vK.Completion] Ewc) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK wc
  change
    ∀ tauC : Ewc ≃ₐ[vK.Completion] Ewc,
      (absoluteValueDecompositionGroup K wc.1).subtype
          (eDwc.symm tauC) =
        (absoluteValueDecompositionGroup K w.1).subtype
          (eDw.symm (AlgEquiv.autCongr e tauC))
  intro tauC
  let tau := AlgEquiv.autCongr e tauC
  let rhoC : absoluteValueDecompositionGroup K wc.1 :=
    eDwc.symm tauC
  let rho : absoluteValueDecompositionGroup K w.1 :=
    eDw.symm tau
  change (rhoC.1 : L ≃ₐ[K] L) =
    (rho.1 : L ≃ₐ[K] L)
  apply AlgEquiv.ext
  intro z
  apply
    (AbsoluteValue.toAlgebraicLocalization
      vK w.1 w.2).injective
  have hcomm :
      g ((rhoC.1 : L ≃ₐ[K] L) (g.symm z)) =
        (rhoC.1 : L ≃ₐ[K] L) z := by
    have hg :
        g * (rhoC.1 : L ≃ₐ[K] L) =
          (rhoC.1 : L ≃ₐ[K] L) * g :=
      (inferInstance :
        IsMulCommutative (L ≃ₐ[K] L)).is_comm.comm _ _
    calc
      g ((rhoC.1 : L ≃ₐ[K] L) (g.symm z)) =
          (g * (rhoC.1 : L ≃ₐ[K] L)) (g.symm z) := rfl
      _ = ((rhoC.1 : L ≃ₐ[K] L) * g) (g.symm z) :=
        DFunLike.congr_fun hg (g.symm z)
      _ = (rhoC.1 : L ≃ₐ[K] L) (g (g.symm z)) := rfl
      _ = (rhoC.1 : L ≃ₐ[K] L) z := by
        rw [g.apply_symm_apply]
  calc
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
        ((rhoC.1 : L ≃ₐ[K] L) z) =
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
        (g ((rhoC.1 : L ≃ₐ[K] L) (g.symm z))) := by
          rw [hcomm]
    _ = e
        (AbsoluteValue.toAlgebraicLocalization vK wc.1 wc.2
          ((rhoC.1 : L ≃ₐ[K] L) (g.symm z))) := by
          rw [
            finitePlaceConjugateLocalizedCompletionAlgEquiv_toAlgebraicLocalization]
    _ = e
        (eDwc rhoC
          (AbsoluteValue.toAlgebraicLocalization
            vK wc.1 wc.2 (g.symm z))) := by
          rw [localizationRamificationGroups_decompositionGroupEquiv_toLocalization]
    _ = e
        (tauC
          (AbsoluteValue.toAlgebraicLocalization
            vK wc.1 wc.2 (g.symm z))) := by
          rw [eDwc.apply_symm_apply]
    _ = (AlgEquiv.autCongr e tauC)
        (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 z) := by
          change
            e
                (tauC
                  (AbsoluteValue.toAlgebraicLocalization
                    vK wc.1 wc.2 (g.symm z))) =
              e
                (tauC
                  (e.symm
                    (AbsoluteValue.toAlgebraicLocalization
                      vK w.1 w.2 z)))
          rw [
            finitePlaceConjugateLocalizedCompletionAlgEquiv_symm_toAlgebraicLocalization]
    _ = tau
        (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 z) := by
          rfl
    _ = eDw rho
        (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 z) := by
          rw [eDw.apply_symm_apply]
    _ = AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
        ((rho.1 : L ≃ₐ[K] L) z) := by
          rw [localizationRamificationGroups_decompositionGroupEquiv_toLocalization]

open scoped Classical in
/-- Conjugation of a place intertwines the two localization
decomposition-group identifications after inclusion in the global
Galois group. -/
theorem finitePlaceDecompositionTransport_conjugate
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    let e :=
      finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g
    let eDw :
        absoluteValueDecompositionGroup K w.1 ≃*
          (Ew ≃ₐ[vK.Completion] Ew) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w
    let eDwc :
        absoluteValueDecompositionGroup K wc.1 ≃*
          (Ewc ≃ₐ[vK.Completion] Ewc) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK wc
    (absoluteValueDecompositionGroup K wc.1).subtype.comp
        eDwc.symm.toMonoidHom =
      ((absoluteValueDecompositionGroup K w.1).subtype.comp
          eDw.symm.toMonoidHom).comp
        (AlgEquiv.autCongr e).toMonoidHom := by
  apply MonoidHom.ext
  intro tauC
  exact
    finitePlaceDecompositionTransport_conjugate_apply
      (K := K) (L := L) v w g tauC

open scoped Classical in
/-- Local Artin maps are natural under the localized-completion
equivalence induced by conjugating a finite-place extension. -/
theorem finitePlaceLocalArtinMonoidHom_conjugate
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    let e :=
      finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g
    (AlgEquiv.autCongr e).toMonoidHom.comp
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v wc) =
      finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wc := absoluteValueExtensionConjugate vK w g
  let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
  let : Algebra vK.Completion Ew :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  let : Algebra vK.Completion Ewc :=
    finitePlaceLocalArtinLocalizedAlgebra v wc
  let : FiniteDimensional vK.Completion Ew :=
    finitePlaceLocalArtinFiniteDimensional v w
  let : FiniteDimensional vK.Completion Ewc :=
    finitePlaceLocalArtinFiniteDimensional v wc
  let : IsAbelianGalois vK.Completion Ew :=
    finitePlaceLocalArtinIsAbelianGalois v w
      (inferInstance : FiniteDimensional K L)
  let : IsAbelianGalois vK.Completion Ewc :=
    finitePlaceLocalArtinIsAbelianGalois v wc
      (inferInstance : FiniteDimensional K L)
  let : ValuativeRel vK.Completion :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField vK.Completion :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let e :=
    finitePlaceConjugateLocalizedCompletionAlgEquiv
      (K := K) (L := L) v w g
  let eK :
      vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  change
    (AlgEquiv.autCongr e).toMonoidHom.comp
        ((LocalClassFieldTheory.abelianLocalArtinMonoidHom
          vK.Completion Ewc).comp eK.symm.toMonoidHom) =
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom
        vK.Completion Ew).comp eK.symm.toMonoidHom
  exact
    congrArg (fun f => f.comp eK.symm.toMonoidHom)
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom_autCongr
        vK.Completion Ewc Ew e)

open scoped Classical in
/-- Conjugating the chosen extension of a finite place does not change
its Artin homomorphism when the global extension is abelian. -/
theorem finitePlaceArtinMonoidHomOfExtension_conjugate
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v
        (absoluteValueExtensionConjugate
          (NumberField.HeightOneSpectrum.adicAbv K v) w g) =
      finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wc := absoluteValueExtensionConjugate vK w g
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hwK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let hwcK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wc.1
  let : SMul K wc.1.Completion := hwcK.toSMul
  let : Algebra vK.Completion wc.1.Completion :=
    AbsoluteValue.completionAlgebra vK wc.1 wc.2
  let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
  let e :=
    finitePlaceConjugateLocalizedCompletionAlgEquiv
      (K := K) (L := L) v w g
  let eDw :
      absoluteValueDecompositionGroup K w.1 ≃*
        (Ew ≃ₐ[vK.Completion] Ew) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let eDwc :
      absoluteValueDecompositionGroup K wc.1 ≃*
        (Ewc ≃ₐ[vK.Completion] Ewc) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK wc
  have htransport :=
    finitePlaceDecompositionTransport_conjugate
      (K := K) (L := L) v w g
  have hlocal :=
    finitePlaceLocalArtinMonoidHom_conjugate
      (K := K) (L := L) v w g
  change
    ((absoluteValueDecompositionGroup K wc.1).subtype.comp
        eDwc.symm.toMonoidHom).comp
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v wc) =
      ((absoluteValueDecompositionGroup K w.1).subtype.comp
        eDw.symm.toMonoidHom).comp
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v w)
  calc
    _ =
        (((absoluteValueDecompositionGroup K w.1).subtype.comp
            eDw.symm.toMonoidHom).comp
          (AlgEquiv.autCongr e).toMonoidHom).comp
            (finitePlaceLocalArtinMonoidHom
              (K := K) (L := L) v wc) :=
      congrArg
        (fun f => f.comp
          (finitePlaceLocalArtinMonoidHom
            (K := K) (L := L) v wc))
        htransport
    _ =
        ((absoluteValueDecompositionGroup K w.1).subtype.comp
          eDw.symm.toMonoidHom).comp
            ((AlgEquiv.autCongr e).toMonoidHom.comp
              (finitePlaceLocalArtinMonoidHom
                (K := K) (L := L) v wc)) := by
      rfl
    _ = _ := by rw [hlocal]

open scoped Classical in
/-- The finite-place Artin homomorphism is independent of the chosen
extension of the base place in an abelian extension. -/
theorem finitePlaceArtinMonoidHomOfExtension_eq
    (v : HeightOneSpectrum (𝓞 K))
    (w w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w =
      finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w' := by
  let : NumberField L := NumberField.of_module_finite K L
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let W' :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w'
  let : Finite (L ≃ₐ[K] L) :=
    IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let :
      IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  let : W.asIdeal.LiesOver v.asIdeal :=
    ⟨(finitePlaceExtensionCentreIdeal_under
      (K := K) (L := L) v w).symm⟩
  let : W'.asIdeal.LiesOver v.asIdeal :=
    ⟨(finitePlaceExtensionCentreIdeal_under
      (K := K) (L := L) v w').symm⟩
  obtain ⟨g, hg⟩ :=
    HilbertRamification.Dedekind.exists_smul_eq_of_isGaloisGroup
      v.asIdeal W.asIdeal W'.asIdeal (L ≃ₐ[K] L)
  have hplace :
      finitePlaceEquiv K L g W = W' := by
    apply HeightOneSpectrum.ext
    rw [finitePlaceEquiv_asIdeal]
    exact hg
  have hconjugate :
      absoluteValueExtensionConjugate
          (NumberField.HeightOneSpectrum.adicAbv K v)
          w g⁻¹ =
        w' := by
    apply
      finitePlaceExtensionCentre_injective
        (K := K) (L := L) v
    rw [finitePlaceExtensionCentre_conjugate]
    simpa only [inv_inv, W, W'] using hplace
  rw [← hconjugate]
  exact
    (finitePlaceArtinMonoidHomOfExtension_conjugate
      (K := K) (L := L) v w g⁻¹).symm

end Reciprocity
end GlobalClassFieldTheory
