/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.FinitePlaceLocalGlobal
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization
/-!
# Finite-place Kummer root-character comparison

The comparison is compiled through an S-valued map from the chosen global
Kummer extension to the Kummer extension chosen over the completion.  The
localized completion and its instance tower occur only in the provider body
which proves compatibility with the two Artin actions.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory

variable (K : Type) [Field K] [NumberField K]

private theorem nthRootsSubgroupMap_comp_eq_unitsMap
    {F C L S : Type} [Field F] [Field C] [Field L] [Field S]
    [Algebra F C] [Algebra F L] [Algebra C S]
    (m : ℕ) (x : nthRootsSubgroup F m) (f : L →+* S)
    (hmap : ∀ y : F,
      algebraMap C S (algebraMap F C y) = f (algebraMap F L y)) :
    (nthRootsSubgroupMap C S m
        (nthRootsSubgroupMap F C m x)).1 =
      Units.map f.toMonoidHom
        (Units.map (algebraMap F L).toMonoidHom x.1) := by
  apply Units.ext
  exact hmap (x.1 : F)

private theorem rootQuotient_map_ringHom_of_action
    {F G L S : Type} [Field F] [Field G] [Field L] [Field S]
    [Algebra F L] [Algebra G S]
    (f : L →+* S) (u : Lˣ) (sigmaL : Gal(L/F)) (sigmaS : Gal(S/G))
    (haction : sigmaS (f (u : L)) = f (sigmaL (u : L))) :
    Units.map f.toMonoidHom
        (rootQuotient (K := F) (L := L) u sigmaL) =
      rootQuotient (K := G) (L := S)
        (Units.map f.toMonoidHom u) sigmaS := by
  apply Units.ext
  simp only [rootQuotient, Units.val_div_eq_div_val, Units.coe_map]
  change f (sigmaL (u : L) / (u : L)) =
    sigmaS (f (u : L)) / f (u : L)
  rw [map_div₀, haction]

/-- The normalized finite-place Artin action commutes with algebraic
localization.  This generic boundary is compiled before the Kummer-specific
comparison, so the latter never re-elaborates the localization tower. -/
private theorem finitePlaceArtin_apply_localized
    {L : Type} [Field L] [Algebra K L]
    [hKLfinite : FiniteDimensional K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) (z : L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    (@abelianLocalArtinMonoidHom vK.Completion E
      (inferInstance : Field vK.Completion) (inferInstance : Field E)
      (finitePlaceLocalArtinLocalizedAlgebra v w)
      (finitePlaceLocalArtinCompletionValuativeRel v)
      (inferInstance : TopologicalSpace vK.Completion)
      (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
      (finitePlaceLocalArtinFiniteDimensional v w)
      (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
      (finitePlaceLocalArtinInput v x))
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 z) =
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
        ((finitePlaceArtinMonoidHomOfExtension
          (K := K) (L := L) v w x) z) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : Algebra vK.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  let sigmaE := @abelianLocalArtinMonoidHom vK.Completion E
    (inferInstance : Field vK.Completion) (inferInstance : Field E)
    (finitePlaceLocalArtinLocalizedAlgebra v w)
    (finitePlaceLocalArtinCompletionValuativeRel v)
    (inferInstance : TopologicalSpace vK.Completion)
    (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
    (finitePlaceLocalArtinFiniteDimensional v w)
    (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
    (finitePlaceLocalArtinInput v x)
  let sigmaG := finitePlaceArtinMonoidHomOfExtension
    (K := K) (L := L) v w x
  have hfactor :=
    finitePlaceArtinMonoidHomOfExtension_apply_normalized
      (K := K) (L := L) v w x
  let hvK : vK.IsNontrivial := RayClass.adicAbv_isNontrivial v
  let eD : absoluteValueDecompositionGroup K w.1 ≃* Gal(E/vK.Completion) :=
    decompositionGroupEquivAlgebraicLocalizationAut vK hvK w
  let delta : absoluteValueDecompositionGroup K w.1 := eD.symm sigmaE
  have hdelta : eD delta = sigmaE := eD.apply_symm_apply sigmaE
  change sigmaE (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 z) =
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (sigmaG z)
  dsimp only [sigmaG]
  rw [hfactor]
  rw [← hdelta]
  exact localizationRamificationGroups_decompositionGroupEquiv_toLocalization
    vK hvK w delta z

private noncomputable def finitePlaceKummerGlobalArtinAutomorphism
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    Gal((chosenSimpleKummerExtension K n hnK b)/K) := by
  let L := chosenSimpleKummerExtension K n hnK b
  let x : (v.adicCompletion K)ˣ :=
    Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a
  letI : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  exact finitePlaceArtinMonoidHomOfExtension
    (K := K) (L := L) v w x

private noncomputable def finitePlaceKummerLocalArtinAutomorphism
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    let C := finitePlaceKummerBaseCompletion K v
    let S := finitePlaceKummerLocalExtension K n hnK v b
    Gal(S/C) := by
  let C := finitePlaceKummerBaseCompletion K v
  let hnC := finitePlaceHilbert_natCast_ne_zero K n hnK v
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty K n hmu v
  let aC := finitePlaceHilbert_completionUnit K v a
  let bC := finitePlaceHilbert_completionUnit K v b
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact
    LocalClassFieldTheory.Kummer.chosenSimpleKummerNormResidueAutomorphism
      C n hnC hmuC bC aC

/-- The canonical map from the chosen global Kummer extension to the
intrinsic Kummer extension over the finite-place completion. -/
private noncomputable def finitePlaceKummerGlobalToLocalRingHom
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    chosenSimpleKummerExtension K n hnK b →+*
      finitePlaceKummerLocalExtension K n hnK v b := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  letI : Algebra C E :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  let e := finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
  let toE : L →+* E :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  exact e.symm.toRingHom.comp toE

/-- The global-to-local Kummer map extends the canonical scalar map from
the number field through its finite-place completion. -/
private theorem finitePlaceKummerGlobalToLocalRingHom_commutes
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b))
    (y : K) :
    let C := finitePlaceKummerBaseCompletion K v
    let L := chosenSimpleKummerExtension K n hnK b
    let S := finitePlaceKummerLocalExtension K n hnK v b
    algebraMap C S (algebraMap K C y) =
      finitePlaceKummerGlobalToLocalRingHom K n hnK hmu v b w
        (algebraMap K L y) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  let : Algebra C E :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  let e := finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
  let toE : L →+* E :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  change algebraMap C S (algebraMap K C y) =
    e.symm (toE (algebraMap K L y))
  apply e.injective
  calc
    e (algebraMap C S (algebraMap K C y)) =
        algebraMap C E (algebraMap K C y) := e.commutes _
    _ = toE (algebraMap K L y) :=
      (AbsoluteValue.toAlgebraicLocalization_algebraMap
        vK w.1 w.2 y).symm
    _ = e (e.symm (toE (algebraMap K L y))) :=
      (e.apply_symm_apply _).symm

private noncomputable def
    finitePlaceKummerTransportedLocalizedArtinAutomorphism
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    let C := finitePlaceKummerBaseCompletion K v
    let S := finitePlaceKummerLocalExtension K n hnK v b
    Gal(S/C) := by
  let C := finitePlaceKummerBaseCompletion K v
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  let aC := finitePlaceHilbert_completionUnit K v a
  letI : FiniteDimensional K
      (chosenSimpleKummerExtension K n hnK b) :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K
      (chosenSimpleKummerExtension K n hnK b) :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  letI : Algebra C E :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  letI : FiniteDimensional C E :=
    finitePlaceKummerLocalizedFiniteDimensional K n hnK v b w
  letI : IsAbelianGalois C E :=
    finitePlaceLocalArtinIsAbelianGalois
      (K := K) (L := chosenSimpleKummerExtension K n hnK b) v w
        (chosenSimpleKummerExtension_finiteDimensional K n hnK b)
  let e := finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
  let sigmaE : Gal(E/C) := abelianLocalArtinMonoidHom C E aC
  exact (AlgEquiv.autCongr e).symm sigmaE

private theorem finitePlaceKummerLocalArtin_eq_transported
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    finitePlaceKummerLocalArtinAutomorphism
        K n hnK hmu v a b =
      finitePlaceKummerTransportedLocalizedArtinAutomorphism
        K n hnK hmu v a b w := by
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  let hnC := finitePlaceHilbert_natCast_ne_zero K n hnK v
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty K n hmu v
  let aC := finitePlaceHilbert_completionUnit K v a
  let bC := finitePlaceHilbert_completionUnit K v b
  let : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : FiniteDimensional C S :=
    finitePlaceKummerLocalFiniteDimensional K n hnK v b
  let : IsAbelianGalois C S :=
    chosenSimpleKummerExtension_isAbelianGalois C n hnC hmuC bC
  let : Algebra C E :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  let : FiniteDimensional C E :=
    finitePlaceKummerLocalizedFiniteDimensional K n hnK v b w
  let : IsAbelianGalois C E :=
    finitePlaceLocalArtinIsAbelianGalois
      (K := K) (L := L) v w
        (chosenSimpleKummerExtension_finiteDimensional K n hnK b)
  let e := finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
  let sigmaS : Gal(S/C) := abelianLocalArtinMonoidHom C S aC
  let sigmaE : Gal(E/C) := abelianLocalArtinMonoidHom C E aC
  let tauS : Gal(S/C) := (AlgEquiv.autCongr e).symm sigmaE
  have hArtinEquiv :
      (AlgEquiv.autCongr e).toMonoidHom sigmaS = sigmaE := by
    have h := DFunLike.congr_fun
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom_autCongr
        C S E e) aC
    simpa only [sigmaS, sigmaE, MonoidHom.comp_apply] using h
  have hsigma : sigmaS = tauS := by
    apply (AlgEquiv.autCongr e).injective
    calc
      (AlgEquiv.autCongr e) sigmaS = sigmaE := hArtinEquiv
      _ = (AlgEquiv.autCongr e) tauS := by
        exact ((AlgEquiv.autCongr e).apply_symm_apply sigmaE).symm
  change sigmaS = tauS
  exact hsigma

private noncomputable def localizedDirectActionValue
    {L : Type} [Field L] [Algebra K L]
    [hfin : FiniteDimensional K L] [hab : IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (y : (NumberField.HeightOneSpectrum.adicAbv K v).Completionˣ)
    (t : AlgebraicNumberTheory.Valuations.LocalizedCompletion
      (NumberField.HeightOneSpectrum.adicAbv K v) w) :
    AlgebraicNumberTheory.Valuations.LocalizedCompletion
      (NumberField.HeightOneSpectrum.adicAbv K v) w := by
  let C := (NumberField.HeightOneSpectrum.adicAbv K v).Completion
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion
    (NumberField.HeightOneSpectrum.adicAbv K v) w
  let _ : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  let _ : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let _ : Algebra C E := finitePlaceLocalArtinLocalizedAlgebra v w
  let _ : FiniteDimensional C E := finitePlaceLocalArtinFiniteDimensional v w
  let _ : IsAbelianGalois C E :=
    finitePlaceLocalArtinIsAbelianGalois v w hfin
  exact abelianLocalArtinMonoidHom C E y t

private noncomputable def finitePlaceKummerCommonRootAction
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    finitePlaceKummerLocalExtension K n hnK v b := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  let aC := finitePlaceHilbert_completionUnit K v a
  letI : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  letI : Algebra C E :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  letI : FiniteDimensional C E :=
    finitePlaceKummerLocalizedFiniteDimensional K n hnK v b w
  letI : IsAbelianGalois C E :=
    finitePlaceLocalArtinIsAbelianGalois
      (K := K) (L := L) v w
        (chosenSimpleKummerExtension_finiteDimensional K n hnK b)
  let e := finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
  let toE : L →+* E :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let uL : Lˣ := chosenSimpleKummerRootUnit K n hnK b
  exact e.symm (localizedDirectActionValue K v w aC (toE (uL : L)))

private theorem finitePlaceKummerTransportedArtinRoot_eq_common
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    let f := finitePlaceKummerGlobalToLocalRingHom
      K n hnK hmu v b w
    let uL := chosenSimpleKummerRootUnit K n hnK b
    finitePlaceKummerTransportedLocalizedArtinAutomorphism
        K n hnK hmu v a b w (f uL) =
      finitePlaceKummerCommonRootAction
        K n hnK hmu v a b w := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  let aC := finitePlaceHilbert_completionUnit K v a
  let : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : Algebra C E :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  let : FiniteDimensional C E :=
    finitePlaceKummerLocalizedFiniteDimensional K n hnK v b w
  let : IsAbelianGalois C E :=
    finitePlaceLocalArtinIsAbelianGalois
      (K := K) (L := L) v w
        (chosenSimpleKummerExtension_finiteDimensional K n hnK b)
  let e := finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
  let toE : L →+* E :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let f : L →+* S := e.symm.toRingHom.comp toE
  let uL : Lˣ := chosenSimpleKummerRootUnit K n hnK b
  let sigmaE : Gal(E/C) := abelianLocalArtinMonoidHom C E aC
  let directE : E := localizedDirectActionValue K v w aC (toE (uL : L))
  let tauS : Gal(S/C) := (AlgEquiv.autCongr e).symm sigmaE
  have hArtinEquiv :
      (AlgEquiv.autCongr e).toMonoidHom tauS = sigmaE :=
    (AlgEquiv.autCongr e).apply_symm_apply sigmaE
  have hlocalNaturality (y : S) :
      e (tauS y) = sigmaE (e y) := by
    calc
      e (tauS y) =
          ((AlgEquiv.autCongr e).toMonoidHom tauS) (e y) := by
        change e (tauS y) = e (tauS (e.symm (e y)))
        exact
          (congrArg (fun t : S => e (tauS t))
            (e.symm_apply_apply y)).symm
      _ = sigmaE (e y) :=
        congrArg (fun tau : Gal(E/C) => tau (e y)) hArtinEquiv
  have hef : e (f (uL : L)) = toE (uL : L) := by
    change e (e.symm (toE (uL : L))) = toE (uL : L)
    exact e.apply_symm_apply _
  have hdirect : directE = sigmaE (toE (uL : L)) := rfl
  change tauS (f (uL : L)) = e.symm directE
  apply e.injective
  calc
    e (tauS (f (uL : L))) = sigmaE (e (f (uL : L))) :=
      hlocalNaturality (f (uL : L))
    _ = sigmaE (toE (uL : L)) :=
      congrArg (fun t : E => sigmaE t) hef
    _ = directE := hdirect.symm
    _ = e (e.symm directE) := (e.apply_symm_apply _).symm

private noncomputable def localizedInputActionValue
    {L : Type} [Field L] [Algebra K L]
    [hfin : FiniteDimensional K L] [hab : IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) (z : L) :
    AlgebraicNumberTheory.Valuations.LocalizedCompletion
      (NumberField.HeightOneSpectrum.adicAbv K v) w :=
  localizedDirectActionValue K v w (finitePlaceLocalArtinInput v x)
    (AbsoluteValue.toAlgebraicLocalization
      (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2 z)

private noncomputable def localizedGlobalActionValue
    {L : Type} [Field L] [Algebra K L]
    [hfin : FiniteDimensional K L] [hab : IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) (z : L) :
    AlgebraicNumberTheory.Valuations.LocalizedCompletion
      (NumberField.HeightOneSpectrum.adicAbv K v) w :=
  AbsoluteValue.toAlgebraicLocalization
    (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2
    (finitePlaceArtinMonoidHomOfExtension
      (K := K) (L := L) v w x z)

private theorem localizedActionValue_eq
    {L : Type} [Field L] [Algebra K L]
    [hfin : FiniteDimensional K L] [hab : IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) (z : L) :
    localizedInputActionValue K v w x z =
      localizedGlobalActionValue K v w x z := by
  exact finitePlaceArtin_apply_localized (K := K) (L := L) v w x z

private noncomputable def finitePlaceKummerLocalizedInputValue
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    finitePlaceKummerLocalizedCompletion K n hnK v b w :=
  localizedInputActionValue (K := K)
    (hfin := chosenSimpleKummerExtension_finiteDimensional K n hnK b)
    (hab := chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b)
    v w
    (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
    (chosenSimpleKummerRootUnit K n hnK b :
      chosenSimpleKummerExtension K n hnK b)

private noncomputable def finitePlaceKummerLocalizedGlobalValue
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    finitePlaceKummerLocalizedCompletion K n hnK v b w :=
  localizedGlobalActionValue (K := K)
    (hfin := chosenSimpleKummerExtension_finiteDimensional K n hnK b)
    (hab := chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b)
    v w
    (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
    (chosenSimpleKummerRootUnit K n hnK b :
      chosenSimpleKummerExtension K n hnK b)

private theorem finitePlaceKummerLocalizedValue_eq
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    finitePlaceKummerLocalizedInputValue K n hnK hmu v a b w =
      finitePlaceKummerLocalizedGlobalValue K n hnK hmu v a b w := by
  exact localizedActionValue_eq
    (K := K) (L := chosenSimpleKummerExtension K n hnK b)
    (hfin := chosenSimpleKummerExtension_finiteDimensional K n hnK b)
    (hab := chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b)
    v w
    (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
    (chosenSimpleKummerRootUnit K n hnK b :
      chosenSimpleKummerExtension K n hnK b)

private theorem finitePlaceKummerCommonImage_eq_localizedInputValue
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
        (finitePlaceKummerCommonRootAction K n hnK hmu v a b w) =
      finitePlaceKummerLocalizedInputValue K n hnK hmu v a b w := by
  let L := chosenSimpleKummerExtension K n hnK b
  let C := finitePlaceKummerBaseCompletion K v
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  let _ : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let _ : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let _ : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  let _ : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let _ : Algebra C E := finitePlaceKummerLocalizedAlgebra K n hnK v b w
  let _ : FiniteDimensional C E :=
    finitePlaceKummerLocalizedFiniteDimensional K n hnK v b w
  let _ : IsAbelianGalois C E :=
    finitePlaceLocalArtinIsAbelianGalois
      (K := K) (L := L) v w
        (chosenSimpleKummerExtension_finiteDimensional K n hnK b)
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let x : (v.adicCompletion K)ˣ :=
    Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a
  let aC : Cˣ := finitePlaceHilbert_completionUnit K v a
  let z : L := chosenSimpleKummerRootUnit K n hnK b
  let toE : L →+* E := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let e := finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
  let directFor (y : Cˣ) : E :=
    localizedDirectActionValue K v w y (toE z)
  have hinput : finitePlaceLocalArtinInput v x = aC :=
    finitePlaceLocalArtinInput_globalUnit K v a
  calc
    e (finitePlaceKummerCommonRootAction K n hnK hmu v a b w) =
        directFor aC := by
      change e (e.symm (directFor aC)) = directFor aC
      exact e.apply_symm_apply _
    _ = directFor (finitePlaceLocalArtinInput v x) :=
      congrArg directFor hinput.symm
    _ = finitePlaceKummerLocalizedInputValue K n hnK hmu v a b w := by
      unfold finitePlaceKummerLocalizedInputValue localizedInputActionValue
      rfl

private theorem finitePlaceKummerGlobalArtin_localized_action
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
        (finitePlaceKummerCommonRootAction K n hnK hmu v a b w) =
      AbsoluteValue.toAlgebraicLocalization
        (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2
        (finitePlaceKummerGlobalArtinAutomorphism
          K n hnK hmu v a b w
          (chosenSimpleKummerRootUnit K n hnK b)) := by
  calc
    finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
        (finitePlaceKummerCommonRootAction K n hnK hmu v a b w) =
        finitePlaceKummerLocalizedInputValue K n hnK hmu v a b w :=
      finitePlaceKummerCommonImage_eq_localizedInputValue
        K n hnK hmu v a b w
    _ = finitePlaceKummerLocalizedGlobalValue K n hnK hmu v a b w :=
      finitePlaceKummerLocalizedValue_eq K n hnK hmu v a b w
    _ = AbsoluteValue.toAlgebraicLocalization
        (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2
        (finitePlaceKummerGlobalArtinAutomorphism
          K n hnK hmu v a b w
          (chosenSimpleKummerRootUnit K n hnK b)) := rfl

private theorem finitePlaceKummerCommonRootAction_eq_global
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    let f := finitePlaceKummerGlobalToLocalRingHom
      K n hnK hmu v b w
    let uL := chosenSimpleKummerRootUnit K n hnK b
    finitePlaceKummerCommonRootAction
        K n hnK hmu v a b w =
      f (finitePlaceKummerGlobalArtinAutomorphism
        K n hnK hmu v a b w uL) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  let aC := finitePlaceHilbert_completionUnit K v a
  let x : (v.adicCompletion K)ˣ :=
    Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a
  let hKLfinite : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let hKLgalois : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : Algebra C E :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  let : FiniteDimensional C E :=
    finitePlaceKummerLocalizedFiniteDimensional K n hnK v b w
  let : IsAbelianGalois C E :=
    finitePlaceLocalArtinIsAbelianGalois
      (K := K) (L := L) v w hKLfinite
  let e := finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
  let toE : L →+* E :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let f : L →+* S := e.symm.toRingHom.comp toE
  let uL : Lˣ := chosenSimpleKummerRootUnit K n hnK b
  let sigmaG : Gal(L/K) :=
    finitePlaceArtinMonoidHomOfExtension
      (K := K) (L := L) v w x
  have himage := finitePlaceKummerGlobalArtin_localized_action
    K n hnK hmu v a b w
  apply e.injective
  calc
    e (finitePlaceKummerCommonRootAction
        K n hnK hmu v a b w) =
        toE (sigmaG (uL : L)) := himage
    _ = e (f (sigmaG (uL : L))) := by
      change toE (sigmaG (uL : L)) =
        e (e.symm (toE (sigmaG (uL : L))))
      exact (e.apply_symm_apply _).symm

private theorem finitePlaceKummerTransportedArtin_root_action
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    let f := finitePlaceKummerGlobalToLocalRingHom
      K n hnK hmu v b w
    let uL := chosenSimpleKummerRootUnit K n hnK b
    finitePlaceKummerTransportedLocalizedArtinAutomorphism
        K n hnK hmu v a b w (f uL) =
      f (finitePlaceKummerGlobalArtinAutomorphism
        K n hnK hmu v a b w uL) :=
  (finitePlaceKummerTransportedArtinRoot_eq_common
    K n hnK hmu v a b w).trans
      (finitePlaceKummerCommonRootAction_eq_global
        K n hnK hmu v a b w)

/-- The global-to-local Kummer map intertwines the two Artin actions on the
chosen Kummer root. -/
private theorem finitePlaceKummerGlobalToLocalRingHom_artin_action
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    let f := finitePlaceKummerGlobalToLocalRingHom
      K n hnK hmu v b w
    let uL := chosenSimpleKummerRootUnit K n hnK b
    finitePlaceKummerLocalArtinAutomorphism
        K n hnK hmu v a b (f uL) =
      f (finitePlaceKummerGlobalArtinAutomorphism
        K n hnK hmu v a b w uL) := by
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let f : L →+* S :=
    finitePlaceKummerGlobalToLocalRingHom K n hnK hmu v b w
  let uL : Lˣ := chosenSimpleKummerRootUnit K n hnK b
  let sigmaS : Gal(S/C) :=
    finitePlaceKummerLocalArtinAutomorphism
      K n hnK hmu v a b
  let tauS : Gal(S/C) :=
    finitePlaceKummerTransportedLocalizedArtinAutomorphism
      K n hnK hmu v a b w
  let sigmaG : Gal(L/K) :=
    finitePlaceKummerGlobalArtinAutomorphism
      K n hnK hmu v a b w
  calc
    sigmaS (f (uL : L)) = tauS (f (uL : L)) :=
      congrArg (fun tau : Gal(S/C) => tau (f (uL : L)))
        (finitePlaceKummerLocalArtin_eq_transported
          K n hnK hmu v a b w)
    _ = f (sigmaG (uL : L)) :=
      finitePlaceKummerTransportedArtin_root_action
        K n hnK hmu v a b w

/-- The image of the chosen global Kummer root has the same prescribed
power as the root chosen intrinsically over the completion. -/
private theorem finitePlaceKummerGlobalToLocalRingHom_root_pow
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    let C := finitePlaceKummerBaseCompletion K v
    let S := finitePlaceKummerLocalExtension K n hnK v b
    let f := finitePlaceKummerGlobalToLocalRingHom
      K n hnK hmu v b w
    let uL := chosenSimpleKummerRootUnit K n hnK b
    let bC := finitePlaceHilbert_completionUnit K v b
    Units.map f.toMonoidHom uL ^ (n : ℕ) =
      Units.map (algebraMap C S).toMonoidHom bC := by
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let f := finitePlaceKummerGlobalToLocalRingHom
    K n hnK hmu v b w
  let uL : Lˣ := chosenSimpleKummerRootUnit K n hnK b
  let bC := finitePlaceHilbert_completionUnit K v b
  have huLpow :
      uL ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom b :=
    chosenSimpleKummerRootUnit_pow K n hnK b
  calc
    Units.map f.toMonoidHom uL ^ (n : ℕ) =
        Units.map f.toMonoidHom (uL ^ (n : ℕ)) :=
      (map_pow (Units.map f.toMonoidHom) uL (n : ℕ)).symm
    _ = Units.map f.toMonoidHom
        (Units.map (algebraMap K L).toMonoidHom b) := by rw [huLpow]
    _ = Units.map (algebraMap C S).toMonoidHom bC := by
      apply Units.ext
      change f (algebraMap K L (b : K)) =
        algebraMap C S (algebraMap K C (b : K))
      exact
        (finitePlaceKummerGlobalToLocalRingHom_commutes
          K n hnK hmu v b w (b : K)).symm

private theorem finitePlaceKummerMappedGlobalCharacter_units
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    let L := chosenSimpleKummerExtension K n hnK b
    let f := finitePlaceKummerGlobalToLocalRingHom
      K n hnK hmu v b w
    let uL := chosenSimpleKummerRootUnit K n hnK b
    let sigmaG := finitePlaceKummerGlobalArtinAutomorphism
      K n hnK hmu v a b w
    let globalValue :=
      finitePlaceKummerRootCharacterOfExtension
        K n hnK hmu v a b w
    Units.map f.toMonoidHom
        (Units.map (algebraMap K L).toMonoidHom globalValue.1) =
      Units.map f.toMonoidHom
        (rootQuotient (K := K) (L := L) uL sigmaG) := by
  let L := chosenSimpleKummerExtension K n hnK b
  let f := finitePlaceKummerGlobalToLocalRingHom
    K n hnK hmu v b w
  let uL : Lˣ := chosenSimpleKummerRootUnit K n hnK b
  let sigmaG : Gal(L/K) :=
    finitePlaceKummerGlobalArtinAutomorphism
      K n hnK hmu v a b w
  let globalValue :=
    finitePlaceKummerRootCharacterOfExtension
      K n hnK hmu v a b w
  have hglobalMap :
      nthRootsSubgroupMap K L (n : ℕ) globalValue =
        chosenSimpleKummerRootCharacter K n hnK hmu b sigmaG := by
    unfold globalValue sigmaG
    unfold finitePlaceKummerRootCharacterOfExtension
      finitePlaceKummerGlobalArtinAutomorphism
    exact
      (nthRootsSubgroupEquivOfPrimitiveRoots K L n hmu).apply_symm_apply _
  have hglobalRoot :
      Units.map (algebraMap K L).toMonoidHom globalValue.1 =
        rootQuotient (K := K) (L := L) uL sigmaG := by
    have h := congrArg Subtype.val hglobalMap
    rw [chosenSimpleKummerRootCharacter_apply] at h
    exact h
  exact congrArg (Units.map f.toMonoidHom) hglobalRoot

private theorem finitePlaceKummerRootQuotient_eq_local
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    let C := finitePlaceKummerBaseCompletion K v
    let L := chosenSimpleKummerExtension K n hnK b
    let S := finitePlaceKummerLocalExtension K n hnK v b
    let f := finitePlaceKummerGlobalToLocalRingHom
      K n hnK hmu v b w
    let uL := chosenSimpleKummerRootUnit K n hnK b
    let uS := chosenSimpleKummerRootUnit C
      n (finitePlaceHilbert_natCast_ne_zero K n hnK v)
        (finitePlaceHilbert_completionUnit K v b)
    let sigmaG := finitePlaceKummerGlobalArtinAutomorphism
      K n hnK hmu v a b w
    let sigmaS := finitePlaceKummerLocalArtinAutomorphism
      K n hnK hmu v a b
    Units.map f.toMonoidHom
        (rootQuotient (K := K) (L := L) uL sigmaG) =
      rootQuotient (K := C) (L := S) uS sigmaS := by
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let hnC := finitePlaceHilbert_natCast_ne_zero K n hnK v
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty K n hmu v
  let bC := finitePlaceHilbert_completionUnit K v b
  let f : L →+* S :=
    finitePlaceKummerGlobalToLocalRingHom K n hnK hmu v b w
  let uL : Lˣ := chosenSimpleKummerRootUnit K n hnK b
  let uS : Sˣ := chosenSimpleKummerRootUnit C n hnC bC
  let sigmaG : Gal(L/K) :=
    finitePlaceKummerGlobalArtinAutomorphism
      K n hnK hmu v a b w
  let sigmaS : Gal(S/C) :=
    finitePlaceKummerLocalArtinAutomorphism
      K n hnK hmu v a b
  have haction :
      sigmaS (f (uL : L)) = f (sigmaG (uL : L)) :=
    finitePlaceKummerGlobalToLocalRingHom_artin_action
      K n hnK hmu v a b w
  have hrootMap :
      Units.map f.toMonoidHom
          (rootQuotient (K := K) (L := L) uL sigmaG) =
        rootQuotient (K := C) (L := S)
          (Units.map f.toMonoidHom uL) sigmaS :=
    rootQuotient_map_ringHom_of_action
      f uL sigmaG sigmaS haction
  have huTpow :
      Units.map f.toMonoidHom uL ^ (n : ℕ) =
        Units.map (algebraMap C S).toMonoidHom bC :=
    finitePlaceKummerGlobalToLocalRingHom_root_pow
      K n hnK hmu v b w
  have huSpow :
      uS ^ (n : ℕ) = Units.map (algebraMap C S).toMonoidHom bC :=
    chosenSimpleKummerRootUnit_pow C n hnC bC
  have hchoice :
      rootQuotient (K := C) (L := S)
          (Units.map f.toMonoidHom uL) sigmaS =
        rootQuotient (K := C) (L := S) uS sigmaS :=
    rootQuotient_eq_of_same_pow_of_primitiveRoots
      C n hmuC bC (Units.map f.toMonoidHom uL) uS
        huTpow huSpow sigmaS
  exact hrootMap.trans hchoice

private theorem finitePlaceKummerLocalHilbert_units
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    let C := finitePlaceKummerBaseCompletion K v
    let S := finitePlaceKummerLocalExtension K n hnK v b
    let uS := chosenSimpleKummerRootUnit C
      n (finitePlaceHilbert_natCast_ne_zero K n hnK v)
        (finitePlaceHilbert_completionUnit K v b)
    let sigmaS := finitePlaceKummerLocalArtinAutomorphism
      K n hnK hmu v a b
    Units.map (algebraMap C S).toMonoidHom
        (finitePlaceLocalHilbertSymbol K n hnK hmu v a b).1 =
      rootQuotient (K := C) (L := S) uS sigmaS := by
  let C := finitePlaceKummerBaseCompletion K v
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let hnC := finitePlaceHilbert_natCast_ne_zero K n hnK v
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty K n hmu v
  let aC := finitePlaceHilbert_completionUnit K v a
  let bC := finitePlaceHilbert_completionUnit K v b
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : FiniteDimensional C S :=
    finitePlaceKummerLocalFiniteDimensional K n hnK v b
  let : IsAbelianGalois C S :=
    chosenSimpleKummerExtension_isAbelianGalois C n hnC hmuC bC
  let uS : Sˣ := chosenSimpleKummerRootUnit C n hnC bC
  let sigmaS : Gal(S/C) :=
    finitePlaceKummerLocalArtinAutomorphism
      K n hnK hmu v a b
  let localValue :=
    LocalClassFieldTheory.Kummer.localHilbertSymbol
      C n hnC hmuC aC bC
  have hmap :=
    LocalClassFieldTheory.Kummer.localHilbertSymbol_map_eq_rootQuotient
      C n hnC hmuC aC bC
  have hroot :
      Units.map (algebraMap C S).toMonoidHom localValue.1 =
        rootQuotient (K := C) (L := S) uS sigmaS := by
    have h := congrArg Subtype.val hmap
    change
      Units.map (algebraMap C S).toMonoidHom localValue.1 =
        rootQuotient (K := C) (L := S) uS sigmaS at h
    exact h
  have hvalue :
      finitePlaceLocalHilbertSymbol K n hnK hmu v a b = localValue := by
    unfold finitePlaceLocalHilbertSymbol localValue
    rfl
  rw [hvalue]
  exact hroot

/-- For every extension of a finite place, the global Kummer root character
equals the finite-place Hilbert symbol. -/
theorem finitePlaceKummerRootCharacterOfExtension_localGlobal
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    finitePlaceKummerRootCharacterOfExtension
        K n hnK hmu v a b w =
      finitePlaceHilbertSymbol K n hnK hmu v a b := by
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let f : L →+* S :=
    finitePlaceKummerGlobalToLocalRingHom K n hnK hmu v b w
  let uL : Lˣ := chosenSimpleKummerRootUnit K n hnK b
  let sigmaG : Gal(L/K) :=
    finitePlaceKummerGlobalArtinAutomorphism
      K n hnK hmu v a b w
  let globalValue :=
    finitePlaceKummerRootCharacterOfExtension K n hnK hmu v a b w
  let localValue :=
    finitePlaceLocalHilbertSymbol K n hnK hmu v a b
  let uS : Sˣ := chosenSimpleKummerRootUnit C
    n (finitePlaceHilbert_natCast_ne_zero K n hnK v)
      (finitePlaceHilbert_completionUnit K v b)
  let sigmaS : Gal(S/C) :=
    finitePlaceKummerLocalArtinAutomorphism
      K n hnK hmu v a b
  apply nthRootsSubgroupMap_injective K C (n : ℕ)
  rw [finitePlaceHilbertSymbol_map_eq_localHilbertSymbol]
  apply nthRootsSubgroupMap_injective C S (n : ℕ)
  apply Subtype.ext
  change
    (nthRootsSubgroupMap C S (n : ℕ)
      (nthRootsSubgroupMap K C (n : ℕ) globalValue)).1 =
        (nthRootsSubgroupMap C S (n : ℕ) localValue).1
  calc
    (nthRootsSubgroupMap C S (n : ℕ)
        (nthRootsSubgroupMap K C (n : ℕ) globalValue)).1 =
      Units.map f.toMonoidHom
        (Units.map (algebraMap K L).toMonoidHom globalValue.1) :=
      nthRootsSubgroupMap_comp_eq_unitsMap
        (n : ℕ) globalValue f
          (finitePlaceKummerGlobalToLocalRingHom_commutes
            K n hnK hmu v b w)
    _ = Units.map f.toMonoidHom
        (rootQuotient (K := K) (L := L) uL sigmaG) :=
      finitePlaceKummerMappedGlobalCharacter_units
        K n hnK hmu v a b w
    _ = rootQuotient (K := C) (L := S) uS sigmaS :=
      finitePlaceKummerRootQuotient_eq_local
        K n hnK hmu v a b w
    _ = Units.map (algebraMap C S).toMonoidHom localValue.1 :=
      (finitePlaceKummerLocalHilbert_units
        K n hnK hmu v a b).symm
    _ = (nthRootsSubgroupMap C S (n : ℕ) localValue).1 := rfl

/-- The canonical finite-place Kummer root character is the finite-place
Hilbert symbol. -/
theorem finitePlaceKummerRootCharacter_localGlobal
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    finitePlaceKummerRootCharacter K n hnK hmu v a b =
      finitePlaceHilbertSymbol K n hnK hmu v a b := by
  let L := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let w := chosenFinitePlaceExtension (L := L) v
  calc
    finitePlaceKummerRootCharacter K n hnK hmu v a b =
        finitePlaceKummerRootCharacterOfExtension
          K n hnK hmu v a b w :=
      (finitePlaceKummerRootCharacterOfExtension_eq
        K n hnK hmu v a b w).symm
    _ = finitePlaceHilbertSymbol K n hnK hmu v a b :=
      finitePlaceKummerRootCharacterOfExtension_localGlobal
        K n hnK hmu v a b w

end Reciprocity
end GlobalClassFieldTheory
