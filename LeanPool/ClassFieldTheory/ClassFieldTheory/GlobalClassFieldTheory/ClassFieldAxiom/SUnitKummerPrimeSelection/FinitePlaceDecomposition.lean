/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Galois.CyclicPrimeSubextension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
/-!
# Finite-place decomposition groups in Galois towers

This file relates relative and absolute finite-place decomposition groups and
proves cyclicity for the decomposition group at a chosen unramified place.
The results are independent of the S-unit Kummer construction.
-/

open scoped NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

open scoped Classical in
/-- Full relative decomposition above `q` puts every
`M`-automorphism inside the global chosen decomposition group below
`q`. -/
theorem
    restrictAutomorphismScalars_mem_finitePlaceDecompositionGroup_of_relative_eq_top
    {F M L : Type}
    [Field F] [NumberField F]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra F M] [Algebra M L] [Algebra F L]
    [IsScalarTower F M L]
    [FiniteDimensional F L]
    [IsGalois F L] [IsGalois M L]
    [IsMulCommutative (L ≃ₐ[F] L)]
    (p : HeightOneSpectrum (𝓞 F))
    (q : HeightOneSpectrum (𝓞 M))
    (hq :
      _root_.finitePlaceBelow (K := F) q = p)
    (hfull :
      _root_.finitePlaceDecompositionGroup
          (K := M) (L := L) q =
        ⊤)
    (tau : L ≃ₐ[M] L) :
    RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
          (K := F) (M := M) tau ∈
      _root_.finitePlaceDecompositionGroup
        (K := F) (L := L) p := by
  let wM :=
    _root_.chosenFinitePlaceExtension
      (L := L) q
  let W :=
    _root_.finitePlaceExtensionCentre
      (K := M) (L := L) q wM
  have hWM :
      _root_.finitePlaceBelow (K := M) W =
        q :=
    _root_.finitePlaceBelow_finitePlaceExtensionCentre
      (K := M) (L := L) q wM
  have hWF :
      _root_.finitePlaceBelow (K := F) W =
        p := by
    rw [
      ← _root_.finitePlaceBelow_finitePlaceBelow
        (K := F) (M := M) (L := L) W,
      hWM, hq]
  let Wp :
      {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := F) W = p} :=
    ⟨W, hWF⟩
  let wF :=
    (_root_.finitePlaceExtensionEquivAbove
      (K := F) (L := L) p).symm Wp
  have hwFcentre :
      _root_.finitePlaceExtensionCentre
          (K := F) (L := L) p wF =
        W := by
    have hh :=
      (_root_.finitePlaceExtensionEquivAbove
        (K := F) (L := L) p).apply_symm_apply Wp
    simpa only [wF, Wp, finitePlaceExtensionEquivAbove_coe] using
      congrArg
        (fun T :
          {W : HeightOneSpectrum (𝓞 L) //
            _root_.finitePlaceBelow (K := F) W = p} =>
          (T : HeightOneSpectrum (𝓞 L))) hh
  have hequiv : wM.1.IsEquiv wF.1 := by
    apply
      _root_.finitePlaceExtensions_isEquiv_of_centres_eq
        (F := M) (M := F) q p wM wF
    simpa [W] using hwFcentre.symm
  have hDvalue :
      HilbertRamification.absoluteValueDecompositionGroup
          F wM.1 =
        HilbertRamification.absoluteValueDecompositionGroup
          F wF.1 :=
    absoluteValueDecompositionGroup_eq_of_absoluteValue_isEquiv
      wM.1 wF.1 hequiv
  have hDchosen :
      HilbertRamification.absoluteValueDecompositionGroup
          F wF.1 =
        HilbertRamification.absoluteValueDecompositionGroup
          F
          (_root_.chosenFinitePlaceExtension
            (L := L) p).1 :=
    absoluteValueDecompositionGroup_eq_of_exactExtensions_of_isMulCommutative
      (HeightOneSpectrum.adicAbv F p)
      (RayClass.adicAbv_isNontrivial p)
      wF
      (_root_.chosenFinitePlaceExtension
        (L := L) p)
  have htauM :
      tau ∈
        HilbertRamification.absoluteValueDecompositionGroup
          M wM.1 := by
    change
      tau ∈
        _root_.finitePlaceDecompositionGroup
          (K := M) (L := L) q
    rw [hfull]
    exact Subgroup.mem_top tau
  let rho :=
    RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
      (K := F) (M := M) tau
  have hrho :
      rho ∈
        HilbertRamification.absoluteValueDecompositionGroup
          F wM.1 := by
    exact
      (HilbertRamification.decompositionGroupRestriction_mem_absoluteValueDecompositionGroup_restrictScalars_iff
          (K := F) (M := M) wM.1 tau).mpr htauM
  change
    rho ∈
      HilbertRamification.absoluteValueDecompositionGroup
        F
        (_root_.chosenFinitePlaceExtension
          (L := L) p).1
  rw [← hDchosen, ← hDvalue]
  exact hrho

open scoped Classical in
/-- An unramified chosen finite-place decomposition group is cyclic. -/
theorem finitePlaceDecompositionGroup_isCyclic_of_chosenUnramified
    {F L : Type}
    [Field F] [NumberField F]
    [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    (v : HeightOneSpectrum (𝓞 F))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := F) (L := L) v) :
    IsCyclic
      (_root_.finitePlaceDecompositionGroup
        (K := F) (L := L) v) := by
  let Fv :=
    _root_.ChosenFinitePlaceBaseCompletion
      (K := F) v
  let Lv :=
    _root_.ChosenFinitePlaceLocalizedCompletion
      (K := F) (L := L) v
  let :
      LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        Fv Lv := by
    simpa [Fv, Lv, _root_.ChosenFinitePlaceIsUnramified] using hunram
  let eLocal :
      _root_.finitePlaceDecompositionGroup
          (K := F) (L := L) v ≃*
        (Lv ≃ₐ[Fv] Lv) :=
    HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut
        (HeightOneSpectrum.adicAbv F v)
        (RayClass.adicAbv_isNontrivial v)
        (_root_.chosenFinitePlaceExtension
          (L := L) v)
  exact
    eLocal.isCyclic.mpr
      (LocalFieldTheory.isCyclic_galoisGroup_of_unramifiedValuation
        Fv Lv)

end GlobalClassFieldTheory.ClassFieldAxiom
