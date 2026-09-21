/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.DecompositionFields
import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.FinitePlaceDecomposition
/-!
# The conclusion of S-unit Kummer prime selection

This file proves that the selected local power conditions cut out exactly
the finite Kummer radical and records the support-enlargement consequence
used by the global reciprocity argument.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section FinitePlaces

variable {K : Type} [Field K]
    [NumberField K]

/-- The chosen primes cut out exactly the Kummer radical of `E / K`: an
enlarged `S`-unit is a local `n`-th power at every chosen
prime if and only if it has an `n`-th root in `E`. -/
theorem
    sUnitLocalPowerKernel_sUnitKummerPrimeSet_eq_comap_sUnitFiniteKummerRadical
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let T :=
      sUnitKummerPrimeSet
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S
    sUnitLocalPowerKernel (K := K) n S' T =
      (sUnitFiniteKummerRadical
        (K := K) (L := E) n S').comap
          (SUnitGroup (K := K) S').subtype := by
  dsimp only
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let T :=
    sUnitKummerPrimeSet
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : Algebra E N :=
    enlargedSUnitKummerAlgebra
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG) S
  let : IsScalarTower K E N := by
    infer_instance
  change
    sUnitLocalPowerKernel (K := K) n S' T =
      (sUnitFiniteKummerRadical
        (K := K) (L := E) n S').comap
          (SUnitGroup (K := K) S').subtype
  ext x
  constructor
  · intro hx
    have hxLocal :
        ∀ w : T,
          Units.map
                (algebraMap K
                  ((w : HeightOneSpectrum (𝓞 K)).adicCompletion K)).toMonoidHom
                (x : Kˣ) ∈
            (powMonoidHom (n : ℕ) :
              ((w : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ →*
                ((w : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ).range :=
      (mem_sUnitLocalPowerKernel_iff
        (K := K) n S' T x).mp hx
    let aFull :
        (fullSUnitKummerSubgroup (K := K) n S').1 :=
      sUnitToFullSUnitKummerSubgroup
        (K := K) n S' x
    have haN :
        (x : Kˣ) ∈
          KummerTheory.finiteKummerRadicalSubgroup
            (K := K) (L := N) n :=
      KummerTheory.le_finiteKummerRadicalSubgroup_kummerRadicalExtension
        (K := K) (Omega := Omega) n hnK
        (fullSUnitKummerSubgroup (K := K) n S').1
        aFull.property
    obtain ⟨beta, hbeta⟩ :=
      (KummerTheory.mem_finiteKummerRadicalSubgroup_iff
        (K := K) (L := N) n).mp haN
    have hbetaCoordinate
        (i : Fin
          (sUnitKummerPrimeCount
            (K := K) E n hmu r S)) :
        (beta : N) ∈
          sUnitKummerCoordinateFixedField
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i := by
      let wi :=
        sUnitKummerChosenBasePlaces
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i
      have hwiT : wi ∈ T := by
        change
          wi ∈
            Finset.univ.image
              (sUnitKummerChosenBasePlaces
                (K := K) (Omega := Omega) E n hmu
                p v hp hv hn r eG S)
        exact
          Finset.mem_image.mpr
            ⟨i, Finset.mem_univ i, rfl⟩
      let wT : T := ⟨wi, hwiT⟩
      have hlocal :
              Units.map
                (algebraMap K (wi.adicCompletion K)).toMonoidHom
                (x : Kˣ) ∈
            (powMonoidHom (n : ℕ) :
              (wi.adicCompletion K)ˣ →*
                (wi.adicCompletion K)ˣ).range := by
        simpa [wT, wi] using hxLocal wT
      have hfixed :
          (beta : N) ∈
            IntermediateField.fixedField
              (HilbertRamification.absoluteValueDecompositionGroup K
                (_root_.chosenFinitePlaceExtension
                  (L := N) wi).1) :=
        (KummerTheory.finitePlaceKummerRadicand_mem_nthPowerSubgroup_iff_root_mem_decompositionFixedField
            (K := K) (L := N) wi n hmu (x : Kˣ) beta hbeta).mp
          hlocal
      rw [
        ← sUnitKummerChosenDecompositionField_eq_coordinateFixedField
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i]
      simpa only [_root_.finitePlaceDecompositionGroup] using hfixed
    let R :=
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod
          (K := K) E n r eG) S).ker
    let Fix : Subgroup R :=
      MulAction.stabilizer R (beta : N)
    have hgeneratorFix
        (i : Fin
          (sUnitKummerPrimeCount
            (K := K) E n hmu r S)) :
        sUnitKummerKernelGenerator
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i ∈
          Fix := by
      have hbi := hbetaCoordinate i
      change
        (beta : N) ∈
          IntermediateField.fixedField
            (Subgroup.zpowers
              ((sUnitKummerKernelGenerator
                  (K := K) (Omega := Omega) E n hmu
                  p v hp hv hn r eG S i :
                    R).1)) at hbi
      rw [IntermediateField.mem_fixedField_iff] at hbi
      have hfix :=
        hbi
          ((sUnitKummerKernelGenerator
              (K := K) (Omega := Omega) E n hmu
              p v hp hv hn r eG S i :
                R).1)
          (Subgroup.mem_zpowers
            ((sUnitKummerKernelGenerator
                (K := K) (Omega := Omega) E n hmu
                p v hp hv hn r eG S i :
                  R).1))
      rw [show Fix = MulAction.stabilizer R (beta : N) from rfl,
        MulAction.mem_stabilizer_iff]
      simpa only [
        MulAction.subgroup_smul_def,
        AlgEquiv.smul_def] using hfix
    have hspan :
        (⨆ i :
            Fin
              (sUnitKummerPrimeCount
                (K := K) E n hmu r S),
          Subgroup.zpowers
            (sUnitKummerKernelGenerator
              (K := K) (Omega := Omega) E n hmu
              p v hp hv hn r eG S i)) ≤
          Fix := by
      refine iSup_le ?_
      intro i
      exact Subgroup.zpowers_le.mpr (hgeneratorFix i)
    have hFixTop : Fix = ⊤ := by
      apply top_unique
      rw [
        ← iSup_zpowers_sUnitKummerKernelGenerator_eq_top
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S]
      exact hspan
    have hbetaKernel :
        (beta : N) ∈
          IntermediateField.fixedField
            (enlargedSUnitKummerRestrictionHom
              (K := K) (Omega := Omega) E n hmu
              (galois_pow_eq_one_of_equiv_pi_zmod
                (K := K) E n r eG) S).ker := by
      rw [IntermediateField.mem_fixedField_iff]
      intro sigma hsigma
      let sigmaR : R := ⟨sigma, hsigma⟩
      have hsigmaFix : sigmaR ∈ Fix := by
        rw [hFixTop]
        exact Subgroup.mem_top sigmaR
      have hfix :
          sigmaR • (beta : N) = (beta : N) := by
        exact
          MulAction.mem_stabilizer_iff.mp
            (show
              sigmaR ∈ MulAction.stabilizer R (beta : N) by
              simpa only [Fix] using hsigmaFix)
      simpa only [
        MulAction.subgroup_smul_def,
        AlgEquiv.smul_def] using hfix
    have hbetaEmbedded :
        (beta : N) ∈
          enlargedSUnitKummerEmbeddedExtension
            (K := K) (Omega := Omega) E n hmu
            (galois_pow_eq_one_of_equiv_pi_zmod
              (K := K) E n r eG) S := by
      rw [
        ← fixedField_enlargedSUnitKummerRestrictionHom_ker
          (K := K) (Omega := Omega) E n hmu
          (galois_pow_eq_one_of_equiv_pi_zmod
            (K := K) E n r eG) S]
      exact hbetaKernel
    change
      (beta : N) ∈ Set.range (algebraMap E N)
        at hbetaEmbedded
    obtain ⟨gamma, hgamma⟩ := hbetaEmbedded
    have hgamma_ne : gamma ≠ 0 := by
      intro hgammaZero
      apply beta.ne_zero
      calc
        (beta : N) = algebraMap E N gamma := hgamma.symm
        _ = 0 := by rw [hgammaZero, map_zero]
    let gammaUnit : Eˣ :=
      Units.mk0 gamma hgamma_ne
    change
      (x : Kˣ) ∈
        sUnitFiniteKummerRadical
          (K := K) (L := E) n S'
    apply
      (mem_sUnitFiniteKummerRadical_iff
        (K := K) (L := E) n S' (x : Kˣ)).mpr
    refine ⟨x.property, gammaUnit, ?_⟩
    apply Units.ext
    apply (algebraMap E N).injective
    change
      algebraMap E N (gamma ^ (n : ℕ)) =
        algebraMap E N
          (algebraMap K E ((x : Kˣ) : K))
    calc
      algebraMap E N (gamma ^ (n : ℕ)) =
          (beta : N) ^ (n : ℕ) := by
        rw [map_pow, hgamma]
      _ = algebraMap K N ((x : Kˣ) : K) := by
        simpa using congrArg Units.val hbeta
      _ =
          algebraMap E N
            (algebraMap K E ((x : Kˣ) : K)) := by
        rw [IsScalarTower.algebraMap_apply K E N]
  · intro hx
    change
      (x : Kˣ) ∈
        sUnitFiniteKummerRadical
          (K := K) (L := E) n S' at hx
    obtain ⟨_hxS, betaE, hbetaE⟩ :=
      (mem_sUnitFiniteKummerRadical_iff
        (K := K) (L := E) n S' (x : Kˣ)).mp hx
    let betaN : Nˣ :=
      Units.map (algebraMap E N).toMonoidHom betaE
    have hbetaN :
        betaN ^ (n : ℕ) =
          Units.map (algebraMap K N).toMonoidHom
            (x : Kˣ) := by
      calc
        betaN ^ (n : ℕ) =
            Units.map (algebraMap E N).toMonoidHom
              (betaE ^ (n : ℕ)) := by
          rw [map_pow]
        _ =
            Units.map (algebraMap E N).toMonoidHom
              (Units.map (algebraMap K E).toMonoidHom
                (x : Kˣ)) := by
          rw [hbetaE]
        _ =
            Units.map (algebraMap K N).toMonoidHom
              (x : Kˣ) := by
          apply Units.ext
          exact
            (IsScalarTower.algebraMap_apply
              K E N ((x : Kˣ) : K)).symm
    apply
      (mem_sUnitLocalPowerKernel_iff
        (K := K) n S' T x).mpr
    intro w
    have hw :
        (w : HeightOneSpectrum (𝓞 K)) ∈
          sUnitKummerPrimeSet
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S :=
      w.property
    rw [sUnitKummerPrimeSet, Finset.mem_image] at hw
    obtain ⟨i, _hi, hwi⟩ := hw
    have hbetaEmbedded :
        (betaN : N) ∈
          enlargedSUnitKummerEmbeddedExtension
            (K := K) (Omega := Omega) E n hmu
            (galois_pow_eq_one_of_equiv_pi_zmod
              (K := K) E n r eG) S := by
      change
        (betaN : N) ∈ Set.range (algebraMap E N)
      exact ⟨(betaE : E), rfl⟩
    have hbetaCoordinate :
        (betaN : N) ∈
          sUnitKummerCoordinateFixedField
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i := by
      exact
        enlargedSUnitKummerEmbeddedExtension_le_cyclicFixedField
          (K := K) (Omega := Omega) E n hmu
          (galois_pow_eq_one_of_equiv_pi_zmod
            (K := K) E n r eG) S
          (sUnitKummerKernelGenerator
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i)
          hbetaEmbedded
    have hbetaFixed :
        (betaN : N) ∈
          IntermediateField.fixedField
            (HilbertRamification.absoluteValueDecompositionGroup K
              (_root_.chosenFinitePlaceExtension
                (L := N)
                (sUnitKummerChosenBasePlaces
                  (K := K) (Omega := Omega) E n hmu
                  p v hp hv hn r eG S i)).1) := by
      have hdecomp :
          (betaN : N) ∈
            IntermediateField.fixedField
              (_root_.finitePlaceDecompositionGroup
                (K := K) (L := N)
                (sUnitKummerChosenBasePlaces
                  (K := K) (Omega := Omega) E n hmu
                  p v hp hv hn r eG S i)) := by
        rw [
          sUnitKummerChosenDecompositionField_eq_coordinateFixedField
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i]
        exact hbetaCoordinate
      simpa only [_root_.finitePlaceDecompositionGroup] using hdecomp
    have hlocal :=
      (KummerTheory.finitePlaceKummerRadicand_mem_nthPowerSubgroup_iff_root_mem_decompositionFixedField
          (K := K) (L := N)
          (sUnitKummerChosenBasePlaces
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i)
          n hmu (x : Kˣ) betaN hbetaN).mpr
        hbetaFixed
    rw [← hwi]
    exact hlocal

/-- Enlarging `S` by the radical supports preserves the idelic
factorization `I_K = I_K^S Kˣ`. -/
theorem supportedAt_sup_principalSubgroup_eq_top_of_enlargeByRadicalSupport
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS :
      IdeleGroup.supportedAt (K := K) (S : Set _) ⊔
        IdeleGroup.principalSubgroup K = ⊤) :
    IdeleGroup.supportedAt
          (K := K)
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := L) n hmu S : Set _) ⊔
        IdeleGroup.principalSubgroup K =
      ⊤ := by
  apply top_unique
  rw [← hS]
  apply sup_le
  · exact
      (IdeleGroup.supportedAt_mono
        (K := K)
        (show
          (S : Set (HeightOneSpectrum (𝓞 K))) ⊆
            (enlargeByFiniteKummerRadicalSupport
              (K := K) (L := L) n hmu S : Set _) by
          intro v hv
          exact subset_enlargeByFiniteKummerRadicalSupport
            (K := K) (L := L) n hmu S hv)).trans le_sup_left
  · exact le_sup_right

end FinitePlaces

end GlobalClassFieldTheory.ClassFieldAxiom
