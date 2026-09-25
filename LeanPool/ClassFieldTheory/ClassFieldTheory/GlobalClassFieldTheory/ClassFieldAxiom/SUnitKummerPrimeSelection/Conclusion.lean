/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.DecompositionFields
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.FinitePlaceDecomposition
/-!
# The conclusion of S-unit Kummer prime selection

This file proves that the selected local power conditions cut out exactly
the finite Kummer radical and records the support-enlargement consequence
used by the global reciprocity argument.
-/

@[expose] public section

open scoped NumberField IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section FinitePlaces

variable {K : Type} [Field K]
    [NumberField K]

omit [NumberField K] in
private theorem mem_fixedField_of_subgroup_generators
    {L : Type*} [Field L] [Algebra K L] {ι : Type*}
    (R : Subgroup Gal(L/K)) (g : ι → R)
    (hgen : (⨆ i, Subgroup.zpowers (g i)) = ⊤) (x : L)
    (hx : ∀ i, x ∈ IntermediateField.fixedField (Subgroup.zpowers (g i).1)) :
    x ∈ IntermediateField.fixedField R := by
  let H := MulAction.stabilizer R x
  have htop : H = ⊤ := by
    apply top_unique
    rw [← hgen]
    refine iSup_le fun i => Subgroup.zpowers_le.mpr ?_
    have hi := hx i
    rw [IntermediateField.mem_fixedField_iff] at hi
    have hfix := hi (g i).1 (Subgroup.mem_zpowers (g i).1)
    exact MulAction.mem_stabilizer_iff.mpr hfix
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have hmem : (⟨σ, hσ⟩ : R) ∈ H := htop ▸ Subgroup.mem_top _
  exact MulAction.mem_stabilizer_iff.mp hmem

omit [NumberField K] in
private theorem exists_unit_root_of_mem_algebraMap_range
    {E N : Type*} [Field E] [Field N] [Algebra K E] [Algebra K N]
    [Algebra E N] [IsScalarTower K E N]
    (n : ℕ) (x : Kˣ) (beta : Nˣ)
    (hbeta : beta ^ n = Units.map (algebraMap K N).toMonoidHom x)
    (hrange : (beta : N) ∈ Set.range (algebraMap E N)) :
    ∃ gamma : Eˣ, gamma ^ n = Units.map (algebraMap K E).toMonoidHom x := by
  obtain ⟨gamma, hgamma⟩ := hrange
  have hgamma_ne : gamma ≠ 0 := by
    intro hzero
    apply beta.ne_zero
    rw [← hgamma, hzero, map_zero]
  refine ⟨Units.mk0 gamma hgamma_ne, ?_⟩
  apply Units.ext
  apply (algebraMap E N).injective
  change algebraMap E N (gamma ^ n) = algebraMap E N (algebraMap K E (x : K))
  rw [map_pow, hgamma, ← IsScalarTower.algebraMap_apply K E N]
  exact congrArg Units.val hbeta

omit [NumberField K] in
private theorem unit_root_map_tower
    {E N : Type*} [Field E] [Field N] [Algebra K E] [Algebra K N]
    [Algebra E N] [IsScalarTower K E N]
    (n : ℕ) (x : Kˣ) (beta : Eˣ)
    (hbeta : beta ^ n = Units.map (algebraMap K E).toMonoidHom x) :
    (Units.map (algebraMap E N).toMonoidHom beta) ^ n =
      Units.map (algebraMap K N).toMonoidHom x := by
  rw [← map_pow, hbeta]
  apply Units.ext
  exact (IsScalarTower.algebraMap_apply K E N (x : K)).symm

open scoped Classical in
private theorem local_power_iff_coordinate_fixedField
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
    let S' := enlargeByFiniteKummerRadicalSupport (K := K) (L := E) n hmu S
    let N := fullSUnitKummerExtension (K := K) (Omega := Omega) n S'
    ∀ (i : Fin (sUnitKummerPrimeCount (K := K) E n hmu r S)) (x : Kˣ) (beta : Nˣ),
      beta ^ (n : ℕ) = Units.map (algebraMap K N).toMonoidHom x →
      let wi := sUnitKummerChosenBasePlaces (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i
      Units.map (algebraMap K (wi.adicCompletion K)).toMonoidHom x ∈
        (powMonoidHom (n : ℕ) : (wi.adicCompletion K)ˣ →* (wi.adicCompletion K)ˣ).range ↔
      (beta : N) ∈ sUnitKummerCoordinateFixedField (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i := by
  dsimp only
  let S' := enlargeByFiniteKummerRadicalSupport (K := K) (L := E) n hmu S
  let N := fullSUnitKummerExtension (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by exact_mod_cast n.ne_zero
  let : FiniteDimensional K N := fullSUnitKummerExtension_finiteDimensional
    (K := K) (Omega := Omega) n hnK hmu S'
  let : IsGalois K N := fullSUnitKummerExtension_isGalois
    (K := K) (Omega := Omega) n S'
  intro i x beta hbeta
  let wi := sUnitKummerChosenBasePlaces (K := K) (Omega := Omega) E n hmu
    p v hp hv hn r eG S i
  have h :=
    KummerTheory.finitePlaceKummerRadicand_mem_nthPowerSubgroup_iff_root_mem_decompositionFixedField
    (K := K) (L := N) wi n hmu x beta hbeta
  change _ ↔ (beta : N) ∈ IntermediateField.fixedField
    (_root_.finitePlaceDecompositionGroup (K := K) (L := N) wi) at h
  rw [sUnitKummerChosenDecompositionField_eq_coordinateFixedField
    (K := K) (Omega := Omega) E n hmu p v hp hv hn r eG S i] at h
  exact h

open scoped Classical in
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
      apply (local_power_iff_coordinate_fixedField E n hmu p v hp hv hn r eG S
        i (x : Kˣ) beta hbeta).mp
      exact hxLocal ⟨sUnitKummerChosenBasePlaces (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
    let R :=
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod
          (K := K) E n r eG) S).ker
    have hbetaKernel : (beta : N) ∈ IntermediateField.fixedField R :=
      mem_fixedField_of_subgroup_generators R
        (sUnitKummerKernelGenerator (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S)
        (iSup_zpowers_sUnitKummerKernelGenerator_eq_top
          (K := K) (Omega := Omega) E n hmu p v hp hv hn r eG S) beta hbetaCoordinate
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
    obtain ⟨gamma, hgamma⟩ := exists_unit_root_of_mem_algebraMap_range
      (n : ℕ) (x : Kˣ) beta hbeta hbetaEmbedded
    exact (mem_sUnitFiniteKummerRadical_iff (K := K) (L := E) n S' (x : Kˣ)).mpr
      ⟨x.property, gamma, hgamma⟩
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
    have hbetaN : betaN ^ (n : ℕ) =
        Units.map (algebraMap K N).toMonoidHom (x : Kˣ) :=
      unit_root_map_tower (n : ℕ) (x : Kˣ) betaE hbetaE
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
    have hlocal := (local_power_iff_coordinate_fixedField E n hmu p v hp hv hn r eG S
      i (x : Kˣ) betaN hbetaN).mpr hbetaCoordinate
    rw [← hwi]
    exact hlocal

open scoped Classical in
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
