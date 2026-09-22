/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.BasePlaceSelection
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.FinitePlaceDecomposition
/-!
# Coordinate places in an S-unit Kummer extension

This file lifts the chosen base places to coordinate places in the full
Kummer extension and proves the required decomposition and unramifiedness
properties.
-/

open scoped NumberField IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section FinitePlaces

variable {K : Type} [Field K]
    [NumberField K]

open scoped Classical in
/-- A completely decomposed coordinate place above the `i`-th chosen
base prime. -/
theorem exists_sUnitKummerCoordinatePlace
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
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hnK hmu S'
    let Ni :=
      enlargedSUnitKummerCyclicFixedField
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod
          (K := K) E n r eG) S
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)
    letI : NumberField Ni :=
      NumberField.of_module_finite K Ni
    letI : IsGalois Ni N :=
      enlargedSUnitKummerCyclicFixedField_isGalois
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod
          (K := K) E n r eG) S
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)
    ∃ q : HeightOneSpectrum (𝓞 Ni),
      _root_.finitePlaceBelow (K := K) q =
          sUnitKummerChosenBasePlaces
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i ∧
        _root_.finitePlaceDecompositionGroup
            (K := Ni) (L := N) q =
          ⊤ := by
  dsimp only
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  let Ni :=
    enlargedSUnitKummerCyclicFixedField
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG) S
      (sUnitKummerKernelGenerator
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i)
  let : NumberField Ni :=
    NumberField.of_module_finite K Ni
  let : IsGalois Ni N :=
    enlargedSUnitKummerCyclicFixedField_isGalois
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG) S
      (sUnitKummerKernelGenerator
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i)
  have h :=
    sUnitKummerChosenBasePlaces_mem_coordinateBasePlaceCandidates
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  change ∃ q : HeightOneSpectrum (𝓞 Ni),
    _root_.finitePlaceBelow (K := K) q =
        sUnitKummerChosenBasePlaces
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i ∧
      _root_.finitePlaceDecompositionGroup
          (K := Ni) (L := N) q =
        ⊤ at h
  exact h

open scoped Classical in
/-- The selected coordinate place above the `i`-th chosen base prime. -/
noncomputable def sUnitKummerCoordinatePlace
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
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :=
  Classical.choose
    (exists_sUnitKummerCoordinatePlace
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i)

open scoped Classical in
/-- The selected coordinate place lies over the corresponding chosen
base prime. -/
@[simp]
theorem sUnitKummerCoordinatePlace_below
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
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hnK hmu S'
    let Ni :=
      enlargedSUnitKummerCyclicFixedField
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod
          (K := K) E n r eG) S
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)
    letI : NumberField Ni :=
      NumberField.of_module_finite K Ni
    _root_.finitePlaceBelow (K := K)
        (sUnitKummerCoordinatePlace
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i) =
      sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i :=
  (Classical.choose_spec
    (exists_sUnitKummerCoordinatePlace
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i)).1

open scoped Classical in
/-- The selected coordinate place is completely decomposed in the full
Kummer extension over its coordinate fixed field. -/
@[simp]
theorem sUnitKummerCoordinatePlace_decompositionGroup
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
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hnK hmu S'
    let Ni :=
      enlargedSUnitKummerCyclicFixedField
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod
          (K := K) E n r eG) S
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)
    letI : NumberField Ni :=
      NumberField.of_module_finite K Ni
    letI : IsGalois Ni N :=
      enlargedSUnitKummerCyclicFixedField_isGalois
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod
          (K := K) E n r eG) S
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)
    _root_.finitePlaceDecompositionGroup
        (K := Ni) (L := N)
        (sUnitKummerCoordinatePlace
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i) =
      ⊤ :=
  (Classical.choose_spec
    (exists_sUnitKummerCoordinatePlace
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i)).2

open scoped Classical in
/-- The `i`-th selected base prime is unramified in the full Kummer
extension. -/
theorem sUnitKummerChosenBasePlace_not_mem_ramified
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
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hnK hmu S'
    letI : IsGalois K N :=
      fullSUnitKummerExtension_isGalois
        (K := K) (Omega := Omega) n S'
    letI : NumberField N :=
      NumberField.of_module_finite K N
    sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i ∉
      _root_.ramifiedBaseFinitePlaces
        (K := K) (L := N) := by
  dsimp only
  intro hram
  apply
    sUnitKummerChosenBasePlaces_not_mem_avoided
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  unfold sUnitKummerAvoidedBasePlaces
  dsimp only
  exact
    Finset.mem_union_left _
      (Finset.mem_union_right _ hram)

open scoped Classical in
/-- The chosen completed place at `p_i` is unramified in `N/K`. -/
theorem sUnitKummerChosenBasePlace_isUnramified
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
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hnK hmu S'
    letI : IsGalois K N :=
      fullSUnitKummerExtension_isGalois
        (K := K) (Omega := Omega) n S'
    letI : NumberField N :=
      NumberField.of_module_finite K N
    _root_.ChosenFinitePlaceIsUnramified
      (K := K) (L := N)
      (sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i) := by
  dsimp only
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
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
  let : NumberField N :=
    NumberField.of_module_finite K N
  apply
    _root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt
  by_contra hram
  apply
    sUnitKummerChosenBasePlace_not_mem_ramified
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
  exact
    ⟨_,
      _root_.finitePlaceExtensionCentre_liesOver
        (K := K)
        (L := N)
        _
        (_root_.chosenFinitePlaceExtension
          (L := N) _),
      hram⟩

end FinitePlaces

end GlobalClassFieldTheory.ClassFieldAxiom
