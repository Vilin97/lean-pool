/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.NormalClosure
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.CoordinatePlaces
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.PrimeSet
/-!
# Decomposition groups and fields for S-unit Kummer prime selection

This file identifies the chosen decomposition groups with the cyclic
coordinate subgroups, proves complete splitting in the prescribed extension,
and identifies the associated decomposition fields.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section FinitePlaces

variable {K : Type} [Field K]
    [NumberField K]

/-- The coordinate generator lies in the chosen global decomposition
group. -/
theorem sUnitKummerKernelGenerator_mem_decompositionGroup
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
    ((sUnitKummerKernelGenerator
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i :
          (enlargedSUnitKummerRestrictionHom
            (K := K) (Omega := Omega) E n hmu
            (galois_pow_eq_one_of_equiv_pi_zmod
              (K := K) E n r eG) S).ker) :
        Gal(N/K)) ∈
      _root_.finitePlaceDecompositionGroup
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
  let _ : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : NumberField N :=
    NumberField.of_module_finite K N
  let sigmaKer :=
    sUnitKummerKernelGenerator
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  let sigma : Gal(N/K) :=
    sigmaKer.1
  let P : Subgroup Gal(N/K) :=
    Subgroup.zpowers sigma
  let Ni := IntermediateField.fixedField P
  let : NumberField Ni :=
    NumberField.of_module_finite K Ni
  let : IsGalois Ni N :=
    enlargedSUnitKummerCyclicFixedField_isGalois
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG)
      S sigmaKer
  let : IsScalarTower K Ni N :=
    IntermediateField.isScalarTower_mid Ni
  let : IsMulCommutative Gal(N/K) :=
    KummerTheory.kummerRadicalExtension_isMulCommutative
      n hmu (fullSUnitKummerSubgroup (K := K) n S').1
  let q : HeightOneSpectrum (𝓞 Ni) :=
    sUnitKummerCoordinatePlace
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  let tau : N ≃ₐ[Ni] N :=
    IntermediateField.subgroupEquivAlgEquiv P
      ⟨sigma, Subgroup.mem_zpowers sigma⟩
  have hq :
      _root_.finitePlaceBelow (K := K) q =
        sUnitKummerChosenBasePlaces
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i :=
    sUnitKummerCoordinatePlace_below
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  have hfull :
      _root_.finitePlaceDecompositionGroup
          (K := Ni) (L := N) q =
        ⊤ :=
    sUnitKummerCoordinatePlace_decompositionGroup
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  have hmem :=
    restrictAutomorphismScalars_mem_finitePlaceDecompositionGroup_of_relative_eq_top
      (F := K) (M := Ni) (L := N)
      _ q hq hfull tau
  have htau :
      sigma =
        RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
          (K := K) (M := Ni) tau := by
    apply AlgEquiv.ext
    intro x
    rfl
  change
    sigma ∈ finitePlaceDecompositionGroup
      (sUnitKummerChosenBasePlaces E n hmu p v hp hv hn r eG S i)
  rw [htau]
  exact hmem

/-- The chosen global decomposition group is exactly the cyclic
coordinate subgroup generated by `σᵢ`. -/
theorem sUnitKummerChosenDecompositionGroup_eq_zpowers
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
    _root_.finitePlaceDecompositionGroup
        (K := K) (L := N)
        (sUnitKummerChosenBasePlaces
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i) =
      Subgroup.zpowers
        ((sUnitKummerKernelGenerator
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i :
              (enlargedSUnitKummerRestrictionHom
                (K := K) (Omega := Omega) E n hmu
                (galois_pow_eq_one_of_equiv_pi_zmod
                  (K := K) E n r eG) S).ker) :
          Gal(N/K)) := by
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
  let _ : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : NumberField N :=
    NumberField.of_module_finite K N
  let D :=
    _root_.finitePlaceDecompositionGroup
      (K := K) (L := N)
      (sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i)
  let sigmaKer :=
    sUnitKummerKernelGenerator
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  let sigma : Gal(N/K) :=
    sigmaKer.1
  let : Finite Gal(N/K) :=
    finite_fullSUnitKummerExtension_galois
      (K := K) (Omega := Omega) n
      (by
        exact_mod_cast n.ne_zero)
      hmu S'
  let : IsCyclic D :=
    finitePlaceDecompositionGroup_isCyclic_of_chosenUnramified
      (F := K) (L := N)
      _
      (sUnitKummerChosenBasePlace_isUnramified
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i)
  have hsigma : sigma ∈ D :=
    sUnitKummerKernelGenerator_mem_decompositionGroup
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  let sigmaD : D := ⟨sigma, hsigma⟩
  have horderD : orderOf sigmaD = (n : ℕ) := by
    calc
      orderOf sigmaD = orderOf sigma := by
        simpa only [sigmaD] using
          Subgroup.orderOf_mk sigma hsigma
      _ = orderOf sigmaKer := by
        simpa only [sigma] using
          Subgroup.orderOf_coe sigmaKer
      _ = (n : ℕ) :=
        orderOf_sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i
  have hlower : (n : ℕ) ≤ Nat.card D := by
    rw [← horderD]
    exact orderOf_le_card
  let := Fintype.ofFinite D
  have hpow (g : D) : g ^ (n : ℕ) = 1 := by
    apply Subtype.ext
    exact
      fullSUnitKummerExtension_galois_pow_eq_one
        (K := K) (Omega := Omega) n hmu S' g.1
  have hupper : Nat.card D ≤ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card D =
          (Finset.univ.filter
            (fun g : D => g ^ (n : ℕ) = 1)).card := by
        simp only [hpow, Finset.filter_true, Finset.card_univ]
      _ ≤ (n : ℕ) :=
        IsCyclic.card_pow_eq_one_le n.pos
  have hcard : Nat.card D = (n : ℕ) :=
    le_antisymm hupper hlower
  have hgen :
      Subgroup.zpowers sigmaD = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, horderD, hcard]
  calc
    D = (⊤ : Subgroup D).map D.subtype := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = (Subgroup.zpowers sigmaD).map D.subtype := by
      rw [hgen]
    _ = Subgroup.zpowers sigma := by
      rw [MonoidHom.map_zpowers]
      congr 1

/-- Every prime selected by the Kummer construction splits completely in the
prescribed extension `E / K`.  The selected decomposition group
upstairs is generated by an element of the kernel of restriction to
`E`, so complete splitting follows from the actual tower restriction
formula. -/
theorem finitePlaceSplitsCompletely_of_mem_sUnitKummerPrimeSet
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
    ∀ w,
      w ∈ sUnitKummerPrimeSet
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S →
        _root_.FinitePlaceSplitsCompletely
          (K := K) (L := E) w := by
  intro w hw
  rw [sUnitKummerPrimeSet, Finset.mem_image] at hw
  obtain ⟨i, -, rfl⟩ := hw
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  let _ : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let _ : NumberField N :=
    NumberField.of_module_finite K N
  let : Algebra E N :=
    enlargedSUnitKummerAlgebra
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG) S
  let : IsScalarTower K E N := by
    infer_instance
  apply
    finitePlaceSplitsCompletely_of_decompositionGroup_le_restrictNormalHom_ker
      (K := K) (E := E) (N := N)
  rw [
    sUnitKummerChosenDecompositionGroup_eq_zpowers
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i]
  apply Subgroup.zpowers_le.mpr
  simpa only [enlargedSUnitKummerRestrictionHom, N, S'] using
    (sUnitKummerKernelGenerator
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i).property

/-- The decomposition field of the chosen base place is the coordinate fixed
field used in the Kummer prime-selection construction. -/
theorem sUnitKummerChosenDecompositionField_eq_coordinateFixedField
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
    IntermediateField.fixedField
        (_root_.finitePlaceDecompositionGroup
          (K := K) (L := N)
          (sUnitKummerChosenBasePlaces
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i)) =
      sUnitKummerCoordinateFixedField
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i := by
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
  let _ : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : NumberField N :=
    NumberField.of_module_finite K N
  rw [
    sUnitKummerChosenDecompositionGroup_eq_zpowers
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i]
  rfl

end FinitePlaces

end GlobalClassFieldTheory.ClassFieldAxiom
