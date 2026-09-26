/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Combinatorics.Hall.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.RestrictionKernel
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.CyclicPrimePowerFullDecomposition
/-!
# Base-place selection for S-unit Kummer extensions

This file constructs infinite full-decomposition candidate sets and chooses
pairwise distinct base places outside the finite avoidance set. Distinctness
is obtained from Mathlib's Hall marriage theorem.
-/

@[expose] public section

open scoped NumberField IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable
section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section FinitePlaces

variable {K : Type} [Field K]
    [NumberField K]

open scoped Classical in
/-- Base finite places lying below a full-decomposition place for the
cyclic coordinate extension `N/N_i`. -/
noncomputable def sUnitKummerCoordinateBasePlaceCandidates
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
    Set (HeightOneSpectrum (𝓞 K)) := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
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
  let _ : IsGalois Ni N :=
    enlargedSUnitKummerCyclicFixedField_isGalois
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG) S
      (sUnitKummerKernelGenerator
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i)
  exact
    {w | ∃ q : HeightOneSpectrum (𝓞 Ni),
      _root_.finitePlaceBelow (K := K) q = w ∧
      _root_.finitePlaceDecompositionGroup
        (K := Ni) (L := N) q = ⊤}

open scoped Classical in
/-- Each cyclic coordinate extension supplies infinitely many base
finite places below completely decomposed places. -/
theorem sUnitKummerCoordinateBasePlaceCandidates_infinite
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
    (sUnitKummerCoordinateBasePlaceCandidates
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i).Infinite := by
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
  let : NumberField N :=
    NumberField.of_module_finite K N
  let Ni :=
    sUnitKummerCoordinateFixedField
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
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
  let : IsCyclic (N ≃ₐ[Ni] N) :=
    enlargedSUnitKummerCyclicFixedField_isCyclic
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG) S
      (sUnitKummerKernelGenerator
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i)
  have hdegree : Module.finrank Ni N = (n : ℕ) := by
    simpa only [Ni, N, S'] using
      sUnitKummerCoordinateFixedField_finrank
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i
  have hcard : Nat.card (N ≃ₐ[Ni] N) = p ^ v := by
    calc
      Nat.card (N ≃ₐ[Ni] N) = Module.finrank Ni N :=
        IsGalois.card_aut_eq_finrank Ni N
      _ = (n : ℕ) := hdegree
      _ = p ^ v := hn
  have hfull :=
    Cohomology.cyclic_prime_power_infinite_fullDecompositionPlaces
      (K := Ni) (L := N) hp hv hcard
  intro hfinite
  have hpre :=
    _root_.Set.Finite.preimage_finitePlaceBelow
      (K := K) (L := Ni) hfinite
  apply hfull
  apply hpre.subset
  intro q hq
  change _root_.finitePlaceBelow (K := K) q ∈
    sUnitKummerCoordinateBasePlaceCandidates
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  change ∃ q' : HeightOneSpectrum (𝓞 Ni),
    _root_.finitePlaceBelow (K := K) q' =
      _root_.finitePlaceBelow (K := K) q ∧
    _root_.finitePlaceDecompositionGroup
      (K := Ni) (L := N) q' = ⊤
  exact ⟨q, rfl, hq⟩

open scoped Classical in
/-- The finite set avoided in the prime choice: the enlarged support,
all base primes ramified in the full Kummer extension, and the support of
the exponent `n`. -/
noncomputable def sUnitKummerAvoidedBasePlaces
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  letI : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  letI : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  letI : NumberField N :=
    NumberField.of_module_finite K N
  exact
    (S' ∪
      _root_.ramifiedBaseFinitePlaces
        (K := K) (L := N)) ∪
      chosenUnitFiniteSupport (K := K)
        (Units.mk0 ((n : ℕ) : K) hnK)

open scoped Classical in
/-- The enlarged support is contained in the finite avoidance set. -/
theorem
    enlargeByFiniteKummerRadicalSupport_subset_sUnitKummerAvoidedBasePlaces
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S ⊆
      sUnitKummerAvoidedBasePlaces
        (K := K) (Omega := Omega) E n hmu S := by
  unfold sUnitKummerAvoidedBasePlaces
  dsimp only
  intro w hw
  exact
    Finset.mem_union_left _
      (Finset.mem_union_left _ hw)

open scoped Classical in
/-- Simultaneously choose distinct full-decomposition candidates outside
the enlarged support, the ramified primes of `N/K`, and the support of `n`. -/
theorem exists_sUnitKummerChosenBasePlaces
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
    ∃ f :
        Fin
            (sUnitKummerPrimeCount
              (K := K) E n hmu r S) →
          HeightOneSpectrum (𝓞 K),
      Function.Injective f ∧
        ∀ i,
          f i ∈
              sUnitKummerCoordinateBasePlaceCandidates
                (K := K) (Omega := Omega) E n hmu
                p v hp hv hn r eG S i ∧
            f i ∉
              sUnitKummerAvoidedBasePlaces
                (K := K) (Omega := Omega) E n hmu S := by
  let q :=
    sUnitKummerPrimeCount
      (K := K) E n hmu r S
  let A :
      Fin q → Set (HeightOneSpectrum (𝓞 K)) :=
    fun i =>
      sUnitKummerCoordinateBasePlaceCandidates
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i \
        (sUnitKummerAvoidedBasePlaces
          (K := K) (Omega := Omega) E n hmu S : Set _)
  have hA : ∀ i, (A i).Infinite := by
    intro i
    exact
      (sUnitKummerCoordinateBasePlaceCandidates_infinite
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i).sdiff
        (sUnitKummerAvoidedBasePlaces
          (K := K) (Omega := Omega) E n hmu S).finite_toSet
  classical
  choose B hBsub hBcard using
    fun i => (hA i).exists_subset_card_eq q
  have hHall :
      ∀ t : Finset (Fin q),
        t.card ≤ (t.biUnion B).card := by
    intro t
    by_cases ht : t.Nonempty
    · obtain ⟨i, hi⟩ := ht
      calc
        t.card ≤ q := by
          simpa using t.card_le_univ
        _ = (B i).card := (hBcard i).symm
        _ ≤ (t.biUnion B).card :=
          Finset.card_le_card
            (Finset.subset_biUnion_of_mem B hi)
    · simp [Finset.not_nonempty_iff_eq_empty.mp ht]
  obtain ⟨f, hf, hfB⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' B).mp
      hHall
  refine ⟨f, hf, ?_⟩
  intro i
  exact hBsub i (hfB i)

open scoped Classical in
/-- The chosen ordered family of base primes. -/
noncomputable def sUnitKummerChosenBasePlaces
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
    Fin
        (sUnitKummerPrimeCount
          (K := K) E n hmu r S) →
      HeightOneSpectrum (𝓞 K) :=
  Classical.choose
    (exists_sUnitKummerChosenBasePlaces
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S)

open scoped Classical in
/-- The chosen base primes are pairwise distinct. -/
theorem sUnitKummerChosenBasePlaces_injective
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
    Function.Injective
      (sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S) :=
  (Classical.choose_spec
    (exists_sUnitKummerChosenBasePlaces
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S)).1

open scoped Classical in
/-- Each chosen base prime lies below a completely decomposed place in
its coordinate fixed field. -/
theorem
    sUnitKummerChosenBasePlaces_mem_coordinateBasePlaceCandidates
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
    sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i ∈
      sUnitKummerCoordinateBasePlaceCandidates
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i :=
  ((Classical.choose_spec
    (exists_sUnitKummerChosenBasePlaces
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S)).2 i).1

open scoped Classical in
/-- Every chosen base prime avoids the enlarged support, the ramified
primes of the full Kummer extension, and the support of `n`. -/
theorem sUnitKummerChosenBasePlaces_not_mem_avoided
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
    sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i ∉
      sUnitKummerAvoidedBasePlaces
        (K := K) (Omega := Omega) E n hmu S :=
  ((Classical.choose_spec
    (exists_sUnitKummerChosenBasePlaces
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S)).2 i).2

open scoped Classical in
/-- The exponent `n` is a unit at every chosen base prime. -/
theorem sUnitKummerChosenBasePlaces_valuation_natCast_eq_one
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
    (sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i).valuation K
          ((n : ℕ) : K) =
      1 := by
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let nUnit : Kˣ :=
    Units.mk0 ((n : ℕ) : K) hnK
  have hnotSupport :
      sUnitKummerChosenBasePlaces
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i ∉
        chosenUnitFiniteSupport (K := K) nUnit := by
    intro hmem
    apply
      sUnitKummerChosenBasePlaces_not_mem_avoided
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i
    unfold sUnitKummerAvoidedBasePlaces
    dsimp only
    exact Finset.mem_union_right _ hmem
  have hunit :=
    (mem_SUnitGroup_iff
      (K := K) (chosenUnitFiniteSupport (K := K) nUnit) nUnit).mp
      (mem_sUnitGroup_chosenUnitFiniteSupport (K := K) nUnit)
      (sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i)
      hnotSupport
  simpa [nUnit] using hunit

end FinitePlaces

end GlobalClassFieldTheory.ClassFieldAxiom
