/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.BasePlaceSelection
/-!
# The finite prime set for an S-unit Kummer extension

This file packages the chosen base places as a finite set and proves its
cardinality and disjointness properties.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section FinitePlaces

variable {K : Type} [Field K]
    [NumberField K]

/-- The finite set `T` of primes chosen for the coordinate cyclic extensions
that detect the enlarged `S`-unit Kummer radical. -/
noncomputable def sUnitKummerPrimeSet
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
    Finset (HeightOneSpectrum (𝓞 K)) :=
  Finset.univ.image
    (sUnitKummerChosenBasePlaces
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S)

/-- The chosen prime set has the required cardinality `s-r`. -/
@[simp]
theorem sUnitKummerPrimeSet_card
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
    (sUnitKummerPrimeSet
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S).card =
        sUnitKummerPrimeCount
          (K := K) E n hmu r S := by
  rw [sUnitKummerPrimeSet,
    Finset.card_image_of_injective Finset.univ
      (sUnitKummerChosenBasePlaces_injective
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S),
    Finset.card_univ, Fintype.card_fin]

/-- The chosen prime set is disjoint from the enlarged finite Kummer-radical support. -/
theorem sUnitKummerPrimeSet_disjoint_enlargeByFiniteKummerRadicalSupport
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
    Disjoint
      (sUnitKummerPrimeSet
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S)
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S) := by
  rw [Finset.disjoint_left]
  intro w hwT hwS
  rw [sUnitKummerPrimeSet, Finset.mem_image] at hwT
  obtain ⟨i, -, hi⟩ := hwT
  subst w
  exact
    sUnitKummerChosenBasePlaces_not_mem_avoided
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
      (enlargeByFiniteKummerRadicalSupport_subset_sUnitKummerAvoidedBasePlaces
        (K := K) (Omega := Omega) E n hmu S hwS)

end FinitePlaces

end GlobalClassFieldTheory.ClassFieldAxiom
