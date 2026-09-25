/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.CompletelySplitPrimes
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.DegreeOnePrimes
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Data.Nat.ModEq

/-! # Completely Split Primes Mod Four -/

@[expose] public section
open scoped NumberField
open NumberField IsDedekindDomain

namespace AlgebraicNumberTheory.PrimeSelection

/-- At an odd degree-one prime in a field containing i, reduction of i
makes -1 a square in the prime field, forcing q ≡ 1 mod 4. -/
theorem modFour_eq_one_of_degreeOnePrime_sq_neg_one
    (K : Type*) [Field K] [NumberField K]
    (q : ℕ) [Fact q.Prime] (hqTwo : q ≠ 2)
    (W : HeightOneSpectrum (𝓞 K))
    (hOver : W.asIdeal.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)))
    (hf : W.asIdeal.inertiaDeg ℤ = 1)
    (j : 𝓞 K) (hj : j ^ 2 = -1) : q % 4 = 1 := by
  let p : Ideal ℤ := Ideal.span ({(q : ℤ)} : Set ℤ)
  have : W.asIdeal.LiesOver p := hOver
  have : p.IsMaximal := Int.ideal_span_isMaximal_of_prime q
  let : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  let : Field ((𝓞 K) ⧸ W.asIdeal) := Ideal.Quotient.field W.asIdeal
  have hRank : Module.finrank (ℤ ⧸ p) ((𝓞 K) ⧸ W.asIdeal) = 1 :=
    (Ideal.inertiaDeg_eq_of_isMaximal p W.asIdeal).symm.trans hf
  have hSurj : Function.Surjective
      (algebraMap (ℤ ⧸ p) ((𝓞 K) ⧸ W.asIdeal)) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hRank).2
  obtain ⟨a, ha⟩ := hSurj (Ideal.Quotient.mk W.asIdeal j)
  have haSq : a ^ 2 = -1 := by
    apply (algebraMap (ℤ ⧸ p) ((𝓞 K) ⧸ W.asIdeal)).injective
    rw [map_pow, ha, ← map_pow, hj, map_neg, map_one, map_neg, map_one]
  have hRoot : ((Int.quotientSpanNatEquivZMod q) a) ^ 2 = (-1 : ZMod q) := by
    rw [← map_pow, haSq, map_neg, map_one]
  have hNeThree : q % 4 ≠ 3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one hRoot
  have hOdd : q % 2 = 1 := Nat.odd_iff.mp ((Fact.out : q.Prime).odd_of_ne_two hqTwo)
  exact (Nat.odd_mod_four_iff.mp hOdd).resolve_right hNeThree

/-- Prime selection with complete splitting, the congruence q ≡ 1 mod 4,
and avoidance of an arbitrary finite set. The proof applies the elementary
polynomial prime-divisor argument to K(i), then contracts its degree-one
unramified prime to K. -/
theorem exists_completelySplitPrime_modFour_one_not_mem
    (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (bad : Finset ℕ) :
    ∃ q : Nat.Primes, q.val ∉ bad ∧ q.val % 4 = 1 ∧
      FinitePlaceSplitsCompletely (K := ℚ) (L := K)
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q) := by
  classical
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq
    (-1 : AlgebraicClosure K) (by decide : 0 < 2)
  have haInt : IsIntegral K a := IsIntegral.of_pow (by decide : 0 < 2) (by
    rw [ha]
    exact isIntegral_one.neg)
  let L := IntermediateField.adjoin K ({a} : Set (AlgebraicClosure K))
  have : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional haInt
  have : NumberField L := NumberField.of_module_finite K L
  let j : L := ⟨a, IntermediateField.mem_adjoin_simple_self K a⟩
  have hj : j ^ 2 = -1 := Subtype.ext ha
  have hjInt : IsIntegral ℤ j := IsIntegral.of_pow (by decide : 0 < 2) (by
    rw [hj]
    exact isIntegral_one.neg)
  let jO : 𝓞 L := ⟨j, hjInt⟩
  have hjO : jO ^ 2 = -1 := NumberField.RingOfIntegers.ext hj
  obtain ⟨q, hq, hqBad, W, hOver, hf, hU⟩ :=
    exists_unramified_degreeOnePrime_not_mem L (insert 2 bad)
  have : Fact q.Prime := ⟨hq⟩
  have hqTwo : q ≠ 2 := fun h => hqBad (h ▸ Finset.mem_insert_self _ _)
  have hqFour : q % 4 = 1 :=
    modFour_eq_one_of_degreeOnePrime_sq_neg_one L q hqTwo W hOver hf jO hjO
  let V : HeightOneSpectrum (𝓞 K) := finitePlaceBelow (K := K) W
  have : W.asIdeal.LiesOver V.asIdeal := ⟨rfl⟩
  have : W.asIdeal.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hOver
  have hVOver : V.asIdeal.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
    Ideal.LiesOver.tower_bot W.asIdeal V.asIdeal (Ideal.span ({(q : ℤ)} : Set ℤ))
  have hVf : V.asIdeal.inertiaDeg ℤ = 1 := by
    apply Nat.dvd_one.mp
    rw [← hf]
    exact Ideal.inertiaDeg_below_dvd (R := ℤ) V.asIdeal W.asIdeal
  have : Algebra.IsUnramifiedAt ℤ W.asIdeal := hU
  have hVU : Algebra.IsUnramifiedAt ℤ V.asIdeal :=
    Algebra.IsUnramifiedAt.of_liesOver ℤ V.asIdeal W.asIdeal
  exact ⟨⟨q, hq⟩, (fun h => hqBad (Finset.mem_insert_of_mem h)), hqFour,
    finitePlaceSplitsCompletely_of_unramified_degree_one K ⟨q, hq⟩ V hVOver hVf hVU⟩

end AlgebraicNumberTheory.PrimeSelection
