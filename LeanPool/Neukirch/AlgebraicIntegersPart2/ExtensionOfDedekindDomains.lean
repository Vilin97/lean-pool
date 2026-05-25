/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hu Yongle
-/

/-
Copyright (c) 2023 Hu Yongle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hu Yongle
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.RamificationInertia
import Mathlib.RingTheory.DedekindDomain.Factorization

set_option autoImplicit false

open IsDedekindDomain Algebra UniqueFactorizationMonoid Ideal.IsDedekindDomain Multiset
  FiniteDimensional Classical

attribute [local instance] Ideal.Quotient.field

theorem FiniteDimensional.finrank_mul_finrank'' (F K L : Type*) [Field F] [Field K]
    [Ring L] [Nontrivial L] [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L] :
    finrank F K * finrank K L = finrank F L := by
  by_cases h : FiniteDimensional F K
  · exact FiniteDimensional.finrank_mul_finrank F K L
  · have ha : ¬ FiniteDimensional F L := fun _ ↦ h (left F K L)
    rw[finrank_of_infinite_dimensional h, finrank_of_infinite_dimensional ha, zero_mul]

namespace Ideal

theorem sup_multiset_prod_eq_top {R : Type*} [CommSemiring R] {I : Ideal R}
    {s : Multiset (Ideal R)} (h : ∀  p ∈ s, I ⊔ p = ⊤) : I ⊔ Multiset.prod s = ⊤ :=
  Multiset.prod_induction (I ⊔ · = ⊤) s (fun _ _ hp hq ↦ (sup_mul_eq_of_coprime_left hp).trans hq)
    (by simp only [one_eq_top, ge_iff_le, top_le_iff, le_top, sup_of_le_right]) h

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem factor_to_prime_pow [IsDedekindDomain R] {P I : Ideal R} [hpm : IsPrime P] (hp0 : P ≠ ⊥)
    (hI : I ≠ ⊥) : ∃ Q : Ideal R, P ⊔ Q = ⊤ ∧ I = P ^ (count P (normalizedFactors I)) * Q := by
  use Multiset.prod (filter (¬ P = ·) (normalizedFactors I))
  constructor
  · refine sup_multiset_prod_eq_top (fun p hp ↦ ?_)
    have hm := prime_of_normalized_factor p (filter_subset (¬ P = ·) (normalizedFactors I) hp)
    have hm := IsPrime.isMaximal (isPrime_of_prime hm) (Prime.ne_zero hm)
    exact IsMaximal.coprime_of_ne (IsPrime.isMaximal hpm hp0) hm (of_mem_filter hp)
  · nth_rw 1 [← prod_normalizedFactors_eq_self hI, ← filter_add_not (P = ·) (normalizedFactors I)]
    rw[prod_add, pow_count]

theorem ramificationIdx_tower [IsDedekindDomain S] [IsDedekindDomain T] {f : R →+* S} {g : S →+* T}
    {p : Ideal R} {P : Ideal S} {Q : Ideal T} [hpm : IsPrime P] [hqm : IsPrime Q]
    (hf0 : map f p ≠ ⊥) (hg0 : map g P ≠ ⊥) (hfg : map (g.comp f) p ≠ ⊥)
    (hp0 : P ≠ ⊥) (hq0 : Q ≠ 0) (hg : P = comap g Q) :
    ramificationIdx (g.comp f) p Q = ramificationIdx f p P * ramificationIdx g P Q := by
  rw[ramificationIdx_eq_normalizedFactors_count hf0 hpm hp0,
    ramificationIdx_eq_normalizedFactors_count hg0 hqm hq0,
    ramificationIdx_eq_normalizedFactors_count hfg hqm hq0, ← map_map]
  rcases factor_to_prime_pow hp0 hf0 with ⟨I, hcp, heq⟩
  have hcp : map g P ⊔ map g I = ⊤ := by rw[← map_sup, hcp, map_top g]
  have hp : map g P ≤ Q := map_le_iff_le_comap.mpr (le_of_eq hg)
  have hntq : ¬ ⊤ ≤ Q := fun ht ↦ IsPrime.ne_top hqm (Iff.mpr (eq_top_iff_one Q) (ht trivial))
  nth_rw 1 [heq, map_mul, Ideal.map_pow, normalizedFactors_mul (pow_ne_zero _ hg0) (by
    by_contra h
    simp only [h, Submodule.zero_eq_bot, ge_iff_le, bot_le, sup_of_le_left] at hcp
    rw[hcp] at hp
    exact hntq hp), count_add, normalizedFactors_pow, count_nsmul]
  apply add_right_eq_self.mpr
  by_contra h
  have hpi := sup_le hp (le_of_dvd (dvd_of_mem_normalizedFactors (count_ne_zero.mp h)))
  rw[hcp] at hpi
  exact hntq hpi

theorem inertiaDeg_tower {f : R →+* S} {g : S →+* T} {p : Ideal R} {P : Ideal S} {I : Ideal T}
    [IsMaximal p] [IsMaximal P] [Nontrivial (T ⧸ I)] (hp : p = comap f P) (hP : P = comap g I) :
    inertiaDeg (g.comp f) p I = inertiaDeg f p P * inertiaDeg g P I := by
  have h : comap (g.comp f) I = p := by rw[hp, hP, comap_comap]
  simp only [inertiaDeg, dif_pos hp.symm, dif_pos hP.symm, dif_pos h]
  let _ := Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq hp)
  let _ := Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq hP)
  let _ := Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq h.symm)
  have : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ I) := IsScalarTower.of_algebraMap_eq (by rintro ⟨⟩; rfl)
  exact (finrank_mul_finrank'' (R ⧸ p) (S ⧸ P) (T ⧸ I)).symm

variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

theorem ramificationIdx_algebra_tower [IsDedekindDomain S] [IsDedekindDomain T]
    {p : Ideal R} {P : Ideal S} {Q : Ideal T} [hpm : IsPrime P] [hqm : IsPrime Q]
    (hf0 : map (algebraMap R S) p ≠ ⊥) (hg0 : map (algebraMap S T) P ≠ ⊥)
    (hfg : map (algebraMap R T) p ≠ ⊥) (hp0 : P ≠ ⊥) (hq0 : Q ≠ 0)
    (hg : P = comap (algebraMap S T) Q) : ramificationIdx (algebraMap R T) p Q =
    ramificationIdx (algebraMap R S) p P * ramificationIdx (algebraMap S T) P Q := by
  rw[IsScalarTower.algebraMap_eq R S T]
  rw[IsScalarTower.algebraMap_eq R S T] at hfg
  exact ramificationIdx_tower hf0 hg0 hfg hp0 hq0 hg

theorem inertiaDeg_algebra_tower {p : Ideal R} {P : Ideal S} {I : Ideal T} [IsMaximal p]
    [IsMaximal P] [Nontrivial (T ⧸ I)] (hp : p = comap (algebraMap R S) P)
    (hP : P = comap (algebraMap S T) I) : inertiaDeg (algebraMap R T) p I =
    inertiaDeg (algebraMap R S) p P * inertiaDeg (algebraMap S T) P I := by
  rw[IsScalarTower.algebraMap_eq R S T]
  exact inertiaDeg_tower hp hP



-- Proposition 8.1
#check integralClosure.isDedekindDomain

-- Proposition 8.2
#check sum_ramification_inertia

-- Proposition 8.3
#check KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk

#check finprod_heightOneSpectrum_factorization



#check map_le_of_le_comap
#check le_comap_of_map_le

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

class IsUnramified (p : Ideal R) [p.IsMaximal] : Prop where
  ramificationIdxeqOne : ∀ P : Ideal S, P.IsMaximal → p ≤ comap f P → ramificationIdx f p P = 1
  separable: ∀ P : Ideal S, P.IsMaximal → (h : p ≤ comap f P) →
    @Algebra.IsSeparable (R ⧸ p) (S ⧸ P) _ _ (Ideal.Quotient.algebraQuotientOfLEComap h)

class TotallySplit (p : Ideal R) [p.IsMaximal] : Prop where
  ramificationIdx_eq_one : ∀ P : Ideal S, P.IsMaximal → p ≤ comap f P → ramificationIdx f p P = 1
  inertiaDeg_eq_one : ∀ P : Ideal S, P.IsMaximal → p ≤ comap f P → inertiaDeg f p P = 1

class Nonsplit (p : Ideal R) : Prop where
  nonsplit : ∀ P : Ideal S, P.IsMaximal → p = comap f P →
    ∀ Q : Ideal S, Q.IsMaximal → p = comap f Q → P = Q

end Ideal



open Ideal NumberField

#check IsIntegralClosure.isNoetherian

-- Proposition 8.4
theorem OnlyFinitelyManyPrimeidealsRamified (R S : Type*) [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDomain S] [Algebra R S] (K L : Type*) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
  [IsFractionRing S L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
  [IsIntegralClosure S R L] :
  Set.Finite { p : HeightOneSpectrum R | ¬ (p.asIdeal).IsUnramified (algebraMap R S) } := sorry



#check legendreSym

instance {p : ℕ} [hpp : Fact (Nat.Prime p)] : IsMaximal (Submodule.span ℤ {(p : ℤ)}) :=
  PrincipalIdealRing.isMaximal_of_irreducible <|
    irreducible_iff_prime.mpr (Nat.prime_iff_prime_int.mp (Fact.elim hpp))

open Polynomial

-- Proposition 8.5
theorem IsQuadratic_iff_TotallySplit {a : ℤ} {p : ℕ} (ha : Squarefree a) (hp : p ≠ 2)
    [Fact (Nat.Prime p)] (hpa : IsCoprime a p) : legendreSym p a = 1 ↔
    TotallySplit (algebraMap ℤ (𝓞 (SplittingField (X ^ 2 - (a : ℚ[X])))))
    (Submodule.span ℤ {(p : ℤ)}) := sorry



-- Theorem 8.6
#check legendreSym.quadratic_reciprocity

#check legendreSym.at_neg_one

#check legendreSym.at_two
