/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

noncomputable section

open Polynomial UniqueFactorizationMonoid

namespace LeanPolyABC

variable {k : Type*} [Field k] [DecidableEq k]
variable {α : Type*} [CommMonoidWithZero α] [NormalizationMonoid α] [UniqueFactorizationMonoid α]

open scoped Classical in
/-- Prime factors of `a` are monic factors of `a` without duplication. -/
def primeFactors (a : α) : Finset α :=
  (normalizedFactors a).toFinset

open scoped Classical in
/-- Radical of `a` is a product of prime factors of `a`. -/
def radical (a : α) : α :=
  (primeFactors a).prod id

theorem radical_zero_eq_one : radical (0 : α) = 1 := by
  classical
  rw [radical, primeFactors, normalizedFactors_zero, Multiset.toFinset_zero, Finset.prod_empty]

theorem radical_one_eq_one : radical (1 : α) = 1 := by
  classical
  rw [radical, primeFactors, normalizedFactors_one, Multiset.toFinset_zero, Finset.prod_empty]

theorem radical_associated_eq {a b : α} (h : Associated a b) : radical a = radical b := by
  classical
  rcases iff_iff_and_or_not_and_not.mp h.eq_zero_iff with (⟨rfl, rfl⟩ | ⟨ha, hb⟩)
  · rfl
  · simp_rw [radical, primeFactors]
    rw [(associated_iff_normalizedFactors_eq_normalizedFactors ha hb).mp h]

theorem radical_unit_eq_one {a : α} (h : IsUnit a) : radical a = 1 :=
  (radical_associated_eq (associated_one_iff_isUnit.mpr h)).trans radical_one_eq_one

theorem radical_mul_unit_left {u a : α} (h : IsUnit u) : radical (u * a) = radical a :=
  radical_associated_eq (associated_unit_mul_left _ _ h)

theorem radical_mul_unit_right {u a : α} (h : IsUnit u) : radical (a * u) = radical a :=
  radical_associated_eq (associated_mul_unit_left _ _ h)

theorem primeFactors_pow (a : α) {n : ℕ} (hn : 0 < n) : primeFactors (a ^ n) = primeFactors a := by
  classical
  simp_rw [primeFactors]
  simp only [normalizedFactors_pow]
  rw [Multiset.toFinset_nsmul]
  exact ne_of_gt hn

theorem radical_pow (a : α) {n : Nat} (hn : 0 < n) : radical (a ^ n) = radical a := by
  simp_rw [radical, primeFactors_pow a hn]

theorem radical_dvd_self (a : α) : radical a ∣ a := by
  classical
  by_cases ha : a = 0
  · rw [ha]
    apply dvd_zero
  · rw [radical, ← Finset.prod_val, ← (prod_normalizedFactors ha).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le
    rw [primeFactors, Multiset.toFinset_val]
    apply Multiset.dedup_le

theorem radical_dvd_radical_self_mul {a b : α} (hb : b ≠ 0) : radical a ∣ radical (a * b) := by
  classical
  by_cases ha : a = 0
  · rw [ha, zero_mul]
  · rw [radical, ← Finset.prod_val, radical, ← Finset.prod_val]
    apply Multiset.prod_dvd_prod_of_le
    repeat rw [primeFactors]
    rw [normalizedFactors_mul ha hb, Finset.val_le_iff, Multiset.toFinset_add]
    exact Finset.subset_union_left

theorem radical_dvd_radical_mul_self {a b : α} (hb : b ≠ 0) : radical a ∣ radical (b * a) := by
  rw [mul_comm b a]
  exact radical_dvd_radical_self_mul hb

theorem radical_dvd_radical_of_dvd {a b : α} (hb : b ≠ 0) (h : a ∣ b) :
    radical a ∣ radical b := by
  rcases h with ⟨c, hc⟩
  rw [hc]
  rw [hc, mul_ne_zero_iff] at hb
  exact radical_dvd_radical_self_mul hb.right

theorem radical_mul_dvd_mul_radical (a b : α) : radical (a * b) ∣ radical a * radical b := by
  classical
  by_cases ha : a = 0
  · rw [ha]
    simp only [zero_mul, dvd_mul_right]
  by_cases hb : b = 0
  · rw [hb]
    simp only [mul_zero, dvd_mul_left]
  rw [radical, primeFactors, normalizedFactors_mul ha hb, Multiset.toFinset_add]
  rw [radical, primeFactors]
  rw [radical, primeFactors]
  exact ⟨((normalizedFactors a).toFinset ∩ (normalizedFactors b).toFinset).prod id,
    (Finset.prod_union_inter).symm⟩

theorem radical_prime {a : α} (ha : Prime a) : radical a = normalize a := by
  classical
  rw [radical, primeFactors]
  rw [normalizedFactors_irreducible ha.irreducible]
  simp only [Multiset.toFinset_singleton, id, Finset.prod_singleton]

theorem radical_prime_pow {a : α} (ha : Prime a) {n : ℕ} (hn : 1 ≤ n) :
    radical (a ^ n) = normalize a := by
  rw [radical_pow a hn]
  exact radical_prime ha

theorem prime_dvd_radical_iff {a p : α} (ha : a ≠ 0) (hp : Prime p) :
    p ∣ radical a ↔ p ∣ a := by
  classical
  constructor
  · exact fun h => h.trans <| radical_dvd_self a
  · intro hpa
    rcases exists_mem_normalizedFactors_of_dvd ha hp.irreducible hpa with ⟨q, ⟨hqf, hpq⟩⟩
    rw [hpq.dvd_iff_dvd_left]
    rw [radical, primeFactors]
    apply Finset.dvd_prod_of_mem id
    rw [Multiset.mem_toFinset]
    exact hqf

theorem radical_isUnit_iff {a : α} (h : a ≠ 0) : IsUnit (radical a) ↔ IsUnit a := by
  constructor
  · contrapose
    intro ha
    rcases exists_mem_factors h ha with ⟨p, hpf⟩
    have hpp := prime_of_factor _ hpf
    have hpd := dvd_of_mem_factors hpf
    apply not_isUnit_of_not_isUnit_dvd hpp.not_unit
    rw [prime_dvd_radical_iff h hpp]
    exact hpd
  · intro ha
    rw [radical_unit_eq_one ha]
    exact isUnit_one

-- Theorems for commutative rings
variable {R : Type _} [CommRing R] [IsDomain R] [NormalizationMonoid R]
  [UniqueFactorizationMonoid R]

namespace IsCoprime

omit [IsDomain R] in
/-- coprime polynomials have disjoint prime factors (as multisets). -/
private theorem disjoint_normalizedFactors {a b : R} (hc : IsCoprime a b) :
    Disjoint (normalizedFactors a) (normalizedFactors b) := by
  rw [Multiset.disjoint_left]
  intro x hxa hxb
  have x_dvd_a := dvd_of_mem_normalizedFactors hxa
  have x_dvd_b := dvd_of_mem_normalizedFactors hxb
  have xp := prime_of_normalized_factor x hxa
  exact xp.not_unit (hc.isUnit_of_dvd' x_dvd_a x_dvd_b)

omit [IsDomain R] in
-- coprime polynomials have disjoint prime factors (as finsets)
private theorem disjoint_primeFactors {a b : R} (hc : IsCoprime a b) :
    Disjoint (primeFactors a) (primeFactors b) := by
  classical
  exact Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors hc)

omit [IsDomain R] in
private theorem hMul_primeFactors_disjUnion {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : IsCoprime a b) :
    primeFactors (a * b) =
      (primeFactors a).disjUnion (primeFactors b) (disjoint_primeFactors hc) := by
  classical
  rw [Finset.disjUnion_eq_union]
  simp_rw [primeFactors]
  rw [normalizedFactors_mul ha hb, Multiset.toFinset_add]

end IsCoprime

omit [IsDomain R] in
-- possible TODO: the proof is unnecessarily long
@[simp]
theorem radical_neg_one : radical (-1 : R) = 1 :=
  radical_unit_eq_one isUnit_one.neg

omit [IsDomain R] in
theorem radical_hMul {a b : R} (hc : IsCoprime a b) :
    radical (a * b) = radical a * radical b := by
  classical
  by_cases ha : a = 0
  · subst ha; rw [isCoprime_zero_left] at hc
    simp only [MulZeroClass.zero_mul, radical_zero_eq_one, one_mul, radical_unit_eq_one hc]
  by_cases hb : b = 0
  · subst hb; rw [isCoprime_zero_right] at hc
    simp only [MulZeroClass.mul_zero, radical_zero_eq_one, mul_one, radical_unit_eq_one hc]
  simp_rw [radical]
  rw [IsCoprime.hMul_primeFactors_disjUnion ha hb hc]
  rw [Finset.prod_disjUnion (IsCoprime.disjoint_primeFactors hc)]

omit [IsDomain R] in
theorem radical_neg {a : R} : radical (-a) = radical a :=
  neg_one_mul a ▸ (radical_associated_eq <| associated_unit_mul_left a (-1) isUnit_one.neg)

-- This actually holds for nontrivial monoids - do not need ring assumption.
theorem radical_ne_zero (a : R) : radical a ≠ 0 := by
  classical
  rw [radical, ← Finset.prod_val]
  apply Multiset.prod_ne_zero
  rw [primeFactors]
  simp only [Multiset.toFinset_val, Multiset.mem_dedup]
  exact zero_notMem_normalizedFactors _

namespace Polynomial

theorem radical_degree_le {a : k[X]} (ha : a ≠ 0) : (radical a).degree ≤ a.degree :=
  degree_le_of_dvd (radical_dvd_self a) ha

theorem radical_natDegree_le (a : k[X]) : (radical a).natDegree ≤ a.natDegree := by
  by_cases ha : a = 0
  · rw [ha, radical_zero_eq_one, natDegree_one, natDegree_zero]
  · exact natDegree_le_of_dvd (radical_dvd_self a) ha

theorem radical_natDegree_mul_le (a b : k[X]) :
    (radical (a * b)).natDegree ≤ (radical a).natDegree + (radical b).natDegree := by
  rw [← natDegree_mul (radical_ne_zero _) (radical_ne_zero _)]
  apply natDegree_le_of_dvd (radical_mul_dvd_mul_radical a b)
  apply mul_ne_zero
  · exact radical_ne_zero _
  · exact radical_ne_zero _

end Polynomial

end LeanPolyABC
