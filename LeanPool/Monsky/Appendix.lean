/-
Copyright (c) 2026 Dhyan Aranha and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha and contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace LeanPool.Monsky

noncomputable section

open ValuationSubring
open Algebra
open Polynomial

-- multiplying a polynomial by 2 commutes with deleting a power
-- Could generalize outside of 2
lemma mul_del_commute {R : Type} [CommRing R] (p : Polynomial R) (n : ℕ) :
 C 2 * erase n p = erase n (C 2 * p) := by
  -- Now we use that a polynomial deleting the n-th term and adding it back in
  -- is the same as doing nothing
  have one := Polynomial.monomial_add_erase p n
  have two := Polynomial.monomial_add_erase (C 2 * p) n
  have three : erase n (C 2 * p) = (C 2 * p) - (monomial n) ((C 2 * p).coeff n) := by
    exact eq_sub_of_add_eq' two
  have four : erase n p = p - (monomial n) (p.coeff n) := by
    exact eq_sub_of_add_eq' one
  rw[three]
  rw[four]
  nth_rewrite 3 [mul_comm]
  rw[coeff_mul_C]
  rw[← monomial_mul_C]
  ring

-- Deleting the highest order term of a polynomial of degree at most n
-- leads to a polynomial of degree less than n
lemma erase_degree_leq_n (R : Type) [CommRing R] (p : Polynomial R) (n : ℕ) (h1 : n > 0)
(h2 : p.natDegree ≤ n) : (p.erase n).natDegree < n := by
  rw[le_iff_lt_or_eq] at h2
  rcases h2 with lt | eq
  · -- If the degree of p is less than n the nth coefficient is 0
    have n_not_in_support : n ∉ p.support := by
      intro n_in_support
      have := eq_natDegree_of_le_mem_support (Nat.le_of_succ_le lt) n_in_support
      rw[this] at lt
      apply lt_irrefl at lt
      exact lt
    have equal : Finsupp.erase n p.toFinsupp = p.toFinsupp := by
      exact Finsupp.erase_of_notMem_support n_not_in_support
    have equal1 : (erase n p).toFinsupp = p.toFinsupp := by
      rw[toFinsupp_erase]
      exact equal
    have equal2 : erase n p = p := toFinsupp_inj.mp equal1
    rwa[equal2]
  · -- If the degree is n
    rcases eraseLead_natDegree_lt_or_eraseLead_eq_zero p with lt2 | zero
    · rw[← eq]
      exact lt2
    · have def1 : p.eraseLead = p.erase p.natDegree := by rfl
      rw[← eq, ← def1, zero, eq]
      exact h1

/-- For nonzero `α` and `x ≤ n`, we have `α ^ n * (α ^ x)⁻¹ = α ^ (n - x)`. -/
lemma pow_mul_inv_pow_of_le {α : ℝ} (hα : α ≠ 0) {n x : ℕ} (h : x ≤ n) :
    α ^ n * (α ^ x)⁻¹ = α ^ (n - x) := by
  rw [pow_sub₀]
  · exact hα
  · exact h

/-- The degree of `q1.erase n` is either `< n` or `0`, given `q1.natDegree ≤ n`. -/
lemma erase_natDegree_lt_or_zero {B : Subring ℝ} {q1 : Polynomial B} {n : ℕ}
    (deg1 : q1.natDegree ≤ n) :
    (q1.erase n).natDegree < n ∨ (q1.erase n).natDegree = 0 := by
  rw [le_iff_lt_or_eq] at deg1
  rcases deg1 with lt | eq
  · left
    calc (erase n q1).natDegree
        ≤ q1.natDegree := natDegree_le_natDegree (degree_erase_le q1 n)
      _ < n            := lt
  · rw [← eq]
    by_cases gt_or_eq : q1.natDegree > 0
    · left
      calc (q1.erase q1.natDegree).natDegree
          ≤ q1.natDegree - 1 := eraseLead_natDegree_le q1
        _ < q1.natDegree     := Nat.sub_one_lt_of_lt gt_or_eq
    · right
      have eq_zero2 : q1.natDegree = 0 := Nat.eq_zero_of_not_pos gt_or_eq
      rw [← Nat.le_zero_eq, ← eq_zero2]
      exact eraseLead_natDegree_le_aux

-- If we have polynomials p and q of degrees m and n and an α∈ ℝ such that α, α⁻¹∉ B,
-- a subring of ℝ, p(α)=1/2 and q(α⁻¹)=1/2 then there is an m' < m such that
-- there exists a polynomial pq of degree m' such that pq(α)=1/2.
lemma lower_degree (B : Subring ℝ) (α : ℝ) (m n : ℕ) (H : α ∉ B ∧ α⁻¹ ∉ B) (p : Polynomial B)
  (q : Polynomial B) (m_eq_degree_p : p.natDegree = m) (n_eq_degree_q : q.natDegree = n)
  (zero_lt_m : m ≠ 0) (zero_lt_n : n ≠ 0) (p_eval : (aeval α) p = 1 / 2)
  (q_eval : (aeval α⁻¹) q = 1 / 2) (leq : n ≤ m) :
  ∃(m' : ℕ) (pq : Polynomial B), m' < m ∧ (aeval α) pq = 1/2 ∧ m' = pq.natDegree := by
  have algebramap : ∀x : B, (algebraMap ↥B ℝ) x = x := by -- the identity algebra map
    intro x
    rfl
  let v₀ := coeff q 0
  have two_eq_constant : C (2:B) = (2 : Polynomial ↥B) := by rfl
  have constant_in_poly :
    ∀(b : B), ∀(p : Polynomial B), (aeval α) ((C b) * p) = b * (aeval α) p := by
      intro b p
      rw[map_mul, aeval_C, algebramap b]
  have two_p_eval : (aeval α) (2 * p) = 1 := by -- (2p)(α)=1
    rw[← two_eq_constant, (constant_in_poly 2 p), p_eval]
    simp only [one_div]
    exact CommGroupWithZero.mul_inv_cancel 2 (Ne.symm (NeZero.ne' 2))
  have one_minus_two_v₀_eq : (aeval α) ((C (1 - 2*v₀)) * (2*p)) = (1 - 2*v₀) := by
    -- multiplying by a constant 1-2v₀ where it is seen as a polynomial of degree 0.
    rw[constant_in_poly (1 - 2*v₀) (2*p), two_p_eval]
    simp only [AddSubgroupClass.coe_sub, OneMemClass.coe_one, Subring.coe_mul, mul_one,
      sub_right_inj, mul_eq_mul_right_iff, ZeroMemClass.coe_eq_zero]
    left
    rfl
  let p1 := (C (1 - 2*v₀)) * (2*p) + (C (2*v₀)) -- Define polynomial p1 = (1-2v₀)2p+2v₀
  have one_eq : 1 = (aeval α) (p1) := by
    rw[← Eq.symm (aeval_add α), aeval_C, algebramap (2*v₀), (one_minus_two_v₀_eq)]
    exact sub_eq_iff_eq_add.mp rfl
  -- For m>0 the m-th coefficient of (1-2v₀)(2p)+ 2v₀ is 2(1-2v₀) times the m-th coefficient of p
  have this6 : p1.erase m + (monomial m (2*(1 - 2*v₀)*p.coeff m)) = p1 := by
    rw[add_comm]
    nth_rewrite 2 [← monomial_add_erase p1 m]
    simp only [add_left_inj]
    rw[monomial_eq_monomial_iff]
    left
    constructor
    · rfl
    · rw[coeff_add, coeff_C_ne_zero zero_lt_m, coeff_C_mul, ← two_eq_constant, coeff_C_mul]
      ring
  -- sum of monomials of degree n-k with as coefficient the k-th coefficient of q over k≤ n.
  -- proving a finite sum of polynomials is a polynomial
  let q1 : Polynomial B := ∑ (k ∈ Finset.range (n+1)), monomial (n-k) (coeff q k)
  have rest_zero : ∑ k ∈ Finset.range n,
  ((monomial (n - (k + 1))) (q.coeff (k + 1))).coeff n = 0 := by
    apply Finset.sum_eq_zero
    intro x in_Finset -- x is a natural number less than n
    rw[Finset.mem_range] at in_Finset
    have lt_n : n - (x + 1) < n := by
      norm_num
      exact Nat.zero_lt_of_ne_zero zero_lt_n
    have ne_n : n - (x + 1) ≠ n := by
      exact Nat.ne_of_lt lt_n
    exact Polynomial.coeff_monomial_of_ne (q.coeff (x + 1)) ne_n.symm
  have nth_coeff : q1.coeff n = q.coeff 0 := by
    rw[Polynomial.finset_sum_coeff, Finset.sum_range_succ',
     Nat.sub_zero, coeff_monomial_same n (q.coeff 0), rest_zero]
    ring
  have hα0 : α ≠ 0 := fun h1 ↦ H.1 (h1 ▸ Subring.zero_mem B)
  have equation (x : ℕ) (h : x ≤ n) : α ^ n * (α ^ x)⁻¹ = α^(n-x) :=
    pow_mul_inv_pow_of_le hα0 h
  have this : α^n * ((aeval α⁻¹) q) = (aeval α) q1 := by
    rw[aeval_eq_sum_range, Finset.mul_sum]
    simp only [inv_pow, Algebra.mul_smul_comm]
    rw[n_eq_degree_q, _root_.map_sum]
    simp only [aeval_monomial]
    apply Finset.sum_congr
    · rfl
    · intro x in_Finset
      rw[algebramap]
      have x_le_n : x ≤ n := by
        rw[Finset.mem_range] at in_Finset
        exact Nat.le_of_lt_succ in_Finset
      rw[equation x x_le_n]
      rfl
  have this2 : α^n = 2 * (aeval α) q1 := by
    rw[← this, q_eval]
    ring
  have this3 : q1.erase n = q1 + - monomial n v₀ := by
  -- the leading coefficient of q_1
    nth_rewrite 2 [← (Polynomial.monomial_add_erase q1 n)]
    rw[nth_coeff]
    ring
  have this4 : (aeval α) q1 - v₀*α^n  = (aeval α) (q1.erase n) := by
    rw[this3, aeval_add α]
    simp only [map_neg, aeval_monomial]
    rw[algebramap v₀]
    ring
  have this5 : (1 - 2 * v₀) * α^n = 2 * (aeval α) (q1.erase n) := by
    -- (1-2v₀)α^n = 2 q'(α) where q'=q1 dropping the x^n term
    rw[← this4]
    ring_nf
    simp only [add_right_inj]
    rw[this2]
    ring
  have coeff_erase_neq_zero : coeff (q1.erase n) 0 = (coeff q) n := by
    -- the constant term of q' is the n-th coefficient of q
    rw[erase_ne q1 n 0 zero_lt_n.symm, finset_sum_coeff, Finset.sum_range_succ,
                Nat.sub_self, coeff_monomial_same 0 (q.coeff n), add_eq_right]
    apply Finset.sum_eq_zero
    intro x in_Finset
    have n_sub_x : n - x ≠ 0 := by
      rw[Finset.mem_range] at in_Finset
      rwa[Nat.sub_ne_zero_iff_lt]
    apply coeff_monomial_of_ne
    exact n_sub_x.symm
  have erase_neq_zero : q1.erase n ≠ 0 := by
    -- the constant term of q' is nonzero
    rw[← support_nonempty]
    use 0 -- we have shown the constant term is nonzero
    rw[mem_support_iff]
    rw[coeff_erase_neq_zero]
    intro eq_zero4
    rw[← n_eq_degree_q] at eq_zero4
    simp at eq_zero4
    have zero_lt_natDegree : 0 < q.natDegree := by
      -- by assumption
      calc
        0 < n           := Nat.zero_lt_of_ne_zero zero_lt_n
        _ = q.natDegree := n_eq_degree_q.symm
    have q_neq_zero : q ≠ 0 := by
      exact Polynomial.ne_zero_of_natDegree_gt (zero_lt_natDegree)
    tauto
  have deg1 : q1.natDegree ≤ n := by
    -- degree of sum is ≤ highest degree of summands
    apply natDegree_sum_le_of_forall_le
    intro x x_in_Finset
    calc ((monomial (n - x)) (q.coeff x)).natDegree
        ≤ n - x  := natDegree_monomial_le (q.coeff x)
      _ ≤ n      := Nat.sub_le n x
  have deg2 : (q1.erase n).natDegree < n ∨ (q1.erase n).natDegree = 0 :=
    erase_natDegree_lt_or_zero deg1
  have deg3 : (monomial (m-n) 1 * q1.erase n).natDegree < m := by
    rcases deg2 with lt | eq
    · rw[Polynomial.natDegree_mul]
      · nth_rewrite 2 [← tsub_add_cancel_of_le leq]
        simp only [natDegree_monomial, one_ne_zero, ↓reduceIte, add_lt_add_iff_left]
        exact lt
      · simp
      · exact erase_neq_zero
    · rw[Polynomial.natDegree_mul]
      · rw[eq]
        simp only [natDegree_monomial, one_ne_zero, ↓reduceIte, add_zero, tsub_lt_self_iff]
        exact ⟨Nat.zero_lt_of_ne_zero zero_lt_m, Nat.zero_lt_of_ne_zero zero_lt_n⟩
      · simp
      · exact erase_neq_zero
  have this10 : ((1 - 2 * v₀):B) * α^m = 2 * (aeval α) (monomial (m-n) 1 * q1.erase n) := by
    rw[aeval_mul]
    nth_rewrite 4 [mul_comm]
    rw[← mul_assoc, ← this5, Polynomial.aeval_monomial, algebramap 1]
    norm_num
    rw[mul_assoc]
    rw[← pow_add]
    rw[Nat.add_sub_of_le leq]
    simp only [mul_eq_mul_right_iff, sub_right_inj, ZeroMemClass.coe_eq_zero, pow_eq_zero_iff',
      ne_eq]
    left
    left
    abel
  have deg4 : ((C (1 - 2*v₀)) * p + (C v₀)).natDegree ≤ m := by
    -- We show this by considering two different cases:
    -- (1-2v₀) = 0 and (1-2v₀) ≠ 0.
    by_cases eq_zero5 : (1 - 2*v₀) = 0
    · rw[eq_zero5] -- the case (1-2v₀) = 0
      simp
    · rw[natDegree_add_C, natDegree_C_mul] -- the case (1-2v₀) ≠ 0
      · exact m_eq_degree_p.le
      · simp
        tauto
  have deg5 : (((C (1 - 2*v₀)) * p + (C v₀)).erase m).natDegree < m :=
    erase_degree_leq_n B ((C (1 - 2*v₀)) * p + (C v₀)) m
      (Nat.zero_lt_of_ne_zero zero_lt_m) deg4
  -- Here we define a new polynomial which here we call pq (this is not the product of the two)
  let pq := ((C (1 - 2*v₀)) * p + (C v₀)).erase m +
  C 2 * C (p.coeff m) * (monomial (m-n) 1) * q1.erase n
  have this11 (p : Polynomial B) : 2 * (aeval α) p = (aeval α) (2 * p) := by
    exact Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (constant_in_poly (↑2) p)))
  -- The polynomial pq evaluated at α multiplied by 2 equals 1
  have this12 : 1 = 2 * (aeval α) (pq) := by
    rw[this11, left_distrib, aeval_add]
    nth_rewrite 2 [← this11]
    rw[mul_assoc]
    nth_rewrite 2 [aeval_mul]
    rw[← mul_assoc]
    nth_rewrite 5 [mul_comm]
    rw[mul_assoc, ← this10, ← algebramap (1 - 2*v₀), ← aeval_monomial, ← aeval_mul]
    nth_rewrite 4 [mul_comm]
    rw[← C_mul, monomial_mul_C, ← mul_assoc]
    nth_rewrite 5 [mul_comm]
    rw[← two_eq_constant, mul_del_commute, left_distrib, ← C_mul, ← mul_assoc]
    nth_rewrite 2 [mul_comm]
    rw[mul_assoc, two_eq_constant, ← aeval_add, this6]
    exact one_eq
  let m' := pq.natDegree
  have deg7 : (C 2 * C (p.coeff m) * (monomial (m-n) 1) * q1.erase n).natDegree < m := by
    rw[← C_mul]
    rw[mul_assoc]
    rw[natDegree_C_mul]
    · exact deg3
    · simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      rw[← m_eq_degree_p]
      simp only [coeff_natDegree, leadingCoeff_eq_zero]
      have zero_lt_natDegree : 0 < m := Nat.zero_lt_of_ne_zero zero_lt_m
      rw[← m_eq_degree_p] at zero_lt_natDegree
      exact ne_zero_of_natDegree_gt zero_lt_natDegree
  have deg6 : m' < m := by
    rw[← Nat.le_sub_one_iff_lt (Nat.zero_lt_of_ne_zero zero_lt_m)]
    rw[← Nat.le_sub_one_iff_lt (Nat.zero_lt_of_ne_zero zero_lt_m)] at deg5
    rw[← Nat.le_sub_one_iff_lt (Nat.zero_lt_of_ne_zero zero_lt_m)] at deg7
    exact (natDegree_add_le_of_degree_le deg5 deg7)
  exact ⟨m', pq, deg6, eq_one_div_of_mul_eq_one_right (_root_.id (Eq.symm this12)), by rfl⟩

-- Any maximal subring of ℝ not containing 1/2 is a valuation ring.
lemma inclusion_maximal_valuation (B : Subring ℝ) (h1 : (1 / 2) ∉ B)
(h2 : ∀ (C : Subring ℝ), (B ≤ C) ∧ (1 / 2) ∉ C → B = C) :
    ∃(D : ValuationSubring ℝ), D.toSubring = B := by
  -- We assume that B is not a valuationring
  by_contra no_vr
  have alpha_existence : ∃(α : ℝ), (α ∉ B ∧ α⁻¹ ∉ B) := by
  -- This is true, because B is not a valuationring
    by_contra H
    rw[← not_forall_not, not_not] at H
    simp_rw[← or_iff_not_and_not] at H
    let D : ValuationSubring ℝ :=
      { B with
        mem_or_inv_mem' := H}
    have for_contra : ∃ (D : ValuationSubring ℝ), D.toSubring = B := by
      use D
    tauto
  obtain ⟨α, H⟩ := alpha_existence
  -- We consider B[α], B[α⁻¹] (as algebras over B)
  let Balpha := adjoin B {α}
  let Balpha' := adjoin B {α⁻¹}
  have alpha_in_Balpha : α ∈ Balpha := subset_adjoin rfl
  have alpha_in_Balpha' : α⁻¹ ∈ Balpha' := subset_adjoin rfl
  have algebramap : ∀x : B, (algebraMap ↥B ℝ) x = x := by
    intro x
    rfl
  -- -- We consider {2} as a subset of Balpha and {2} as a subset of Balpha'
  -- let (two : Set Balpha.toSubring) := {2}
  -- let (two' : Set Balpha'.toSubring) := {2}
  -- -- We view 2B[α], 2B[α⁻¹] as principle ideals,
  -- -- i.e. submodules generated by 1 element
  -- let twoBalpha := Submodule.span Balpha.toSubring two
  -- let twoBalpha' := Submodule.span Balpha'.toSubring two'
  have Balpha_contains_half : 1/2 ∈ Balpha := by
  -- otherwise there is a contradiction with maximality
    by_contra h
    have B_leq_Balpha : B ≤ Balpha.toSubring := by
      -- B is a subring of B[α]
      intro x h'
      lift x to B using h'
      apply Subalgebra.algebraMap_mem'
    have B_is_Balpha : B = Balpha.toSubring := by
      -- Here we use the maximality of B
      exact h2 Balpha.toSubring ⟨B_leq_Balpha, h⟩
    have Balpha_leq_B : Balpha.toSubring ≤ B := by
      exact le_of_eq_of_le (_root_.id (Eq.symm B_is_Balpha)) fun ⦃x⦄ a ↦ a
    have alpha_in_B : α ∈ B := Balpha_leq_B alpha_in_Balpha
    -- We have now shown that α ∈ B, but we also know that α ∉ B by assumption
    -- therefore we obtain a contradiction
    rw[← false_iff] at H
    rwa[H.1]
  have Balpha'_contains_half : 1/2 ∈ Balpha' := by
    -- This is essentially the same proof as above, only with primes
    by_contra h
    have B_leq_Balpha' : B ≤ Balpha'.toSubring := by
      -- B is a subring of B[α⁻¹]
      intro x h'
      lift x to B using h'
      apply Subalgebra.algebraMap_mem'
    have B_is_Balpha' : B = Balpha'.toSubring := by
      -- Here we use the maximality of B
      exact h2 Balpha'.toSubring ⟨B_leq_Balpha', h⟩
    have Balpha'_leq_B : Balpha'.toSubring ≤ B := by
      exact le_of_eq_of_le (_root_.id (Eq.symm B_is_Balpha')) fun ⦃x⦄ a ↦ a
    have alpha_in_B : α⁻¹ ∈ B := Balpha'_leq_B alpha_in_Balpha'
    -- We have now shown that α⁻¹ ∈ B, but we also know that α⁻¹ ∉ B by assumption
    -- therefore we obtain a contradiction
    have one_last : α⁻¹ ∉ B := H.2
    rw[← false_iff] at one_last
    rwa[one_last]
  let degree : Set ℕ := {n : ℕ | ∃(p : Polynomial B),
   p.natDegree = n ∧ (Polynomial.aeval α) p = 1/2}
  let degree' : Set ℕ := {n : ℕ | ∃(p : Polynomial B),
   p.natDegree = n ∧ (Polynomial.aeval α⁻¹) p = 1/2}
  -- Any element of B[α] can be written as a polynomial in α with variables in B
  have contains_half : 1/2 ∈ ((Polynomial.aeval α).range : Subalgebra ↥B ℝ) := by
    rw[← adjoin_singleton_eq_range_aeval B α]
    exact Balpha_contains_half
  have is_nonempty : degree ≠ ∅ := by
    intro is_empty
    rcases contains_half with ⟨p, eval⟩
    have deg : p.natDegree ∈ degree := by
      exact ⟨p, by rfl, eval⟩
    rw[is_empty] at deg
    tauto
  have nonempty : degree.Nonempty := by
    exact Set.nonempty_iff_ne_empty.mpr is_nonempty
  -- Any element of B[α⁻¹] can be written as a polynomial in α⁻¹ with coefficients in B
  have contains_half' : 1/2 ∈ ((Polynomial.aeval α⁻¹).range : Subalgebra ↥B ℝ) := by
    rw[← adjoin_singleton_eq_range_aeval B α⁻¹]
    exact Balpha'_contains_half
  have is_nonempty' : degree' ≠ ∅ := by
    intro is_empty
    rcases contains_half' with ⟨p, eval⟩
    have deg : p.natDegree ∈ degree' := by
      exact ⟨p, by rfl, eval⟩
    rw[is_empty] at deg
    tauto
  have nonempty' : degree'.Nonempty := by
    exact Set.nonempty_iff_ne_empty.mpr is_nonempty'
  -- Since the natural numbers are well-founded and degree and degree' are
  -- non-empty, we may conclude that degree and degree' have a minimal element
  let m := WellFounded.min wellFounded_lt degree nonempty
  let n := WellFounded.min wellFounded_lt degree' nonempty'
  have m_mem : m ∈ degree := WellFounded.min_mem wellFounded_lt degree nonempty
  have n_mem : n ∈ degree' := WellFounded.min_mem wellFounded_lt degree' nonempty'
  rcases m_mem with ⟨p, m_eq_degree_p, p_eval⟩
  rcases n_mem with ⟨q, n_eq_degree_q, q_eval⟩
  -- m and n are not equal to zero, because otherwise 1/2 would be in B
  -- We use that a polynomial of degree zero is constant and  that the
  -- evalauation of a contant polynomial lands in B (Polynomial.aeval_C)
  have zero_lt_m : m ≠ 0 := by
    intro m_eq_zero
    rw[← m_eq_degree_p, Polynomial.natDegree_eq_zero] at m_eq_zero
    rcases m_eq_zero with ⟨x, eq⟩
    rw[← eq, Polynomial.aeval_C, algebramap x] at p_eval
    rw[← p_eval] at h1
    apply h1
    exact SetLike.coe_mem x
  have zero_lt_n : n ≠ 0 := by
    intro n_eq_zero
    rw[← n_eq_degree_q, natDegree_eq_zero] at n_eq_zero
    rcases n_eq_zero with ⟨x, eq⟩
    rw[← eq, aeval_C, algebramap x] at q_eval
    rw[← q_eval] at h1
    apply h1
    exact SetLike.coe_mem x
  by_cases leq : n ≤ m
  · rcases (lower_degree B α m n H p q m_eq_degree_p n_eq_degree_q
     zero_lt_m zero_lt_n p_eval q_eval leq) with ⟨m', pq, deg, eval, deg2⟩
    have main : m' ∈ degree := by
      exact ⟨pq, deg2.symm, eval⟩
    have ge : m' ≥ m := by
      exact WellFounded.min_le wellFounded_lt main
    rw[lt_iff_not_ge] at deg
    tauto
  · have leq2 : m ≤ n := Nat.le_of_not_ge leq
    have H3 : α⁻¹ ∉ B ∧ α⁻¹⁻¹ ∉ B := by
      simp only [inv_inv]
      exact _root_.id (And.symm H)
    have p_eval2 : (aeval α⁻¹⁻¹) p = 1/2 := by
      simp only [inv_inv, one_div]
      rw[← one_div]
      exact p_eval
    rcases (lower_degree B α⁻¹ n m H3 q p n_eq_degree_q m_eq_degree_p
     zero_lt_n zero_lt_m q_eval p_eval2 leq2) with ⟨m', pq, deg, eval, deg2⟩
    have main : m' ∈ degree' := by
      exact ⟨pq, deg2.symm, eval⟩
    have ge : m' ≥ n := by
      exact WellFounded.min_le wellFounded_lt main
    rw[lt_iff_not_ge] at deg
    tauto

/-- The set of subrings of `ℝ` not containing `1/2`. -/
def S := {A : Subring ℝ | (1/2) ∉ A}
/-- The image of `ℤ` inside `ℝ` as a subring. -/
def Z := (Int.castRingHom ℝ).range

-- This lemma shows that the subring of integers in ℝ lies in the set S
lemma Z_in_S : Z ∈ S := by
  -- Now follows the to us trivial notion that the elements
  -- represented by 2 in ℤ and ℝ are the same under coercion
  have two_eq_two : (Int.castRingHom ℝ) 2 = 2 := by rfl
  intro half_in_Z
  simp only [one_div] at half_in_Z
  rcases half_in_Z with ⟨n, h⟩
  rw[← two_eq_two] at h
  -- Here we use injectivity of coercion
  have inj : (Int.castRingHom ℝ).toFun.Injective := by
    exact Isometry.injective fun x1 ↦ congrFun rfl
  have two_n : (Int.castRingHom ℝ) (2*n) = 1 := by-- 2n=1∈ ℤ
    rw[map_mul, h]
    simp
  rw[← (Int.castRingHom ℝ).map_one] at two_n
  have two_n_eq_one : 2*n = 1 := by
    exact (inj two_n)
  have n_two_eq_one : n*2 = 1 := by
    rw[← two_n_eq_one]
    exact Int.mul_comm n 2
  have two_unit : ∃two : ℤˣ, two = (2:ℤ) := by-- implying 2 is a unit in ℤ
    refine CanLift.prf 2 ?_
    rw[isUnit_iff_exists]
    use n
  rcases two_unit with ⟨two, H⟩
  -- We will now use that the only units in ℤ are ±1
  obtain l | l := Int.units_eq_one_or two <;> (rw[l] at H; tauto)

lemma sUnion_is_ub : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
-- Idea: The upper bound is the union of the subrings.
  intro c subset chain
  -- we want to treat the empty chain seperately
  by_cases emp_or_not : c ≠ ∅
  -- Here we have to fiddle around a bit to get our desired upper bound
  -- we do this by first only treating the carriers and showing that that is a subring
  -- Here we send the subrings of c to their carriers (the underlying subset of ℝ)
  · let subring_to_set_of_sets : Set (Set ℝ) :=
      {Rset : Set ℝ | ∃R : Subring ℝ, R ∈ c ∧ Rset = R.carrier}
    let union_of_sets : Set ℝ := ⋃₀ subring_to_set_of_sets
    -- Here we show that ub is actually a subring of ℝ
    let ub : Subring ℝ :=
      { carrier := union_of_sets,
        zero_mem' := by
          have in_c : ∃(t : Subring ℝ), t ∈ c := Set.nonempty_iff_ne_empty.mpr emp_or_not
          obtain ⟨t, in_c⟩ := in_c
          exact Set.mem_sUnion.mpr ⟨t.carrier, ⟨t, in_c, by rfl⟩, t.zero_mem'⟩
        one_mem' := by
          have in_c : ∃(t : Subring ℝ), t ∈ c := Set.nonempty_iff_ne_empty.mpr emp_or_not
          obtain ⟨t, in_c⟩ := in_c
          exact Set.mem_sUnion.mpr ⟨t.carrier, ⟨t, in_c, by rfl⟩, t.one_mem'⟩
        add_mem' := by
          intro a b a_in_carrier b_in_carrier
          refine Set.mem_sUnion.mpr ?_
          rcases a_in_carrier with ⟨cara, hypa, a_in_cara⟩
          rcases b_in_carrier with ⟨carb, hypb, b_in_carb⟩
          have hypa' := hypa
          have hypb' := hypb
          rcases hypa with ⟨ringa, H1a, H2a⟩
          rcases hypb with ⟨ringb, H1b, H2b⟩
          have antisymm : ringa ≤ ringb ∨ ringb ≤ ringa := by
            exact IsChain.total chain H1a H1b
          rcases antisymm with l | r
          · use carb
            have cara_subset_carb : cara ≤ carb := by
              rwa[H2a, H2b]
            have a_and_b_in_carb : a ∈ ringb ∧ b ∈ ringb := by
              repeat rw[← Subring.mem_carrier]
              rw[← H2b]
              exact ⟨cara_subset_carb a_in_cara, b_in_carb⟩
            have a_plus_b_in_ringb : a+b ∈ ringb := by
              exact (ringb.add_mem' a_and_b_in_carb.1 a_and_b_in_carb.2)
            exact ⟨hypb', by rwa[H2b]⟩
          · use cara
            have carb_subset_cara : carb ≤ cara := by
              rwa[H2b, H2a]
            have a_and_b_in_cara : a ∈ ringa ∧ b ∈ ringa := by
              repeat rw[← Subring.mem_carrier]
              rw[← H2a]
              exact ⟨a_in_cara, carb_subset_cara b_in_carb⟩
            have a_plus_b_in_ringa : a+b ∈ ringa := by
              exact (ringa.add_mem' a_and_b_in_cara.1 a_and_b_in_cara.2)
            exact ⟨hypa', by rwa[H2a]⟩,
        mul_mem' := by
          intro a b a_in_carrier b_in_carrier
          refine Set.mem_sUnion.mpr ?_
          rcases a_in_carrier with ⟨cara, hypa, a_in_cara⟩
          rcases b_in_carrier with ⟨carb, hypb, b_in_carb⟩
          have hypa' := hypa
          have hypb' := hypb
          rcases hypa with ⟨ringa, H1a, H2a⟩
          rcases hypb with ⟨ringb, H1b, H2b⟩
          have antisymm : ringa ≤ ringb ∨ ringb ≤ ringa := by
            exact IsChain.total chain H1a H1b
          rcases antisymm with l | r
          · use carb
            have cara_subset_carb : cara ≤ carb := by
              rwa[H2a, H2b]
            have a_and_b_in_carb : a ∈ ringb ∧ b ∈ ringb := by
              repeat rw[← Subring.mem_carrier]
              rw[← H2b]
              exact ⟨cara_subset_carb a_in_cara, b_in_carb⟩
            have a_plus_b_in_ringb : a*b ∈ ringb := by
              exact (ringb.mul_mem' a_and_b_in_carb.1 a_and_b_in_carb.2)
            exact ⟨hypb', by rwa[H2b]⟩
          · use cara
            have carb_subset_cara : carb ≤ cara := by
              rwa[H2b, H2a]
            have a_and_b_in_cara : a ∈ ringa ∧ b ∈ ringa := by
              repeat rw[← Subring.mem_carrier]
              rw[← H2a]
              exact ⟨a_in_cara, carb_subset_cara b_in_carb⟩
            have a_plus_b_in_ringa : a*b ∈ ringa := by
              exact (ringa.mul_mem' a_and_b_in_cara.1 a_and_b_in_cara.2)
            exact ⟨hypa', by rwa[H2a]⟩,
        neg_mem' := by
          intro a a_in_carrier
          rcases a_in_carrier with ⟨cara, hypa, a_in_cara⟩
          have hypa' := hypa
          rcases hypa with ⟨ringa, H1a, H2a⟩
          refine Set.mem_sUnion.mpr ?intro.intro.intro.intro.a
          use cara
          constructor
          · exact hypa'
          · rw[H2a, Subring.mem_carrier]
            rw[H2a, Subring.mem_carrier] at a_in_cara
            exact Subring.neg_mem ringa a_in_cara}
    -- Now we show that 1/2∉ ub
    have ub_carrier_non_half : 1/2 ∉ ub.carrier := by
      intro half_in
      rw[Set.mem_sUnion] at half_in
      rcases half_in with ⟨t, h, g⟩
      rcases h with ⟨ringt, H2, H3⟩
      have half_not_in_t : 1/2 ∉ t := Eq.mpr_not (congrFun H3 (1 / 2)) (subset H2)
      tauto
    -- So ub ∈ S
    have ub_mem_S : ub ∈ S := by
      exact ub_carrier_non_half
    use ub -- here we tell lean to use the ub we constructed
    constructor
    · exact ub_mem_S
    · intro z hz x hx
      exact Subring.mem_carrier.mp (Set.mem_sUnion.mpr ⟨z, ⟨z, hz, by rfl⟩, hx⟩)
  · simp only [ne_eq, Decidable.not_not] at emp_or_not
    use Z -- as Z lies in S, S is nonempty
    constructor
    · exact Z_in_S
    · rw[emp_or_not, Set.forall_mem_empty]
      trivial

-- This lemma shows that there is a valuation ring of ℝ
-- such that 1/2 does not lie in it
lemma valuation_ring_no_half : ∃(B : ValuationSubring ℝ), (1/2) ∉ B := by
  have h2 := zorn_le₀ S sUnion_is_ub -- use Zorn's lemma
  rcases h2 with ⟨B, hl, hr⟩
  have h3 : ∀(C : Subring ℝ), (B ≤ C) ∧ (1/2) ∉ C → B = C := by
    rintro y ⟨h6, h7⟩
    have h8 : y ∈ S := by
      exact h7
    have h5 : y ≤ B := hr h8 h6
    exact LE.le.antisymm h6 h5
  have h4 := inclusion_maximal_valuation B hl h3
  obtain ⟨D, hd⟩ := h4
  use D
  have D_no_half : 1/2 ∉ D.toSubring := by
    rwa[hd]
  exact D_no_half


lemma non_archimedean (Γ₀ : Type) [LinearOrderedCommGroupWithZero Γ₀] (K : Type) [Field K]
(v : Valuation K Γ₀) :(∀(x y : K), v x ≠ v y → v (x + y) = max (v x) (v y)) := by
  exact fun x y a ↦ Valuation.map_add_of_distinct_val v a


-- There is a valuation v on ℝ such that v(1/2) > 1.
theorem valuation_on_reals : ∃(Γ₀ : Type) (_ : LinearOrderedCommGroupWithZero Γ₀)
  (v : Valuation ℝ Γ₀), (v (1/2)) > 1 := by
    have h := valuation_ring_no_half
    obtain ⟨B, h⟩ := h
    use B.ValueGroup, inferInstance, B.valuation
    have g := valuation_le_one_iff B (1/2)
    rw[← not_iff_not] at g
    rwa[gt_iff_lt, ← not_le, g]

lemma odd_valuation (Γ₀ : Type) (_ : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
(vhalf : v (1 / 2) > 1) : ∀ n : ℕ, Odd n → v (1/n) = 1 := by
have vhalf' : v (2) < 1 := by
  rw [Valuation.map_div, Valuation.map_one] at vhalf
  refine (Valuation.val_lt_one_iff v ?_).mpr ?_
  · norm_num
  · simp_all only [map_inv₀, one_div, gt_iff_lt]
have vind : ∀ (k : ℕ), k ≠ 0 →  v (2* k) < 1:= by
  intro k
  induction k
  · tauto
  · rename_i k kind
    intro kpos
    by_cases kpos' : k = 0
    · rw [kpos']
      simp only [zero_add, Nat.cast_one, mul_one]
      apply vhalf'
    · apply kind at kpos'
      simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      have : v (2 * ↑k + 2) ≤ max (v (2 * ↑k)) (v 2) := by
        apply Valuation.map_add
      have this2 : v (2 * ↑k) ⊔ v 2 < 1 := by
        have h1 : v (2 * ↑k) < 1 := kpos'
        have h2 : v 2 < 1 := vhalf'
        exact max_lt h1 h2
      exact trans this this2
have vind' : ∀ k : ℕ, k ≠ 0 →  v (2*k + 1) = 1 := by
  intro n hn
  have this : 2*n ≠ 1 := by
    norm_num
  have this2 : v (1) = 1 := by
    rw [Valuation.map_one]
  rw [Valuation.map_add_of_distinct_val]
  · specialize vind n hn
    simp_all only [one_div, map_inv₀, gt_iff_lt, ne_eq, mul_eq_one, OfNat.ofNat_ne_one, false_and,
      not_false_eq_true, map_mul, map_one, sup_eq_right, ge_iff_le]
    exact le_of_lt vind
  · rw [this2]
    specialize vind n hn
    simp_all only [one_div, map_inv₀, gt_iff_lt, ne_eq, mul_eq_one, OfNat.ofNat_ne_one, false_and,
      not_false_eq_true, map_one, map_mul]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [lt_self_iff_false]
intro n odd
have odd' : ∃ k, 2 *k + 1 = n := by
  rw [Odd] at odd
  rcases odd with ⟨k, eq⟩
  use k
  rw [eq]
rcases odd' with ⟨k, eq⟩
specialize vind' k
by_cases kpos : k = 0
· rw [kpos] at eq
  simp only [mul_zero, zero_add] at eq
  simp only [one_div, map_inv₀, inv_eq_one]
  rw [← eq]
  rw [Nat.cast_one]
  apply Valuation.map_one v
· have kpos_val : v (2 * ↑k + 1) = 1 := vind' kpos
  rw [eq.symm]
  have : v (1 / ↑(2 * k + 1)) = v 1 / v (↑(2 * k + 1)) := by
    apply Valuation.map_div
  rw [this]
  have : v (↑(2 * k + 1)) = 1 := by
    rw [Nat.cast_add, Nat.cast_mul]
    simp_all only [one_div, map_inv₀, gt_iff_lt, ne_eq, map_mul, not_false_eq_true, imp_self,
      map_one, Nat.cast_ofNat, Nat.cast_one]
  rw [this]
  simp

end
end Monsky
end LeanPool
