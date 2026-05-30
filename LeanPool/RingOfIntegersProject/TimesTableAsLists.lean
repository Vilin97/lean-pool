/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import Mathlib.Tactic.Cases
import Mathlib.Data.List.Indexes
import Mathlib.LinearAlgebra.Basis.Defs
import LeanPool.RingOfIntegersProject.PolynomialsAsLists
import LeanPool.RingOfIntegersProject.LinearAlgebraAuxiliaryLemmas

/-!
# Times Table with lists

Given a times table (multiplication table) `T : Fin n → Fin n → Fin n → R`, we define
multiplication on lists of length `n` (seen as coordinates of an element) with respect to
this times table. We also define efficient exponentiation.

## Main Definitions:
- `table_mul_list'` : multiplication of lists with respect to a times table.
- `nPow_sq_table` : exponentiation of lists with respect to a times table.

## Main results.
- `table_mul_list_eq_mul` : in an algebra with times table `T`, this
  multiplication on lists corresponds to multiplication in the algebra.
- `table_nPow_sq_table_eq_pow` : in an algebra with times table `T`,
  exponentiation on lists corresponds to exponentiation in the algebra.

-/

open Module BigOperators


variable {n : ℕ} {R : Type*} [Semiring R]

lemma list_sum_length (hn : n ≠ 0) (f : Fin n → List R) (h : ∀ i, (f i).length = m) :
    (List.sum (List.ofFn (fun i => f i))).length = m := by
  induction n with
  | zero => contradiction
  | succ n hn1 =>
    unfold List.sum
    rw [List.ofFn_succ, List.foldr_cons, List.add_length, h]
    by_cases h1 : n = 0
    · simp only [h1, List.ofFn_zero, List.foldr_nil]
      erw [List.length_nil]
      simp
    · erw [hn1 h1 (fun i => f (Fin.succ i)) ?_, max_self]
      simp only [h, implies_true]

variable (T : Fin n → Fin n → Fin n → R)

/-- This is the multiplication based on a times table `T`,
  given by `(aᵢ) * (bᵢ) = ∑ᵢ∑ⱼ aᵢ * bⱼ • Tᵢⱼ`.
  We allow lists of different lengths, filling out with zeros if the indices are out of range. -/
def table_mul_list' (a b : List R) : List R :=
  List.sum (List.ofFn (fun i => List.sum (List.ofFn
    (fun j => List.mulPointwise ((List.getD a i 0) * (List.getD b j 0))  (List.ofFn (T i j))))))

lemma table_mul_list_length (a b : List R) : (table_mul_list' T a b).length = n := by
  by_cases hn : n = 0
  · unfold table_mul_list'
    simp only [hn, List.ofFn_zero]
    rfl
  · unfold table_mul_list'
    refine list_sum_length (R := R) hn _ ?_
    · intro i
      refine list_sum_length (R := R) hn _ ?_
      · intro j
        rw [List.mulPointwise_length, List.length_ofFn]

lemma FnOfList_add_ofFn (a b c : Fin n → R)
    (hc : List.ofFn c = (List.ofFn a) + (List.ofFn b)) :
    c = a + b := by
  rw [List.add_ofFn, List.ofFn_inj] at hc
  exact hc

lemma FnOfList_mulPointwise_ofFin (a c : Fin n → R)
   (hc : List.ofFn c = List.mulPointwise d (List.ofFn a)) :
    c = d • a := by
  rw [List.mulPointwise_ofFn a d, List.ofFn_inj] at hc
  exact hc

lemma FnOfList_sum_ofFn {m : ℕ} (f : Fin m → (Fin n → R)) (c : Fin n → R)
    (h : List.ofFn c = List.sum (List.ofFn (fun i => List.ofFn (f i)))) :
    c = ∑ i, f i := by
  match m with
  | 0 =>
      simp only [List.ofFn_zero, Finset.univ_eq_empty, Finset.sum_empty] at h ⊢
      erw [List.ofFn_eq_nil_iff] at h
      ext i
      simp only [h] at i
      exact Fin.elim0 i
  | Nat.succ m =>
    rw [← List.sum_ofFn', List.ofFn_inj] at h
    · exact h
    · simp only [ne_eq, Nat.succ_ne_zero, not_false_eq_true]

lemma List.table_mul_list_ofFn (hn : n ≠ 0) (a b : Fin n → R) :
    List.ofFn (∑ i, (∑ j, (a i * b j) • T i j)) =
    table_mul_list' T (List.ofFn a) (List.ofFn b) := by
  unfold table_mul_list'
  simp_rw [List.mulPointwise_ofFn, ← List.sum_ofFn' hn, List.ofFn_inj]
  congr
  ext i k
  simp only [Finset.sum_apply, Pi.smul_apply]
  congr
  ext j
  congr
  · rw [List.getD_eq_getElem _ _ (lt_of_lt_of_eq i.2 (List.length_ofFn (f := a)).symm)]
    simp only [List.getElem_ofFn, Fin.eta]
  · rw [List.getD_eq_getElem _ _ (lt_of_lt_of_eq j.2 (List.length_ofFn (f := b)).symm)]
    simp only [List.getElem_ofFn, Fin.eta]

lemma FnOfList_table_mul_list_eq_sum_sum (a b c : Fin n → R)
    (hc : List.ofFn c = table_mul_list' T (List.ofFn a) (List.ofFn b)) :
    c = ∑ i, (∑ j, (a i * b j) • T i j) := by
  match n with
  | 0 =>
    simp only [Finset.univ_eq_empty, Matrix.smul_empty, Finset.sum_const, Finset.card_empty]
    ext i
    exact Fin.elim0 i
  | Nat.succ n =>
    rw [← List.table_mul_list_ofFn T (Nat.succ_ne_zero n), List.ofFn_inj] at hc
    exact hc

lemma table_add_list_eq_add {S : Type*} [AddCommMonoid S] [Module R S] [Mul S]
    (B : Basis (Fin n) R S) (a b c : Fin n → R) (hc : List.ofFn c = (List.ofFn a) + (List.ofFn b)) :
    (B.equivFun.symm a) + (B.equivFun.symm b) = B.equivFun.symm c := by
  rw [← B.equivFun.symm.map_add, FnOfList_add_ofFn _ _ _ hc]

lemma table_mulPointwise_eq_smul
    {S : Type*} [AddCommMonoid S] [Module R S] [Mul S] (B : Basis (Fin n) R S)
    (a c : Fin n → R) (d : R) (hc : List.ofFn c = List.mulPointwise d (List.ofFn a)) :
    d • (B.equivFun.symm a) = (B.equivFun.symm c) := by
  rw [← B.equivFun.symm.map_smul, FnOfList_mulPointwise_ofFin _ _ hc]

/-- Multiplication of lists with coordinates
  corresponds to multiplication in the algebra with times table `T`. -/
lemma table_mul_list_eq_mul
    {S : Type*} [NonUnitalNonAssocSemiring S] [Module R S] [SMulCommClass R S S] [IsScalarTower R S
      S] (B : Basis (Fin n) R S) (a b c : Fin n → R)
    (basisMulBasis : ∀ i j k, B.repr (B i * B j) k = T i j k)
    (hc : List.ofFn c = table_mul_list' T (List.ofFn a) (List.ofFn b)) :
    (B.equivFun.symm a) * (B.equivFun.symm b) = (B.equivFun.symm c) := by
  rw [FnOfList_table_mul_list_eq_sum_sum T a b c hc]
  simp only [    Basis.equivFun_symm_apply, map_sum, LinearMapClass.map_smul]
  rw [Finset.sum_mul_sum _ _ _ _]
  simp_rw [smul_mul_smul_comm]
  have : ∀ i j, B i * B j = ∑ k, T i j k • B k := by
    intro i j
    rw [← Basis.sum_repr B (B i * B j)]
    simp_rw [basisMulBasis]
  simp_rw [this]

/-- A version of `table_mul_list'` in which the entries of the times table
  are given by lists instead of vectors `Fin n → R`. This performs better. -/
def table_mul_list (T : Fin n → Fin n → List R) (a : List R) (b : List R) :=
  List.sum (List.ofFn (fun i => List.sum (List.ofFn
  (fun j => List.mulPointwise ((List.getD a i 0) * (List.getD b j 0))  (T i j)))))


lemma table_mul_eq_table_mul' (T' : Fin n → Fin n → Fin n → R) (T : Fin n → Fin n → List R)
    (h : ∀ i j, T i j = List.ofFn (T' i j)) : table_mul_list T a b = table_mul_list' T' a b := by
  unfold table_mul_list' table_mul_list
  simp_rw [h]

/-- Exponentiation by squaring given a times table `T`. -/
def nPow_sq_table (T : Fin n → Fin n → List R) (a : List R) (m : ℕ) : List R :=
  match m with
  | 0 => 1
  | 1 => a
  | Nat.succ k =>
    if h : k % 2 = 0 then table_mul_list T a (table_mul_list T (nPow_sq_table T a (k / 2))
      (nPow_sq_table T a (k / 2)))
    else table_mul_list T (nPow_sq_table T a ((Nat.succ k) / 2))
      (nPow_sq_table T a ((Nat.succ k) / 2))

lemma nPow_sq_table_length (T' : Fin n → Fin n → Fin n → R) (T : Fin n → Fin n → List R)
    (a : List R) (m : ℕ) (hm : 0 < m) (heq : ∀ i j,
      T i j = List.ofFn (T' i j)) (ha : a.length = n) :
    (nPow_sq_table T a m).length = n := by
  match m with
  | 0 => contradiction
  | Nat.succ m =>
  · by_cases h : m = 0
    · rw [h]
      have heq : nPow_sq_table T a (Nat.succ 0) = a := by
        unfold nPow_sq_table
        rfl
      rw [heq, ha]
    · by_cases hp : m % 2 = 0
      · have heq' : nPow_sq_table T a (Nat.succ m) =
          table_mul_list T a
            (table_mul_list T (nPow_sq_table T a (m / 2)) (nPow_sq_table T a (m / 2))) := by
            simp only [nPow_sq_table, hp, reduceDIte]
        rw [heq', table_mul_eq_table_mul' T' T heq, table_mul_list_length]
      · have heq' : nPow_sq_table T a (Nat.succ m) =
          table_mul_list T (nPow_sq_table T a ((Nat.succ m) / 2))
            (nPow_sq_table T a ((Nat.succ m) / 2)) := by
            simp only [nPow_sq_table, hp, ↓reduceDIte]
        rw [heq', table_mul_eq_table_mul' T' T heq, table_mul_list_length]

/-- Exponentiation of lists with coordinates
  corresponds to exponentiation in the algebra with times table `T`. -/
lemma table_nPow_sq_table_eq_pow {S : Type*} [Semiring S] [Module R S] [SMulCommClass R S S]
    [IsScalarTower R S S] (T' : Fin n → Fin n → Fin n → R) (T : Fin n → Fin n → List R)
    (B : Basis (Fin n) R S) (a : Fin n → R)
    (basisMulBasis : ∀ i j k, B.repr (B i * B j) k = T' i j k)
    (heq : ∀ i j, T i j = List.ofFn (T' i j)) (m : ℕ) (hmp : 0 < m) (c : Fin n → R)
    (hc : List.ofFn c = nPow_sq_table T (List.ofFn a) m) :
    (B.equivFun.symm a) ^ m = (B.equivFun.symm c) := by
  revert c
  have nataux : ∀ n, n % 2 = 0 → (n / 2) + (n / 2) = n := by
    intro n hn
    nth_rw 3 [← Nat.div_add_mod n 2]
    rw [← two_mul, hn, add_zero]
  have nataux2 : ∀ n, n ≠ 0 → n % 2 = 0 → 2 ≤ n :=
    fun n hnp hnt => Nat.le_of_dvd (Nat.pos_of_ne_zero hnp) (Nat.dvd_of_mod_eq_zero hnt)
  induction m using Nat.case_strong_induction_on with
  | hz => contradiction
  | hi m hm =>
    by_cases h : m = 0
    · simp_rw [h]
      intro c hc
      have heq : nPow_sq_table T (List.ofFn a) (Nat.succ 0) = List.ofFn a := by
        unfold nPow_sq_table
        rfl
      rw [heq, List.ofFn_inj] at hc
      rw [hc, pow_one]
    · intro c hc
      by_cases hp : m % 2 = 0
      · have heq' : nPow_sq_table T (List.ofFn a) (Nat.succ m) =
        table_mul_list T (List.ofFn a) (table_mul_list T (nPow_sq_table T (List.ofFn a) (m / 2))
          (nPow_sq_table T (List.ofFn a) (m / 2))) := by
          simp only [nPow_sq_table, hp, ↓reduceDIte]
        rw [heq', table_mul_eq_table_mul' _ _ heq, table_mul_eq_table_mul' _ _ heq, ] at hc
        let d := FnOfList n (nPow_sq_table T (List.ofFn a) (m / 2))
          (nPow_sq_table_length T' T (List.ofFn a) (m / 2)
            (Nat.div_pos (nataux2 m h hp) (Nat.ofNat_pos)) heq
            (List.length_ofFn (f := a)))
        have auxd: List.ofFn d = nPow_sq_table T (List.ofFn a) (m / 2) := by
          rw [listOfFn_of_FnOfList]
        let e := FnOfList n (table_mul_list' T'  (nPow_sq_table T (List.ofFn a) (m / 2))
          (nPow_sq_table T (List.ofFn a) (m / 2))) (table_mul_list_length _ _ _)
        have auxe : List.ofFn e = (table_mul_list' T'
          (nPow_sq_table T (List.ofFn a) (m / 2))  (nPow_sq_table T (List.ofFn a) (m / 2))) := by
          rw [listOfFn_of_FnOfList]
        simp_rw [← auxe] at hc
        rw [← auxd] at auxe
        rw [← table_mul_list_eq_mul T' B a e c basisMulBasis hc,
          ← table_mul_list_eq_mul T' B _ _ _ basisMulBasis auxe,
          ← hm (m / 2) (Nat.div_le_self _ _) (Nat.div_pos (nataux2 m h hp) (Nat.ofNat_pos)) d auxd,
            ← pow_add, ← pow_succ', nataux m hp]
      · have heq' : nPow_sq_table T (List.ofFn a) (Nat.succ m) =
        table_mul_list T (nPow_sq_table T (List.ofFn a)
          ((Nat.succ m) / 2)) (nPow_sq_table T (List.ofFn a) ((Nat.succ m) / 2)) := by
          simp only [nPow_sq_table, hp, ↓reduceDIte]
        rw [heq',  table_mul_eq_table_mul' _ _ heq] at hc
        have hpSucc : (Nat.succ m) % 2 = 0 := by
          rw [Nat.succ_eq_add_one, Nat.succ_mod_two_eq_zero_iff, ← Nat.mod_two_ne_zero]
          exact hp
        let d := FnOfList n (nPow_sq_table T (List.ofFn a) (Nat.succ m / 2))
          (nPow_sq_table_length T' T (List.ofFn a) (Nat.succ m / 2) (Nat.div_pos
            (nataux2 (Nat.succ m) (Nat.succ_ne_zero m) hpSucc) (Nat.ofNat_pos))
            heq (List.length_ofFn (f := a)))
        have auxd : List.ofFn d = nPow_sq_table T (List.ofFn a) (Nat.succ m / 2) := by
          rw [listOfFn_of_FnOfList]
        rw [← auxd] at hc
        rw [← table_mul_list_eq_mul T' B _ _ _ basisMulBasis hc,  ← hm (Nat.succ m / 2)
          (by exact Nat.lt_succ_iff.1 (Nat.div_lt_self (n := Nat.succ m)
          (Nat.zero_lt_succ _) (Nat.one_lt_ofNat)))
          (Nat.div_pos (nataux2 (Nat.succ m) (Nat.succ_ne_zero m) hpSucc) (Nat.ofNat_pos)) d auxd,
          ← pow_add, nataux _ hpSucc]
