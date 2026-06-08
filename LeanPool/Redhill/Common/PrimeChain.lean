/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.Data.Nat.Prime.Infinite
import LeanPool.Redhill.Common.SubsumCondition

/-!
# Prime chains

These are sequences of primes where the next prime is at least twice the last.
-/


open Nat

/-- `primeChain s` is the lexicographically earliest sequence of primes
with `primeChain s 0 > s` and each succeeding element more than twice the last. -/
def primeChain (s : ℕ) : ℕ → ℕ
  | 0 => Nat.find (exists_infinite_primes (s + 1))
  | n + 1 => Nat.find (exists_infinite_primes (2 * primeChain s n + 1))

lemma prime_primeChain {s n : ℕ} : (primeChain s n).Prime := by
  induction n <;> exact (Nat.find_spec (exists_infinite_primes _)).2

lemma primeChain_zero_gt {s : ℕ} : s < primeChain s 0 :=
  (Nat.find_spec (exists_infinite_primes _)).1

lemma primeChain_succ_gt {s n : ℕ} : 2 * primeChain s n < primeChain s (n + 1) :=
  (Nat.find_spec (exists_infinite_primes _)).1

lemma strictMono_primeChain {s : ℕ} : StrictMono (primeChain s) :=
  strictMono_nat_of_lt_succ (by grind [primeChain_succ_gt])

lemma primeChain_gt {s n : ℕ} : s < primeChain s n :=
  primeChain_zero_gt.trans_le (strictMono_primeChain.monotone (Nat.zero_le _))

open Fin Finset

/-- An `(n + 2)`-tuple that satisfies the strong subsum condition if `0 < m ≤ s`. -/
def chainTup (n m s : ℕ) (i : Fin (n + 2)) : ℤ :=
  i.addCases (primeChain s ·.1) fun | 0 => m | 1 => -(m + ∑ i ∈ range n, primeChain s i)

variable {n m s : ℕ}

lemma chainTup_zero : chainTup 0 m s = fun | 0 => m | 1 => -m := by
  ext i
  cases i using addCases with
  | left i => exact i.elim0
  | right i =>
    simp_rw [chainTup, sum_range_zero, addCases_right, natAdd_zero]
    rfl

lemma chainTup_induction_compl :
    {natAdd n 0, natAdd n 2}ᶜ = insert (natAdd n 1) (univ.map (castAddEmb 3)) := by
  ext i
  simp_rw [mem_compl, mem_insert, mem_singleton, mem_map, mem_univ, true_and, coe_castAddEmb]
  cases i using addCases <;> grind

lemma add_sum_lt_primeChain (h : m ≤ s) : m + ∑ i ∈ range n, primeChain s i < primeChain s n := by
  induction n with
  | zero =>
    rw [sum_range_zero, primeChain]
    exact h.trans_lt primeChain_zero_gt
  | succ n ih =>
    rw [sum_range_succ, ← add_assoc]
    apply (primeChain_succ_gt).trans'
    rw [two_mul]
    exact add_lt_add_left ih _

lemma isSubsumBlock_chainTup (h : m ≤ s) :
    IsSubsumBlock (chainTup (n + 1) m s) {natAdd n (0 : Fin 3), natAdd n (2 : Fin 3)} := by
  have nmem : natAdd n 1 ∉ univ.map (castAddEmb 3) := by
    simp_rw [mem_map, mem_univ, true_and, not_exists, coe_castAddEmb, ← Fin.val_inj]
    grind
  have : ∑ i ∈ {natAdd n (0 : Fin 3), natAdd n 2}ᶜ, (chainTup (n + 1) m s i).natAbs =
      m + ∑ i ∈ range n, primeChain s i := by
    have sh₁ : natAdd n (1 : Fin 3) = natAdd (n + 1) (0 : Fin 2) := rfl
    have sh₂ (i : Fin n) : castAdd 3 i = castAdd 2 i.castSucc := rfl
    simp_rw [chainTup_induction_compl, sum_insert nmem, sum_map, coe_castAddEmb, chainTup, sh₁,
      addCases_right, sh₂, addCases_left, Int.natAbs_natCast, val_castSucc, sum_univ_eq_sum_range]
  have sh₁ : natAdd n (0 : Fin 3) = (last n).castAdd 2 := rfl
  have sh₂ : natAdd n (2 : Fin 3) = natAdd (n + 1) (1 : Fin 2) := rfl
  apply IsSubsumBlock.pair_of_sum_natAbs_lt
  · simp_rw [this, chainTup, sh₁, addCases_left, Int.natAbs_natCast, val_last]
    exact add_sum_lt_primeChain h
  · simp_rw [this, chainTup, sh₂, addCases_right, Int.natAbs_neg, ← cast_add, Int.natAbs_natCast,
      sum_range_succ, ← add_assoc]
    exact Nat.lt_add_of_pos_right (by grind [primeChain_gt])
  · simp_rw [chainTup, sh₁, addCases_left, sh₂, addCases_right, mul_neg, Left.neg_nonpos_iff]
    norm_cast
    exact Nat.zero_le _

lemma tupReduce_chainTup {c : n + 1 = n + 1 + 2 - #{natAdd n (0 : Fin 3), natAdd n 2}} :
    tupReduce (chainTup (n + 1) m s) {natAdd n (0 : Fin 3), natAdd n (2 : Fin 3)} c =
    chainTup n m s := by
  ext i
  unfold tupReduce
  cases i using lastCases with
  | last =>
    rw [lastCases_last, sum_pair (by simp)]
    have sh₁ : natAdd n (0 : Fin 3) = (last n).castAdd 2 := rfl
    have sh₂ : natAdd n (2 : Fin 3) = natAdd (n + 1) (1 : Fin 2) := rfl
    have sh₃ : last (n + 1) = natAdd n (1 : Fin 2) := rfl
    simp_rw [chainTup, sh₁, addCases_left, sh₂, addCases_right, sh₃, addCases_right,
      sum_range_succ, Nat.cast_add, val_last]
    lia
  | cast i =>
    have prel : #{natAdd n (0 : Fin 3), natAdd n 2}ᶜ = n + 1 := by simp [card_compl]
    have : complRank {natAdd n 0, natAdd n 2} c = lastCases (natAdd n 1) (castAdd 3) := by
      refine (orderEmbOfFin_unique prel (fun i ↦ ?_) (fun i j h ↦ ?_)).symm
      · rw [chainTup_induction_compl]
        cases i using lastCases <;> simp
      · cases i using lastCases with
        | last => exact absurd (le_last _) (not_le.mpr h)
        | cast i =>
          rw [lastCases_castSucc]
          cases j using lastCases with
          | last => grind
          | cast j =>
            rw [lastCases_castSucc]
            exact (castAddOrderEmb _).strictMono h
    simp_rw [lastCases_castSucc, this, chainTup]
    cases i using lastCases with
    | last =>
      have sh₁ : natAdd n (1 : Fin 3) = (0 : Fin 2).natAdd (n + 1) := rfl
      have sh₂ : (last n).castSucc = natAdd n (0 : Fin 2) := rfl
      rw [lastCases_last, sh₁, addCases_right, sh₂, addCases_right]
    | cast i =>
      have sh₁ : i.castAdd 3 = (i.castAdd 1).castAdd 2 := rfl
      have sh₂ : i.castSucc.castSucc = castAdd 2 i := rfl
      rw [lastCases_castSucc, sh₁, addCases_left, sh₂, addCases_left, val_castAdd]

lemma strongSSC_chainTup (hm : 0 < m) (hs : m ≤ s) : StrongSSC (chainTup n m s) := by
  induction n with
  | zero =>
    rw [chainTup_zero]
    intro b hs
    rw [Fin.sum_univ_two] at hs
    simp only [Fin.isValue, mul_neg, ← sub_eq_add_neg, ← sub_mul] at hs
    simp_rw [Int.mul_eq_zero, Int.sub_eq_zero, Int.natCast_eq_zero, hm.ne', or_false] at hs
    simp_rw [mem_univ, forall_const, Nat.reduceAdd, forall_fin_two, exists_eq_left']
    cases s₀ : b 0 <;> cases s₁ : b 1 <;> simp_all
  | succ n ih =>
    have c : n + 1 = n + 1 + 2 - #{natAdd n (0 : Fin 3), natAdd n 2} := by simp
    apply (isSubsumBlock_chainTup hs).strongSSC_tupReduce c
    rwa [tupReduce_chainTup]
