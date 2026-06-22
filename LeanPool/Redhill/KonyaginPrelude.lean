/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Radical.NatInt
import LeanPool.Redhill.Common.Conjectures

/-!
# The "warm-up" result (Theorem 2.1)
-/


namespace KonyaginPrelude

variable (k : ℕ)

/-- The quintuple defined in Section 2.1. -/
def tup : Fin 5 → ℤ
  | 0 => (6 ^ 2 ^ k + 1) ^ 3
  | 1 => -(6 ^ 2 ^ k - 1) ^ 3
  | 2 => -6 * (6 ^ 2 ^ k) ^ 2
  | 3 => -31
  | 4 => 29

lemma sum_tup : ∑ i, tup k i = 0 := by
  simp [tup, Fin.sum_univ_five]
  ring

lemma injective_tup : tup.Injective := fun i j e ↦ by
  replace e : (6 ^ 2 ^ i + 1 : ℤ) ^ 3 = (6 ^ 2 ^ j + 1) ^ 3 := congr($e 0)
  rwa [pow_left_inj₀ (by positivity) (by positivity) (by lia), add_right_cancel_iff,
    pow_right_inj₀ (by lia) (by lia), Nat.pow_right_inj one_lt_two] at e

section Coprime

lemma six_pow_two_pow_mod_29_mem : (6 ^ 2 ^ k : ℤ) % 29 ∈ [6, 7, 20, 23] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, sq, Int.mul_emod]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ih
    obtain ih | ih | ih | ih := ih <;> simp [ih]

lemma six_pow_two_pow_mod_31_mem : (6 ^ 2 ^ k : ℤ) % 31 ∈ [5, 6, 25] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, sq, Int.mul_emod]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ih
    obtain ih | ih | ih := ih <;> simp [ih]

open IsCoprime in
lemma isCoprime_29 :
    IsCoprime 29 ((6 ^ 2 ^ k + 1) ^ 3 : ℤ) ∧ IsCoprime 29 (-(6 ^ 2 ^ k - 1) ^ 3) ∧
    IsCoprime 29 (-6 * (6 ^ 2 ^ k) ^ 2) := by
  have p29 : Prime (29 : ℤ) := by rw [Int.prime_ofNat_iff]; decide
  rw [neg_right_iff, pow_right_iff zero_lt_three, pow_right_iff zero_lt_three, mul_right_iff]
  simp_rw [show IsCoprime 29 (-6) by decide, true_and, pow_right_iff zero_lt_two,
    p29.coprime_iff_not_dvd, Int.dvd_iff_emod_eq_zero]
  rw [← Int.emod_add_emod, ← Int.emod_sub_emod]
  have := six_pow_two_pow_mod_29_mem k
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  obtain h | h | h | h := this <;> simp [h]

open IsCoprime in
lemma isCoprime_31 :
    IsCoprime 31 ((6 ^ 2 ^ k + 1) ^ 3 : ℤ) ∧ IsCoprime 31 (-(6 ^ 2 ^ k - 1) ^ 3) ∧
    IsCoprime 31 (-6 * (6 ^ 2 ^ k) ^ 2) := by
  have p31 : Prime (31 : ℤ) := by rw [Int.prime_ofNat_iff]; decide
  rw [neg_right_iff, pow_right_iff zero_lt_three, pow_right_iff zero_lt_three, mul_right_iff]
  simp_rw [show IsCoprime 31 (-6) by decide, true_and, pow_right_iff zero_lt_two,
    p31.coprime_iff_not_dvd, Int.dvd_iff_emod_eq_zero]
  rw [← Int.emod_add_emod, ← Int.emod_sub_emod]
  have := six_pow_two_pow_mod_31_mem k
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  obtain h | h | h := this <;> simp [h]

open IsCoprime in
lemma pairwiseCoprime_tup : PairwiseCoprime (tup k) := by
  haveI : Std.Symm (fun i j ↦ IsCoprime (tup k i) (tup k j)) :=
    ⟨fun {a b} (h : IsCoprime (tup k a) (tup k b)) ↦ h.symm⟩
  refine Pairwise.of_lt fun i j h ↦ ?_
  fin_cases j <;> simp only [Fin.reduceFinMk, Fin.not_lt_zero, Fin.lt_one_iff] at *
  · subst h
    rw [tup, pow_left_iff zero_lt_three, tup, neg_right_iff, pow_right_iff zero_lt_three]
    exact add_one_sub_one_of_two_dvd ((show (2 : ℤ) ∣ 6 by lia).pow (by positivity))
  · rw [tup, neg_mul, neg_right_iff, ← pow_mul, ← pow_succ', pow_right_iff (by positivity)]
    obtain rfl | rfl : i = 0 ∨ i = 1 := by lia
    all_goals simp only [tup, neg_left_iff, pow_left_iff zero_lt_three]
    · exact add_one_left_of_dvd (dvd_pow_self 6 (by positivity))
    · exact sub_one_left_of_dvd (dvd_pow_self 6 (by positivity))
  · rw [tup, isCoprime_comm, neg_left_iff]
    obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by lia
    exacts [(isCoprime_31 k).1, (isCoprime_31 k).2.1, (isCoprime_31 k).2.2]
  · rw [tup, isCoprime_comm]
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by lia
    on_goal 4 => rw [tup]; decide
    exacts [(isCoprime_29 k).1, (isCoprime_29 k).2.1, (isCoprime_29 k).2.2]

end Coprime

section Subsum

/-- The quintuple defined in Section 2.1 with `k` in place of `6 ^ 2 ^ k`
for easier term manipulation. -/
def tupReduced : Fin 5 → ℤ
  | 0 => (k + 1) ^ 3
  | 1 => -(k - 1) ^ 3
  | 2 => -6 * k ^ 2
  | 3 => -31
  | 4 => 29

lemma sum_tupReduced_lt_tupReduced_one (hk : 10 ≤ k) :
    ∑ i ∈ {0, 1}ᶜ, (tupReduced k i).natAbs < (tupReduced k 1).natAbs := by
  have se : ({0, 1}ᶜ : Finset (Fin 5)) = {2, 3, 4} := by decide
  simp only [se, Finset.mem_insert, Fin.reduceEq, Finset.mem_singleton, or_self, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton]
  unfold tupReduced
  simp only [Int.reduceNeg, neg_mul, Int.natAbs_neg, Int.natAbs_mul, Int.reduceAbs, Int.natAbs_pow,
    Int.natAbs_natCast, Nat.reduceAdd, show (k - 1 : ℤ).natAbs = k - 1 by lia]
  induction k, hk using Nat.le_induction with
  | base => lia
  | succ k lk ih =>
    have rearr : (k + 1 - 1) ^ 3 = (k - 1) ^ 3 + (3 * k * (k - 1) + 1) := by
      rw [add_tsub_cancel_right]
      replace lk : 1 ≤ k := by lia
      zify [lk]
      ring
    rw [rearr, show 6 * (k + 1) ^ 2 + 60 = 6 * k ^ 2 + 60 + (12 * k + 6) by ring]
    apply add_lt_add_of_lt_of_le ih
    calc
      _ ≤ 3 * 5 * k := by lia
      _ ≤ 3 * (k - 1) * k := by gcongr; lia
      _ ≤ _ := by lia

lemma sum_tupReduced_lt_tupReduced_zero (hk : 10 ≤ k) :
    ∑ i ∈ {0, 1}ᶜ, (tupReduced k i).natAbs < (tupReduced k 0).natAbs := by
  apply (sum_tupReduced_lt_tupReduced_one _ hk).trans_le
  simp_rw [tupReduced, Int.natAbs_neg, Int.natAbs_pow]
  exact pow_le_pow_left₀ (by lia) (by lia) 3

/-- `tupReduced` with the first two terms added together. -/
def tupReduced2 : Fin 4 → ℤ
  | 0 => -6 * k ^ 2
  | 1 => -31
  | 2 => 29
  | 3 => 6 * k ^ 2 + 2

lemma tupReduce_tupReduced {c₁ : 3 = 5 - ({0, 1} : Finset (Fin 5)).card} :
    tupReduce (tupReduced k) {0, 1} c₁ = tupReduced2 k := by
  ext i
  unfold tupReduce
  cases i using Fin.lastCases with
  | last =>
    simp_rw [Fin.lastCases_last, Finset.sum_pair zero_ne_one, tupReduced, tupReduced2,
      Fin.reduceLast]
    ring
  | cast i =>
    have : complRank {0, 1} c₁ = (·.natAdd 2) := by
      refine (Finset.orderEmbOfFin_unique _ (fun i ↦ ?_) ?_).symm
      · fin_cases i <;> simp
      · exact (Fin.natAddOrderEmb 2).strictMono
    simp_rw [Fin.lastCases_castSucc, this, tupReduced, tupReduced2]
    fin_cases i <;> rfl

lemma sum_tupReduced2_lt_tupReduced2_zero (hk : 10 ≤ k) :
    ∑ i ∈ {0, 3}ᶜ, (tupReduced2 k i).natAbs < (tupReduced2 k 0).natAbs := by
  have se : ({0, 3}ᶜ : Finset (Fin 4)) = {1, 2} := by decide
  simp only [se, Fin.reduceEq, Finset.mem_singleton, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton]
  unfold tupReduced2
  simp only [Int.natAbs_mul, Int.reduceAbs, Int.natAbs_natCast, Nat.reduceAdd, sq, ← mul_assoc,
    show 60 = 6 * 2 * 5 by lia]
  gcongr <;> lia

lemma sum_tupReduced2_lt_tupReduced2_three (hk : 10 ≤ k) :
    ∑ i ∈ {0, 3}ᶜ, (tupReduced2 k i).natAbs < (tupReduced2 k 3).natAbs := by
  apply (sum_tupReduced2_lt_tupReduced2_zero _ hk).trans_le
  simp_rw [tupReduced2, neg_mul, Int.natAbs_neg, ← Nat.cast_le (α := ℤ)]
  iterate 2 rw [Int.natAbs_of_nonneg (by positivity)]
  lia

lemma tupReduce_tupReduced2 {c₂ : 2 = 4 - ({0, 3} : Finset (Fin 4)).card} :
    tupReduce (tupReduced2 k) {0, 3} c₂ = ![-31, 29, 2] := by
  ext i
  unfold tupReduce
  cases i using Fin.lastCases with
  | last =>
    rw [Fin.lastCases_last, Finset.sum_pair (by decide)]
    simp [tupReduced2]
  | cast i =>
    have : complRank {0, 3} c₂ = ![1, 2] := by
      refine (Finset.orderEmbOfFin_unique _ (fun i ↦ ?_) ?_).symm
      · fin_cases i <;> simp
      · decide
    simp_rw [Fin.lastCases_castSucc, this, tupReduced2]
    fin_cases i <;> rfl

lemma strongSSC_tupReduced (hk : 10 ≤ k) : StrongSSC (tupReduced k) := by
  have key : IsSubsumBlock (tupReduced k) {0, 1} := by
    apply IsSubsumBlock.pair_of_sum_natAbs_lt (sum_tupReduced_lt_tupReduced_zero _ hk)
      (sum_tupReduced_lt_tupReduced_one _ hk)
    simp_rw [tupReduced, mul_neg, Int.neg_nonpos_iff, ← mul_pow]
    exact Int.pow_nonneg (mul_nonneg (by lia) (by lia))
  have c₁ : 3 = 5 - ({0, 1} : Finset (Fin 5)).card := by simp
  apply key.strongSSC_tupReduce c₁
  rw [tupReduce_tupReduced]
  have key2 : IsSubsumBlock (tupReduced2 k) {0, 3} := by
    apply IsSubsumBlock.pair_of_sum_natAbs_lt (sum_tupReduced2_lt_tupReduced2_zero _ hk)
      (sum_tupReduced2_lt_tupReduced2_three _ hk)
    simp_rw [tupReduced2, neg_mul, Int.neg_nonpos_iff]
    positivity
  have c₂ : 2 = 4 - ({0, 3} : Finset (Fin 4)).card := by simp
  apply key2.strongSSC_tupReduce c₂
  rw [tupReduce_tupReduced2, StrongSSC, IsSubsumBlock]
  decide +kernel

lemma strongSSC_tup : StrongSSC (tup k) := by
  obtain rfl | hk := eq_or_ne k 0
  · rw [StrongSSC, IsSubsumBlock]
    decide +kernel
  have hk' : 10 ≤ 6 ^ 2 ^ k := by
    apply (show 10 ≤ 6 ^ 2 ^ 1 by lia).trans
    gcongr <;> lia
  convert strongSSC_tupReduced (6 ^ 2 ^ k) hk' using 1
  ext i
  fin_cases i <;> simp [tup, tupReduced]

end Subsum

section Quality

open Real UniqueFactorizationMonoid UniqueFactorizationDomain

lemma six_pow_pos {n : ℕ} (hn : n ≠ 0) : 0 < (6 : ℤ) ^ n - 1 := by
  rw [sub_pos]
  exact one_lt_pow₀ (by lia) hn

lemma radical_tup_dvd : radical (∏ i, tup k i) ∣ (6 ^ (2 * 2 ^ k) - 1) * 5394 := by
  simp_rw [show (5394 : ℤ) = 6 * 31 * 29 by lia, ← mul_assoc, tup, Fin.prod_univ_five]
  iterate 3 refine radical_mul_dvd.trans (mul_dvd_mul ?_ ?_)
  · rw [mul_neg, radical_neg, ← mul_pow, ← mul_self_sub_one, ← sq, pow_mul', radical_pow _ (by lia)]
    exact radical_dvd_self
  · rw [neg_mul, radical_neg, ← pow_mul, ← pow_succ', radical_pow _ (by lia)]
    exact radical_dvd_self
  · simp [radical_dvd_self]
  · exact radical_dvd_self

lemma log_radical_tup_le : log (radical (∏ i, tup k i) : ℤ) ≤ 2 * 2 ^ k * log 6 + log 5394 := by
  rw [log_le_iff_le_exp (by exact_mod_cast Int.radical_pos _),
    exp_add, exp_log (by norm_num), mul_comm (_ * _), exp_mul, exp_log (by norm_num)]
  norm_cast
  push_cast
  have : 0 < (6 : ℤ) ^ (2 * 2 ^ k) - 1 := six_pow_pos (by positivity)
  apply (Int.le_of_dvd (by positivity) (radical_tup_dvd k)).trans
  gcongr
  lia

lemma maxAbs_tup : maxAbs (tup k) = (6 ^ 2 ^ k + 1) ^ 3 := by
  simp_rw [maxAbs_eq_foldr, List.ofFn_succ, List.ofFn_zero, Fin.reduceSucc, List.foldr_cons,
    List.foldr_nil]
  change max ((6 ^ 2 ^ k + 1) ^ 3) _ = _
  have e1 : max (tup k 3).natAbs (max (tup k 4).natAbs 0) = 31 := by simp [tup]
  simp_rw [e1, sup_eq_left, tup]
  have e2 : max (-6 * (6 ^ 2 ^ k) ^ 2).natAbs 31 = 6 ^ (2 * 2 ^ k + 1) := by
    rw [neg_mul, Int.natAbs_neg, ← pow_mul', ← pow_succ', Int.natAbs_pow]
    simp_rw [Int.reduceAbs, sup_eq_left]
    apply (show 31 ≤ 6 ^ (2 * 2 ^ 0 + 1) by lia).trans
    gcongr <;> lia
  rw [e2, sup_le_iff, Int.natAbs_neg, Int.natAbs_pow]
  refine ⟨pow_le_pow_left₀ zero_le (by lia) _, ?_⟩
  calc
    _ ≤ 6 ^ (3 * 2 ^ k) := by
      rw [Nat.succ_mul 2]
      gcongr
      · lia
      · exact Nat.one_le_two_pow
    _ ≤ _ := by
      rw [pow_mul']
      gcongr
      exact Nat.le_add_right ..

lemma le_tupleQuality :
    .ofReal ((3 * 2 ^ k * log 6) / (2 * 2 ^ k * log 6 + log 5394)) ≤ tupleQuality (tup k) := by
  apply ENNReal.ofReal_le_ofReal
  rw [maxAbs_tup]
  apply div_le_div₀
  · positivity
  · push_cast
    rw [log_pow, Nat.cast_ofNat, mul_assoc]
    gcongr
    calc
      _ = log (6 ^ 2 ^ k) := by simp only [log_pow, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ _ := by
        gcongr
        norm_num
  · apply log_pos
    rw [← Int.cast_one, Int.cast_lt, Int.one_lt_radical_iff]
    exact (strongSSC_tup _).one_lt_natAbs_prod (by lia)
  · exact log_radical_tup_le k

open Filter in
lemma liminf_tupleQuality_tup : 3 / 2 ≤ liminf (tupleQuality ∘ tup) atTop := by
  refine le_of_eq_of_le ?_ (liminf_le_liminf (.of_forall le_tupleQuality))
  have e₁ : (3 / 2 : ENNReal) = ENNReal.ofReal (3 / 2) := by
    simp [ENNReal.ofReal_div_of_pos zero_lt_two]
  have e₂ (k : ℕ) : (2 ^ k : ℝ) = (2 ^ k : ℕ) := by norm_cast
  simp_rw [e₁, e₂]
  refine (ENNReal.tendsto_ofReal ?_).liminf_eq.symm
  change Tendsto ((fun k : ℕ ↦ 3 * k * log 6 / (2 * k * log 6 + log 5394)) ∘ (2 ^ ·))
    atTop (nhds (3 / 2))
  refine Tendsto.comp ?_ (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  convert tendsto_add_mul_div_add_mul_atTop_nhds 0 (log 5394) (3 * log 6)
    (show 2 * log 6 ≠ 0 by positivity) using 2 with k
  · simp [mul_right_comm _ (k : ℝ), add_comm]
  · exact (mul_div_mul_right _ _ (by positivity)).symm

end Quality

lemma tup_mem_factorFreeTuples : tup k ∈ factorFreeTuples ∅ 5 := by
  simp [factorFreeTuples, sum_tup, strongSSC_tup, pairwiseCoprime_tup]

end KonyaginPrelude

open KonyaginPrelude

/-- Theorem 2.1. -/
theorem konyagin_prelude : 3 / 2 ≤ quality (factorFreeTuples ∅ 5) := by
  refine quality_ge_of_liminf_univ ⟨_, injective_tup⟩ ?_ liminf_tupleQuality_tup
  simp [tup_mem_factorFreeTuples]

theorem not_ramaekersConjecture_five : ¬RamaekersConjecture 5 := by
  have := konyagin_prelude.trans quality_factorFreeTuples_le_ramaekersTuples
  refine (this.trans_lt' ?_).ne'
  rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp)]
  norm_num
