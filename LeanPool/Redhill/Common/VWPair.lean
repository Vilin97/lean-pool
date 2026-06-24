/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factors
import Mathlib.Data.ZMod.Defs
import LeanPool.Redhill.Common.PrimeChain

/-!
# VW pairs

The paper stipulates `u < 0 < m` and `w ≤ 0 < v`.
These bounds are formalised by typing all four variables as natural numbers,
negating `u` and `w` as needed.

The bound `w ≤ (m + 1) * primorial m` is not used in any proof and has been removed.
The bound `primorial m < v` has been simplified to `m < v`.

Note that the paper's algorithm does not necessarily guarantee `q < v` (without the negations
performed in this file). For example, take `m = 5, q = 30, u = -2`, then step 1 sets
`v = 29, w = -31` and both numbers are unchanged in the rest of the algorithm
because 29 and 31 are big primes.

The coprimality condition only requires `0 < u ≤ m` and is proved separately.
-/


open Nat Finset

/-- `VWPair u m` holds `v` and `w` and states that `-u, m, v, -w` satisfy the conditions
in Lemma 2.2. -/
structure VWPair (u m : ℕ) where
  /-- `v` in the paper -/
  v : ℕ
  /-- `w` in the paper, **negated** -/
  w : ℕ
  /-- `u = v + w` in the paper -/
  eq_add : w = u + v
  /-- `m < v` -/
  m_lt_v : m < v
  /-- `w` is odd -/
  w_odd : Odd w
  /-- No number in `[3,m]` divides `v` or `w` -/
  not_dvd (k) (hk : k ∈ Icc 3 m) : ¬k ∣ v ∧ ¬k ∣ w

namespace VWPair

variable {v w u m p : ℕ}

variable (v w p) in
lemma nonempty_double_not_dvd (hp : 3 ≤ p) :
    Finset.Nonempty {i : Fin p | ¬p ∣ v + i ∧ ¬p ∣ w + i} := by
  let nzp : NeZero p := ⟨by lia⟩
  have rearr (i : Fin p) (n : ℕ) : p ∣ n + i ↔ i = -Fin.ofNat p n := by
    rw [← add_eq_zero_iff_eq_neg, ← Fin.val_eq_zero_iff, Fin.val_add, Fin.val_ofNat,
      ← dvd_iff_mod_eq_zero]
    nth_rw 1 [← n.mod_add_div p, ← add_rotate, ← Nat.dvd_add_iff_left (by simp)]
  conv =>
    enter [1, 1, i]
    rw [rearr, rearr, ← not_or, ← @mem_singleton _ (-Fin.ofNat p w), ← mem_insert]
  rw [filter_notMem_eq_sdiff, ← card_pos, card_sdiff_of_subset (subset_univ _), Finset.card_univ,
    Fintype.card_fin]
  grind

variable (v w) in
/-- Note the divisor of 2 and not 4 for `w`. -/
lemma nonempty_double_not_dvd_four : Finset.Nonempty {i : Fin 4 | ¬4 ∣ v + i ∧ ¬2 ∣ w + i} := by
  by_cases hw : 2 ∣ w
  · by_cases hv : v % 4 = 3
    · use 3; grind
    · use 1; grind
  · by_cases hv : 4 ∣ v
    · use 2; grind
    · use 0; grind

/-- The finset consisting of 4 and all odd primes at most `m`. -/
def fourAndOddPrimes (m : ℕ) : Finset ℕ :=
  insert 4 {p ∈ Icc 3 m | p.Prime}

lemma zero_notMem_fourAndOddPrimes : 0 ∉ fourAndOddPrimes m := by simp [fourAndOddPrimes]

lemma fourAndOddPrimes_pairwise_coprime : Set.Pairwise (fourAndOddPrimes m) Coprime := by
  rw [fourAndOddPrimes, coe_insert, coe_filter, Set.pairwise_insert_of_symm]
  refine ⟨fun p mp q mq hn ↦ (coprime_primes mp.2 mq.2).mpr hn, fun p ⟨bp, pp⟩ _ ↦ ?_⟩
  rw [show 4 = 2 ^ 2 by rfl]
  apply Coprime.pow_left
  rw [coprime_two_left]
  exact pp.odd_of_ne_two (by grind)

/-- Produce a number `i < p` such that `v + i` and `w + i` are both not divisible by `p`.
When `p = 4`, `w + i` is additionally guaranteed to be odd. Return 0 for `p ≤ 2`. -/
def nonDividingShift (v w p : ℕ) : ℕ :=
  if p = 4 then (min' _ (nonempty_double_not_dvd_four v w)).1 else
  if hp : 3 ≤ p then (min' _ (nonempty_double_not_dvd v w p hp)).1 else 0

lemma not_dvd_nonDividingShift_of_three_le (hp : 3 ≤ p) :
    ¬p ∣ v + nonDividingShift v w p ∧ ¬p ∣ w + nonDividingShift v w p := by
  unfold nonDividingShift
  split_ifs with p4
  · subst p4
    obtain ⟨dv, dw⟩ := (mem_filter_univ _).mp (min'_mem _ (nonempty_double_not_dvd_four v w))
    refine ⟨dv, ?_⟩
    contrapose! dw
    exact (show 2 ∣ 4 by decide).trans dw
  simpa using min'_mem _ (nonempty_double_not_dvd v w p hp)

/-- `crtShift v w m` is a number that can be added to `v, w` such that
* no number in `[3,m]` divides the resulting `v` or `w`
* the resulting `w` is odd.

This number is calculated through the Chinese remainder theorem. -/
def crtShift (v w m : ℕ) : ℕ :=
  chineseRemainderOfFinset (nonDividingShift v w) id (fourAndOddPrimes m)
    (by simp [zero_notMem_fourAndOddPrimes]) fourAndOddPrimes_pairwise_coprime

lemma crtShift_modEq (mi : p ∈ fourAndOddPrimes m) :
    crtShift v w m ≡ nonDividingShift v w p [MOD p] := (chineseRemainderOfFinset ..).2 _ mi

lemma crtShift_not_dvd {k : ℕ} (hk : k ∈ Icc 3 m) :
    ¬k ∣ v + crtShift v w m ∧ ¬k ∣ w + crtShift v w m := by
  obtain ⟨i, rfl⟩ | ⟨p, pp, dp, op⟩ := eq_two_pow_or_exists_odd_prime_and_dvd k
  · rcases lt_or_ge i 2 with hi | hi
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by lia
      all_goals grind
    suffices ¬4 ∣ v + crtShift v w m ∧ ¬4 ∣ w + crtShift v w m by
      contrapose this
      rw [← not_or, not_not] at this ⊢
      have d2i : 2 ^ 2 ∣ 2 ^ i := pow_dvd_pow_iff_le_right'.mpr hi
      exact this.imp (d2i.trans ·) (d2i.trans ·)
    have meq : crtShift v w m ≡ nonDividingShift v w 4 [MOD 4] := by
      simp [crtShift_modEq, fourAndOddPrimes]
    rw [dvd_iff_mod_eq_zero, add_mod, meq, ← add_mod, dvd_iff_mod_eq_zero, add_mod w, meq,
      ← add_mod, ← dvd_iff_mod_eq_zero, ← dvd_iff_mod_eq_zero]
    exact not_dvd_nonDividingShift_of_three_le (by decide)
  · suffices ¬p ∣ v + crtShift v w m ∧ ¬p ∣ w + crtShift v w m by
      contrapose this
      rw [← not_or, not_not] at this ⊢
      exact this.imp (dp.trans ·) (dp.trans ·)
    rw [mem_Icc] at hk
    rw [pp.odd_iff] at op
    have meq : crtShift v w m ≡ nonDividingShift v w p [MOD p] := by
      apply crtShift_modEq
      rw [fourAndOddPrimes, mem_insert, mem_filter, mem_Icc]
      refine .inr ⟨⟨op, ?_⟩, pp⟩
      exact (le_of_dvd (zero_lt_three.trans_le hk.1) dp).trans hk.2
    rw [dvd_iff_mod_eq_zero, add_mod, meq, ← add_mod, dvd_iff_mod_eq_zero, add_mod w, meq,
      ← add_mod, ← dvd_iff_mod_eq_zero, ← dvd_iff_mod_eq_zero]
    exact not_dvd_nonDividingShift_of_three_le op

lemma odd_add_crtShift : Odd (w + crtShift v w m) := by
  rw [← not_even_iff_odd, even_iff_two_dvd]
  have meq : crtShift v w m ≡ nonDividingShift v w 4 [MOD 2] := by
    apply ModEq.of_dvd (show 2 ∣ 4 by decide)
    simp [crtShift_modEq, fourAndOddPrimes]
  rw [dvd_iff_mod_eq_zero, add_mod, meq, ← add_mod, ← dvd_iff_mod_eq_zero]
  simp only [nonDividingShift, ↓reduceIte]
  have key := min'_mem _ (nonempty_double_not_dvd_four v w)
  simp_all

/-- Lemma 2.2. A `VWPair u m` always exists. -/
def of (u m : ℕ) : VWPair u m where
  v := m + 1 + crtShift (m + 1) (m + 1 + u) m
  w := m + 1 + u + crtShift (m + 1) (m + 1 + u) m
  eq_add := by lia
  m_lt_v := by lia
  w_odd := odd_add_crtShift
  not_dvd _ := crtShift_not_dvd

/-- When `0 < u ≤ m`, `v` and `w` are coprime. -/
lemma of_coprime (hu : 0 < u) (hm : u ≤ m) : (of u m).v.Coprime (of u m).w := by
  by_contra h
  rw [Prime.not_coprime_iff_dvd] at h
  obtain ⟨p, pp, dv, dw⟩ := h
  obtain rfl | op := pp.eq_two_or_odd'
  · grind [(of u m).w_odd]
  rw [pp.odd_iff] at op
  obtain hp | hp := le_or_gt p m
  · exact ((of u m).not_dvd p (mem_Icc.mpr ⟨op, hp⟩)).1 dv
  rw [(of u m).eq_add, Nat.dvd_add_left dv] at dw
  grind [le_of_dvd hu dw]

end VWPair

open Fin Finset

variable {n m s B : ℕ} {vw : VWPair (m + ∑ i ∈ range n, primeChain s i) B}

variable (vw) in
/-- An `(n + 3)`-tuple reducing to `chainTup n m s`. -/
def vwTup (i : Fin (n + 3)) : ℤ :=
  i.addCases (primeChain s ·.1) fun
    | 0 => vw.v
    | 1 => -vw.w
    | 2 => m

lemma vwTup_compl : {natAdd n 0, natAdd n 1}ᶜ = insert (natAdd n 2) (univ.map (castAddEmb 3)) := by
  ext i
  simp_rw [mem_compl, mem_insert, mem_singleton, mem_map, mem_univ, true_and, coe_castAddEmb]
  cases i using addCases <;> grind

lemma isSubsumBlock_vwTup (hB : m + ∑ i ∈ range n, primeChain s i ≤ B) :
    IsSubsumBlock (vwTup vw) {natAdd n 0, natAdd n 1} := by
  have nmem : natAdd n 2 ∉ univ.map (castAddEmb 3) := by
    simp_rw [mem_map, mem_univ, true_and, not_exists, coe_castAddEmb, ← Fin.val_inj]
    grind
  have : ∑ i ∈ {natAdd n 0, natAdd n 1}ᶜ, (vwTup vw i).natAbs =
      m + ∑ i ∈ range n, primeChain s i := by
    simp_rw [vwTup_compl, sum_insert nmem, sum_map, coe_castAddEmb, vwTup, addCases_left,
      addCases_right, Int.natAbs_natCast, sum_univ_eq_sum_range]
  have vlb : m + ∑ i ∈ range n, primeChain s i < vw.v := hB.trans_lt vw.m_lt_v
  apply IsSubsumBlock.pair_of_sum_natAbs_lt
  · simp_rw [this, vwTup, addCases_right, Int.natAbs_natCast, vlb]
  · simp_rw [this, vwTup, addCases_right, Int.natAbs_neg, Int.natAbs_natCast, vw.eq_add]
    lia
  · simp_rw [vwTup, addCases_right, mul_neg, Left.neg_nonpos_iff, ← Nat.cast_mul]
    exact Int.natCast_nonneg _

lemma tupReduce_vwTup {c₂ : n + 1 = n + 3 - #{natAdd n 0, natAdd n 1}} :
    tupReduce (vwTup vw) {natAdd n 0, natAdd n 1} c₂ = chainTup n m s := by
  ext i
  unfold tupReduce
  cases i using lastCases with
  | last =>
    rw [lastCases_last, sum_pair (by simp)]
    have : last (n + 1) = natAdd n (1 : Fin 2) := rfl
    simp_rw [vwTup, chainTup, this, addCases_right, vw.eq_add]
    lia
  | cast i =>
    have prel : #{natAdd n (0 : Fin 3), natAdd n 1}ᶜ = n + 1 := by simp [card_compl]
    have : complRank {natAdd n 0, natAdd n 1} c₂ = lastCases (natAdd n 2) (castAdd 3) := by
      refine (orderEmbOfFin_unique prel (fun i ↦ ?_) (fun i j h ↦ ?_)).symm
      · rw [vwTup_compl]
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
    simp_rw [lastCases_castSucc, this, vwTup, chainTup]
    cases i using lastCases with
    | last =>
      have last_eq : (last n).castSucc = natAdd n (0 : Fin 2) := rfl
      rw [lastCases_last, addCases_right, last_eq, addCases_right]
    | cast i =>
      have cast_eq : i.castSucc.castSucc = castAdd 2 i := rfl
      rw [lastCases_castSucc, addCases_left, cast_eq, addCases_left]

lemma strongSSC_vwTup (hm : 0 < m) (hs : m ≤ s) (hB : m + ∑ i ∈ range n, primeChain s i ≤ B) :
    StrongSSC (vwTup vw) := by
  have c : n + 1 = n + 3 - #{natAdd n (0 : Fin 3), natAdd n 1} := by simp
  apply (isSubsumBlock_vwTup hB).strongSSC_tupReduce c
  rw [tupReduce_vwTup]
  exact strongSSC_chainTup hm hs
