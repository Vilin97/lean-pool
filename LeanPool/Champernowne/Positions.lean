/-
Copyright (c) 2026 Arthur Champernowne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Champernowne
-/
module

public import LeanPool.Champernowne.DigitCount
public import LeanPool.Champernowne.Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Position arithmetic & prefix decomposition

`champIndex b n` locates digit position `n` in the base-`b` stream: the
greatest `N` whose complete block `champBlocks b N` fits within the first
`n` digits. The chain `champBlocks b (champIndex b n) <+: champPrefix b n
<+: champBlocks b (champIndex b n + 1)` transfers occurrence counts from
complete blocks to arbitrary prefixes with a one-number error, giving the
two-sided comparison between `b^k · countOccurrences w (champPrefix b n)`
and `n` with error `O(k)·b^(2k)·b^M`.
-/

@[expose] public section

namespace Champernowne

/-- Greatest `N` with `(champBlocks b N).length ≤ n`. -/
def champIndex (b n : ℕ) : ℕ :=
  Nat.findGreatest (fun N => (champBlocks b N).length ≤ n) n

theorem length_champBlocks_champIndex_le (b n : ℕ) :
    (champBlocks b (champIndex b n)).length ≤ n := by
  have h0 : (champBlocks b 0).length ≤ n := by simp [champBlocks]
  exact Nat.findGreatest_spec (P := fun N => (champBlocks b N).length ≤ n)
    (Nat.zero_le n) h0

theorem lt_length_champBlocks_champIndex_succ (b n : ℕ) :
    n < (champBlocks b (champIndex b n + 1)).length := by
  rcases Nat.lt_or_ge n (champIndex b n + 1) with h | h
  · exact lt_of_lt_of_le h (le_length_champBlocks b _)
  · have hng := Nat.findGreatest_is_greatest
      (P := fun N => (champBlocks b N).length ≤ n)
      (k := champIndex b n + 1) (Nat.lt_succ_self _) h
    exact Nat.lt_of_not_le hng

/-- `champPrefix b n` is a prefix of the blocks it is carved from. -/
theorem champPrefix_prefix (b n : ℕ) : champPrefix b n <+: champBlocks b n :=
  List.take_prefix n _

/-- Complete blocks below position `n` form a prefix of `champPrefix b n`. -/
theorem champBlocks_prefix_champPrefix {b N n : ℕ}
    (h : (champBlocks b N).length ≤ n) :
    champBlocks b N <+: champPrefix b n := by
  have hNn : N ≤ n := le_trans (le_length_champBlocks b N) h
  exact List.prefix_of_prefix_length_le (champBlocks_prefix hNn)
    (champPrefix_prefix b n) (by rw [length_champPrefix]; exact h)

/-- Position `n` lies within one number's digits of the complete blocks. -/
theorem n_lt_length_champIndex_add (b n : ℕ) :
    n < (champBlocks b (champIndex b n)).length
      + (bigDigits b (champIndex b n + 1)).length := by
  have h := lt_length_champBlocks_champIndex_succ b n
  rwa [champBlocks_succ, List.length_append] at h

/-- The straddling number has at most `M + 1` digits. -/
theorem length_bigDigits_champIndex_succ_le {b n M : ℕ} (hb : 1 < b)
    (h2 : champIndex b n + 1 ≤ b ^ M) :
    (bigDigits b (champIndex b n + 1)).length ≤ M + 1 := by
  rw [bigDigits, List.length_reverse]
  refine (Nat.digits_length_le_iff hb _).mpr ?_
  calc champIndex b n + 1 ≤ b ^ M := h2
  _ < b ^ (M + 1) := Nat.pow_lt_pow_right hb (Nat.lt_succ_self M)

/-! ### General-`w` straddle transfer

Only the lower transfer is proved against the counting machinery (the
stream sandwich `sum_le_countOccurrences_champBlocks`, the
general-`N` result `le_base_pow_countOccurrences_champBlocks` from
`DigitCount.lean`, and the `champIndex` straddle). The upper transfer is
then *derived* from the lower one by a complement/pigeonhole argument
over all `b^k` length-`k` words (`allWords`), at the price of one extra
`b^k` factor in the error constant. -/

/-- `champBlocks (champIndex n)` is a genuine prefix of `champPrefix n`, so
its occurrence count only ever undercounts. -/
theorem le_countOccurrences_champPrefix (b n : ℕ) {w : List ℕ} (hwne : w ≠ []) :
    countOccurrences w (champBlocks b (champIndex b n))
      ≤ countOccurrences w (champPrefix b n) := by
  obtain ⟨l, hl⟩ := champBlocks_prefix_champPrefix (length_champBlocks_champIndex_le b n)
  rw [← hl]
  have h := add_countOccurrences_le_append hwne (champBlocks b (champIndex b n)) l
  omega

/-- Main transfer, lower: for `b^(M-1) ≤ champIndex b n + 1 ≤ b^M` and
`w.length ≤ M`, `n ≤ b^k · countOccurrences w (champPrefix b n) +
7(k+1)·b^k·b^M`. -/
theorem le_base_pow_countOccurrences_champPrefix {b : ℕ} (hb : 1 < b) (n M : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hM : 0 < M) (hwM : w.length ≤ M)
    (h1 : b ^ (M - 1) ≤ champIndex b n + 1) (h2 : champIndex b n + 1 ≤ b ^ M) :
    n ≤ b ^ w.length * countOccurrences w (champPrefix b n)
      + 7 * (w.length + 1) * b ^ w.length * b ^ M := by
  have hS := sum_le_countOccurrences_champBlocks (b := b) hwne (champIndex b n)
  have hDig := le_base_pow_countOccurrences_champBlocks hb (champIndex b n) M hw hwne hM hwM h1 h2
  have hlen := n_lt_length_champIndex_add b n
  have hstraddle := length_bigDigits_champIndex_succ_le hb h2
  have hle := le_countOccurrences_champPrefix b n hwne (w := w)
  have hMpow : M + 1 ≤ b ^ M := by
    have h0 := linear_le_const_mul_pow hb 0 M; simpa using h0
  rw [length_champBlocks] at hlen
  have hSmul : b ^ w.length
      * (∑ n ∈ Finset.Ico 1 (champIndex b n + 1), countOccurrences w (bigDigits b n))
      ≤ b ^ w.length * countOccurrences w (champBlocks b (champIndex b n)) :=
    Nat.mul_le_mul_left _ hS
  have hlemul : b ^ w.length * countOccurrences w (champBlocks b (champIndex b n))
      ≤ b ^ w.length * countOccurrences w (champPrefix b n) :=
    Nat.mul_le_mul_left _ hle
  have hp : 1 ≤ b ^ w.length := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hMscale : M + 1 ≤ b ^ w.length * b ^ M := by
    calc M + 1 ≤ b ^ M := hMpow
    _ = 1 * b ^ M := by ring
    _ ≤ b ^ w.length * b ^ M := Nat.mul_le_mul_right _ hp
  have hbudget : 6 * (w.length + 1) * b ^ M + b ^ w.length * b ^ M
      ≤ 7 * (w.length + 1) * b ^ w.length * b ^ M := by
    have e0 : 6 * (w.length + 1) * b ^ M ≤ 6 * (w.length + 1) * b ^ w.length * b ^ M := by
      calc 6 * (w.length + 1) * b ^ M = 6 * (w.length + 1) * 1 * b ^ M := by ring
      _ ≤ 6 * (w.length + 1) * b ^ w.length * b ^ M :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)
    have e1 : b ^ w.length * b ^ M ≤ (w.length + 1) * b ^ w.length * b ^ M := by
      have hh : b ^ w.length ≤ (w.length + 1) * b ^ w.length :=
        Nat.le_mul_of_pos_left _ (by omega)
      exact Nat.mul_le_mul_right _ hh
    have e2 : 6 * (w.length + 1) * b ^ w.length * b ^ M + (w.length + 1) * b ^ w.length * b ^ M
        = 7 * (w.length + 1) * b ^ w.length * b ^ M := by ring
    omega
  omega

/-- Main transfer, upper — derived from the lower transfer by complement:
a window position matches exactly one of the `b^k` length-`k` words, so
`b^k·(occ w + Σ_{v ≠ w} occ v) ≤ b^k·(n+1)` (`sum_countOccurrences_allWords_le`),
while the lower transfer applied to each of the `b^k − 1` words `v ≠ w`
bounds `Σ_{v ≠ w} b^k·occ v` from below. Costs one extra `b^k` factor in
the error over the lower bound's `7(k+1)·b^k·b^M`. -/
theorem base_pow_countOccurrences_champPrefix_le {b : ℕ} (hb : 1 < b) (n M : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hM : 0 < M) (hwM : w.length ≤ M)
    (h1 : b ^ (M - 1) ≤ champIndex b n + 1) (h2 : champIndex b n + 1 ≤ b ^ M) :
    b ^ w.length * countOccurrences w (champPrefix b n)
      ≤ n + 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ M := by
  have hk : 0 < w.length := List.length_pos_of_ne_nil hwne
  have hwW : w ∈ allWords b w.length := mem_allWords.mpr ⟨rfl, hw⟩
  -- Pigeonhole over all length-k words, with the w term split off.
  have hpig := sum_countOccurrences_allWords_le b w.length (champPrefix b n)
  rw [length_champPrefix, ← Finset.add_sum_erase _ _ hwW] at hpig
  have hpig' := Nat.mul_le_mul_left (b ^ w.length) hpig
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at hpig'
  -- The lower transfer at each of the other words.
  have hlow : ∀ v ∈ (allWords b w.length).erase w,
      n ≤ b ^ w.length * countOccurrences v (champPrefix b n)
        + 7 * (w.length + 1) * b ^ w.length * b ^ M := by
    intro v hv
    obtain ⟨hvlen, hvlt⟩ := mem_allWords.mp (Finset.mem_of_mem_erase hv)
    have hvne : v ≠ [] := by
      intro hnil
      rw [hnil] at hvlen
      simp only [List.length_nil] at hvlen
      omega
    have hvM : v.length ≤ M := by rw [hvlen]; exact hwM
    have h := le_base_pow_countOccurrences_champPrefix hb n M hvlt hvne hM hvM h1 h2
    rwa [hvlen] at h
  have hsum := Finset.sum_le_sum hlow
  simp only [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hsum
  -- Count of the other words: card + 1 = b^k.
  have hcard : ((allWords b w.length).erase w).card + 1 = b ^ w.length := by
    rw [Finset.card_erase_of_mem hwW, card_allWords]
    have hp : 0 < b ^ w.length := pow_pos (by omega) _
    omega
  -- Rewrite the goal's error as b^k · (lower-bound error), then abstract.
  rw [show 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ M
      = b ^ w.length * (7 * (w.length + 1) * b ^ w.length * b ^ M) by
    rw [two_mul, pow_add]; ring]
  set P := b ^ w.length with hPdef
  set E := 7 * (w.length + 1) * P * b ^ M with hEdef
  set C := countOccurrences w (champPrefix b n) with hCdef
  set S := ∑ v ∈ (allWords b w.length).erase w,
    countOccurrences v (champPrefix b n) with hSdef
  set c := ((allWords b w.length).erase w).card with hcdef
  -- Bridges between the omega atoms.
  have g1 : c * n + n = P * n := by rw [← hcard]; ring
  have g2 : c * E + E = P * E := by rw [← hcard]; ring
  have g3 : P ≤ E := by
    have hbM : 1 ≤ b ^ M := Nat.one_le_pow _ _ (by omega)
    calc P = 1 * P * 1 := by ring
    _ ≤ 7 * (w.length + 1) * P * b ^ M :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) hbM
  -- hpig' : P*C + P*S ≤ P*n + P; hsum : c*n ≤ P*S + c*E; goal : P*C ≤ n + P*E.
  omega

/-! ### Prefix chain -/

/-- `champPrefix b n` sits inside the complete blocks covering position `n`.
This completes the prefix chain `champBlocks (champIndex n) <+: champPrefix n <+:
champBlocks (champIndex n + 1)`. -/
theorem champPrefix_prefix_champBlocks {b n N : ℕ}
    (h : n ≤ (champBlocks b N).length) :
    champPrefix b n <+: champBlocks b N := by
  rcases le_total n N with hnN | hNn
  · exact (champPrefix_prefix b n).trans (champBlocks_prefix hnN)
  · exact List.prefix_of_prefix_length_le (champPrefix_prefix b n)
      (champBlocks_prefix hNn) (by rw [length_champPrefix]; exact h)

end Champernowne
