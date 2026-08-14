/-
Copyright (c) 2026 Jose Fonollosa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose Fonollosa
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring.RingNF

/-!
# Minimum modulus for the unique multiset-sum problem

Formalization of the paper *Minimum modulus for the unique multiset-sum
problem, with an application to computing the permanent* (J. A. R.
Fonollosa, 2026) for the super-increasing set `A = {2^i − 1 : 0 ≤ i < n}`.

Everything is stated in `k`-space (the paper's `k = c + 1` variables), over ℕ:
a candidate multiset is `k : ℕ → ℕ` with digit sum `∑_{i<n} k i = n`, and
validity mod `N` says the only such `k` with `∑ k_i·a_i ≡ ∑ a_i [MOD N]` is
all-ones.  The paper's signed multiples `V = ±jN` enter only through the
congruence `M ≡ 2^n − 1 [MOD N]` on `M = ∑ k_i 2^i`, so no integers appear.

Contents:
* definitions: `a`, `dsum`, `val`, `Supp`, `Valid`
* representation constructors (existence half of the paper's master
  achievability criterion, Prop. 1):
  `ones_rep`, `ones_erase_rep`, `exists_rep_le`, `exists_rep_lt`,
  `exists_rep_compl`, and contiguity `dsum_succ_of_lt` / `exists_dsum_eq`
* `theoremB` (paper §6, optimality / lower bound) — **complete**
* `gmin` and the greedy minimality bound `gmin_le_dsum` (paper Lemma 3,
  downward half), the step lemma `gmin_step` (paper Lemma 4) and the
  `j`-induction bound `slack` (popcount-free, no range restriction)
* `ones_unique` (paper Lemma 2)
* `theoremA` (paper §5, validity / upper bound) — **complete**
* `nmin_eq` — the main theorem `Nmin(n) = 2^n − 2^⌊log₂ n⌋` — **complete,
  no axioms beyond propext / Classical.choice / Quot.sound**
-/

namespace MinModulus

open Finset

/-- The super-increasing set: `a i = 2^i − 1`. -/
def a (i : ℕ) : ℕ := 2 ^ i - 1

/-- Digit sum of `k` on `[0, n)`. -/
def dsum (n : ℕ) (k : ℕ → ℕ) : ℕ := ∑ i ∈ range n, k i

/-- Value of `k` on `[0, n)` with power-of-two coins (paper: `M = Σ k_i 2^i`). -/
def val (n : ℕ) (k : ℕ → ℕ) : ℕ := ∑ i ∈ range n, k i * 2 ^ i

/-- `k` is supported on `[0, n)`. -/
def Supp (n : ℕ) (k : ℕ → ℕ) : Prop := ∀ i, n ≤ i → k i = 0

/-- Validity mod `N` (paper §2, problem statement): the all-ones vector is the only size-`n`
multiset drawn from `A` whose sum is `≡ Σ a_i (mod N)`. -/
def Valid (n N : ℕ) : Prop :=
  ∀ k : ℕ → ℕ, dsum n k = n →
    (∑ i ∈ range n, k i * a i) ≡ (∑ i ∈ range n, a i) [MOD N] →
    ∀ i < n, k i = 1

/-! ### Basic identities -/

lemma sum_two_pow (w : ℕ) : ∑ i ∈ range w, 2 ^ i = 2 ^ w - 1 := by
  induction w with
  | zero => rfl
  | succ w ih =>
    have h1 : 1 ≤ 2 ^ w := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    rw [Finset.sum_range_succ, ih]
    omega

/-- The paper's `Σ k_i a_i = M − Σ k_i` identity, subtraction-free. -/
lemma sum_a_add_dsum (n : ℕ) (k : ℕ → ℕ) :
    (∑ i ∈ range n, k i * a i) + dsum n k = val n k := by
  unfold dsum val
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : 1 ≤ 2 ^ i := Nat.one_le_pow _ _ (by norm_num)
  have ha : a i + 1 = 2 ^ i := Nat.sub_add_cancel h1
  calc k i * a i + k i = k i * (a i + 1) := by ring
    _ = k i * 2 ^ i := by rw [ha]

/-- To refute validity it suffices to exhibit `k` with digit sum `n` and value
`M ≠ 2^n − 1` congruent to `2^n − 1` mod `N`. -/
lemma not_valid_of_witness {n N M : ℕ} (hn : 1 ≤ n)
    (hne : M ≠ 2 ^ n - 1) (hmod : M ≡ (2 ^ n - 1) [MOD N])
    (h : ∃ k, val n k = M ∧ dsum n k = n) : ¬ Valid n N := by
  obtain ⟨k, hv, hd⟩ := h
  intro hval
  -- the all-ones vector
  have hd1 : dsum n (fun _ => 1) = n := by
    unfold dsum
    rw [Finset.sum_const, smul_eq_mul, mul_one, card_range]
  have hv1 : val n (fun _ => 1) = 2 ^ n - 1 := by
    unfold val
    calc (∑ i ∈ range n, 1 * 2 ^ i) = ∑ i ∈ range n, 2 ^ i :=
          Finset.sum_congr rfl fun i _ => one_mul _
      _ = 2 ^ n - 1 := sum_two_pow n
  -- convert `hmod` into the congruence `Valid` expects
  have e1 : (∑ i ∈ range n, k i * a i) + n = M := by
    have h0 := sum_a_add_dsum n k
    rw [hd, hv] at h0
    exact h0
  have e2 : (∑ i ∈ range n, a i) + n = 2 ^ n - 1 := by
    have h0 := sum_a_add_dsum n (fun _ => 1)
    simp only [one_mul] at h0
    rw [hd1, hv1] at h0
    exact h0
  have hcong : (∑ i ∈ range n, k i * a i) ≡ (∑ i ∈ range n, a i) [MOD N] := by
    apply Nat.ModEq.add_right_cancel' n
    rw [e1, e2]
    exact hmod
  -- Valid forces k = all-ones, contradicting val = M ≠ 2^n − 1
  have hone := hval k hd hcong
  have hvk : val n k = 2 ^ n - 1 := by
    unfold val
    calc (∑ i ∈ range n, k i * 2 ^ i) = ∑ i ∈ range n, 2 ^ i :=
          Finset.sum_congr rfl fun i hi => by
            rw [hone i (Finset.mem_range.mp hi), one_mul]
      _ = 2 ^ n - 1 := sum_two_pow n
  omega

/-! ### Padding and top-coin composition -/

lemma supp_mono {e w : ℕ} (h : e ≤ w) {k : ℕ → ℕ} (hs : Supp e k) : Supp w k :=
  fun i hi => hs i (by omega)

lemma val_pad {e w : ℕ} (h : e ≤ w) {k : ℕ → ℕ} (hs : Supp e k) :
    val w k = val e k := by
  unfold val
  refine (Finset.sum_subset (Finset.range_subset_range.mpr h) fun i _ hni => ?_).symm
  have he : e ≤ i := by
    by_contra hc
    exact hni (Finset.mem_range.mpr (by omega))
  rw [hs i he, zero_mul]

lemma dsum_pad {e w : ℕ} (h : e ≤ w) {k : ℕ → ℕ} (hs : Supp e k) :
    dsum w k = dsum e k := by
  unfold dsum
  refine (Finset.sum_subset (Finset.range_subset_range.mpr h) fun i _ hni => ?_).symm
  have he : e ≤ i := by
    by_contra hc
    exact hni (Finset.mem_range.mpr (by omega))
  exact hs i he

/-- Put `c` coins on the top index `w` of a representation supported below `w`. -/
lemma update_top (w c : ℕ) (k : ℕ → ℕ) (hs : Supp w k) :
    Supp (w + 1) (Function.update k w c) ∧
    val (w + 1) (Function.update k w c) = val w k + c * 2 ^ w ∧
    dsum (w + 1) (Function.update k w c) = dsum w k + c := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [Function.update_of_ne (by omega)]
    exact hs i (by omega)
  · unfold val
    rw [Finset.sum_range_succ, Function.update_self]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.mp hi
    rw [Function.update_of_ne (by omega)]
  · unfold dsum
    rw [Finset.sum_range_succ, Function.update_self]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.mp hi
    rw [Function.update_of_ne (by omega)]

/-- Shift a representation up one index, placing `c` at index 0. -/
def shift (c : ℕ) (k : ℕ → ℕ) : ℕ → ℕ := fun i => if i = 0 then c else k (i - 1)

lemma shift_supp {w c : ℕ} {k : ℕ → ℕ} (h : Supp w k) :
    Supp (w + 1) (shift c k) := by
  intro i hi
  unfold shift
  rw [ite_eq_right (by omega)]
  exact h (i - 1) (by omega)

lemma shift_val (w c : ℕ) (k : ℕ → ℕ) :
    val (w + 1) (shift c k) = 2 * val w k + c := by
  unfold val
  rw [Finset.sum_range_succ']
  have h0 : shift c k 0 * 2 ^ 0 = c := by unfold shift; simp
  have hstep : ∀ i ∈ range w, shift c k (i + 1) * 2 ^ (i + 1) = 2 * (k i * 2 ^ i) := by
    intro i _
    unfold shift
    rw [ite_eq_right (Nat.succ_ne_zero i), Nat.add_sub_cancel, pow_succ]
    ring
  rw [Finset.sum_congr rfl hstep, h0, ← Finset.mul_sum]

lemma shift_dsum (w c : ℕ) (k : ℕ → ℕ) :
    dsum (w + 1) (shift c k) = dsum w k + c := by
  unfold dsum
  rw [Finset.sum_range_succ']
  have h0 : shift c k 0 = c := by unfold shift; simp
  have hstep : ∀ i ∈ range w, shift c k (i + 1) = k i := by
    intro i _
    unfold shift
    rw [ite_eq_right (Nat.succ_ne_zero i), Nat.add_sub_cancel]
  rw [Finset.sum_congr rfl hstep, h0]

/-! ### Explicit representations (bases of the four witness families, paper §6) -/

/-- The all-ones representation of `2^w − 1`. -/
lemma ones_rep (w : ℕ) :
    ∃ k, Supp w k ∧ val w k = 2 ^ w - 1 ∧ dsum w k = w := by
  refine ⟨fun i => if i < w then 1 else 0, fun i hi => ite_eq_right (by omega), ?_, ?_⟩
  · unfold val
    calc (∑ i ∈ range w, (if i < w then 1 else 0) * 2 ^ i)
        = ∑ i ∈ range w, 2 ^ i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [ite_eq_left (Finset.mem_range.mp hi), one_mul]
      _ = 2 ^ w - 1 := sum_two_pow w
  · unfold dsum
    calc (∑ i ∈ range w, (if i < w then 1 else 0))
        = ∑ i ∈ range w, 1 := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [ite_eq_left (Finset.mem_range.mp hi)]
      _ = w := by rw [Finset.sum_const, smul_eq_mul, mul_one, card_range]

/-- All-ones minus bit `e`: represents `2^w − 1 − 2^e` with `w − 1` coins. -/
lemma ones_erase_rep {w e : ℕ} (he : e < w) :
    ∃ k, Supp w k ∧ val w k = 2 ^ w - 1 - 2 ^ e ∧ dsum w k = w - 1 := by
  have hmem : e ∈ range w := Finset.mem_range.mpr he
  have h1 : 1 ≤ 2 ^ e := Nat.one_le_pow _ _ (by norm_num)
  refine ⟨fun i => if i = e then 0 else if i < w then 1 else 0,
    fun i hi => by
      have hne : ¬ i = e := by omega
      have hlt : ¬ i < w := by omega
      simp [hne, hlt], ?_, ?_⟩
  · simp only [val]
    have hsplit : (∑ i ∈ range w,
          (if i = e then 0 else if i < w then 1 else 0) * 2 ^ i)
        + (∑ i ∈ range w, if i = e then 2 ^ e else 0)
        = ∑ i ∈ range w, 2 ^ i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      by_cases hie : i = e
      · subst hie; simp
      · simp [hie, Finset.mem_range.mp hi]
    have hone : (∑ i ∈ range w, if i = e then 2 ^ e else 0) = 2 ^ e := by
      rw [Finset.sum_ite_eq' (range w) e (fun _ => 2 ^ e), ite_eq_left hmem]
    rw [sum_two_pow] at hsplit
    omega
  · simp only [dsum]
    have hsplit : (∑ i ∈ range w, (if i = e then 0 else if i < w then 1 else 0))
        + (∑ i ∈ range w, if i = e then 1 else 0)
        = ∑ i ∈ range w, 1 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      by_cases hie : i = e
      · subst hie; simp
      · simp [hie, Finset.mem_range.mp hi]
    have hone : (∑ i ∈ range w, if i = e then 1 else 0) = 1 := by
      rw [Finset.sum_ite_eq' (range w) e (fun _ => 1), ite_eq_left hmem]
    have hcard : (∑ i ∈ range w, (1 : ℕ)) = w := by
      rw [Finset.sum_const, smul_eq_mul, mul_one, card_range]
    omega

/-- Any `x < 2^w` has a representation on `[0, w)` with digit sum `≤ w`. -/
lemma exists_rep_le : ∀ w x : ℕ, x < 2 ^ w →
    ∃ k, Supp w k ∧ val w k = x ∧ dsum w k ≤ w := by
  intro w
  induction w with
  | zero =>
    intro x hx
    rw [pow_zero] at hx
    obtain rfl : x = 0 := by omega
    refine ⟨fun _ => 0, fun _ _ => rfl, ?_, ?_⟩ <;> simp [val, dsum]
  | succ w ih =>
    intro x hx
    have h2 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    rcases Nat.lt_or_ge x (2 ^ w) with h | h
    · obtain ⟨k, hs, hv, hd⟩ := ih x h
      exact ⟨k, supp_mono (by omega) hs,
        by rw [val_pad (by omega) hs, hv],
        by rw [dsum_pad (by omega) hs]; omega⟩
    · obtain ⟨k, hs, hv, hd⟩ := ih (x - 2 ^ w) (by omega)
      obtain ⟨us, uv, ud⟩ := update_top w 1 k hs
      exact ⟨Function.update k w 1, us, by rw [uv, hv]; omega, by rw [ud]; omega⟩

/-- Sharp version (paper §6, case (i)): `x < 2^w − 1` needs at most `w − 1` coins. -/
lemma exists_rep_lt : ∀ w x : ℕ, x < 2 ^ w - 1 →
    ∃ k, Supp w k ∧ val w k = x ∧ dsum w k ≤ w - 1 := by
  intro w
  induction w with
  | zero =>
    intro x hx
    rw [pow_zero] at hx
    omega
  | succ w ih =>
    intro x hx
    have h2 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    have h1 : 1 ≤ 2 ^ w := Nat.one_le_pow _ _ (by norm_num)
    rcases Nat.lt_or_ge x (2 ^ w - 1) with h | h
    · obtain ⟨k, hs, hv, hd⟩ := ih x h
      exact ⟨k, supp_mono (by omega) hs,
        by rw [val_pad (by omega) hs, hv],
        by rw [dsum_pad (by omega) hs]; omega⟩
    · rcases Nat.lt_or_ge x (2 ^ w) with h' | h'
      · -- x = 2^w − 1: the all-ones representation, w coins
        have hx' : x = 2 ^ w - 1 := by omega
        obtain ⟨k, hs, hv, hd⟩ := ones_rep w
        exact ⟨k, supp_mono (by omega) hs,
          by rw [val_pad (by omega) hs, hv, hx'],
          by rw [dsum_pad (by omega) hs]; omega⟩
      · -- 2^w ≤ x < 2^{w+1} − 1: recurse sharply below a top coin
        have hw1 : 1 ≤ w := by
          rcases Nat.eq_zero_or_pos w with rfl | hw
          · norm_num at hx h'
            omega
          · exact hw
        obtain ⟨k, hs, hv, hd⟩ := ih (x - 2 ^ w) (by omega)
        obtain ⟨us, uv, ud⟩ := update_top w 1 k hs
        exact ⟨Function.update k w 1, us, by rw [uv, hv]; omega, by rw [ud]; omega⟩

/-- Complement representation (paper §6, case (iii)): if `0 ≠ s < 2^w` is not a
power of two, then `2^w − 1 − s` needs at most `w − 2` coins. -/
lemma exists_rep_compl : ∀ w s : ℕ, s < 2 ^ w → s ≠ 0 → (¬ ∃ e, s = 2 ^ e) →
    ∃ k, Supp w k ∧ val w k = 2 ^ w - 1 - s ∧ dsum w k ≤ w - 2 := by
  intro w
  induction w with
  | zero =>
    intro s hs h0 _
    rw [pow_zero] at hs
    omega
  | succ w ih =>
    intro s hs h0 hp
    have h2 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    have h1 : 1 ≤ 2 ^ w := Nat.one_le_pow _ _ (by norm_num)
    rcases Nat.even_or_odd s with ⟨q, hq⟩ | ⟨q, hq⟩
    · -- s = 2q even: coin at 0 + shifted witness for q
      have hq0 : q ≠ 0 := by omega
      have hqp : ¬ ∃ e, q = 2 ^ e := by
        rintro ⟨e, rfl⟩
        exact hp ⟨e + 1, by rw [pow_succ]; omega⟩
      have hqlt : q < 2 ^ w := by omega
      have hw2 : 2 ≤ w := by
        rcases Nat.lt_or_ge w 2 with hw | hw
        · exfalso
          rcases (by omega : w = 0 ∨ w = 1) with rfl | rfl
          · -- w = 0: s < 2 but s = 2q ≥ 2
            norm_num at hs
            omega
          · -- w = 1: q = 1 = 2^0, excluded as a power
            norm_num at hqlt
            exact hqp ⟨0, by rw [pow_zero]; omega⟩
        · exact hw
      obtain ⟨k, hks, hkv, hkd⟩ := ih q hqlt hq0 hqp
      refine ⟨shift 1 k, shift_supp hks, ?_, ?_⟩
      · rw [shift_val, hkv]; omega
      · rw [shift_dsum]; omega
    · -- s = 2q + 1 odd
      have hq1 : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with rfl | h
        · exact absurd ⟨0, by rw [pow_zero]; omega⟩ hp
        · exact h
      have hqlt : q < 2 ^ w := by omega
      by_cases hqp : ∃ e, q = 2 ^ e
      · -- q = 2^e: base is all-ones-minus-bit-e, exactly w − 1 coins
        obtain ⟨e, rfl⟩ := hqp
        have hew : e < w := by
          by_contra hc
          push Not at hc
          have hle' : 2 ^ w ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hc
          omega
        have he2 : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
        have hle : 2 ^ (e + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
        obtain ⟨k, hks, hkv, hkd⟩ := ones_erase_rep hew
        refine ⟨shift 0 k, shift_supp hks, ?_, ?_⟩
        · rw [shift_val, hkv]; omega
        · rw [shift_dsum]; omega
      · -- q not a power: shifted witness for q
        obtain ⟨k, hks, hkv, hkd⟩ := ih q hqlt (by omega) hqp
        refine ⟨shift 0 k, shift_supp hks, ?_, ?_⟩
        · rw [shift_val, hkv]; omega
        · rw [shift_dsum]; omega

/-! ### Contiguity (paper Lemma 3, upward direction) -/

/-- Splitting step: a representation of `M` with digit sum `s < M` yields one
with digit sum `s + 1` (replace a coin `2^i`, `i ≥ 1`, by two `2^{i-1}`s). -/
lemma dsum_succ_of_lt {n M s : ℕ}
    (h : ∃ k, val n k = M ∧ dsum n k = s) (hlt : s < M) :
    ∃ k, val n k = M ∧ dsum n k = s + 1 := by
  obtain ⟨k, hv, hd⟩ := h
  -- some index i ≥ 1 carries a coin, else value = digit sum
  have hex : ∃ i, 1 ≤ i ∧ i < n ∧ 1 ≤ k i := by
    by_contra hno
    push Not at hno
    have hvd : val n k = dsum n k := by
      unfold val dsum
      refine Finset.sum_congr rfl fun i hi => ?_
      rcases Nat.eq_zero_or_pos i with rfl | hi1
      · simp
      · have hk0 : k i = 0 := by
          have := hno i hi1 (Finset.mem_range.mp hi)
          omega
        rw [hk0]
        ring
    omega
  obtain ⟨i, hi1, hin, hki⟩ := hex
  obtain ⟨A, hA⟩ : ∃ A, k i = A + 1 := ⟨k i - 1, by omega⟩
  have hii : i - 1 ≠ i := by omega
  have hmem : i ∈ range n := Finset.mem_range.mpr hin
  have hmem' : i - 1 ∈ (range n).erase i :=
    Finset.mem_erase.mpr ⟨hii, Finset.mem_range.mpr (by omega)⟩
  -- decompose a sum by peeling index i, then i − 1
  have decomp : ∀ f : ℕ → ℕ, (∑ j ∈ range n, f j)
      = f i + (f (i - 1) + ∑ j ∈ ((range n).erase i).erase (i - 1), f j) := by
    intro f
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem']
  refine ⟨fun j => if j = i then A else if j = i - 1 then k (i - 1) + 2 else k j,
    ?_, ?_⟩
  · -- value is preserved
    unfold val
    rw [decomp fun j =>
      (if j = i then A else if j = i - 1 then k (i - 1) + 2 else k j) * 2 ^ j]
    unfold val at hv
    rw [decomp fun j => k j * 2 ^ j] at hv
    have hrest : (∑ j ∈ ((range n).erase i).erase (i - 1),
        (if j = i then A else if j = i - 1 then k (i - 1) + 2 else k j) * 2 ^ j)
        = ∑ j ∈ ((range n).erase i).erase (i - 1), k j * 2 ^ j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      obtain ⟨hj1, hj2⟩ := Finset.mem_erase.mp hj
      obtain ⟨hj3, _⟩ := Finset.mem_erase.mp hj2
      rw [ite_eq_right hj3, ite_eq_right hj1]
    rw [ite_eq_left rfl, ite_eq_right hii, ite_eq_left rfl, hrest]
    rw [hA] at hv
    have hpi : 2 ^ i = 2 ^ (i - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpi] at hv ⊢
    -- (A+1)·2P + B·P + R = M  ⟹  A·2P + (B+2)·P + R = M
    ring_nf at hv ⊢
    omega
  · -- digit sum goes up by one
    unfold dsum
    rw [decomp fun j =>
      if j = i then A else if j = i - 1 then k (i - 1) + 2 else k j]
    unfold dsum at hd
    rw [decomp k] at hd
    have hrest : (∑ j ∈ ((range n).erase i).erase (i - 1),
        (if j = i then A else if j = i - 1 then k (i - 1) + 2 else k j))
        = ∑ j ∈ ((range n).erase i).erase (i - 1), k j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      obtain ⟨hj1, hj2⟩ := Finset.mem_erase.mp hj
      obtain ⟨hj3, _⟩ := Finset.mem_erase.mp hj2
      rw [ite_eq_right hj3, ite_eq_right hj1]
    rw [ite_eq_left rfl, ite_eq_right hii, ite_eq_left rfl, hrest]
    omega

/-- From digit sum `≤ t` to digit sum exactly `t`, provided `t ≤ M`
(the paper's interval `[s_min, M]` of achievable digit sums). -/
lemma exists_dsum_eq {n M t : ℕ}
    (h : ∃ k, val n k = M ∧ dsum n k ≤ t) (htM : t ≤ M) :
    ∃ k, val n k = M ∧ dsum n k = t := by
  obtain ⟨k, hv, hd⟩ := h
  suffices aux : ∀ d s, s + d = t → (∃ k, val n k = M ∧ dsum n k = s) →
      ∃ k, val n k = M ∧ dsum n k = t by
    exact aux (t - dsum n k) (dsum n k) (by omega) ⟨k, hv, rfl⟩
  intro d
  induction d with
  | zero =>
    intro s h0 hk
    obtain rfl : s = t := by omega
    exact hk
  | succ d ih =>
    intro s h0 hk
    exact ih (s + 1) (by omega) (dsum_succ_of_lt hk (by omega))

/-! ### Small arithmetic helpers -/

lemma succ_le_two_pow_pred : ∀ n, 3 ≤ n → n + 1 ≤ 2 ^ (n - 1) := by
  intro n
  induction n with
  | zero => omega
  | succ p ih =>
    intro h
    rcases Nat.lt_or_ge p 3 with h3 | h3
    · have hp : p = 2 := by omega
      subst hp
      norm_num
    · have hp := ih h3
      have h1 : p + 1 - 1 = p := by omega
      rw [h1]
      have h2 : 2 ^ p = 2 * 2 ^ (p - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega

/-! ### Theorem B: optimality (paper §6) -/

/-- **Theorem B** (lower bound): every modulus `2 ≤ N < 2^n − 2^⌊log₂ n⌋` is
invalid for the super-increasing set.  The four witness families of the paper:
(i) `N < 2^{n-1}` — `M = 2^n − 1 + N`; (ii) `N = 2^{n-1}` — `M = 2^{n-1} − 1`
(a negative multiple, `V = −N`); (iii) gap `s := 2^n − N` not a power of two —
`M = 2^n − 1 + N`; (iv) gap `s = 2^e`, `⌊log₂ n⌋ < e ≤ n−2` — `M = 2^e − 1`
(again `V = −N`), where `2^e − 1 ≥ n` is exactly `e > ⌊log₂ n⌋`. -/
theorem theoremB {n N : ℕ} (hn : 2 ≤ n) (hN2 : 2 ≤ N)
    (hNlt : N < 2 ^ n - 2 ^ Nat.log 2 n) : ¬ Valid n N := by
  set m := Nat.log 2 n with hm
  have hmn : 2 ^ m ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hnm : n < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h1m : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
  -- n = 2 makes the N-range empty, so n ≥ 3
  have hn3 : 3 ≤ n := by
    by_contra hc
    have h2 : n = 2 := by omega
    subst h2
    have hlog : Nat.log 2 2 = 1 :=
      Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
    rw [hm, hlog] at hNlt
    norm_num at hNlt
    omega
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h1p : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
  have hnlt : n < 2 ^ n := Nat.lt_two_pow_self
  have hn12 : n + 1 ≤ 2 ^ (n - 1) := succ_le_two_pow_pred n hn3
  have hm_le : 2 ^ m ≤ 2 ^ (n - 1) := by omega   -- 2^m ≤ n < 2^{n-1}
  rcases lt_trichotomy N (2 ^ (n - 1)) with hlt | heq | hgt
  · -- ── case (i): 2 ≤ N < 2^{n-1}; witness value M = 2^n − 1 + N
    obtain ⟨k0, hs, hv, hd⟩ := exists_rep_lt (n - 1) (N - 1) (by omega)
    obtain ⟨us, uv, ud⟩ := update_top (n - 1) 2 k0 hs
    have hn' : n - 1 + 1 = n := by omega
    rw [hn', hv] at uv
    rw [hn'] at ud
    have hbase : ∃ k, val n k = 2 ^ n - 1 + N ∧ dsum n k ≤ n :=
      ⟨Function.update k0 (n - 1) 2, by rw [uv]; omega, by rw [ud]; omega⟩
    have hex := exists_dsum_eq hbase (by omega)
    refine not_valid_of_witness (by omega) (by omega) ?_ hex
    have hle : 2 ^ n - 1 ≤ 2 ^ n - 1 + N := by omega
    refine ((Nat.modEq_iff_dvd' hle).mpr ?_).symm
    have heq' : 2 ^ n - 1 + N - (2 ^ n - 1) = N := by omega
    rw [heq']
  · -- ── case (ii): N = 2^{n-1}; witness value M = 2^{n-1} − 1  (V = −N)
    obtain ⟨k0, hs, hv, hd⟩ := ones_rep (n - 1)
    have hbase : ∃ k, val n k = 2 ^ (n - 1) - 1 ∧ dsum n k ≤ n :=
      ⟨k0, by rw [val_pad (by omega) hs, hv], by rw [dsum_pad (by omega) hs]; omega⟩
    have hex := exists_dsum_eq hbase (by omega)
    refine not_valid_of_witness (by omega) (by omega) ?_ hex
    have hle : 2 ^ (n - 1) - 1 ≤ 2 ^ n - 1 := by omega
    refine (Nat.modEq_iff_dvd' hle).mpr ?_
    have heq' : 2 ^ n - 1 - (2 ^ (n - 1) - 1) = N := by omega
    rw [heq']
  · -- N > 2^{n-1}: the gap s := 2^n − N satisfies 2^m < s < 2^{n-1}
    have hs_ub : 2 ^ n - N < 2 ^ (n - 1) := by omega
    have hs_lb : 2 ^ m < 2 ^ n - N := by omega
    by_cases hpw : ∃ e, 2 ^ n - N = 2 ^ e
    · -- ── case (iv): single-power gap 2^e; witness M = 2^e − 1  (V = −N)
      obtain ⟨e, he⟩ := hpw
      have hme : m < e := by
        by_contra hc
        push Not at hc
        have hle' : 2 ^ e ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hc
        omega
      have he2 : 2 ^ (m + 1) ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hen : e ≤ n - 1 := by
        by_contra hc
        push Not at hc
        have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hc.le
        omega
      obtain ⟨k0, hs0, hv0, hd0⟩ := ones_rep e
      have hbase : ∃ k, val n k = 2 ^ e - 1 ∧ dsum n k ≤ n :=
        ⟨k0, by rw [val_pad (by omega) hs0, hv0],
          by rw [dsum_pad (by omega) hs0, hd0]; omega⟩
      have hex := exists_dsum_eq hbase (by omega)
      refine not_valid_of_witness (by omega) (by omega) ?_ hex
      have hle : 2 ^ e - 1 ≤ 2 ^ n - 1 := by omega
      refine (Nat.modEq_iff_dvd' hle).mpr ?_
      have heq' : 2 ^ n - 1 - (2 ^ e - 1) = N := by omega
      rw [heq']
    · -- ── case (iii): gap with ≥ 2 bits; witness value M = 2^n − 1 + N
      obtain ⟨k0, hs0, hv0, hd0⟩ :=
        exists_rep_compl (n - 1) (2 ^ n - N) hs_ub (by omega) hpw
      obtain ⟨us, uv, ud⟩ := update_top (n - 1) 3 k0 hs0
      have hn' : n - 1 + 1 = n := by omega
      rw [hn', hv0] at uv
      rw [hn'] at ud
      have hbase : ∃ k, val n k = 2 ^ n - 1 + N ∧ dsum n k ≤ n :=
        ⟨Function.update k0 (n - 1) 3, by rw [uv]; omega, by rw [ud]; omega⟩
      have hex := exists_dsum_eq hbase (by omega)
      refine not_valid_of_witness (by omega) (by omega) ?_ hex
      have hle : 2 ^ n - 1 ≤ 2 ^ n - 1 + N := by omega
      refine ((Nat.modEq_iff_dvd' hle).mpr ?_).symm
      have heq' : 2 ^ n - 1 + N - (2 ^ n - 1) = N := by omega
      rw [heq']

/-- Doc §4's concrete case-(iv) example: `n = 5`, `N = 24 = 2^5 − 2^3`
(the single-power gap killed by a negative multiple, ex-Conjecture B). -/
example : ¬ Valid 5 24 :=
  theoremB (by norm_num) (by norm_num)
    (by rw [Nat.log_eq_of_pow_le_of_lt_pow (by norm_num : 2 ^ 2 ≤ 5)
          (by norm_num : 5 < 2 ^ (2 + 1))]
        norm_num)

/-- Doc §4's concrete case-(ii) example: `n = 4`, `N = 8 = 2^{4-1}`
(invalid only via a negative multiple). -/
example : ¬ Valid 4 8 :=
  theoremB (by norm_num) (by norm_num)
    (by rw [Nat.log_eq_of_pow_le_of_lt_pow (by norm_num : 2 ^ 2 ≤ 4)
          (by norm_num : 4 < 2 ^ (2 + 1))]
        norm_num)

/-! ### The greedy digit-sum lower bound (paper Lemma 3, minimality half)

`gmin w M` is the digit sum of the greedy representation of `M` with coins
`2^0, …, 2^w`: the binary digits of `M` below bit `w` plus the whole quotient
`⌊M/2^w⌋` on the top coin.  Everything is proved by induction on `w`, peeling
one bit per step, so only literal `/2` and `%2` appear — `omega`-friendly.
The step lemma `gmin_step` (paper Lemma 4) replaces the paper's popcount
identities: `slack` iterates it over `j`, with no range restriction. -/

/-- Greedy digit sum with coins `2^0..2^w` (`w+1` coin types). -/
def gmin : ℕ → ℕ → ℕ
  | 0, M => M
  | w + 1, M => M % 2 + gmin w (M / 2)

/-- Adding `t` to the target raises the greedy digit sum by at most `t`. -/
lemma gmin_add_le : ∀ w x t, gmin w (x + t) ≤ gmin w x + t := by
  intro w
  induction w with
  | zero => intro x t; simp [gmin]
  | succ w ih =>
    intro x t
    simp only [gmin]
    obtain ⟨t', ht'⟩ : ∃ t', (x + t) / 2 = x / 2 + t' :=
      ⟨(x + t) / 2 - x / 2, by omega⟩
    have h2 := ih (x / 2) t'
    rw [ht']
    omega

/-- Adding the top coin raises the greedy digit sum by exactly `1`. -/
lemma gmin_add_pow : ∀ w X, gmin w (X + 2 ^ w) = gmin w X + 1 := by
  intro w
  induction w with
  | zero => intro X; simp [gmin]
  | succ w ih =>
    intro X
    have h2 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    simp only [gmin]
    have e1 : (X + 2 ^ (w + 1)) % 2 = X % 2 := by omega
    have e2 : (X + 2 ^ (w + 1)) / 2 = X / 2 + 2 ^ w := by omega
    rw [e1, e2, ih (X / 2)]
    omega

/-- Greedy digit sum of the all-ones target: `gmin w (2^{w+1} − 1) = w + 1`. -/
lemma gmin_ones : ∀ w, gmin w (2 ^ (w + 1) - 1) = w + 1 := by
  intro w
  induction w with
  | zero => norm_num [gmin]
  | succ w ih =>
    have h2 : 2 ^ (w + 1 + 1) = 2 * 2 ^ (w + 1) := by rw [pow_succ]; ring
    have h1 : 1 ≤ 2 ^ (w + 1) := Nat.one_le_pow _ _ (by norm_num)
    simp only [gmin]
    have e1 : (2 ^ (w + 1 + 1) - 1) % 2 = 1 := by omega
    have e2 : (2 ^ (w + 1 + 1) - 1) / 2 = 2 ^ (w + 1) - 1 := by omega
    rw [e1, e2, ih]
    omega

/-- **Step lemma** (paper §5, Lemma 4): adding `2^{w+1} − 2^t` (`t ≤ w`;
subtraction encoded as `M' + 2^t = M + 2^{w+1}`) raises the greedy digit sum
by at least `1`.  Induction on `w`, peeling one bit: for `t ≥ 1` both sides
keep their parity and the shifted instance is `(w−1, t−1)`; for `t = 0` the
parity flips, and the odd-`M` branch pays two top coins via `gmin_add_pow`. -/
lemma gmin_step : ∀ w t M M', t ≤ w → M' + 2 ^ t = M + 2 ^ (w + 1) →
    gmin w M + 1 ≤ gmin w M' := by
  intro w
  induction w with
  | zero =>
    intro t M M' ht hM
    have ht0 : t = 0 := by omega
    subst ht0
    norm_num at hM
    simp only [gmin]
    omega
  | succ w ih =>
    intro t M M' ht hM
    have h2 : 2 ^ (w + 1 + 1) = 2 * 2 ^ (w + 1) := by rw [pow_succ]; ring
    have h1 : 1 ≤ 2 ^ (w + 1) := Nat.one_le_pow _ _ (by norm_num)
    simp only [gmin]
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · -- gap `2^{w+2} − 1`: the parity flips
      simp only [pow_zero] at hM
      rcases Nat.mod_two_eq_zero_or_one M with hp | hp
      · -- `M` even, `M'` odd: recurse on the `(w, 0)` instance
        have hstep := ih 0 (M / 2) (M' / 2) (Nat.zero_le w)
          (by simp only [pow_zero]; omega)
        omega
      · -- `M` odd, `M'` even: `M'/2 = M/2 + 2·2^w`, two top coins
        have ha1 := gmin_add_pow w (M / 2)
        have ha2 := gmin_add_pow w (M / 2 + 2 ^ w)
        have h2w : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
        have e2 : M' / 2 = M / 2 + 2 ^ w + 2 ^ w := by omega
        rw [e2, ha2, ha1]
        omega
    · -- gap `2^{w+2} − 2^t` with `t ≥ 1`: parities agree, recurse on `(w, t−1)`
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      have hps : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
      have hstep := ih s (M / 2) (M' / 2) (by omega) (by omega)
      omega

/-- **Slack bound** (paper §5): by induction on `j` from the step lemma, the
positive-multiple target `2^{w+1} − 1 + j·N` at a power-of-two gap
(`N + 2^t = 2^{w+1}`, `t ≤ w`) has greedy digit sum at least `w + 1 + j` —
the paper's `s_min(M_j) ≥ n + j`, for **every** `j`. -/
lemma slack {w t N : ℕ} (ht : t ≤ w) (hN : N + 2 ^ t = 2 ^ (w + 1)) :
    ∀ j, w + 1 + j ≤ gmin w (2 ^ (w + 1) - 1 + j * N) := by
  intro j
  induction j with
  | zero =>
    have h := gmin_ones w
    simp only [Nat.zero_mul, Nat.add_zero]
    omega
  | succ j ih =>
    have hmul : (j + 1) * N = j * N + N := by ring
    have h1 : 1 ≤ 2 ^ (w + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hstep := gmin_step w t (2 ^ (w + 1) - 1 + j * N)
      (2 ^ (w + 1) - 1 + (j + 1) * N) ht (by omega)
    omega

/-- Peel index 0 off a value (inverse of `shift_val`). -/
lemma unshift_val (w : ℕ) (k : ℕ → ℕ) :
    val (w + 1) k = k 0 + 2 * val w (fun i => k (i + 1)) := by
  have h := shift_val w (k 0) (fun i => k (i + 1))
  have hk : val (w + 1) (shift (k 0) (fun i => k (i + 1))) = val (w + 1) k := by
    unfold val
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [shift]
    · have hne : i ≠ 0 := by omega
      have hi1 : i - 1 + 1 = i := by omega
      simp only [shift, ite_eq_right hne, hi1]
  rw [hk] at h
  omega

/-- Peel index 0 off a digit sum (inverse of `shift_dsum`). -/
lemma unshift_dsum (w : ℕ) (k : ℕ → ℕ) :
    dsum (w + 1) k = k 0 + dsum w (fun i => k (i + 1)) := by
  have h := shift_dsum w (k 0) (fun i => k (i + 1))
  have hk : dsum (w + 1) (shift (k 0) (fun i => k (i + 1))) = dsum (w + 1) k := by
    unfold dsum
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [shift]
    · have hne : i ≠ 0 := by omega
      have hi1 : i - 1 + 1 = i := by omega
      simp only [shift, ite_eq_right hne, hi1]
  rw [hk] at h
  omega

/-- Each unit of digit sum contributes a coin worth at least `1`. -/
lemma dsum_le_val (n : ℕ) (k : ℕ → ℕ) : dsum n k ≤ val n k :=
  Finset.sum_le_sum fun i _ =>
    Nat.le_mul_of_pos_right (k i) (pow_pos (by norm_num) i)

/-- Each unit of digit sum contributes a coin worth at most `2^{n-1}`. -/
lemma val_le_dsum_mul (n : ℕ) (k : ℕ → ℕ) :
    val n k ≤ dsum n k * 2 ^ (n - 1) := by
  unfold val dsum
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hin : i ≤ n - 1 := by have := Finset.mem_range.mp hi; omega
  exact Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right (by norm_num) hin)

/-- **Greedy minimality** (paper Lemma 3, downward half): the digit sum of any
representation is at least the greedy digit sum of its value.  Induction on
the width: split the bottom coin `k 0 = M % 2 + 2t`; the `2t` surplus carries
up into the shifted representation, and `gmin_add_le` absorbs it. -/
lemma gmin_le_dsum : ∀ w (k : ℕ → ℕ), gmin w (val (w + 1) k) ≤ dsum (w + 1) k := by
  intro w
  induction w with
  | zero =>
    intro k
    simp [gmin, val, dsum]
  | succ w ih =>
    intro k
    have hv := unshift_val (w + 1) k
    have hd := unshift_dsum (w + 1) k
    have hih := ih (fun i => k (i + 1))
    obtain ⟨t, ht⟩ : ∃ t, k 0 = (val (w + 1 + 1) k) % 2 + 2 * t :=
      ⟨k 0 / 2, by omega⟩
    have hsplit : val (w + 1) (fun i => k (i + 1)) + t = (val (w + 1 + 1) k) / 2 := by
      omega
    have hadd := gmin_add_le w (val (w + 1) (fun i => k (i + 1))) t
    rw [hsplit] at hadd
    simp only [gmin]
    omega

/-- **Lemma 2** (paper §3): the all-ones vector is the *only* representation of
`2^n − 1` with digit sum `n`.  Descent on the bottom coin: parity forces
`k 0 = 1 + 2t`, and the greedy bound on the shifted representation forces
`t = 0`; recurse. -/
lemma ones_unique : ∀ n (k : ℕ → ℕ), val n k = 2 ^ n - 1 → dsum n k = n →
    ∀ i < n, k i = 1 := by
  intro n
  induction n with
  | zero => intro k _ _ i hi; omega
  | succ n ih =>
    intro k hv hd
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · intro i hi
      have h0 : i = 0 := by omega
      subst h0
      simp [val] at hv
      omega
    · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
      have hv' := unshift_val (p + 1) k
      have hd' := unshift_dsum (p + 1) k
      have h2 : 2 ^ (p + 1 + 1) = 2 * 2 ^ (p + 1) := by rw [pow_succ]; ring
      have h1 : 1 ≤ 2 ^ (p + 1) := Nat.one_le_pow _ _ (by norm_num)
      obtain ⟨t, ht⟩ : ∃ t, k 0 = 1 + 2 * t := ⟨k 0 / 2, by omega⟩
      have hveq : val (p + 1) (fun i => k (i + 1)) + t = 2 ^ (p + 1) - 1 := by
        omega
      have hlb := gmin_le_dsum p (fun i => k (i + 1))
      have hg := gmin_ones p
      have hadd := gmin_add_le p (val (p + 1) (fun i => k (i + 1))) t
      rw [hveq, hg] at hadd
      have ht0 : t = 0 := by omega
      have hk0 : k 0 = 1 := by omega
      have hval1 : val (p + 1) (fun i => k (i + 1)) = 2 ^ (p + 1) - 1 := by omega
      have hds1 : dsum (p + 1) (fun i => k (i + 1)) = p + 1 := by omega
      have hres := ih (fun i => k (i + 1)) hval1 hds1
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · exact hk0
      · have hi1 : i - 1 + 1 = i := by omega
        have h := hres (i - 1) (by omega)
        simpa [hi1] using h

/-! ### Theorem A and the main theorem -/

/-- **Theorem A** (upper bound, paper §5): the super-increasing set is valid at
`N = 2^n − 2^⌊log₂ n⌋`.  Pass to `M = val n k ≡ 2^n − 1 [MOD N]` and split:
`M < 2^n − 1` falls below the floor (`2^m ≤ n` — the only place `⌊log₂⌋`
enters); `M = 2^n − 1` is `ones_unique`; and `M = 2^n − 1 + jN` has greedy
digit sum at least `n + j > n` by `slack` — uniformly in `j ≥ 1` and `n ≥ 2`,
with no range restriction and no small-`n` cases. -/
theorem theoremA {n : ℕ} (hn : 2 ≤ n) :
    Valid n (2 ^ n - 2 ^ Nat.log 2 n) := by
  have hmn : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hnm : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  set m := Nat.log 2 n with hm
  set N := 2 ^ n - 2 ^ m with hN
  have h1m : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have hnlt : n < 2 ^ n := Nat.lt_two_pow_self
  have hmltn : m < n := by
    have h : m < 2 ^ m := Nat.lt_two_pow_self
    omega
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hmle : 2 ^ m ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2p : 2 ≤ 2 ^ (n - 1) := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 1 ≤ n - 1)
    simpa using h
  intro k hd hcong
  -- pass from the `a`-congruence to `M = val n k ≡ 2^n − 1 [MOD N]`
  have e1 : (∑ i ∈ range n, k i * a i) + n = val n k := by
    have h0 := sum_a_add_dsum n k
    rw [hd] at h0
    exact h0
  have hd1 : dsum n (fun _ => 1) = n := by
    unfold dsum
    rw [Finset.sum_const, smul_eq_mul, mul_one, card_range]
  have hv1 : val n (fun _ => 1) = 2 ^ n - 1 := by
    unfold val
    calc (∑ i ∈ range n, 1 * 2 ^ i) = ∑ i ∈ range n, 2 ^ i :=
          Finset.sum_congr rfl fun i _ => one_mul _
      _ = 2 ^ n - 1 := sum_two_pow n
  have e2 : (∑ i ∈ range n, a i) + n = 2 ^ n - 1 := by
    have h0 := sum_a_add_dsum n (fun _ => 1)
    simp only [one_mul] at h0
    rw [hd1, hv1] at h0
    exact h0
  have hMcong : val n k ≡ 2 ^ n - 1 [MOD N] := by
    have h := Nat.ModEq.add_right n hcong
    rwa [e1, e2] at h
  have hlow : n ≤ val n k := by
    have h := dsum_le_val n k
    omega
  rcases lt_trichotomy (val n k) (2 ^ n - 1) with hlt | heq | hgt
  · -- M < 2^n − 1: a positive multiple downward lands below 2^m ≤ n ≤ M
    exfalso
    have hdvd : N ∣ 2 ^ n - 1 - val n k :=
      (Nat.modEq_iff_dvd' (by omega)).mp hMcong
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  · exact ones_unique n k heq hd
  · -- M = 2^n − 1 + jN with 1 ≤ j ≤ n − 2: greedy digit sum exceeds n
    exfalso
    have hdvd : N ∣ val n k - (2 ^ n - 1) :=
      (Nat.modEq_iff_dvd' (by omega)).mp hMcong.symm
    obtain ⟨j, hj⟩ := hdvd
    have hcomm : N * j = j * N := Nat.mul_comm N j
    have hjeq : val n k = 2 ^ n - 1 + j * N := by omega
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · rw [Nat.zero_mul] at hjeq
        omega
      · exact h
    have hgd : gmin (n - 1) (val n k) ≤ n := by
      have h := gmin_le_dsum (n - 1) k
      have h' : n - 1 + 1 = n := by omega
      rw [h'] at h
      omega
    -- `slack` at gap `2^m`: `gmin (n−1) M_j ≥ n + j > n`, contradiction
    have hw : n - 1 + 1 = n := by omega
    have hNt : N + 2 ^ m = 2 ^ (n - 1 + 1) := by rw [hw]; omega
    have hs := slack (by omega : m ≤ n - 1) hNt j
    have harg : 2 ^ (n - 1 + 1) - 1 + j * N = val n k := by
      rw [hw]
      omega
    rw [harg, hw] at hs
    omega

/-- **Main theorem**: `Nmin(n) = 2^n − 2^⌊log₂ n⌋` — it is valid there, and
every smaller modulus (≥ 2) is invalid.  (Modulo `theoremA`.) -/
theorem nmin_eq {n : ℕ} (hn : 2 ≤ n) :
    IsLeast {N | 2 ≤ N ∧ Valid n N} (2 ^ n - 2 ^ Nat.log 2 n) := by
  have hmn : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hnlt : n < 2 ^ n := Nat.lt_two_pow_self
  have hmlt : Nat.log 2 n < n := by
    by_contra hc
    push Not at hc
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hc
    omega
  have hple : 2 ^ Nat.log 2 n ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2p : 2 ≤ 2 ^ (n - 1) := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 1 ≤ n - 1)
    simpa using h
  constructor
  · exact ⟨by omega, theoremA hn⟩
  · rintro N ⟨hN2, hNv⟩
    by_contra hc
    push Not at hc
    exact theoremB hn hN2 hc hNv

end MinModulus
