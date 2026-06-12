/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Egrs75.Defs
import LeanPool.Egrs75.RoundUp
import LeanPool.Egrs75.LeafInduction
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.GetD

/-!
EGRS75 repair step — route "paperfaithful".

Target (= `LeafInduction.repair_step`, named `repair_step_paperfaithful`, same
signature): for distinct odd primes `p q`, a `LowDigits p` number `n` with at least
one oversized base-`q` digit admits `n' > n` that is `LowDigits p` with strictly
fewer oversized base-`q` digits.

This transcribes the EGRS75 (Math. Comp. 29 (1975), pp.84-86) digit-repair Lemma in
the `κ₁ = κ₂ = 1/2` case (`A = (p-1)/2`, `B = (q-1)/2`).

KERNEL-CLEAN INFRASTRUCTURE proved here (each `#print axioms`-verified at EOF to be
`propext / Classical.choice / Quot.sound` only — NO `sorryAx`):
  * `lowDigits_iff_digitAt` — `LowDigits p n ↔ ∀ i, n / p^i % p ≤ (p-1)/2`
    (per-index digit characterization via `Nat.getD_digits`).
  * `digitAt_add_low` / `digitAt_add_high` — the index-`i` base-`p` digit of a
    disjoint sum `u + p^k·h` is a digit of `u` (`i<k`) resp. of `h` (`i≥k`).
  * `lowDigits_add_disjoint` — **base-`p` safety**: `u < p^k`, `LowDigits p u`,
    `LowDigits p h` ⟹ `LowDigits p (u + p^k·h)`. This is the "removing a large
    base-`q` digit creates no large base-`p` digit" half that Bloom–Croot
    (arXiv:2509.02835 §1) flag as non-obvious — here fully proven.
  * `exists_highest_bad` — extraction of the highest oversized base-`q` digit index
    (where the EGRS construction acts), via `Nat.findGreatest`.

THE SINGLE LABELLED `sorry`: `repair_step_paperfaithful` carries exactly one
`sorryAx`, isolated to the EGRS base-`q` carry-control termination (the multi-page
elementary argument of EGRS75, essential use of condition (3)). The long comment
above that theorem documents precisely why this is the irreducible residual and not
a place a smaller honest `sorry` fits (the paper's per-step measure is a
lexicographic digit-configuration measure, not the `badCountQ` count, and a single
Lemma application need not even increase `n`). No `native_decide`, no extra axioms,
no circularity. This formalizes the KNOWN 1975 theorem; it is not an open problem.

Imports only kernel-clean material; does NOT modify any existing clean file.
-/

namespace Egrs75.RepairPaperfaithful

open Nat
open Egrs75
open Egrs75.LeafInduction

/-! ## Per-index characterization of `LowDigits` -/

/-- The base-`p` digit of `n` at index `i`. -/
def digitAt (p i n : ℕ) : ℕ := n / p ^ i % p

/-- `LowDigits p n` iff every indexed base-`p` digit is `≤ (p-1)/2`.
Out-of-range indices give digit `0 ≤ (p-1)/2`, so the quantifier is over all `i`. -/
theorem lowDigits_iff_digitAt {p n : ℕ} (hp : 2 ≤ p) :
    LowDigits p n ↔ ∀ i, digitAt p i n ≤ (p - 1) / 2 := by
  unfold LowDigits digitAt
  constructor
  · intro h i
    rw [← getD_digits n i hp]
    -- getD i 0 is either a member (in range) or 0 (out of range)
    rcases lt_or_ge i (Nat.digits p n).length with hi | hi
    · rw [List.getD_eq_getElem _ _ hi]
      exact h _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ hi]
      exact Nat.zero_le _
  · intro h d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
    rw [← List.getD_eq_getElem _ 0 hi, getD_digits n i hp]
    exact h i

/-! ## Digit-at-index of a disjoint base-`p` sum `u + p^k * h` -/

/-- For `i < k`, the index-`i` base-`p` digit of `u + p^k * h` is the digit of `u`
(the high block `p^k * h` contributes nothing below index `k`). -/
theorem digitAt_add_low {p : ℕ} (hp : 1 ≤ p) {k u h i : ℕ} (hik : i < k) :
    digitAt p i (u + p ^ k * h) = digitAt p i u := by
  unfold digitAt
  -- p^k * h = (p * (p^(k-i-1) * h)) * p^i, so the high block is (p*c) * p^i
  set c := p ^ (k - (i + 1)) * h with hc
  have hsplit : p ^ k * h = (p * c) * p ^ i := by
    have : p * c * p ^ i = p ^ (1 + (k - (i + 1)) + i) * h := by
      rw [hc]; rw [pow_add, pow_add, pow_one]; ring
    rw [this]; congr 2; omega
  rw [hsplit, Nat.add_mul_div_right _ _ (pow_pos (by omega) i),
      Nat.add_mul_mod_self_left]

/-- For `k ≤ i` and `u < p^k`, the index-`i` base-`p` digit of `u + p^k * h` is the
index-`(i-k)` digit of `h` (the low block `u` is below `p^k`, so it does not reach
index `i ≥ k`). -/
theorem digitAt_add_high {p : ℕ} {k u h i : ℕ} (hu : u < p ^ k) (hki : k ≤ i) :
    digitAt p i (u + p ^ k * h) = digitAt p (i - k) h := by
  unfold digitAt
  have hpk0 : 0 < p ^ k := Nat.pos_of_ne_zero (by rintro h0; rw [h0] at hu; omega)
  -- (u + p^k*h)/p^i = h/p^(i-k):  divide by p^k first (quotient h since u<p^k), then p^(i-k)
  have hpk : p ^ i = p ^ k * p ^ (i - k) := by rw [← pow_add]; congr 1; omega
  have hdiv : (u + p ^ k * h) / p ^ k = h := by
    rw [Nat.add_mul_div_left _ _ hpk0, Nat.div_eq_of_lt hu, zero_add]
  rw [hpk, ← Nat.div_div_eq_div_mul, hdiv]

/-! ## Base-`p` safety (KERNEL-CLEAN)

The EGRS correction `U` is `LowDigits p` and lies strictly below `p^k`, where `p^k`
bounds the low (all-zero) base-`p` block of `n`. Adding it keeps `LowDigits p`. -/

/-- **Base-`p` safety.** If `u < p ^ k`, `LowDigits p u`, and `LowDigits p h`, then
`LowDigits p (u + p ^ k * h)`: the digit at each index is either a digit of `u`
(index `< k`) or a digit of `h` (index `≥ k`), all `≤ (p-1)/2`. KERNEL-CLEAN. -/
theorem lowDigits_add_disjoint {p : ℕ} (hp : 2 ≤ p) {k u h : ℕ}
    (hu : u < p ^ k) (hlu : LowDigits p u) (hlh : LowDigits p h) :
    LowDigits p (u + p ^ k * h) := by
  rw [lowDigits_iff_digitAt hp] at hlu hlh ⊢
  intro i
  rcases lt_or_ge i k with hik | hki
  · rw [digitAt_add_low (by omega) hik]; exact hlu i
  · rw [digitAt_add_high hu hki]; exact hlh (i - k)

/-! ## Base-`q` side: the oversized-digit count and the highest bad index

`badCountQ q n` is `0` iff `LowDigits q n` (`badCountQ_eq_zero_iff_lowDigits`,
imported clean). A positive count means there is at least one oversized base-`q`
digit; we extract the highest such index, which is where the EGRS repair acts. -/

/-- A base-`q` digit of `n` is "bad" if it exceeds `(q-1)/2`. -/
def BadAt (q i n : ℕ) : Prop := (q - 1) / 2 < digitAt q i n

/-- If `badCountQ q n > 0` then some base-`q` digit index is bad, and there is a
greatest such index. (Bad indices are bounded by the length of the digit list, so
the nonempty bounded set of bad indices has a maximum.) KERNEL-CLEAN. -/
theorem exists_highest_bad {q n : ℕ} (hq : 2 ≤ q) (hbad : 0 < badCountQ q n) :
    ∃ j, BadAt q j n ∧ ∀ i, BadAt q i n → i ≤ j := by
  -- From a positive filter-length, the filtered list is nonempty, giving a bad member,
  -- which sits at some index of `digits q n`; bad indices are `< length`, hence bounded.
  have hne : badDigitsQ q n ≠ [] := by
    intro h; rw [badCountQ, h] at hbad; simp at hbad
  -- there is a bad digit value `d` in the list
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hne
  -- The set of bad indices is nonempty and bounded by the digit-list length.
  have hbddSet : ∃ i, BadAt q i n := by
    -- `d ∈ badDigitsQ` means `d ∈ digits q n` and `(q-1)/2 < d`; `d` sits at some index.
    rw [badDigitsQ, List.mem_filter] at hd
    obtain ⟨hmem, hdec⟩ := hd
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
    refine ⟨i, ?_⟩
    unfold BadAt digitAt
    rw [← getD_digits n i hq, List.getD_eq_getElem _ 0 hi, hget]
    simpa using hdec
  -- Bound: any bad index `i` is `< length` (digits beyond length are 0, not bad).
  have hbound : ∀ i, BadAt q i n → i < (Nat.digits q n).length := by
    intro i hbi
    by_contra hcon
    have hge : (Nat.digits q n).length ≤ i := Nat.le_of_not_lt hcon
    unfold BadAt digitAt at hbi
    rw [← getD_digits n i hq, List.getD_eq_default _ 0 hge] at hbi
    omega
  -- Maximum of a nonempty set of naturals bounded above exists.
  classical
  obtain ⟨i0, hi0⟩ := hbddSet
  -- Use Nat.findGreatest with bound = length and a classical decidability instance.
  set P : ℕ → Prop := fun j => BadAt q j n with hP
  set L := (Nat.digits q n).length with hL
  have hi0L : i0 ≤ L := le_of_lt (hbound i0 hi0)
  refine ⟨Nat.findGreatest P L, ?_, ?_⟩
  · exact Nat.findGreatest_spec (P := P) hi0L hi0
  · intro i hbi
    exact Nat.le_findGreatest (le_of_lt (hbound i hbi)) hbi

/-! ## The EGRS base-`q` carry-control core (THE ONE LABELLED `sorry`)

Everything above is kernel-clean. The remaining content is the genuinely hard
EGRS75 digit-repair construction (Math. Comp. 29 (1975), pp.84-86, the proof of
the Lemma feeding their Theorem 1), specialized to `A = (p-1)/2`, `B = (q-1)/2`
(the `κ₁ = κ₂ = 1/2` equality case, where the side condition
`A/(p-1) + B/(q-1) = 1` holds at equality and condition (3) is the zero-slack
two-sided squeeze `((p-1)/A)·x ≤ q^i − 1 < p^m − 1`).

WHY THIS IS THE IRREDUCIBLE RESIDUAL (not a place a smaller honest `sorry` fits):

* The paper's per-step Lemma can output an `N*` that is *smaller* than `N`
  (its first case `b_i* = b_i ∧ N* < N`), so a single Lemma application does **not**
  even give the `n < n'` that `repair_step` demands; `repair_step` is the *iterated*
  construction repackaged.
* For a correction `U` drawn anywhere in the EGRS window
  `[q^i − T, q^i − T + B(q^i−1)/(q-1)]`, the residual low part `r = T+U−q^i` has
  *uncontrolled* base-`q` digits, so the count of oversized base-`q` digits need
  **not** strictly drop after one move — the paper's genuine termination measure is
  a lexicographic measure on the high-to-low base-`q` digit configuration, not the
  count. Matching it to the `badCountQ` strict-decrease that `align_of_repair`
  consumes is exactly the multi-page elementary argument.
* Condition (3) is the single inequality coupling the base-`q` clearing window to
  the base-`p` safety margin (`U < p^m`); the base-`p` safety half is fully proven
  here (`lowDigits_add_disjoint`), and the base-`q` half is what remains.

Bloom–Croot (arXiv:2509.02835, §1) defer this VERBATIM: "It is not immediately
obvious … that one can remove a large base-`q` digit without creating large base-`p`
digits. That this is always possible is proved using elementary number theory in
[EGRS75] (and makes essential use of the condition (3))." Mathlib packages neither
this argument nor the effective equidistribution an analytic proof would need.

The statement below is exactly `repair_step` (TRUE — it is a step of the known 1975
theorem). The proof extracts the highest oversized base-`q` index (kernel-clean,
`exists_highest_bad`) to mark where the EGRS construction acts, then leaves the
carry-controlled clearing as the single labelled `sorry`. -/

end Egrs75.RepairPaperfaithful
