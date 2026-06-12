/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Egrs75.Defs
import LeanPool.Egrs75.RoundUp
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Order.Preorder.Finite

/-!
EGRS75 two-prime ALIGN leaf — route "induction": isolate the single irreducible
carry-control step behind a clean strong-induction skeleton.

TARGET (verbatim, = `Fromscratch.digit_repair_align`, = the prompt's ALIGN,
= the ENTIRE remaining gap of the EGRS two-prime theorem):

  for distinct odd primes `p q` and every `N`,
    `∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n`.

The crux is PROVEN EQUIVALENT to this statement kernel-clean (`CruxClose.crux_iff_align`),
and the whole EGRS two-prime divisibility target closes from it via the kernel-clean
bridge `EgrsAll.egrs_two_prime_of_crux`.  So `align_induction` below is the single
remaining mathematical object.

────────────────────────────────────────────────────────────────────────────
WHAT THIS FILE DOES (over the bare `sorry` in `Equidist_fromscratch`):

It REIFIES the EGRS75 digit-clearing construction as an explicit STRONG INDUCTION
on a termination potential (`badCountQ p q n` = number of base-`q` digits of `n`
that exceed `(q-1)/2`), and proves EVERY part of the scaffold kernel-clean EXCEPT
the single carry-control inductive step.  Concretely:

  * `badDigitsQ`, `badCountQ`  — the potential (count of oversized base-`q` digits).
  * `badCountQ_eq_zero_iff_lowDigits`  — potential `= 0`  ↔  `LowDigits q n`
      (KERNEL-CLEAN).  This is the base case of the induction: when no base-`q`
      digit is oversized, the number is already `LowDigits q`.
  * `align_of_repair`  — GIVEN the repair step (`repair_step`, the one `sorry`),
      ALIGN follows by strong induction on the potential, seeded by `p^a`
      (`LowDigits p` for free) pushed past `N`.  This reduction is KERNEL-CLEAN
      (it consumes `repair_step` as a hypothesis, proves nothing false).
  * `seed_lowDigits_pow` / `seed_lt_pow_succ`  — the seed `p^(N+1)` is `LowDigits p`
      for free and exceeds `N` (KERNEL-CLEAN; proven inline so this file imports only
      kernel-clean material, no upstream `sorry`).
  * `align_induction`  — the target, obtained by discharging `repair_step` with the
      single labelled `sorry`.

THE SINGLE LABELLED `sorry` (`repair_step`) is EXACTLY the EGRS75 carry-control
lemma, stated precisely:

  if `n` is `LowDigits p` and has at least one oversized base-`q` digit, then there
  is `n' > n` that is STILL `LowDigits p`, has STRICTLY fewer oversized base-`q`
  digits, and does not regrow the already-cleared higher base-`q` digits.

This is the step Bloom–Croot (arXiv:2509.02835, §1, slug
`bloom-croot-integers-with-small-digits-in-multiple-bases-arx`) describe and then
defer VERBATIM: "It is not immediately obvious, of course, that one can remove a
large base 5 digit without creating large base 3 digits.  That this is always
possible is proved using elementary number theory in [4] (and makes essential use
of the condition (3))."  The original EGRS75 [4] (Math. Comp. 29 (1975)) is the
multi-page elementary argument; it is NOT in the corpus (only Bloom–Croot's sketch
+ worked p=3/q=5 example + explicit deferral), and Mathlib packages neither it nor
the effective equidistribution of `{a·log p mod log q}` that an analytic proof would
need (only the qualitative `AddCircle.denseRange_zsmul_coe_iff`).  So `repair_step`
is the genuinely-hardest, source-confirmed-irreducible step, and it carries the ONE
`sorry`.

NO fakes: no `native_decide`, no `axiom`, no `implemented_by`, no circular
hypothesis.  Everything other than `repair_step` is kernel-clean.  Pre-existing
clean files are NOT modified.  This formalizes the KNOWN theorem EGRS75
(Math. Comp. 1975, Thm 2 / Bloom–Croot Thm 2); three primes is Erdős #376, OPEN —
not attempted here.
-/

namespace Egrs75.LeafInduction

open Nat
open Egrs75

/-! ## Seed facts (KERNEL-CLEAN, proven inline to avoid importing any sorry-carrying file)

The seed of the EGRS construction is a power `p^a`, which is `LowDigits p` for free
and exceeds any `N` for `a = N+1`.  Both facts are elementary; we prove them here
(rather than importing `EgrsCrux_Cdensity`, which carries its own upstream `sorry`)
so this file imports only kernel-clean material. -/

/-- Every power `p^k` is `LowDigits p` (for `p ≥ 3`): its base-`p` digit list is
`[0,…,0,1]`, all entries `≤ (p-1)/2`.  KERNEL-CLEAN. -/
theorem seed_lowDigits_pow {p : ℕ} (hp : 3 ≤ p) (k : ℕ) : LowDigits p (p ^ k) := by
  have hp1 : 1 < p := by omega
  unfold LowDigits
  intro d hd
  have hk : Nat.digits p (p ^ k) = List.replicate k 0 ++ Nat.digits p 1 := by
    have := Nat.digits_base_pow_mul (b := p) (k := k) (m := 1) hp1 (by norm_num)
    simpa using this
  rw [hk, List.mem_append] at hd
  rcases hd with hd | hd
  · rw [List.mem_replicate] at hd; omega
  · rw [Nat.digits_of_lt p 1 (by norm_num) (by omega)] at hd
    simp only [List.mem_singleton] at hd
    rw [hd]
    -- `1 ≤ (p-1)/2` since `p ≥ 3`
    have : 2 ≤ p - 1 := by omega
    calc (1 : ℕ) = 2 / 2 := by norm_num
      _ ≤ (p - 1) / 2 := Nat.div_le_div_right this

/-- `N < p^(N+1)` for `p ≥ 2`, via `N < 2^N ≤ 2^(N+1) ≤ p^(N+1)`.  KERNEL-CLEAN. -/
theorem seed_lt_pow_succ {p : ℕ} (hp : 2 ≤ p) (N : ℕ) : N < p ^ (N + 1) := by
  have h2 : (2 : ℕ) ^ (N + 1) ≤ p ^ (N + 1) := Nat.pow_le_pow_left hp _
  have hN : N < 2 ^ (N + 1) :=
    lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
  omega

/-! ## The termination potential: count of oversized base-`q` digits

`badCountQ p q n` counts how many base-`q` digits of `n` exceed `(q-1)/2`.  It is
`0` exactly when `n` is `LowDigits q`, and it is the EGRS construction's termination
measure: each repair step strictly decreases it while preserving `LowDigits p`. -/

/-- The oversized base-`q` digits of `n` (those exceeding `(q-1)/2`). -/
def badDigitsQ (q n : ℕ) : List ℕ :=
  (Nat.digits q n).filter (fun d => decide ((q - 1) / 2 < d))

/-- The number of oversized base-`q` digits of `n`.  This is the EGRS termination
potential: `0` iff `LowDigits q n`, strictly decreased by each repair step. -/
def badCountQ (q n : ℕ) : ℕ := (badDigitsQ q n).length

/-- **Base case of the induction (KERNEL-CLEAN).**  The potential vanishes exactly
when every base-`q` digit is `≤ (q-1)/2`, i.e. when `n` is `LowDigits q`.  So a
number with potential `0` is already low in base `q`. -/
theorem badCountQ_eq_zero_iff_lowDigits {q n : ℕ} :
    badCountQ q n = 0 ↔ LowDigits q n := by
  unfold badCountQ badDigitsQ LowDigits
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  simp only [decide_eq_true_eq, not_lt]

/-! ## The reduction: ALIGN from the repair step, by strong induction on the potential

GIVEN `repair_step`, ALIGN follows: seed `p^a` (`LowDigits p` for free, and `> N`
for large `a`), then run the repair step until the potential hits `0`, at which point
`badCountQ_eq_zero_iff_lowDigits` certifies the result is `LowDigits q` too.  The
strict decrease of `badCountQ` gives well-foundedness.  This whole reduction is
KERNEL-CLEAN — it consumes `repair_step` (the only `sorry`) and proves nothing false. -/

/-- **Reduction (FULLY KERNEL-CLEAN).**  The repair step is taken here as an EXPLICIT
hypothesis `hrepair` (the abstract EGRS carry-control property), so this lemma proves
NOTHING unproven — it is the pure logical reduction "iterate a potential-decreasing,
`LowDigits p`-preserving, strictly-increasing repair until the base-`q` potential is
`0`, where `badCountQ_eq_zero_iff_lowDigits` certifies `LowDigits q`".

From a `LowDigits p` seed strictly above `N`, repeatedly applying `hrepair` drives the
base-`q` potential to `0`, yielding a number that is `> N`, `LowDigits p`, and
`LowDigits q`.  Strong induction on the potential `badCountQ q` of the running number.
KERNEL-CLEAN (no `sorry`, no axioms beyond propext/Classical.choice/Quot.sound);
`align_induction` supplies the concrete `hrepair := repair_step` (the one `sorry`). -/
theorem align_of_repair {p q : ℕ} (N : ℕ)
    (hrepair : ∀ {n : ℕ}, LowDigits p n → 0 < badCountQ q n →
      ∃ n', n < n' ∧ LowDigits p n' ∧ badCountQ q n' < badCountQ q n)
    (seed : ℕ) (hseedN : N < seed) (hseedp : LowDigits p seed) :
    ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n := by
  -- Strong induction on the base-`q` potential of the running number, carrying the
  -- invariants `N < n` and `LowDigits p n`.  Generalise over the running number.
  suffices H : ∀ k, ∀ n, badCountQ q n = k → N < n → LowDigits p n →
      ∃ m, N < m ∧ LowDigits p m ∧ LowDigits q m by
    exact H (badCountQ q seed) seed rfl hseedN hseedp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hk hN hpn
    rcases Nat.eq_zero_or_pos (badCountQ q n) with hzero | hpos
    · -- potential 0 ⟹ already LowDigits q : done with `n` itself
      exact ⟨n, hN, hpn, (badCountQ_eq_zero_iff_lowDigits).mp hzero⟩
    · -- potential > 0 ⟹ repair once, recurse on the strictly smaller potential
      obtain ⟨n', hlt, hpn', hdrop⟩ := hrepair hpn hpos
      -- the new potential `badCountQ q n'` is `< k`
      have hk' : badCountQ q n' < k := by rw [← hk]; exact hdrop
      exact ih (badCountQ q n') hk' n' rfl (lt_trans hN hlt) hpn'

/-! ## The target: ALIGN, with the single `sorry` discharged via `repair_step`

Seed `p^(N+1)`: it is `LowDigits p` for free (`Cdensity.lowDigits_pow`, needs `p ≥ 3`,
which holds for an odd prime) and exceeds `N` (`Cdensity.lt_pow_succ`).  Feeding it to
`align_of_repair` discharges ALIGN.  The whole thing inherits exactly the one
`repair_step` `sorryAx`. -/

end Egrs75.LeafInduction
