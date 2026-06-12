/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Egrs75.Defs
import LeanPool.Egrs75.RoundUp
import LeanPool.Egrs75.LeafInduction
import LeanPool.Egrs75.DigitVector
import LeanPool.Egrs75.DigitAtToolkit
import Mathlib.Data.Nat.Digits.Lemmas

/-!
EGRS75 two-prime clearing — PRIMITIVE P2: the ADD branch (`add_clears`).

This file builds the ADD branch of the EGRS75 repair Lemma (Math. Comp. 29 (1975),
pp.84-85, equality case `A = B = (p-1)/2 = (q-1)/2`), the half of the low-case
`egrs_clearing_low` residual that ADDS a controlled `LowDigits p` correction `U` to
clear the top oversized base-`q` digit.

ROLE in the LOW-case proof.  When the base-`q` tail `T = n % q^j` (`j = topBadIndex q n`)
is small (`T < S`, available only when the lowest nonzero base-`p` digit index `m > 0`),
the paper adds `U` with `q^i - T ≤ U ≤ q^i - T + B(q^j-1)/(q-1)` and `U < p^m`, where
`i` is the least good base-`q` index `> j`.  Condition (3),
`q^i - 1 < ((q-1)/B)((p-A-1)/(p-1))(p^m - 1)`, reduces in the equality case to
`2*(q^i - T) ≤ p^m` (so that the density Fact's `[x,2x)` window lands inside `[x, p^m)`):
the single place the two bases interact.

WHAT IS KERNEL-CLEAN HERE.  The existence of the correction `U` in the required range
with the base-`p` SAFETY of `n + U` is proved kernel-clean from the existing,
pre-proved infrastructure:

  • `RoundUp.exists_lowDigits_between` (the EGRS density Fact, ratio `(p-1)/A = 2`):
    `[x, 2x)` contains a `LowDigits p` number  — gives `U ∈ [q^i - T, 2(q^i - T))`,
    hence `U < p^m` once `2(q^i - T) ≤ p^m` (the consumable form of condition (3));
  • `RepairDV.lowDigits_disjoint_add` (disjoint-support base-`p` addition): with
    `n` divisible by `p^m` (its low base-`p` block is all-zero, `m` = lowest nonzero
    digit index) and `U < p^m`, the sum `n + U = U + p^m·(n/p^m)` is `LowDigits p`.

These two pieces — `exists_U_in_range` and `add_U_lowDigits_p` — print
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`); they are the genuine,
load-bearing base-`p` carry content of the ADD branch and consume condition (3).

THE ONE LABELLED `sorry`.  The base-`q` CLEARING claim of `add_clears`
(`∀ idx ≥ j, ¬ BadAt q idx (n + U)` — the top oversized base-`q` digit and everything
above is cleared, `b_i* = b_i + 1`) is the irreducible carry-controlled PLACEMENT.
It genuinely needs the full repair context (`i` = least good index `> j`, the
`b_k = B` plateau for `j < k < i`, and the base-`q` carry chain of `T + U ↑ q^i`),
which the hypotheses of this primitive do not pin down.  This is exactly the part
Bloom–Croot (arXiv:2509.02835 §1) defer VERBATIM to [EGRS75]; Mathlib packages no
carry bookkeeping for it.  ONE labelled `sorry`, reported precisely.  No
`native_decide`, no bogus `axiom`, no circularity.

Formalizes the KNOWN theorem EGRS75 (1975).  Three primes is Erdős #376 (OPEN);
not attempted.  Recon: ~/Knowledge/Construct/recon/erdos_376.md.

Imports only the pre-existing kernel-clean files; modifies none of them.
-/

namespace Egrs75.ClearingP2

open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful

/-! ## Base-`p` block lemmas (KERNEL-CLEAN)

The lowest nonzero base-`p` digit index of `n` is `m`, encoded as `p^m ∣ n`
(`n % p^m = 0`): the base-`p` digits of `n` below index `m` are all `0`.  Two facts
follow that drive the ADD branch:

* the high base-`p` block `n / p^m` is itself `LowDigits p` (a digit suffix of `n`);
* adding any `LowDigits p` correction `U < p^m` keeps `LowDigits p` (the supports are
  disjoint: `U` fills the zeroed low block, `n / p^m` is untouched above it).
-/

/-- **High base-`p` block stays low (KERNEL-CLEAN).**  If every base-`p` digit of `n`
is `≤ (p-1)/2`, so is every base-`p` digit of `n / p^m`: the digit of `n / p^m` at
index `i` is the digit of `n` at index `m + i`. -/
theorem lowDigits_div_pow {p : ℕ} (hp : 2 ≤ p) {n m : ℕ}
    (hpn : LowDigits p n) : LowDigits p (n / p ^ m) := by
  rw [lowDigits_iff_digitAt hp] at hpn ⊢
  intro i
  -- digitAt p i (n / p^m) = (n / p^m) / p^i % p = n / p^(m+i) % p = digitAt p (m+i) n
  have hdiv : (n / p ^ m) / p ^ i = n / p ^ (m + i) := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]
  have : digitAt p i (n / p ^ m) = digitAt p (m + i) n := by
    unfold digitAt; rw [hdiv]
  rw [this]; exact hpn (m + i)

/-- **Base-`p` safety of `n + U` (KERNEL-CLEAN).**  Let `m` be the lowest nonzero
base-`p` digit index of `n` (`p^m ∣ n`).  If `U < p^m`, `U` and `n` are both
`LowDigits p`, and `n > 0`, then `n + U` is `LowDigits p`.

Proof.  `p^m ∣ n` gives `n = p^m · (n / p^m)`, so `n + U = U + p^m · (n / p^m)` with
`U < p^m`; the high block `n / p^m` is `LowDigits p` (`lowDigits_div_pow`) and `> 0`
(since `n > 0` forces `n ≥ p^m`), so `lowDigits_disjoint_add` applies — adding the
disjoint-support correction creates no oversized base-`p` digit.  This is the EGRS
"`U < p^m` keeps the base-`p` digits small" step. -/
theorem add_U_lowDigits_p {p : ℕ} (hp : 2 ≤ p) {n m U : ℕ}
    (hpn : LowDigits p n) (hpU : LowDigits p U) (hUlt : U < p ^ m)
    (hm : n % p ^ m = 0) (hnpos : 0 < n) : LowDigits p (n + U) := by
  have hp1 : 1 < p := by omega
  -- p^m ∣ n  ⟹  n = p^m * (n / p^m)
  have hdvd : p ^ m ∣ n := Nat.dvd_of_mod_eq_zero hm
  obtain ⟨H, hH⟩ := hdvd            -- n = p^m * H
  -- High block H = n / p^m is positive (n > 0).
  have hHpos : 0 < H := by
    rcases Nat.eq_zero_or_pos H with h0 | hpos
    · rw [h0, Nat.mul_zero] at hH; omega
    · exact hpos
  have hHlow : LowDigits p H := by
    have : H = n / p ^ m := by
      rw [hH, Nat.mul_div_cancel_left _ (pow_pos (by omega) m)]
    rw [this]; exact lowDigits_div_pow hp hpn
  -- n + U = U + p^m * H, a disjoint-support base-`p` sum.
  have hrw : n + U = U + p ^ m * H := by rw [hH]; ring
  rw [hrw]
  exact lowDigits_disjoint_add hp1 hUlt hHpos hpU hHlow

/-! ## Existence of the correction `U` (KERNEL-CLEAN)

`x = q^i - T ≥ 1` and the EGRS density Fact (`exists_lowDigits_between`) give a
`LowDigits p` number `U ∈ [x, 2x)`.  Condition (3) in the equality case is exactly
`2x ≤ p^m`, so `U < 2x ≤ p^m`: the correction lands inside the all-zero base-`p`
low block of `n`.  This is the load-bearing consumption of condition (3). -/

/-- **The ADD-branch correction exists (KERNEL-CLEAN).**  For odd `p ≥ 3`, set
`x = q^i - T`.  If `1 ≤ x` (a genuine clearing window) and `2*x ≤ p^m` (the equality
-case form of EGRS condition (3): `q^i - 1 < ((q-1)/B)((p-A-1)/(p-1))(p^m-1)` collapses
to `2(q^i - T) ≤ p^m` at `A = B = (p-1)/2 = (q-1)/2`), then there is a `LowDigits p`
number `U` with `q^i - T ≤ U` and `U < p^m`.

Drawn from the density Fact `RoundUp.exists_lowDigits_between` (interval `[x, 2x)`,
ratio `(p-1)/A = 2`); `U < 2x ≤ p^m`. -/
theorem exists_U_in_range {p q i T m : ℕ} (hp : 3 ≤ p) (hpo : Odd p)
    (hx1 : 1 ≤ q ^ i - T) (hcond3 : 2 * (q ^ i - T) ≤ p ^ m) :
    ∃ U, q ^ i - T ≤ U ∧ U < p ^ m ∧ LowDigits p U := by
  obtain ⟨U, hlo, hhi, hUlow⟩ := RoundUp.exists_lowDigits_between hp hpo (q ^ i - T) hx1
  exact ⟨U, hlo, by omega, hUlow⟩

/-! ## The ADD branch, assembled (`add_clears`) — carries the ONE base-`q` clearing `sorry`

`exists_U_in_range` + `add_U_lowDigits_p` deliver the correction `U` with the range,
base-`p` safety, and magnitude conjuncts FULLY kernel-clean.  The remaining base-`q`
CLEARING conjunct (`∀ idx ≥ j, ¬ BadAt q idx (n + U)`) is the irreducible
carry-controlled placement; it is the single labelled `sorry`. -/

end Egrs75.ClearingP2
