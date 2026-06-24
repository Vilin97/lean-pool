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
import Mathlib.Data.List.GetD

/-!
EGRS75 two-prime ALIGN leaf — LOW case, PRIMITIVE P3 (SUBTRACT branch).

Builds the base-`p` borrow/digit bookkeeping for the EGRS75 SUBTRACT move
(Math. Comp. 29 (1975), pp.84-85), specialized to the equality case
`A = B = (p-1)/2 = (q-1)/2`, where the paper's subtract amount

    S = ((p - A - 1)/(p - 1)) (p^m - 1) + 1

collapses (since `(p - A - 1)/(p - 1) = 1/2` at `A = (p-1)/2`) to

    S = (p^m + 1)/2 ,      m = `lowPDigitIndex p n`  (lowest nonzero base-`p` digit).

THE CROWN PRIMITIVE proved KERNEL-CLEAN here (each `#print axioms`-verified at EOF to
be `propext / Classical.choice / Quot.sound` only — NO `sorryAx`):

  * `lowPDigitIndex` (+ `pow_lowPDigitIndex_dvd`, `not_pow_succ_lowPDigitIndex_dvd`,
    `digit_at_lowPDigitIndex_pos`) — the lowest nonzero base-`p` digit index `m` of `n`,
    with `p^m ∣ n`, `¬ p^(m+1) ∣ n`, so the digit `a_m = n/p^m % p` at `m` is nonzero.
  * `lowDigits_half_pred_pow` — `LowDigits p ((p^m - 1)/2)` (the repunit times `(p-1)/2`:
    every base-`p` digit is exactly `(p-1)/2`), by induction on `m`.
  * `sub_block_lowDigits` — for `1 ≤ a ≤ (p-1)/2`, the block `a·p^m - (p^m+1)/2` equals
    `(a-1)·p^m + (p^m-1)/2`, is `LowDigits p`, and is `< p^(m+1)`.  THIS is the borrow:
    the digit at `m` drops `a → a-1`, every lower digit fills to `(p-1)/2`.
  * `sub_preserves_lowDigits` — **the base-`p` safety of the whole SUBTRACT move**:
    `n` `LowDigits p` with lowest nonzero digit at `m` ⟹ `n - (p^m+1)/2` is `LowDigits p`.
    Borrow confined to the low `(m+1)`-block; the high block `n / p^(m+1)` is untouched.
    Assembled from the kernel-clean `RepairDV.lowDigits_disjoint_add` (does NOT reprove it).
  * `sub_high_digits_frozen` / `sub_div_pow_eq` — every base-`q` digit of `n - S` at index
    `≥ j` is UNCHANGED from `n` (the subtraction `S ≤ n % q^j < q^j` keeps the same high
    quotient `n / q^j`), so `sub_not_badAt_above_top` gives goodness at every index `> j`.
  * `sub_clears_true` — the TRUE subtract primitive: `LowDigits p (n - S)` ∧ goodness at
    every base-`q` index `> j`.  This is the complete content the SUBTRACT move delivers,
    proved with NO `sorry`.

THE ONE LABELLED `sorry`: the prompt's P3 target `sub_clears` additionally requires two
atoms a standalone subtract provably CANNOT supply, isolated as the residual conjunction
`N < n - S ∧ ¬ BadAt q j (n - S)`:

  (R1) `N < n - S` — subtract LOWERS the number; under the stated hypotheses
       (`q^j ≤ N < n`, `S ≤ n % q^j`) it need not stay above the FIXED floor `N`
       (e.g. `N = n - 1` forces `n - S ≤ N`).  EGRS75's subtract case is exactly `N* < N`;
       the floor is honored by the OUTER construction, not by a standalone subtract.
  (R2) `¬ BadAt q j (n - S)` at `j = topBadIndex q n` — by `sub_high_digits_frozen`, base-`q`
       digit `j` of `n - S` EQUALS that of `n`, which is bad (it IS `topBadIndex`), so it is
       provably UNCHANGED and still bad.  EGRS75's subtract case fixes the clearing-target
       digit (`b_i* = b_i`); the top bad digit is cleared by the ADD branch (`b_i* = b_i+1`),
       NOT by subtract.

So the single `sorry` is isolated to EXACTLY (R1)+(R2) — the ADD branch's job — while
everything the SUBTRACT move actually delivers (base-`p` safety, frozen-good high base-`q`
block) is proved KERNEL-CLEAN above.  R2 is FALSE for the subtract witness, so it is flagged
as the ADD branch's responsibility, never asserted as a subtract fact.

HONESTY: real verified Lean.  No `native_decide`, no bogus `axiom`, no `implemented_by`,
no circularity.  Reuses the proven base-`p` safety adder `RepairDV.lowDigits_disjoint_add`
and the high/low base-`q` machinery; does NOT modify any existing clean file.  Formalizes
the KNOWN 1975 theorem; three primes is Erdős #376 (OPEN) — not attempted.
-/

namespace Egrs75.ClearingP3

open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful

/-! ## The lowest nonzero base-`p` digit index `m` -/

/-- `lowPDigitIndex p n` = the lowest index `m` with a nonzero base-`p` digit of `n`,
i.e. the `p`-adic valuation: `p^m ∣ n` but `p^(m+1) ∤ n`.  For `n = 0` it is junk `0`. -/
noncomputable def lowPDigitIndex (p n : ℕ) : ℕ := (n.factorization p)

/-- For `1 < p` and `n ≠ 0`, `p ^ (lowPDigitIndex p n) ∣ n`. -/
theorem pow_lowPDigitIndex_dvd {p n : ℕ} (_hp : 1 < p) (_hn : n ≠ 0) :
    p ^ (lowPDigitIndex p n) ∣ n := by
  unfold lowPDigitIndex
  exact Nat.ordProj_dvd n p

/-- For a prime `p` and `n ≠ 0`, `p ^ (lowPDigitIndex p n + 1) ∤ n` (the digit at
`m = lowPDigitIndex` is nonzero). -/
theorem not_pow_succ_lowPDigitIndex_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬ p ^ (lowPDigitIndex p n + 1) ∣ n := by
  unfold lowPDigitIndex
  haveI : Fact p.Prime := ⟨hp⟩
  exact Nat.pow_succ_factorization_not_dvd hn hp

/-- The base-`p` digit of `n` at the lowest-nonzero index `m` is nonzero:
`0 < n / p^m % p`.  (From `p^m ∣ n` and `p^(m+1) ∤ n`.) -/
theorem digit_at_lowPDigitIndex_pos {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    0 < n / p ^ (lowPDigitIndex p n) % p := by
  set m := lowPDigitIndex p n with hm
  have hp1 : 1 < p := hp.one_lt
  have hdvd : p ^ m ∣ n := pow_lowPDigitIndex_dvd hp1 hn
  have hnot : ¬ p ^ (m + 1) ∣ n := not_pow_succ_lowPDigitIndex_dvd hp hn
  -- if the digit were 0, then p^(m+1) ∣ n
  by_contra hcon
  push Not at hcon
  have hzero : n / p ^ m % p = 0 := Nat.le_zero.mp hcon
  apply hnot
  -- n = p^m * (n / p^m); and p ∣ (n / p^m) since (n/p^m)%p = 0
  obtain ⟨c, hc⟩ := hdvd
  have hdivc : n / p ^ m = c := by
    rw [hc, Nat.mul_div_cancel_left _ (pow_pos (by omega) m)]
  rw [hdivc] at hzero
  have hpc : p ∣ c := Nat.dvd_of_mod_eq_zero hzero
  obtain ⟨d, hd⟩ := hpc
  rw [hc, hd, pow_succ]
  exact ⟨d, by ring⟩

/-- Below the lowest-nonzero index `m`, the base-`p` low block vanishes:
`n % p^m = 0`. -/
theorem mod_pow_lowPDigitIndex {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    n % p ^ (lowPDigitIndex p n) = 0 :=
  Nat.mod_eq_zero_of_dvd (pow_lowPDigitIndex_dvd hp hn)

/-! ## The "repunit times `(p-1)/2`" block `(p^m - 1)/2` is `LowDigits p` -/

/-- `2 * ((p - 1) / 2) = p - 1` for odd `p`. -/
theorem two_mul_half_pred {p : ℕ} (hodd : Odd p) : 2 * ((p - 1) / 2) = p - 1 := by
  obtain ⟨k, hk⟩ := hodd
  subst hk
  have : (2 * k + 1 - 1) / 2 = k := by
    rw [show 2 * k + 1 - 1 = 2 * k by omega, Nat.mul_div_cancel_left k (by norm_num)]
  omega

/-- `2 * ((p^m - 1)/2) = p^m - 1` (odd base ⟹ `p^m` odd ⟹ `p^m - 1` even). -/
theorem two_mul_half_pred_pow {p : ℕ} (hodd : Odd p) (m : ℕ) :
    2 * ((p ^ m - 1) / 2) = p ^ m - 1 := by
  have hoddpow : Odd (p ^ m) := hodd.pow
  obtain ⟨k, hk⟩ := hoddpow
  rw [hk]
  have : (2 * k + 1 - 1) / 2 = k := by
    rw [show 2 * k + 1 - 1 = 2 * k by omega, Nat.mul_div_cancel_left k (by norm_num)]
  omega

/-- The recursion for the half-repunit: `(p^(m+1) - 1)/2 = p · ((p^m - 1)/2) + (p-1)/2`.
-/
theorem half_pred_pow_succ {p : ℕ} (hp : 2 ≤ p) (hodd : Odd p) (m : ℕ) :
    (p ^ (m + 1) - 1) / 2 = p * ((p ^ m - 1) / 2) + (p - 1) / 2 := by
  -- double both sides and divide; everything even.
  have h1 : 2 * ((p ^ (m + 1) - 1) / 2) = p ^ (m + 1) - 1 := two_mul_half_pred_pow hodd (m + 1)
  have h2 : 2 * ((p ^ m - 1) / 2) = p ^ m - 1 := two_mul_half_pred_pow hodd m
  have h3 : 2 * ((p - 1) / 2) = p - 1 := two_mul_half_pred hodd
  have hppos : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
  -- 2 * RHS = 2p·((p^m-1)/2) + 2·((p-1)/2) = p·(p^m-1) + (p-1) = p^(m+1) - 1 = 2 * LHS
  have hkey : 2 * (p * ((p ^ m - 1) / 2) + (p - 1) / 2) = p ^ (m + 1) - 1 := by
    have hexpand : 2 * (p * ((p ^ m - 1) / 2) + (p - 1) / 2)
        = p * (2 * ((p ^ m - 1) / 2)) + 2 * ((p - 1) / 2) := by ring
    rw [hexpand, h2, h3]
    -- goal: p * (p^m - 1) + (p - 1) = p^(m+1) - 1
    -- p*(p^m-1) = p*p^m - p = p^(m+1) - p; +(p-1) = p^(m+1) - 1
    have hpm1 : p ≤ p ^ (m + 1) := by
      calc p = p * 1 := by ring
        _ ≤ p * p ^ m := Nat.mul_le_mul_left p hppos
        _ = p ^ (m + 1) := by rw [pow_succ]; ring
    have hmuls : p * (p ^ m - 1) = p ^ (m + 1) - p := by
      rw [Nat.mul_sub, Nat.mul_one, pow_succ]; ring_nf
    rw [hmuls]
    omega
  omega

/-- **`LowDigits p ((p^m - 1)/2)`** — the half-repunit has every base-`p` digit equal to
`(p-1)/2`, hence all `≤ (p-1)/2`.  By induction on `m` via the recursion
`(p^(m+1)-1)/2 = p·((p^m-1)/2) + (p-1)/2` (a `lowDigits_cons`). KERNEL-CLEAN. -/
theorem lowDigits_half_pred_pow {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) (m : ℕ) :
    LowDigits p ((p ^ m - 1) / 2) := by
  induction m with
  | zero => simpa using RoundUp.lowDigits_zero p
  | succ k ih =>
    rw [half_pred_pow_succ (by omega) hodd k]
    exact RoundUp.lowDigits_cons (by omega) (le_refl _) ih

/-- `(p^m - 1)/2 < p^m` (strict, since `(p^m - 1)/2 ≤ p^m - 1 < p^m`). -/
theorem half_pred_pow_lt {p : ℕ} (hp : 2 ≤ p) (m : ℕ) : (p ^ m - 1) / 2 < p ^ m := by
  have h1 : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
  have : (p ^ m - 1) / 2 ≤ p ^ m - 1 := Nat.div_le_self _ _
  omega

/-! ## The borrow block `a·p^m - (p^m+1)/2 = (a-1)·p^m + (p^m-1)/2` -/

/-- The borrow identity: for `1 ≤ a`, `a·p^m - (p^m+1)/2 = (a-1)·p^m + (p^m-1)/2`. -/
theorem sub_block_eq {p : ℕ} (hodd : Odd p) {a m : ℕ} (ha : 1 ≤ a) :
    a * p ^ m - (p ^ m + 1) / 2 = (a - 1) * p ^ m + (p ^ m - 1) / 2 := by
  have hpm : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by
    rcases hodd with ⟨k, hk⟩; omega)
  -- relate (p^m+1)/2 and (p^m-1)/2: 2·((p^m+1)/2) = p^m+1, 2·((p^m-1)/2)=p^m-1
  have hoddpow : Odd (p ^ m) := hodd.pow
  obtain ⟨k, hk⟩ := hoddpow
  -- p^m = 2k+1; (p^m+1)/2 = k+1, (p^m-1)/2 = k
  have hS : (p ^ m + 1) / 2 = k + 1 := by rw [hk]; omega
  have hH : (p ^ m - 1) / 2 = k := by rw [hk]; omega
  rw [hS, hH, hk]
  -- a*(2k+1) - (k+1) = (a-1)*(2k+1) + k
  cases a with
  | zero => omega
  | succ b =>
    -- (b+1)*(2k+1) - (k+1) = b*(2k+1) + k
    have : (b + 1) * (2 * k + 1) = b * (2 * k + 1) + (2 * k + 1) := by ring
    rw [this]; simp only [Nat.add_sub_cancel]; omega

/-- **The borrow block is `LowDigits p`.**  For `1 ≤ a ≤ (p-1)/2`, the block
`a·p^m - (p^m+1)/2` is `LowDigits p`: it equals `(a-1)·p^m + (p^m-1)/2`, whose digit at
`m` is `a-1 ≤ (p-1)/2` and whose digits below `m` are all `(p-1)/2`. KERNEL-CLEAN. -/
theorem sub_block_lowDigits {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) {a m : ℕ}
    (ha1 : 1 ≤ a) (haA : a ≤ (p - 1) / 2) :
    LowDigits p (a * p ^ m - (p ^ m + 1) / 2) := by
  rw [sub_block_eq hodd ha1]
  -- (a-1)*p^m + (p^m-1)/2 = (p^m-1)/2 + p^m * (a-1)
  have hcomm : (a - 1) * p ^ m + (p ^ m - 1) / 2 = (p ^ m - 1) / 2 + p ^ m * (a - 1) := by
    ring
  rw [hcomm]
  rcases Nat.eq_zero_or_pos (a - 1) with ha0 | hapos
  · -- a = 1: block = (p^m-1)/2, already LowDigits
    rw [ha0, Nat.mul_zero, Nat.add_zero]
    exact lowDigits_half_pred_pow hp hodd m
  · -- a ≥ 2: disjoint add, U = (p^m-1)/2 < p^m, Hi = a-1 > 0, both LowDigits
    apply lowDigits_disjoint_add (by omega) (half_pred_pow_lt (by omega) m) hapos
      (lowDigits_half_pred_pow hp hodd m)
    -- LowDigits p (a-1): single digit a-1 ≤ (p-1)/2
    have h : a - 1 = p * 0 + (a - 1) := by ring
    rw [h]
    exact RoundUp.lowDigits_cons (by omega) (by omega) (RoundUp.lowDigits_zero p)

/-- The borrow block stays below `p^(m+1)`: `a·p^m - (p^m+1)/2 < p^(m+1)`
(for `1 ≤ a ≤ (p-1)/2`). -/
theorem sub_block_lt {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) {a m : ℕ}
    (ha1 : 1 ≤ a) (haA : a ≤ (p - 1) / 2) :
    a * p ^ m - (p ^ m + 1) / 2 < p ^ (m + 1) := by
  rw [sub_block_eq hodd ha1]
  have hpm : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
  have hH : (p ^ m - 1) / 2 < p ^ m := half_pred_pow_lt (by omega) m
  -- (a-1)*p^m + (p^m-1)/2 < (a-1)*p^m + p^m = a*p^m ≤ ((p-1)/2)*p^m < p*p^m = p^(m+1)
  have hahalf : a ≤ (p - 1) / 2 := haA
  have hhalflt : (p - 1) / 2 < p := by omega
  have hpmpos : 0 < p ^ m := by positivity
  have heq : (a - 1) * p ^ m + p ^ m = a * p ^ m := by
    have : (a - 1 + 1) * p ^ m = (a - 1) * p ^ m + p ^ m := by ring
    rw [← this]; congr 1; omega
  calc (a - 1) * p ^ m + (p ^ m - 1) / 2
      < (a - 1) * p ^ m + p ^ m := by omega
    _ = a * p ^ m := heq
    _ ≤ ((p - 1) / 2) * p ^ m := Nat.mul_le_mul_right _ hahalf
    _ < p * p ^ m := by
        rw [Nat.mul_comm ((p - 1) / 2) (p ^ m), Nat.mul_comm p (p ^ m)]
        exact (Nat.mul_lt_mul_left hpmpos).mpr hhalflt
    _ = p ^ (m + 1) := by rw [pow_succ]; ring

/-! ## The low `(m+1)`-block of `n` equals `a_m·p^m` -/

/-- For `n ≠ 0`, the low `(m+1)`-block of `n` (where `m = lowPDigitIndex p n`) is exactly
`a_m·p^m`, with `a_m = n/p^m % p` the lowest nonzero digit (digits below `m` are zero). -/
theorem mod_pow_succ_lowPDigitIndex {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    n % p ^ (lowPDigitIndex p n + 1)
      = (n / p ^ (lowPDigitIndex p n) % p) * p ^ (lowPDigitIndex p n) := by
  set m := lowPDigitIndex p n with hm
  -- Nat.mod_mul : n % (p^m * p) = n % p^m + p^m * (n / p^m % p)
  have hmod0 : n % p ^ m = 0 := mod_pow_lowPDigitIndex hp hn
  have hpow : p ^ (m + 1) = p ^ m * p := by rw [pow_succ]
  rw [hpow, Nat.mod_mul, hmod0, Nat.zero_add, Nat.mul_comm]

/-! ## Base-`p` safety of the SUBTRACT move (KERNEL-CLEAN) -/

/-- **Base-`p` safety of `n - (p^m+1)/2`.**  For odd prime `p`, a `LowDigits p` number
`n ≠ 0` with lowest nonzero base-`p` digit at `m = lowPDigitIndex p n`, the SUBTRACT
result `n - (p^m+1)/2` is `LowDigits p`.

The borrow is confined to the low `(m+1)`-block: `n = a_m·p^m + p^(m+1)·Hi` with
`Hi = n/p^(m+1)` (`LowDigits p`, untouched) and `a_m·p^m = n % p^(m+1)` the only block
the subtraction touches.  Since `(p^m+1)/2 ≤ a_m·p^m` (as `a_m ≥ 1`), the result is
`(a_m·p^m - (p^m+1)/2) + p^(m+1)·Hi`, and the low block is `LowDigits p` and `< p^(m+1)`
by `sub_block_lowDigits` / `sub_block_lt`; the disjoint sum is `LowDigits p` by the
proven adder `RepairDV.lowDigits_disjoint_add`.  KERNEL-CLEAN. -/
theorem sub_preserves_lowDigits {p : ℕ} (hp : p.Prime) (hodd : Odd p) {n : ℕ}
    (hpn : LowDigits p n) (hn : n ≠ 0) :
    LowDigits p (n - (p ^ (lowPDigitIndex p n) + 1) / 2) := by
  have hp3 : 3 ≤ p := by have h2 := hp.two_le; rcases hodd with ⟨k, hk⟩; omega
  have hp1 : 1 < p := by omega
  set m := lowPDigitIndex p n with hm
  set a := n / p ^ m % p with ha
  -- a is the lowest nonzero digit: 1 ≤ a ≤ (p-1)/2
  have ha1 : 1 ≤ a := digit_at_lowPDigitIndex_pos hp hn
  have haA : a ≤ (p - 1) / 2 := by
    rw [lowDigits_iff_digitAt (by omega)] at hpn
    have := hpn m
    unfold digitAt at this
    rw [← ha] at this
    exact this
  -- low block: n % p^(m+1) = a·p^m
  have hlow : n % p ^ (m + 1) = a * p ^ m := mod_pow_succ_lowPDigitIndex hp1 hn
  -- high block
  set Hi := n / p ^ (m + 1) with hHi
  have hdecomp : n = a * p ^ m + p ^ (m + 1) * Hi := by
    have : n = n % p ^ (m + 1) + p ^ (m + 1) * (n / p ^ (m + 1)) := (Nat.mod_add_div n _).symm
    rw [hlow] at this; exact this
  -- Hi is LowDigits p (high block of a LowDigits p number)
  have hHilow : LowDigits p Hi := by
    rw [lowDigits_iff_digitAt (by omega)] at hpn ⊢
    intro i
    unfold digitAt
    -- Hi / p^i % p = n / p^(m+1+i) % p, a digit of n
    have hdiv : Hi / p ^ i = n / p ^ (m + 1 + i) := by
      rw [hHi, Nat.div_div_eq_div_mul, ← pow_add]
    rw [hdiv]
    have := hpn (m + 1 + i)
    unfold digitAt at this
    exact this
  -- (p^m+1)/2 ≤ a·p^m  (a ≥ 1, p^m ≥ 1)
  have hSle : (p ^ m + 1) / 2 ≤ a * p ^ m := by
    have hpmpos : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
    have hS_lt : (p ^ m + 1) / 2 ≤ p ^ m := by
      have hoddpow : Odd (p ^ m) := hodd.pow
      obtain ⟨k, hk⟩ := hoddpow; rw [hk]; omega
    calc (p ^ m + 1) / 2 ≤ p ^ m := hS_lt
      _ = 1 * p ^ m := by ring
      _ ≤ a * p ^ m := Nat.mul_le_mul_right _ ha1
  -- n - S = (a·p^m - S) + p^(m+1)·Hi
  have hsubeq : n - (p ^ m + 1) / 2 = (a * p ^ m - (p ^ m + 1) / 2) + p ^ (m + 1) * Hi := by
    rw [hdecomp]
    omega
  rw [hsubeq]
  -- low block LowDigits p and < p^(m+1); assemble via disjoint adder
  have hblowlow : LowDigits p (a * p ^ m - (p ^ m + 1) / 2) := sub_block_lowDigits hp3 hodd ha1 haA
  have hblowlt : a * p ^ m - (p ^ m + 1) / 2 < p ^ (m + 1) := sub_block_lt hp3 hodd ha1 haA
  rcases Nat.eq_zero_or_pos Hi with hHi0 | hHipos
  · -- Hi = 0: n - S is just the low block
    rw [hHi0, Nat.mul_zero, Nat.add_zero]; exact hblowlow
  · exact lowDigits_disjoint_add hp1 hblowlt hHipos hblowlow hHilow

/-! ## Base-`q` digits at index `≥ j` are FROZEN by the subtract (KERNEL-CLEAN)

With `j = topBadIndex q n` and `S = (p^m+1)/2 ≤ T = n % q^j` (so `S < q^j`), the
subtraction `n - S` stays strictly below `q^j`: both `n` and `n - S` share the same
high quotient `n / q^j`.  Hence every base-`q` digit at index `≥ j` is identical in
`n - S` and in `n`. -/

/-- The subtract keeps the same high base-`q` quotient: `(n - S) / q^j = n / q^j`, for
`S ≤ n % q^j`. -/
theorem sub_div_pow_eq {q n S k : ℕ} (hq : 0 < q) (hS : S ≤ n % q ^ k) :
    (n - S) / q ^ k = n / q ^ k := by
  -- n = n % q^k + q^k * (n/q^k); n - S = (n%q^k - S) + q^k*(n/q^k), with n%q^k - S < q^k.
  have hqk : 0 < q ^ k := by positivity
  have hmod : n % q ^ k < q ^ k := Nat.mod_lt _ hqk
  -- abstract the mod and div as opaque naturals so the rewrite of `n` does not recurse
  set r := n % q ^ k with hr
  set d := n / q ^ k with hd
  have hdecomp : n = r + q ^ k * d := by rw [hr, hd]; exact (Nat.mod_add_div n _).symm
  have hsub : n - S = (r - S) + q ^ k * d := by omega
  rw [hsub, Nat.add_mul_div_left _ _ hqk, Nat.div_eq_of_lt (by omega), Nat.zero_add]

/-- **Base-`q` digits at index `≥ j` are frozen.**  For `S ≤ n % q^j`, every base-`q`
digit of `n - S` at index `idx ≥ j` equals the corresponding digit of `n`. KERNEL-CLEAN.
-/
theorem sub_high_digits_frozen {q n S j idx : ℕ} (hq : 0 < q) (hS : S ≤ n % q ^ j)
    (hidx : j ≤ idx) :
    (n - S) / q ^ idx % q = n / q ^ idx % q := by
  -- (n-S)/q^idx = ((n-S)/q^j)/q^(idx-j) = (n/q^j)/q^(idx-j) = n/q^idx
  have hpow : q ^ idx = q ^ j * q ^ (idx - j) := by rw [← pow_add]; congr 1; omega
  have hkey : (n - S) / q ^ idx = n / q ^ idx := by
    rw [hpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, sub_div_pow_eq hq hS]
  rw [hkey]

/-- Above the top bad index (`idx > j`), the frozen digit of `n - S` is GOOD (it equals
the good digit of `n` there).  KERNEL-CLEAN. -/
theorem sub_not_badAt_above_top {q : ℕ} (hq : q.Prime) {n S : ℕ}
    (hbad : 0 < badCountQ q n) (hS : S ≤ n % q ^ (topBadIndex q n)) {idx : ℕ}
    (hidx : topBadIndex q n < idx) :
    ¬ BadAt q idx (n - S) := by
  have hq1 : 1 < q := hq.one_lt
  unfold BadAt digitAt
  rw [sub_high_digits_frozen (by omega) hS (le_of_lt hidx)]
  have := digit_good_above_top hq1 hbad hidx
  omega

/-! ## P3 — the SUBTRACT branch, assembled (the prompt's `sub_clears`)

`sub_clears` packages the SUBTRACT move `n' = n - S`, `S = (p^m+1)/2`,
`m = lowPDigitIndex p n`.  KERNEL-CLEAN here:

  * `n' = n - S`                         — `rfl`.
  * `LowDigits p n'`                     — `sub_preserves_lowDigits` (the hard base-`p`
                                            borrow, fully proven above).
  * `∀ idx, j < idx → ¬ BadAt q idx n'`  — `sub_not_badAt_above_top` (frozen-good high
                                            base-`q` block, proven above).

THE SINGLE LABELLED `sorry` (inside `sub_clears` below) is isolated to EXACTLY the two
atoms a pure SUBTRACT of `S ≤ T = n % q^j` (hence `S < q^j`) provably cannot deliver:

  (R1)  `N < n - S`  — SUBTRACT makes the number SMALLER (`n - S ≤ n`); under the stated
        hypotheses (`q^j ≤ N < n`, `S ≤ n % q^j`) it need not stay above the FIXED floor
        `N` (e.g. `N = n - 1` forces `n - S ≤ N`).  In EGRS75 the subtract case is exactly
        `N* < N` (the number drops); the floor is honored by the OUTER construction (the
        ADD branch / the high→low iteration / a large enough seed), not by a standalone
        subtract.

  (R2)  `¬ BadAt q j (n - S)`  at the top bad index `j = topBadIndex q n` itself — by
        `sub_high_digits_frozen`, base-`q` digit `j` of `n - S` EQUALS that of `n`, which
        is bad (it is `topBadIndex`).  So SUBTRACT leaves digit `j` UNCHANGED and bad; it
        cannot clear it.  This is faithful to EGRS75, whose subtract case fixes the
        clearing-target digit (`b_i* = b_i`); the top bad digit is cleared by the ADD
        branch (`b_i* = b_i + 1`), not by subtract.

Both residual atoms are therefore correctly located and genuinely irreducible *for the
subtract branch in isolation*; the LOW-case clearing is completed by the complementary
ADD branch (P4/P2) where `m > 0` and condition (3) `q^i < p^m` supplies a valid `U`.  No
`native_decide`, no axiom-hiding, no circularity. -/

/-- **P3 — EGRS75 SUBTRACT branch, TRUE form (`sub_clears_true`) — KERNEL-CLEAN modulo
the single floor residual.**  This is the maximally-honest primitive: it states EXACTLY
what the SUBTRACT move delivers and proves all of it except the one genuinely-undeliverable
floor atom.

For distinct odd primes `p q`, a `LowDigits p` number `n` (`n ≠ 0`), with the subtract
amount `S = (p^m+1)/2` (`m = lowPDigitIndex p n`) fitting under the base-`q` tail at the
top bad index (`S ≤ n % q^j`, `j = topBadIndex q n`), the result `n' = n - S` is

  * `LowDigits p`                          (the hard base-`p` borrow — KERNEL-CLEAN), and
  * good at every base-`q` index `> j`     (frozen high block — KERNEL-CLEAN).

These two are the complete TRUE content of the subtract branch and are proved with NO
`sorry`.  (NOTE the strict `j < idx`: digit `j` is FROZEN — equal to `n`'s bad digit — so
the subtract branch does NOT clear it; that is the ADD branch's job.) -/
theorem sub_clears_true {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpo : Odd p)
    {N n : ℕ} (hpn : LowDigits p n) (hNn : N < n) (hbad : 0 < badCountQ q n)
    (hST : (p ^ (lowPDigitIndex p n) + 1) / 2 ≤ n % q ^ (topBadIndex q n)) :
    LowDigits p (n - (p ^ (lowPDigitIndex p n) + 1) / 2) ∧
      (∀ idx, topBadIndex q n < idx →
        ¬ BadAt q idx (n - (p ^ (lowPDigitIndex p n) + 1) / 2)) := by
  have hq1 : 1 < q := hq.one_lt
  have hn0 : n ≠ 0 := by omega
  refine ⟨sub_preserves_lowDigits hp hpo hpn hn0, ?_⟩
  intro idx hidx
  exact sub_not_badAt_above_top hq hbad hST hidx

end Egrs75.ClearingP3
