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
EGRS75 two-prime — digit toolkit for the single μ-move (2026-06-12).

NEW file.  Local, self-contained digit arithmetic consumed by
`EgrsMuFinish_20260612.lean`.  Deliberately does NOT import `EgrsFinish_core`
(so that file can later import the μ-closure without a cycle); the two tiny
overlaps (`mem_badIndexSet_iff`-style bridge) are re-proved here.

CONTENTS (all KERNEL-CLEAN, no sorry):
  • `div_mul_pow_mono`     — truncation at a lower scale keeps a larger value.
  • `add_carry_decomp`     — `n+U = R + q^i·(H+1)` under a single carry.
  • `add_div_pow_eq`       — `(n+U)/q^i = n/q^i + 1` (single carry).
  • `add_digit_i`          — digit `i` becomes `b_i + 1` (when `b_i < q-1`).
  • `add_high_frozen`      — digits above `i` are frozen (when `b_i < q-1`).
  • `add_low_digit`        — digits below `i` of `n+U` are the digits of `R`.
  • `badAt_of_mem` / `topBad_lt_of_good_from` — top-bad bound from a goodness ray.
  • `staircase`            — THE KEY: a number `< ((q^i)-1)/2 - 1` (i.e. `2R+3 ≤ q^i`)
                             has, below `i`, a strictly-good digit `k` with all
                             digits in `(k,i)` exactly `B = (q-1)/2`.  This is the
                             EGRS75 p.85 case-(c) "staircase" fact, and it is what
                             makes the clearing index DROP after every ADD move.

Formalizes part of the KNOWN theorem EGRS75 (1975); three primes is Erdős #376
(OPEN) — not attempted.  Recon: ~/Knowledge/Construct/recon/erdos_376.md.
-/

namespace Egrs75.MoveDigits

open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful

/-! ## Truncation monotonicity -/

/-- Keeping MORE high digits keeps a larger (or equal) value:
`n/q^b · q^b ≤ n/q^a · q^a` for `a ≤ b`. -/
theorem div_mul_pow_mono {q : ℕ} (_hq : 0 < q) (n : ℕ) {a b : ℕ} (hab : a ≤ b) :
    n / q ^ b * q ^ b ≤ n / q ^ a * q ^ a := by
  have hsplit : q ^ b = q ^ a * q ^ (b - a) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, ← Nat.div_div_eq_div_mul]
  have h1 : n / q ^ a / q ^ (b - a) * q ^ (b - a) ≤ n / q ^ a :=
    Nat.div_mul_le_self _ _
  calc n / q ^ a / q ^ (b - a) * (q ^ a * q ^ (b - a))
      = n / q ^ a / q ^ (b - a) * q ^ (b - a) * q ^ a := by ring
    _ ≤ n / q ^ a * q ^ a := Nat.mul_le_mul_right _ h1

/-! ## Single-carry ADD arithmetic -/

/-- The carry decomposition `n + U = R + q^i·(H+1)`, `R = (T+U) − q^i`,
`H = n / q^i`, valid when `q^i ≤ T + U` with `T = n % q^i`. -/
theorem add_carry_decomp {q : ℕ} (hq : 1 ≤ q) (n U i : ℕ)
    (hlo : q ^ i ≤ n % q ^ i + U) :
    n + U = (n % q ^ i + U - q ^ i) + q ^ i * (n / q ^ i + 1) := by
  have hqi : 0 < q ^ i := pow_pos (by omega) i
  have hsplit : n = n % q ^ i + q ^ i * (n / q ^ i) := (Nat.mod_add_div n (q ^ i)).symm
  have hmul : q ^ i * (n / q ^ i + 1) = q ^ i * (n / q ^ i) + q ^ i := by ring
  omega

/-- Under a single carry (`q^i ≤ T+U < 2q^i`), the block above `i` increments:
`(n+U)/q^i = n/q^i + 1`. -/
theorem add_div_pow_eq {q : ℕ} (hq : 1 < q) (n U i : ℕ)
    (hlo : q ^ i ≤ n % q ^ i + U) (hhi : n % q ^ i + U < 2 * q ^ i) :
    (n + U) / q ^ i = n / q ^ i + 1 := by
  have hqi : 0 < q ^ i := pow_pos (by omega) i
  have hdecomp := add_carry_decomp (by omega) n U i hlo
  have hRlt : n % q ^ i + U - q ^ i < q ^ i := by omega
  rw [hdecomp, Nat.add_mul_div_left _ _ hqi, Nat.div_eq_of_lt hRlt, Nat.zero_add]

/-- The increment does not cascade: `(H+1)/q^s = H/q^s` for `s ≥ 1` when the
units digit of `H` is below `q − 1`. -/
theorem succ_div_pow_eq {q : ℕ} (hq : 1 < q) {H : ℕ} (hH : H % q < q - 1)
    {s : ℕ} (hs : 1 ≤ s) : (H + 1) / q ^ s = H / q ^ s := by
  have hq0 : 0 < q := by omega
  have hHq : (H + 1) / q = H / q := by
    have hd := Nat.div_add_mod H q
    have h1 : H + 1 = q * (H / q) + (H % q + 1) := by omega
    rw [h1, Nat.mul_add_div hq0,
      Nat.div_eq_of_lt (show H % q + 1 < q by omega), Nat.add_zero]
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [pow_succ, mul_comm (q ^ t) q, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul, hHq]

/-- **Digit at `i` becomes `b_i + 1`** under a single carry, when `b_i < q − 1`. -/
theorem add_digit_i {q : ℕ} (hq : 1 < q) (n U i : ℕ)
    (hlo : q ^ i ≤ n % q ^ i + U) (hhi : n % q ^ i + U < 2 * q ^ i)
    (hbi : n / q ^ i % q < q - 1) :
    (n + U) / q ^ i % q = n / q ^ i % q + 1 := by
  rw [add_div_pow_eq hq n U i hlo hhi]
  have hd := Nat.div_add_mod (n / q ^ i) q
  have h1 : n / q ^ i + 1 = q * (n / q ^ i / q) + (n / q ^ i % q + 1) := by omega
  rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- **Digits above `i` are frozen** under a single carry, when `b_i < q − 1`. -/
theorem add_high_frozen {q : ℕ} (hq : 1 < q) (n U i idx : ℕ)
    (hlo : q ^ i ≤ n % q ^ i + U) (hhi : n % q ^ i + U < 2 * q ^ i)
    (hbi : n / q ^ i % q < q - 1) (hidx : i < idx) :
    (n + U) / q ^ idx % q = n / q ^ idx % q := by
  have hsplit : q ^ idx = q ^ i * q ^ (idx - i) := by
    rw [← pow_add]; congr 1; omega
  have h1 : (n + U) / q ^ idx = (n + U) / q ^ i / q ^ (idx - i) := by
    rw [hsplit, Nat.div_div_eq_div_mul]
  have h2 : n / q ^ idx = n / q ^ i / q ^ (idx - i) := by
    rw [hsplit, Nat.div_div_eq_div_mul]
  rw [h1, h2, add_div_pow_eq hq n U i hlo hhi,
    succ_div_pow_eq hq hbi (by omega : 1 ≤ idx - i)]

/-- **Digits below `i` of `n+U` are the digits of the new tail `R`.** -/
theorem add_low_digit {q : ℕ} (hq : 1 < q) (n U i t : ℕ) (ht : t < i)
    (hlo : q ^ i ≤ n % q ^ i + U) :
    (n + U) / q ^ t % q = (n % q ^ i + U - q ^ i) / q ^ t % q := by
  have hdecomp := add_carry_decomp (by omega) n U i hlo
  have hlow := digitAt_add_low (p := q) (by omega) (k := i)
    (u := n % q ^ i + U - q ^ i) (h := n / q ^ i + 1) (i := t) ht
  unfold digitAt at hlow
  rwa [hdecomp]

/-! ## Top-bad bound from a goodness ray -/

/-- Membership in `badIndexSet` is exactly `BadAt` (local copy; the original
lives in `EgrsFinish_core`, which this file must not import). -/
theorem mem_badIndexSet_iff' {q n i : ℕ} (hq : 1 < q) :
    i ∈ badIndexSet q n ↔ BadAt q i n := by
  unfold BadAt digitAt badIndexSet
  simp only [Finset.mem_filter, Finset.mem_range, bigQ, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hbig⟩
    rwa [getD_digits n i (by omega)] at hbig
  · intro hbig
    have hlen : i < (Nat.digits q n).length := by
      by_contra hcon
      push Not at hcon
      rw [← getD_digits n i (by omega), List.getD_eq_default _ 0 hcon] at hbig
      omega
    refine ⟨hlen, ?_⟩
    rwa [getD_digits n i (by omega)]

/-- If every digit at index `≥ x` is good, the top bad index is `< x`. -/
theorem topBad_lt_of_good_from {q n x : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n)
    (hgood : ∀ idx, x ≤ idx → n / q ^ idx % q ≤ (q - 1) / 2) :
    topBadIndex q n < x := by
  by_contra hcon
  push Not at hcon
  have hmem := topBadIndex_mem hq hbad
  rw [mem_badIndexSet_iff' hq] at hmem
  unfold BadAt digitAt at hmem
  have := hgood _ hcon
  omega

/-! ## THE STAIRCASE (EGRS75 p.85, case (c))

A tail `R` with `2R + 3 ≤ q^i` (strictly below the all-`B` value `(q^i−1)/2`)
has a strictly-good digit `k < i` such that every digit in `(k, i)` is exactly
`B`.  Consequence: after the tight-window ADD, the new clearing index drops
strictly below the old one — the μ-measure first coordinate falls. -/

/-- **The staircase lemma (KERNEL-CLEAN).** -/
theorem staircase {q : ℕ} (hq3 : 3 ≤ q) (hqo : Odd q) :
    ∀ i R : ℕ, 2 * R + 3 ≤ q ^ i →
      ∃ k, k < i ∧ R / q ^ k % q < (q - 1) / 2 ∧
        ∀ t, k < t → t < i → R / q ^ t % q = (q - 1) / 2 := by
  intro i
  induction i with
  | zero =>
    intro R hR
    exfalso
    simp only [pow_zero] at hR
    omega
  | succ i ih =>
    intro R hR
    have hq1 : 1 < q := by omega
    have hqi : 0 < q ^ i := pow_pos (by omega) i
    have hqs : q ^ (i + 1) = q ^ i * q := pow_succ q i
    have hB2 : 2 * ((q - 1) / 2) = q - 1 := by
      obtain ⟨c, hc⟩ := hqo; omega
    have hRlt : R < q ^ (i + 1) := by omega
    have hdlt : R / q ^ i < q := by
      rw [Nat.div_lt_iff_lt_mul hqi]
      have hcomm : q * q ^ i = q ^ i * q := Nat.mul_comm _ _
      omega
    have hdmod : R / q ^ i % q = R / q ^ i := Nat.mod_eq_of_lt hdlt
    rcases Nat.lt_trichotomy (R / q ^ i) ((q - 1) / 2) with hlt | heq | hgt
    · -- top digit of the window strictly good: it is the barrier.
      exact ⟨i, Nat.lt_succ_self i, by rw [hdmod]; exact hlt,
        fun t ht1 ht2 => by omega⟩
    · -- top digit exactly B: recurse into the low block.
      have hsplit : R = R % q ^ i + q ^ i * (R / q ^ i) :=
        (Nat.mod_add_div R (q ^ i)).symm
      have hlow2 : 2 * (R % q ^ i) + 3 ≤ q ^ i := by
        have h1 : q ^ i * (q - 1) + q ^ i = q ^ i * q := by
          have hq' : q - 1 + 1 = q := by omega
          calc q ^ i * (q - 1) + q ^ i = q ^ i * ((q - 1) + 1) := by ring
            _ = q ^ i * q := by rw [hq']
        have h2 : 2 * R = 2 * (R % q ^ i) + q ^ i * (q - 1) := by
          calc 2 * R = 2 * (R % q ^ i + q ^ i * (R / q ^ i)) := by
                conv_lhs => rw [hsplit]
            _ = 2 * (R % q ^ i) + q ^ i * (2 * (R / q ^ i)) := by ring
            _ = 2 * (R % q ^ i) + q ^ i * (2 * ((q - 1) / 2)) := by rw [heq]
            _ = 2 * (R % q ^ i) + q ^ i * (q - 1) := by rw [hB2]
        omega
      obtain ⟨k, hk, hkstrict, hkbet⟩ := ih (R % q ^ i) hlow2
      have hlowdig : ∀ t, t < i → R / q ^ t % q = (R % q ^ i) / q ^ t % q := by
        intro t ht
        have hlow := digitAt_add_low (p := q) (by omega) (k := i)
          (u := R % q ^ i) (h := R / q ^ i) (i := t) ht
        unfold digitAt at hlow
        calc R / q ^ t % q
            = (R % q ^ i + q ^ i * (R / q ^ i)) / q ^ t % q := by
              conv_lhs => rw [hsplit]
          _ = (R % q ^ i) / q ^ t % q := hlow
      refine ⟨k, by omega, ?_, ?_⟩
      · rw [hlowdig k hk]; exact hkstrict
      · intro t ht1 ht2
        rcases Nat.lt_or_ge t i with hti | hti
        · rw [hlowdig t hti]; exact hkbet t ht1 hti
        · have hteq : t = i := by omega
          subst hteq
          rw [hdmod]; exact heq
    · -- top digit > B: impossible below the all-B ceiling.
      exfalso
      have h1 : ((q - 1) / 2 + 1) * q ^ i ≤ R / q ^ i * q ^ i :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : R / q ^ i * q ^ i ≤ R := Nat.div_mul_le_self R (q ^ i)
      have h3 : 2 * (((q - 1) / 2 + 1) * q ^ i) = q ^ i * q + q ^ i := by
        calc 2 * (((q - 1) / 2 + 1) * q ^ i)
            = (2 * ((q - 1) / 2) + 2) * q ^ i := by ring
          _ = (q + 1) * q ^ i := by rw [hB2]; congr 1; omega
          _ = q ^ i * q + q ^ i := by ring
      omega

end Egrs75.MoveDigits
