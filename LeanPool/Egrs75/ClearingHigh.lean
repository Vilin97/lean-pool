/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Egrs75.DigitAtToolkit
import LeanPool.Egrs75.RoundUp
import Mathlib.Data.Finset.Attr

/-!
The HIGH-case clearing: when the floor `N` lies below `q^j` (the scale of the
top oversized base-`q` digit), a fresh `LowDigits p` window number drawn from
`[q^j, 2·q^j)` is automatically good at every base-`q` index `≥ j` and exceeds
`N` — no carry control is needed.  This discharges the high case of the
clearing dichotomy; the low case is the μ-measure machine in `MuFinish`.
-/

@[expose] public section

namespace Egrs75.Probe

open Nat
open Egrs75
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful

/-- Goodness of the high block: if `q^j ≤ m < 2*q^j` and `q ≥ 3`, then every base-`q`
digit of `m` at index `≥ j` is `≤ (q-1)/2` (digit at `j` is `1`, digits above are `0`). -/
theorem good_above_of_mem_window {q j m : ℕ} (hq : 3 ≤ q)
    (hlo : q ^ j ≤ m) (hhi : m < 2 * q ^ j) :
    ∀ i, j ≤ i → m / q ^ i % q ≤ (q - 1) / 2 := by
  intro i hi
  have hqpos : 0 < q ^ j := pow_pos (by omega) j
  rcases eq_or_lt_of_le hi with rfl | hlt
  · -- i = j: m / q^j = 1, so digit = 1 % q = 1 ≤ (q-1)/2
    have h1 : m / q ^ j = 1 := by
      have hub : m < (1 + 1) * q ^ j := by rw [add_mul, one_mul]; omega
      have hlb : 1 * q ^ j ≤ m := by rw [one_mul]; exact hlo
      exact Nat.div_eq_of_lt_le hlb hub
    rw [h1, Nat.mod_eq_of_lt (show (1:ℕ) < q by omega)]
    omega
  · -- i > j: m / q^i = 0 since m < 2*q^j ≤ q^(j+1) ≤ q^i
    have hstep : 2 * q ^ j ≤ q ^ (j + 1) := by
      rw [pow_succ]; nlinarith [pow_pos (show 0 < q by omega) j]
    have hle : q ^ (j + 1) ≤ q ^ i := Nat.pow_le_pow_right (by omega) hlt
    have : m < q ^ i := by omega
    rw [Nat.div_eq_of_lt this]
    simp

/-- **Clean branch of `egrs_clearing`: when `q^j > N`.**  If the top bad base-`q`
index `j` of `n` satisfies `q^j > N`, then a `LowDigits p` number drawn from the
window `[q^j, 2*q^j)` is `> N` and good at every base-`q` index `≥ j` — no carry
control needed.  KERNEL-CLEAN. -/
theorem clearing_high {p q : ℕ} (hp3 : 3 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q)
    (N : ℕ) {j : ℕ} (hjN : N < q ^ j) :
    ∃ n', LowDigits p n' ∧ N < n' ∧ (∀ i, j ≤ i → ¬ BadAt q i n') := by
  have hx1 : 1 ≤ q ^ j := Nat.one_le_pow _ _ (by omega)
  obtain ⟨m, hlo, hhi, hlowp⟩ := RoundUp.exists_lowDigits_between hp3 hpo (q ^ j) hx1
  refine ⟨m, hlowp, lt_of_lt_of_le hjN hlo, ?_⟩
  intro i hi
  unfold BadAt digitAt
  have := good_above_of_mem_window hq3 hlo hhi i hi
  omega

end Egrs75.Probe
