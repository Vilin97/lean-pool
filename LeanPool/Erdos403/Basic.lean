/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-!
# Erdős Problem #403 — sums of distinct factorials that are powers of 2

**Problem (Burr–Erdős; [ErGr80, p.79]).** Does
`2^m = a₁! + a₂! + ⋯ + aₖ!` with `a₁ < a₂ < ⋯ < aₖ` have only finitely many solutions?

**Answer: yes** (Frankl and Shen Lin, independently, 1976 — both proofs *unpublished*;
Lin's was a Bell Labs internal memorandum, "On Two Problems of Erdős Concerning Sums of
Distinct Factorials"). The largest solution is `2⁷ = 2! + 3! + 5! = 128`.

Because the original proofs are lost to the literature, this is a **reconstruction**, not a
transcription. The final proof (in `Erdos403.Sharp`) works in the factorial number system: a sum of
distinct factorials is exactly a factorial-base numeral with all digits `≤ 1`, and for every
`m ≥ 8` both `2^m` and `2^m − 1` carry a digit `≥ 2` at some index `≤ 11` — a finite, fixed-modulus
(`12!`) check. Both `erdos_403_finite` and `erdos_403_sharp` are `sorry`-free and kernel-pure.

* This file: the core definition `factSum`, the extremal `witness`, and the size sandwich.
* `Erdos403.FactBase`: the factorial-number-system digit machinery.
* `Erdos403.Sharp`: the headline theorems.
* `Erdos403.Superseded`: an earlier, unused 2-adic valuation approach, preserved for the record.

A "sum of distinct factorials" is modelled by a `Finset ℕ` of indices (distinctness of the `aᵢ` is
automatic). Note `0! = 1! = 1`, so e.g. `{0,1}` sums to `2`.
-/

namespace Erdos403

open scoped Nat

/-- The sum of distinct factorials indexed by `S`: `∑_{a ∈ S} a!`. -/
def factSum (S : Finset ℕ) : ℕ := ∑ a ∈ S, a !

/-- The extremal witness: `factSum {2, 3, 5} = 2! + 3! + 5! = 2 + 6 + 120 = 128 = 2⁷`. -/
theorem witness : factSum {2, 3, 5} = 2 ^ 7 := by
  rw [factSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  decide

/-! ## The size sandwich

For nonempty `S` with top element `M = max' S`: `M! ≤ factSum S ≤ 2·M!`. The lower bound (the top
factorial is one of the summands) is what the finiteness argument in `Erdos403.Sharp` uses. -/

/-- The partial factorial sum is bounded by the top factorial: `∑_{a<n} a! ≤ n!`. Tight at
`n = 0,1,2`. -/
theorem sum_range_factorial_le (n : ℕ) : ∑ a ∈ Finset.range n, a ! ≤ n ! := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · calc ∑ a ∈ Finset.range k, a ! + k ! ≤ k ! + k ! := Nat.add_le_add_right ih _
        _ = 2 * k ! := by ring
        _ ≤ (k + 1) * k ! := by gcongr; omega
        _ = (k + 1)! := (Nat.factorial_succ k).symm

/-- Lower bound of the sandwich: the top factorial is one of the summands. -/
theorem factorial_max_le_factSum {S : Finset ℕ} (h : S.Nonempty) :
    (S.max' h)! ≤ factSum S :=
  Finset.single_le_sum (f := fun a => a !) (fun _ _ => Nat.zero_le _) (S.max'_mem h)

end Erdos403
