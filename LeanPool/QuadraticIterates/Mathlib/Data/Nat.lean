/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Linarith.Frontend

/-!
# Natural-number lemmas

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- If `a ≤ c`, `b ≤ d` and `a * b = c * d` with `c, d` positive, then `a = c` and `b = d`.
The positivity hypotheses are needed since `ℕ`-multiplication is not strictly monotone at `0`
(compare `mul_eq_mul_iff_eq_and_eq`, which does not apply to `ℕ`). -/
lemma Nat.eq_and_eq_of_le_of_le_of_mul_eq_mul {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d)
    (hmul : a * b = c * d) (hc : 0 < c) (hd : 0 < d) : a = c ∧ b = d := by
  constructor <;> nlinarith [Nat.mul_le_mul hac hbd]
