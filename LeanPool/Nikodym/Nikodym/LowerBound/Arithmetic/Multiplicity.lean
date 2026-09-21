/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib

/-!
# Natural-number multiplicity choice

Blueprint node C05: with `r = a * M / L + 1` one has `a * M < r * L ≤ a * M + L ≤ (a + 1) * M`
and `a ≤ r`. If also `(a + 1) * M ≤ q * L`, then `r ≤ q`.

In the induction, `a = 8 d ^ 2`, `C = a + 1`, and `M = Δ q ^ k`.
-/

namespace Nikodym.LowerBound

/-- Blueprint C05: `a * M < r * L` for `r = a * M / L + 1`. -/
theorem lt_mul (a M L : ℕ) (hL : 0 < L) :
    a * M < (a * M / L + 1) * L := by
  rw [add_one_mul]
  exact Nat.lt_div_mul_add hL

/-- Blueprint C05: `r * L ≤ a * M + L` for `r = a * M / L + 1`. -/
theorem mul_le (a M L : ℕ) :
    (a * M / L + 1) * L ≤ a * M + L := by
  rw [add_one_mul]
  exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _

/-- Blueprint C05: `a * M + L ≤ (a + 1) * M` when `L ≤ M`. -/
theorem le_mul_add (a M L : ℕ) (hLM : L ≤ M) :
    a * M + L ≤ (a + 1) * M := by
  rw [add_one_mul]
  exact Nat.add_le_add_left hLM _

/-- Blueprint C05: `a ≤ r` for `r = a * M / L + 1`, using `0 < L` and `L ≤ M`. -/
theorem le_r (a M L : ℕ) (hL : 0 < L) (hLM : L ≤ M) :
    a ≤ a * M / L + 1 := by
  have hlt : a * L < (a * M / L + 1) * L :=
    (Nat.mul_le_mul_left a hLM).trans_lt (lt_mul a M L hL)
  exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right hlt)

/-- Blueprint C05: if `(a + 1) * M ≤ q * L`, then `r ≤ q`. -/
theorem r_le_of_le (a M L q : ℕ) (hL : 0 < L) (hM : 0 < M)
    (hq : (a + 1) * M ≤ q * L) :
    a * M / L + 1 ≤ q := by
  rw [Nat.add_one_le_iff, Nat.div_lt_iff_lt_mul hL]
  exact (Nat.mul_lt_mul_of_pos_right a.lt_succ_self hM).trans_le hq

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
