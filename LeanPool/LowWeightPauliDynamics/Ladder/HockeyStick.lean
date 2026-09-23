/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# Hockey-stick identity, in the form the LPD cumulation proof uses

This file proves the hockey-stick identity `∑_{l < g} C(l, m) = C(g, m+1)` over `Finset.range`,
in `ℕ` and cast to `ℝ`. The proof of `apd:cor:norm_cumulation_jump` closes its inductive step
with this identity, applied as `∑_{l=0}^{g-1} C(l, m-1) = C(g, m)`.

Mathlib has `Nat.sum_Icc_choose : ∑ m ∈ Finset.Icc k n, m.choose k = (n+1).choose (k+1)`,
but the paper's sum runs over `Finset.range g` with the vanishing low terms included.
We prove that form directly by induction on `g` via Pascal's rule; it is shorter than
reconciling the index ranges, and avoids `ℕ`-subtraction at `g = 0`.

## Main results

* `sum_range_choose`: the identity in `ℕ`.
* `sum_range_choose_real`: the same identity with both sides cast to `ℝ`.
-/

@[expose] public section

namespace Lean4LPD

open Finset

/-- **Hockey-stick identity**, `range` form: `∑_{l < g} C(l, m) = C(g, m+1)`.

This is the identity used in `apd:cor:norm_cumulation_jump` to sum the
damped ladder recursion over rotations. Note both sides vanish for `g = 0`. -/
theorem sum_range_choose (m : ℕ) :
    ∀ g : ℕ, ∑ l ∈ range g, l.choose m = g.choose (m + 1) := by
  intro g
  induction g with
  | zero => simp
  | succ g ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ]
    ring

/-- Real-valued restatement, which is what the cumulation bound consumes. -/
theorem sum_range_choose_real (m g : ℕ) :
    ∑ l ∈ range g, (l.choose m : ℝ) = (g.choose (m + 1) : ℝ) := by
  rw [← Nat.cast_sum, sum_range_choose]

end Lean4LPD
