/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import Mathlib.Data.Fin.VecNotation
public import LeanPool.NaslundCounterexample.Definitions

/-!
# The ten-word code

The construction lifts a set of polynomials of degree below `m` to one of degree below `m + 8`,
and the four coordinates `(s_0, s_1, s_2, s_∞)` attached to a lifted polynomial — its three
values at the points of `F_3` and its coefficient at the top of the new range — are constrained
to lie in a fixed ten-element code `S ⊆ F_3^4`.

The only property of `S` the construction uses is that two of its words never differ by a vector
with every coordinate in `{0, 1}`, the set of squares of `F_3`; this file records that property,
together with the three facts about squares in `F_3` it is used with. Everything here is a finite
check over `Fin 4 → ZMod 3` and `ZMod 3`, decided by the kernel.
-/

public section

namespace NaslundCounterexample

/-- The ten-word code `S ⊆ F_3^4`, in the coordinates `(s_0, s_1, s_2, s_∞)`:
`0000`, `0211`, `0121`, `0112`, `1200`, `1020`, `1002`, `2212`, `2122`, `2221`. -/
def code : Finset (Fin 4 → ZMod 3) :=
  {![0, 0, 0, 0], ![0, 2, 1, 1], ![0, 1, 2, 1], ![0, 1, 1, 2], ![1, 2, 0, 0], ![1, 0, 2, 0],
    ![1, 0, 0, 2], ![2, 2, 1, 2], ![2, 1, 2, 2], ![2, 2, 2, 1]}

/-- The code has ten words. -/
theorem code_card : code.card = 10 := by decide +kernel

/-- **The code property.** Two words of `S` whose difference has every coordinate in `{0, 1}` —
the two squares of `F_3` — are equal. -/
theorem code_property :
    ∀ s ∈ code, ∀ s' ∈ code, (∀ i, s' i - s i = 0 ∨ s' i - s i = 1) → s = s' := by decide +kernel

/-- Every square in `F_3` is `0` or `1`. -/
theorem sq_eq_zero_or_one (a : ZMod 3) : a ^ 2 = 0 ∨ a ^ 2 = 1 := by revert a; decide

/-- In `F_3`, `a ^ 2 = 0` forces `a = 0`. -/
theorem eq_zero_of_sq_eq_zero (a : ZMod 3) (h : a ^ 2 = 0) : a = 0 := by revert a; decide

/-- In `F_3`, `v ^ 2 + u ^ 2 = 0` forces `u = v = 0`; this is what makes the base `B_4`
square-difference-free. -/
theorem eq_zero_of_sq_add_sq (u v : ZMod 3) (h : v ^ 2 + u ^ 2 = 0) : u = 0 ∧ v = 0 := by
  revert u v; decide

end NaslundCounterexample
