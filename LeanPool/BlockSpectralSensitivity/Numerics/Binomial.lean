/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.NormNum.Pow

/-!
# The binomial evaluations of the construction

This file evaluates, as standalone identities in `ℕ`, the five binomial sums that the
counting arguments of `bs_lambda.txt` reduce to:

* Section 8.2 (active radius-one flags through a fixed pair): `N_A` (`typeAFlagSum_eq`) and
  `N_B` (`typeBFlagSum_eq`), whose sum is the constant `N_1 = 214620087510`.
* Section 9 (radius-two obstructions): the constant `K = 1300311466573824`
  (`radiusTwoSum_eq`; the Lean declaration for `K` is `BSLambda.LLL.radiusTwoConst`).
* Section 10.1 (dependency counts): `D_12` (`depSumOneTwo_eq`) and `D_22`
  (`depSumTwoTwo_eq`).

## Implementation notes

`Nat.choose` recurses through Pascal's rule, so kernel reduction (`decide`/`rfl`) on numbers
such as `Nat.choose 14006 7` is hopeless.  Every coefficient here is instead evaluated
through `Nat.choose_eq_descFactorial_div_factorial`: `Nat.descFactorial` recurses only on its
second argument, so it unfolds in a number of steps equal to that argument, and `norm_num`
finishes with one big division.  The three unfolding lemmas are made `local simp` below, so
each identity is a single `simp` call.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

public section

namespace BSLambda.Numerics

-- Evaluate `Nat.choose` by unfolding the descending factorial; see the implementation notes.
-- Local to this file, since unfolding `Nat.factorial` is only ever wanted on numerals.
attribute [local simp] Nat.choose_eq_descFactorial_div_factorial Nat.descFactorial Nat.factorial

/-- The number of Type-A radius-one flags through a fixed pair,
`N_A = C(d-1,3) + t * C(d-2,2) = 143,100,492,510` at `d = 7005`, `t = 3502` (Section 8.2). -/
theorem typeAFlagSum_eq : Nat.choose 7004 3 + 3502 * Nat.choose 7003 2 = 143100492510 := by simp

/-- The number of Type-B radius-one flags through a fixed pair,
`N_B = C(t,3) + 2 t C(t-1,2) + C(t,2) (t-2) = 71,519,595,000` at `t = 3502` (Section 8.2).
Together with `typeAFlagSum_eq` this gives `N_1 = N_A + N_B = 214,620,087,510`. -/
theorem typeBFlagSum_eq :
    Nat.choose 3502 3 + 2 * 3502 * Nat.choose 3501 2 + Nat.choose 3502 2 * 3500 =
      71519595000 := by
  simp

/-- The radius-two obstruction constant
`K = 9 * 2^20 * ∑_{l=0}^{8} C(8,l) C(28,8-l) 2^l = 1,300,311,466,573,824` (Section 9); the
Lean declaration for this number is `BSLambda.LLL.radiusTwoConst`. -/
theorem radiusTwoSum_eq :
    9 * 2 ^ 20 * (∑ l ∈ Finset.range 9, Nat.choose 8 l * Nat.choose 28 (8 - l) * 2 ^ l) =
      1300311466573824 := by
  simp [Finset.sum_range_succ]

/-- The number of type-2 events meeting a fixed five-element support in at least two
vertices, `D_12 = ∑_{s=2}^{5} C(5,s) C(14006,9-s) = 209,572,451,535,510,643,927,671,555`
(Section 10.1). -/
theorem depSumOneTwo_eq :
    ∑ s ∈ Finset.Icc 2 5, Nat.choose 5 s * Nat.choose 14006 (9 - s) =
      209572451535510643927671555 := by
  simp [Finset.sum_Icc_succ_top]

/-- The number of other nine-element supports meeting a fixed nine-element support in at
least two vertices, `D_22 = (∑_{s=2}^{9} C(9,s) C(14002,9-s)) - 1`
`= 753,455,972,623,601,870,517,771,054` (Section 10.1); the subtraction removes the event
itself. -/
theorem depSumTwoTwo_eq :
    (∑ s ∈ Finset.Icc 2 9, Nat.choose 9 s * Nat.choose 14002 (9 - s)) - 1 =
      753455972623601870517771054 := by
  simp [Finset.sum_Icc_succ_top]

end BSLambda.Numerics
