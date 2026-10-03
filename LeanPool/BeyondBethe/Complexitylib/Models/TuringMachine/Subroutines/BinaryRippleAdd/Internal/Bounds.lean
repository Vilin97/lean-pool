/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Defs
public import Mathlib.Data.Nat.Size

/-!
# Linear binary addition -- resource-bound internals

This file relates the concrete scan and composed-machine bounds to the
standard binary widths of the two operands.
-/


@[expose] public section

namespace Complexity

namespace TM

theorem size_add_le_max_add_one_internal (lhs rhs : ℕ) :
    (lhs + rhs).size ≤ max lhs.size rhs.size + 1 := by
  rw [Nat.size_le]
  let width := max lhs.size rhs.size
  have hlhs : lhs < 2 ^ width := by
    exact lt_of_lt_of_le (Nat.lt_size_self lhs)
      (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have hrhs : rhs < 2 ^ width := by
    exact lt_of_lt_of_le (Nat.lt_size_self rhs)
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  have hsum : lhs + rhs < 2 ^ width + 2 ^ width :=
    Nat.add_lt_add hlhs hrhs
  simpa [width, pow_succ, Nat.mul_comm, Nat.two_mul] using hsum

theorem binaryRippleAddTime_le_internal (lhs rhs : ℕ) :
    binaryRippleAddTime lhs rhs ≤ 3 * (lhs.size + rhs.size) + 14 := by
  have hsum := size_add_le_max_add_one_internal lhs rhs
  have hmax : max lhs.size rhs.size ≤ lhs.size + rhs.size := by
    exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  simp only [binaryRippleAddTime]
  omega

end TM

end Complexity
