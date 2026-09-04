/-
Copyright (c) 2026 AddCombi contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AddCombi contributors
-/

module

public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Data.Rat.Cast.CharZero

/-!
# Cast lemmas for nonnegative rational numbers
-/

namespace NNRat
variable {K : Type*} [DivisionRing K] [CharZero K]

@[simp]
public
lemma cast_sub {p q : ℚ≥0} (h : p ≤ q) : (↑(q - p) : K) = q - p := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact tsub_add_cancel_of_le h

end NNRat
