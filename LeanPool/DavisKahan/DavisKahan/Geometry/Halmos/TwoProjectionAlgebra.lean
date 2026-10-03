/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Tactic.Abel

/-! # Algebra shared by the ambient single- and double-angle tangent proofs -/

public section

namespace TauCeti.DavisKahan.TwoProjectionAlgebra

variable {A : Type*} [Ring A] {p D : A}

/-- Solve the two-projection relation for the square of the difference. -/
theorem difference_square_eq_sub (hkey : D * p + p * D + D * D = D) :
    D * D = D - D * p - p * D := by
  have h : D * D = D - (D * p + p * D) := eq_sub_of_add_eq' hkey
  rw [h]
  abel

/-- Left compression of the difference square is the negative diagonal corner. -/
theorem projection_mul_difference_square (hp : p * p = p) (hkey : D * p + p * D + D * D = D) :
    p * (D * D) = -(p * D * p) := by
  have e1 : p * (D * p) = p * D * p := (mul_assoc p D p).symm
  have e2 : p * (p * D) = p * D := by rw [← mul_assoc, hp]
  rw [difference_square_eq_sub hkey, mul_sub, mul_sub, e1, e2]
  abel

/-- Right compression gives the same negative diagonal corner. -/
theorem difference_square_mul_projection (hp : p * p = p) (hkey : D * p + p * D + D * D = D) :
    D * D * p = -(p * D * p) := by
  have e3 : D * p * p = D * p := by rw [mul_assoc, hp]
  rw [difference_square_eq_sub hkey, sub_mul, sub_mul, e3]
  abel

/-- An idempotent commutes with the square of its two-projection difference. -/
theorem projection_commutes_difference_square (hp : p * p = p) (hkey : D * p + p * D + D * D = D) :
    p * (D * D) = D * D * p := by
  rw [projection_mul_difference_square hp hkey, difference_square_mul_projection hp hkey]

end TauCeti.DavisKahan.TwoProjectionAlgebra
