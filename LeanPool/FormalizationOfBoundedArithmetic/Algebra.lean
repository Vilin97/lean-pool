/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

import Mathlib.Algebra.Regular.Defs

import LeanPool.FormalizationOfBoundedArithmetic.IOPEN
import LeanPool.FormalizationOfBoundedArithmetic.IDelta0

/-!
# LeanPool.FormalizationOfBoundedArithmetic.Algebra
-/

-- INSTANCES!

universe u v

section IOPEN
variable {M : Type u} [iopen : IOPENModel M]

open BASICModel IOPENModel


theorem isAddRightRegular_one : IsAddRightRegular (1 : M) := by
  unfold IsAddRightRegular Function.Injective
  exact B2

instance : IsRightCancelAdd M where
  add_right_cancel := by
    intro a
    unfold IsAddRightRegular Function.Injective
    intro b c
    simp only
    apply add_cancel_right.mp

instance instMulZeroClassLeanPool : MulZeroClass M where
  zero_mul := zero_mul
  mul_zero := by apply B5

instance instCommMonoidLeanPool : CommMonoid M where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

instance instAddCommMonoidLeanPool : AddCommMonoid M where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := by
    exact B3
  nsmul := nsmulRec
  add_comm := add_comm

instance instSemiringLeanPool : Semiring M where
  left_distrib := by
    exact IOPENModel.mul_add
  right_distrib := by
    intro a b c
    rw [<- iopen.mul_comm]
    rw [iopen.mul_add]
    rw [iopen.mul_comm]
    conv => lhs; rhs; rw [iopen.mul_comm]

end IOPEN

section IDelta0

open BASICModel
variable {M : Type u} [idelta0 : IDelta0Model M]

instance : IsOrderedAddMonoid M where
  add_le_add_left := fun _ _ a_1 c ↦ add_le_add_left a_1 c

-- D7 used
instance : IsOrderedMonoid M where
  mul_le_mul_left := fun a b h c ↦ by
    exact idelta0.le_mul_right h

instance instAddCommMonoidLeanPool' : AddCommMonoid M where


instance : IsOrderedRing M where
  zero_le_one := by exact idelta0.zero_le 1
  mul_le_mul_of_nonneg_left := by
    intro a h_zero_a b c hbc
    rw [mul_comm a b, mul_comm a c]
    exact idelta0.le_mul_right hbc
  mul_le_mul_of_nonneg_right := by
    intro c h_zero_c a b hab
    exact idelta0.le_mul_right hab

instance instCommSemiringLeanPool : CommSemiring M where

instance : IsLeftCancelAdd M where
  add_left_cancel x := by
    unfold IsAddLeftRegular
    unfold Function.Injective
    intro a1 a2
    simp only
    intro h
    conv at h =>
      rw [add_comm]
      rhs
      rw [add_comm]
    rw [@IOPENModel.add_cancel_right] at h
    exact h

-- instance : IsStrictOrderedRing M where
--   le_of_add_le_add_left := by
--     intro a b c h
--     rw [le_cancel_left]


end IDelta0
