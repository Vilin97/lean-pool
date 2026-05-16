/-
Copyright (c) 2026 Rémy Degenne, Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Tactic.Ring.RingNF

/-!
# Two identities expressing `max`/`min` of two reals via their sum and absolute difference.
-/

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

lemma max_eq_add_add_abs_sub (a b : α) : max a b = 2⁻¹  * (a + b + |a - b|) := by
  rw [← max_add_min a, ← max_sub_min_eq_abs', add_sub_left_comm, add_sub_cancel_right]
  ring

lemma min_eq_add_sub_abs_sub (a b : α) : min a b = 2⁻¹ * (a + b - |a - b|) := by
  rw [← min_add_max a, ← max_sub_min_eq_abs', add_sub_assoc, sub_sub_cancel]
  ring
