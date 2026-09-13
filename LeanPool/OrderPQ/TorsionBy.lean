/-
Copyright (c) 2026 Scott Harper, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Harper, Peiran Wu
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset
/-!
# LeanPool.OrderPQ.TorsionBy
-/

@[expose] public section

variable {α : Type*} [CommGroup α]

variable (α) in
/-- The subgroup of elements `a` of a commutative group `α` satisfying `a ^ d = 1`. -/
@[to_additive (attr := simps)
/-- The subgroup of elements `a` of an additive commutative group `α` satisfying `d • a = 0`. -/]
def Subgroup.torsionBy' (d : ℕ) : Subgroup α where
  carrier := {a | a ^ d = 1}
  mul_mem' {x y} hx hy := by
    rw [Set.mem_ofPred_eq, mul_pow, hx, hy, mul_one]
  one_mem' := by
    rw [Set.mem_ofPred_eq, one_pow]
  inv_mem' {x} hx := by
    simp_all

@[to_additive (attr := simp)]
lemma Subgroup.mem_torsionBy' (d : ℕ) (a : α) :
    a ∈ Subgroup.torsionBy' α d ↔ a ^ d = 1 := Iff.rfl
