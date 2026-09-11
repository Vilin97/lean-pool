/-
Copyright (c) 2026 Scott Harper, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Harper, Peiran Wu
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Polyrith
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
