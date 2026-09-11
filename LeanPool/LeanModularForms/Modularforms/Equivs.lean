/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-! # Equivs -/


@[expose] public section



open TopologicalSpace Set
  Metric Filter Function Complex



/-- Negation as an equivalence `ℤ ≃ ℤ`. -/
def negEquiv : ℤ ≃ ℤ where
  toFun n := -n
  invFun n := -n
  left_inv := neg_neg
  right_inv := neg_neg


/-- The successor map as an equivalence `ℤ ≃ ℤ`. -/
def succEquiv : ℤ ≃ ℤ where
  toFun n := n.succ
  invFun n := n.pred
  left_inv := Int.pred_succ
  right_inv := Int.succ_pred





/-- Swaps the two entries of a length-2 vector. -/
def swap {α : Type*} : (Fin 2 → α) → (Fin 2 → α) := fun x => ![x 1, x 0]

@[simp]
lemma swap_apply {α : Type*} (b : Fin 2 → α) : swap b = ![b 1, b 0] := rfl

lemma swap_involutive {α : Type*} (b : Fin 2 → α) : swap (swap b) = b := by
  ext i
  fin_cases i <;> rfl

/-- Swapping the two entries of a length-2 vector as an equivalence. -/
def swapEquiv {α : Type*} : Equiv (Fin 2 → α) (Fin 2 → α) := Equiv.mk swap swap
  swap_involutive swap_involutive
