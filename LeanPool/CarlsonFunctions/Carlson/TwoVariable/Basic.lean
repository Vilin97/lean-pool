/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.BigOperators.Fin

/-! # Two-variable Carlson functions -/

open Complex
open scoped Matrix
@[expose] public noncomputable section CarlsonTwoVariable
namespace DirichletTransform.TwoVariable

/-- A pair, represented as a function on the canonical two-element index type. -/
def pair (x y : ℂ) : Fin 2 → ℂ := ![x, y]

/-- The zeroth entry of a pair is its first argument. -/
@[simp] theorem pair_zero (x y : ℂ) : pair x y 0 = x := rfl

/-- The first entry of a pair is its second argument. -/
@[simp] theorem pair_one (x y : ℂ) : pair x y 1 = y := rfl

/-- The sum of the entries of a pair. -/
theorem sum_pair (x y : ℂ) : ∑ i, pair x y i = x + y := by
  simp [pair, Fin.sum_univ_two]

/-- The transposition of the two coordinates of `Fin 2`. -/
def swap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- Composing a pair with the two-coordinate transposition exchanges its entries. -/
@[simp] theorem pair_comp_swap (x y : ℂ) : pair x y ∘ swap = pair y x := by
  funext i
  fin_cases i <;> rfl

end DirichletTransform.TwoVariable
end CarlsonTwoVariable
