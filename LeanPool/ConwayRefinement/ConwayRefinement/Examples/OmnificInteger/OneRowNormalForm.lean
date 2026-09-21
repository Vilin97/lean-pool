/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.HahnSeries.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.TypeTags

/-!
# Conway's one-row omnific integer

This module writes the normal form

`1 + Σ n : ℕ, ω ^ (1 / (n + 1))`,

with every displayed coefficient equal to one. Its positive exponents form one decreasing row
converging to zero, followed by the final constant term. The sibling statement `OneRowPrime`
records its arithmetic properties using only Mathlib and CombinatorialGames.
-/

@[expose] public noncomputable section

namespace Surreal.OmnificInteger.OneRowExample

open Set

/-- The `n`-th positive exponent in Conway's one-row normal form. -/
def exponent (n : ℕ) : ℝ :=
  1 / (n + 1 : ℝ)

@[simp]
theorem exponent_apply (n : ℕ) : exponent n = 1 / (n + 1 : ℝ) := by
  rfl

private theorem exponent_strictAnti : StrictAnti exponent := by
  refine strictAnti_nat_of_succ_lt fun n ↦ ?_
  rw [exponent_apply, exponent_apply]
  apply one_div_lt_one_div_of_lt
  · positivity
  · norm_num

/-- The natural-number row followed by the final constant-term index. -/
abbrev Index := WithTop ℕ

/-- The exponent at an index of the displayed normal form. -/
def exponentAtIndex : Index → Surreal
  | ⊤ => 0
  | (n : ℕ) => (exponent n : ℝ)

private theorem exponent_pos (n : ℕ) : 0 < exponent n := by
  rw [exponent_apply]
  positivity

private theorem exponentAtIndex_strictAnti : StrictAnti exponentAtIndex := by
  intro p q hpq
  induction p using WithTop.recTopCoe with
  | top => exact (not_lt_of_ge le_top hpq).elim
  | coe p =>
      induction q using WithTop.recTopCoe with
      | top =>
          change (0 : Surreal) < (exponent p : ℝ)
          exact_mod_cast exponent_pos p
      | coe q =>
          change ((exponent q : ℝ) : Surreal) < (exponent p : ℝ)
          exact_mod_cast exponent_strictAnti (WithTop.coe_lt_coe.mp hpq)

/-- The coefficient function supported on the displayed exponents. -/
def coefficient (i : Surreal) : ℝ :=
  by
    classical
    exact if i ∈ range exponentAtIndex then 1 else 0

private theorem support_coefficient :
    Function.support coefficient = range exponentAtIndex := by
  classical
  ext i
  simp [Function.support, coefficient]

/-- The displayed coefficient support is small enough for a surreal Hahn series. -/
theorem small_support_coefficient :
    Small.{0} (Function.support coefficient) := by
  rw [support_coefficient]
  infer_instance

/-- The displayed exponents are reverse well-ordered. -/
theorem wellFoundedOn_support_coefficient :
    (Function.support coefficient).WellFoundedOn (· > ·) := by
  rw [support_coefficient, wellFoundedOn_range]
  convert wellFounded_lt (α := Index) using 1
  ext p q
  exact exponentAtIndex_strictAnti.lt_iff_gt

/-- Conway's coefficient-one normal form `1 + Σ n, ω ^ (1 / (n + 1))`. -/
def normalForm : SurrealHahnSeries :=
  SurrealHahnSeries.mk coefficient small_support_coefficient
    wellFoundedOn_support_coefficient

@[simp]
theorem normalForm_coeff (i : Surreal) :
    normalForm.coeff i = coefficient i := by
  rw [normalForm, SurrealHahnSeries.coeff_mk, coefficient]

@[simp]
theorem normalForm_support : normalForm.support = range exponentAtIndex := by
  rw [normalForm, SurrealHahnSeries.support_mk, support_coefficient]

theorem normalForm_coeff_exponent (n : ℕ) :
    normalForm.coeff (exponent n : ℝ) = 1 := by
  classical
  rw [normalForm_coeff, coefficient, if_pos]
  exact ⟨(n : Index), rfl⟩

theorem normalForm_coeff_zero : normalForm.coeff 0 = 1 := by
  classical
  rw [normalForm_coeff, coefficient, if_pos]
  exact ⟨⊤, rfl⟩

end Surreal.OmnificInteger.OneRowExample
