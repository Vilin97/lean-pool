/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.OmnificIntegers
public import Mathlib.Data.Prod.Lex
public import Mathlib.SetTheory.Ordinal.Arithmetic

import all LeanPool.ConwayRefinement.CombinatorialGames.Surreal.HahnSeries.Basic

/-!
# A concrete degree-two omnific integer

The nonconstant exponents of the explicit element are

`1 / (m + 1) + 1 / ((m + 1) * (m + 2) * (n + 1))`,

for `m n : ℕ`, and every displayed coefficient is one. For fixed `m` these exponents decrease to
`1 / (m + 1)`; the rows themselves decrease to zero. The final constant term is also one.

The construction is universe-polymorphic: the normal form is written in the surreal numbers of
every universe `u`. Its support order type and primeness are stated in `DegreeTwoPrime`.
-/

universe u

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.Oz.DegreeTwoExample

open Set

/-- The positive Conway exponent in row `m` and column `n`. -/
def exponent (m n : ℕ) : ℝ :=
  1 / (m + 1 : ℝ) +
    1 / ((m + 1 : ℝ) * (m + 2 : ℝ) * (n + 1 : ℝ))

@[simp]
theorem exponent_apply (m n : ℕ) :
    exponent m n =
      1 / (m + 1 : ℝ) +
        1 / ((m + 1 : ℝ) * (m + 2 : ℝ) * (n + 1 : ℝ)) := by
  rfl

private def cutoff (m : ℕ) : ℝ :=
  1 / (m + 1 : ℝ)

private theorem exponent_strictAnti_second (m : ℕ) :
    StrictAnti (exponent m) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [exponent_apply, exponent_apply]
  gcongr
  omega

private theorem cutoff_lt_exponent (m n : ℕ) :
    cutoff m < exponent m n := by
  rw [cutoff, exponent_apply]
  have : 0 <
      1 / ((m + 1 : ℝ) * (m + 2 : ℝ) * (n + 1 : ℝ)) := by
    positivity
  linarith

private theorem next_exponent_zero_lt_cutoff (m : ℕ) :
    exponent (m + 1) 0 < cutoff m := by
  rw [exponent_apply, cutoff]
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one]
  ring_nf
  nlinarith

private theorem exponent_gt_of_first_lt
    {m m' n n' : ℕ} (hmm' : m < m') :
    exponent m n > exponent m' n' := by
  calc
    exponent m' n' ≤ exponent (m + 1) 0 := by
      by_cases hsucc : m + 1 = m'
      · subst m'
        exact (exponent_strictAnti_second (m + 1)).antitone (Nat.zero_le n')
      · have hfirst : m + 1 < m' := lt_of_le_of_ne (Nat.succ_le_iff.mpr hmm') hsucc
        exact (exponent_gt_of_first_lt hfirst).le
    _ < cutoff m := next_exponent_zero_lt_cutoff m
    _ < exponent m n := cutoff_lt_exponent m n
termination_by m' - m

private theorem exponent_strictAnti_lex :
    StrictAnti (fun p : Lex (ℕ × ℕ) ↦ exponent (ofLex p).1 (ofLex p).2) := by
  intro p q hpq
  rw [Prod.Lex.lt_iff] at hpq
  rcases hpq with hfirst | ⟨hfirst, hsecond⟩
  · exact exponent_gt_of_first_lt hfirst
  · change exponent (ofLex p).1 (ofLex p).2 > exponent (ofLex q).1 (ofLex q).2
    rw [hfirst]
    exact exponent_strictAnti_second _ hsecond

/-- The row-column index, followed by one final index for the constant term. -/
abbrev Index := WithTop (Lex (ℕ × ℕ))

/-- The exponent sequence of the concrete Conway normal form. -/
def exponentAtIndex : Index → Surreal.{u}
  | ⊤ => 0
  | (p : Lex (ℕ × ℕ)) => (exponent (ofLex p).1 (ofLex p).2 : ℝ)

private theorem exponent_pos (m n : ℕ) : 0 < exponent m n := by
  rw [exponent_apply]
  positivity

private theorem exponentAtIndex_strictAnti : StrictAnti exponentAtIndex.{u} := by
  intro p q hpq
  induction p using WithTop.recTopCoe with
  | top => exact (not_lt_of_ge le_top hpq).elim
  | coe p =>
      induction q using WithTop.recTopCoe with
      | top =>
          change (0 : Surreal) < (exponent (ofLex p).1 (ofLex p).2 : ℝ)
          exact_mod_cast exponent_pos (ofLex p).1 (ofLex p).2
      | coe q =>
          change ((exponent (ofLex q).1 (ofLex q).2 : ℝ) : Surreal) <
            (exponent (ofLex p).1 (ofLex p).2 : ℝ)
          exact_mod_cast exponent_strictAnti_lex (WithTop.coe_lt_coe.mp hpq)

/-- The coefficient function of the explicit normal form. -/
def coefficient (i : Surreal.{u}) : ℝ :=
  by
    classical
    exact if i ∈ range exponentAtIndex then 1 else 0

private theorem support_coefficient :
    Function.support coefficient.{u} = range exponentAtIndex := by
  classical
  ext i
  simp [Function.support, coefficient]

/-- The displayed coefficient support is small enough for `SurrealHahnSeries` in every
universe. -/
theorem small_support_coefficient :
    Small.{u} (Function.support coefficient.{u}) := by
  rw [support_coefficient]
  infer_instance

/-- The displayed exponents are reverse well-ordered. -/
theorem wellFoundedOn_support_coefficient :
    (Function.support coefficient.{u}).WellFoundedOn (· > ·) := by
  rw [support_coefficient, wellFoundedOn_range]
  convert wellFounded_lt (α := Index) using 1
  ext p q
  exact exponentAtIndex_strictAnti.lt_iff_gt

/-- The explicit Conway normal form with all coefficients equal to one. -/
def normalForm : SurrealHahnSeries.{u} :=
  SurrealHahnSeries.mk coefficient small_support_coefficient
    wellFoundedOn_support_coefficient

@[simp]
theorem normalForm_coeff (i : Surreal.{u}) :
    normalForm.coeff i = coefficient i := by
  rw [normalForm, SurrealHahnSeries.coeff_mk, coefficient]

@[simp]
theorem normalForm_support : normalForm.{u}.support = range exponentAtIndex := by
  rw [normalForm, SurrealHahnSeries.support_mk, support_coefficient]

theorem normalForm_coeff_exponent (m n : ℕ) :
    normalForm.{u}.coeff (exponent m n : ℝ) = 1 := by
  classical
  rw [normalForm_coeff, coefficient, ite_eq_left]
  exact ⟨(↑(toLex (m, n)) : Index), rfl⟩

theorem normalForm_coeff_zero : normalForm.{u}.coeff 0 = 1 := by
  classical
  rw [normalForm_coeff, coefficient, ite_eq_left]
  exact ⟨⊤, rfl⟩

private theorem normalForm_support_nonnegative : normalForm.{u}.support ⊆ Ici 0 := by
  rw [normalForm_support]
  rintro i ⟨p, rfl⟩
  induction p using WithTop.recTopCoe with
  | top => exact le_rfl
  | coe p =>
      rw [mem_Ici]
      change (0 : Surreal) ≤ (exponent (ofLex p).1 (ofLex p).2 : ℝ)
      exact_mod_cast (exponent_pos (ofLex p).1 (ofLex p).2).le

/-- The explicit normal form, regarded as an omnific integer. -/
def degreeTwoOz : Oz.OmnificInteger.{u} :=
  ⟨normalForm, by
    rw [Oz.mem_omnificIntegers]
    exact ⟨normalForm_support_nonnegative, ⟨1, by simpa using normalForm_coeff_zero.symm⟩⟩⟩

@[simp]
theorem degreeTwoOz_val : degreeTwoOz.{u}.1 = normalForm := by
  rfl

/-- The coefficient-doubled comparison element. It has the same support as `degreeTwoOz`, but its
factorisation as `2 * degreeTwoOz` is visible in the definition. -/
def degreeTwoFoil : Oz.OmnificInteger.{u} :=
  2 * degreeTwoOz

@[simp]
theorem degreeTwoFoil_val : degreeTwoFoil.{u}.1 = 2 * normalForm := by
  rfl

/-- Doubling every nonzero coefficient does not change the Conway support. -/
theorem degreeTwoFoil_support :
    degreeTwoFoil.{u}.1.support = degreeTwoOz.1.support := by
  rw [degreeTwoFoil_val, degreeTwoOz_val, two_mul]
  ext i
  simp only [SurrealHahnSeries.mem_support_iff,
    SurrealHahnSeries.coeff_add_apply]
  constructor
  · intro h hzero
    apply h
    rw [hzero, zero_add]
  · intro h hsum
    apply h
    linarith

end ConwayRefinement.Standalone.Oz.DegreeTwoExample
