/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeAlgebra
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset

/-! Degree bounds and the exact shift caused by a fast derivative. -/

@[expose] public section


noncomputable section

namespace EulerFiniteGrades

open Finset

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

omit [Module ℝ V] in
@[simp] theorem truncate_of_le (M n : ℕ) (u : ℕ → V) (hn : n ≤ M) :
    truncate M u n = u n := ite_eq_left hn

omit [Module ℝ V] in
@[simp] theorem truncate_of_gt (M n : ℕ) (u : ℕ → V) (hn : M < n) :
    truncate M u n = 0 := ite_eq_right (not_le.mpr hn)

theorem evaluate_extend (M N : ℕ) (hMN : M ≤ N) (κ : ℝ) (u : ℕ → V)
    (hu : ∀ n, M < n → u n = 0) : evaluate N κ u = evaluate M κ u := by
  have hz : ∑ n ∈ Ico (M+1) (N+1), κ^n • u n = 0 := by
    apply sum_eq_zero
    intro n hn
    rw [hu n (by have h := (mem_Ico.mp hn).1; omega), smul_zero]
  have h := sum_range_add_sum_Ico (fun n => κ^n • u n) (Nat.add_le_add_right hMN 1)
  rw [hz, add_zero] at h
  exact h.symm

theorem evaluate_truncate (M : ℕ) (κ : ℝ) (u : ℕ → V) :
    evaluate M κ (truncate M u) = evaluate M κ u := by
  apply sum_congr rfl
  intro n hn
  rw [truncate_of_le M n u (by have h := mem_range.mp hn; omega)]

theorem evaluate_truncate_extend (M N : ℕ) (hMN : M ≤ N) (κ : ℝ) (u : ℕ → V) :
    evaluate N κ (truncate M u) = evaluate M κ u :=
  (evaluate_extend M N hMN κ (truncate M u) (fun n hn => truncate_of_gt M n u hn)).trans
    (evaluate_truncate M κ u)

/-- Shift down, given by `truncate M u (n+1)`. -/
def shiftDown (M : ℕ) (u : ℕ → V) (n : ℕ) : V := truncate M u (n+1)

omit [Module ℝ V] in
theorem shiftDown_above (M n : ℕ) (u : ℕ → V) (hn : M ≤ n) : shiftDown M u n = 0 :=
  truncate_of_gt M (n+1) u (by omega)

theorem inverse_evaluate_shiftDown (M : ℕ) (κ : ℝ) (hκ : κ ≠ 0)
    (u : ℕ → V) (hu : u 0 = 0) :
    κ⁻¹ • evaluate M κ u = evaluate M κ (shiftDown M u) := by
  rw [inverse_evaluate M κ hκ u hu, evaluate, sum_range_succ]
  rw [shiftDown_above M M u le_rfl, smul_zero, add_zero]
  apply sum_congr rfl
  intro n hn
  rw [shiftDown, truncate_of_le M (n+1) u (by have h := mem_range.mp hn; omega)]

theorem inverse_evaluate_shiftDown_extend (M N : ℕ) (hMN : M ≤ N)
    (κ : ℝ) (hκ : κ ≠ 0) (u : ℕ → V) (hu : u 0 = 0) :
    κ⁻¹ • evaluate M κ u = evaluate N κ (shiftDown M u) :=
  (inverse_evaluate_shiftDown M κ hκ u hu).trans
    (evaluate_extend M N hMN κ (shiftDown M u) (fun n hn => shiftDown_above M n u hn.le)).symm

end EulerFiniteGrades
