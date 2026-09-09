/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeAlgebra
import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeSupport
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset

/-! Reindexing the literal primary/corrector packet into its actual power coefficients. -/

@[expose] public section


noncomputable section

namespace EulerFiniteGrades

open Finset

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Shift up as an element of `ℕ → V | 0 => 0 | n+1 => truncate M u n`. -/
def shiftUp (M : ℕ) (u : ℕ → V) : ℕ → V
  | 0 => 0
  | n+1 => truncate M u n

/-- Assemble, given by `truncate M u n + shiftUp M c n`. -/
def assemble (M : ℕ) (u c : ℕ → V) (n : ℕ) : V :=
  truncate M u n + shiftUp M c n

theorem evaluate_shiftUp (M : ℕ) (κ : ℝ) (u : ℕ → V) :
    evaluate (M+1) κ (shiftUp M u) = κ • evaluate M κ u := by
  unfold evaluate
  rw [sum_range_succ']
  simp only [shiftUp, smul_zero, add_zero, smul_sum, smul_smul]
  apply sum_congr rfl
  intro i hi
  rw [truncate_of_le M i u (by have h := mem_range.mp hi; omega), pow_succ']

theorem evaluate_assemble (M : ℕ) (κ : ℝ) (u c : ℕ → V) :
    evaluate (M+1) κ (assemble M u c) = evaluate M κ u + κ • evaluate M κ c := by
  change evaluate (M+1) κ (fun n => truncate M u n+shiftUp M c n) = _
  rw [evaluate_add, evaluate_shiftUp, evaluate_truncate_extend M (M+1) (by omega)]

theorem evaluate_from_one (M : ℕ) (κ : ℝ) (u : ℕ → V) (hu : u 0 = 0) :
    evaluate M κ u = ∑ i ∈ range M, κ^(i+1) • u (i+1) := by
  unfold evaluate
  rw [sum_range_succ']
  simp only [hu, smul_zero, add_zero]

/-- Equation (13), with the extra final corrector retained rather than dropped. -/
theorem evaluate_assemble_from_one (M : ℕ) (κ : ℝ) (u c : ℕ → V)
    (hu : u 0 = 0) (hc : c 0 = 0) :
    evaluate (M+1) κ (assemble M u c) =
      ∑ i ∈ range M, (κ^(i+1) • u (i+1) + κ^(i+2) • c (i+1)) := by
  rw [evaluate_assemble, evaluate_from_one M κ u hu, evaluate_from_one M κ c hc,
    smul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  simp only [smul_smul, show i+2=(i+1)+1 by omega, pow_succ']

omit [Module ℝ V] in
theorem assemble_zero (M : ℕ) (u c : ℕ → V) (hu : u 0 = 0) :
    assemble M u c 0 = 0 := by
  simp [assemble, shiftUp, hu]

omit [Module ℝ V] in
theorem assemble_interior (M n : ℕ) (hn : 1 ≤ n) (hMn : n ≤ M) (u c : ℕ → V) :
    assemble M u c n = u n+c (n-1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_eq_add_one, assemble, shiftUp, truncate_of_le M (j+1) u hMn,
    truncate_of_le M j c (by omega), Nat.add_sub_cancel]

omit [Module ℝ V] in
theorem assemble_last (M : ℕ) (u c : ℕ → V) :
    assemble M u c (M+1) = c M := by
  simp only [assemble, shiftUp, truncate_of_gt M (M+1) u (by omega),
    truncate_of_le M M c le_rfl, zero_add]

omit [Module ℝ V] in
theorem assemble_above (M n : ℕ) (hn : M + 1 < n) (u c : ℕ → V) :
    assemble M u c n = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [assemble, shiftUp, truncate_of_gt M (j+1) u (by omega),
    truncate_of_gt M j c (by omega), add_zero]

end EulerFiniteGrades
