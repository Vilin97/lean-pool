/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Markov

/-! # Expectations -/

namespace FD1D

noncomputable section

open scoped BigOperators

namespace FiniteLaw

variable {α : Type*} [Fintype α]

theorem expect_add (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun x => f x + g x) = μ.expect f + μ.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun x => f x - g x) = μ.expect f - μ.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_const_mul (μ : FiniteLaw α) (c : ℝ) (f : α → ℝ) :
    μ.expect (fun x => c * f x) = c * μ.expect f := by
  rw [expect, expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem expect_mul_const (μ : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    μ.expect (fun x => f x * c) = μ.expect f * c := by
  rw [expect, expect, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

end FiniteLaw

namespace FiniteKernel

variable {α : Type*} [Fintype α]

/-- The expectation after one kernel step is the expectation of the
conditional next-state expectation. -/
theorem expect_step (K : FiniteKernel α) (μ : FiniteLaw α) (f : α → ℝ) :
    (K.step μ).expect f =
      μ.expect (fun x => ∑ y, K x y * f y) := by
  rw [FiniteLaw.expect, FiniteLaw.expect]
  simp_rw [mass_step, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Expected one-step change, in conditional-drift form. -/
theorem expect_step_sub (K : FiniteKernel α) (μ : FiniteLaw α)
    (f : α → ℝ) :
    (K.step μ).expect f - μ.expect f =
      μ.expect (fun x => ∑ y, K x y * (f y - f x)) := by
  rw [K.expect_step μ f, ← μ.expect_sub]
  apply congrArg μ.expect
  funext x
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, K.sum_trans, one_mul]

theorem expect_iterate_succ (K : FiniteKernel α) (μ : FiniteLaw α)
    (n : ℕ) (f : α → ℝ) :
    (K.iterate (n + 1) μ).expect f - (K.iterate n μ).expect f =
      (K.iterate n μ).expect
        (fun x => ∑ y, K x y * (f y - f x)) := by
  rw [iterate_succ]
  exact K.expect_step_sub (K.iterate n μ) f

theorem IsStationary.expect_eq {K : FiniteKernel α} {μ : FiniteLaw α}
    (hμ : K.IsStationary μ) (f : α → ℝ) :
    (K.step μ).expect f = μ.expect f := by
  rw [hμ]

end FiniteKernel

end

end FD1D
