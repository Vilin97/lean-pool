/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Fully dynamic matching on the line

Common definitions for the formal proof of the hierarchical quantile matching
bound.  All analytic quantities are represented in `ℝ`; finite probability
laws are represented by weighted sums over finite types.
-/

namespace FD1D

noncomputable section

/-- The regularizing parameter used by the policy. -/
def policyA (m : ℕ) : ℕ := 200 * ⌈Real.logb 2 (m + 1)⌉₊

/-- A probability mass function on a finite type, represented without quotienting. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  mass : α → ℝ
  mass_nonneg : ∀ x, 0 ≤ mass x
  sum_mass : ∑ x, mass x = 1

namespace FiniteLaw

variable {α β : Type*} [Fintype α] [Fintype β]

def expect (μ : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ x, μ.mass x * f x

@[simp] theorem expect_const (μ : FiniteLaw α) (c : ℝ) :
    μ.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, μ.sum_mass]

theorem expect_nonneg (μ : FiniteLaw α) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ μ.expect f := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.mass_nonneg x) (hf x)

theorem expect_mono (μ : FiniteLaw α) {f g : α → ℝ}
    (hfg : ∀ x, f x ≤ g x) : μ.expect f ≤ μ.expect g := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (hfg x) (μ.mass_nonneg x)

end FiniteLaw

end

end FD1D
