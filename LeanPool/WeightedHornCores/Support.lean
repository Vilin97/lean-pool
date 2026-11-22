/-
Copyright (c) 2026 Weighted Horn Cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weighted Horn Cores contributors
-/
module

public import LeanPool.WeightedHornCores.CoreBound

/-!
# Removing zero-weight clauses

Restricting a nonnegatively weighted formula to its positive support preserves its total
weight, its branching weight, and the weight it loses on each assignment.
-/

@[expose] public section

namespace WeightedHornCores

variable {α : Type*}

/-- The clauses of a formula with strictly positive weight. -/
noncomputable def positiveSupport (F : Finset (Clause α)) (w : Clause α → ℝ) : Finset (Clause α) :=
  F.filter fun c => 0 < w c

variable {F : Finset (Clause α)} {w : Clause α → ℝ}

/-- Membership in the positive support records both membership and positive weight. -/
@[simp] theorem mem_positiveSupport {c : Clause α} :
    c ∈ positiveSupport F w ↔ c ∈ F ∧ 0 < w c := Finset.mem_filter

private theorem sum_positiveSupport_of_zero (hw : ∀ c ∈ F, 0 ≤ w c) (g : Clause α → ℝ)
    (hg : ∀ c ∈ F, w c = 0 → g c = 0) :
    (∑ c ∈ positiveSupport F w, g c) = ∑ c ∈ F, g c := by
  apply Finset.sum_subset (show positiveSupport F w ⊆ F from
    fun _ hc => (mem_positiveSupport.mp hc).1)
  intro c hc hnot
  exact hg c hc (le_antisymm (le_of_not_gt fun hp => hnot (mem_positiveSupport.mpr ⟨hc, hp⟩))
    (hw c hc))

/-- Removing zero-weight clauses preserves total weight. -/
theorem sum_positiveSupport (hw : ∀ c ∈ F, 0 ≤ w c) :
    (∑ c ∈ positiveSupport F w, w c) = ∑ c ∈ F, w c :=
  sum_positiveSupport_of_zero hw w fun _ _ h => h

/-- Removing zero-weight clauses preserves the loss on every assignment. -/
theorem violationWeight_positiveSupport (hw : ∀ c ∈ F, 0 ≤ w c) (s : Set α) :
    violationWeight (positiveSupport F w) w s = violationWeight F w s := by
  unfold violationWeight
  apply sum_positiveSupport_of_zero hw
  intro c _ hz
  simp [hz]

/-- Removing zero-weight clauses preserves the branching weight. -/
theorem branchingWeight_positiveSupport (hw : ∀ c ∈ F, 0 ≤ w c) :
    branchingWeight (positiveSupport F w) w = branchingWeight F w := by
  unfold branchingWeight
  apply sum_positiveSupport_of_zero hw
  intro c _ hz
  simp [hz]

/-- The loss on a single assignment cannot exceed the total weight. -/
theorem violationWeight_le_total (hw : ∀ c ∈ F, 0 ≤ w c) (s : Set α) :
    violationWeight F w s ≤ ∑ c ∈ F, w c := by
  unfold violationWeight
  apply Finset.sum_le_sum
  intro c hc
  split <;> first | exact le_rfl | exact hw c hc

/-- Branching rules have nonnegative total weight when each clause has nonnegative weight. -/
theorem branchingWeight_nonneg (hw : ∀ c ∈ F, 0 ≤ w c) : 0 ≤ branchingWeight F w := by
  unfold branchingWeight
  apply Finset.sum_nonneg
  intro c hc
  split <;> first | exact hw c hc | exact le_rfl

end WeightedHornCores
