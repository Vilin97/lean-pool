/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.V5.Parameters

/-!
# Abstract resource accounting for the v5 hierarchical policy

This module formalizes the manuscript's real-arithmetic accounting model.
One primitive arithmetic operation, comparison, or constant-time tree access
costs one unit. A period visits one root-to-leaf path. Memory consists of one
word for each labeled supply and a constant number of words per tree leaf.

These are mathematical accounting functions, not runtime measurements of
Lean's noncomputable definitions.
-/

namespace FD1D.V5

noncomputable section

open Filter Asymptotics

/-- Abstract primitive-operation count for one period. -/
def hierarchicalOperationCount (m : ℕ) : ℕ :=
  20 * (treeDepth m + 1)

/-- Abstract memory count for labeled supplies and complete-tree data. -/
def hierarchicalMemoryCount (m : ℕ) : ℕ :=
  m + 4 * leafCount m

/-- Operations are bounded by a constant times the base-two ceiling logarithm. -/
theorem hierarchicalOperationCount_le_clog
    {m : ℕ} (hm : 1 ≤ m) :
    hierarchicalOperationCount m ≤
      20 * (Nat.clog 2 (m + 1) + 1) := by
  unfold hierarchicalOperationCount
  exact Nat.mul_le_mul_left 20
    (Nat.add_le_add_right (treeDepth_le_clog hm) 1)

/-- The abstract memory budget is at most `5m` words. -/
theorem hierarchicalMemoryCount_le_five_mul
    {m : ℕ} (hm : 1 ≤ m) :
    hierarchicalMemoryCount m ≤ 5 * m := by
  have hleaf : leafCount m ≤ m :=
    (leafCount_le_depthTarget m).trans (depthTarget_le hm)
  unfold hierarchicalMemoryCount
  omega

/-- Explicit natural-log bound for the real-valued operation count. -/
theorem hierarchicalOperationCount_cast_le_log
    {m : ℕ} (hm : 2 ≤ m) :
    (hierarchicalOperationCount m : ℝ) ≤
      (100 / Real.log 2) * Real.log (m : ℝ) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogMono : Real.log 2 ≤ Real.log (m : ℝ) := by
    apply Real.log_le_log
    · norm_num
    · exact_mod_cast hm
  have hdepth :
      (20 : ℝ) * treeDepth m ≤
        (80 / Real.log 2) * Real.log (m : ℝ) := by
    have hscaled :
        (20 : ℝ) * treeDepth m ≤ (parameterA m : ℝ) / 100 := by
      have hparameter :=
        parameterA_cast_ge_treeDepth (show 1 ≤ m by omega)
      nlinarith
    have hparameterLogb := parameterA_cast_le_logb hm
    have hparameterLog :
        (parameterA m : ℝ) ≤
          (8000 / Real.log 2) * Real.log (m : ℝ) := by
      calc
        (parameterA m : ℝ) ≤
            8000 * (Real.log (m : ℝ) / Real.log 2) := by
          simpa [Real.logb] using hparameterLogb
        _ = (8000 / Real.log 2) * Real.log (m : ℝ) := by ring
    calc
      (20 : ℝ) * treeDepth m ≤ (parameterA m : ℝ) / 100 := hscaled
      _ ≤ ((8000 / Real.log 2) * Real.log (m : ℝ)) / 100 :=
        div_le_div_of_nonneg_right hparameterLog (by norm_num)
      _ = (80 / Real.log 2) * Real.log (m : ℝ) := by ring
  have hroot :
      (20 : ℝ) ≤ (20 / Real.log 2) * Real.log (m : ℝ) := by
    calc
      (20 : ℝ) = (20 / Real.log 2) * Real.log 2 := by
        field_simp
      _ ≤ (20 / Real.log 2) * Real.log (m : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlogMono
          (div_nonneg (by norm_num) hlogTwo.le)
  rw [hierarchicalOperationCount, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_add, Nat.cast_one]
  calc
    (20 : ℝ) * ((treeDepth m : ℝ) + 1) =
        (20 : ℝ) * treeDepth m + 20 := by ring
    _ ≤ (80 / Real.log 2) * Real.log (m : ℝ) +
        (20 / Real.log 2) * Real.log (m : ℝ) :=
      add_le_add hdepth hroot
    _ = (100 / Real.log 2) * Real.log (m : ℝ) := by ring

/-- Per-period operations are `O(log m)` in the accounting model. -/
theorem hierarchicalOperationCount_isBigO_log :
    (fun m : ℕ => (hierarchicalOperationCount m : ℝ)) =O[atTop]
      (fun m : ℕ => Real.log (m : ℝ)) := by
  refine IsBigO.of_bound (100 / Real.log 2) ?_
  filter_upwards [eventually_ge_atTop 2] with m hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega)))]
  exact hierarchicalOperationCount_cast_le_log hm

/-- Memory is `O(m)` in the accounting model. -/
theorem hierarchicalMemoryCount_isBigO_linear :
    (fun m : ℕ => (hierarchicalMemoryCount m : ℝ)) =O[atTop]
      (fun m : ℕ => (m : ℝ)) := by
  refine IsBigO.of_bound 5 ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast hierarchicalMemoryCount_le_five_mul hm

/-- Public bundle of the manuscript's operation and memory guarantees. -/
structure HierarchicalResourceGuarantees : Prop where
  operationsExplicit :
    ∀ {m : ℕ}, 2 ≤ m →
      (hierarchicalOperationCount m : ℝ) ≤
        (100 / Real.log 2) * Real.log (m : ℝ)
  memoryExplicit :
    ∀ {m : ℕ}, 1 ≤ m → hierarchicalMemoryCount m ≤ 5 * m
  operationsAsymptotic :
    (fun m : ℕ => (hierarchicalOperationCount m : ℝ)) =O[atTop]
      (fun m : ℕ => Real.log (m : ℝ))
  memoryAsymptotic :
    (fun m : ℕ => (hierarchicalMemoryCount m : ℝ)) =O[atTop]
      (fun m : ℕ => (m : ℝ))

theorem hierarchicalPolicy_resourceGuarantees :
    HierarchicalResourceGuarantees where
  operationsExplicit := hierarchicalOperationCount_cast_le_log
  memoryExplicit := hierarchicalMemoryCount_le_five_mul
  operationsAsymptotic := hierarchicalOperationCount_isBigO_log
  memoryAsymptotic := hierarchicalMemoryCount_isBigO_linear

end

end FD1D.V5
