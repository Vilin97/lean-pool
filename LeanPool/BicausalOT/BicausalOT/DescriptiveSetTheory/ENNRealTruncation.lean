/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
module

public import Mathlib.Basic.ENNReal.Operations

/-!
# Truncations of extended nonnegative real numbers

The kernel integration and lower semicontinuity arguments use the same truncation limit.
-/

public section

open scoped ENNReal

/-- Every extended nonnegative real is the supremum of its natural-number truncations. -/
theorem ennreal_iSup_min_natCast (a : ℝ≥0∞) : ⨆ n : ℕ, min a (n : ℝ≥0∞) = a := by
  refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
  rcases eq_or_ne a ∞ with rfl | ha
  · have hmin : ∀ n : ℕ, min (∞ : ℝ≥0∞) (n : ℝ≥0∞) = (n : ℝ≥0∞) :=
      fun n => min_eq_right le_top
    calc (∞ : ℝ≥0∞) = ⨆ n : ℕ, (n : ℝ≥0∞) := ENNReal.iSup_natCast.symm
      _ ≤ ⨆ n : ℕ, min (∞ : ℝ≥0∞) (n : ℝ≥0∞) :=
          iSup_mono fun n => (hmin n).symm.le
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
    exact le_iSup_of_le n (by simp [min_eq_left hn.le])
