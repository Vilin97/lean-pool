/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-! TODO: Add doc-string. -/

@[expose] public section

open NumberField Module

variable (K : Type*) [Field K] [NumberField K]

theorem pow_finrank_le_abs_discr_of_le_rootDiscr {c : ℝ} (hc : 0 ≤ c)
    (h : c ≤ rootDiscr K) :
    c ^ finrank ℚ K ≤ |(discr K : ℝ)| := by
  calc
    c ^ finrank ℚ K ≤ rootDiscr K ^ finrank ℚ K :=
      pow_le_pow_left₀ hc h _
    _ = |(discr K : ℝ)| := by
      rw [rootDiscr_def, ← Int.cast_abs,
        Real.rpow_inv_natCast_pow (by positivity) finrank_pos.ne']

theorem target_pow_finrank_le_abs_discr
    (h : (8.25 : ℝ) ≤ rootDiscr K) :
    (8.25 : ℝ) ^ finrank ℚ K ≤ |(discr K : ℝ)| :=
  pow_finrank_le_abs_discr_of_le_rootDiscr K (by norm_num) h
