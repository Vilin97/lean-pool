/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

/-! TODO: Add doc-string. -/

@[expose] public section

namespace NumberField.Odlyzko

/-- An odlyzko scale used in the Odlyzko-bound argument. -/
noncomputable def odlyzkoScale : ℝ :=
  41 / 50

theorem odlyzkoScale_pos : 0 < odlyzkoScale := by
  norm_num [odlyzkoScale]

theorem degreeCorrection_le_degreeEighteen {n : ℕ} (hn : 18 ≤ n) :
    12 * Real.pi / (5 * n * odlyzkoScale) ≤ 20 * Real.pi / 123 := by
  have : (18 : ℝ) ≤ n := by simp_all
  calc
    12 * Real.pi / (5 * n * odlyzkoScale)
        ≤ 12 * Real.pi / (5 * 18 * odlyzkoScale) := by
          gcongr
          all_goals norm_num [odlyzkoScale]
    _ = 20 * Real.pi / 123 := by
      rw [odlyzkoScale]
      ring

end NumberField.Odlyzko
