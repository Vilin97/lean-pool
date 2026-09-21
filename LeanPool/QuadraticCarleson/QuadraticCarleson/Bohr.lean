/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.Definitions

/-!
# Elementary phase and Bohr-set lemmas

These are the first checked ingredients for Section 3 of the paper.
-/

open MeasureTheory Set

namespace QuadraticCarleson

@[simp]
theorem norm_phase (s : ℝ) : ‖phase s‖ = 1 := by
  simpa [phase] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * s)

theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem torusNorm_nonneg (x : ℝ) : 0 ≤ torusNorm x := by
  rw [torusNorm]
  exact le_min (Int.fract_nonneg x) (sub_nonneg.mpr (Int.fract_lt_one x).le)

theorem torusNorm_le_half (x : ℝ) : torusNorm x ≤ 1 / 2 := by
  rw [torusNorm]
  rcases le_total (Int.fract x) (1 / 2 : ℝ) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

@[simp]
theorem torusNorm_add_int (x : ℝ) (z : ℤ) : torusNorm (x + z) = torusNorm x := by
  simp [torusNorm, Int.fract_add_intCast]

theorem measurable_torusNorm : Measurable torusNorm := by
  change Measurable (fun x : ℝ => min (Int.fract x) (1 - Int.fract x))
  exact measurable_fract.min (measurable_const.sub measurable_fract)

theorem bohrSet_subset_Ico (k : ℕ) (ρ : ℝ) :
    bohrSet k ρ ⊆ Ico (1 / 4 : ℝ) (1 / 2 : ℝ) := by
  intro x hx
  exact hx.1

theorem measurableSet_bohrSet (k : ℕ) (ρ : ℝ) : MeasurableSet (bohrSet k ρ) := by
  rw [bohrSet]
  exact measurableSet_Ico.inter <|
    measurableSet_le (measurable_torusNorm.comp (measurable_const.mul measurable_id))
      measurable_const

end QuadraticCarleson
