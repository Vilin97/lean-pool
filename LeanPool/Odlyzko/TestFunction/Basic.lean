/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.Lattice

/-! TODO: Add doc-string. -/

@[expose] public section

namespace NumberField.Odlyzko

/-- A weight used in the Odlyzko-bound argument. -/
noncomputable def Tartar.weight (x : ℝ) : ℝ :=
  max (1 - x ^ 2) 0

/-- An amplitude used in the Odlyzko-bound argument. -/
noncomputable def Tartar.amplitude (x : ℝ) : ℝ :=
  if x = 0 then 1 else 3 * (Real.sin x - x * Real.cos x) / x ^ 3

/-- A test function used in the Odlyzko-bound argument. -/
noncomputable def Tartar.testFunction (x : ℝ) : ℝ :=
  Tartar.amplitude x ^ 2

@[simp]
theorem tartarAmplitude_zero : Tartar.amplitude 0 = 1 := by
  simp [Tartar.amplitude]

@[simp]
theorem tartarTestFunction_zero : Tartar.testFunction 0 = 1 := by
  simp [Tartar.testFunction]

theorem tartarWeight_nonneg (x : ℝ) : 0 ≤ Tartar.weight x :=
  le_max_right _ _

theorem tartarTestFunction_nonneg (x : ℝ) : 0 ≤ Tartar.testFunction x := by
  exact sq_nonneg _

theorem tartarWeight_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) :
    Tartar.weight x = 0 := by
  rw [Tartar.weight, max_eq_right]
  simp_all

theorem tartarWeight_eq_one_sub_sq_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    Tartar.weight x = 1 - x ^ 2 := by
  rw [Tartar.weight, max_eq_left]
  simp_all

theorem tartarWeight_neg (x : ℝ) : Tartar.weight (-x) = Tartar.weight x := by
  simp [Tartar.weight]

theorem tartarAmplitude_neg (x : ℝ) : Tartar.amplitude (-x) = Tartar.amplitude x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [Tartar.amplitude, neg_eq_zero, hx, ite_false, Real.sin_neg, Real.cos_neg]
    ring

theorem tartarTestFunction_neg (x : ℝ) :
    Tartar.testFunction (-x) = Tartar.testFunction x := by
  simp [Tartar.testFunction, tartarAmplitude_neg]

theorem tartarWeight_continuous : Continuous Tartar.weight := by
  unfold Tartar.weight
  fun_prop

end NumberField.Odlyzko
