/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.TestFunction.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! TODO: Add doc-string. -/

@[expose] public section

open Set Filter

namespace NumberField.Odlyzko

theorem tartarAmplitude_eq_of_ne {x : ℝ} (hx : x ≠ 0) :
    Tartar.amplitude x = 3 * (Real.sin x - x * Real.cos x) / x ^ 3 := by
  simp [Tartar.amplitude, hx]

theorem tartarAmplitude_continuousAt_of_ne {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt Tartar.amplitude x := by
  let f : ℝ → ℝ := fun y ↦ 3 * (Real.sin y - y * Real.cos y) / y ^ 3
  have hf : ContinuousAt f x := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simp_all
  apply hf.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  simp [f, Tartar.amplitude, hy]

private theorem tartarAmplitude_continuousOn_compl_singleton :
    ContinuousOn Tartar.amplitude ({0}ᶜ : Set ℝ) := by
  intro x hx
  exact (tartarAmplitude_continuousAt_of_ne (by grind)).continuousWithinAt

private theorem tartarAmplitude_measurable : Measurable Tartar.amplitude := by
  exact measurable_of_continuousOn_compl_singleton 0
    tartarAmplitude_continuousOn_compl_singleton

theorem tartarTestFunction_measurable : Measurable Tartar.testFunction := by
  exact tartarAmplitude_measurable.pow_const 2

end NumberField.Odlyzko
