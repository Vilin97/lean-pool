/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# LeanPool.RlTheoryInLean.MeasureTheory.MeasurableSpace.Constructions
-/

lemma Measurable.of_uncurry
  {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {f : α → β → γ} (h : Measurable (Function.uncurry f))
  : Measurable f := by
    apply measurable_pi_iff.mpr
    intro a
    apply Measurable.of_uncurry_right h
