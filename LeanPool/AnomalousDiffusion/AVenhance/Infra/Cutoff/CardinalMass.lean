/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.CardinalStep
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Cardinal Mass

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Cutoff

/-- The quadratic mass of the cardinal smooth step on the unit interval. -/
def cardinalMass : ℝ :=
  ∫ x in (0 : ℝ)..1, cardinalStep x * (1 - cardinalStep x)

theorem cardinalMass_lower : 9 / 50 ≤ cardinalMass := by
  let f : ℝ → ℝ := fun x => cardinalStep x * (1 - cardinalStep x)
  have hf : Continuous f := by
    dsimp [f]
    exact (cardinalStep_contDiff.continuous).mul
      ((continuous_const.sub cardinalStep_contDiff.continuous))
  have hI01 : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) 1 :=
    hf.intervalIntegrable (μ := MeasureTheory.volume) _ _
  have hI0a : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) (1 / 8) :=
    hf.intervalIntegrable (μ := MeasureTheory.volume) _ _
  have hIab : IntervalIntegrable f MeasureTheory.volume (1 / 8 : ℝ) (7 / 8) :=
    hf.intervalIntegrable (μ := MeasureTheory.volume) _ _
  have hIb1 : IntervalIntegrable f MeasureTheory.volume (7 / 8 : ℝ) 1 :=
    hf.intervalIntegrable (μ := MeasureTheory.volume) _ _
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals hI0a hIab
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (hI0a.trans hIab) hIb1
  have hleft : 0 ≤ ∫ x in (0 : ℝ)..(1 / 8), f x := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    dsimp [f]
    exact mul_nonneg (step_nonneg _) (sub_nonneg.mpr (step_le_one _))
  have hright : 0 ≤ ∫ x in (7 / 8 : ℝ)..1, f x := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    dsimp [f]
    exact mul_nonneg (step_nonneg _) (sub_nonneg.mpr (step_le_one _))
  have hconst : (9 / 50 : ℝ) = ∫ x in (1 / 8 : ℝ)..(7 / 8), (6 / 25 : ℝ) := by
    simp [intervalIntegral.integral_const]
    ring
  have hmid : (9 / 50 : ℝ) ≤ ∫ x in (1 / 8 : ℝ)..(7 / 8), f x := by
    have hmono :
        (∫ x in (1 / 8 : ℝ)..(7 / 8), (6 / 25 : ℝ)) ≤
          ∫ x in (1 / 8 : ℝ)..(7 / 8), f x := by
      apply intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const hIab
      intro x hx
      dsimp [f]
      have hx' : 1 / 8 ≤ x ∧ x ≤ 7 / 8 := hx
      exact cardinalStep_sq_complement_lower hx'.1 hx'.2
    rw [hconst]
    exact hmono
  change 9 / 50 ≤ ∫ x in (0 : ℝ)..1, f x
  rw [← hsplit2, ← hsplit1]
  linarith

theorem cardinalMass_pos : 0 < cardinalMass := by
  exact lt_of_lt_of_le (by norm_num) cardinalMass_lower

end AVenhance.Infra.Cutoff
