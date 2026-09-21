/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.WeightedLayerCake

/-! # Local Weighted Tail -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

/-- The defining density of `sqWeightedMeasure`, on sets measurable up to a
`μ`-null set. -/
theorem sqWeightedMeasure_apply₀ {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} (f : α → E) {s : Set α}
    (hs : NullMeasurableSet s μ) :
    sqWeightedMeasure f μ s =
      ∫⁻ x in s, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)) ∂μ := by
  exact MeasureTheory.withDensity_apply₀ _ hs

private theorem sq_le_tail_split {E : Type*} [NormedAddCommGroup E]
    {f v : E} {r a : ℝ} (hr : 2 < r) (ha : 0 < a) :
    (if a < ‖f‖ then ‖f‖ ^ (2 : ℕ) else 0) ≤
      2 * (a / 2) ^ (2 - r) * ‖v‖ ^ r *
          (if a / 2 < ‖v‖ then 1 else 0) +
        6 * ‖f - v‖ ^ (2 : ℕ) := by
  have htri : ‖f‖ ≤ ‖v‖ + ‖f - v‖ := by
    calc
      ‖f‖ = ‖v + (f - v)‖ := by congr 1; abel
      _ ≤ ‖v‖ + ‖f - v‖ := norm_add_le _ _
  by_cases hf : a < ‖f‖
  · rw [if_pos hf]
    by_cases hv : a / 2 < ‖v‖
    · rw [if_pos hv]
      have hhalf : 0 < a / 2 := by linarith
      have hv_pos : 0 < ‖v‖ := hhalf.trans hv
      have hpow : ‖v‖ ^ (2 : ℝ) ≤ (a / 2) ^ (2 - r) * ‖v‖ ^ r := by
        have hneg : 2 - r ≤ 0 := by linarith
        have hmono : ‖v‖ ^ (2 - r) ≤ (a / 2) ^ (2 - r) :=
          Real.rpow_le_rpow_of_nonpos hhalf hv.le hneg
        have hvr_nonneg : 0 ≤ ‖v‖ ^ r := Real.rpow_nonneg (norm_nonneg _) _
        calc
          ‖v‖ ^ (2 : ℝ) = ‖v‖ ^ (2 - r) * ‖v‖ ^ r := by
            rw [← Real.rpow_add hv_pos]
            congr 1
            ring
          _ ≤ (a / 2) ^ (2 - r) * ‖v‖ ^ r :=
            mul_le_mul_of_nonneg_right hmono hvr_nonneg
      have hsq : ‖f‖ ^ (2 : ℕ) ≤
          2 * ‖v‖ ^ (2 : ℝ) + 2 * ‖f - v‖ ^ (2 : ℕ) := by
        have hsq_base : ‖f‖ ^ (2 : ℕ) ≤ (‖v‖ + ‖f - v‖) ^ (2 : ℕ) :=
          (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htri
        norm_num [Real.rpow_two]
        nlinarith [sq_nonneg (‖v‖ - ‖f - v‖)]
      nlinarith [hpow, sq_nonneg (‖f - v‖)]
    · rw [if_neg hv]
      have hv_le : ‖v‖ ≤ a / 2 := le_of_not_gt hv
      have hdiff : ‖f‖ / 2 < ‖f - v‖ := by linarith
      nlinarith [sq_nonneg (‖f - v‖)]
  · rw [if_neg hf]
    positivity

theorem sqWeightedMeasure_tail_le_comparison {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {B : Set α} (hB : MeasurableSet B)
    {f v : α → E} (hf : AEStronglyMeasurable f μ) (hv : AEStronglyMeasurable v μ)
    {r a : ℝ} (hr : 2 < r) (ha : 0 < a) :
    sqWeightedMeasure f μ ({x | a < ‖f x‖} ∩ B) ≤
      2 * ENNReal.ofReal ((a / 2) ^ (2 - r)) *
          (∫⁻ x in B, ENNReal.ofReal (‖v x‖ ^ r) ∂μ) +
        6 * (∫⁻ x in B, ENNReal.ofReal (‖f x - v x‖ ^ (2 : ℕ)) ∂μ) := by
  let T : Set α := {x | a < ‖f x‖}
  have hT : NullMeasurableSet T μ := by
    simpa [T] using aestronglyMeasurable_const.nullMeasurableSet_lt hf.norm
  have hTB : NullMeasurableSet (T ∩ B) μ := hT.inter hB.nullMeasurableSet
  let V : α → ℝ≥0∞ := fun x => ENNReal.ofReal (‖v x‖ ^ r)
  let D : α → ℝ≥0∞ := fun x => ENNReal.ofReal (‖f x - v x‖ ^ (2 : ℕ))
  let c : ℝ≥0∞ := ENNReal.ofReal ((a / 2) ^ (2 - r))
  have hV_meas : AEMeasurable V μ :=
    (hv.norm.aemeasurable.pow aemeasurable_const).ennreal_ofReal
  have hD_meas : AEMeasurable D μ :=
    ((hf.sub hv).norm.aemeasurable.pow aemeasurable_const).ennreal_ofReal
  have hpoint : (T ∩ B).indicator (fun x => ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) ≤
      B.indicator (fun x => 2 * c * V x + 6 * D x) := by
    intro x
    by_cases hxB : x ∈ B
    · rw [Set.indicator_of_mem hxB]
      by_cases hxT : x ∈ T
      · rw [Set.indicator_of_mem (show x ∈ T ∩ B from ⟨hxT, hxB⟩)]
        have hs := sq_le_tail_split (f := f x) (v := v x) hr ha
        have hreal : ‖f x‖ ^ (2 : ℕ) ≤
            2 * ((a / 2) ^ (2 - r)) * ‖v x‖ ^ r +
              6 * ‖f x - v x‖ ^ (2 : ℕ) := by
          have hs' : ‖f x‖ ^ (2 : ℕ) ≤
              2 * ((a / 2) ^ (2 - r)) * ‖v x‖ ^ r *
                  (if a / 2 < ‖v x‖ then 1 else 0) +
                6 * ‖f x - v x‖ ^ (2 : ℕ) := by
            have hfx : a < ‖f x‖ := by simpa [T] using hxT
            simpa only [if_pos hfx] using hs
          by_cases hv' : a / 2 < ‖v x‖
          · simpa [hv'] using hs'
          · rw [if_neg hv'] at hs'
            have hvpow : 0 ≤ 2 * ((a / 2) ^ (2 - r)) * ‖v x‖ ^ r := by
              positivity
            linarith
        calc
          ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)) ≤
              ENNReal.ofReal
                (2 * ((a / 2) ^ (2 - r)) * ‖v x‖ ^ r +
                  6 * ‖f x - v x‖ ^ (2 : ℕ)) := ENNReal.ofReal_le_ofReal hreal
          _ = 2 * c * V x + 6 * D x := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity)]
            norm_num [c, V, D]
      · rw [Set.indicator_of_notMem (fun h => hxT h.1)]
        positivity
    · rw [Set.indicator_of_notMem hxB]
      by_cases hxT : x ∈ T
      · rw [Set.indicator_of_notMem (fun h => hxB h.2)]
      · rw [Set.indicator_of_notMem (fun h => hxB h.2)]
  rw [sqWeightedMeasure_apply₀ f hTB]
  calc
    ∫⁻ x in T ∩ B, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)) ∂μ =
        ∫⁻ x, (T ∩ B).indicator (fun x => ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) x ∂μ :=
      (MeasureTheory.lintegral_indicator₀ hTB _).symm
    _ ≤ ∫⁻ x, B.indicator (fun x => 2 * c * V x + 6 * D x) x ∂μ := by
      apply lintegral_mono
      exact hpoint
    _ = ∫⁻ x in B, 2 * c * V x + 6 * D x ∂μ :=
      MeasureTheory.lintegral_indicator hB _
    _ = 2 * c * (∫⁻ x in B, V x ∂μ) + 6 * (∫⁻ x in B, D x ∂μ) := by
      rw [MeasureTheory.lintegral_add_left'
        ((hV_meas.const_mul (2 * c)).restrict), MeasureTheory.lintegral_const_mul''
        6 (hD_meas.restrict), MeasureTheory.lintegral_const_mul'' (2 * c) hV_meas.restrict]

end CubeCalderonZygmund

end

end Homogenization
