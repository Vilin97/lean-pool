/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.KStatistic
import LeanPool.Feige.TransferProbability

/-!
# The nonnegative-real exponential law

This module isolates the elementary push-forward identity relating the
`NNReal` model of a unit exponential to Mathlib's real-valued exponential
measure.
-/

open Set MeasureTheory ProbabilityTheory

namespace Feige

theorem map_nnexpMeasure_coe :
    Measure.map (fun x : NNReal ↦ (x : ℝ)) nnexpMeasure =
      expMeasure 1 := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  rw [nnexpMeasure, Measure.map_map NNReal.continuous_coe.measurable
    measurable_real_toNNReal]
  have hneg : expMeasure 1 (Iio (0 : ℝ)) = 0 := by
    rw [← compl_Ici,
      measure_compl measurableSet_Ici (measure_ne_top _ _)]
    rw [ExponentialTransfer.expMeasure_one_Ici le_rfl]
    simp
  have hae : ∀ᵐ x ∂expMeasure 1, 0 ≤ x := by
    rw [ae_iff]
    rw [show {a : ℝ | ¬ 0 ≤ a} = Iio 0 by ext; simp]
    exact hneg
  calc
    Measure.map (NNReal.toReal ∘ Real.toNNReal) (expMeasure 1) =
        Measure.map id (expMeasure 1) := by
      apply Measure.map_congr
      filter_upwards [hae] with x hx
      simp [Real.toNNReal_of_nonneg hx]
    _ = expMeasure 1 := Measure.map_id

end Feige
