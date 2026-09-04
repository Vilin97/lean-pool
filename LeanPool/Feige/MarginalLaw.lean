/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.MeanOneReduction
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Elementary facts about one-dimensional marginal laws

These lemmas package the three facts needed when replacing independent
random variables by their product of marginal distributions: integrability,
the first moment, and nonnegative support.
-/

open MeasureTheory Set

namespace Feige

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integrable_id_map
    {X : Ω → ℝ} (hXmeas : Measurable X) (hXint : Integrable X μ) :
    Integrable (fun x : ℝ ↦ x) (μ.map X) := by
  rw [integrable_map_measure (by fun_prop) hXmeas.aemeasurable]
  simpa [Function.comp_def] using hXint

theorem integral_id_map
    {X : Ω → ℝ} (hXmeas : Measurable X) :
    (∫ x : ℝ, x ∂μ.map X) = ∫ ω, X ω ∂μ := by
  rw [integral_map hXmeas.aemeasurable (by fun_prop)]

theorem map_apply_Iio_zero_of_nonnegative
    {X : Ω → ℝ} (hXmeas : Measurable X)
    (hXnonneg : ∀ ω, 0 ≤ X ω) :
    (μ.map X) (Iio 0) = 0 := by
  rw [Measure.map_apply hXmeas measurableSet_Iio]
  have hpre : X ⁻¹' Iio 0 = ∅ := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false]
    exact not_lt_of_ge (hXnonneg ω)
  rw [hpre, measure_empty]

end

end Feige
