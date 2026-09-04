/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.ConditionalProductKernel
import Mathlib.MeasureTheory.Measure.Real

/-!
# Averaging conditional probability bounds

This file records the elementary final step used after the latent
two-point decomposition: an almost-everywhere event bound for the
conditional Markov kernel survives averaging over a probability law.
-/

open MeasureTheory ProbabilityTheory

namespace Feige

noncomputable section

/-- An almost-everywhere real-valued probability bound for the fibres of a
Markov kernel is inherited by the mixture measure. -/
theorem measureReal_bind_apply_le
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (κ : Kernel A B) [IsMarkovKernel κ]
    (ν : Measure A) [IsProbabilityMeasure ν]
    {s : Set B} (hs : MeasurableSet s)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ᵐ a ∂ν, (κ a).real s ≤ c) :
    (κ ∘ₘ ν).real s ≤ c := by
  rw [measureReal_def, Measure.bind_apply hs κ.aemeasurable]
  have hfibres :
      ∀ᵐ a ∂ν, κ a s ≤ ENNReal.ofReal c := by
    filter_upwards [hc] with a ha
    rw [← ofReal_measureReal (μ := κ a) (s := s)]
    exact ENNReal.ofReal_le_ofReal ha
  have hint :
      (∫⁻ a, κ a s ∂ν) ≤ ∫⁻ _a, ENNReal.ofReal c ∂ν :=
    lintegral_mono_ae hfibres
  rw [lintegral_const, measure_univ, mul_one] at hint
  calc
    (∫⁻ a, κ a s ∂ν).toReal ≤ (ENNReal.ofReal c).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hint
    _ = c := ENNReal.toReal_ofReal hc0

end

end Feige
