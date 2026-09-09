/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanLocalL2Energy

@[expose] public section

/-! Integrating the source's different lower bounds inside and outside the core. -/

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerLiftedPressure
open scoped NNReal

theorem localized_coefficient_lower (M : Space → Space →L[ℝ] Space)
    (hM : AEStronglyMeasurable M volume) (C : ℝ≥0) (hC : ∀ x, ‖M x‖ ≤ C)
    (s : Set Space) (hs : MeasurableSet s) (Be Bc : ℝ) (hBe : 0 ≤ Be)
    (hext : ∀ x, x ∉ s → ∀ v : Space, -Be * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
    (hcore : ∀ x, x ∈ s → ∀ v : Space, -Bc * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
    (z : L2) :
    -Be * ‖z‖^2 - Bc * localL2Energy s z ≤
      ⟪coefficientOperator M hM C hC z, z⟫_ℝ := by
  have hi := integrable_norm_sq_L2 z
  have his := hi.indicator hs
  have hieq : (∫ x, -Be * ‖z x‖^2 - Bc * s.indicator (fun y => ‖z y‖^2) x) =
      -Be * ‖z‖^2 - Bc * localL2Energy s z := by
    rw [integral_sub (hi.const_mul (-Be)) (his.const_mul Bc), integral_const_mul,
      integral_const_mul, integral_indicator hs, integral_norm_sq_L2]
    rfl
  rw [← hieq, MeasureTheory.L2.inner_def]
  apply integral_mono_ae ((hi.const_mul (-Be)).sub (his.const_mul Bc))
    (MeasureTheory.L2.integrable_inner (coefficientOperator M hM C hC z) z)
  filter_upwards [coefficientOperator_ae M hM C hC z] with x hx
  change -Be * ‖z x‖^2 - Bc * s.indicator (fun y => ‖z y‖^2) x ≤
    ⟪(coefficientOperator M hM C hC z) x, z x⟫_ℝ
  rw [hx]
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs]
    have H := hcore x hxs (z x)
    nlinarith only [H, mul_nonneg hBe (sq_nonneg ‖z x‖)]
  · rw [Set.indicator_of_notMem hxs, mul_zero, sub_zero]
    exact hext x hxs (z x)

end EulerMeanHarmonic
