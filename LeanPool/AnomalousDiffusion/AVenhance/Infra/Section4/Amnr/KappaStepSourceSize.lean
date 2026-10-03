/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.LRecurseTop
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureMaterialInduction

/-! The actual diffusivity step controls Kmat also at the terminal scale. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- The exact diffusivity recursion, including the terminal step. -/
theorem amnr_kappa_previous_eq_step {β κ : ℝ} (I : AVenhance.Ingredients β)
    {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) :
    I.kappaAt κ (m - 1) (M - (m - 1)) =
      I.KhomScalar (I.kappaAt κ m (M - m)) m := by
  have hdepth : M - (m - 1) = (M - m) + 1 := by omega
  rw [hdepth, AVenhance.Ingredients.kappaAt, show m - 1 + 1 = m by omega]

/-- Smallness in the proved one-step averaging error yields a uniform
size comparison without an invalid upper diffusivity-recursion bound at the terminal index. -/
theorem amnr_kappa_step_size_of_averaging {β C₀ κ : ℝ}
    (I : AVenhance.Ingredients β) (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀)
    {m : ℕ} (hm : 1 ≤ m) (hκ : 0 < κ)
    (hsmall : Section3.lAmtOneStepConstant β C₀ *
      (AVenhance.epsilon β I.Λ m ^ 2 / (κ * AVenhance.tau β I.Λ m) +
        AVenhance.epsilon β I.Λ (m - 1) ^ AVenhance.delta β) ≤ 9 / 160) :
    κ + AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 4 / κ ≤
      (160 / 9) * I.KhomScalar κ m := by
  have he := Section3.KhomScalar_one_step_error_unconditional I hz hh hm hκ
  have hS : 0 ≤ AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 4 / κ := by positivity
  have herr := mul_le_mul_of_nonneg_right hsmall hS
  have hlower := (abs_le.mp he).1
  nlinarith only [hlower, herr, hκ.le]

end AVenhance.Infra.Section4
