/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.KmatStepMixedBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureCoefficientBounds

/-! Literal source coefficients through the terminal permitted scale. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Constant controlling the diffusivity ratio in the source estimate. -/
def amnrSourceRatioConstant (β C : ℝ) : ℝ :=
  1 + C + Section3.kappaPrimeEndpointExpratConstant β

theorem amnrSourceRatioConstant_nonneg {β C : ℝ} (I : AVenhance.Ingredients β) (hC : 0 ≤ C) :
    0 ≤ amnrSourceRatioConstant β C := by
  have ht : 0 ≤ Section3.kappaPrimeEndpointExpratConstant β := by
    have hq : 0 ≤ AVenhance.q β := le_trans (by norm_num)
      (AVenhance.Infra.Ingredients.one_lt_q I.one_lt_beta I.beta_lt).le
    unfold Section3.kappaPrimeEndpointExpratConstant
    have hs : 0 ≤ AVenhance.Infra.Ingredients.supergeoConstant β := by
      unfold AVenhance.Infra.Ingredients.supergeoConstant
      positivity
    have hb : 0 ≤ 1 + AVenhance.Infra.Ingredients.supergeoConstant β / 128 := by positivity
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hb _)
  dsimp [amnrSourceRatioConstant]
  positivity

end AVenhance.Infra.Section4
