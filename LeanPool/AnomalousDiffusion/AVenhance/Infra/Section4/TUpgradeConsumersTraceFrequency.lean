/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersProfile

/-! # TUpgrade Consumers Trace Frequency

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

theorem TUpgradeConsumersTraceFrequency.iterateSpatialWord_eq_classicalWordDerivative
    (w : List (Fin 2)) (f : Vec 2 → ℝ) :
    iterateSpatialWord w f = classicalWordDerivative w f := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [iterateSpatialWord, classicalWordDerivative,
    Classical.classicalWordDerivative, ih]

end AVenhance.Infra.Section4
