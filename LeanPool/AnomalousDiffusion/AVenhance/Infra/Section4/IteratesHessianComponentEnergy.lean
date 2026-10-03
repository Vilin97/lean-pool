/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesComponentEnergy

/-! # Iterates Hessian Component Energy

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- An actual Hessian word uses the gradient energy of a one-shorter word. -/
theorem iterate_hessian_word_component_energy_bound {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) (j k : Fin 2) :
    (∫ z in timeCube, (iterateSpatialWord (j :: k :: w) (u z.1) z.2) ^ 2) ≤
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord (k :: w) (u t))) := by
  exact iterate_word_gradient_component_energy_bound hu (k :: w) j

end AVenhance.Infra.Section4
