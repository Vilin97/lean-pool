/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedIntegrability

/-! Component energies are controlled by the actual vector gradient energy. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Every coordinate square lies below the vector square. -/
theorem iterate_component_sq_le_normSq (a : Vec 2) (j : Fin 2) : a j ^ 2 ≤ vecNormSq a := by
  unfold vecNormSq vecDot
  have h := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 2))) =>
    mul_self_nonneg (a i)) (Finset.mem_univ j)
  simpa only [pow_two] using h

/-- The actual word-gradient component inherits the full gradient energy
bound, with integrability proved from the smooth scalar carrier. -/
theorem iterate_word_gradient_component_energy_bound {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) (j : Fin 2) :
    (∫ z in timeCube, spaceGrad (iterateSpatialWord w (u z.1)) z.2 j ^ 2) ≤
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u t))) := by
  have hc := (continuous_apply j).comp_continuousOn
    (iterate_word_gradient_smooth_up_to_initial hu w).continuousOn
  have hi := iterate_timeCube_integrable_of_continuousOn (hc.pow 2)
  have hg := iterate_word_gradient_energy_integrable hu w
  exact integral_mono hi hg (fun z => iterate_component_sq_le_normSq _ j)

end AVenhance.Infra.Section4
