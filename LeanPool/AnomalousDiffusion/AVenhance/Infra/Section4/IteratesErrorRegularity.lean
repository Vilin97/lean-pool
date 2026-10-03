/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocitySmooth

/-! Integrable representatives of actual material errors and their gradients. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- On the positive cell the actual material error is the explicit
 lower velocity sum, whose initial-time smooth representative is proved. -/
theorem iterate_material_error_ae_lower_velocity
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    (fun z : AmnrSpace => iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
      (fun z => v z.1 z.2) z) =ᵐ[volume.restrict timeCube]
      (fun z => iterateVelocitySplit ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty))
        (b z.1) (v z.1) z.2) := by
  have hmono : (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ⊆
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun z hz => ⟨(show 0 < z.1 from hz.1).le, hz.2⟩
  apply (ae_restrict_mem iterate_timeCube_isOpen.measurableSet).mono
  intro z hz
  change iterateWordMaterialError _ w _ (z.1, z.2) = _
  exact iterateWordMaterialError_lower_velocity (hb.mono hmono) (hv.mono hmono) hz.1.1 w z.2

/-- The actual spatial gradient equals the gradient of the lower velocity
 representative almost everywhere on timeCube. -/
theorem iterate_material_error_gradient_ae_lower_velocity
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    (fun z : AmnrSpace => spaceGrad (fun y => iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => v z.1 z.2) (z.1, y)) z.2) =ᵐ[
      volume.restrict timeCube]
      (fun z => spaceGrad (iterateVelocitySplit
        ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty)) (b z.1) (v z.1)) z.2) := by
  have hmono : (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ⊆
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun z hz => ⟨(show 0 < z.1 from hz.1).le, hz.2⟩
  apply (ae_restrict_mem iterate_timeCube_isOpen.measurableSet).mono
  intro z hz
  have he : (fun y => iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
      (fun z => v z.1 z.2) (z.1, y)) =
      iterateVelocitySplit ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty)) (b z.1) (v
          z.1) := by
    funext y
    exact iterateWordMaterialError_lower_velocity (hb.mono hmono) (hv.mono hmono) hz.1.1 w y
  dsimp only
  rw [he]

/-- The actual scalar material-error square is integrable. -/
theorem iterate_material_error_energy_integrable
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    IntegrableOn (fun z : AmnrSpace => iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => v z.1 z.2) z ^ 2) timeCube := by
  have hi := iterate_timeCube_integrable_of_continuousOn
    ((iterateVelocitySplit_continuousOn hb hv
      ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty))).pow 2)
  change IntegrableOn (fun z : AmnrSpace => iterateVelocitySplit
    ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty)) (b z.1) (v z.1) z.2 ^ 2) timeCube
        at hi
  exact hi.congr ((iterate_material_error_ae_lower_velocity hb hv w).fun_comp (fun x => x ^ 2)).symm

/-- The actual material-error gradient square is integrable. -/
theorem iterate_material_error_gradient_energy_integrable
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    IntegrableOn (fun z : AmnrSpace => vecNormSq (spaceGrad (fun y => iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => v z.1 z.2) (z.1, y)) z.2)) timeCube := by
  have hs := iterateVelocitySplit_smooth_up_to_initial hb hv
    ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty))
  have hi := iterate_word_gradient_energy_integrable
    (u := fun t x => iterateVelocitySplit
      ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty)) (b t) (v t) x) hs []
  exact hi.congr ((iterate_material_error_gradient_ae_lower_velocity hb hv w).fun_comp
      vecNormSq).symm

end AVenhance.Infra.Section4
