/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixContinuity

/-! # Iterates Flux Pairing Continuity

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual word flux pairing is continuous up to zero when its scalar
 carriers and literal coefficient jets are continuous up to zero. -/
theorem iterate_word_flux_pairing_continuousOn
    {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {u v : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2))
    (hA : ∀ p ∈ iterateSpatialSplits w, ContinuousOn
      (fun z : AmnrSpace => iterateMatrixWord (A z.1) p.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun z : AmnrSpace =>
      vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
        (iterateWordFlux (A z.1) (v z.1) w z.2)) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have ha := (iterate_word_gradient_smooth_up_to_initial hu w).continuousOn
  have hF := iterateSplitFlux_continuousOn_of_jets (iterateSpatialSplits w) hA hv
  have he : (fun z : AmnrSpace => iterateWordFlux (A z.1) (v z.1) w z.2) =
      fun z => iterateSplitFlux (iterateSpatialSplits w) (A z.1) (v z.1) z.2 := by
    funext z
    rfl
  rw [he] at *
  unfold vecDot
  exact continuousOn_finsetSum Finset.univ (fun j _ =>
    ((continuous_apply j).comp_continuousOn ha).mul
      ((continuous_apply j).comp_continuousOn hF))

end AVenhance.Infra.Section4
