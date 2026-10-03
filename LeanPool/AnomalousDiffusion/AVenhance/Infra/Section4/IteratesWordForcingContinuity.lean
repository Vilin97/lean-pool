/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordForcingEnergy

/-! Natural all-order forcing integrability from actual coefficient jets. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Joint continuity of the actual forcing gradient follows from its finite
explicit word-flux expansion, including the initial boundary. -/
theorem iterate_word_forcing_gradient_continuousOn
    {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hA : ∀ t, 0 ≤ t → ContDiff ℝ (⊤ : ℕ∞) (A t))
    (hcoef : ∀ r : List (Fin 2),
      ContinuousOn (fun z : AmnrSpace => iterateMatrixWord (A z.1) r z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    ContinuousOn (fun z : AmnrSpace => spaceGrad
      (iterateSpatialWord w (vecDiv (fun y => (A z.1 y).mulVec (spaceGrad (v z.1) y)))) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  apply continuousOn_pi.mpr
  intro k
  have hc : ContinuousOn (fun z : AmnrSpace =>
      ∑ i : Fin 2, iterateWordFlux (A z.1) (v z.1) (i :: k :: w) z.2 i)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    continuousOn_finsetSum Finset.univ (fun i _ =>
      (continuous_apply i).comp_continuousOn
        (iterateSplitFlux_continuousOn_of_jets (iterateSpatialSplits (i :: k :: w))
          (fun p _ => hcoef p.1) hv))
  apply hc.congr
  intro z hz
  have hvs : ContDiff ℝ (⊤ : ℕ∞) (v z.1) :=
    hv.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (z.1, x)))
      (fun _ => ⟨hz.1, Set.mem_univ _⟩)
  exact iterate_word_forcing_gradient_flux_formula (hA z.1 hz.1) hvs w z.2 k

/-- No forcing-energy integrability premise is needed for the actual smooth
coefficient and scalar carriers. -/
theorem iterate_word_forcing_gradient_energy_integrable
    {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hA : ∀ t, 0 ≤ t → ContDiff ℝ (⊤ : ℕ∞) (A t))
    (hcoef : ∀ r : List (Fin 2),
      ContinuousOn (fun z : AmnrSpace => iterateMatrixWord (A z.1) r z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    IntegrableOn (fun z : AmnrSpace => vecNormSq (spaceGrad
      (iterateSpatialWord w (vecDiv (fun y => (A z.1 y).mulVec (spaceGrad (v z.1) y)))) z.2))
          timeCube :=
  iterate_timeCube_integrable_of_continuousOn
    ((iterate_vecNormSq_continuous continuous_id).comp_continuousOn
      (iterate_word_forcing_gradient_continuousOn hv hA hcoef w))

end AVenhance.Infra.Section4
