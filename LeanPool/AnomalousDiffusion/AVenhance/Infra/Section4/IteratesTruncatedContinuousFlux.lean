/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedWeighted
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedIntegrability

/-! Natural integrability for every terminal selected coefficient flux. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- All-order space-time forcing estimate with natural integrability
discharged from actual scalar smoothness and conditional coefficient continuity. -/
theorem iterate_truncated_flux_pairing_bound_of_continuous_jets
    {s : ℝ} (hs1 : s ≤ 1)
    (P : List (List (Fin 2) × List (Fin 2)))
    {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {u v : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hA : ∀ p ∈ P, ContinuousOn
      (fun z : AmnrSpace => iterateMatrixWord (A z.1) p.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2)) (ρ D : List (Fin 2) × List (Fin 2) → ℝ)
    (hρ : ∀ p ∈ P, 0 < ρ p)
    (hAj : ∀ t x, ∀ p ∈ P, ∀ i j,
      |iterateSpatialWord p.1 (fun y => A t y i j) x| ≤ D p) :
    |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      (iterateSplitFlux P (A z.1) (v z.1) z.2)| ≤
      (P.map ρ).sum * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u t))) +
      (P.map (fun p => D p ^ 2 / ρ p * spaceTimeGradNormSq
        (fun t => spaceGrad (iterateSpatialWord p.2 (v t))))).sum := by
  have ha := (iterate_word_gradient_smooth_up_to_initial hu w).continuousOn
  have hF := iterateSplitFlux_continuousOn_of_jets P hA hv
  have hp : IntegrableOn (fun z : AmnrSpace =>
      vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
        (iterateSplitFlux P (A z.1) (v z.1) z.2)) timeCube := by
    apply iterate_timeCube_integrable_of_continuousOn
    unfold vecDot
    exact continuousOn_finsetSum Finset.univ (fun i _ =>
      ((continuous_apply i).comp_continuousOn ha).mul ((continuous_apply i).comp_continuousOn hF))
  exact iterate_truncated_split_flux_pairing_bound hs1 P A v
    (fun t => spaceGrad (iterateSpatialWord w (u t))) ρ D hρ hAj
    (iterate_word_gradient_energy_integrable hu w)
    (fun p _ => iterate_word_gradient_energy_integrable hv p.2) hp

end AVenhance.Infra.Section4
