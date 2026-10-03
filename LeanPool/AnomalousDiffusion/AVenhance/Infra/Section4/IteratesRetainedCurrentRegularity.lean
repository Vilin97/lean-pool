/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesRetainedCurrentForcing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesLaplacianEnergy

/-! Natural integrability for the current oscillatory material pairing. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The current material budget requires no separately assumed integrability
of diffusion or forcing pairings. Actual smoothness supplies them. -/
theorem iterate_terminal_retained_current_pairing_of_continuity
    {s : ℝ} (hs1 : s ≤ 1)
    {b : ℝ → Vec 2 → Vec 2} {κ D : ℝ} {F u v : ℝ → Vec 2 → ℝ}
    {u₀ : Vec 2 → ℝ} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hsol : IsClassicalSol b κ F u₀ u) (w : List (Fin 2))
    (hκ : 0 < κ) (hQ : ∀ t i j, |Q t i j| ≤ D)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hvp : ∀ t, 0 < t → IsZ2Periodic (v t))
    (hF : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (F t))
    (hFc : ContinuousOn (fun z : AmnrSpace => spaceGrad (iterateSpatialWord w (F z.1)) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQc : ContinuousOn Q (Set.Ici (0 : ℝ))) :
    |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (amnrMaterial b u
        z.1)) z.2)
      ((Q z.1).mulVec (spaceGrad (v z.1) z.2))| ≤
      κ / 24 * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u t))) +
      24 * κ * D ^ 2 * spaceTimeGradNormSq
        (fun t x j => spaceLap (fun y => spaceGrad (v t) y j) x) +
      |∫ z in iterateTruncatedCell s, vecDot
        (spaceGrad (iterateSpatialWord w (F z.1)) z.2)
        ((Q z.1).mulVec (spaceGrad (v z.1) z.2))| := by
  have hQc' : ContinuousOn (fun z : AmnrSpace => Q z.1)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    hQc.comp continuousOn_fst (fun _ hz => hz.1)
  have hu := (iterate_word_gradient_smooth_up_to_initial hsol.1 w).continuousOn
  have hv' := (iterate_word_gradient_smooth_up_to_initial hv []).continuousOn
  have hLu := iterate_word_laplacian_gradient_continuousOn hsol.1 w
  have hLv := iterate_word_laplacian_gradient_continuousOn hv []
  have normCont {a : AmnrSpace → Vec 2}
      (ha : ContinuousOn a (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
      ContinuousOn (fun z => vecNormSq (a z)) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    unfold vecNormSq vecDot
    exact continuousOn_finsetSum Finset.univ (fun j _ =>
      ((continuous_apply j).comp_continuousOn ha).mul ((continuous_apply j).comp_continuousOn ha))
  exact iterate_terminal_current_word_pairing_retained_forcing hs1 hsol w hκ hQ
    (fun t ht => hv.comp_contDiff
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
      (fun _ => ⟨ht.le, Set.mem_univ _⟩)) hvp hF
    (iterate_word_gradient_energy_integrable hsol.1 w)
    (iterate_timeCube_integrable_of_continuousOn (normCont hLv))
    (iterate_matrix_pairing_integrable hLu hv' hQc')
    (iterate_matrix_pairing_integrable hu hLv hQc')
    (iterate_matrix_pairing_integrable hFc hv' hQc')

end AVenhance.Infra.Section4
