/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesGradientMaterialMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialGradientRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedMatrix

/-! # Iterates Terminal Previous Material

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The previous material-gradient term receives current dissipation by
Young's inequality. Its natural integrability follows from the actual PDE. -/
theorem iterate_terminal_previous_material_pairing_bound
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u v : ℝ → Vec 2 → ℝ} {v₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F v₀ v)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2))
    (hFc : ContinuousOn (fun z : AmnrSpace => spaceGrad (iterateSpatialWord w (F z.1)) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hQc : ContinuousOn (fun z : AmnrSpace => Q z.1) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {D s : ℝ} (hQ : ∀ t j k, |Q t j k| ≤ D) (hκ : 0 < κ) (hs1 : s ≤ 1) :
    |∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      ((Q z.1).mulVec (spaceGrad
        (amnrMaterial b (fun t => iterateSpatialWord w (v t)) z.1) z.2))| ≤
      κ / 24 * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u t))) +
      24 * D ^ 2 / κ * spaceTimeGradNormSq (fun t => spaceGrad
        (amnrMaterial b (fun s => iterateSpatialWord w (v s)) t)) := by
  have huw := iterateSpatialWord_smooth_up_to_initial hu w
  have hvw := iterateSpatialWord_smooth_up_to_initial hsol.1 w
  have hi := iterate_gradient_material_matrix_pairing_integrable
    (u := fun t => iterateSpatialWord w (u t))
    (v := fun t => iterateSpatialWord w (v t)) hb huw hvw hQc
  have ha := iterate_timeCube_integrable_of_continuousOn
    ((iterate_vecNormSq_continuous continuous_id).comp_continuousOn
      (iterate_word_gradient_smooth_up_to_initial hu w).continuousOn)
  have hv := iterate_commuted_material_gradient_energy_integrable hsol hb w hFc
  have ht := iterate_truncated_matrix_pairing_bound (A := fun t _ => Q t)
    (a := fun t => spaceGrad (iterateSpatialWord w (u t)))
    (b := fun t => spaceGrad (amnrMaterial b (fun s => iterateSpatialWord w (v s)) t))
    hs1 (div_pos hκ (by norm_num : (0 : ℝ) < 24))
    (fun t _ j k => hQ t j k) ha hv hi
  convert ht using 1
  field_simp

end AVenhance.Infra.Section4
