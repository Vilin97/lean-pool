/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialGradientRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVectorSquares

/-! Actual all-order material-gradient energy from its equation. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual commuted PDE yields the material-gradient energy estimate.
 Original forcing-jet continuity is structural; no energy estimate is assumed. -/
theorem iterate_commuted_material_gradient_energy_bound
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F v : ℝ → Vec 2 → ℝ} {v₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F v₀ v)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2))
    (hFc : ContinuousOn (fun z : AmnrSpace => spaceGrad (iterateSpatialWord w (F z.1)) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    spaceTimeGradNormSq (fun t => spaceGrad (amnrMaterial b (fun s => iterateSpatialWord w (v s))
        t)) ≤
      2 * κ ^ 2 * spaceTimeGradNormSq
        (fun t x j => spaceLap (fun y => spaceGrad (iterateSpatialWord w (v t)) y j) x) +
      4 * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (F t))) +
      4 * spaceTimeGradNormSq (fun t x => spaceGrad (fun y => iterateWordMaterialError
        (fun z : AmnrSpace => b z.1 z.2) w (fun z => v z.1 z.2) (t, y)) x) := by
  have hl := iterate_timeCube_integrable_of_continuousOn
    ((iterate_vecNormSq_continuous continuous_id).comp_continuousOn
      (iterate_word_laplacian_gradient_continuousOn hsol.1 w))
  have hf := iterate_timeCube_integrable_of_continuousOn
    ((iterate_vecNormSq_continuous continuous_id).comp_continuousOn hFc)
  have he := iterate_material_error_gradient_energy_integrable hb hsol.1 w
  have hmono : (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ⊆
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun z hz => ⟨(show 0 < z.1 from hz.1).le, hz.2⟩
  have ht := integral_mono_ae (iterate_commuted_material_gradient_energy_integrable hsol hb w hFc)
    (((hl.const_mul (2 * κ ^ 2)).add (hf.const_mul 4)).add (he.const_mul 4)) (by
      apply (ae_restrict_mem iterate_timeCube_isOpen.measurableSet).mono
      intro z hz
      have hvec : spaceGrad (amnrMaterial b (fun t => iterateSpatialWord w (v t)) z.1) z.2 =
          κ • (fun j => spaceLap (fun y => spaceGrad (iterateSpatialWord w (v z.1)) y j) z.2) +
            spaceGrad (iterateSpatialWord w (F z.1)) z.2 -
            spaceGrad (fun y => iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
              (fun z => v z.1 z.2) (z.1, y)) z.2 := by
        funext j
        exact iterate_classical_commuted_material_gradient_equation hsol (hb.mono hmono) hz.1.1 w
            z.2 j
      dsimp only [Pi.add_apply, Function.comp_def, id_eq]
      rw [hvec]
      exact iterate_material_vector_sq_bound κ _ _ _)
  dsimp only [Pi.add_apply, Function.comp_def, id_eq] at ht
  have ha := integral_add ((hl.const_mul (2 * κ ^ 2)).add (hf.const_mul 4)) (he.const_mul 4)
  dsimp only [Pi.add_apply, Function.comp_def, id_eq] at ha
  have ha2 := integral_add (hl.const_mul (2 * κ ^ 2)) (hf.const_mul 4)
  dsimp only [Function.comp_def, id_eq] at ha2
  rw [ha, ha2, integral_const_mul, integral_const_mul, integral_const_mul] at ht
  exact ht

end AVenhance.Infra.Section4
