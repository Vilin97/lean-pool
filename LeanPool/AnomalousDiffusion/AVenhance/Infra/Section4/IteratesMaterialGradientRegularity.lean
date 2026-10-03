/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCommutedMaterialGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesErrorRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesLaplacianEnergy

/-! Initial-time integrable representative of the actual commuted material gradient. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual PDE expresses the commuted material gradient through diffusion,
 original forcing, and the proved smooth representative of the drift error. -/
theorem iterate_commuted_material_gradient_ae_representation
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F v : ℝ → Vec 2 → ℝ} {v₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F v₀ v)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    (fun z : AmnrSpace => spaceGrad (amnrMaterial b (fun t => iterateSpatialWord w (v t)) z.1)
        z.2) =ᵐ[
      volume.restrict timeCube]
      (fun z => κ • (fun j => spaceLap (fun y => spaceGrad (iterateSpatialWord w (v z.1)) y j)
          z.2) +
        spaceGrad (iterateSpatialWord w (F z.1)) z.2 -
        spaceGrad (iterateVelocitySplit ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty))
          (b z.1) (v z.1)) z.2) := by
  have hmono : (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ⊆
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun z hz => ⟨(show 0 < z.1 from hz.1).le, hz.2⟩
  filter_upwards [ae_restrict_mem iterate_timeCube_isOpen.measurableSet,
    iterate_material_error_gradient_ae_lower_velocity hb hsol.1 w] with z hz he
  funext j
  have ht := iterate_classical_commuted_material_gradient_equation hsol (hb.mono hmono) hz.1.1 w
      z.2 j
  rw [congrFun he j] at ht
  exact ht

/-- All natural material-gradient energy integrability follows from the
 actual equation and original forcing-jet continuity. -/
theorem iterate_commuted_material_gradient_energy_integrable
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F v : ℝ → Vec 2 → ℝ} {v₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F v₀ v)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2))
    (hFc : ContinuousOn (fun z : AmnrSpace => spaceGrad (iterateSpatialWord w (F z.1)) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    IntegrableOn (fun z : AmnrSpace => vecNormSq
      (spaceGrad (amnrMaterial b (fun t => iterateSpatialWord w (v t)) z.1) z.2)) timeCube := by
  have hs := iterateVelocitySplit_smooth_up_to_initial hb hsol.1
    ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty))
  have hg := (iterate_word_gradient_smooth_up_to_initial
    (u := fun t x => iterateVelocitySplit ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty))
      (b t) (v t) x) hs []).continuousOn
  have hc := ((iterate_word_laplacian_gradient_continuousOn hsol.1 w).const_smul κ).add hFc |>.sub
      hg
  have hi := iterate_timeCube_integrable_of_continuousOn
    ((iterate_vecNormSq_continuous continuous_id).comp_continuousOn hc)
  exact hi.congr ((iterate_commuted_material_gradient_ae_representation hsol hb w).fun_comp
      vecNormSq).symm

end AVenhance.Infra.Section4
