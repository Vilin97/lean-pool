/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesErrorRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordTimeEnergy

/-! Actual homogeneous scalar material energy at every spatial order. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The scalar Laplacian of an actual word has a continuous initial-time carrier. -/
theorem iterate_word_laplacian_continuousOn {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    ContinuousOn (fun z : AmnrSpace => spaceLap (iterateSpatialWord w (u z.1)) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  exact continuousOn_finsetSum Finset.univ (fun k _ =>
    (continuous_apply k).comp_continuousOn
      (iterate_word_gradient_smooth_up_to_initial hu (k :: w)).continuousOn)

/-- The actual homogeneous PDE retains the complete drift commutator. -/
theorem iterate_homogeneous_word_material_equation
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ (fun _ _ => 0) u₀ u)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) {t : ℝ} (ht : 0 < t)
    (w : List (Fin 2)) (x : Vec 2) :
    amnrMaterial b (fun s => iterateSpatialWord w (u s)) t x =
      κ * spaceLap (iterateSpatialWord w (u t)) x -
      iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
        (fun z => u z.1 z.2) (t, x) := by
  have he := iterate_material_equation (iterate_classical_spatial_word_sol hsol hb w) ht x
  simpa only [iterateSpatialWord_zero, Pi.zero_apply, zero_sub, sub_eq_add_neg, zero_add] using he

/-- Homogeneous material energy is derived from diffusion and the actual drift
error. Its integrability follows from proved initial-time representatives. -/
theorem iterate_homogeneous_word_material_energy_bound
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ (fun _ _ => 0) u₀ u)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    (∫ z in timeCube,
      (amnrMaterial b (fun t => iterateSpatialWord w (u t)) z.1 z.2) ^ 2) ≤
      2 * κ ^ 2 * (∫ z in timeCube, (spaceLap (iterateSpatialWord w (u z.1)) z.2) ^ 2) +
      2 * (∫ z in timeCube, (iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2)
        w (fun z => u z.1 z.2) z) ^ 2) := by
  have hmono : (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ⊆
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun z hz => ⟨(show 0 < z.1 from hz.1).le, hz.2⟩
  have hL := iterate_word_laplacian_continuousOn hsol.1 w
  have hLi := iterate_timeCube_integrable_of_continuousOn (hL.pow 2)
  change IntegrableOn (fun z : AmnrSpace => (spaceLap (iterateSpatialWord w (u z.1)) z.2) ^ 2)
      timeCube at hLi
  have hEi := iterate_material_error_energy_integrable hb hsol.1 w
  have hrepr := iterateVelocitySplit_continuousOn hb hsol.1
    ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty))
  have hi := iterate_timeCube_integrable_of_continuousOn (((hL.const_mul κ).sub hrepr).pow 2)
  change IntegrableOn (fun z : AmnrSpace =>
    (κ * spaceLap (iterateSpatialWord w (u z.1)) z.2 -
      iterateVelocitySplit ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty))
        (b z.1) (u z.1) z.2) ^ 2) timeCube at hi
  have he : (fun z : AmnrSpace => amnrMaterial b
      (fun t => iterateSpatialWord w (u t)) z.1 z.2) =ᵐ[volume.restrict timeCube]
      (fun z => κ * spaceLap (iterateSpatialWord w (u z.1)) z.2 -
        iterateVelocitySplit ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty))
          (b z.1) (u z.1) z.2) := by
    filter_upwards [ae_restrict_mem iterate_timeCube_isOpen.measurableSet,
      iterate_material_error_ae_lower_velocity hb hsol.1 w] with z hz hErr
    have ht := iterate_homogeneous_word_material_equation hsol (hb.mono hmono) hz.1.1 w z.2
    rw [hErr] at ht
    exact ht
  have hMi : IntegrableOn (fun z : AmnrSpace =>
      (amnrMaterial b (fun t => iterateSpatialWord w (u t)) z.1 z.2) ^ 2) timeCube :=
    hi.congr ((he.fun_comp (fun x => x ^ 2)).symm)
  have ht := integral_mono_ae hMi ((hLi.const_mul (2 * κ ^ 2)).add (hEi.const_mul 2)) (by
    apply (ae_restrict_mem iterate_timeCube_isOpen.measurableSet).mono
    intro z hz
    dsimp only [Pi.add_apply, Pi.pow_apply]
    rw [iterate_homogeneous_word_material_equation hsol (hb.mono hmono) hz.1.1 w z.2]
    nlinarith only [sq_nonneg (κ * spaceLap (iterateSpatialWord w (u z.1)) z.2 +
      iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w (fun z => u z.1 z.2) z)])
  have hs := integral_add (hLi.const_mul (2 * κ ^ 2)) (hEi.const_mul 2)
  dsimp only [Pi.add_apply] at hs ht
  rw [hs, integral_const_mul, integral_const_mul] at ht
  exact ht

end AVenhance.Infra.Section4
