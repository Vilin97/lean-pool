/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedCurrentRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialGradientRegularity

/-! Exact current material pairing with its retained drift commutator. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The commuted current material pairing is the original PDE pairing minus
 the actual drift error. Its natural integrability is derived from the PDE. -/
theorem iterate_terminal_commuted_current_pairing_split
    {s : ℝ} (hs1 : s ≤ 1)
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u v : ℝ → Vec 2 → ℝ}
    {u₀ : Vec 2 → ℝ} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hsol : IsClassicalSol b κ F u₀ u)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2))
    (hFc : ContinuousOn (fun z : AmnrSpace => spaceGrad (iterateSpatialWord w (F z.1)) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQc : ContinuousOn Q (Set.Ici (0 : ℝ))) :
    (∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (amnrMaterial b (fun s => iterateSpatialWord w (u s)) z.1) z.2)
      ((Q z.1).mulVec (spaceGrad (v z.1) z.2))) =
    (∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (iterateSpatialWord w (amnrMaterial b u z.1)) z.2)
      ((Q z.1).mulVec (spaceGrad (v z.1) z.2))) -
    (∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (fun y => iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2)
        w (fun z => u z.1 z.2) (z.1, y)) z.2)
      ((Q z.1).mulVec (spaceGrad (v z.1) z.2))) := by
  have hmono : (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ⊆
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun z hz => ⟨(show 0 < z.1 from hz.1).le, hz.2⟩
  have hQc' : ContinuousOn (fun z : AmnrSpace => Q z.1)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := hQc.comp continuousOn_fst (fun _ hz => hz.1)
  have hgc := (iterate_word_gradient_smooth_up_to_initial hv []).continuousOn
  have hrepr := ((iterate_word_laplacian_gradient_continuousOn hsol.1 w).const_smul κ).add hFc
  have hi := iterate_matrix_pairing_integrable hrepr hgc hQc'
  have hOrig : (fun z : AmnrSpace => spaceGrad (iterateSpatialWord w (amnrMaterial b u z.1)) z.2)
      =ᵐ[volume.restrict timeCube] (fun z => κ •
        (fun j => spaceLap (fun y => spaceGrad (iterateSpatialWord w (u z.1)) y j) z.2) +
        spaceGrad (iterateSpatialWord w (F z.1)) z.2) := by
    apply (ae_restrict_mem iterate_timeCube_isOpen.measurableSet).mono
    intro z hz
    funext j
    exact iterate_classical_word_material_gradient_equation hsol hz.1.1
      (iterate_classical_forcing_spatial_smooth hsol (hb.mono hmono) hz.1.1) w z.2 j
  have hO : IntegrableOn (fun z : AmnrSpace => vecDot
      (spaceGrad (iterateSpatialWord w (amnrMaterial b u z.1)) z.2)
      ((Q z.1).mulVec (spaceGrad (v z.1) z.2))) timeCube := by
    apply hi.congr
    filter_upwards [hOrig] with z hz
    rw [hz]
    rfl
  have hs := iterateVelocitySplit_smooth_up_to_initial hb hsol.1
    ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty))
  have hErrC := (iterate_word_gradient_smooth_up_to_initial
    (u := fun t x => iterateVelocitySplit ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty))
      (b t) (u t) x) hs []).continuousOn
  have hEi := iterate_matrix_pairing_integrable hErrC hgc hQc'
  have hE : IntegrableOn (fun z : AmnrSpace => vecDot
      (spaceGrad (fun y => iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2)
        w (fun z => u z.1 z.2) (z.1, y)) z.2)
      ((Q z.1).mulVec (spaceGrad (v z.1) z.2))) timeCube := by
    apply hEi.congr
    filter_upwards [iterate_material_error_gradient_ae_lower_velocity hb hsol.1 w] with z hz
    rw [hz]
    rfl
  have hsub := iterateTruncatedCell_subset hs1
  rw [← integral_sub (hO.mono_set hsub) (hE.mono_set hsub)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
    (iterate_commuted_material_gradient_ae_representation hsol hb w),
    ae_restrict_of_ae_restrict_of_subset hsub hOrig,
    ae_restrict_of_ae_restrict_of_subset hsub
      (iterate_material_error_gradient_ae_lower_velocity hb hsol.1 w)] with z hm ho he
  rw [hm, ho, he]
  simp [vecDot, sub_mul, Finset.sum_sub_distrib]

end AVenhance.Infra.Section4
