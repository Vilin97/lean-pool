/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialGradientCommutator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCrossCell

/-! # Iterates Gradient Material Cross

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- A smooth actual vector field has a jointly continuous spatial matrix
 gradient on the closed nonnegative-time domain. -/
theorem iterate_flow_gradient_matrix_continuousOn {b : ℝ → Vec 2 → Vec 2}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun z : AmnrSpace => gradMatrix (b z.1) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  apply continuousOn_pi.mpr
  intro j
  apply continuousOn_pi.mpr
  intro k
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2 k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := contDiffOn_pi.mp hb k
  exact (iterate_spatial_partial_smooth_up_to_initial hc j).continuousOn

/-- Pairings with the actual gradient of a material derivative inherit
integrability from the C1 material representative and the exact drift term. -/
theorem iterate_gradient_material_cross_timeCube_integrable
    {b : ℝ → Vec 2 → Vec 2} {u v : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContinuousOn (fun z : AmnrSpace => u z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (j : Fin 2) :
    IntegrableOn (fun z : AmnrSpace => u z.1 z.2 * spaceGrad (amnrMaterial b v z.1) z.2 j)
      timeCube := by
  have hvg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => spaceGrad (v z.1) z.2 j)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := iterate_spatial_partial_smooth_up_to_initial hv j
  have hi := iterate_material_cross_timeCube_integrable
    (v := fun t x => spaceGrad (v t) x j) hb.continuousOn hu (hvg.of_le (by simp))
  have hBg := iterate_flow_gradient_matrix_continuousOn hb
  have hVg := (iterate_word_gradient_smooth_up_to_initial hv []).continuousOn
  have hc : ContinuousOn (fun z : AmnrSpace =>
      u z.1 z.2 * ((gradMatrix (b z.1) z.2).mulVec (spaceGrad (v z.1) z.2)) j)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    apply hu.mul
    change ContinuousOn (fun z : AmnrSpace => ∑ k : Fin 2,
      gradMatrix (b z.1) z.2 j k * spaceGrad (v z.1) z.2 k) _
    exact continuousOn_finsetSum Finset.univ (fun k _ =>
      ((continuous_apply k).comp_continuousOn ((continuous_apply j).comp_continuousOn hBg)).mul
        ((continuous_apply k).comp_continuousOn hVg))
  have ht := hi.add (iterate_timeCube_integrable_of_continuousOn hc)
  have hmono : (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ⊆
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun z hz => ⟨(show 0 < z.1 from hz.1).le, hz.2⟩
  apply ht.congr
  apply (ae_restrict_mem iterate_timeCube_isOpen.measurableSet).mono
  intro z hz
  have he := iterate_material_gradient_commutator (hb.mono hmono) (hv.mono hmono) hz.1.1 z.2 j
  dsimp only [Pi.add_apply]
  rw [he]
  ring

end AVenhance.Infra.Section4
