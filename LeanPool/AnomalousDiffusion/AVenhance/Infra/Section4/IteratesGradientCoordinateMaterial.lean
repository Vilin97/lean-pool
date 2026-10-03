/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesGradientMaterialCross

/-! # Iterates Gradient Coordinate Material

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Coordinate material pairings inherit integrability directly from the
C1 scalar gradient carriers and the continuous primitive entry. -/
theorem iterate_gradient_coordinate_material_pairing_integrable
    {b : ℝ → Vec 2 → Vec 2} {u v : ℝ → Vec 2 → ℝ} {q : ℝ → ℝ}
    (hb : ContinuousOn (fun z : AmnrSpace => b z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hq : ContinuousOn (fun z : AmnrSpace => q z.1) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (j k : Fin 2) :
    IntegrableOn (fun z : AmnrSpace => q z.1 * spaceGrad (u z.1) z.2 j *
      amnrMaterial b (fun t x => spaceGrad (v t) x k) z.1 z.2) timeCube := by
  have hgu := iterate_spatial_partial_smooth_up_to_initial hu j
  have hgv := iterate_spatial_partial_smooth_up_to_initial hv k
  exact iterate_material_cross_timeCube_integrable
    (u := fun t x => q t * spaceGrad (u t) x j)
    (v := fun t x => spaceGrad (v t) x k) hb
    (hq.mul hgu.continuousOn) (hgv.of_le (by simp))

end AVenhance.Infra.Section4
