/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesGradientMaterialCross
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixContinuity

/-! # Iterates Gradient Material Matrix

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Natural integrability of the vector material-gradient pairing follows
componentwise from the exact gradient commutator. -/
theorem iterate_gradient_material_matrix_pairing_integrable
    {b : ℝ → Vec 2 → Vec 2} {u v : ℝ → Vec 2 → ℝ}
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQ : ContinuousOn (fun z : AmnrSpace => Q z.1) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    IntegrableOn (fun z : AmnrSpace => vecDot (spaceGrad (u z.1) z.2)
      ((Q z.1).mulVec (spaceGrad (amnrMaterial b v z.1) z.2))) timeCube := by
  have hgu := (iterate_word_gradient_smooth_up_to_initial hu []).continuousOn
  have hi (j k : Fin 2) : IntegrableOn (fun z : AmnrSpace =>
      (spaceGrad (u z.1) z.2 j * Q z.1 j k) *
        spaceGrad (amnrMaterial b v z.1) z.2 k) timeCube :=
    iterate_gradient_material_cross_timeCube_integrable
      (u := fun t x => spaceGrad (u t) x j * Q t j k) hb
      (((continuous_apply j).comp_continuousOn hgu).mul
        ((continuous_apply k).comp_continuousOn ((continuous_apply j).comp_continuousOn hQ))) hv k
  have ht := integrable_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hi j k))
  unfold IntegrableOn at hi ⊢
  convert ht using 1
  funext z
  simp only [vecDot, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

end AVenhance.Infra.Section4
