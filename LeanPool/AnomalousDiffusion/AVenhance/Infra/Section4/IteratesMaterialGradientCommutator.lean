/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesErrorGradient

/-! # Iterates Material Gradient Commutator

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Material differentiation of an actual gradient keeps the one-jet drift
commutator with its exact sign and the gradMatrix convention. -/
theorem iterate_material_gradient_commutator
    {b : ℝ → Vec 2 → Vec 2} {u : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) {t : ℝ} (ht : 0 < t) (x : Vec 2) (j : Fin 2) :
    amnrMaterial b (fun s y => spaceGrad (u s) y j) t x =
      spaceGrad (amnrMaterial b u t) x j -
        ((gradMatrix (b t) x).mulVec (spaceGrad (u t) x)) j := by
  have he := iterate_material_spatial_word_expansion hb hu ht [j] x
  have herr := iterate_material_error_gradient_formula hb hu ht [] x j
  simp only [iterateWordMaterialError, iterateSpatialWord, spaceGrad, fderiv_fun_const,
    Pi.zero_apply, zero_apply] at herr
  change (0 : ℝ) = iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) [j]
    (fun z => u z.1 z.2) (t, x) -
    ∑ k : Fin 2, spaceGrad (fun y => b t y k) x j * spaceGrad (u t) x k at herr
  change spaceGrad (amnrMaterial b u t) x j =
    amnrMaterial b (fun s y => spaceGrad (u s) y j) t x +
    iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) [j]
      (fun z => u z.1 z.2) (t, x) at he
  simp only [gradMatrix, Matrix.of_apply, Matrix.mulVec, dotProduct]
  linarith only [he, herr]

end AVenhance.Infra.Section4
