/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordForcingGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedGrouping

/-! Forcing-gradient energy without pointwise scalar analytic hypotheses. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- The gradient of the actual differentiated forcing is a sum of two
explicit flux components at two additional derivative letters. -/
theorem iterate_word_forcing_gradient_flux_formula
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (w : List (Fin 2)) (x : Vec 2) (k : Fin 2) :
    spaceGrad (iterateSpatialWord w (vecDiv (fun y => (A y).mulVec (spaceGrad v y)))) x k =
      ∑ i : Fin 2, iterateWordFlux A v (i :: k :: w) x i := by
  rw [iterate_word_forcing_gradient_formula hA hv]
  rfl

/-- Squaring this finite component sum costs two, with no dependence on n. -/
theorem iterate_word_forcing_gradient_flux_sq_bound
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (w : List (Fin 2)) (x : Vec 2) :
    vecNormSq (spaceGrad
      (iterateSpatialWord w (vecDiv (fun y => (A y).mulVec (spaceGrad v y)))) x) ≤
      2 * ∑ k : Fin 2, ∑ i : Fin 2, vecNormSq (iterateWordFlux A v (i :: k :: w) x) := by
  have hc (k : Fin 2) :
      spaceGrad (iterateSpatialWord w (vecDiv (fun y => (A y).mulVec (spaceGrad v y)))) x k ^ 2 ≤
      2 * ∑ i : Fin 2, vecNormSq (iterateWordFlux A v (i :: k :: w) x) := by
    rw [iterate_word_forcing_gradient_flux_formula hA hv]
    simp only [Fin.sum_univ_two, vecNormSq, vecDot]
    nlinarith only [sq_nonneg (iterateWordFlux A v (0 :: k :: w) x 0 -
      iterateWordFlux A v (1 :: k :: w) x 1),
      sq_nonneg (iterateWordFlux A v (0 :: k :: w) x 1),
      sq_nonneg (iterateWordFlux A v (1 :: k :: w) x 0)]
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 2))) => hc k)
  simpa only [vecNormSq, vecDot, pow_two, ← Finset.mul_sum] using hs

end AVenhance.Infra.Section4
