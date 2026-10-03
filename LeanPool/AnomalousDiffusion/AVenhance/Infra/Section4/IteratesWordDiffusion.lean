/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusion

/-! Ordered spatial words and exact diffusion commutation for l.V. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open AVenhance

/-- Ordered coordinate derivatives, with the outermost derivative first. -/
def iterateSpatialWord : List (Fin 2) → (Vec 2 → ℝ) → Vec 2 → ℝ
  | [], f => f
  | i :: w, f => fun x => spaceGrad (iterateSpatialWord w f) x i

/-- Classical spatial smoothness is preserved at every derivative order. -/
theorem iterateSpatialWord_smooth {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : List (Fin 2)) :
    ContDiff ℝ (⊤ : ℕ∞) (iterateSpatialWord w f) := by
  induction w with
  | nil => exact hf
  | cons i w ih => exact contDiff_pi.mp (iterate_gradient_smooth ih) i

/-- Constant diffusivity commutes with every ordered spatial derivative.
No differentiated diffusion equation is supplied as an induction hypothesis. -/
theorem iterateSpatialWord_laplacian {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : List (Fin 2)) :
    iterateSpatialWord w (spaceLap f) = spaceLap (iterateSpatialWord w f) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [iterateSpatialWord, ih]
    funext x
    exact iterate_gradient_laplacian_commute (iterateSpatialWord_smooth hf w) x i

end AVenhance.Infra.Section4
