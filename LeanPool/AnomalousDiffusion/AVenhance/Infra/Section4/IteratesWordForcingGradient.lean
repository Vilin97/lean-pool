/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordGrouping
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordFluxPairing

/-! All-order explicit gradient of the forcing, with exact binomial grouping. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

theorem IteratesWordForcingGradient.iterate_abs_list_sum {α : Type*} (P : List α) (f : α → ℝ) :
    |(P.map f).sum| ≤ (P.map (fun p => |f p|)).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

/-- Differentiating the actual forcing once more is the full Leibniz expansion
with two extra derivative letters: one for divergence and one for the gradient. -/
theorem iterate_word_forcing_gradient_formula
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (w : List (Fin 2)) (x : Vec 2) (k : Fin 2) :
    spaceGrad (iterateSpatialWord w (vecDiv (fun y => (A y).mulVec (spaceGrad v y)))) x k =
      ∑ i : Fin 2, ∑ j : Fin 2,
        ((iterateSpatialSplits (i :: k :: w)).map (fun p =>
          iterateSpatialWord p.1 (fun y => A y i j) x *
          spaceGrad (iterateSpatialWord p.2 v) x j)).sum := by
  change iterateSpatialWord (k :: w) (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x = _
  rw [iterateSpatialWord_divergence (iterate_matrix_gradient_smooth hA hv)]
  unfold vecDiv
  apply Finset.sum_congr rfl
  intro i _
  change iterateSpatialWord (i :: k :: w)
    (fun y => (A y).mulVec (spaceGrad v y) i) x = _
  exact congrFun (iterateSpatialWord_matrix_flux hA hv (i :: k :: w) i) x

end AVenhance.Infra.Section4
