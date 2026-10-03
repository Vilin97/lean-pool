/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordSolution

/-! Material derivatives are differentiated before commuting the drift. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The differentiated current material field has only the differentiated
original forcing on its right side. Drift commutators are kept separately. -/
theorem iterate_classical_word_material_gradient_equation
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F u₀ u) {t : ℝ} (ht : 0 < t)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (F t)) (w : List (Fin 2)) (x : Vec 2) (j : Fin 2) :
    spaceGrad (iterateSpatialWord w (amnrMaterial b u t)) x j =
      κ * spaceLap (fun y => spaceGrad (iterateSpatialWord w (u t)) y j) x +
        spaceGrad (iterateSpatialWord w (F t)) x j := by
  have hu : ContDiff ℝ (⊤ : ℕ∞) (u t) := by
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)) := by fun_prop
    exact hsol.1.comp_contDiff hm (fun _ => ⟨ht.le, Set.mem_univ _⟩)
  rw [iterate_classical_material_word_equation hsol ht hF w]
  have hL := ((iterate_laplacian_smooth (iterateSpatialWord_smooth hu w)).differentiable
    (by simp)).differentiableAt (x := x)
  have hW := ((iterateSpatialWord_smooth hF w).differentiable (by simp)).differentiableAt (x := x)
  unfold spaceGrad
  rw [fderiv_fun_add (hL.const_mul κ) hW, fderiv_const_mul hL κ]
  change κ * spaceGrad (spaceLap (iterateSpatialWord w (u t))) x j +
    spaceGrad (iterateSpatialWord w (F t)) x j = _
  rw [iterate_gradient_laplacian_commute (iterateSpatialWord_smooth hu w)]
  rfl

end AVenhance.Infra.Section4
