/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordDiffusion

/-! All-order differentiated material equations for the actual increments. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Ordered differentiation distributes over the actual constant-coefficient
linear combination in the increment equation. -/
theorem iterateSpatialWord_linear {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (c : ℝ) (w : List (Fin 2)) :
    iterateSpatialWord w (fun x => c * f x + g x) =
      fun x => c * iterateSpatialWord w f x + iterateSpatialWord w g x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [iterateSpatialWord, ih]
    funext x
    have hdf := (iterateSpatialWord_smooth hf w).differentiable (by simp) |>.differentiableAt (x
        := x)
    have hdg := (iterateSpatialWord_smooth hg w).differentiable (by simp) |>.differentiableAt (x
        := x)
    unfold spaceGrad
    rw [fderiv_fun_add (hdf.const_mul c) hdg, fderiv_const_mul hdf c]
    rfl

/-- Differentiate the actual classical PDE at every spatial order. This keeps
D^w(D_t u) on the left; commuting D_t past the word is a subsequent step. -/
theorem iterate_classical_material_word_equation
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F u₀ u) {t : ℝ} (ht : 0 < t)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (F t)) (w : List (Fin 2)) :
    iterateSpatialWord w (amnrMaterial b u t) = fun x =>
      κ * spaceLap (iterateSpatialWord w (u t)) x + iterateSpatialWord w (F t) x := by
  have hu : ContDiff ℝ (⊤ : ℕ∞) (u t) := by
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)) := by fun_prop
    exact hsol.1.comp_contDiff hm (fun _ => ⟨ht.le, Set.mem_univ _⟩)
  have heq : amnrMaterial b u t = fun x => κ * spaceLap (u t) x + F t x := by
    funext x
    exact iterate_material_equation hsol ht x
  rw [heq, iterateSpatialWord_linear (iterate_laplacian_smooth hu) hF,
    iterateSpatialWord_laplacian hu]

end AVenhance.Infra.Section4
