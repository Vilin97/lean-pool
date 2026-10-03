/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordMaterialGradient

/-! The actual material-gradient equation with its full drift error. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Differentiate the actual commuted equation. The drift error has a minus
sign and is kept explicit for transfer to the preceding Hessian. -/
theorem iterate_classical_commuted_material_gradient_equation
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F u₀ u)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) {t : ℝ} (ht : 0 < t)
    (w : List (Fin 2)) (x : Vec 2) (j : Fin 2) :
    spaceGrad (amnrMaterial b (fun s => iterateSpatialWord w (u s)) t) x j =
      κ * spaceLap (fun y => spaceGrad (iterateSpatialWord w (u t)) y j) x +
      spaceGrad (iterateSpatialWord w (F t)) x j -
      spaceGrad (fun y => iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
        (fun z => u z.1 z.2) (t, y)) x j := by
  have hws := iterate_classical_spatial_word_sol hsol hb w
  have hF := iterate_classical_forcing_spatial_smooth hsol hb ht
  have hU := (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).prod (isOpen_univ : IsOpen (Set.univ : Set
      (Vec 2)))
  have hu := hsol.1.mono (show (Set.Ioi (0 : ℝ) ×ˢ Set.univ) ⊆
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) from fun z hz => ⟨(show 0 < z.1 from hz.1).le, hz.2⟩)
  have hes := (iterateWordMaterialError_smoothOn hU hb hu w).comp_contDiff
    (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
    (fun _ => ⟨ht, Set.mem_univ _⟩)
  change ContDiff ℝ (⊤ : ℕ∞) (fun y => iterateWordMaterialError
    (fun z : AmnrSpace => b z.1 z.2) w (fun z => u z.1 z.2) (t, y)) at hes
  have hwf := iterateSpatialWord_smooth hF w
  have he := iterate_classical_material_gradient_equation hws ht x
    ((hwf.sub hes).differentiable (by simp)).differentiableAt j
  change spaceGrad (amnrMaterial b (fun s => iterateSpatialWord w (u s)) t) x j =
    κ * spaceLap (fun y => spaceGrad (iterateSpatialWord w (u t)) y j) x +
      spaceGrad (fun y => iterateSpatialWord w (F t) y - iterateWordMaterialError
        (fun z : AmnrSpace => b z.1 z.2) w (fun z => u z.1 z.2) (t, y)) x j at he
  unfold spaceGrad at he
  rw [fderiv_fun_sub (hwf.differentiable (by simp)).differentiableAt
    (hes.differentiable (by simp)).differentiableAt] at he
  change _ = κ * spaceLap (fun y => spaceGrad (iterateSpatialWord w (u t)) y j) x +
    (spaceGrad (iterateSpatialWord w (F t)) x j -
      spaceGrad (fun y => iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
        (fun z => u z.1 z.2) (t, y)) x j) at he
  change spaceGrad (amnrMaterial b (fun s => iterateSpatialWord w (u s)) t) x j = _ at he
  linarith only [he]

end AVenhance.Infra.Section4
