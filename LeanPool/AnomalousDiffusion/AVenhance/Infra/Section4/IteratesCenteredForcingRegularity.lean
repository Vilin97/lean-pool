/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCenteredHessianTransfer

/-! # Iterates Centered Forcing Regularity

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The literal centered Hessian forcing has a joint C1 carrier. Only one
 time derivative of K is used, as available whenever the first iterate exists. -/
theorem iterate_centered_hessian_forcing_joint_C1 {β : ℝ} (I : Ingredients β)
    (hN : 1 ≤ Nstar β) {m : ℕ} {κm : ℝ} (hm : 1 ≤ m) (hκm : 0 < κm)
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    ContDiffOn ℝ 1 (fun z : AmnrSpace => ∑ j : Fin 2, ∑ k : Fin 2,
      (I.Kmat κm m z.1 j k - timeAvgMat (I.Kmat κm m) j k) *
        iterateSpatialWord (j :: k :: w) (u z.1) z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hK := ((AVenhance.Infra.Section3.Kmat_contDiff I hm hκm).of_le
    (by exact_mod_cast hN : (1 : WithTop ℕ∞) ≤ Nstar β)).comp
    (contDiff_fst : ContDiff ℝ 1 (fun z : AmnrSpace => z.1))
  apply ContDiffOn.sum
  intro j _
  apply ContDiffOn.sum
  intro k _
  exact (((contDiff_pi.mp (contDiff_pi.mp hK j) k).contDiffOn).sub contDiffOn_const).mul
    ((iterateSpatialWord_smooth_up_to_initial hu (j :: k :: w)).of_le (by simp))

/-- Natural joint continuity of the actual centered forcing gradient. -/
theorem iterate_centered_hessian_forcing_gradient_continuousOn {β : ℝ} (I : Ingredients β)
    (hN : 1 ≤ Nstar β) {m : ℕ} {κm : ℝ} (hm : 1 ≤ m) (hκm : 0 < κm)
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    ContinuousOn (fun z : AmnrSpace => spaceGrad (fun y => ∑ j : Fin 2, ∑ k : Fin 2,
      (I.Kmat κm m z.1 j k - timeAvgMat (I.Kmat κm m) j k) *
        iterateSpatialWord (j :: k :: w) (u z.1) y) z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  apply continuousOn_pi.mpr
  intro j
  exact iterate_spatial_partial_continuous_up_to_initial
    (iterate_centered_hessian_forcing_joint_C1 I hN hm hκm hu w) j

end AVenhance.Infra.Section4
