/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalVelocityTransfer
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalMaterialHessian

/-! Quantitative actual differentiated material commutator after transfer. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual gradient commutator has the linear geometric recurrence
 bound after spatial transfer, with no extra current scalar derivative. -/
theorem iterate_terminal_transferred_material_error_analytic_bound
    {s : ℝ} (hs1 : s ≤ 1)
    {b : ℝ → Vec 2 → Vec 2} {u v : ℝ → Vec 2 → ℝ}
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQc : ContinuousOn Q (Set.Ici (0 : ℝ)))
    (hbp : ∀ t, 0 < t → IsZ2Periodic (b t))
    (hup : ∀ t, 0 < t → IsZ2Periodic (u t))
    (hvp : ∀ t, 0 < t → IsZ2Periodic (v t)) (w : List (Fin 2)) (i : ℕ)
    {Qmax B Gprev Gcur r L : ℝ} (hQmax : 0 ≤ Qmax) (hB : 0 ≤ B)
    (hGp : 0 ≤ Gprev) (hGc : 0 ≤ Gcur) (hr : 0 ≤ r) (hL : 0 < L)
    (hgain : r / L ≤ 1 / 2) (D : ℕ → ℝ) (hD : ∀ n, 0 ≤ D n)
    (hQ : ∀ t j k, |Q t j k| ≤ Qmax)
    (hjet : ∀ t x p, p ∈ (iterateSpatialSplits w).filter (fun p => !p.1.isEmpty) → ∀ j,
      |iterateSpatialWord p.1 (fun y => b t y j) x| ≤ B * (p.1.length.factorial : ℝ) * r ^
          p.1.length)
    (hprev : ∀ k : Fin 2,
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord (k :: w) (v t))) ≤
        (Gprev * ((w.length + 2 * i - 1).factorial : ℝ) * L ^ (w.length + 1)) ^ 2)
    (hcur : ∀ p ∈ (iterateSpatialSplits w).filter (fun p => !p.1.isEmpty),
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (u t))) ≤
        (Gcur * ((p.2.length + 2 * i).factorial : ℝ) * L ^ p.2.length * D p.2.length) ^ 2) :
    |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (fun y => iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => u z.1 z.2) (z.1, y)) z.2)
      ((Q z.1).mulVec (spaceGrad (iterateSpatialWord w (v z.1)) z.2))| ≤
      8 * Qmax * B * Gprev * Gcur * r *
        (((w.length + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2 *
        ∑ k ∈ Finset.range w.length, (1 / (2 : ℝ)) ^ k * D (w.length - 1 - k) := by
  have hp (t : ℝ) (ht : 0 < t) : IsZ2Periodic (iterateSpatialWord w (v t)) := by
    have hs : ContDiff ℝ (⊤ : ℕ∞) (v t) :=
      hv.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
        (fun _ => ⟨ht.le, Set.mem_univ _⟩)
    exact iterateSpatialWord_periodic hs (hvp t ht) w
  rw [iterate_terminal_material_error_gradient_transfer hs1 hb hu
    (iterateSpatialWord_smooth_up_to_initial hv w) hQc hbp hup hp w, abs_neg]
  have he := iterate_terminal_material_hessian_error_analytic_bound hs1 hb hu hv hQc w i
    hQmax hB hGp hGc hr hL hgain D hD hQ hjet hprev hcur
  have hswap : (fun z : AmnrSpace => iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => u z.1 z.2) z *
      ∑ j : Fin 2, ∑ k : Fin 2, Q z.1 j k *
        spaceGrad (fun y => spaceGrad (iterateSpatialWord w (v z.1)) y k) z.2 j) =
      (fun z => (∑ j : Fin 2, ∑ k : Fin 2, Q z.1 j k *
        spaceGrad (fun y => spaceGrad (iterateSpatialWord w (v z.1)) y k) z.2 j) *
        iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w (fun z => u z.1 z.2) z) := by
    funext z; ring
  rw [hswap]
  exact he

end AVenhance.Infra.Section4
