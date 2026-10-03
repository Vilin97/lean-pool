/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHessianFactor
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalAnalyticMaterial

/-! Actual preceding Hessian and current lower drift error in analytic weights. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The transferred current material error has the source linear geometric
 kernel. Hessian energy is derived from actual preceding gradients. -/
theorem iterate_terminal_material_hessian_error_analytic_bound
    {s : ℝ} (hs1 : s ≤ 1)
    {b : ℝ → Vec 2 → Vec 2} {u v : ℝ → Vec 2 → ℝ}
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQc : ContinuousOn Q (Set.Ici (0 : ℝ))) (w : List (Fin 2)) (i : ℕ)
    {Qmax B Gprev Gcur r L : ℝ} (hQmax : 0 ≤ Qmax) (hB : 0 ≤ B)
    (hGp : 0 ≤ Gprev) (hGc : 0 ≤ Gcur) (hr : 0 ≤ r) (hL : 0 < L)
    (hgain : r / L ≤ 1 / 2) (D : ℕ → ℝ) (hD : ∀ n, 0 ≤ D n)
    (hQ : ∀ t j k, |Q t j k| ≤ Qmax)
    (hjet : ∀ t x p, p ∈ (iterateSpatialSplits w).filter (fun p => !p.1.isEmpty) → ∀ j,
      |iterateSpatialWord p.1 (fun y => b t y j) x| ≤
        B * (p.1.length.factorial : ℝ) * r ^ p.1.length)
    (hprev : ∀ k : Fin 2,
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord (k :: w) (v t))) ≤
        (Gprev * ((w.length + 2 * i - 1).factorial : ℝ) * L ^ (w.length + 1)) ^ 2)
    (hcur : ∀ p ∈ (iterateSpatialSplits w).filter (fun p => !p.1.isEmpty),
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (u t))) ≤
        (Gcur * ((p.2.length + 2 * i).factorial : ℝ) * L ^ p.2.length * D p.2.length) ^ 2) :
    |∫ z in iterateTruncatedCell s, (∑ j : Fin 2, ∑ k : Fin 2, Q z.1 j k *
      spaceGrad (fun y => spaceGrad (iterateSpatialWord w (v z.1)) y k) z.2 j) *
      iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
        (fun z => u z.1 z.2) z| ≤
      8 * Qmax * B * Gprev * Gcur * r *
        (((w.length + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2 *
        ∑ k ∈ Finset.range w.length, (1 / (2 : ℝ)) ^ k * D (w.length - 1 - k) := by
  have he := iterate_hessian_factor_energy_bound hv hQc w hQmax hQ hprev
  have hea : (∫ z in timeCube, (∑ j : Fin 2, ∑ k : Fin 2, Q z.1 j k *
      spaceGrad (fun y => spaceGrad (iterateSpatialWord w (v z.1)) y k) z.2 j) ^ 2) ≤
      ((4 * Qmax * Gprev) * ((w.length + 2 * i - 1).factorial : ℝ) *
        L ^ (w.length + 1)) ^ 2 := by
    convert he using 1; ring
  have ht := iterate_terminal_analytic_material_error_bound hs1 hb hu
    (iterate_hessian_factor_continuousOn hv hQc w) w i hB
    (by positivity : 0 ≤ 4 * Qmax * Gprev) hGc hr hL hgain D hD hjet hea hcur
  convert ht using 1; ring

end AVenhance.Infra.Section4
