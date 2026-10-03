/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.WordLinearCalculus

/-! Applying a finite outer word to the primitive gradient PDE. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Finite-order flux regularity suffices to differentiate the primitive PDE.
The two spatial letters are retained explicitly for the budget accounting. -/
theorem amnr_gradient_material_word_equation {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} (hb : ContDiffOn ℝ (⊤ : ℕ∞) b U)
    {g F : Fin 2 → AmnrSpace → ℝ} (hg : ∀ p, ContDiffOn ℝ (⊤ : ℕ∞) (g p) U)
    {N : ℕ} (hF : ∀ q, ContDiffOn ℝ N (F q) U) {κ : ℝ} (p : Fin 2)
    (hEq : EqOn (amnrOp b none (g p))
      (fun z => κ * (∑ q : Fin 2, amnrWord b [some q, some q] (g p) z) +
        (∑ q : Fin 2, amnrWord b [some p, some q] (F q) z) -
        ∑ q : Fin 2, amnrVelocityGradient b q p z * g q z) U)
    (w : List (Option (Fin 2))) (hw : w.length + 2 ≤ N) :
    EqOn (amnrWord b (w ++ [none]) (g p))
      (fun z => κ * (∑ q : Fin 2, amnrWord b (w ++ [some q, some q]) (g p) z) +
        (∑ q : Fin 2, amnrWord b (w ++ [some p, some q]) (F q) z) -
        amnrWord b w (fun y => ∑ q : Fin 2, amnrVelocityGradient b q p y * g q y) z) U := by
  let M := N - 2
  have hbM : ContDiffOn ℝ M b U := hb.of_le (by simp)
  have hwl : w.length ≤ M := by dsimp [M]; omega
  have hgD (q : Fin 2) : ContDiffOn ℝ M (amnrWord b [some q, some q] (g p)) U :=
    (amnrWord_contDiffOn_infty hU hb (hg p) _).of_le (by simp)
  have hFD (q : Fin 2) : ContDiffOn ℝ M (amnrWord b [some p, some q] (F q)) U :=
    amnrWord_contDiffOn hU (hb.of_le (by simp)) (hF q) _ (by dsimp [M]; omega)
  have hBg (q : Fin 2) : ContDiffOn ℝ M (amnrVelocityGradient b q p * g q) U :=
    ((amnrVelocityGradient_contDiffOn_infty hU hb q p).mul (hg q)).of_le (by simp)
  have hGsum : ContDiffOn ℝ M (fun z => ∑ q : Fin 2, amnrWord b [some q, some q] (g p) z) U :=
    ContDiffOn.sum (fun q _ => hgD q)
  have hFsum : ContDiffOn ℝ M (fun z => ∑ q : Fin 2, amnrWord b [some p, some q] (F q) z) U :=
    ContDiffOn.sum (fun q _ => hFD q)
  have hBsum : ContDiffOn ℝ M (fun z => ∑ q : Fin 2, amnrVelocityGradient b q p z * g q z) U :=
    ContDiffOn.sum (fun q _ => hBg q)
  intro z hz
  rw [amnrWord_append]
  change amnrWord b w (amnrOp b none (g p)) z = _
  rw [amnrWord_congr hU hEq w hz]
  have hsub := amnrWord_sub hU hbM (hGsum.const_smul κ |>.add hFsum) hBsum w hwl hz
  have hadd := amnrWord_add hU hbM (hGsum.const_smul κ) hFsum w hwl hz
  change amnrWord b w (fun y => κ * (∑ q : Fin 2, amnrWord b [some q, some q] (g p) y) +
    (∑ q : Fin 2, amnrWord b [some p, some q] (F q) y) -
    ∑ q : Fin 2, amnrVelocityGradient b q p y * g q y) z = _ at hsub
  rw [hsub]
  simp only [Pi.sub_apply, smul_eq_mul]
  change amnrWord b w (fun y => κ * (∑ q : Fin 2, amnrWord b [some q, some q] (g p) y) +
    ∑ q : Fin 2, amnrWord b [some p, some q] (F q) y) z = _ at hadd
  rw [hadd]
  simp only [Pi.add_apply, smul_eq_mul]
  have hscale := congrFun (amnrWord_const_smul b κ w
    (fun y => ∑ q : Fin 2, amnrWord b [some q, some q] (g p) y)) z
  change amnrWord b w (fun y => κ * ∑ q : Fin 2, amnrWord b [some q, some q] (g p) y) z = _
      at hscale
  rw [hscale]
  simp only [Pi.smul_apply, smul_eq_mul]
  have heG := amnrWord_sum hU hbM Finset.univ
    (fun q => amnrWord b [some q, some q] (g p)) (fun q _ => hgD q) w hwl hz
  have heF := amnrWord_sum hU hbM Finset.univ
    (fun q => amnrWord b [some p, some q] (F q)) (fun q _ => hFD q) w hwl hz
  simp only [Finset.sum_fn] at heG heF
  rw [heG, heF]
  simp only [amnrWord_append]

end AVenhance.Infra.Section4
