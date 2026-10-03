/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureFluxEvolution

/-! # Word Linear Calculus

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

theorem amnrWord_add {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f g : AmnrSpace → ℝ} {N : ℕ}
    (hb : ContDiffOn ℝ N b U) (hf : ContDiffOn ℝ N f U)
    (hg : ContDiffOn ℝ N g U) (w : List (Option (Fin 2))) (hw : w.length ≤ N) :
    Set.EqOn (amnrWord b w (f + g)) (amnrWord b w f + amnrWord b w g) U := by
  induction w with
  | nil => intro z _; rfl
  | cons d w ih =>
    have hwN : w.length ≤ N := by simp only [List.length_cons] at hw; omega
    intro z hz
    have hnear := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy => ih hwN hy)
    have hf' := (amnrWord_contDiffOn hU hb hf w (n := 1)
      (by simp only [List.length_cons] at hw; omega)).contDiffAt (hU.mem_nhds hz)
    have hg' := (amnrWord_contDiffOn hU hb hg w (n := 1)
      (by simp only [List.length_cons] at hw; omega)).contDiffAt (hU.mem_nhds hz)
    unfold amnrWord amnrOp
    rw [hnear.fderiv_eq, fderiv_add (hf'.differentiableAt (by norm_num))
      (hg'.differentiableAt (by norm_num))]
    rfl

end AVenhance.Infra.Section4
