/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.ScalarQuadraticL2

/-! Exact finite-order spatial slice bridges for the actual flux. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Spatial words require only their own ordinary derivative count; they do
not infer infinite joint regularity from the finite source coefficient. -/
theorem amnrWord_spatial_slice_on_vertical_domain_finite {U : Set AmnrSpace}
    (hU : IsOpen U) {f : AmnrSpace → ℝ} {N : ℕ} (hf : ContDiffOn ℝ N f U)
    (b : AmnrSpace → Vec 2) (α : List (Fin 2)) (hα : α.length ≤ N) (t : ℝ)
    (hvertical : ∀ x, (t, x) ∈ U) (x : Vec 2) :
    amnrWord b (α.map some) f (t, x) = amnrSpaceWord α (fun y => f (t, y)) x := by
  rw [amnrWord_spatial_independent b (fun _ => (0 : Vec 2)) α f]
  induction α generalizing x with
  | nil => rfl
  | cons i α ih =>
    have hlen : α.length ≤ N := by simp only [List.length_cons] at hα; omega
    have hg := amnrWord_contDiffOn hU
      (contDiffOn_const : ContDiffOn ℝ N (fun _ : AmnrSpace => (0 : Vec 2)) U)
      hf (α.map some) (n := 1)
      (by simp only [List.length_map, List.length_cons] at hα ⊢; omega)
    have hd := (hg.contDiffAt (hU.mem_nhds (hvertical x))).differentiableAt (by norm_num)
    simp only [List.map_cons, amnrWord]
    rw [amnrOp_space hd i]
    have heq : (fun y => amnrWord (fun _ => (0 : Vec 2)) (α.map some) f (t, y)) =
        amnrSpaceWord α (fun y => f (t, y)) := funext (ih hlen)
    rw [heq]
    rfl

end AVenhance.Infra.Section4
