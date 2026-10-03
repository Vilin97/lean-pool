/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureLaplacian

/-! Explicit spatial/material commutators used in the temperature cascade. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Every finite ordered word preserves classical smoothness on an open domain. -/
theorem amnrWord_contDiffOn_infty {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (w : List (Option (Fin 2))) : ContDiffOn ℝ (⊤ : ℕ∞) (amnrWord b w f) U := by
  apply contDiffOn_infty.mpr
  intro N
  exact amnrWord_contDiffOn hU (hb.of_le (by simp)) (hf.of_le (by simp)) w
    (N := N + w.length) (n := N) le_rfl

/-- Primitive velocity gradients are smooth from the velocity itself. -/
theorem amnrVelocityGradient_contDiffOn_infty {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} (hb : ContDiffOn ℝ (⊤ : ℕ∞) b U) (i p : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (amnrVelocityGradient b i p) U := by
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => b z i) U := (contDiffOn_pi.mp hb) i
  have hg := amnrWord_contDiffOn_infty hU hb hf [some p]
  apply hg.congr
  intro z hz
  exact (amnrOp_space ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) p).symm

/-- Pure spatial words do not depend on the velocity chosen for the material
letter, so diffusion can be written with the actual advecting field. -/
theorem amnrWord_spatial_independent (b c : AmnrSpace → Vec 2)
    (α : List (Fin 2)) (f : AmnrSpace → ℝ) :
    amnrWord b (α.map some) f = amnrWord c (α.map some) f := by
  induction α with
  | nil => rfl
  | cons i α ih =>
    simp only [List.map_cons, amnrWord]
    rw [ih]
    rfl

end AVenhance.Infra.Section4
