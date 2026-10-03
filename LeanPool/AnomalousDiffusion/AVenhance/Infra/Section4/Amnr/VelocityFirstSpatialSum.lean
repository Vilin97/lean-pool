/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.StreamFirstMaterialSpatial

/-! Scale summation for every spatial first-material velocity jet. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- A smooth global difference commutes with every actual word. -/
theorem amnrWord_sub_global {b : AmnrSpace → Vec 2} {f g : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (w : List (Option (Fin 2))) :
    amnrWord b w (f - g) = amnrWord b w f - amnrWord b w g := by
  funext z
  exact amnrWord_sub isOpen_univ
    (hb.of_le (show (w.length : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).contDiffOn
    (hf.of_le (show (w.length : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).contDiffOn
    (hg.of_le (show (w.length : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).contDiffOn
    w le_rfl (mem_univ z)

end AVenhance.Infra.Section4
