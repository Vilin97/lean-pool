/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocityRegularity

/-! Joint initial-time regularity of the actual explicit lower velocity sum. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem IteratesVelocitySmooth.velocity_contDiffOn_list {α : Type*} (P : List α)
    (f : α → AmnrSpace → ℝ) (S : Set AmnrSpace)
    (hf : ∀ p ∈ P, ContDiffOn ℝ (⊤ : ℕ∞) (f p) S) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (P.map (fun p => f p z)).sum) S := by
  induction P with
  | nil => exact contDiffOn_const
  | cons p P ih =>
    exact (hf p List.mem_cons_self).add (ih
      (fun q hq => hf q (List.mem_cons_of_mem p hq)))

/-- The explicit velocity sum is smooth jointly up to zero. This supplies a
 regular representative of the actual material error on the positive cell. -/
theorem iterateVelocitySplit_smooth_up_to_initial
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (P : List (List (Fin 2) × List (Fin 2))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => iterateVelocitySplit P (b z.1) (v z.1) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  unfold iterateVelocitySplit
  apply ContDiffOn.sum
  intro j _
  apply IteratesVelocitySmooth.velocity_contDiffOn_list
  intro p _
  exact (iterateSpatialWord_smooth_up_to_initial (u := fun t x => b t x j)
    (contDiffOn_pi.mp hb j) p.1).mul
    (contDiffOn_pi.mp (iterate_word_gradient_smooth_up_to_initial hv p.2) j)

end AVenhance.Infra.Section4
