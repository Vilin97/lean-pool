/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDriftExpansion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordSplitPrincipal

/-! Every material commutator contains a positive-order velocity jet. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The velocity commutator has exactly the nonprincipal ordered splits. -/
theorem iterateWordMaterialError_lower_velocity
    {b : ℝ → Vec 2 → Vec 2} {u : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 < t) (w : List (Fin 2)) (x : Vec 2) :
    iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
      (fun z => u z.1 z.2) (t, x) =
      ∑ j : Fin 2, (((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty)).map (fun p =>
        iterateSpatialWord p.1 (fun y => b t y j) x *
        spaceGrad (iterateSpatialWord p.2 (u t)) x j)).sum := by
  rw [iterateWordMaterialError_transport hb hu ht]
  have hs (j : Fin 2) : ((iterateSpatialSplits w).map (fun p =>
      iterateSpatialWord p.1 (fun y => b t y j) x *
        spaceGrad (iterateSpatialWord p.2 (u t)) x j)).sum =
      b t x j * spaceGrad (iterateSpatialWord w (u t)) x j +
      (((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty)).map (fun p =>
        iterateSpatialWord p.1 (fun y => b t y j) x *
        spaceGrad (iterateSpatialWord p.2 (u t)) x j)).sum := by
    rw [iterate_split_list_sum (iterateSpatialSplits w) _ (fun p => p.1.isEmpty),
      iterateSpatialSplits_nil_left]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      iterateSpatialWord]
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  unfold vecDot
  ring

end AVenhance.Infra.Section4
