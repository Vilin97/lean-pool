/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Classification.GenusTwoReduction
public import LeanPool.BrillNoetherGraphs.Bananas.Basics.DegreeOneRepresentatives

/-!
# Normal form for a theta counterexample

This connects the general rank-theoretic reduction to the strand geometry.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- A negative marked second difference on a theta graph has, after deleting
the first marked chip, a unique vertex-chip representative. -/
theorem theta_negative_rankDelta_normal_form
    (B : Banana 2) (u v : B.graph.V) (huv : u ≠ v)
    (D : CFDiv B.graph)
    (hNeg : rankDelta (mark B.graph u v) D < 0) :
    ∃! w : B.graph.V, linearEquiv B.graph
      (D - oneChip u) (oneChip w) := by
  let M := mark B.graph u v
  have hDistinct : ¬ linearEquiv B.graph (oneChip u - oneChip v) 0 :=
    marks_not_linearEquiv (by omega) B huv
  have hReduced := degree_and_rank_eq_of_rankDelta_neg_genus_two M D
    (graphConnected B) B.genus_graph hDistinct hNeg
  obtain ⟨hDu, _, _⟩ := (rankDelta_neg_iff_rank_pattern M D).mp hNeg
  dsimp [M] at hReduced hDu
  change deg D = 2 ∧ rank B.graph D = 0 at hReduced
  change rank B.graph D = rank B.graph (D - oneChip u) at hDu
  have hDu' : rank B.graph D = rank B.graph (D - oneChip u) := by
    exact hDu
  have hRankD : rank B.graph D = 0 := by
    exact hReduced.2
  have hDegreeD : deg D = 2 := by
    exact hReduced.1
  have hDuRank : rank B.graph (D - oneChip u) = 0 := by
    rw [← hDu']
    exact hRankD
  have hDuDegree : deg (D - oneChip u) = 1 := by
    rw [deg.map_sub, deg_one_chip]
    omega
  obtain ⟨w, hw⟩ :=
    exists_one_chip_representative_of_rank_zero_degree_one B.graph
      (D - oneChip u) hDuRank hDuDegree
  refine ⟨w, hw, ?_⟩
  intro w' hw'
  exact one_chip_representative_unique_on_banana (by omega) B
    (D := D - oneChip u) (x := w) (y := w') hw hw' |>.symm

end Bananas
