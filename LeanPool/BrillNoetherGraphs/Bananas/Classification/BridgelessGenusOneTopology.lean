/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Classification.BridgelessGenusTwoTopology

/-!
# Bridgeless genus-one topology

The intrinsic genus-one factors in the genus-two wedge normal form are
two-regular.  This is the numerical cycle property needed by an explicit
cycle-presentation construction.
-/

namespace Bananas

open Utilities

/-- Every vertex of a nontrivial bridgeless genus-one graph is bivalent. -/
theorem vertex_degree_eq_two_of_bridgeless_genus_one
    (G : CFGraph) (hCut : TwoEdgeCutCondition G)
    (hNontrivial : ∃ p q : G.V, p ≠ q) (hGenus : genus G = 1)
    (vertex : G.V) : vertex_degree G vertex = 2 := by
  let hMin := hasMinimumValenceTwo_of_twoEdgeCutCondition G hCut hNontrivial
  have hSum := sum_vertex_degree_sub_two G
  rw [hGenus] at hSum
  have hNonneg : ∀ v ∈ (Finset.univ : Finset G.V),
      0 ≤ vertex_degree G v - 2 := by
    intro v _
    have hLower := hMin v
    omega
  have hEach := (Finset.sum_eq_zero_iff_of_nonneg hNonneg).mp hSum
  have hZero : vertex_degree G vertex - 2 = 0 :=
    hEach vertex (Finset.mem_univ _)
  have hLower := hMin vertex
  omega

end Bananas
