/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointInversions

/-!
# Endpoint values of the banana rank second difference

This file completes Corollary 2.25(1): on the two multivalent endpoints, the
rank second difference of the `a`-fold endpoint pencil is one through genus
and zero afterwards.
-/

namespace Bananas

open Utilities

open Utilities Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- Paper Corollary 2.25(1) (`cor-BananaDeltaComps`). -/
theorem rankDelta_endpointPencil_nsmul
    {g : ℕ} (B : Banana g) (a : ℕ) :
    rankDelta (mark B.graph (leftEndpoint B) (rightEndpoint B))
        (a • endpointPencilDivisor B) =
      if a ≤ g then 1 else 0 := by
  by_cases ha : a ≤ g
  · rw [rankDelta_endpointPencil_nsmul_eq_one B a ha]
    simp [ha]
  · have hag : g < a := by omega
    have hagZ : (g : ℤ) < (a : ℤ) := by exact_mod_cast hag
    let D : CFDiv B.graph := a • endpointPencilDivisor B
    have hDegreeD : deg D = 2 * (a : ℤ) := by
      dsimp [D]
      rw [map_nsmul, degree_endpointPencilDivisor]
      ring
    have hDegreeLeft :
        deg (D - oneChip (leftEndpoint B)) = 2 * (a : ℤ) - 1 := by
      rw [deg.map_sub, hDegreeD, deg_one_chip]
    have hDegreeRight :
        deg (D - oneChip (rightEndpoint B)) = 2 * (a : ℤ) - 1 := by
      rw [deg.map_sub, hDegreeD, deg_one_chip]
    have hDegreeBoth :
        deg (D - oneChip (leftEndpoint B) - oneChip (rightEndpoint B)) =
          2 * (a : ℤ) - 2 := by
      rw [deg.map_sub, hDegreeLeft, deg_one_chip]
      omega
    have hRankD : rank B.graph D = 2 * (a : ℤ) - (g : ℤ) := by
      have h := (rank_nonspecial_range (banana_graph_connected B) D).2.2 (by
        rw [hDegreeD, banana_genus]
        omega)
      rw [hDegreeD, banana_genus] at h
      exact h
    have hRankLeft :
        rank B.graph (D - oneChip (leftEndpoint B)) =
          2 * (a : ℤ) - 1 - (g : ℤ) := by
      have h := (rank_nonspecial_range (banana_graph_connected B)
        (D - oneChip (leftEndpoint B))).2.2 (by
          rw [hDegreeLeft, banana_genus]
          omega)
      rw [hDegreeLeft, banana_genus] at h
      exact h
    have hRankRight :
        rank B.graph (D - oneChip (rightEndpoint B)) =
          2 * (a : ℤ) - 1 - (g : ℤ) := by
      have h := (rank_nonspecial_range (banana_graph_connected B)
        (D - oneChip (rightEndpoint B))).2.2 (by
          rw [hDegreeRight, banana_genus]
          omega)
      rw [hDegreeRight, banana_genus] at h
      exact h
    have hRankBoth :
        rank B.graph
            (D - oneChip (leftEndpoint B) - oneChip (rightEndpoint B)) =
          2 * (a : ℤ) - 2 - (g : ℤ) := by
      have h := (rank_nonspecial_range (banana_graph_connected B)
        (D - oneChip (leftEndpoint B) - oneChip (rightEndpoint B))).2.2 (by
          rw [hDegreeBoth, banana_genus]
          omega)
      rw [hDegreeBoth, banana_genus] at h
      exact h
    have hDelta : rankDelta
        (mark B.graph (leftEndpoint B) (rightEndpoint B)) D = 0 := by
      unfold rankDelta mark
      rw [hRankD, hRankLeft, hRankRight, hRankBoth]
      ring
    change rankDelta (mark B.graph (leftEndpoint B) (rightEndpoint B)) D = _
    rw [hDelta]
    simp [ha]

end Bananas
