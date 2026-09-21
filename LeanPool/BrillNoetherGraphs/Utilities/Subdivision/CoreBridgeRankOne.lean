/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.ElementaryExistence
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeRankOne
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreBridgeCut

/-!
# Rank one across a checked genus-two/genus-two core bridge

A separating core slot remains a separating unit edge in every positive
subdivision.  When its two induced factors have genus two, elementary
Brill--Noether existence supplies degree-two pencils on the factors and the
bridge gluing theorem removes one chip.  The result is a degree-three pencil
on the original subdivision, uniformly in all positive slot lengths.

This is the structural shortcut used by the first Draisma--Vargas genus-four
type.  It is independent of that application and of any finite cone cover.
-/

namespace MarkedGraphs.Certificate.CoreBridgeCut.Data

open Utilities
open Utilities.Certificate
open Utilities.Certificate.CoreVertexCut.Data

variable {n p : ℕ}
  {spec : SubdivisionGraph.Spec n p}
  (cutData : CoreBridgeCut.Data spec.core)

private theorem genusTwo_bnExists
    {G : CFGraph} (hConnected : graph_connected G) (hGenus : genus G = 2) :
    BNExists G 1 2 := by
  apply BNExists_elementary hConnected
  · norm_num
  · simp [bnNumber, rectangleWidth, hGenus]
  · right
    simp [rectangleWidth, hGenus]

/-- A valid separating core edge with two genus-two sides gives a
degree-three rank-one divisor on every positive subdivision of that core. -/
theorem bnExists_one_three_of_two_two
    (hValid : cutData.Valid) (hConnected : graph_connected spec.graph)
    (hLeft : cutData.toCoreVertexCut.leftGenus = 2)
    (hRight : cutData.toCoreVertexCut.rightGenus = 2) :
    BNExists spec.graph 1 3 := by
  let cut := cutData.toOneBridgeCut spec hValid
  have hFactors := cut.graph_connected_factors_of_connected hConnected
  have hLeftGenus : genus cut.leftGraph = 2 := by
    dsimp only [cut]
    rw [cutData.leftGraph_genus spec hValid, hLeft]
  have hAmbientGenus : genus spec.graph = 4 := by
    have hSum := cutData.toCoreVertexCut.leftGenus_add_rightGenus_eq_graph_genus
      spec (cutData.toCoreVertexCut_valid hValid)
    rw [hLeft, hRight] at hSum
    omega
  have hRightGenus : genus cut.rightGraph = 2 := by
    dsimp only [cut]
    rw [cutData.rightGraph_genus_eq spec hValid, hAmbientGenus, hLeft]
    norm_num
  have hLeftBN : BNExists cut.leftGraph 1 2 :=
    genusTwo_bnExists hFactors.1 hLeftGenus
  have hRightBN : BNExists cut.rightGraph 1 2 :=
    genusTwo_bnExists hFactors.2 hRightGenus
  have hBridge : BNExists cut.bridgeGraph 1 3 := by
    change BNExists (bridgeGraph cut.leftGraph cut.rightGraph
      cut.leftGlue cut.rightGlue) 1 3
    simpa using MarkedGraphs.BNExists_bridgeGraph_rank_one
      cut.leftGraph cut.rightGraph cut.leftGlue cut.rightGlue hLeftBN hRightBN
  exact (cut.laplacianEquiv.bnExists_iff 1 3).mp hBridge

end MarkedGraphs.Certificate.CoreBridgeCut.Data
