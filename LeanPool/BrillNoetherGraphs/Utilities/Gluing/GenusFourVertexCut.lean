/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.ElementaryExistence
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeContraction
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeRankOne
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.GenusThreeCycleWedge
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexCutConnectivity

/-!
# Genus-four rank one across a one-vertex cut

The two structural alternatives used by the finite genus-four cut checker are
entirely graph-theoretic.  Two genus-two factors glue with one chip saved;
a genus-three factor and a pointed rigid genus-one factor glue without adding
a chip.  This module keeps those statements in the public gluing layer.
-/

namespace Utilities

universe u v

private theorem genusTwo_bnExists {G : CFGraph} (hConnected : graph_connected G)
    (hGenus : genus G = 2) : BNExists G 1 2 := by
  apply BNExists_elementary hConnected
  · norm_num
  · simp [bnNumber, rectangleWidth, hGenus]
  · right
    simp [rectangleWidth, hGenus]

/-- Two connected genus-two factors carry a degree-three pencil on their
vertex wedge. -/
theorem BNExists_vertexWedge_rankOneDegreeThree_of_genus_two_two
    (G : CFGraph.{u}) (H : CFGraph.{v})
    (hG : graph_connected G) (hH : graph_connected H)
    (hGenusG : genus G = 2) (hGenusH : genus H = 2)
    (x : G.V) (y : H.V) :
    BNExists (vertexWedge G H x y) 1 3 := by
  have hBridge : BNExists (bridgeGraph G H x y) 1 3 := by
    simpa using MarkedGraphs.BNExists_bridgeGraph_rank_one G H x y
      (genusTwo_bnExists hG hGenusG) (genusTwo_bnExists hH hGenusH)
  exact (BNExists_bridge_iff_vertexWedge G H x y 1 3).mp hBridge

end Utilities

namespace Utilities.OneVertexCut

open Utilities

variable {K : CFGraph.{u}} (cut : OneVertexCut K)

/-- A connected graph split into two genus-two induced factors carries a
degree-three rank-one divisor. -/
theorem BNExists_rankOneDegreeThree_of_genus_two_two
    (hK : graph_connected K)
    (hLeftGenus : genus cut.leftGraph = 2)
    (hRightGenus : genus cut.rightGraph = 2) :
    BNExists K 1 3 := by
  apply (cut.BNExists_iff 1 3).mpr
  exact Utilities.BNExists_vertexWedge_rankOneDegreeThree_of_genus_two_two
    cut.leftGraph cut.rightGraph
    (cut.graph_connected_left_of_connected hK)
    (cut.graph_connected_right_of_connected hK)
    hLeftGenus hRightGenus cut.leftGlue cut.rightGlue

/-- A connected genus-three left factor and a pointed rigid genus-one right
factor give the ambient degree-three pencil. -/
theorem BNExists_rankOneDegreeThree_of_left_three_right_rigid_one
    (hK : graph_connected K)
    (hLeftGenus : genus cut.leftGraph = 3)
    (hRightRigid : PointedGenusOneRigid cut.rightGraph cut.rightGlue) :
    BNExists K 1 3 := by
  apply (cut.BNExists_iff 1 3).mpr
  exact MarkedGraphs.BNExists_vertexWedge_rankOneDegreeThree_of_genus_three
    cut.leftGraph cut.rightGraph cut.leftGlue cut.rightGlue
    (cut.graph_connected_left_of_connected hK) hLeftGenus hRightRigid

/-- Symmetric `(1,3)` form, obtained by exchanging the two sides. -/
theorem BNExists_rankOneDegreeThree_of_left_rigid_one_right_three
    (hK : graph_connected K)
    (hLeftRigid : PointedGenusOneRigid cut.leftGraph cut.leftGlue)
    (hRightGenus : genus cut.rightGraph = 3) :
    BNExists K 1 3 := by
  exact cut.swap.BNExists_rankOneDegreeThree_of_left_three_right_rigid_one
    hK hRightGenus hLeftRigid

end Utilities.OneVertexCut
