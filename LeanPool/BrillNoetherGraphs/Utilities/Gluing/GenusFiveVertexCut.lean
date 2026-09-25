/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.ElementaryExistence
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeRankOne
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeContraction
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexCutConnectivity
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.PointedGenusOneRigidTransport

/-!
# Rank one across a positive-genus articulation in genus five

The unmarked genus-five structural exit is considerably simpler than its
once-marked ancestor.  The two factors have genera `(1,4)` or `(2,3)`, up to
order.  The genus-at-most-three factor carries its elementary critical pencil,
the genus-four factor uses the supplied genus-four theorem, and bridge gluing
followed by contraction of the artificial bridge loses exactly one degree.
-/

@[expose] public section
namespace Utilities

universe u

private theorem elementary_rank_one_pencil
    (G : CFGraph.{u}) (hConnected : graphConnected G)
    (g d : ℤ) (hGenus : genus G = g)
    (hRho : 0 ≤ g - 2 * (g - d + 1))
    (hWidth : g - d + 1 ≤ 1) :
    BNExists G 1 d := by
  apply BNExists_elementary hConnected
  · norm_num
  · simpa [bnNumber, rectangleWidth, hGenus] using hRho
  · right
    simpa [rectangleWidth, hGenus] using hWidth

/-- Rank-one pencils on two factors glue on their vertex wedge with the
bridge correction: the resulting degree is one less than the sum. -/
theorem BNExists_vertexWedge_rank_one_bridge_corrected
    (G H : CFGraph.{u}) (x : G.V) (y : H.V)
    {dG dH : ℤ} (hG : BNExists G 1 dG) (hH : BNExists H 1 dH) :
    BNExists (vertexWedge G H x y) 1 (dG + dH - 1) := by
  apply (BNExists_bridge_iff_vertexWedge G H x y 1 (dG + dH - 1)).mp
  exact MarkedGraphs.BNExists_bridgeGraph_rank_one G H x y hG hH

/-- Attaching a pointed rigid genus-one factor to a genus-four graph raises
the critical pencil degree from three to four. -/
theorem BNExists_vertexWedge_one_four_of_genus_four
    (genusFour : ∀ (G : CFGraph.{u}), graphConnected G → genus G = 4 →
      BNExists G 1 3)
    (G H : CFGraph.{u}) (x : G.V) (y : H.V)
    (hGConnected : graphConnected G) (hGGenus : genus G = 4)
    (hHRigid : PointedGenusOneRigid H y) :
    BNExists (vertexWedge G H x y) 1 4 := by
  have hG : BNExists G 1 3 := genusFour G hGConnected hGGenus
  have hH : BNExists H 1 2 :=
    elementary_rank_one_pencil H hHRigid.connected 1 2 hHRigid.genus_one
      (by norm_num) (by norm_num)
  simpa using BNExists_vertexWedge_rank_one_bridge_corrected G H x y hG hH

/-- Any positive-genus one-vertex decomposition of a connected genus-five
graph supplies a degree-four rank-one divisor, assuming only the genus-four
critical pencil theorem in the same universe. -/
theorem BNExists_one_four_of_positiveGenus_oneVertexCut
    (genusFour : ∀ (G : CFGraph.{u}), graphConnected G → genus G = 4 →
      BNExists G 1 3)
    (K : CFGraph.{u}) (hConnected : graphConnected K) (hGenus : genus K = 5)
    (cut : OneVertexCut K)
    (hLeftPos : 0 < genus cut.leftGraph)
    (hRightPos : 0 < genus cut.rightGraph) :
    BNExists K 1 4 := by
  have hFactors := cut.graph_connected_factors hConnected
  have hAdd := cut.genus_eq
  rw [hGenus] at hAdd
  have hCases :
      (genus cut.leftGraph = 1 ∧ genus cut.rightGraph = 4) ∨
      (genus cut.leftGraph = 2 ∧ genus cut.rightGraph = 3) ∨
      (genus cut.leftGraph = 3 ∧ genus cut.rightGraph = 2) ∨
      (genus cut.leftGraph = 4 ∧ genus cut.rightGraph = 1) := by
    omega
  apply (cut.BNExists_iff 1 4).mpr
  rcases hCases with hOneFour | hTwoThree | hThreeTwo | hFourOne
  · have hLeft : BNExists cut.leftGraph 1 2 :=
      elementary_rank_one_pencil cut.leftGraph hFactors.1 1 2 hOneFour.1
        (by norm_num) (by norm_num)
    have hRight : BNExists cut.rightGraph 1 3 :=
      genusFour cut.rightGraph hFactors.2 hOneFour.2
    simpa using BNExists_vertexWedge_rank_one_bridge_corrected
      cut.leftGraph cut.rightGraph cut.leftGlue cut.rightGlue hLeft hRight
  · have hLeft : BNExists cut.leftGraph 1 2 :=
      elementary_rank_one_pencil cut.leftGraph hFactors.1 2 2 hTwoThree.1
        (by norm_num) (by norm_num)
    have hRight : BNExists cut.rightGraph 1 3 :=
      elementary_rank_one_pencil cut.rightGraph hFactors.2 3 3 hTwoThree.2
        (by norm_num) (by norm_num)
    simpa using BNExists_vertexWedge_rank_one_bridge_corrected
      cut.leftGraph cut.rightGraph cut.leftGlue cut.rightGlue hLeft hRight
  · have hLeft : BNExists cut.leftGraph 1 3 :=
      elementary_rank_one_pencil cut.leftGraph hFactors.1 3 3 hThreeTwo.1
        (by norm_num) (by norm_num)
    have hRight : BNExists cut.rightGraph 1 2 :=
      elementary_rank_one_pencil cut.rightGraph hFactors.2 2 2 hThreeTwo.2
        (by norm_num) (by norm_num)
    simpa using BNExists_vertexWedge_rank_one_bridge_corrected
      cut.leftGraph cut.rightGraph cut.leftGlue cut.rightGlue hLeft hRight
  · have hLeft : BNExists cut.leftGraph 1 3 :=
      genusFour cut.leftGraph hFactors.1 hFourOne.1
    have hRight : BNExists cut.rightGraph 1 2 :=
      elementary_rank_one_pencil cut.rightGraph hFactors.2 1 2 hFourOne.2
        (by norm_num) (by norm_num)
    simpa using BNExists_vertexWedge_rank_one_bridge_corrected
      cut.leftGraph cut.rightGraph cut.leftGlue cut.rightGlue hLeft hRight

end Utilities
