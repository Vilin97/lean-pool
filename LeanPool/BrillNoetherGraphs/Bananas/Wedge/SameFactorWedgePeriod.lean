/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Wedge.SameFactorWedgeRight
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TorsionOrderExact
import LeanPool.BrillNoetherGraphs.Bananas.Wedge.WedgeTorsionRestriction

/-!
# The period in the same-factor wedge exception
-/

namespace Bananas

open Utilities

theorem same_leftFactor_kGeneral_period_eq_two
    (G H : CFGraph) (x u : G.V) (y : H.V) (k : ℕ)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hCut : TwoEdgeCutCondition G) (hCard : Fintype.card G.V = 2)
    (hxu : x ≠ u)
    (hK : KGeneralTransmission
      (mark (vertexWedge G H x y) (Sum.inl x) (Sum.inl u)) k) :
    k = 2 := by
  have hConn : _root_.graphConnected (vertexWedge G H x y) :=
    graph_connected_vertexWedge G H x y hG.connected hH.connected
  have hPos : 0 < genus (vertexWedge G H x y) := by
    rw [genus_vertexWedge, hG.genus_one, hH.genus_one]
    norm_num
  have hDistinct : (Sum.inl x : (vertexWedge G H x y).V) ≠ Sum.inl u := by
    simpa using hxu
  have hKOrder := hK.isTorsionOrder hDistinct hConn hPos
  have hTwo := same_leftFactor_wedge_isTorsionOrder_two
    G H x u y hG hCut hCard hxu
  exact hKOrder.eq_of_same_marked_graph hTwo

theorem same_rightFactor_kGeneral_period_eq_two
    (G H : CFGraph) (x : G.V) (y p : H.V) (k : ℕ)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hCut : TwoEdgeCutCondition H) (hCard : Fintype.card H.V = 2)
    (hpy : p ≠ y)
    (hK : KGeneralTransmission (mark (vertexWedge G H x y)
      (wedgeRightVertex G H x y y) (wedgeRightVertex G H x y p)) k) :
    k = 2 := by
  have hConn : _root_.graphConnected (vertexWedge G H x y) :=
    graph_connected_vertexWedge G H x y hG.connected hH.connected
  have hPos : 0 < genus (vertexWedge G H x y) := by
    rw [genus_vertexWedge, hG.genus_one, hH.genus_one]
    norm_num
  have hDistinct : wedgeRightVertex G H x y y ≠ wedgeRightVertex G H x y p := by
    rw [wedgeRightVertex_marked, wedgeRightVertex_unmarked G H x y p hpy]
    simp
  have hKOrder := hK.isTorsionOrder hDistinct hConn hPos
  have hTwo := same_rightFactor_wedge_isTorsionOrder_two
    G H x y p hH hCut hCard hpy
  exact hKOrder.eq_of_same_marked_graph hTwo

end Bananas
