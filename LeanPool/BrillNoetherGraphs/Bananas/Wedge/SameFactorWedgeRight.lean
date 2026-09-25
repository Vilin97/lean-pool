/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Wedge.SameFactorWedgeKGeneral
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.ChainTwoLoopsSameRight

/-!
# Right-factor form of the same-factor wedge exception

This is the factor-symmetric transport of the left-factor theorems across
the explicit commutativity isomorphism for vertex wedges.
-/

@[expose] public section

namespace Bananas

open Utilities

theorem same_rightFactor_marks_of_allSubmodular
    (G H : CFGraph) (x : G.V) (y p q : H.V)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hCut : TwoEdgeCutCondition H)
    (hSub : AllSubmodular (mark (vertexWedge G H x y)
      (wedgeRightVertex G H x y p) (wedgeRightVertex G H x y q))) :
    (p = y ∨ q = y) ∧ Fintype.card H.V ≤ 2 := by
  let W := vertexWedge G H x y
  let W' := vertexWedge H G y x
  let phi : CFGraphIso W W' := vertexWedgeComm G H x y
  let M := mark W (wedgeRightVertex G H x y p) (wedgeRightVertex G H x y q)
  let N := mark W' (Sum.inl p) (Sum.inl q)
  have hp : phi.vertexEquiv M.u = N.u := by
    change phi.vertexEquiv (wedgeRightVertex G H x y p) = Sum.inl p
    dsimp [phi]
    exact vertexWedge_comm_apply_right G H x y p
  have hq : phi.vertexEquiv M.v = N.v := by
    change phi.vertexEquiv (wedgeRightVertex G H x y q) = Sum.inl q
    dsimp [phi]
    exact vertexWedge_comm_apply_right G H x y q
  have hTransport : AllSubmodular N ↔ AllSubmodular M :=
    allSubmodular_map_of_marks_iff phi hp hq
  have hLeft : AllSubmodular N := hTransport.mpr hSub
  simpa only [N, W'] using
    same_leftFactor_marks_of_allSubmodular H G y p q x hH hG hCut hLeft

/-- The necessary right-factor conclusion for a general-transmission wedge. -/
theorem same_rightFactor_marks_of_kGeneral
    (G H : CFGraph) (x : G.V) (y p q : H.V) (k : ℕ)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hCut : TwoEdgeCutCondition H)
    (hK : KGeneralTransmission (mark (vertexWedge G H x y)
      (wedgeRightVertex G H x y p) (wedgeRightVertex G H x y q)) k) :
    (p = y ∨ q = y) ∧ Fintype.card H.V ≤ 2 :=
  same_rightFactor_marks_of_allSubmodular G H x y p q hG hH hCut hK.2.1

theorem same_rightFactor_wedge_twoGeneral
    (G H : CFGraph) (x : G.V) (y p : H.V)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hCut : TwoEdgeCutCondition H) (hCard : Fintype.card H.V = 2)
    (hpy : p ≠ y)
    (hSub : AllSubmodular (mark (vertexWedge G H x y)
      (wedgeRightVertex G H x y y) (wedgeRightVertex G H x y p))) :
    KGeneralTransmission (mark (vertexWedge G H x y)
      (wedgeRightVertex G H x y y) (wedgeRightVertex G H x y p)) 2 := by
  let W := vertexWedge G H x y
  let W' := vertexWedge H G y x
  let phi : CFGraphIso W W' := vertexWedgeComm G H x y
  let M := mark W (wedgeRightVertex G H x y y) (wedgeRightVertex G H x y p)
  let N := mark W' (Sum.inl y) (Sum.inl p)
  have hy : phi.vertexEquiv M.u = N.u := by
    change phi.vertexEquiv (wedgeRightVertex G H x y y) = Sum.inl y
    dsimp [phi]
    exact vertexWedge_comm_apply_right G H x y y
  have hp : phi.vertexEquiv M.v = N.v := by
    change phi.vertexEquiv (wedgeRightVertex G H x y p) = Sum.inl p
    dsimp [phi]
    exact vertexWedge_comm_apply_right G H x y p
  have hSubLeft : AllSubmodular N :=
    (allSubmodular_map_of_marks_iff phi hy hp).mpr hSub
  have hLeft : KGeneralTransmission N 2 := by
    simpa only [N, W'] using
      same_leftFactor_wedge_twoGeneral H G y p x hH hG hCut hCard hpy.symm hSubLeft
  exact (kGeneralTransmission_map_of_marks_iff phi hy hp 2).mp hLeft

/-- The two-vertex same-right-factor exception is automatically
two-general; this is the commuted form of the genus-one Riemann--Roch
left-factor theorem. -/
theorem same_rightFactor_wedge_twoGeneral_of_card_eq_two
    (G H : CFGraph) (x : G.V) (y p : H.V)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hCut : TwoEdgeCutCondition H) (hCard : Fintype.card H.V = 2)
    (hpy : p ≠ y) :
    KGeneralTransmission (mark (vertexWedge G H x y)
      (wedgeRightVertex G H x y y) (wedgeRightVertex G H x y p)) 2 := by
  let W := vertexWedge G H x y
  let W' := vertexWedge H G y x
  let phi : CFGraphIso W W' := vertexWedgeComm G H x y
  let M := mark W (wedgeRightVertex G H x y y) (wedgeRightVertex G H x y p)
  let N := mark W' (Sum.inl y) (Sum.inl p)
  have hy : phi.vertexEquiv M.u = N.u := by
    change phi.vertexEquiv (wedgeRightVertex G H x y y) = Sum.inl y
    dsimp [phi]
    exact vertexWedge_comm_apply_right G H x y y
  have hp : phi.vertexEquiv M.v = N.v := by
    change phi.vertexEquiv (wedgeRightVertex G H x y p) = Sum.inl p
    dsimp [phi]
    exact vertexWedge_comm_apply_right G H x y p
  have hLeft : KGeneralTransmission N 2 := by
    simpa only [N, W'] using
      same_leftFactor_wedge_twoGeneral_of_card_eq_two H G y p x
        hH hG hCut hCard hpy.symm
  exact (kGeneralTransmission_map_of_marks_iff phi hy hp 2).mp hLeft

theorem same_rightFactor_wedge_isTorsionOrder_two
    (G H : CFGraph) (x : G.V) (y p : H.V)
    (hH : PointedGenusOneRigid H y)
    (hCut : TwoEdgeCutCondition H) (hCard : Fintype.card H.V = 2)
    (hpy : p ≠ y) :
    IsTorsionOrder (mark (vertexWedge G H x y)
      (wedgeRightVertex G H x y y) (wedgeRightVertex G H x y p)) 2 := by
  let W := vertexWedge G H x y
  let W' := vertexWedge H G y x
  let phi : CFGraphIso W W' := vertexWedgeComm G H x y
  let M := mark W (wedgeRightVertex G H x y y) (wedgeRightVertex G H x y p)
  let N := mark W' (Sum.inl y) (Sum.inl p)
  have hy : phi.vertexEquiv M.u = N.u := by
    change phi.vertexEquiv (wedgeRightVertex G H x y y) = Sum.inl y
    dsimp [phi]
    exact vertexWedge_comm_apply_right G H x y y
  have hp : phi.vertexEquiv M.v = N.v := by
    change phi.vertexEquiv (wedgeRightVertex G H x y p) = Sum.inl p
    dsimp [phi]
    exact vertexWedge_comm_apply_right G H x y p
  have hLeft : IsTorsionOrder N 2 := by
    simpa only [N, W'] using
      same_leftFactor_wedge_isTorsionOrder_two H G y p x hH hCut hCard hpy.symm
  exact (isTorsionOrder_map_of_marks_iff phi hy hp 2).mp hLeft

end Bananas
