/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Transmission.ChainTwoLoopsSameLeft
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoEdgeConnectedRigidity
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.OneVertexCutFactors

/-!
# Same-factor submodularity on a rigid genus-one wedge

The same-factor branch of Theorem 4.13 only survives when that factor has
two vertices.  The point is that a third vertex supplies the explicit
negative rank-difference witness already used for Proposition 3.7.
-/

namespace Bananas

open Utilities

/-- On a bridgeless genus-one factor, pointed rigidity is available at every
vertex, not merely at the wedge attachment. -/
theorem pointedGenusOneRigid_of_any_vertex
    (G : CFGraph) (x : G.V) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 1) (hCut : TwoEdgeCutCondition G) :
    PointedGenusOneRigid G x :=
  pointedGenusOneRigid_of_twoEdgeCutCondition x hConnected hGenus
    (exists_vertex_ne_of_genus_pos x (by rw [hGenus]; norm_num)) hCut

/-- If two distinct marks lie in the left genus-one factor of a bridgeless
wedge and all divisors are submodular, that factor has exactly its two marked
vertices.  A third vertex gives the explicit negative second difference. -/
theorem card_leftFactor_le_two_of_allSubmodular
    (G H : CFGraph) (x u : G.V) (y : H.V)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hCut : TwoEdgeCutCondition G)
    (hSub : AllSubmodular
      (mark (vertexWedge G H x y) (Sum.inl x) (Sum.inl u))) :
    Fintype.card G.V ≤ 2 := by
  by_contra hNot
  have hCard : 2 < Fintype.card G.V := by omega
  obtain ⟨w, hwx, hwu⟩ := exists_ne_two_of_two_lt_card x u hCard
  have hGu : PointedGenusOneRigid G u :=
    pointedGenusOneRigid_of_any_vertex G u hG.connected hG.genus_one hCut
  have hNeg := rankDelta_wedgeLiftLeft_pair_neg G H x u w y
    hG.connected hG.genus_one hG hGu hH hwx hwu
  have hNonneg := (allSubmodular_iff_rankDelta_nonneg
    (mark (vertexWedge G H x y) (Sum.inl x) (Sum.inl u))).mp hSub
    (wedgeLiftLeftDivisor G H x y (one_chip x + one_chip w))
  omega

/-- The only all-submodular marking supported on one factor of a bridgeless
genus-one wedge uses the gluing vertex and a two-vertex factor. -/
theorem same_leftFactor_marks_of_allSubmodular
    (G H : CFGraph) (x u v : G.V) (y : H.V)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hCut : TwoEdgeCutCondition G)
    (hSub : AllSubmodular
      (mark (vertexWedge G H x y) (Sum.inl u) (Sum.inl v))) :
    (u = x ∨ v = x) ∧ Fintype.card G.V ≤ 2 := by
  let W := vertexWedge G H x y
  change AllSubmodular (mark W (Sum.inl u) (Sum.inl v)) at hSub
  by_cases hux : u = x
  · subst u
    exact ⟨Or.inl rfl,
      card_leftFactor_le_two_of_allSubmodular G H x v y hG hH hCut hSub⟩
  by_cases hvx : v = x
  · subst v
    refine ⟨Or.inr rfl, ?_⟩
    by_contra hNot
    have hCard : 2 < Fintype.card G.V := by omega
    obtain ⟨w, hwx, hwu⟩ := exists_ne_two_of_two_lt_card x u hCard
    have hGu : PointedGenusOneRigid G u :=
      pointedGenusOneRigid_of_any_vertex G u hG.connected hG.genus_one hCut
    have hNeg := rankDelta_wedgeLiftLeft_pair_neg G H x u w y
      hG.connected hG.genus_one hG hGu hH hwx hwu
    have hNonneg := (allSubmodular_iff_rankDelta_nonneg
      (mark W (Sum.inl u) (Sum.inl x))).mp hSub
      (wedgeLiftLeftDivisor G H x y (one_chip x + one_chip w))
    change 0 ≤ rankDelta
      (mark (vertexWedge G H x y) (Sum.inl u) (Sum.inl x))
      (wedgeLiftLeftDivisor G H x y (one_chip x + one_chip w)) at hNonneg
    rw [← rankDelta_swap_marks (vertexWedge G H x y) (Sum.inl x) (Sum.inl u)] at hNonneg
    exact (by omega : False).elim
  exfalso
  have hGu : PointedGenusOneRigid G v :=
    pointedGenusOneRigid_of_any_vertex G v hG.connected hG.genus_one hCut
  have hNeg := rankDelta_wedgeLiftLeft_mark_add_glue_neg G H x u v y
    hG.connected hG.genus_one hG hGu hH hux hvx
  have hNonneg := (allSubmodular_iff_rankDelta_nonneg
    (mark (vertexWedge G H x y) (Sum.inl u) (Sum.inl v))).mp hSub
    (wedgeLiftLeftDivisor G H x y (one_chip u + one_chip x))
  omega

/-- The necessary same-factor conclusion for a general-transmission wedge is
just its all-submodularity component. -/
theorem same_leftFactor_marks_of_kGeneral
    (G H : CFGraph) (x u v : G.V) (y : H.V)
    (k : ℕ) (hG : PointedGenusOneRigid G x)
    (hH : PointedGenusOneRigid H y) (hCut : TwoEdgeCutCondition G)
    (hK : KGeneralTransmission
      (mark (vertexWedge G H x y) (Sum.inl u) (Sum.inl v)) k) :
    (u = x ∨ v = x) ∧ Fintype.card G.V ≤ 2 :=
  same_leftFactor_marks_of_allSubmodular G H x u v y hG hH hCut hK.2.1

end Bananas
