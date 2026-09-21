/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TwoVertexGenusOneTorsion
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TorsionOrderTwoGeneral
import LeanPool.BrillNoetherGraphs.Bananas.Wedge.TwoVertexWedgeSubmodularity

/-!
# The same-factor exceptional wedge marking

When the marked genus-one wedge factor has two vertices, its two marked
vertices have exact order two in the whole wedge.  Consequently the general
order-two criterion supplies general transmission as soon as submodularity is
known.
-/

namespace Bananas

open Utilities
private theorem wedgeLiftLeft_zsmul
    (G H : CFGraph) (x : G.V) (y : H.V) (n : ℤ) (D : CFDiv G) :
    wedgeLiftLeftDivisor G H x y (n • D) =
      n • wedgeLiftLeftDivisor G H x y D := by
  ext z
  cases z with
  | inl a => simp
  | inr b => simp

/-- The two vertices of a two-vertex bridgeless genus-one left factor have
exact marked torsion order two after attaching any pointed-rigid genus-one
right factor. -/
theorem same_leftFactor_wedge_isTorsionOrder_two
    (G H : CFGraph) (x u : G.V) (y : H.V)
    (hG : PointedGenusOneRigid G x)
    (hCut : TwoEdgeCutCondition G) (hCard : Fintype.card G.V = 2)
    (hxu : x ≠ u) :
    IsTorsionOrder
      (mark (vertexWedge G H x y) (Sum.inl x) (Sum.inl u)) 2 := by
  let W := vertexWedge G H x y
  let M := mark W (Sum.inl x) (Sum.inl u)
  have hFactor := (twoVertexGenusOne_isTorsionOrder_two
    G x u hG hCut hCard hxu).1.2
  have hWedge : linear_equiv W
      (wedgeLiftLeftDivisor G H x y
        ((2 : ℤ) • (one_chip x - one_chip u))) 0 := by
    have h := linear_equiv_wedgeAddDivisor G H x y
      ((2 : ℤ) • (one_chip x - one_chip u)) 0 0 0 hFactor
      (linear_equiv.refl H 0)
    convert h using 1 <;> ext z <;> cases z <;>
      simp [wedgeLiftLeftDivisor, wedgeAddDivisor] <;> rfl
  have hNotOne : ¬ TorsionWitness M 1 := by
    intro hOne
    apply left_mark_difference_not_principal G H x u y hG hxu.symm
    change TorsionWitness (mark W (Sum.inl x) (Sum.inl u)) 1 at hOne
    have hEq := hOne.2
    change linear_equiv W ((1 : ℤ) •
      (one_chip (G := W) (Sum.inl x) - one_chip (G := W) (Sum.inl u))) 0 at hEq
    simpa using hEq
  refine ⟨?_, ?_⟩
  · refine ⟨by norm_num, ?_⟩
    change linear_equiv W ((2 : ℤ) •
      (one_chip (G := W) (Sum.inl x) - one_chip (G := W) (Sum.inl u))) 0
    rw [wedge_left_difference]
    rw [← wedgeLiftLeft_zsmul]
    exact hWedge
  · intro m hm
    by_contra hTwo
    have hmOne : m = 1 := by
      have hmPos := hm.1
      omega
    subst m
    exact hNotOne hm

/-- The same-factor two-vertex exception has two-general transmission. -/
theorem same_leftFactor_wedge_twoGeneral
    (G H : CFGraph) (x u : G.V) (y : H.V)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hCut : TwoEdgeCutCondition G) (hCard : Fintype.card G.V = 2)
    (hxu : x ≠ u)
    (hSub : AllSubmodular
      (mark (vertexWedge G H x y) (Sum.inl x) (Sum.inl u))) :
    KGeneralTransmission
      (mark (vertexWedge G H x y) (Sum.inl x) (Sum.inl u)) 2 := by
  apply torsionOrder_two_allSubmodular_isKGeneral
  · exact graph_connected_vertexWedge G H x y hG.connected hH.connected
  · exact same_leftFactor_wedge_isTorsionOrder_two G H x u y hG hCut hCard hxu
  · exact hSub

/-- The same-factor two-vertex exception needs no additional submodularity
hypothesis: genus-one Riemann--Roch and the wedge rank formula prove it
automatically. -/
theorem same_leftFactor_wedge_twoGeneral_of_card_eq_two
    (G H : CFGraph) (x u : G.V) (y : H.V)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hCut : TwoEdgeCutCondition G) (hCard : Fintype.card G.V = 2)
    (hxu : x ≠ u) :
    KGeneralTransmission
      (mark (vertexWedge G H x y) (Sum.inl x) (Sum.inl u)) 2 :=
  same_leftFactor_wedge_twoGeneral G H x u y hG hH hCut hCard hxu
    (allSubmodular_same_leftFactor_of_card_eq_two G H x u y hG hH hCard hxu)

end Bananas
