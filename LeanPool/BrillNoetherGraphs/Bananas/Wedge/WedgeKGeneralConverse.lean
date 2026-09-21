/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Classification.PointedGenusOneKGeneral
import LeanPool.BrillNoetherGraphs.Bananas.Wedge.WedgePeriodRecurrence
import LeanPool.BrillNoetherGraphs.Bananas.Classification.BridgelessGenusTwoCornerAlgebra
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TorsionOrderExact

/-!
# Period extraction from a rigid genus-two wedge

This is the converse-period component of the distinct-factor branch of
Theorem 4.13.  Once factor torsion orders have been identified, general
transmission on a bridgeless rigid wedge forces the smaller nontrivial order
to equal the other one.
-/

namespace Bananas

open Utilities
/-- In the ordered distinct-factor wedge branch, `k`-general transmission
forces the two nontrivial factor torsion orders to agree.  The factor exact
orders are deliberately explicit: constructing them from a concrete cycle
presentation is a separate, purely topological part of the global
classification. -/
theorem factor_torsionOrders_eq_of_vertexWedge_opposite_kGeneral
    {G H : CFGraph} (x : G.V) (y : H.V) (u : G.V) (v : H.V)
    (a b k : ℕ) (hG : PointedGenusOneRigid G x)
    (hH : PointedGenusOneRigid H y) (hv : v ≠ y)
    (hA : IsTorsionOrder (mark G u x) a)
    (hB : IsTorsionOrder (mark H y v) b)
    (hWCut : TwoEdgeCutCondition (vertexWedge G H x y))
    (hWRigid : ¬ linear_equiv (vertexWedge G H x y)
      (one_chip (Sum.inl u) + one_chip (wedgeRightVertex G H x y v))
      (canonical_divisor (vertexWedge G H x y)))
    (haOne : 1 < a) (hAB : a ≤ b)
    (hK : KGeneralTransmission
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) k) :
    a = b := by
  let W := vertexWedge G H x y
  let U : W.V := Sum.inl u
  let V : W.V := wedgeRightVertex G H x y v
  have hWConn : _root_.graph_connected W :=
    graph_connected_vertexWedge G H x y hG.connected hH.connected
  have hWGenus : genus W = 2 := by
    dsimp [W]
    rw [genus_vertexWedge, hG.genus_one, hH.genus_one]
    norm_num
  have hUV : U ≠ V := by
    dsimp [U, V]
    rw [wedgeRightVertex_unmarked G H x y v hv]
    simp
  have hWNontrivial : ∃ p q : W.V, p ≠ q := ⟨U, V, hUV⟩
  have hK' : KGeneralTransmission (mark W U V) k := by
    simpa only [W, U, V] using hK
  have hWRigid' : ¬ linear_equiv W (one_chip U + one_chip V)
      (canonical_divisor W) := by
    simpa only [W, U, V] using hWRigid
  have hWPos : 0 < genus (mark W U V).graph := by
    change 0 < genus W
    rw [hWGenus]
    norm_num
  have hWOrder : IsTorsionOrder (mark W U V) k :=
    hK'.isTorsionOrder hUV hWConn hWPos
  have hWNonrec : NonRecurrent (mark W U V) k :=
    (bridgelessGenusTwoRigid_kGeneral_iff_nonRecurrent
      W hWConn hWCut hWNontrivial hWGenus U V k hK'.2.1 hWOrder hWRigid').mp hK'
  exact left_torsionOrder_eq_of_nonRecurrent_of_le
    G H x y u v a b k hH.connected hH.genus_one hA hB hWOrder
    hWNonrec haOne hAB

/-- Exact distinct-factor branch of Theorem 4.13 in the intrinsic
pointed-rigid interface.  At the (necessarily lcm) wedge torsion order,
general transmission is equivalent to equality of the two ordered,
nontrivial factor orders. -/
theorem pointedGenusOneRigid_vertexWedge_opposite_kGeneral_iff_orders_eq
    {G H : CFGraph} (x : G.V) (y : H.V) (u : G.V) (v : H.V)
    (a b : ℕ) (hG : PointedGenusOneRigid G x)
    (hH : PointedGenusOneRigid H y) (hu : u ≠ x) (hv : v ≠ y)
    (hA : IsTorsionOrder (mark G u x) a)
    (hB : IsTorsionOrder (mark H y v) b)
    (hWCut : TwoEdgeCutCondition (vertexWedge G H x y))
    (hWRigid : ¬ linear_equiv (vertexWedge G H x y)
      (one_chip (Sum.inl u) + one_chip (wedgeRightVertex G H x y v))
      (canonical_divisor (vertexWedge G H x y)))
    (haOne : 1 < a) (hAB : a ≤ b) :
    KGeneralTransmission
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) (Nat.lcm a b) ↔
      a = b := by
  constructor
  · intro hK
    exact factor_torsionOrders_eq_of_vertexWedge_opposite_kGeneral
      x y u v a b (Nat.lcm a b) hG hH hv hA hB hWCut hWRigid haOne hAB hK
  · intro hEq
    subst b
    rw [Nat.lcm_self]
    exact pointedGenusOneRigid_vertexWedge_opposite_kGeneral_of_isTorsionOrder
      x y u v a hG hH hu hv hA hB

end Bananas
