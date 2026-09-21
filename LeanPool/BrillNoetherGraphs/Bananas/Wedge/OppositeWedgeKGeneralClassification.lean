/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Wedge.OppositeWedgeRigidity
import LeanPool.BrillNoetherGraphs.Bananas.Wedge.WedgeKGeneralSymmetric
import LeanPool.BrillNoetherGraphs.Bananas.Wedge.WedgeTorsionRestriction

/-!
# The distinct-factor branch of the genus-two wedge classification

For opposite non-gluing marks, general transmission itself recovers the two
factor torsion orders, forces them equal, and identifies the asserted wedge
period with that common order.
-/

namespace Bananas

open Utilities

theorem opposite_wedge_kGeneral_factor_orders
    (G H : CFGraph) (x u : G.V) (y v : H.V) (k : ℕ)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hu : u ≠ x) (hv : v ≠ y)
    (hCut : TwoEdgeCutCondition (vertexWedge G H x y))
    (hK : KGeneralTransmission
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) k) :
    ∃ a : ℕ, IsTorsionOrder (mark G u x) a ∧
      IsTorsionOrder (mark H y v) a ∧ k = a := by
  let W := vertexWedge G H x y
  have hConn : _root_.graph_connected W :=
    graph_connected_vertexWedge G H x y hG.connected hH.connected
  have hPos : 0 < genus W := by
    dsimp [W]
    rw [genus_vertexWedge, hG.genus_one, hH.genus_one]
    norm_num
  have hUV : (Sum.inl u : W.V) ≠ wedgeRightVertex G H x y v := by
    rw [wedgeRightVertex_unmarked G H x y v hv]
    simp
  obtain ⟨a, b, hA, hB, hkLcm⟩ :=
    exists_factor_torsionOrders_lcm_eq_of_vertexWedge_opposite_kGeneral
      G H x y u v k hConn hPos hUV hK
  have hRigid : ¬ linear_equiv W
      (one_chip (Sum.inl u) + one_chip (wedgeRightVertex G H x y v))
      (canonical_divisor W) := by
    simpa [W] using
      opposite_wedge_mark_pair_not_linearEquiv_canonical G H x u y v hG hH hu
  have hEq : a = b :=
    factor_torsionOrders_eq_of_vertexWedge_opposite_kGeneral_symmetric
      x y u v a b k hG hH hu hv hA hB hCut hRigid hK
  subst b
  refine ⟨a, hA, hB, ?_⟩
  simpa using hkLcm

end Bananas
