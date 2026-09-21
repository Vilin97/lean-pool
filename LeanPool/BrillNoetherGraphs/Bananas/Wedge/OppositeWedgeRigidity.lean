/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Transmission.ChainTwoLoopsSameLeft
import LeanPool.BrillNoetherGraphs.Bananas.Classification.GenusTwoDegreeTwo
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedgeRankFormula

/-!
# Rigidity of opposite-factor marks on a genus-one wedge

The phase `ell = 0` in the exact wedge rank formula shows that one chip on
each factor has rank zero whenever neither chip is the gluing point.
-/

namespace Bananas

open Utilities

private theorem rank_difference_eq_neg_one_of_pointedRigid
    (G : CFGraph) (x u : G.V) (hG : PointedGenusOneRigid G x)
    (hu : u ≠ x) : rank G (one_chip u - one_chip x) = -1 := by
  rw [rank_neg_one_iff_unwinnable]
  intro hWin
  apply hG.nontrivial u hu
  have hZero := linear_equiv_zero_of_winnable_deg_zero G _ hWin (by
    rw [deg.map_sub, deg_one_chip, deg_one_chip]
    norm_num)
  unfold linear_equiv at hZero ⊢
  have hNeg := (principal_divisors G).neg_mem hZero
  convert hNeg using 1
  abel

/-- One chip on each non-gluing factor vertex has rank zero on the wedge. -/
theorem rank_wedgeAdd_opposite_one_chips_eq_zero
    (G H : CFGraph) (x u : G.V) (y v : H.V)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hu : u ≠ x) :
    rank (vertexWedge G H x y)
      (wedgeAddDivisor G H x y (one_chip u) (one_chip v)) = 0 := by
  have hLeft : rank G (one_chip u - one_chip x) = -1 :=
    rank_difference_eq_neg_one_of_pointedRigid G x u hG hu
  have hRight : rank H (one_chip v) = 0 := by
    have h := genusOne_rank_eq_degree_sub_one hH.connected hH.genus_one
      (one_chip v) (by rw [deg_one_chip]; norm_num)
    rw [deg_one_chip] at h
    norm_num at h ⊢
    exact h
  have hNotOne : ¬ rank (vertexWedge G H x y)
      (wedgeAddDivisor G H x y (one_chip u) (one_chip v)) ≥ 1 := by
    intro hOne
    have hProfile :=
      (vertexWedge_rank_ge_iff_profile_inequalities G H x y
        (one_chip u) (one_chip v) 1 (by norm_num)).mp hOne 0
    norm_num at hProfile
    rw [hLeft, hRight] at hProfile
    omega
  have hEffective : effective (wedgeAddDivisor G H x y (one_chip u) (one_chip v)) :=
    effective_wedgeAddDivisor G H x y (one_chip u) (one_chip v)
      (fun z => eff_one_chip u z) (fun z => eff_one_chip v z)
  have hNonneg : 0 ≤ rank (vertexWedge G H x y)
      (wedgeAddDivisor G H x y (one_chip u) (one_chip v)) := by
    exact (rank_geq_iff _ _ 0).mp
      ((rank_nonneg_iff_winnable _ _).mpr
        (winnable_of_effective _ _ hEffective))
  omega

/-- Hence the opposite-factor marked pair is not canonical, the rigidity
condition used in the distinct-factor branch of Theorem 4.13. -/
theorem opposite_wedge_mark_pair_not_linearEquiv_canonical
    (G H : CFGraph) (x u : G.V) (y v : H.V)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hu : u ≠ x) :
    ¬ linear_equiv (vertexWedge G H x y)
      (one_chip (Sum.inl u) + one_chip (wedgeRightVertex G H x y v))
      (canonical_divisor (vertexWedge G H x y)) := by
  intro hCanon
  have hPair : one_chip (Sum.inl u) + one_chip (wedgeRightVertex G H x y v) =
      wedgeAddDivisor G H x y (one_chip u) (one_chip v) := by
    rw [← wedgeAddDivisor_one_chip_left, ← wedgeAddDivisor_one_chip_right]
    rw [wedgeAddDivisor_add]
    simp
  have hRankPair : rank (vertexWedge G H x y)
      (one_chip (Sum.inl u) + one_chip (wedgeRightVertex G H x y v)) = 0 := by
    rw [hPair]
    exact rank_wedgeAdd_opposite_one_chips_eq_zero G H x u y v hG hH hu
  have hConn : _root_.graph_connected (vertexWedge G H x y) :=
    graph_connected_vertexWedge G H x y hG.connected hH.connected
  have hGenus : genus (vertexWedge G H x y) = 2 := by
    rw [genus_vertexWedge, hG.genus_one, hH.genus_one]
    norm_num
  have hRank := rank_eq_of_linear_equiv _ hCanon
  rw [hRankPair] at hRank
  have hCanonical := rank_canonical_eq_one_of_genus_two hConn hGenus
  omega

end Bananas
