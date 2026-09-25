/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Wedge.SameFactorWedgeSubmodularity

/-!
# Automatic submodularity in the two-vertex same-factor wedge exception

The genus-one Riemann--Roch rank profile leaves no negative marked second
difference once the marked wedge factor has only its attachment and one other
vertex.  This is the converse to the obstruction in
`SameFactorWedgeSubmodularity`.
-/

namespace Bananas

open Utilities

private theorem eq_attachment_of_card_two
    {X : Type} [Fintype X] [DecidableEq X]
    (hCard : Fintype.card X = 2) {x u w : X}
    (hxu : x ≠ u) (hwu : w ≠ u) : w = x := by
  by_contra hwx
  have hSubset : ({w, x, u} : Finset X) ⊆ Finset.univ := by simp
  have hThree : ({w, x, u} : Finset X).card = 3 := by
    simp [hwx, hwu, hxu]
  have hLe := Finset.card_le_card hSubset
  rw [hThree, Finset.card_univ, hCard] at hLe
  omega

/-- The intrinsic two-vertex same-factor wedge exception is automatically
submodular.  The proof is just genus-one Riemann--Roch on the left factor and
the exact wedge rank criterion. -/
theorem allSubmodular_same_leftFactor_of_card_eq_two
    (G H : CFGraph) (x u : G.V) (y : H.V)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hCard : Fintype.card G.V = 2) (hxu : x ≠ u) :
    AllSubmodular
      (mark (vertexWedge G H x y) (Sum.inl x) (Sum.inl u)) := by
  apply allSubmodular_mark_of_rankDelta_nonneg
  intro D
  by_contra hNonneg
  let W := vertexWedge G H x y
  have hNeg : rankDelta (mark W (Sum.inl x) (Sum.inl u)) D < 0 := by
    change rankDelta (mark (vertexWedge G H x y) (Sum.inl x) (Sum.inl u)) D < 0
    omega
  have hWconn : _root_.graphConnected W :=
    graph_connected_vertexWedge G H x y hG.connected hH.connected
  have hWgenus : genus W = 2 := by
    rw [genus_vertexWedge, hG.genus_one, hH.genus_one]
    norm_num
  have hDistinct : ¬ linearEquiv W
      (oneChip (Sum.inl x) - oneChip (Sum.inl u)) 0 :=
    left_mark_difference_not_principal G H x u y hG hxu.symm
  have hRankD : rank W D = 0 :=
    rank_eq_zero_of_rankDelta_neg_genus_two
      (mark W (Sum.inl x) (Sum.inl u)) D hWconn hWgenus hDistinct hNeg
  obtain ⟨w, hRep, _hRed, hwu, hPair⟩ :=
    exists_vertex_rep_of_rankDelta_neg_genus_two W
      (Sum.inl x) (Sum.inl u) D hWconn hWgenus hDistinct hNeg
  cases w with
  | inl a =>
      have hau : a ≠ u := by
        intro h
        apply hwu
        exact congrArg Sum.inl h
      have ha : a = x :=
        eq_attachment_of_card_two hCard hxu hau
      subst a
      let A : CFDiv G := oneChip x + oneChip x
      have hDPair : linearEquiv W D
          (oneChip (Sum.inl x) + oneChip (Sum.inl x)) := by
        unfold linearEquiv at hRep ⊢
        have hEq :
            (oneChip (Sum.inl x) + oneChip (Sum.inl x) - D : CFDiv W) =
              oneChip (Sum.inl x) - (D - oneChip (Sum.inl x)) := by
          abel
        rw [hEq]
        exact hRep
      have hRankA : rank G A = 1 := by
        have h := genusOne_rank_eq_degree_sub_one hG.connected hG.genus_one A (by
          dsimp [A]
          norm_num)
        rw [show deg A = 2 by
          dsimp [A]
          norm_num] at h
        exact h
      have hResidual : winnable G (A - (2 : ℤ) • oneChip x) := by
        have hZero : A - (2 : ℤ) • oneChip x = 0 := by
          dsimp [A]
          abel
        rw [hZero]
        exact winnable_of_effective G 0 (by intro z; simp)
      have hRankPair : rank W (wedgeLiftLeftDivisor G H x y A) ≥ 1 :=
        (rank_wedgeLiftLeft_ge_one_iff G H x y hH A).mpr ⟨by omega, hResidual⟩
      have hPairEq :
          oneChip (G := W) (Sum.inl x) + oneChip (G := W) (Sum.inl x) =
            wedgeLiftLeftDivisor G H x y A :=
        wedge_left_pair G H x y x x
      have hRankEq := rank_eq_of_linear_equiv W hDPair
      rw [hRankD, hPairEq] at hRankEq
      omega
  | inr b =>
      have hNotWin := wedge_right_aux_pair_not_winnable
        G H x u y hG hH hxu.symm b
      apply hNotWin
      exact (rank_nonneg_iff_winnable W _).mp
        ((rank_geq_iff W _ 0).mpr (by omega))

end Bananas
