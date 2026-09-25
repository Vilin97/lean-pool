/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Wedge.WedgeKGeneralConverse
import LeanPool.BrillNoetherGraphs.Bananas.Sections.SectionSixChainConclusion
import LeanPool.BrillNoetherGraphs.Bananas.Classification.GenusTwoDegreeTwo
import LeanPool.BrillNoetherGraphs.Bananas.Basics.MarkedIso
import LeanPool.BrillNoetherGraphs.Bananas.Basics.GraphIsoCuts

/-!
# Symmetric period comparison on a rigid genus-two wedge

`WedgeKGeneralConverse` proves the period comparison after choosing an order
on the two factors.  This file removes that bookkeeping hypothesis by
commuting the vertex wedge and swapping the marked vertices in the other
case.
-/

namespace Bananas

open Utilities

private theorem torsionOrder_gt_one_of_pointedGenusOneRigid_ne
    {G : CFGraph} (x u : G.V) (hG : PointedGenusOneRigid G x)
    (hu : u ≠ x) {a : ℕ} (hA : IsTorsionOrder (mark G u x) a) :
    1 < a := by
  have hPos := hA.1.1
  by_contra hNot
  have ha : a = 1 := by omega
  subst a
  apply hG.nontrivial u hu
  have hWitness := hA.1
  change 0 < 1 ∧ linearEquiv G
    ((1 : ℤ) • (oneChip u - oneChip x)) 0 at hWitness
  have h : linearEquiv G (oneChip u - oneChip x) 0 := by
    simpa using hWitness.2
  unfold linearEquiv at h ⊢
  have hNeg := (principalDivisors G).neg_mem h
  convert hNeg using 1
  abel

private theorem isTorsionOrder_swap
    {G : CFGraph} (u v : G.V) {k : ℕ}
    (h : IsTorsionOrder (mark G u v) k) :
    IsTorsionOrder (mark G v u) k := by
  refine ⟨torsionWitness_swap u v h.1, ?_⟩
  intro m hm
  exact h.2 m (torsionWitness_swap v u hm)

/-- The period comparison on an opposite-side rigid wedge is symmetric in the
two factors: distinct factor marks force their exact torsion orders to agree
under `k`-general transmission. -/
theorem factor_torsionOrders_eq_of_vertexWedge_opposite_kGeneral_symmetric
    {G H : CFGraph} (x : G.V) (y : H.V) (u : G.V) (v : H.V)
    (a b k : ℕ) (hG : PointedGenusOneRigid G x)
    (hH : PointedGenusOneRigid H y) (hu : u ≠ x) (hv : v ≠ y)
    (hA : IsTorsionOrder (mark G u x) a)
    (hB : IsTorsionOrder (mark H y v) b)
    (hWCut : TwoEdgeCutCondition (vertexWedge G H x y))
    (hWRigid : ¬ linearEquiv (vertexWedge G H x y)
      (oneChip (Sum.inl u) + oneChip (wedgeRightVertex G H x y v))
      (canonicalDivisor (vertexWedge G H x y)))
    (hK : KGeneralTransmission
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) k) :
    a = b := by
  have haOne : 1 < a :=
    torsionOrder_gt_one_of_pointedGenusOneRigid_ne (a := a) x u hG hu hA
  have hBswap : IsTorsionOrder (mark H v y) b :=
    isTorsionOrder_swap y v hB
  have hbOne : 1 < b :=
    torsionOrder_gt_one_of_pointedGenusOneRigid_ne (a := b) y v hH hv hBswap
  rcases le_total a b with hAB | hBA
  · exact factor_torsionOrders_eq_of_vertexWedge_opposite_kGeneral
      x y u v a b k hG hH hv hA hB hWCut hWRigid haOne hAB hK
  · let W := vertexWedge G H x y
    let W' := vertexWedge H G y x
    let U : W.V := Sum.inl u
    let V : W.V := wedgeRightVertex G H x y v
    let U' : W'.V := Sum.inl v
    let V' : W'.V := wedgeRightVertex H G y x u
    let phi : CFGraphIso W W' := vertexWedgeComm G H x y
    have hPhiU : phi.vertexEquiv U = V' := by rfl
    have hPhiV : phi.vertexEquiv V = U' := by
      exact vertexWedge_comm_apply_right G H x y v
    have hKSwap : KGeneralTransmission (mark W' U' V') k := by
      have hSwap : KGeneralTransmission (mark W V U) k :=
        KGeneralTransmission.swap_marks U V (by simpa [W, U, V] using hK)
      exact (kGeneralTransmission_map_of_marks_iff phi hPhiV hPhiU k).mpr hSwap
    have hCutSwap : TwoEdgeCutCondition W' :=
      (phi.twoEdgeCutCondition_map_iff).mpr (by simpa [W] using hWCut)
    have hConn : _root_.graphConnected W :=
      graph_connected_vertexWedge G H x y hG.connected hH.connected
    have hGenus : genus W = 2 := by
      dsimp [W]
      rw [genus_vertexWedge, hG.genus_one, hH.genus_one]
      norm_num
    have hRigidSwap : ¬ linearEquiv W'
        (oneChip U' + oneChip V') (canonicalDivisor W') := by
      intro hCanon
      have hRank' : rank W' (oneChip U' + oneChip V') = 1 := by
        rw [rank_eq_of_linear_equiv W' hCanon]
        exact rank_canonical_eq_one_of_genus_two
          (by
            simpa [W'] using (graph_connected_vertexWedge H G y x
              hH.connected hG.connected)) (by
              dsimp [W']
              rw [genus_vertexWedge, hH.genus_one, hG.genus_one]
              norm_num)
      have hMap : phi.mapDiv (oneChip U + oneChip V) =
          oneChip U' + oneChip V' := by
        rw [map_add, phi.mapDiv_one_chip, phi.mapDiv_one_chip, hPhiU, hPhiV]
        abel
      have hRank : rank W (oneChip U + oneChip V) = 1 := by
        have := phi.rank_mapDiv (oneChip U + oneChip V)
        rw [hMap, hRank'] at this
        exact this.symm
      apply hWRigid
      change linearEquiv W (oneChip U + oneChip V) (canonicalDivisor W)
      exact linearEquiv_canonical_of_rank_eq_one_degree_two_genus_two
        hConn hGenus _ (by simp) hRank
    have hAswap : IsTorsionOrder (mark G x u) a :=
      isTorsionOrder_swap u x hA
    have hEq : b = a :=
      factor_torsionOrders_eq_of_vertexWedge_opposite_kGeneral
        y x v u b a k hH hG hu hBswap hAswap
        (by simpa [W'] using hCutSwap) (by simpa [W', U', V'] using hRigidSwap)
        hbOne hBA hKSwap
    exact hEq.symm

end Bananas
