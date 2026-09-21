/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Wedge.SameFactorWedgePeriod
import LeanPool.BrillNoetherGraphs.Bananas.Wedge.OppositeWedgeKGeneralClassification
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.KGeneralSwap

/-!
# Mark-placement classification on a rigid genus-two wedge

This is the wedge half of Theorem 4.13.  It is deliberately intrinsic: the
two genus-one factors are not presented as chosen cycles.
-/

namespace Bananas

open Utilities

private theorem card_eq_two_of_le_two_rigid
    (G : CFGraph) (x : G.V) (hG : PointedGenusOneRigid G x)
    (hLe : Fintype.card G.V ≤ 2) : Fintype.card G.V = 2 := by
  obtain ⟨z, hz⟩ := hG.exists_ne
  have hSubset : ({x, z} : Finset G.V) ⊆ Finset.univ := by simp
  have hTwo : ({x, z} : Finset G.V).card = 2 :=
    (Finset.card_pair_eq_two_iff).mpr (Ne.symm hz)
  have hGe := Finset.card_le_card hSubset
  rw [hTwo, Finset.card_univ] at hGe
  omega

/-- The six ordered placements that can survive general transmission on a
rigid wedge of two genus-one factors.  The first four are the order-two
two-vertex same-factor exceptions; the last two are the distinct-factor
equal-order branch. -/
def WedgeKGeneralPlacement
    (G H : CFGraph) (x : G.V) (y : H.V)
    (u v : (vertexWedge G H x y).V) (k : ℕ) : Prop :=
  (∃ a : G.V, u = Sum.inl x ∧ v = Sum.inl a ∧ a ≠ x ∧
    Fintype.card G.V = 2 ∧ k = 2) ∨
  (∃ a : G.V, u = Sum.inl a ∧ v = Sum.inl x ∧ a ≠ x ∧
    Fintype.card G.V = 2 ∧ k = 2) ∨
  (∃ p : H.V, u = wedgeRightVertex G H x y y ∧
    v = wedgeRightVertex G H x y p ∧ p ≠ y ∧
    Fintype.card H.V = 2 ∧ k = 2) ∨
  (∃ p : H.V, u = wedgeRightVertex G H x y p ∧
    v = wedgeRightVertex G H x y y ∧ p ≠ y ∧
    Fintype.card H.V = 2 ∧ k = 2) ∨
  (∃ a : G.V, ∃ p : H.V, u = Sum.inl a ∧
    v = wedgeRightVertex G H x y p ∧ a ≠ x ∧ p ≠ y ∧
    ∃ r : ℕ, IsTorsionOrder (mark G a x) r ∧
      IsTorsionOrder (mark H y p) r ∧ k = r) ∨
  (∃ a : G.V, ∃ p : H.V, u = wedgeRightVertex G H x y p ∧
    v = Sum.inl a ∧ a ≠ x ∧ p ≠ y ∧
    ∃ r : ℕ, IsTorsionOrder (mark G a x) r ∧
      IsTorsionOrder (mark H y p) r ∧ k = r)
/-- Necessity half of the wedge branch of Theorem 4.13. -/
theorem wedge_kGeneral_placement
    (G H : CFGraph) (x : G.V) (y : H.V)
    (u v : (vertexWedge G H x y).V) (k : ℕ)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hGCut : TwoEdgeCutCondition G) (hHCut : TwoEdgeCutCondition H)
    (hWCut : TwoEdgeCutCondition (vertexWedge G H x y))
    (huv : u ≠ v)
    (hK : KGeneralTransmission (mark (vertexWedge G H x y) u v) k) :
    WedgeKGeneralPlacement G H x y u v k := by
  cases u with
  | inl a =>
      cases v with
      | inl b =>
          have hSame := same_leftFactor_marks_of_kGeneral G H x a b y k
            hG hH hGCut hK
          rcases hSame with ⟨ha | hb, hCardLe⟩
          · subst a
            have hbx : b ≠ x := by
              intro h
              apply huv
              simp [h]
            left
            refine ⟨b, rfl, rfl, hbx, card_eq_two_of_le_two_rigid G x hG hCardLe, ?_⟩
            exact same_leftFactor_kGeneral_period_eq_two G H x b y k hG hH
              hGCut (card_eq_two_of_le_two_rigid G x hG hCardLe) hbx.symm hK
          · subst b
            have hax : a ≠ x := by
              intro h
              apply huv
              simp [h]
            right; left
            refine ⟨a, rfl, rfl, hax, card_eq_two_of_le_two_rigid G x hG hCardLe, ?_⟩
            have hSwap : KGeneralTransmission
                (mark (vertexWedge G H x y) (Sum.inl x) (Sum.inl a)) k :=
              KGeneralTransmission.swap_marks _ _ hK
            exact same_leftFactor_kGeneral_period_eq_two G H x a y k hG hH
              hGCut (card_eq_two_of_le_two_rigid G x hG hCardLe) hax.symm hSwap
      | inr b =>
          by_cases hax : a = x
          · subst a
            have hK' : KGeneralTransmission (mark (vertexWedge G H x y)
                (wedgeRightVertex G H x y y)
                (wedgeRightVertex G H x y b.1)) k := by
              rw [wedgeRightVertex_marked, wedgeRightVertex_unmarked G H x y b.1 b.2]
              exact hK
            have hSame := same_rightFactor_marks_of_kGeneral G H x y y b.1 k
              hG hH hHCut hK'
            obtain ⟨_, hCardLe⟩ := hSame
            right; right; left
            refine ⟨b.1, ?_, ?_, b.2,
              card_eq_two_of_le_two_rigid H y hH hCardLe, ?_⟩
            · rw [wedgeRightVertex_marked]
            · exact (wedgeRightVertex_unmarked G H x y b.1 b.2).symm
            · exact same_rightFactor_kGeneral_period_eq_two G H x y b.1 k
                hG hH hHCut (card_eq_two_of_le_two_rigid H y hH hCardLe) b.2 hK'
          · rcases opposite_wedge_kGeneral_factor_orders G H x a y b.1 k
              hG hH hax b.2 hWCut (by
                rw [wedgeRightVertex_unmarked G H x y b.1 b.2]
                exact hK) with ⟨r, hA, hB, hk⟩
            right; right; right; right; left
            exact ⟨a, b.1, rfl, (wedgeRightVertex_unmarked G H x y b.1 b.2).symm,
              hax, b.2, r, hA, hB, hk⟩
  | inr a =>
      cases v with
      | inl b =>
          by_cases hbx : b = x
          · subst b
            have hK' : KGeneralTransmission (mark (vertexWedge G H x y)
                (wedgeRightVertex G H x y a.1)
                (wedgeRightVertex G H x y y)) k := by
              rw [wedgeRightVertex_marked, wedgeRightVertex_unmarked G H x y a.1 a.2]
              exact hK
            have hSame := same_rightFactor_marks_of_kGeneral G H x y a.1 y k
              hG hH hHCut hK'
            obtain ⟨_, hCardLe⟩ := hSame
            right; right; right; left
            refine ⟨a.1, ?_, ?_, a.2,
              card_eq_two_of_le_two_rigid H y hH hCardLe, ?_⟩
            · exact (wedgeRightVertex_unmarked G H x y a.1 a.2).symm
            · rw [wedgeRightVertex_marked]
            · have hSwap : KGeneralTransmission (mark (vertexWedge G H x y)
                  (wedgeRightVertex G H x y y)
                  (wedgeRightVertex G H x y a.1)) k :=
                KGeneralTransmission.swap_marks _ _ hK'
              exact same_rightFactor_kGeneral_period_eq_two G H x y a.1 k
                hG hH hHCut (card_eq_two_of_le_two_rigid H y hH hCardLe) a.2 hSwap
          · rcases opposite_wedge_kGeneral_factor_orders G H x b y a.1 k
              hG hH hbx a.2 hWCut (by
                have hSwap : KGeneralTransmission
                    (mark (vertexWedge G H x y) (Sum.inl b) (Sum.inr a)) k :=
                  KGeneralTransmission.swap_marks _ _ hK
                rw [wedgeRightVertex_unmarked G H x y a.1 a.2]
                exact hSwap) with ⟨r, hA, hB, hk⟩
            right; right; right; right; right
            exact ⟨b, a.1, (wedgeRightVertex_unmarked G H x y a.1 a.2).symm, rfl,
              hbx, a.2, r, hA, hB, hk⟩
      | inr b =>
          have hK' : KGeneralTransmission (mark (vertexWedge G H x y)
              (wedgeRightVertex G H x y a.1)
              (wedgeRightVertex G H x y b.1)) k := by
            rw [wedgeRightVertex_unmarked G H x y a.1 a.2,
              wedgeRightVertex_unmarked G H x y b.1 b.2]
            exact hK
          have hSame := same_rightFactor_marks_of_kGeneral G H x y a.1 b.1 k
            hG hH hHCut hK'
          rcases hSame with ⟨ha | hb, _⟩
          · exact (a.2 ha).elim
          · exact (b.2 hb).elim

/-- Sufficiency half of the intrinsic wedge classification.  Each placement
is either the automatic order-two two-vertex exception or an opposite-factor
pair with equal exact factor orders. -/
theorem kGeneral_of_wedge_placement
    (G H : CFGraph) (x : G.V) (y : H.V)
    (u v : (vertexWedge G H x y).V) (k : ℕ)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hGCut : TwoEdgeCutCondition G) (hHCut : TwoEdgeCutCondition H)
    (hPlace : WedgeKGeneralPlacement G H x y u v k) :
    KGeneralTransmission (mark (vertexWedge G H x y) u v) k := by
  rcases hPlace with hLeft | hPlace
  · rcases hLeft with ⟨a, hu, hv, hax, hCard, hk⟩
    subst u
    subst v
    subst k
    exact same_leftFactor_wedge_twoGeneral_of_card_eq_two
      G H x a y hG hH hGCut hCard hax.symm
  rcases hPlace with hLeft | hPlace
  · rcases hLeft with ⟨a, hu, hv, hax, hCard, hk⟩
    subst u
    subst v
    subst k
    exact KGeneralTransmission.swap_marks _ _
      (same_leftFactor_wedge_twoGeneral_of_card_eq_two
        G H x a y hG hH hGCut hCard hax.symm)
  rcases hPlace with hRight | hPlace
  · rcases hRight with ⟨p, hu, hv, hpy, hCard, hk⟩
    subst u
    subst v
    subst k
    exact same_rightFactor_wedge_twoGeneral_of_card_eq_two
      G H x y p hG hH hHCut hCard hpy
  rcases hPlace with hRight | hPlace
  · rcases hRight with ⟨p, hu, hv, hpy, hCard, hk⟩
    subst u
    subst v
    subst k
    exact KGeneralTransmission.swap_marks _ _
      (same_rightFactor_wedge_twoGeneral_of_card_eq_two
        G H x y p hG hH hHCut hCard hpy)
  rcases hPlace with hOpp | hOpp
  · rcases hOpp with ⟨a, p, hu, hv, hax, hpy, r, hA, hB, hk⟩
    subst u
    subst v
    subst k
    exact pointedGenusOneRigid_vertexWedge_opposite_kGeneral_of_isTorsionOrder
      x y a p r hG hH hax hpy hA hB
  · rcases hOpp with ⟨a, p, hu, hv, hax, hpy, r, hA, hB, hk⟩
    subst u
    subst v
    subst k
    exact KGeneralTransmission.swap_marks _ _
      (pointedGenusOneRigid_vertexWedge_opposite_kGeneral_of_isTorsionOrder
        x y a p r hG hH hax hpy hA hB)

/-- Exact intrinsic wedge form of the general-transmission branch of
Theorem 4.13, for distinct marked vertices. -/
theorem kGeneral_iff_wedge_placement
    (G H : CFGraph) (x : G.V) (y : H.V)
    (u v : (vertexWedge G H x y).V) (k : ℕ)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hGCut : TwoEdgeCutCondition G) (hHCut : TwoEdgeCutCondition H)
    (hWCut : TwoEdgeCutCondition (vertexWedge G H x y))
    (huv : u ≠ v) :
    KGeneralTransmission (mark (vertexWedge G H x y) u v) k ↔
      WedgeKGeneralPlacement G H x y u v k :=
  ⟨wedge_kGeneral_placement G H x y u v k hG hH hGCut hHCut hWCut huv,
    kGeneral_of_wedge_placement G H x y u v k hG hH hGCut hHCut⟩

end Bananas
