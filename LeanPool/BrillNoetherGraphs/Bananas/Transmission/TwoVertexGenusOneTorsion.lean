/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Wedge.SameFactorWedgeSubmodularity
public import LeanPool.BrillNoetherGraphs.Bananas.Classification.BridgelessGenusOneTopology

/-!
# The exact order of a two-vertex bridgeless genus-one factor

A loopless genus-one graph with two vertices and no one-edge cut consists of
two parallel edges.  Firing either vertex therefore doubles the marked
difference, while rigidity excludes order one.
-/

@[expose] public section

namespace Bananas

open Utilities

private theorem eq_of_ne_of_card_eq_two
    {X : Type*} [Fintype X] [DecidableEq X]
    (hCard : Fintype.card X = 2) {x u w : X}
    (hxu : x ≠ u) (hwu : w ≠ u) : w = x := by
  by_contra hwx
  have hSubset : ({w, x, u} : Finset X) ⊆ Finset.univ := by simp
  have hThree : ({w, x, u} : Finset X).card = 3 := by
    simp [hwx, hwu, hxu]
  have hLe := Finset.card_le_card hSubset
  rw [hThree, Finset.card_univ, hCard] at hLe
  omega

private theorem num_edges_eq_two_of_card_two
    (G : CFGraph) (x u : G.V) (hRigid : PointedGenusOneRigid G x)
    (hCut : TwoEdgeCutCondition G) (hCard : Fintype.card G.V = 2)
    (hxu : x ≠ u) : numEdges G x u = 2 := by
  have hDegree : vertexDegree G x = 2 :=
    vertex_degree_eq_two_of_bridgeless_genus_one G hCut ⟨x, u, hxu⟩
      hRigid.genus_one x
  have hSum : (∑ z : G.V, (numEdges G x z : ℤ)) = numEdges G x u := by
    rw [Finset.sum_eq_single u]
    · intro z _ hzu
      have hz : z = x :=
        eq_of_ne_of_card_eq_two (X := G.V) hCard hxu hzu
      subst z
      simp [num_edges_self_zero]
    · simp
  rw [vertexDegree, hSum] at hDegree
  exact_mod_cast hDegree

private theorem prin_double_marked_difference_of_card_two
    (G : CFGraph) (x u : G.V) (hRigid : PointedGenusOneRigid G x)
    (hCut : TwoEdgeCutCondition G) (hCard : Fintype.card G.V = 2)
    (hxu : x ≠ u) :
    prin G (oneChip x) = (2 : ℤ) • (oneChip u - oneChip x) := by
  have hEdges : numEdges G x u = 2 :=
    num_edges_eq_two_of_card_two G x u hRigid hCut hCard hxu
  ext z
  by_cases hzu : z = u
  · subst z
    rw [prin_apply]
    have hSum : (∑ w : G.V,
        (oneChip x w - oneChip x u) * (numEdges G u w : ℤ)) =
        (oneChip x x - oneChip x u) * (numEdges G u x : ℤ) := by
      rw [Finset.sum_eq_single x]
      · intro w _ hwx
        have hw : w = u :=
          eq_of_ne_of_card_eq_two (X := G.V) (x := u) (u := x)
            hCard hxu.symm hwx
        subst w
        simp [oneChip, num_edges_self_zero]
      · simp
    rw [hSum]
    simp [oneChip, num_edges_symmetric G u x, hEdges]
    ring
  · have hzx : z = x :=
      eq_of_ne_of_card_eq_two (X := G.V) hCard hxu hzu
    subst z
    rw [prin_apply]
    have hSum : (∑ w : G.V,
        (oneChip x w - oneChip x x) * (numEdges G x w : ℤ)) =
        (oneChip x u - oneChip x x) * (numEdges G x u : ℤ) := by
      rw [Finset.sum_eq_single u]
      · intro w _ hwu
        have hw : w = x :=
          eq_of_ne_of_card_eq_two (X := G.V) hCard hxu hwu
        subst w
        simp [oneChip, num_edges_self_zero]
      · simp
    rw [hSum]
    simp [oneChip, hxu, hxu.symm, hEdges]

/-- The two distinct vertices of a bridgeless two-vertex genus-one factor
have marked-difference torsion of exact order two. -/
theorem twoVertexGenusOne_isTorsionOrder_two
    (G : CFGraph) (x u : G.V) (hRigid : PointedGenusOneRigid G x)
    (hCut : TwoEdgeCutCondition G) (hCard : Fintype.card G.V = 2)
    (hxu : x ≠ u) : IsTorsionOrder (mark G x u) 2 := by
  refine ⟨?_, ?_⟩
  · refine ⟨by norm_num, ?_⟩
    change linearEquiv G ((2 : ℤ) • (oneChip x - oneChip u)) 0
    unfold linearEquiv
    rw [show (0 : CFDiv G) -
        ((2 : ℤ) • (oneChip x - oneChip u)) =
        (2 : ℤ) • (oneChip u - oneChip x) by abel]
    exact (principal_iff_eq_prin G _).mpr ⟨oneChip x,
      (prin_double_marked_difference_of_card_two G x u hRigid hCut hCard hxu).symm⟩
  · intro m hm
    have hmPositive := hm.1
    by_contra hTwo
    have hmOne : m = 1 := by omega
    subst m
    apply hRigid.nontrivial u hxu.symm
    have h := hm.2
    change linearEquiv G ((1 : ℤ) • (oneChip x - oneChip u)) 0 at h
    simpa using h

end Bananas
