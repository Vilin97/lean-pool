/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.RankZeroVertexBridge
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoEdgeConnectedRigidity

/-!
# Degree-one classes on a bridgeless graph

This formalizes Lemma 2.3 of the paper using `TwoEdgeCutCondition` as the
precise no-bridge hypothesis.  A nontriviality hypothesis is stated
explicitly: for the one-vertex edgeless graph the cut condition is vacuous,
but its unique degree-one class has rank one rather than rank zero.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- Lemma 2.3(1): on a connected graph with no one-edge cut, two vertices
are equal exactly when their degree-one divisors are linearly equivalent. -/
theorem vertex_eq_iff_one_chip_linear_equiv_of_twoEdgeCutCondition
    (G : CFGraph) (hConnected : _root_.graphConnected G)
    (hCut : TwoEdgeCutCondition G) (u v : G.V) :
    u = v ↔ linearEquiv G (oneChip u) (oneChip v) := by
  constructor
  · rintro rfl
    exact linearEquiv.refl G (oneChip u)
  · intro hEquiv
    by_contra huv
    apply not_linear_equiv_one_chip_sub_of_twoEdgeCutCondition
      hConnected hCut (Ne.symm huv)
    unfold linearEquiv at hEquiv ⊢
    simpa using hEquiv

/-- On a nontrivial connected graph with no one-edge cut, every one-chip
divisor has rank exactly zero. -/
theorem rank_one_chip_eq_zero_of_twoEdgeCutCondition
    (G : CFGraph) (hConnected : _root_.graphConnected G)
    (hCut : TwoEdgeCutCondition G)
    (hNontrivial : ∃ p q : G.V, p ≠ q) (x : G.V) :
    rank G (oneChip x) = 0 := by
  obtain ⟨p, q, hpq⟩ := hNontrivial
  obtain ⟨y, hyx⟩ : ∃ y : G.V, y ≠ x := by
    by_cases hxp : x = p
    · subst x
      exact ⟨q, hpq.symm⟩
    · exact ⟨p, Ne.symm hxp⟩
  have hNonnegative : 0 ≤ rank G (oneChip x) := by
    apply (rank_geq_iff G (oneChip x) 0).1
    apply (rank_nonneg_iff_winnable G (oneChip x)).2
    exact winnable_of_effective G (oneChip x) (eff_one_chip x)
  have hNotOne : ¬1 ≤ rank G (oneChip x) := by
    intro hOne
    have hResidual : winnable G (oneChip x - oneChip y) :=
      (rank_ge_one_iff_winnable_sub_one_chip G (oneChip x)).1 hOne y
    have hDegree : deg (oneChip x - oneChip y) = 0 := by simp
    have hPrincipal := linear_equiv_zero_of_winnable_deg_zero G
      (oneChip x - oneChip y) hResidual hDegree
    exact (not_linear_equiv_one_chip_sub_of_twoEdgeCutCondition
      hConnected hCut hyx) hPrincipal
  omega

/-- The rank-zero part of the degree-one Picard component, represented in
the additive quotient model used throughout the formalization. -/
def RankZeroDegreeOneClass (G : CFGraph) :=
  {c : CFDiv G ⧸ principalDivisors G //
    ∃ D : CFDiv G,
      QuotientAddGroup.mk' (principalDivisors G) D = c ∧
      rank G D = 0 ∧ deg D = 1}

/-- The Abel--Jacobi vertex map, with codomain restricted to rank-zero
degree-one divisor classes. -/
def bridgelessDegreeOneClassMap
    (G : CFGraph) (hConnected : _root_.graphConnected G)
    (hCut : TwoEdgeCutCondition G)
    (hNontrivial : ∃ p q : G.V, p ≠ q) :
    G.V → RankZeroDegreeOneClass G := fun x =>
  ⟨QuotientAddGroup.mk' (principalDivisors G) (oneChip x),
    ⟨oneChip x, rfl,
      rank_one_chip_eq_zero_of_twoEdgeCutCondition G hConnected hCut
        hNontrivial x,
      deg_one_chip x⟩⟩

/-- Lemma 2.3(2): vertices are in bijection with rank-zero divisor classes
of degree one. -/
theorem bridgelessDegreeOneClassMap_bijective
    (G : CFGraph) (hConnected : _root_.graphConnected G)
    (hCut : TwoEdgeCutCondition G)
    (hNontrivial : ∃ p q : G.V, p ≠ q) :
    Function.Bijective
      (bridgelessDegreeOneClassMap G hConnected hCut hNontrivial) := by
  constructor
  · intro x y hxy
    apply (vertex_eq_iff_one_chip_linear_equiv_of_twoEdgeCutCondition
      G hConnected hCut x y).2
    have hValues := congrArg Subtype.val hxy
    have hRelation := QuotientAddGroup.eq_iff_sub_mem.mp hValues
    unfold linearEquiv
    simpa using (principalDivisors G).neg_mem hRelation
  · rintro ⟨c, D, hClass, hRank, hDegree⟩
    obtain ⟨x, hRepresentative⟩ :=
      exists_one_chip_representative_of_rank_zero_degree_one
        G D hRank hDegree
    refine ⟨x, Subtype.ext ?_⟩
    change QuotientAddGroup.mk' (principalDivisors G) (oneChip x) = c
    rw [← hClass]
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    exact hRepresentative

end Bananas
