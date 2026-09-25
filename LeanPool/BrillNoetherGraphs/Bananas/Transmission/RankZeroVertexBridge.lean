/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Classification.GenusTwoReduction

/-!
# Rank-zero witnesses as reduced one-chip classes

The theta argument starts with a negative second-difference witness.  In
genus two its deletion at either mark has degree one and rank zero.  Reducing
that deletion at the other mark therefore gives a *single vertex* rather
than an arbitrary divisor.  This file records that passage in the precise
form needed before applying the banana cut calculation.
-/

namespace Bananas

open Utilities

/-- A degree-one winnable divisor has a representative consisting of one
chip. -/
theorem exists_one_chip_representative_of_rank_zero_degree_one
    (G : CFGraph) (A : CFDiv G)
    (hRank : rank G A = 0) (hDeg : deg A = 1) :
    ∃ x : G.V, linearEquiv G A (oneChip x) := by
  have hWin : winnable G A :=
    (rank_nonneg_iff_winnable G A).mp
      ((rank_geq_iff G A 0).mpr (by omega))
  obtain ⟨E, hEff, hAE⟩ := (winnable_iff_exists_effective G A).mp hWin
  have hEDeg : deg E = 1 := by
    rw [← linear_equiv_preserves_deg G A E hAE, hDeg]
  obtain ⟨x, hx⟩ := effective_degree_one_eq_one_chip E hEff hEDeg
  exact ⟨x, hx ▸ hAE⟩

/-- In the genus-two negative-`Δ` situation, reducing `D-u` at `v`
produces a unique one-chip representative.  It is not `v`, and translating
back identifies the rank-zero divisor to which the `SameStrand` lemma is
applied in the paper. -/
theorem exists_qReduced_vertex_rep_of_rankDelta_neg_genus_two
    (M : TwiceMarked) (D : CFDiv M.graph)
    (hConn : _root_.graphConnected M.graph)
    (hGenus : genus M.graph = 2)
    (hDistinct : ¬ linearEquiv M.graph (oneChip M.u - oneChip M.v) 0)
    (hNeg : rankDelta M D < 0) :
    ∃ w : M.graph.V,
      linearEquiv M.graph (D - oneChip M.u) (oneChip w) ∧
      qReduced M.graph M.v (oneChip w) ∧
      w ≠ M.v ∧
      rank M.graph (oneChip w + oneChip M.u - oneChip M.v) = 0 := by
  have hDRank : rank M.graph D = 0 :=
    rank_eq_zero_of_rankDelta_neg_genus_two M D hConn hGenus hDistinct hNeg
  obtain ⟨hU, hV, hUV⟩ :=
    (rankDelta_neg_iff_rank_zero_deletions M D hDRank).mp hNeg
  have hUWin : winnable M.graph (D - oneChip M.u) :=
    (rank_nonneg_iff_winnable M.graph _).mp
      ((rank_geq_iff M.graph _ 0).mpr (by omega))
  obtain ⟨E, hUE, hERed⟩ :=
    exists_q_reduced_representative hConn M.v (D - oneChip M.u)
  have hEEff : effective E :=
    effective_of_winnable_and_q_reduced M.graph M.v E
      (winnable_equiv_winnable M.graph _ _ hUWin hUE) hERed
  have hEDeg : deg E = 1 := by
    rw [← linear_equiv_preserves_deg M.graph (D - oneChip M.u) E hUE,
      deg.map_sub, deg_one_chip]
    have hDDeg : deg D = 2 :=
      degree_eq_two_of_rankDelta_neg_genus_two M D hConn hGenus hDistinct hNeg
    omega
  obtain ⟨w, hw⟩ := effective_degree_one_eq_one_chip E hEEff hEDeg
  subst E
  refine ⟨w, hUE, hERed, ?_, ?_⟩
  · intro hwv
    subst w
    have hZero : linearEquiv M.graph
        (D - oneChip M.u - oneChip M.v) 0 := by
      unfold linearEquiv at hUE ⊢
      convert hUE using 1 ; abel
    have hRankZero := rank_eq_of_linear_equiv M.graph hZero
    rw [hUV, zero_divisor_rank] at hRankZero
    omega
  · have hShift : linearEquiv M.graph (D - oneChip M.v)
        (oneChip w + oneChip M.u - oneChip M.v) := by
      unfold linearEquiv at hUE ⊢
      convert hUE using 1 ; abel
    rw [← rank_eq_of_linear_equiv M.graph hShift]
    exact hV

end Bananas
