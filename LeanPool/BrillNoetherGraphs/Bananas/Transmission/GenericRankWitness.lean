/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.SameStrand
import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointInversions
import LeanPool.BrillNoetherGraphs.Utilities.Segments.SeamCalculus

/-!
# Generic-genus rank witnesses on bananas

This file is deliberately separate from `Statements.lean`.  It packages the
rank facts used by the far-mark construction in Theorem 3.5 of
the twice-marked banana paper.
-/

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec


/-- A degree-zero divisor which is not principal has rank `-1`. -/
theorem rank_eq_neg_one_of_degree_zero_not_linear_equiv
    (G : CFGraph) (D : CFDiv G) (hDeg : deg D = 0)
    (hNotPrincipal : ¬ linearEquiv G D 0) :
    rank G D = -1 := by
  have hLower := rank_geq_neg_one G D
  by_contra hNot
  have hNonneg : 0 ≤ rank G D := by omega
  obtain ⟨E, hEff, hDE⟩ := (rank_nonneg_iff_winnable G D).mp
    ((rank_geq_iff G D 0).mpr hNonneg)
  have hEDeg : deg E = 0 := by
    rw [← linear_equiv_preserves_deg G D E hDE, hDeg]
  have hE : E = 0 := eff_degree_zero E hEff hEDeg
  apply hNotPrincipal
  simpa [hE] using hDE

/-- An effective divisor whose deletion at one vertex has rank `-1` has rank
zero. -/
theorem rank_eq_zero_of_effective_of_rank_sub_one_chip_eq_neg_one
    (G : CFGraph) (D : CFDiv G) (q : G.V)
    (hEff : effective D)
    (hSub : rank G (D - oneChip q) = -1) :
    rank G D = 0 := by
  have hNonneg : 0 ≤ rank G D :=
    (rank_geq_iff G D 0).mp ((rank_nonneg_iff_winnable G D).mpr
      (winnable_of_effective G D hEff))
  have hLt : rank G D < 1 := by
    by_contra hNot
    have hOne : rank G D ≥ 1 := by omega
    have hWin := (rank_ge_one_iff_winnable_sub_one_chip G D).mp hOne q
    have hSubNonneg : 0 ≤ rank G (D - oneChip q) :=
      (rank_geq_iff G (D - oneChip q) 0).mp
        ((rank_nonneg_iff_winnable G (D - oneChip q)).mpr hWin)
    omega
  omega

/-- A `q`-reduced effective divisor with no chip at `q` has rank zero. -/
theorem rank_eq_zero_of_effective_of_qReduced_of_no_chip
    (G : CFGraph) (q : G.V) (D : CFDiv G)
    (hEff : effective D) (hRed : qReduced G q D)
    (hNoChip : D q = 0) :
    rank G D = 0 := by
  apply rank_eq_zero_of_effective_of_rank_sub_one_chip_eq_neg_one G D q hEff
  apply rank_eq_neg_one_of_qReduced_debt G q
    (D - oneChip q) (q_reduced_sub_one_chip hRed)
  simp [hNoChip]

/-- The one-chip rank on a nontrivial banana is zero, uniformly in the
genus. -/
theorem rank_one_chip_zero_of_banana
    {g : ℕ} (hg : 1 ≤ g) (B : Banana g) (x : B.graph.V) :
    rank B.graph (oneChip x) = 0 := by
  let y : B.graph.V :=
    if x = leftEndpoint B then rightEndpoint B else leftEndpoint B
  have hxy : x ≠ y := by
    dsimp [y]
    split_ifs with hx
    · rw [hx]
      simp [leftEndpoint, rightEndpoint, SubdivisionGraph.Spec.coreVertex]
    · exact hx
  have hNonneg : 0 ≤ rank B.graph (oneChip x) :=
    (rank_geq_iff B.graph _ 0).mp
      ((rank_nonneg_iff_winnable B.graph _).mpr
        (winnable_of_effective B.graph _ (eff_one_chip x)))
  have hLt : rank B.graph (oneChip x) < 1 := by
    by_contra hNot
    have hOne : rank B.graph (oneChip x) ≥ 1 := by omega
    have hxyWin := (rank_ge_one_iff_winnable_sub_one_chip B.graph
      (oneChip x)).mp hOne y
    obtain ⟨E, hEff, hEquiv⟩ := hxyWin
    have hEDeg : deg E = 0 := by
      rw [← linear_equiv_preserves_deg B.graph _ E hEquiv,
        deg.map_sub, deg_one_chip, deg_one_chip]
      norm_num
    have hZero : E = 0 := eff_degree_zero E hEff hEDeg
    apply marks_not_linearEquiv hg B hxy
    simpa [hZero] using hEquiv
  omega

/-- A non-reflected pair on one strand has rank zero in every banana of
genus at least two. -/
theorem rank_same_strand_pair_zero_of_not_reflection_generic
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (α : Fin (g + 1))
    (i k : B.PathPosition α)
    (hNot : i.val + k.val ≠ B.length α) :
    rank B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k)) = 0 := by
  let D : CFDiv B.graph :=
    oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k)
  have hEff : effective D := by
    intro v
    simp [D, oneChip]
    omega
  have hNeg : ∃ q : B.graph.V, rank B.graph (D - oneChip q) = -1 := by
    rcases lt_or_gt_of_ne hNot with hlt | hgt
    · let p : B.PathPosition α :=
        ⟨i.val + k.val, by omega⟩
      let q : B.graph.V := B.pathVertex α ⟨B.length α, by omega⟩
      by_cases hi0 : i.val = 0
      · have hi : i = ⟨0, by omega⟩ := by
          apply Fin.ext
          exact hi0
        have hkLen : k.val < B.length α := by
          calc
            k.val = i.val + k.val := by omega
            _ < B.length α := hlt
        have hBase := rank_path_zero_add_same_strand_sub_of_lt
          hg B α k ⟨B.length α, by omega⟩ hkLen
        have hBase' : rank B.graph
            (oneChip (B.pathVertex α ⟨0, by omega⟩) +
              oneChip (B.pathVertex α k) - oneChip q) = -1 := by
          simpa only [q, B.pathVertex_zero] using hBase
        exact ⟨q, by simpa [D, q, hi, add_comm] using hBase'⟩
      by_cases hk0 : k.val = 0
      · have hk : k = ⟨0, by omega⟩ := by
          apply Fin.ext
          exact hk0
        have hiLen : i.val < B.length α := by
          calc
            i.val = i.val + k.val := by omega
            _ < B.length α := hlt
        have hBase := rank_path_zero_add_same_strand_sub_of_lt
          hg B α i ⟨B.length α, by omega⟩ hiLen
        have hBase' : rank B.graph
            (oneChip (B.pathVertex α ⟨0, by omega⟩) +
              oneChip (B.pathVertex α i) - oneChip q) = -1 := by
          simpa only [q] using hBase
        exact ⟨q, by simpa [D, q, hk, add_comm] using hBase'⟩
      · have hSlide := path_pair_linearEquiv_tail_sum B α i k
          (by omega) (by omega) hlt
        have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
          hSlide q
        have hRankEq := rank_eq_of_linear_equiv B.graph hShift
        have hBase := rank_path_zero_add_same_strand_sub_of_lt
          hg B α p ⟨B.length α, by omega⟩ (by dsimp [p]; omega)
        rw [← B.pathVertex_zero] at hRankEq
        rw [hBase] at hRankEq
        exact ⟨q, by dsimp [D] at hRankEq ⊢; exact hRankEq⟩
    · let p : B.PathPosition α :=
        ⟨i.val + k.val - B.length α, by omega⟩
      let q : B.graph.V := B.pathVertex α ⟨0, by omega⟩
      by_cases hiL : i.val = B.length α
      · have hi : i = ⟨B.length α, by omega⟩ := by
          apply Fin.ext
          exact hiL
        have hkPos : 0 < k.val := by omega
        have hBase := rank_same_strand_add_path_length_sub_of_lt
          hg B α k ⟨0, by omega⟩ hkPos
        have hBase' : rank B.graph
            (oneChip (B.pathVertex α k) +
              oneChip (B.pathVertex α ⟨B.length α, by omega⟩) -
              oneChip q) = -1 := by
          simpa only [q] using hBase
        exact ⟨q, by simpa [D, q, hi, add_comm, add_left_comm, add_assoc] using hBase'⟩
      by_cases hkL : k.val = B.length α
      · have hk : k = ⟨B.length α, by omega⟩ := by
          apply Fin.ext
          exact hkL
        have hiPos : 0 < i.val := by omega
        have hBase := rank_same_strand_add_path_length_sub_of_lt
          hg B α i ⟨0, by omega⟩ hiPos
        have hBase' : rank B.graph
            (oneChip (B.pathVertex α i) +
              oneChip (B.pathVertex α ⟨B.length α, by omega⟩) -
              oneChip q) = -1 := by
          simpa only [q] using hBase
        exact ⟨q, by simpa [D, q, hk, add_comm, add_left_comm, add_assoc] using hBase'⟩
      · have hSlide := path_pair_linearEquiv_head_excess B α i k
          (by omega) (by omega) hgt
        have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
          hSlide q
        have hRankEq := rank_eq_of_linear_equiv B.graph hShift
        have hBase := rank_same_strand_add_path_length_sub_of_lt
          hg B α p ⟨0, by omega⟩ (by dsimp [p]; omega)
        rw [← B.pathVertex_length] at hRankEq
        rw [hBase] at hRankEq
        exact ⟨q, by dsimp [D] at hRankEq ⊢; exact hRankEq⟩
  obtain ⟨q, hq⟩ := hNeg
  exact rank_eq_zero_of_effective_of_rank_sub_one_chip_eq_neg_one
    B.graph D q hEff hq

/-

/-- Three-chip rank bridge used by the generic far-mark construction: two
interior chips on distinct strands become rank `-1` after deleting a third,
distinct interior chip. -/
theorem rank_distinct_interior_pair_sub_of_distinct_interior
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (α β γ : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (q : B.PathPosition γ)
    (hi : B.IsInteriorPosition α i)
    (hj : B.IsInteriorPosition β j)
    (hq : B.IsInteriorPosition γ q)
    (hαβ : α ≠ β)
    (hqx : B.pathVertex γ q ≠ B.pathVertex α i)
    (hqy : B.pathVertex γ q ≠ B.pathVertex β j) :
    rank B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex β j) -
        oneChip (B.pathVertex γ q)) = -1 := by
  have hRed := q_reduced_distinct_interior_path_strands
    hg B α β γ i j q hi hj hq hαβ hqx hqy
  have hDebt :
      ((oneChip (B.pathVertex α i) + oneChip (B.pathVertex β j) -
        oneChip (B.pathVertex γ q) : CFDiv B.graph)
          (B.pathVertex γ q)) < 0 := by
    simp [oneChip, hqx, hqy]
  exact rank_eq_neg_one_of_qReduced_debt B.graph
    (B.pathVertex γ q)
    (oneChip (B.pathVertex α i) + oneChip (B.pathVertex β j) -
      oneChip (B.pathVertex γ q)) hRed hDebt

/-- The corresponding positive-pair rank is zero.  This packages the
degree-two step used in the paper's cross-strand three-chip tables. -/
theorem rank_distinct_interior_pair_zero_of_auxiliary
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (α β γ : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (q : B.PathPosition γ)
    (hi : B.IsInteriorPosition α i)
    (hj : B.IsInteriorPosition β j)
    (hq : B.IsInteriorPosition γ q)
    (hαβ : α ≠ β)
    (hqx : B.pathVertex γ q ≠ B.pathVertex α i)
    (hqy : B.pathVertex γ q ≠ B.pathVertex β j) :
    rank B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex β j)) = 0 := by
  let D : CFDiv B.graph :=
    oneChip (B.pathVertex α i) + oneChip (B.pathVertex β j)
  have hEff : effective D := by
    intro z
    simp [D, oneChip]
    omega
  have hSub : rank B.graph (D - oneChip (B.pathVertex γ q)) = -1 := by
    simpa [D] using rank_distinct_interior_pair_sub_of_distinct_interior
      hg B α β γ i j q hi hj hq hαβ hqx hqy
  exact rank_eq_zero_of_effective_of_rank_sub_one_chip_eq_neg_one
    B.graph D (B.pathVertex γ q) hEff hSub

-/
end Bananas
