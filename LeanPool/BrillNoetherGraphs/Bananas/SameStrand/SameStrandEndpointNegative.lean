/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.NSMSecondCrossWitness
import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.SameStrandInteriorNegative

/-!
# Same-strand endpoint witnesses for Theorem 3.9

This file treats the boundary cases omitted from the interior-coordinate
classification.  On one normalized strand, the exceptional endpoint/interior
pairs in the paper are exactly `(0,n-1)` and `(1,n)` (up to swapping the
marks).  Every other endpoint/interior pair has a two-chip witness with rank
table `0, 0, 0, -1`.

For the left endpoint and an interior mark `v_j` with `j < n-1`, take
`D = v_0 + v_(j+1)`.  Prefix firing gives
`D - v_j ~ v_1`.  The right-endpoint witness is the reflected construction,
`D = v_(j-1) + v_n`.
-/

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- A non-reflected pair in normalized strand coordinates has rank zero in
every banana of genus at least two.  This is the normalized-coordinate wrapper
around `rank_same_strand_pair_zero_of_not_reflection_generic`; the wrapper is
needed because subdivision slots may be stored in the reverse orientation. -/
theorem rank_normalized_same_strand_pair_zero_of_sum_ne_length
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (alpha : Fin (g + 1))
    (i k : B.PathPosition alpha)
    (hNot : i.val + k.val ≠ B.length alpha) :
    rank B.graph
      (oneChip (strandVertex B alpha i) +
        oneChip (strandVertex B alpha k)) = 0 := by
  by_cases hTail : B.core.tail alpha = 0
  · simp only [strandVertex, hTail, ↓reduceIte]
    exact rank_same_strand_pair_zero_of_not_reflection_generic
      hg B alpha i k hNot
  · simp only [strandVertex, hTail, ↓reduceIte]
    apply rank_same_strand_pair_zero_of_not_reflection_generic hg
    change (B.length alpha - i.val) + (B.length alpha - k.val) ≠
      B.length alpha
    have hi : i.val ≤ B.length alpha := Nat.le_of_lt_succ i.isLt
    have hk : k.val ≤ B.length alpha := Nat.le_of_lt_succ k.isLt
    omega

/-- Corrected Theorem 3.9, left-endpoint same-strand branch.

If `j` is strictly interior and is not the penultimate position, the marking
at the common left endpoint and `v_j` has a divisor of negative rank
difference.  The explicit witness is `leftEndpoint + v_(j+1)`. -/
theorem exists_rankDelta_neg_leftEndpoint_same_strand
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (alpha : Fin (g + 1))
    (j : B.PathPosition alpha) (_hj : B.IsInteriorPosition alpha j)
    (hjFar : j.val + 1 < B.length alpha) :
    ∃ D : CFDiv B.graph,
      rankDelta
        (mark B.graph (leftEndpoint B) (strandVertex B alpha j)) D < 0 := by
  let s : B.PathPosition alpha := ⟨j.val + 1, by omega⟩
  let D : CFDiv B.graph :=
    oneChip (leftEndpoint B) + oneChip (strandVertex B alpha s)
  have hRankD : rank B.graph D = 0 := by
    have hZero : strandVertex B alpha ⟨0, by omega⟩ = leftEndpoint B :=
      strandVertex_zero B alpha
    dsimp [D]
    rw [← hZero]
    apply rank_normalized_same_strand_pair_zero_of_sum_ne_length hg
    dsimp [s]
    omega
  have hRankU : rank B.graph (D - oneChip (leftEndpoint B)) = 0 := by
    have hCancel :
        D - oneChip (leftEndpoint B) =
          oneChip (G := B.graph) (strandVertex B alpha s) := by
      dsimp [D]
      abel
    rw [hCancel]
    exact rank_one_chip_zero_of_banana (by omega) B _
  have hRankV :
      rank B.graph (D - oneChip (strandVertex B alpha j)) = 0 := by
    have hSlide := strand_one_add_position_linearEquiv_left_succ B alpha j
      (by omega)
    have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
      hSlide.symm (strandVertex B alpha j)
    have hRankEq := rank_eq_of_linear_equiv B.graph hShift
    have hLeft :
        oneChip (leftEndpoint B) + oneChip (strandVertex B alpha s) -
            oneChip (strandVertex B alpha j) =
          D - oneChip (strandVertex B alpha j) := by
      rfl
    have hRight :
        oneChip (strandVertex B alpha ⟨1, by omega⟩) +
              oneChip (strandVertex B alpha j) -
            oneChip (strandVertex B alpha j) =
          oneChip (G := B.graph) (strandVertex B alpha ⟨1, by omega⟩) := by
      abel
    rw [hLeft, hRight] at hRankEq
    rw [rank_one_chip_zero_of_banana (by omega) B _] at hRankEq
    exact hRankEq
  have hSV : strandVertex B alpha s ≠ strandVertex B alpha j := by
    intro h
    have hv := congrArg Fin.val (strandVertex_injective B alpha h)
    dsimp [s] at hv
    omega
  have hRankUV :
      rank B.graph
        (D - oneChip (leftEndpoint B) -
          oneChip (strandVertex B alpha j)) = -1 := by
    have hCancel :
        D - oneChip (leftEndpoint B) -
            oneChip (strandVertex B alpha j) =
          oneChip (strandVertex B alpha s) -
            oneChip (strandVertex B alpha j) := by
      dsimp [D]
      abel
    rw [hCancel]
    exact rank_one_chip_sub_one_chip_eq_neg_one_of_ne_banana_generic
      (by omega) B _ _ hSV
  refine ⟨D, ?_⟩
  unfold rankDelta mark
  rw [hRankD, hRankU, hRankV, hRankUV]
  norm_num

/-- Corrected Theorem 3.9, right-endpoint same-strand branch.

If `j` is strictly interior and is not the first interior position, the
marking at the common right endpoint and `v_j` has a divisor of negative rank
difference.  The explicit witness is `v_(j-1) + rightEndpoint`. -/
theorem exists_rankDelta_neg_rightEndpoint_same_strand
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (alpha : Fin (g + 1))
    (j : B.PathPosition alpha) (_hj : B.IsInteriorPosition alpha j)
    (hjFar : 1 < j.val) :
    ∃ D : CFDiv B.graph,
      rankDelta
        (mark B.graph (rightEndpoint B) (strandVertex B alpha j)) D < 0 := by
  let p : B.PathPosition alpha := ⟨j.val - 1, by omega⟩
  let D : CFDiv B.graph :=
    oneChip (strandVertex B alpha p) + oneChip (rightEndpoint B)
  have hRankD : rank B.graph D = 0 := by
    have hLength :
        strandVertex B alpha ⟨B.length alpha, by omega⟩ = rightEndpoint B :=
      strandVertex_length B alpha
    dsimp [D]
    rw [← hLength]
    apply rank_normalized_same_strand_pair_zero_of_sum_ne_length hg
    dsimp [p]
    omega
  have hRankU : rank B.graph (D - oneChip (rightEndpoint B)) = 0 := by
    have hCancel :
        D - oneChip (rightEndpoint B) =
          oneChip (G := B.graph) (strandVertex B alpha p) := by
      dsimp [D]
      abel
    rw [hCancel]
    exact rank_one_chip_zero_of_banana (by omega) B _
  have hRankV :
      rank B.graph (D - oneChip (strandVertex B alpha j)) = 0 := by
    have hSlide := strand_position_add_penultimate_linearEquiv_right_pred
      B alpha j hjFar
    have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
      hSlide.symm (strandVertex B alpha j)
    have hRankEq := rank_eq_of_linear_equiv B.graph hShift
    have hLeft :
        oneChip (strandVertex B alpha p) + oneChip (rightEndpoint B) -
            oneChip (strandVertex B alpha j) =
          D - oneChip (strandVertex B alpha j) := by
      rfl
    have hRight :
        oneChip (strandVertex B alpha j) +
              oneChip (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) -
            oneChip (strandVertex B alpha j) =
          oneChip (G := B.graph)
            (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) := by
      abel
    rw [hLeft, hRight] at hRankEq
    rw [rank_one_chip_zero_of_banana (by omega) B _] at hRankEq
    exact hRankEq
  have hPV : strandVertex B alpha p ≠ strandVertex B alpha j := by
    intro h
    have hv := congrArg Fin.val (strandVertex_injective B alpha h)
    dsimp [p] at hv
    omega
  have hRankUV :
      rank B.graph
        (D - oneChip (rightEndpoint B) -
          oneChip (strandVertex B alpha j)) = -1 := by
    have hCancel :
        D - oneChip (rightEndpoint B) -
            oneChip (strandVertex B alpha j) =
          oneChip (strandVertex B alpha p) -
            oneChip (strandVertex B alpha j) := by
      dsimp [D]
      abel
    rw [hCancel]
    exact rank_one_chip_sub_one_chip_eq_neg_one_of_ne_banana_generic
      (by omega) B _ _ hPV
  refine ⟨D, ?_⟩
  unfold rankDelta mark
  rw [hRankD, hRankU, hRankV, hRankUV]
  norm_num

/-- Repeating any marked vertex on a positive-genus banana is
non-submodular.  In particular, this handles the two coincident-endpoint
cases in the endpoint extension of Theorem 3.9. -/
theorem rankDelta_one_chip_self_lt_zero
    {g : ℕ} (hg : 1 ≤ g) (B : Banana g) (x : B.graph.V) :
    rankDelta (mark B.graph x x) (oneChip x) < 0 := by
  have hRankD : rank B.graph (oneChip x) = 0 :=
    rank_one_chip_zero_of_banana hg B x
  have hRankSub : rank B.graph (oneChip x - oneChip x) = 0 := by
    rw [sub_self, zero_divisor_rank]
  have hRankBoth :
      rank B.graph (oneChip x - oneChip x - oneChip x) = -1 := by
    apply rank_neg_one_of_deg_neg
    simp
  unfold rankDelta mark
  rw [hRankD, hRankSub, hRankBoth]
  norm_num

/-- The three same-strand exceptional coordinate pairs in Theorem 3.9,
expanded to include both orders. -/
def NSMForBananaSameStrandException
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (i j : B.PathPosition alpha) : Prop :=
  (i.val = 0 ∧ j.val = B.length alpha) ∨
    (i.val = B.length alpha ∧ j.val = 0) ∨
    (i.val = 1 ∧ j.val = B.length alpha) ∨
    (i.val = B.length alpha ∧ j.val = 1) ∨
    (i.val = 0 ∧ j.val + 1 = B.length alpha) ∨
    (i.val + 1 = B.length alpha ∧ j.val = 0)

private theorem rankDelta_swap_marks_endpoint {G : CFGraph}
    (u v : G.V) (D : CFDiv G) :
    rankDelta (mark G u v) D = rankDelta (mark G v u) D := by
  have hSub : D - oneChip u - oneChip v =
      D - oneChip v - oneChip u := by
    abel
  unfold rankDelta mark
  rw [hSub]
  ring

/-- Complete same-strand coordinate branch of corrected Theorem 3.9,
including endpoints.

For arbitrary normalized positions on one strand, either their ordered pair
is one of the six orientations of the paper's three exceptional pairs, or an
explicit divisor has negative marked rank difference. -/
theorem nsmForBanana_same_strand_classification
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (alpha : Fin (g + 1))
    (i j : B.PathPosition alpha) :
    NSMForBananaSameStrandException B alpha i j ∨
      ∃ D : CFDiv B.graph,
        rankDelta
          (mark B.graph (strandVertex B alpha i)
            (strandVertex B alpha j)) D < 0 := by
  have hiLe : i.val ≤ B.length alpha := Nat.le_of_lt_succ i.isLt
  have hjLe : j.val ≤ B.length alpha := Nat.le_of_lt_succ j.isLt
  by_cases hiZero : i.val = 0
  · have hiVertex : strandVertex B alpha i = leftEndpoint B := by
      have hi : i = ⟨0, by omega⟩ := Fin.ext hiZero
      rw [hi]
      exact strandVertex_zero B alpha
    by_cases hjZero : j.val = 0
    · right
      have hjVertex : strandVertex B alpha j = leftEndpoint B := by
        have hj : j = ⟨0, by omega⟩ := Fin.ext hjZero
        rw [hj]
        exact strandVertex_zero B alpha
      refine ⟨oneChip (leftEndpoint B), ?_⟩
      rw [hiVertex, hjVertex]
      exact rankDelta_one_chip_self_lt_zero (by omega) B _
    · by_cases hjLength : j.val = B.length alpha
      · left
        exact Or.inl ⟨hiZero, hjLength⟩
      · have hjInterior : B.IsInteriorPosition alpha j := by
          change 0 < j.val ∧ j.val < B.length alpha
          omega
        by_cases hjPenultimate : j.val + 1 = B.length alpha
        · left
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hiZero, hjPenultimate⟩))))
        · right
          obtain ⟨D, hD⟩ := exists_rankDelta_neg_leftEndpoint_same_strand
            hg B alpha j hjInterior (by omega)
          refine ⟨D, ?_⟩
          rw [hiVertex]
          exact hD
  · by_cases hiLength : i.val = B.length alpha
    · have hiVertex : strandVertex B alpha i = rightEndpoint B := by
        have hi : i = ⟨B.length alpha, by omega⟩ := Fin.ext hiLength
        rw [hi]
        exact strandVertex_length B alpha
      by_cases hjZero : j.val = 0
      · left
        exact Or.inr (Or.inl ⟨hiLength, hjZero⟩)
      · by_cases hjLength : j.val = B.length alpha
        · right
          have hjVertex : strandVertex B alpha j = rightEndpoint B := by
            have hj : j = ⟨B.length alpha, by omega⟩ := Fin.ext hjLength
            rw [hj]
            exact strandVertex_length B alpha
          refine ⟨oneChip (rightEndpoint B), ?_⟩
          rw [hiVertex, hjVertex]
          exact rankDelta_one_chip_self_lt_zero (by omega) B _
        · have hjInterior : B.IsInteriorPosition alpha j := by
            change 0 < j.val ∧ j.val < B.length alpha
            omega
          by_cases hjOne : j.val = 1
          · left
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hiLength, hjOne⟩)))
          · right
            obtain ⟨D, hD⟩ := exists_rankDelta_neg_rightEndpoint_same_strand
              hg B alpha j hjInterior (by omega)
            refine ⟨D, ?_⟩
            rw [hiVertex]
            exact hD
    · have hiInterior : B.IsInteriorPosition alpha i := by
        change 0 < i.val ∧ i.val < B.length alpha
        omega
      by_cases hjZero : j.val = 0
      · by_cases hiPenultimate : i.val + 1 = B.length alpha
        · left
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨hiPenultimate, hjZero⟩))))
        · right
          have hjVertex : strandVertex B alpha j = leftEndpoint B := by
            have hj : j = ⟨0, by omega⟩ := Fin.ext hjZero
            rw [hj]
            exact strandVertex_zero B alpha
          obtain ⟨D, hD⟩ := exists_rankDelta_neg_leftEndpoint_same_strand
            hg B alpha i hiInterior (by omega)
          refine ⟨D, ?_⟩
          rw [hjVertex, rankDelta_swap_marks_endpoint]
          exact hD
      · by_cases hjLength : j.val = B.length alpha
        · by_cases hiOne : i.val = 1
          · left
            exact Or.inr (Or.inr (Or.inl ⟨hiOne, hjLength⟩))
          · right
            have hjVertex : strandVertex B alpha j = rightEndpoint B := by
              have hj : j = ⟨B.length alpha, by omega⟩ := Fin.ext hjLength
              rw [hj]
              exact strandVertex_length B alpha
            obtain ⟨D, hD⟩ := exists_rankDelta_neg_rightEndpoint_same_strand
              hg B alpha i hiInterior (by omega)
            refine ⟨D, ?_⟩
            rw [hjVertex, rankDelta_swap_marks_endpoint]
            exact hD
        · right
          have hjInterior : B.IsInteriorPosition alpha j := by
            change 0 < j.val ∧ j.val < B.length alpha
            omega
          exact exists_rankDelta_neg_same_strand_interior_any_order
            hg B alpha i j hiInterior hjInterior

end Bananas
