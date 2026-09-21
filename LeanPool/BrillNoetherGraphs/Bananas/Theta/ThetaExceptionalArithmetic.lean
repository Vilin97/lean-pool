/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.SameStrand
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.RankZeroSupport

/-!
# Arithmetic form of the theta exceptional-position condition

This file separates the finite interval calculation in paper Theorem 3.4
from its divisor-rank content.  Coordinates here are the normalized
coordinates used by `strandVertex`, measured from core vertex `0`.
-/

namespace Bananas

open Utilities

/-- The marked second rank difference is symmetric in the two marks. -/
theorem rankDelta_swap_marks (G : CFGraph) (u v : G.V) (D : CFDiv G) :
    rankDelta (mark G u v) D = rankDelta (mark G v u) D := by
  have hSub : D - one_chip u - one_chip v =
      D - one_chip v - one_chip u := by
    abel
  unfold rankDelta mark
  rw [hSub]
  ring

/-- Distinct vertices on a nontrivial banana give a degree-zero divisor of
rank `-1`. -/
theorem rank_one_chip_sub_one_chip_eq_neg_one_of_ne_banana
    (B : Banana 2) (x y : B.graph.V) (hxy : x ≠ y) :
    rank B.graph (one_chip x - one_chip y) = -1 := by
  have hLower := rank_geq_neg_one B.graph (one_chip x - one_chip y)
  by_contra hNot
  have hNonneg : 0 ≤ rank B.graph (one_chip x - one_chip y) := by omega
  obtain ⟨E, hEff, hEquiv⟩ :=
    (rank_nonneg_iff_winnable B.graph (one_chip x - one_chip y)).mp
      ((rank_geq_iff B.graph _ 0).mpr hNonneg)
  have hEDeg : deg E = 0 := by
    rw [← linear_equiv_preserves_deg B.graph _ E hEquiv,
      deg.map_sub, deg_one_chip, deg_one_chip]
    norm_num
  have hEZero : E = 0 := eff_degree_zero E hEff hEDeg
  apply marks_not_linearEquiv (by omega : 1 ≤ 2) B hxy
  simpa [hEZero] using hEquiv

/-- Paper source: `thm-NonSubmodGenus2`, with the exceptional support
construction used in `lem-SameStrand`.

Every two distinct interior normalized positions on one theta strand
admit an explicit negative rank-difference witness. -/
theorem exists_rankDelta_neg_same_strand_interior
    (B : Banana 2) (alpha : Fin 3)
    (i j : B.PathPosition alpha)
    (hi : B.IsInteriorPosition alpha i)
    (hj : B.IsInteriorPosition alpha j)
    (hij : i.val < j.val) :
    ∃ D : CFDiv B.graph,
      rankDelta (mark B.graph (strandVertex B alpha i)
        (strandVertex B alpha j)) D < 0 := by
  let k : B.PathPosition alpha := ⟨j.val - i.val, by
    have hSubLe : j.val - i.val ≤ j.val := Nat.sub_le _ _
    omega⟩
  have hk : B.IsInteriorPosition alpha k := by
    change 0 < j.val - i.val ∧ j.val - i.val < B.length alpha
    exact ⟨Nat.sub_pos_of_lt hij,
      lt_of_le_of_lt (Nat.sub_le _ _) hj.2⟩
  have hIK : i.val + k.val = j.val := by
    dsimp [k]
    rw [Nat.add_sub_of_le (Nat.le_of_lt hij)]
  have hkLtJ : k.val < j.val := by
    dsimp [k]
    have hjPos : 0 < j.val := lt_trans hi.1 hij
    exact Nat.sub_lt hjPos hi.1
  have hKJ : strandVertex B alpha k ≠ strandVertex B alpha j := by
    intro h
    have hEq := strandVertex_injective B alpha h
    have hVal := congrArg Fin.val hEq
    exact (ne_of_lt hkLtJ) hVal
  have hNotReflect : strandVertex B alpha k ≠
      strandVertex B alpha (strandMirror B alpha i) := by
    intro h
    have hEq := strandVertex_injective B alpha h
    have hVal := congrArg Fin.val hEq
    change k.val = B.length alpha - i.val at hVal
    have hSumLength : i.val + k.val = B.length alpha := by
      rw [hVal, Nat.add_sub_of_le (Nat.le_of_lt hi.2)]
    have hJLength : j.val = B.length alpha := hIK.symm.trans hSumLength
    exact (ne_of_lt hj.2) hJLength
  let D : CFDiv B.graph :=
    one_chip (strandVertex B alpha i) + one_chip (strandVertex B alpha k)
  have hRankD : rank B.graph D = 0 := by
    dsimp [D]
    exact rank_same_strand_pair_zero_of_not_reflection B alpha i k hNotReflect
  have hRankU : rank B.graph
      (D - one_chip (strandVertex B alpha i)) = 0 := by
    have hUpper := rank_sub_one_chip_le_rank B.graph D
      (strandVertex B alpha i)
    have hEffective : effective
        (D - one_chip (strandVertex B alpha i)) := by
      have hCancel :
          D - one_chip (strandVertex B alpha i) =
            one_chip (G := B.graph) (strandVertex B alpha k) := by
        dsimp [D]
        abel
      rw [hCancel]
      exact eff_one_chip _
    have hNonneg : 0 ≤ rank B.graph
        (D - one_chip (strandVertex B alpha i)) :=
      (rank_geq_iff B.graph _ 0).mp
        ((rank_nonneg_iff_winnable B.graph _).mpr
          (winnable_of_effective B.graph _ hEffective))
    rw [hRankD] at hUpper
    omega
  have hRankV : rank B.graph
      (D - one_chip (strandVertex B alpha j)) = 0 := by
    by_cases hTail : B.core.tail alpha = 0
    · have hI : strandVertex B alpha i = B.pathVertex alpha i := by
        unfold strandVertex
        rw [if_pos hTail]
      have hK : strandVertex B alpha k = B.pathVertex alpha k := by
        unfold strandVertex
        rw [if_pos hTail]
      have hJ : strandVertex B alpha j = B.pathVertex alpha j := by
        unfold strandVertex
        rw [if_pos hTail]
      dsimp [D]
      rw [hI, hK, hJ]
      apply rank_same_path_pair_sub_of_sum_inside_full B alpha i k j hi hk hj
      constructor <;> omega
    · have hI : strandVertex B alpha i =
          B.pathVertex alpha (strandMirror B alpha i) := by
        unfold strandVertex strandMirror
        rw [if_neg hTail]
      have hK : strandVertex B alpha k =
          B.pathVertex alpha (strandMirror B alpha k) := by
        unfold strandVertex strandMirror
        rw [if_neg hTail]
      have hJ : strandVertex B alpha j =
          B.pathVertex alpha (strandMirror B alpha j) := by
        unfold strandVertex strandMirror
        rw [if_neg hTail]
      have hiMirror : B.IsInteriorPosition alpha (strandMirror B alpha i) := by
        change 0 < B.length alpha - i.val ∧
          B.length alpha - i.val < B.length alpha
        omega
      have hkMirror : B.IsInteriorPosition alpha (strandMirror B alpha k) := by
        change 0 < B.length alpha - k.val ∧
          B.length alpha - k.val < B.length alpha
        omega
      have hjMirror : B.IsInteriorPosition alpha (strandMirror B alpha j) := by
        change 0 < B.length alpha - j.val ∧
          B.length alpha - j.val < B.length alpha
        exact ⟨Nat.sub_pos_of_lt hj.2,
          Nat.sub_lt (B.length_pos alpha) (lt_trans hi.1 hij)⟩
      dsimp [D]
      rw [hI, hK, hJ]
      apply rank_same_path_pair_sub_of_sum_inside_full B alpha
        (strandMirror B alpha i) (strandMirror B alpha k)
        (strandMirror B alpha j) hiMirror hkMirror hjMirror
      simp only [strandMirror]
      constructor <;> omega
  have hRankUV : rank B.graph
      (D - one_chip (strandVertex B alpha i) -
        one_chip (strandVertex B alpha j)) = -1 := by
    have hRank := rank_one_chip_sub_one_chip_eq_neg_one_of_ne_banana B
      (strandVertex B alpha k) (strandVertex B alpha j) hKJ
    have hCancel :
        D - one_chip (strandVertex B alpha i) -
            one_chip (strandVertex B alpha j) =
          one_chip (strandVertex B alpha k) -
            one_chip (strandVertex B alpha j) := by
      dsimp [D]
      abel
    rw [hCancel]
    exact hRank
  refine ⟨D, (rankDelta_neg_iff_rank_zero_deletions
    (mark B.graph (strandVertex B alpha i) (strandVertex B alpha j)) D
      hRankD).mpr ?_⟩
  exact ⟨hRankU, hRankV, hRankUV⟩

/-- Paper source: the boundary cases in `thm-NonSubmodGenus2` and the
support formulation `cor:suppUV`.

The exceptional-position set is empty exactly in the three boundary
markings listed in Corollary 3.6 of the paper.  Writing `j + 1 = length`
avoids truncated subtraction in the formal version of `j = length - 1`. -/
theorem thetaExceptionalPositions_nonempty_iff_not_boundary
    (B : Banana 2) (alpha : Fin 3)
    (i j : B.PathPosition alpha) (hij : i.val < j.val) :
    Set.Nonempty (thetaExceptionalPositions B alpha i j) ↔
      ¬ ((i.val = 0 ∧
            (j.val + 1 = B.length alpha ∨ j.val = B.length alpha)) ∨
          (i.val = 1 ∧ j.val = B.length alpha)) := by
  constructor
  · rintro ⟨q, hqReflect, hqJ, hqLower, _hqUpper⟩ hBoundary
    have hqBound := q.isLt
    rcases hBoundary with ⟨hi, hjNear | hjEnd⟩ | ⟨hi, hjEnd⟩
    · omega
    · omega
    · omega
  · intro hBoundary
    by_cases hiZero : i.val = 0
    · have hjNear : j.val + 1 ≠ B.length alpha := by
        intro h
        exact hBoundary (Or.inl ⟨hiZero, Or.inl h⟩)
      have hjEnd : j.val ≠ B.length alpha := by
        intro h
        exact hBoundary (Or.inl ⟨hiZero, Or.inr h⟩)
      let q : B.PathPosition alpha := ⟨j.val + 1, by omega⟩
      refine ⟨q, ?_, ?_, ?_, ?_⟩ <;> dsimp [q]
      all_goals omega
    · by_cases hjEnd : j.val = B.length alpha
      · have hiOne : i.val ≠ 1 := by
          intro h
          exact hBoundary (Or.inr ⟨h, hjEnd⟩)
        let q : B.PathPosition alpha :=
          ⟨B.length alpha - i.val + 1, by omega⟩
        refine ⟨q, ?_, ?_, ?_, ?_⟩ <;> dsimp [q]
        all_goals omega
      · let q : B.PathPosition alpha := ⟨j.val - i.val, by omega⟩
        refine ⟨q, ?_, ?_, ?_, ?_⟩ <;> dsimp [q]
        all_goals omega

/-- Paper source: `thm-NonSubmodGenus2` (Theorem 3.4).

Complete theta classification for two interior marks on the same strand,
valid for either stored orientation of that strand. -/
theorem theta_nonSubmodular_iff_of_interior_marks
    (B : Banana 2) (alpha : Fin 3)
    (i j : B.PathPosition alpha)
    (hi : B.IsInteriorPosition alpha i)
    (hj : B.IsInteriorPosition alpha j)
    (hij : i.val < j.val) :
    (∃ D : CFDiv B.graph,
        rankDelta (mark B.graph (strandVertex B alpha i)
          (strandVertex B alpha j)) D < 0) ↔
      Set.Nonempty (thetaExceptionalPositions B alpha i j) := by
  change 0 < i.val ∧ i.val < B.length alpha at hi
  change 0 < j.val ∧ j.val < B.length alpha at hj
  constructor
  · intro _hNegative
    apply (thetaExceptionalPositions_nonempty_iff_not_boundary
      B alpha i j hij).mpr
    intro hBoundary
    rcases hBoundary with ⟨hiZero, _⟩ | ⟨_hiOne, hjEnd⟩
    · exact (Nat.ne_of_gt hi.1) hiZero
    · exact (Nat.ne_of_lt hj.2) hjEnd
  · intro _hExceptional
    exact exists_rankDelta_neg_same_strand_interior B alpha i j hi hj hij

/-- Reversing the strand coordinate and swapping the ordered marks preserves
nonemptiness of the exceptional-position set.  This is the arithmetic
transport needed when a subdivision slot is stored from core vertex `1`
rather than from core vertex `0`. -/
theorem thetaExceptionalPositions_nonempty_mirror_swap_iff
    (B : Banana 2) (alpha : Fin 3)
    (i j : B.PathPosition alpha) (hij : i.val < j.val) :
    Set.Nonempty (thetaExceptionalPositions B alpha i j) ↔
      Set.Nonempty (thetaExceptionalPositions B alpha
        (strandMirror B alpha j) (strandMirror B alpha i)) := by
  have hiBound := i.isLt
  have hjBound := j.isLt
  have hMirror :
      (strandMirror B alpha j).val < (strandMirror B alpha i).val := by
    simp only [strandMirror]
    omega
  rw [thetaExceptionalPositions_nonempty_iff_not_boundary B alpha i j hij,
    thetaExceptionalPositions_nonempty_iff_not_boundary B alpha
      (strandMirror B alpha j) (strandMirror B alpha i) hMirror]
  simp only [strandMirror]
  constructor
  · intro hNormal hRaw
    apply hNormal
    rcases hRaw with ⟨hj, hiNear | hiEnd⟩ | ⟨hj, hiEnd⟩
    · right
      omega
    · left
      omega
    · left
      omega
  · intro hRaw hNormal
    apply hRaw
    rcases hNormal with ⟨hi, hjNear | hjEnd⟩ | ⟨hi, hjEnd⟩
    · right
      omega
    · left
      omega
    · left
      omega

/-- A raw-coordinate classification implies the normalized theorem used in
`Statements.lean`.  This checked wrapper isolates the sole remaining
divisor-rank result: the hypothesis `hRaw`. -/
theorem theta_nonSubmodular_iff_of_raw_classification
    (B : Banana 2) (alpha : Fin 3)
    (hRaw : ∀ (p q : B.PathPosition alpha), p.val < q.val →
      ((∃ D : CFDiv B.graph,
          rankDelta (mark B.graph (B.pathVertex alpha p)
            (B.pathVertex alpha q)) D < 0) ↔
        Set.Nonempty (thetaExceptionalPositions B alpha p q)))
    (i j : B.PathPosition alpha) (hij : i.val < j.val) :
    (∃ D : CFDiv B.graph,
        rankDelta (mark B.graph (strandVertex B alpha i)
          (strandVertex B alpha j)) D < 0) ↔
      Set.Nonempty (thetaExceptionalPositions B alpha i j) := by
  by_cases hTail : B.core.tail alpha = 0
  · have hI : strandVertex B alpha i = B.pathVertex alpha i := by
      unfold strandVertex
      rw [if_pos hTail]
    have hJ : strandVertex B alpha j = B.pathVertex alpha j := by
      unfold strandVertex
      rw [if_pos hTail]
    rw [hI, hJ]
    exact hRaw i j hij
  · have hiBound := i.isLt
    have hjBound := j.isLt
    have hI : strandVertex B alpha i =
        B.pathVertex alpha (strandMirror B alpha i) := by
      unfold strandVertex strandMirror
      rw [if_neg hTail]
    have hJ : strandVertex B alpha j =
        B.pathVertex alpha (strandMirror B alpha j) := by
      unfold strandVertex strandMirror
      rw [if_neg hTail]
    have hMirror :
        (strandMirror B alpha j).val < (strandMirror B alpha i).val := by
      simp only [strandMirror]
      omega
    have hClass := hRaw (strandMirror B alpha j)
      (strandMirror B alpha i) hMirror
    have hExceptional :=
      thetaExceptionalPositions_nonempty_mirror_swap_iff B alpha i j hij
    rw [hI, hJ]
    constructor
    · rintro ⟨D, hD⟩
      apply hExceptional.mpr
      apply hClass.mp
      refine ⟨D, ?_⟩
      rw [← rankDelta_swap_marks B.graph
        (B.pathVertex alpha (strandMirror B alpha i))
        (B.pathVertex alpha (strandMirror B alpha j)) D]
      exact hD
    · intro hPosition
      obtain ⟨D, hD⟩ := hClass.mpr (hExceptional.mp hPosition)
      refine ⟨D, ?_⟩
      rw [rankDelta_swap_marks B.graph
        (B.pathVertex alpha (strandMirror B alpha i))
        (B.pathVertex alpha (strandMirror B alpha j)) D]
      exact hD

end Bananas
