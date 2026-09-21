/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.NSMCrossWitness
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffFiring

/-!
# Second distinct-strand witness in Theorem 3.9

This file proves the second explicit rank witness from the distinct-strand
case of corrected Theorem 3.9.  In normalized coordinates the second mark is
the penultimate point of its strand, while the first mark is not the first
interior point.  The extra hypothesis `2 < B.length beta` excludes precisely
the corrected length-two midpoint exception; without it the theorem is false.
-/

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

private theorem secondCrossLinearEquiv_add
    {G : CFGraph} {A B C D : CFDiv G}
    (h₁ : linear_equiv G A B) (h₂ : linear_equiv G C D) :
    linear_equiv G (A + C) (B + D) := by
  unfold linear_equiv at h₁ h₂ ⊢
  have h := (principal_divisors G).add_mem h₁ h₂
  convert h using 1
  abel

private theorem secondCrossLinearEquiv_sub
    {G : CFGraph} {A B C D : CFDiv G}
    (h₁ : linear_equiv G A B) (h₂ : linear_equiv G C D) :
    linear_equiv G (A - C) (B - D) := by
  unfold linear_equiv at h₁ h₂ ⊢
  have h := (principal_divisors G).sub_mem h₁ h₂
  convert h using 1
  abel

private theorem secondCrossLinearEquiv_refl {G : CFGraph} (D : CFDiv G) :
    linear_equiv G D D := by
  unfold linear_equiv
  rw [sub_self]
  exact (principal_divisors G).zero_mem

/-- Two normalized chips at positions `i` and `n - 1` slide to position
`i - 1` and the right endpoint. -/
theorem strand_position_add_penultimate_linearEquiv_right_pred
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (i : B.PathPosition alpha) (hi : 1 < i.val) :
    linear_equiv B.graph
      (one_chip (strandVertex B alpha i) +
        one_chip (strandVertex B alpha ⟨B.length alpha - 1, by
          have := B.length_pos alpha
          omega⟩))
      (one_chip (strandVertex B alpha ⟨i.val - 1, by omega⟩) +
        one_chip (rightEndpoint B)) := by
  have hiPrefix := strand_prefix_linearEquiv B alpha i
  have hPenultimate := strand_prefix_linearEquiv B alpha
    (⟨B.length alpha - 1, by
      have := B.length_pos alpha
      omega⟩ : B.PathPosition alpha)
  have hPred := strand_prefix_linearEquiv B alpha
    (⟨i.val - 1, by omega⟩ : B.PathPosition alpha)
  have hEnd := strand_prefix_linearEquiv B alpha
    (⟨B.length alpha, by omega⟩ : B.PathPosition alpha)
  rw [strandVertex_length B alpha] at hEnd
  have hLeft := secondCrossLinearEquiv_add hiPrefix hPenultimate
  have hRight := secondCrossLinearEquiv_add hPred hEnd
  have hPredCast : ((i.val - 1 : ℕ) : ℤ) = (i.val : ℤ) - 1 := by
    omega
  have hLastCast : ((B.length alpha - 1 : ℕ) : ℤ) =
      (B.length alpha : ℤ) - 1 := by
    have := B.length_pos alpha
    omega
  have hScalar :
      (i.val : ℤ) •
          (one_chip (strandVertex B alpha ⟨1, by omega⟩) -
            one_chip (leftEndpoint B)) +
        ((B.length alpha - 1 : ℕ) : ℤ) •
          (one_chip (strandVertex B alpha ⟨1, by omega⟩) -
            one_chip (leftEndpoint B)) =
      ((i.val - 1 : ℕ) : ℤ) •
          (one_chip (strandVertex B alpha ⟨1, by omega⟩) -
            one_chip (leftEndpoint B)) +
        (B.length alpha : ℤ) •
          (one_chip (strandVertex B alpha ⟨1, by omega⟩) -
            one_chip (leftEndpoint B)) := by
    ext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    rw [hPredCast, hLastCast]
    ring
  have hRight' := hRight
  rw [← hScalar] at hRight'
  have h := hLeft.symm.trans hRight'
  unfold linear_equiv at h ⊢
  convert h using 1
  abel

/-- The second explicit divisor in the distinct-strand proof of corrected
Theorem 3.9 has negative rank difference.  The length assumption excludes
the corrected length-two midpoint exception.

The witness is
`v_(alpha,i) + v_(alpha,n_alpha-1) + v_(beta,1)`.
-/
theorem rankDelta_second_cross_witness_neg
    {g : ℕ} (hg : 3 ≤ g) (B : Banana g)
    (alpha beta : Fin (g + 1)) (i : B.PathPosition alpha)
    (j : B.PathPosition beta)
    (hi : B.IsInteriorPosition alpha i)
    (_hj : B.IsInteriorPosition beta j)
    (hAlphaBeta : alpha ≠ beta)
    (hjPenultimate : j.val + 1 = B.length beta)
    (hiNotOne : i.val ≠ 1)
    (hBetaLength : 2 < B.length beta) :
    rankDelta
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j))
      (one_chip (strandVertex B alpha i) +
        one_chip (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) +
        one_chip (strandVertex B beta ⟨1, by omega⟩)) < 0 := by
  let p : B.PathPosition alpha := ⟨i.val - 1, by omega⟩
  let q : B.PathPosition beta := ⟨2, by omega⟩
  have hi' : 0 < i.val ∧ i.val < B.length alpha := hi
  have hiGtOne : 1 < i.val := by omega
  have hp : B.IsInteriorPosition alpha p := by
    change 0 < i.val - 1 ∧ i.val - 1 < B.length alpha
    omega
  have hq : B.IsInteriorPosition beta q := by
    change 0 < (2 : ℕ) ∧ 2 < B.length beta
    omega
  have hPenultAlpha : B.IsInteriorPosition alpha
      (⟨B.length alpha - 1, by omega⟩ : B.PathPosition alpha) := by
    change 0 < B.length alpha - 1 ∧
      B.length alpha - 1 < B.length alpha
    omega
  have hOneBeta : B.IsInteriorPosition beta
      (⟨1, by omega⟩ : B.PathPosition beta) := by
    change 0 < (1 : ℕ) ∧ 1 < B.length beta
    omega
  have hAlphaSlide :=
    strand_position_add_penultimate_linearEquiv_right_pred B alpha i hiGtOne
  have hBetaShift := crossOneOff_sub_second_mark_shift B beta 1 (by omega)
  have hD : linear_equiv B.graph
      (one_chip (strandVertex B alpha i) +
          one_chip (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) +
        one_chip (strandVertex B beta ⟨1, by omega⟩))
      (one_chip (rightEndpoint B) +
        (one_chip (strandVertex B alpha p) +
          one_chip (strandVertex B beta ⟨1, by omega⟩))) := by
    have h := secondCrossLinearEquiv_add hAlphaSlide
      (secondCrossLinearEquiv_refl
        (one_chip (strandVertex B beta ⟨1, by omega⟩)))
    dsimp [p]
    convert h using 1
    abel
  have hDV : linear_equiv B.graph
      ((one_chip (strandVertex B alpha i) +
          one_chip (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) +
          one_chip (strandVertex B beta ⟨1, by omega⟩)) -
        one_chip (strandVertex B beta j))
      (one_chip (strandVertex B alpha p) +
        one_chip (strandVertex B beta q)) := by
    have hjEq : j = (⟨B.length beta - 1, by omega⟩ : B.PathPosition beta) := by
      apply Fin.ext
      change j.val = B.length beta - 1
      omega
    have hSub := secondCrossLinearEquiv_add hAlphaSlide hBetaShift
    rw [hjEq]
    dsimp [p, q] at hSub ⊢
    unfold linear_equiv at hSub ⊢
    convert hSub using 1
    abel
  have hDUV : linear_equiv B.graph
      ((one_chip (strandVertex B alpha i) +
          one_chip (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) +
          one_chip (strandVertex B beta ⟨1, by omega⟩)) -
        one_chip (strandVertex B alpha i) -
        one_chip (strandVertex B beta j))
      (one_chip (strandVertex B alpha p) +
        one_chip (strandVertex B beta q) -
        one_chip (strandVertex B alpha i)) := by
    have hSub := secondCrossLinearEquiv_sub hDV
      (secondCrossLinearEquiv_refl (one_chip (strandVertex B alpha i)))
    convert hSub using 1
    abel
  have hSemiD : IsSemibreak B
      (one_chip (strandVertex B alpha p) +
        one_chip (strandVertex B beta ⟨1, by omega⟩)) :=
    isSemibreak_two_distinct_strand_chips B alpha beta p _ hp hOneBeta
      hAlphaBeta
  have hSemiDU : IsSemibreak B
      (one_chip (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) +
        one_chip (strandVertex B beta ⟨1, by omega⟩)) :=
    isSemibreak_two_distinct_strand_chips B alpha beta _ _ hPenultAlpha
      hOneBeta hAlphaBeta
  have hSemiDV : IsSemibreak B
      (one_chip (strandVertex B alpha p) +
        one_chip (strandVertex B beta q)) :=
    isSemibreak_two_distinct_strand_chips B alpha beta p q hp hq hAlphaBeta
  have hDegD : deg (one_chip (strandVertex B alpha p) +
      one_chip (strandVertex B beta ⟨1, by omega⟩)) = 2 := by
    rw [deg.map_add, deg_one_chip, deg_one_chip]
    norm_num
  have hDegDU : deg
      (one_chip (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) +
        one_chip (strandVertex B beta ⟨1, by omega⟩)) = 2 := by
    rw [deg.map_add, deg_one_chip, deg_one_chip]
    norm_num
  have hDegDV : deg (one_chip (strandVertex B alpha p) +
      one_chip (strandVertex B beta q)) = 2 := by
    rw [deg.map_add, deg_one_chip, deg_one_chip]
    norm_num
  have hRankD : rank B.graph
      (one_chip (strandVertex B alpha i) +
        one_chip (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) +
        one_chip (strandVertex B beta ⟨1, by omega⟩)) = 0 := by
    rw [rank_eq_of_linear_equiv B.graph hD]
    exact rank_rightEndpoint_add_two_chip_semibreak_eq_zero hg B _ hSemiD hDegD
  have hRankDU : rank B.graph
      ((one_chip (strandVertex B alpha i) +
          one_chip (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) +
          one_chip (strandVertex B beta ⟨1, by omega⟩)) -
        one_chip (strandVertex B alpha i)) = 0 := by
    rw [show (one_chip (strandVertex B alpha i) +
          one_chip (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) +
          one_chip (strandVertex B beta ⟨1, by omega⟩)) -
        one_chip (strandVertex B alpha i) =
        one_chip (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) +
          one_chip (strandVertex B beta ⟨1, by omega⟩) by abel]
    exact rank_semibreak_eq_zero B _ hSemiDU (by rw [hDegDU]; omega)
  have hRankDV : rank B.graph
      ((one_chip (strandVertex B alpha i) +
          one_chip (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) +
          one_chip (strandVertex B beta ⟨1, by omega⟩)) -
        one_chip (strandVertex B beta j)) = 0 := by
    rw [rank_eq_of_linear_equiv B.graph hDV]
    exact rank_semibreak_eq_zero B _ hSemiDV (by rw [hDegDV]; omega)
  have hpx : strandVertex B alpha i ≠ strandVertex B alpha p := by
    intro h
    have hv := congrArg Fin.val (strandVertex_injective B alpha h)
    dsimp [p] at hv
    omega
  have hpy : strandVertex B alpha i ≠ strandVertex B beta q := by
    intro h
    exact hAlphaBeta
      (strand_eq_of_interior_vertex_eq B alpha beta i q hi hq h)
  have hRankDUV : rank B.graph
      ((one_chip (strandVertex B alpha i) +
          one_chip (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) +
          one_chip (strandVertex B beta ⟨1, by omega⟩)) -
        one_chip (strandVertex B alpha i) -
        one_chip (strandVertex B beta j)) = -1 := by
    rw [rank_eq_of_linear_equiv B.graph hDUV]
    exact rank_strand_pair_sub_neg_of_distinct_interior (by omega) B
      alpha beta alpha p q i hp hq hi hAlphaBeta hpx hpy
  unfold rankDelta mark
  rw [hRankD, hRankDU, hRankDV, hRankDUV]
  norm_num

end Bananas
