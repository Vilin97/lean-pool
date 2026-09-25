/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.NSMFullClassification

/-!
# Corrected Theorem 1.16

The published `thm:bananaSimple` claims that a banana marking has a
non-submodular divisor whenever one mark is at distance at least two from
both multivalent vertices.  The corrected Theorem 3.9 shows that this is
false: the other mark may be the midpoint of a distinct length-two strand.
In that case every divisor is submodular, no matter where the first interior
mark lies.

This module records the sharp corrected statement.  A normalized coordinate
`p` is far from both endpoints when `2 ≤ p.val` and
`p.val + 2 ≤ B.length alpha`.  If either mark is far, then either the other
mark is the midpoint of a distinct length-two strand, or an explicit divisor
has negative marked rank difference.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- A normalized banana-strand position lies at graph distance at least two
from each of the two multivalent vertices. -/
def FarFromBananaEndpoints {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (p : B.PathPosition alpha) : Prop :=
  2 ≤ p.val ∧ p.val + 2 ≤ B.length alpha

/-- The extra exceptional family missing from the published Theorem 1.16:
one of the marks is the midpoint of a length-two strand distinct from the
strand containing the other mark. -/
def CorrectedBananaSimpleException {g : ℕ} (B : Banana g)
    (alpha beta : Fin (g + 1))
    (i : B.PathPosition alpha) (j : B.PathPosition beta) : Prop :=
  (alpha ≠ beta ∧ B.length beta = 2 ∧ j.val = 1) ∨
  (alpha ≠ beta ∧ B.length alpha = 2 ∧ i.val = 1)

/-- One-sided sharp form of corrected Theorem 1.16.

If the first mark is far from both endpoints, the only exceptional case is
that the second mark is the midpoint of a distinct length-two strand. -/
theorem corrected_bananaSimple_of_first_far
    {g : ℕ} (hg : 3 ≤ g) (B : Banana g) (alpha beta : Fin (g + 1))
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hiFar : FarFromBananaEndpoints B alpha i) :
    (alpha ≠ beta ∧ B.length beta = 2 ∧ j.val = 1) ∨
      ∃ D : CFDiv B.graph,
        rankDelta
          (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) D < 0 := by
  change 2 ≤ i.val ∧ i.val + 2 ≤ B.length alpha at hiFar
  have hi : B.IsInteriorPosition alpha i := by
    change 0 < i.val ∧ i.val < B.length alpha
    exact ⟨by omega, by omega⟩
  by_cases hj : B.IsInteriorPosition beta j
  · rcases nsmForBanana_interior_classification hg B alpha beta i j hi hj with
      hExceptional | hNegative
    · rcases hExceptional with ⟨hAlphaBeta, hNear | hNear | hLengthTwo | hLengthTwo⟩
      · exact False.elim (by
          rcases hNear with ⟨hiOne, _⟩
          exact (by omega : False))
      · exact False.elim (by
          rcases hNear with ⟨hiPenultimate, _⟩
          exact (by omega : False))
      · exact False.elim (by
          rcases hLengthTwo with ⟨hLength, _⟩
          exact (by omega : False))
      · exact Or.inl ⟨hAlphaBeta, hLengthTwo⟩
    · exact Or.inr hNegative
  · change ¬ (0 < j.val ∧ j.val < B.length beta) at hj
    have hjBound : j.val ≤ B.length beta := Nat.le_of_lt_succ j.isLt
    have hjEndpoint : j.val = 0 ∨ j.val = B.length beta := by omega
    rcases hjEndpoint with hjZero | hjLength
    · have hVertex : strandVertex B beta j = leftEndpoint B := by
        have hPosition : j = ⟨0, by omega⟩ := Fin.ext hjZero
        rw [hPosition, strandVertex_zero]
      rcases exists_rankDelta_neg_leftEndpoint_same_strand
          (by omega) B alpha i hi (by omega) with ⟨D, hD⟩
      exact Or.inr ⟨D, by
        rw [hVertex, rankDelta_swap_marks]
        exact hD⟩
    · have hVertex : strandVertex B beta j = rightEndpoint B := by
        have hPosition : j = ⟨B.length beta, by omega⟩ := Fin.ext hjLength
        rw [hPosition, strandVertex_length]
      rcases exists_rankDelta_neg_rightEndpoint_same_strand
          (by omega) B alpha i hi (by omega) with ⟨D, hD⟩
      exact Or.inr ⟨D, by
        rw [hVertex, rankDelta_swap_marks]
        exact hD⟩

/-- Sharp corrected Theorem 1.16 (`thm:bananaSimple`).

If at least one marked coordinate is at distance at least two from both
multivalent vertices, then either the other mark is the midpoint of a
distinct length-two strand, or there is an explicit divisor with negative
marked rank difference. -/
theorem corrected_bananaSimple
    {g : ℕ} (hg : 3 ≤ g) (B : Banana g) (alpha beta : Fin (g + 1))
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hFar : FarFromBananaEndpoints B alpha i ∨
      FarFromBananaEndpoints B beta j) :
    CorrectedBananaSimpleException B alpha beta i j ∨
      ∃ D : CFDiv B.graph,
        rankDelta
          (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) D < 0 := by
  rcases hFar with hiFar | hjFar
  · rcases corrected_bananaSimple_of_first_far hg B alpha beta i j hiFar with
      hExceptional | hNegative
    · exact Or.inl (Or.inl hExceptional)
    · exact Or.inr hNegative
  · rcases corrected_bananaSimple_of_first_far hg B beta alpha j i hjFar with
      hExceptional | hNegative
    · exact Or.inl (Or.inr ⟨hExceptional.1.symm, hExceptional.2⟩)
    · rcases hNegative with ⟨D, hD⟩
      exact Or.inr ⟨D, by
        rw [rankDelta_swap_marks]
        exact hD⟩

end Bananas
