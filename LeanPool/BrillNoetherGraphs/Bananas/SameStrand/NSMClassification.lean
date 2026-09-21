/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Transmission.FarMarkNegativeAPI
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.LengthTwoCrossMonotonicity
import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.NSMCrossWitness
import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.NSMSecondCrossWitness
import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.SameStrandInteriorNegative
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaExceptionalArithmetic

/-!
# Corrected interior classification for Theorem 3.9

This is the interior-coordinate portion of `thm-NSMForBanana`.  Endpoint
markings require a separate statement because a multivalent vertex has several
strand-coordinate presentations.  Keeping this statement in coordinates makes
the two genuine cross-strand exceptions visible:

* the published near-opposite-endpoint cases; and
* the corrected length-two-midpoint case, in which the other mark may be any
  interior point on another strand.

The proof is intentionally left as a named, documented obligation while the
remaining far-mark rank calculations are assembled.  In particular, it must
not be replaced by the weaker `nonSubmodular_of_rank_pattern` API, whose rank
pattern is itself a hypothesis.
-/

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- The interior-coordinate exceptional alternatives in the corrected form of
Theorem 3.9.  The first two clauses are exchanged by globally swapping the
two multivalent vertices.  The latter two clauses are the correction: a
midpoint on a length-two strand is exceptional against every interior mark on
a distinct strand, not only a near-endpoint mark. -/
def NSMForBananaInteriorException {g : ℕ} (B : Banana g)
    (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β) : Prop :=
  α ≠ β ∧
    ((i.val = 1 ∧ j.val + 1 = B.length β) ∨
      (i.val + 1 = B.length α ∧ j.val = 1) ∨
      (B.length α = 2 ∧ i.val = 1) ∨
      (B.length β = 2 ∧ j.val = 1))

/-- TeX label: `thm-NSMForBanana` (Theorem 3.9), corrected interior-mark
case.

For two strictly interior marked points, either the coordinate pair belongs to
the corrected cross-strand exceptional family, or there is a divisor with
negative marked rank difference.  The two nonexceptional distinct-strand
branches use the paper's explicit three-chip witnesses; the same-strand branch
uses the genus-independent witness in `SameStrandInteriorNegative.lean`. -/
theorem nsmForBanana_interior_classification
    {g : ℕ} (hg : 3 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i) (hj : B.IsInteriorPosition β j) :
    NSMForBananaInteriorException B α β i j ∨
      ∃ D : CFDiv B.graph,
        rankDelta (mark B.graph (strandVertex B α i) (strandVertex B β j)) D < 0 := by
  change 0 < i.val ∧ i.val < B.length α at hi
  change 0 < j.val ∧ j.val < B.length β at hj
  by_cases hαβ : α = β
  · subst β
    right
    exact exists_rankDelta_neg_same_strand_interior_any_order (by omega) B α
      i j hi hj
  · by_cases hjFar : j.val + 1 < B.length β
    · by_cases hiFar : i.val + 1 < B.length α
      · right
        refine ⟨one_chip (strandVertex B α ⟨1, by omega⟩) +
          one_chip (strandVertex B α i) +
          one_chip (strandVertex B β ⟨B.length β - 1, by omega⟩), ?_⟩
        exact rankDelta_first_cross_witness_neg hg B α β i j hi hj hαβ
          hiFar hjFar
      · push Not at hiFar
        have hiPenultimate : i.val + 1 = B.length α := by omega
        by_cases hjOne : j.val = 1
        · left
          exact ⟨hαβ, Or.inr (Or.inl ⟨hiPenultimate, hjOne⟩)⟩
        · by_cases hαLengthTwo : B.length α = 2
          · left
            have hiOne : i.val = 1 := by omega
            exact ⟨hαβ, Or.inr (Or.inr (Or.inl ⟨hαLengthTwo, hiOne⟩))⟩
          · right
            have hαLength : 2 < B.length α := by
              have := B.length_pos α
              omega
            refine ⟨one_chip (strandVertex B β j) +
              one_chip (strandVertex B β ⟨B.length β - 1, by omega⟩) +
              one_chip (strandVertex B α ⟨1, by omega⟩), ?_⟩
            rw [rankDelta_swap_marks]
            exact rankDelta_second_cross_witness_neg hg B β α j i hj hi
              (Ne.symm hαβ) hiPenultimate hjOne hαLength
    · push Not at hjFar
      have hjPenultimate : j.val + 1 = B.length β := by omega
      by_cases hiOne : i.val = 1
      · left
        exact ⟨hαβ, Or.inl ⟨hiOne, hjPenultimate⟩⟩
      · by_cases hβLengthTwo : B.length β = 2
        · left
          have hjOne : j.val = 1 := by omega
          exact ⟨hαβ, Or.inr (Or.inr (Or.inr ⟨hβLengthTwo, hjOne⟩))⟩
        · right
          have hβLength : 2 < B.length β := by
            have := B.length_pos β
            omega
          refine ⟨one_chip (strandVertex B α i) +
            one_chip (strandVertex B α ⟨B.length α - 1, by omega⟩) +
            one_chip (strandVertex B β ⟨1, by omega⟩), ?_⟩
          exact rankDelta_second_cross_witness_neg hg B α β i j hi hj hαβ
            hjPenultimate hiOne hβLength

end Bananas
