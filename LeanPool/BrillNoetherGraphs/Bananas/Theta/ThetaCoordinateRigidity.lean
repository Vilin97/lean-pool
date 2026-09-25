/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaBoundarySubmodularity
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffDelta
import LeanPool.BrillNoetherGraphs.Bananas.Classification.GenusTwoDegreeTwo

/-!
# Rigidity of the non-endpoint theta submodularity families

The theta branch of Theorem 4.13 needs the canonical correction in the
genus-two inversion formula to vanish.  Here that is checked directly from
the coordinate families of Corollary 3.6.
-/

namespace Bananas

open Utilities

private theorem linearEquiv_pair_cancel_right
    {G : CFGraph} {A B C : CFDiv G}
    (h : linearEquiv G (A + C) (B + C)) : linearEquiv G A B := by
  unfold linearEquiv at h ⊢
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

private theorem rank_canonical_banana_two (B : Banana 2) :
    rank B.graph (canonicalDivisor B.graph) = 1 := by
  exact rank_canonical_eq_one_of_genus_two (banana_graph_connected B)
    B.genus_graph

private theorem canonical_banana_two_eq_endpoints (B : Banana 2) :
    canonicalDivisor B.graph =
      oneChip (leftEndpoint B) + oneChip (rightEndpoint B) := by
  rw [canonical_divisor_eq_endpoints]
  norm_num

/-- Adding a vertex other than the right endpoint to the left endpoint is
not canonical on a theta. -/
theorem leftEndpoint_add_not_linearEquiv_canonical
    (B : Banana 2) (w : B.graph.V) (hw : w ≠ rightEndpoint B) :
    ¬ linearEquiv B.graph
      (oneChip (leftEndpoint B) + oneChip w)
      (canonicalDivisor B.graph) := by
  intro hCanon
  rw [canonical_banana_two_eq_endpoints] at hCanon
  have hCancel : linearEquiv B.graph (oneChip w)
      (oneChip (rightEndpoint B)) := by
    apply linearEquiv_pair_cancel_right
      (A := oneChip w) (B := oneChip (rightEndpoint B))
      (C := oneChip (leftEndpoint B))
    simpa only [add_comm] using hCanon
  have hDiff : linearEquiv B.graph
      (oneChip (rightEndpoint B) - oneChip w) 0 := by
    unfold linearEquiv at hCancel ⊢
    have hNeg := (principalDivisors B.graph).neg_mem hCancel
    have hExpr :
        0 - (oneChip (rightEndpoint B) - oneChip w) =
          oneChip w - oneChip (rightEndpoint B) := by abel
    have hNegExpr :
        -(oneChip (rightEndpoint B) - oneChip w) =
          oneChip w - oneChip (rightEndpoint B) := by abel
    rw [hExpr]
    rw [← hNegExpr]
    exact hNeg
  exact not_linearEquiv_one_chip_sub (by omega) B hw hDiff

/-- Symmetric endpoint version of `leftEndpoint_add_not_linearEquiv_canonical`. -/
theorem rightEndpoint_add_not_linearEquiv_canonical
    (B : Banana 2) (w : B.graph.V) (hw : w ≠ leftEndpoint B) :
    ¬ linearEquiv B.graph
      (oneChip w + oneChip (rightEndpoint B))
      (canonicalDivisor B.graph) := by
  intro hCanon
  rw [canonical_banana_two_eq_endpoints] at hCanon
  have hCancel : linearEquiv B.graph (oneChip w)
      (oneChip (leftEndpoint B)) := by
    apply linearEquiv_pair_cancel_right
      (A := oneChip w) (B := oneChip (leftEndpoint B))
      (C := oneChip (rightEndpoint B))
    simpa only [add_comm] using hCanon
  have hDiff : linearEquiv B.graph
      (oneChip (leftEndpoint B) - oneChip w) 0 := by
    unfold linearEquiv at hCancel ⊢
    have hNeg := (principalDivisors B.graph).neg_mem hCancel
    have hExpr :
        0 - (oneChip (leftEndpoint B) - oneChip w) =
          oneChip w - oneChip (leftEndpoint B) := by abel
    have hNegExpr :
        -(oneChip (leftEndpoint B) - oneChip w) =
          oneChip w - oneChip (leftEndpoint B) := by abel
    rw [hExpr]
    rw [← hNegExpr]
    exact hNeg
  exact not_linearEquiv_one_chip_sub (by omega) B hw hDiff

/-- Two interior chips on distinct theta strands have rank zero, so cannot
be canonical. -/
theorem distinctInterior_strand_pair_not_linearEquiv_canonical
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hi : B.IsInteriorPosition alpha i)
    (hj : B.IsInteriorPosition beta j) (hab : alpha ≠ beta) :
    ¬ linearEquiv B.graph
      (oneChip (strandVertex B alpha i) + oneChip (strandVertex B beta j))
      (canonicalDivisor B.graph) := by
  intro hCanon
  have hSemi : IsSemibreak B
      (oneChip (strandVertex B alpha i) + oneChip (strandVertex B beta j)) :=
    isSemibreak_two_distinct_strand_chips B alpha beta i j hi hj hab
  have hZero : rank B.graph
      (oneChip (strandVertex B alpha i) + oneChip (strandVertex B beta j)) = 0 :=
    rank_semibreak_eq_zero B _ hSemi (by
      rw [deg.map_add, deg_one_chip, deg_one_chip]
      norm_num)
  have hRank := rank_eq_of_linear_equiv B.graph hCanon
  rw [hZero, rank_canonical_banana_two B] at hRank
  omega

end Bananas
