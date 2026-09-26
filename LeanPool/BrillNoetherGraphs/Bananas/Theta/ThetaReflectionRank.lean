/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Basics.BananaGeometry

/-!
# The reflected theta pair

On a genus-two banana, a point together with its reflection is a canonical
degree-two divisor.  This is the rank-theoretic exclusion used in the
`SameStrand` argument: a rank-zero pair cannot be a reflected pair.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- A point and its reflection on a theta strand have rank exactly one. -/
theorem rank_strand_reflection_pair_eq_one
    (B : Banana 2) (alpha : Fin 3) (i : B.PathPosition alpha) :
    rank B.graph
      (oneChip (strandVertex B alpha i) +
        oneChip (strandVertex B alpha (strandMirror B alpha i))) = 1 := by
  have hCanonical :
      canonicalDivisor B.graph =
        oneChip (leftEndpoint B) + oneChip (rightEndpoint B) := by
    simpa using canonical_divisor_eq_endpoints B
  have hCanonicalRank : rank B.graph (canonicalDivisor B.graph) = 1 := by
    have hRR := riemann_roch_for_graphs (graphConnected B)
      (canonicalDivisor B.graph)
    rw [sub_self, zero_divisor_rank, degree_of_canonical_divisor,
      B.genus_graph] at hRR
    omega
  have hReflection := endpoint_sum_linearEquiv_strand_reflection B alpha i
  have hRankEq := rank_eq_of_linear_equiv B.graph hReflection
  rw [← hCanonical] at hRankEq
  omega

/-- Consequently, a rank-zero two-chip divisor cannot pair a point with its
strand reflection. -/
theorem ne_strand_reflection_of_pair_rank_zero
    (B : Banana 2) (alpha : Fin 3) (i : B.PathPosition alpha)
    (w : B.graph.V)
    (hRank : rank B.graph
      (oneChip (strandVertex B alpha i) + oneChip w) = 0) :
    w ≠ strandVertex B alpha (strandMirror B alpha i) := by
  intro hw
  subst w
  rw [rank_strand_reflection_pair_eq_one] at hRank
  omega

end Bananas
