/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaGenusTwoCornerSum

/-!
# Degree-two divisors on a connected genus-two graph

These coordinate-free Riemann--Roch facts are the algebraic core needed for
the theta transmission-characterization proposition in Section 4.  Keeping
them at an abstract graph prevents later theta proofs from unfolding concrete
subdivision vertices during divisor algebra.
-/

namespace Bananas

open Utilities

/-- A degree-zero divisor has rank at most zero. -/
theorem rank_le_zero_of_degree_zero
    (G : CFGraph) (X : CFDiv G) (hDegree : deg X = 0) :
    rank G X ≤ 0 := by
  by_cases hNonneg : 0 ≤ rank G X
  · have hBound := rank_le_degree G X (rank G X) hNonneg
      ((rank_geq_iff G X (rank G X)).mpr le_rfl)
    omega
  · omega

/-- On a connected genus-two graph, a degree-two divisor has rank at most
one. -/
theorem rank_le_one_of_degree_two_genus_two
    {G : CFGraph} (hconn : _root_.graph_connected G) (hgenus : genus G = 2)
    (X : CFDiv G) (hDegree : deg X = 2) :
    rank G X ≤ 1 := by
  have hDualDegree : deg (canonical_divisor G - X) = 0 := by
    rw [deg.map_sub, degree_of_canonical_divisor, hgenus, hDegree]
    norm_num
  have hDual : rank G (canonical_divisor G - X) ≤ 0 :=
    rank_le_zero_of_degree_zero G _ hDualDegree
  have hRR := riemann_roch_for_graphs hconn X
  rw [hgenus, hDegree] at hRR
  omega

/-- The canonical divisor has rank one on every connected genus-two graph. -/
theorem rank_canonical_eq_one_of_genus_two
    {G : CFGraph} (hconn : _root_.graph_connected G) (hgenus : genus G = 2) :
    rank G (canonical_divisor G) = 1 := by
  have hRR := riemann_roch_for_graphs hconn (canonical_divisor G)
  have hZero : canonical_divisor G - canonical_divisor G = 0 := by abel
  rw [degree_of_canonical_divisor, hgenus, hZero, zero_divisor_rank] at hRR
  omega

/-- A rank-one degree-two divisor is the canonical class. -/
theorem linearEquiv_canonical_of_rank_eq_one_degree_two_genus_two
    {G : CFGraph} (hconn : _root_.graph_connected G) (hgenus : genus G = 2)
    (X : CFDiv G) (hDegree : deg X = 2) (hRank : rank G X = 1) :
    linear_equiv G X (canonical_divisor G) := by
  have hDualDegree : deg (canonical_divisor G - X) = 0 := by
    rw [deg.map_sub, degree_of_canonical_divisor, hgenus, hDegree]
    norm_num
  have hRR := riemann_roch_for_graphs hconn X
  rw [hgenus, hDegree, hRank] at hRR
  have hDualRank : 0 ≤ rank G (canonical_divisor G - X) := by omega
  have hZero := linearEquiv_zero_of_rank_nonneg_degree_zero' G
    (canonical_divisor G - X) hDualRank hDualDegree
  unfold linear_equiv at hZero ⊢
  have hNeg := AddSubgroup.neg_mem (principal_divisors G) hZero
  convert hNeg using 1
  abel

/-- On a connected genus-two graph, a degree-two divisor has rank one exactly
when it is linearly equivalent to the canonical divisor. -/
theorem rank_eq_one_iff_linearEquiv_canonical_of_degree_two_genus_two
    {G : CFGraph} (hconn : _root_.graph_connected G) (hgenus : genus G = 2)
    (X : CFDiv G) (hDegree : deg X = 2) :
    rank G X = 1 ↔ linear_equiv G X (canonical_divisor G) := by
  constructor
  · exact linearEquiv_canonical_of_rank_eq_one_degree_two_genus_two
      hconn hgenus X hDegree
  · intro hEquiv
    have hRank := rank_eq_of_linear_equiv G hEquiv
    rw [rank_canonical_eq_one_of_genus_two hconn hgenus] at hRank
    exact hRank

end Bananas
