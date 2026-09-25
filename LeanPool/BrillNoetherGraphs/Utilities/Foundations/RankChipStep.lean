/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankInvariance

/-!
# Rank change under one marked chip

Adding one effective chip cannot lower rank.  Conversely, subtracting one chip
can lower a specified rank lower bound by at most one.  The latter is proved
directly from the universal effective-subtraction definition of rank.

These two inequalities are the rank-side input for propagating transmission
conditions between adjacent lattice rows.
-/

namespace Utilities

/-- Adding one chip preserves every rank lower bound. -/
theorem rank_add_one_chip_ge
    {G : CFGraph} (D : CFDiv G) (q : G.V) (k : ℤ)
    (hRank : rank G D ≥ k) :
    rank G (D + oneChip q) ≥ k := by
  exact rank_add_effective_ge G D (oneChip q) (eff_one_chip q) k hRank

/-- If `D` has rank at least `k+1`, then removing one chip leaves rank at least
`k`. -/
theorem rank_sub_one_chip_ge_of_rank_ge_succ
    {G : CFGraph} (D : CFDiv G) (q : G.V) (k : ℤ)
    (hRank : rank G D ≥ k + 1) :
    rank G (D - oneChip q) ≥ k := by
  apply (rank_geq_iff G (D - oneChip q) k).mp
  have hRankGeq : rankGeq G D (k + 1) :=
    (rank_geq_iff G D (k + 1)).mpr hRank
  intro A hA
  have hSumEffective : effective (A + oneChip q) :=
    (Eff G).add_mem hA.1 (eff_one_chip q)
  have hSumDegree : deg (A + oneChip q) = k + 1 := by
    rw [deg.map_add, hA.2, deg_one_chip]
  have hWin := hRankGeq (A + oneChip q) ⟨hSumEffective, hSumDegree⟩
  convert hWin using 1
  abel

/-- Numerical corollary: subtracting one chip lowers rank by at most one. -/
theorem rank_sub_one_chip_ge_rank_sub_one
    {G : CFGraph} (D : CFDiv G) (q : G.V) :
    rank G (D - oneChip q) ≥ rank G D - 1 := by
  apply rank_sub_one_chip_ge_of_rank_ge_succ D q (rank G D - 1)
  omega

end Utilities
