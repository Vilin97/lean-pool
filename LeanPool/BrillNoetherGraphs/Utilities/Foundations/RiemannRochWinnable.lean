/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.Duality

/-!
# Degree-specialized Riemann--Roch and winnability

For a divisor of degree `g - 1 + k`, graph Riemann--Roch says that the rank
condition `rank D ≥ k` is exactly winnability of the canonical complement
`K - D`.  This is the form used repeatedly by residual-chip and
common-complement arguments, where the degree bookkeeping is fixed before the
rank condition is applied.
-/

namespace Utilities

/-- At degree `g - 1 + k`, rank at least `k` is equivalent to winnability of
the canonical complement. -/
theorem rank_ge_iff_canonical_sub_winnable_of_degree
    {G : CFGraph} (hG : graph_connected G) (D : CFDiv G) (k : ℤ)
    (hDegree : deg D = (genus G : ℤ) - 1 + k) :
    rank G D ≥ k ↔ winnable G (canonical_divisor G - D) := by
  rw [rank_ge_iff_dual_rank_ge hG D k]
  have hDualRank : dualRank G k (deg D) = 0 := by
    unfold dualRank rectangleWidth
    rw [hDegree]
    ring
  rw [hDualRank]
  rw [← rank_geq_iff]
  exact rank_nonneg_iff_winnable G (canonical_divisor G - D)

/-- Effective-representative form of the degree-specialized Riemann--Roch
criterion.  This is convenient for residual constructions: a rank hypothesis
can be destructed directly into an effective representative of `K - D`. -/
theorem rank_ge_iff_exists_effective_canonical_complement
    {G : CFGraph} (hG : graph_connected G) (D : CFDiv G) (k : ℤ)
    (hDegree : deg D = (genus G : ℤ) - 1 + k) :
    rank G D ≥ k ↔
      ∃ E : CFDiv G, effective E ∧ linear_equiv G (canonical_divisor G - D) E := by
  rw [rank_ge_iff_canonical_sub_winnable_of_degree hG D k hDegree]
  exact winnable_iff_exists_effective G (canonical_divisor G - D)

/-- Complementary form: if `F` has degree `g - 1 - k`, then `K - F` has rank
at least `k` exactly when `F` is winnable. -/
theorem canonical_sub_rank_ge_iff_winnable_of_degree
    {G : CFGraph} (hG : graph_connected G) (F : CFDiv G) (k : ℤ)
    (hDegree : deg F = (genus G : ℤ) - 1 - k) :
    rank G (canonical_divisor G - F) ≥ k ↔ winnable G F := by
  have hComplementDegree :
      deg (canonical_divisor G - F) = (genus G : ℤ) - 1 + k := by
    rw [deg.map_sub, degree_of_canonical_divisor, hDegree]
    ring
  rw [rank_ge_iff_canonical_sub_winnable_of_degree hG
    (canonical_divisor G - F) k hComplementDegree]
  have hDoubleComplement :
      canonical_divisor G - (canonical_divisor G - F) = F := by
    abel
  rw [hDoubleComplement]

/-- Effective-representative version of the complementary criterion. -/
theorem canonical_sub_rank_ge_iff_exists_effective
    {G : CFGraph} (hG : graph_connected G) (F : CFDiv G) (k : ℤ)
    (hDegree : deg F = (genus G : ℤ) - 1 - k) :
    rank G (canonical_divisor G - F) ≥ k ↔
      ∃ E : CFDiv G, effective E ∧ linear_equiv G F E := by
  rw [canonical_sub_rank_ge_iff_winnable_of_degree hG F k hDegree]
  exact winnable_iff_exists_effective G F

/-- The rank-one canonical-complement test used in the width-two and
prescribed-residual constructions. -/
theorem canonical_sub_rank_ge_one_iff_winnable
    {G : CFGraph} (hG : graph_connected G) (F : CFDiv G)
    (hDegree : deg F = (genus G : ℤ) - 2) :
    rank G (canonical_divisor G - F) ≥ 1 ↔ winnable G F := by
  apply canonical_sub_rank_ge_iff_winnable_of_degree hG F 1
  omega

/-- The degree-`g-1` case: a divisor is winnable exactly when its canonical
complement is winnable. -/
theorem degree_genus_sub_one_winnable_iff_complement_winnable
    {G : CFGraph} (hG : graph_connected G) (D : CFDiv G)
    (hDegree : deg D = (genus G : ℤ) - 1) :
    winnable G D ↔ winnable G (canonical_divisor G - D) := by
  constructor
  · intro hWin
    have hRankGeq : rank_geq G D 0 :=
      (rank_nonneg_iff_winnable G D).mpr hWin
    have hRank : rank G D ≥ 0 := (rank_geq_iff G D 0).mp hRankGeq
    exact (rank_ge_iff_canonical_sub_winnable_of_degree hG D 0 (by omega)).mp hRank
  · intro hComp
    have hRank : rank G D ≥ 0 :=
      (rank_ge_iff_canonical_sub_winnable_of_degree hG D 0 (by omega)).mpr hComp
    have hRankGeq : rank_geq G D 0 := (rank_geq_iff G D 0).mpr hRank
    exact (rank_nonneg_iff_winnable G D).mp hRankGeq

end Utilities
