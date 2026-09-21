/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RiemannRochWinnable
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankInvariance

/-!
# Canonical slack pairs

On a connected graph of genus at least three, split an effective
representative of `K - (x) - (y)` into equal halves.  Restoring the two marked
chips produces complementary degree-`g`, rank-one divisors, each of which
remains winnable after removing the marked pair.

The declarations use the established `MarkedGraphs` namespace for API
compatibility.
-/

namespace MarkedGraphs

open Utilities

/-- A specified divisor satisfying the slack-column near-rectangle conditions
at the marked vertices: degree equal to the genus, rank at least one, and
nonnegative rank after the two marked chips are removed. -/
def IsSlackNearRectangleDivisor
    (H : CFGraph) (x y : H.V) (D : CFDiv H) : Prop :=
  deg D = genus H ∧
  rank H D ≥ 1 ∧
  rank H (D - one_chip x - one_chip y) ≥ 0

/-- Either half of a splitting of the marked canonical residual, restored by
the two marked chips, is a slack near-rectangle divisor. -/
theorem isSlackNearRectangleDivisor_of_canonical_split
    (H : CFGraph) (hH : graph_connected H) (x y : H.V)
    (E F : CFDiv H) (hEEffective : effective E) (hFEffective : effective F)
    (hEDegree : deg E = genus H - 2)
    (hSplit : linear_equiv H
      (canonical_divisor H - (one_chip x + one_chip y)) (E + F)) :
    IsSlackNearRectangleDivisor H x y (E + one_chip x + one_chip y) := by
  have hDegree : deg (E + one_chip x + one_chip y) = genus H := by
    rw [deg.map_add, deg.map_add, deg_one_chip, deg_one_chip, hEDegree]
    ring
  have hERank : rank H E ≥ 0 := by
    apply (rank_geq_iff H E 0).mp
    exact (rank_nonneg_iff_winnable H E).mpr
      (winnable_of_effective H E hEEffective)
  have hFRank : rank H F ≥ 0 := by
    apply (rank_geq_iff H F 0).mp
    exact (rank_nonneg_iff_winnable H F).mpr
      (winnable_of_effective H F hFEffective)
  have hSeam : E + one_chip x + one_chip y - one_chip x - one_chip y = E := by
    abel
  have hComplementEquiv :
      linear_equiv H
        (canonical_divisor H - (E + one_chip x + one_chip y)) F := by
    unfold linear_equiv at hSplit ⊢
    have hDifference :
        F - (canonical_divisor H - (E + one_chip x + one_chip y)) =
          (E + F) - (canonical_divisor H - (one_chip x + one_chip y)) := by
      abel
    rw [hDifference]
    exact hSplit
  have hComplementRank :
      rank H (canonical_divisor H - (E + one_chip x + one_chip y)) ≥ 0 := by
    rw [rank_eq_of_linear_equiv H hComplementEquiv]
    exact hFRank
  have hRR := riemann_roch_for_graphs hH (E + one_chip x + one_chip y)
  rw [hDegree] at hRR
  refine ⟨hDegree, by omega, ?_⟩
  rw [hSeam]
  exact hERank

/-- On a connected graph of genus at least three, every pair of marked
vertices admits complementary slack near-rectangle divisors. -/
theorem exists_canonical_slack_dual_pair
    (H : CFGraph) (hH : graph_connected H) (hGenus : 3 ≤ genus H)
    (x y : H.V) :
    ∃ D₁ D₂ : CFDiv H,
      IsSlackNearRectangleDivisor H x y D₁ ∧
      IsSlackNearRectangleDivisor H x y D₂ ∧
      linear_equiv H (D₁ + D₂)
        (canonical_divisor H + one_chip x + one_chip y) := by
  have hMarkedEffective : effective (one_chip x + one_chip y) := by
    exact (Eff H).add_mem (eff_one_chip x) (eff_one_chip y)
  have hMarkedDegree : deg (one_chip x + one_chip y) = 2 := by
    simp
  have hMarkedRank : rank H (one_chip x + one_chip y) ≥ 0 := by
    apply (rank_geq_iff H (one_chip x + one_chip y) 0).mp
    exact (rank_nonneg_iff_winnable H (one_chip x + one_chip y)).mpr
      (winnable_of_effective H (one_chip x + one_chip y) hMarkedEffective)
  have hResidualDegree :
      deg (canonical_divisor H - (one_chip x + one_chip y)) =
        2 * genus H - 4 := by
    rw [deg.map_sub, degree_of_canonical_divisor, hMarkedDegree]
    ring
  have hResidualRank :
      rank H (canonical_divisor H - (one_chip x + one_chip y)) ≥ 0 := by
    have hRR := riemann_roch_for_graphs hH
      (canonical_divisor H - (one_chip x + one_chip y))
    have hComplement :
        canonical_divisor H -
            (canonical_divisor H - (one_chip x + one_chip y)) =
          one_chip x + one_chip y := by
      abel
    rw [hComplement, hResidualDegree] at hRR
    omega
  have hResidualWinnable :
      winnable H (canonical_divisor H - (one_chip x + one_chip y)) :=
    (rank_nonneg_iff_winnable H
      (canonical_divisor H - (one_chip x + one_chip y))).mp
      ((rank_geq_iff H
        (canonical_divisor H - (one_chip x + one_chip y)) 0).mpr hResidualRank)
  obtain ⟨M, hMEffective, hMEquiv⟩ :=
    (winnable_iff_exists_effective H
      (canonical_divisor H - (one_chip x + one_chip y))).mp hResidualWinnable
  have hMDegree : deg M = 2 * genus H - 4 := by
    have hEq := linear_equiv_preserves_deg H
      (canonical_divisor H - (one_chip x + one_chip y)) M hMEquiv
    omega
  have hHalf : ((genus H - 2).toNat : ℤ) = genus H - 2 :=
    Int.toNat_of_nonneg (by omega)
  obtain ⟨E, F, hEEffective, hFEffective, hEDegree, hFDegree, hMSplit⟩ :=
    effective_divisor_decomposition H M (genus H - 2).toNat (genus H - 2).toNat
      hMEffective (by rw [hMDegree, hHalf]; ring)
  have hEDegree' : deg E = genus H - 2 := hEDegree.trans hHalf
  have hFDegree' : deg F = genus H - 2 := hFDegree.trans hHalf
  have hSplit : linear_equiv H
      (canonical_divisor H - (one_chip x + one_chip y)) (E + F) := by
    rw [← hMSplit]
    exact hMEquiv
  have hSplitSymm : linear_equiv H
      (canonical_divisor H - (one_chip x + one_chip y)) (F + E) := by
    rw [add_comm F E]
    exact hSplit
  refine ⟨E + one_chip x + one_chip y, F + one_chip x + one_chip y,
    isSlackNearRectangleDivisor_of_canonical_split H hH x y E F
      hEEffective hFEffective hEDegree' hSplit,
    isSlackNearRectangleDivisor_of_canonical_split H hH x y F E
      hFEffective hEEffective hFDegree' hSplitSymm, ?_⟩
  unfold linear_equiv at hSplit ⊢
  have hDifference :
      canonical_divisor H + one_chip x + one_chip y -
          (E + one_chip x + one_chip y + (F + one_chip x + one_chip y)) =
        -((E + F) - (canonical_divisor H - (one_chip x + one_chip y))) := by
    abel
  rw [hDifference]
  exact AddSubgroup.neg_mem (principal_divisors H) hSplit

end MarkedGraphs
