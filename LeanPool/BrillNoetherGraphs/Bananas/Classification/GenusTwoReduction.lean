/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Transmission.RankZeroWitness
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.RankDeltaDuality
import LeanPool.BrillNoetherGraphs.Bananas.Basics.BananaGeometry
import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointInversions
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankOne

/-!
# The genus-two rank reduction

The first part of the theta analysis is independent of strand coordinates:
a negative marked second difference on a genus-two graph with inequivalent
marks is necessarily represented in degree two.
-/

namespace Bananas

open Utilities

private theorem linearEquiv_zero_of_rank_nonneg_degree_zero
    (G : CFGraph) (D : CFDiv G) (hRank : 0 ≤ rank G D) (hDeg : deg D = 0) :
    linear_equiv G D 0 := by
  obtain ⟨E, hEff, hDE⟩ := (rank_nonneg_iff_winnable G D).mp
    ((rank_geq_iff G D 0).mpr hRank)
  have hEDeg : deg E = 0 := by
    rw [← linear_equiv_preserves_deg G D E hDE, hDeg]
  have hE : E = 0 := eff_degree_zero E hEff hEDeg
  simpa [hE] using hDE

/-- A negative second difference cannot occur in degree at most one when the
two marked degree-one classes are distinct. -/
theorem two_le_degree_of_rankDelta_neg
    (M : TwiceMarked) (D : CFDiv M.graph)
    (hDistinct : ¬ linear_equiv M.graph (one_chip M.u - one_chip M.v) 0)
    (hNeg : rankDelta M D < 0) :
    2 ≤ deg D := by
  by_contra hNot
  have hDeg : deg D ≤ 1 := by omega
  have hDuvDeg : deg (D - one_chip M.u - one_chip M.v) < 0 := by
    rw [deg.map_sub, deg.map_sub, deg_one_chip, deg_one_chip]
    omega
  have hDuv : rank M.graph (D - one_chip M.u - one_chip M.v) = -1 :=
    rank_neg_one_of_deg_neg M.graph _ hDuvDeg
  obtain ⟨hDu, hDv, hStep⟩ := (rankDelta_neg_iff_rank_pattern M D).mp hNeg
  have hDuZero : rank M.graph (D - one_chip M.u) = 0 := by omega
  have hDvZero : rank M.graph (D - one_chip M.v) = 0 := by omega
  obtain ⟨Eu, hEuEff, hDuEu⟩ :=
    (rank_nonneg_iff_winnable M.graph (D - one_chip M.u)).mp
      ((rank_geq_iff M.graph _ 0).mpr (by omega :
        0 ≤ rank M.graph (D - one_chip M.u)))
  have hEuDeg : deg Eu = deg D - 1 := by
    rw [← linear_equiv_preserves_deg M.graph (D - one_chip M.u) Eu hDuEu]
    rw [deg.map_sub, deg_one_chip]
  have hDegLower : 1 ≤ deg D := by
    have := deg_of_eff_nonneg Eu hEuEff
    omega
  have hDegEq : deg D = 1 := by omega
  have hDuDeg : deg (D - one_chip M.u) = 0 := by
    rw [deg.map_sub, deg_one_chip, hDegEq]
    norm_num
  have hDvDeg : deg (D - one_chip M.v) = 0 := by
    rw [deg.map_sub, deg_one_chip, hDegEq]
    norm_num
  have hDuEquiv : linear_equiv M.graph (D - one_chip M.u) 0 :=
    linearEquiv_zero_of_rank_nonneg_degree_zero M.graph _ (by omega) hDuDeg
  have hDvEquiv : linear_equiv M.graph (D - one_chip M.v) 0 :=
    linearEquiv_zero_of_rank_nonneg_degree_zero M.graph _ (by omega) hDvDeg
  apply hDistinct
  unfold linear_equiv at hDuEquiv hDvEquiv ⊢
  have hSub := AddSubgroup.sub_mem (principal_divisors M.graph) hDvEquiv hDuEquiv
  convert hSub using 1 ; abel

/-- On a connected genus-two graph, the preceding lower bound and
Riemann--Roch duality force every negative second-difference witness to have
degree exactly two. -/
theorem degree_eq_two_of_rankDelta_neg_genus_two
    (M : TwiceMarked) (D : CFDiv M.graph) (hConn : _root_.graph_connected M.graph)
    (hGenus : genus M.graph = 2)
    (hDistinct : ¬ linear_equiv M.graph (one_chip M.u - one_chip M.v) 0)
    (hNeg : rankDelta M D < 0) :
    deg D = 2 := by
  have hLower := two_le_degree_of_rankDelta_neg M D hDistinct hNeg
  let E : CFDiv M.graph :=
    canonical_divisor M.graph + one_chip M.u + one_chip M.v - D
  have hDualNeg : rankDelta M E < 0 := by
    rw [← rankDelta_canonical_dual M hConn D]
    exact hNeg
  have hDualLower := two_le_degree_of_rankDelta_neg M E hDistinct hDualNeg
  have hEDeg : deg E = 4 - deg D := by
    simp only [E, deg.map_sub, deg.map_add, degree_of_canonical_divisor,
      deg_one_chip, hGenus]
    norm_num
  omega

private theorem rank_one_chip_eq_zero_of_not_linearEquiv
    (M : TwiceMarked)
    (hDistinct : ¬ linear_equiv M.graph (one_chip M.u - one_chip M.v) 0) :
    rank M.graph (one_chip M.u) = 0 := by
  have hWinnable : winnable M.graph (one_chip M.u) :=
    winnable_of_effective M.graph _ (eff_one_chip M.u)
  have hNonneg : 0 ≤ rank M.graph (one_chip M.u) :=
    (rank_geq_iff M.graph _ 0).mp
      ((rank_nonneg_iff_winnable M.graph _).mpr hWinnable)
  have hLt : rank M.graph (one_chip M.u) < 1 := by
    by_contra hNot
    have hRank : rank M.graph (one_chip M.u) ≥ 1 := by omega
    have hUVWin := (rank_ge_one_iff_winnable_sub_one_chip M.graph
      (one_chip M.u)).mp hRank M.v
    obtain ⟨E, hEff, hEquiv⟩ := hUVWin
    have hEDeg : deg E = 0 := by
      rw [← linear_equiv_preserves_deg M.graph _ E hEquiv,
        deg.map_sub, deg_one_chip, deg_one_chip]
      norm_num
    have hZero : E = 0 := eff_degree_zero E hEff hEDeg
    apply hDistinct
    simpa [hZero] using hEquiv
  omega

/-- The complete intrinsic rank reduction used in the theta classification.
The Riemann--Roch term is handled explicitly: in genus two it is `1`, not
`0`, so a possible rank-one degree-two witness must be ruled out using the
inequivalence of the marks. -/
theorem rank_eq_zero_of_rankDelta_neg_genus_two
    (M : TwiceMarked) (D : CFDiv M.graph) (hConn : _root_.graph_connected M.graph)
    (hGenus : genus M.graph = 2)
    (hDistinct : ¬ linear_equiv M.graph (one_chip M.u - one_chip M.v) 0)
    (hNeg : rankDelta M D < 0) :
    rank M.graph D = 0 := by
  have hDeg : deg D = 2 :=
    degree_eq_two_of_rankDelta_neg_genus_two M D hConn hGenus hDistinct hNeg
  have hRR := riemann_roch_for_graphs hConn D
  have hKDeg : deg (canonical_divisor M.graph - D) = 0 := by
    rw [deg.map_sub, degree_of_canonical_divisor, hGenus, hDeg]
    norm_num
  have hKLe : rank M.graph (canonical_divisor M.graph - D) ≤ 0 := by
    by_cases hNonneg : 0 ≤ rank M.graph (canonical_divisor M.graph - D)
    · have hBound := rank_le_degree M.graph
        (canonical_divisor M.graph - D)
        (rank M.graph (canonical_divisor M.graph - D)) hNonneg
        ((rank_geq_iff M.graph _ _).mpr le_rfl)
      omega
    · omega
  have hRankLe : rank M.graph D ≤ 1 := by
    rw [hGenus, hDeg] at hRR
    omega
  have hRankNonneg : 0 ≤ rank M.graph D := by
    obtain ⟨_, _, hStep⟩ := (rankDelta_neg_iff_rank_pattern M D).mp hNeg
    have hDuvBound := rank_geq_neg_one M.graph
      (D - one_chip M.u - one_chip M.v)
    omega
  by_contra hNot
  have hRankOne : rank M.graph D = 1 := by omega
  have hKRank : rank M.graph (canonical_divisor M.graph - D) = 0 := by
    rw [hGenus, hDeg, hRankOne] at hRR
    omega
  have hKEquiv : linear_equiv M.graph (canonical_divisor M.graph - D) 0 :=
    linearEquiv_zero_of_rank_nonneg_degree_zero M.graph _ (by omega) hKDeg
  have hDK : linear_equiv M.graph D (canonical_divisor M.graph) := by
    unfold linear_equiv at hKEquiv ⊢
    simpa [sub_eq_add_neg] using
      AddSubgroup.neg_mem (principal_divisors M.graph) hKEquiv
  have hUVEquiv : linear_equiv M.graph
      (canonical_divisor M.graph + one_chip M.u + one_chip M.v - D)
      (one_chip M.u + one_chip M.v) := by
    unfold linear_equiv at hDK ⊢
    have hNegDK := AddSubgroup.neg_mem (principal_divisors M.graph) hDK
    convert hNegDK using 1 ; abel
  have hUVNeg : rankDelta M (one_chip M.u + one_chip M.v) < 0 := by
    have hDualNeg : rankDelta M
        (canonical_divisor M.graph + one_chip M.u + one_chip M.v - D) < 0 := by
      rw [← rankDelta_canonical_dual M hConn D]
      exact hNeg
    rwa [rankDelta_eq_of_linearEquiv hUVEquiv] at hDualNeg
  obtain ⟨_, hV, hStep⟩ :=
    (rankDelta_neg_iff_rank_pattern M (one_chip M.u + one_chip M.v)).mp hUVNeg
  have hZeroRank : rank M.graph (0 : CFDiv M.graph) = 0 := zero_divisor_rank _
  have hURank : rank M.graph (one_chip M.u) = 1 := by
    have hRearrange :
        one_chip M.u + one_chip M.v - one_chip M.v = one_chip M.u := by abel
    rw [hRearrange] at hV
    have hZeroDiv :
        one_chip M.u + one_chip M.v - one_chip M.u - one_chip M.v = 0 := by
      abel
    rw [hZeroDiv, hZeroRank] at hStep
    omega
  have hUZero := rank_one_chip_eq_zero_of_not_linearEquiv M hDistinct
  omega

/-- Combined form of the genus-two reduction, matching the usable content of
Lemma 3.1(1) in the paper. -/
theorem degree_and_rank_eq_of_rankDelta_neg_genus_two
    (M : TwiceMarked) (D : CFDiv M.graph) (hConn : _root_.graph_connected M.graph)
    (hGenus : genus M.graph = 2)
    (hDistinct : ¬ linear_equiv M.graph (one_chip M.u - one_chip M.v) 0)
    (hNeg : rankDelta M D < 0) :
    deg D = 2 ∧ rank M.graph D = 0 :=
  ⟨degree_eq_two_of_rankDelta_neg_genus_two M D hConn hGenus hDistinct hNeg,
    rank_eq_zero_of_rankDelta_neg_genus_two M D hConn hGenus hDistinct hNeg⟩

end Bananas
