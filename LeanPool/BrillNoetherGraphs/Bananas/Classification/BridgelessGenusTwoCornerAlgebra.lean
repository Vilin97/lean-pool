/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Classification.BridgelessGenusTwoNonrecurrence
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaGenusTwoCornerSum
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionAPI
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaInvTauCorrection

/-!
# Genus-two corner algebra without a theta presentation

These are the graph-generic degree slices in the finite proof of Lemma 4.10.
The hypotheses isolate exactly what bridgelessness supplies: every one-chip
divisor has rank zero.
-/

namespace Bananas

open Utilities

/-- In connected genus two, the canonical divisor minus a chip has rank zero
whenever that chip has rank zero. -/
theorem rank_canonical_sub_one_chip_zero_of_genus_two
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (q : G.V)
    (hOne : rank G (one_chip q) = 0) :
    rank G (canonical_divisor G - one_chip q) = 0 := by
  have hRR := riemann_roch_for_graphs hConnected (one_chip q)
  rw [deg_one_chip, hGenus, hOne] at hRR
  omega

/-- The degree-zero slice has the same value as in the theta proof on every
connected genus-two graph. -/
theorem degreeZero_slice_eq_two_mul_rankPlusOne_of_genus_two
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (X : CFDiv G) (hDeg : deg X = 0) :
    rankPlusOne G X * rankPlusOne G (canonical_divisor G - X) =
      2 * rankPlusOne G X := by
  by_cases hZero : linear_equiv G X 0
  · have hRX : rankPlusOne G X = 1 := by
      unfold rankPlusOne
      exact (rank_add_one_eq_one_iff_linearEquiv_zero_of_degree_zero
        G X hDeg).mpr hZero
    have hComp : linear_equiv G (canonical_divisor G - X)
        (canonical_divisor G) := by
      unfold linear_equiv at hZero ⊢
      simpa [sub_eq_add_neg] using hZero
    have hRankEq := rank_eq_of_linear_equiv G hComp
    have hRR := riemann_roch_for_graphs hConnected (canonical_divisor G)
    have hSub : canonical_divisor G - canonical_divisor G = 0 := by abel
    have hRK : rankPlusOne G (canonical_divisor G - X) = 2 := by
      unfold rankPlusOne
      rw [degree_of_canonical_divisor, hGenus, hSub, zero_divisor_rank] at hRR
      rw [hRankEq]
      omega
    rw [hRX, hRK]
    norm_num
  · have hRX : rankPlusOne G X = 0 :=
      rankPlusOne_eq_zero_of_degree_zero_not_principal G X hDeg hZero
    rw [hRX]
    ring

/-- A degree-zero slice remains its principality indicator after the dual
divisor is shifted by one chip. -/
theorem degreeZero_mul_canonical_sub_add_one_chip_of_genus_two
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (X : CFDiv G) (q : G.V)
    (hOne : rank G (one_chip q) = 0) (hDeg : deg X = 0) :
    rankPlusOne G X * rankPlusOne G (canonical_divisor G - (X + one_chip q)) =
      rankPlusOne G X := by
  by_cases hZero : linear_equiv G X 0
  · have hRX : rankPlusOne G X = 1 := by
      unfold rankPlusOne
      exact (rank_add_one_eq_one_iff_linearEquiv_zero_of_degree_zero
        G X hDeg).mpr hZero
    have hComp : linear_equiv G (canonical_divisor G - (X + one_chip q))
        (canonical_divisor G - one_chip q) := by
      unfold linear_equiv at hZero ⊢
      have hX := AddSubgroup.neg_mem (principal_divisors G) hZero
      convert hX using 1
      abel
    have hRankEq := rank_eq_of_linear_equiv G hComp
    have hRComp : rankPlusOne G (canonical_divisor G - (X + one_chip q)) = 1 := by
      unfold rankPlusOne
      rw [hRankEq,
        rank_canonical_sub_one_chip_zero_of_genus_two G hConnected hGenus q hOne]
      norm_num
    rw [hRX, hRComp]
    norm_num
  · have hRX : rankPlusOne G X = 0 :=
      rankPlusOne_eq_zero_of_degree_zero_not_principal G X hDeg hZero
    rw [hRX]
    ring

/-- In genus two, the degree-one slice is idempotent once degree-one
effective divisors have rank zero. -/
theorem degreeOne_slice_eq_rankPlusOne_of_genus_two
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2)
    (hRankZero : ∀ X : CFDiv G, deg X = 1 → 0 ≤ rank G X → rank G X = 0)
    (X : CFDiv G) (hDeg : deg X = 1) :
    rankPlusOne G X * rankPlusOne G (canonical_divisor G - X) =
      rankPlusOne G X := by
  have hRR := riemann_roch_for_graphs hConnected X
  rw [hGenus, hDeg] at hRR
  have hRanks : rank G (canonical_divisor G - X) = rank G X := by omega
  by_cases hNonneg : 0 ≤ rank G X
  · have hRankZero := hRankZero X hDeg hNonneg
    unfold rankPlusOne
    rw [hRanks, hRankZero]
    norm_num
  · have hRankNeg := rank_neg_one_of_not_nonneg G X hNonneg
    unfold rankPlusOne
    rw [hRanks, hRankNeg]
    norm_num

/-- In degree two, the first three marked inclusion--exclusion terms cancel
after multiplication by the canonical complement.  This is the only
degree-two calculation needed before the residual correction term in Lemma
4.10. -/
theorem degreeTwo_first_three_cancel_of_genus_two
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (u v : G.V)
    (hOneU : rank G (one_chip u) = 0)
    (hOneV : rank G (one_chip v) = 0)
    (X : CFDiv G) (hDeg : deg X = 2) :
    (rankPlusOne G X - rankPlusOne G (X - one_chip u) -
        rankPlusOne G (X - one_chip v)) *
      rankPlusOne G (canonical_divisor G - X) = 0 := by
  let Y : CFDiv G := canonical_divisor G - X
  have hYDeg : deg Y = 0 := by
    dsimp [Y]
    rw [deg.map_sub, degree_of_canonical_divisor, hGenus, hDeg]
    norm_num
  by_cases hYZero : linear_equiv G Y 0
  · have hXK : linear_equiv G X (canonical_divisor G) := by
      unfold linear_equiv at hYZero ⊢
      have hNeg := AddSubgroup.neg_mem (principal_divisors G) hYZero
      dsimp [Y] at hNeg
      convert hNeg using 1
      abel
    have hXu : linear_equiv G (X - one_chip u)
        (canonical_divisor G - one_chip u) := by
      unfold linear_equiv at hXK ⊢
      convert hXK using 1
      abel
    have hXv : linear_equiv G (X - one_chip v)
        (canonical_divisor G - one_chip v) := by
      unfold linear_equiv at hXK ⊢
      convert hXK using 1
      abel
    have hRankX := rank_eq_of_linear_equiv G hXK
    have hRankXu := rank_eq_of_linear_equiv G hXu
    have hRankXv := rank_eq_of_linear_equiv G hXv
    have hRR := riemann_roch_for_graphs hConnected (canonical_divisor G)
    have hSub : canonical_divisor G - canonical_divisor G = 0 := by abel
    rw [degree_of_canonical_divisor, hGenus, hSub, zero_divisor_rank] at hRR
    have hRankK : rank G (canonical_divisor G) = 1 := by omega
    have hRankYEq := rank_eq_of_linear_equiv G hYZero
    have hRankY : rank G (canonical_divisor G - X) = 0 := by
      dsimp [Y] at hRankYEq
      rw [hRankYEq, zero_divisor_rank]
    unfold rankPlusOne
    rw [hRankX, hRankXu, hRankXv,
      rank_canonical_sub_one_chip_zero_of_genus_two G hConnected hGenus u hOneU,
      rank_canonical_sub_one_chip_zero_of_genus_two G hConnected hGenus v hOneV,
      hRankK, hRankY]
    norm_num
  · have hRY : rankPlusOne G Y = 0 :=
      rankPlusOne_eq_zero_of_degree_zero_not_principal G Y hYDeg hYZero
    change _ * rankPlusOne G Y = 0
    rw [hRY]
    ring

/-- The degree-zero fixed-twist contribution in the finite inversion sum. -/
theorem degreeZero_twistContribution_eq_of_genus_two
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (u v : G.V) (D : CFDiv G) (b : ℤ) :
    markedRankDelta G u v (fixedDegreeTwist G u v D 0 b) *
        rankPlusOne G (canonical_divisor G - fixedDegreeTwist G u v D 0 b) =
      2 * rankPlusOne G (fixedDegreeTwist G u v D 0 b) := by
  rw [markedRankDelta_eq_rankPlusOne_of_degree_zero G u v _
    (deg_fixedDegreeTwist G u v D 0 b)]
  exact degreeZero_slice_eq_two_mul_rankPlusOne_of_genus_two
    G hConnected hGenus _ (deg_fixedDegreeTwist G u v D 0 b)

/-- The degree-one fixed-twist contribution, with its two degree-zero
boundary terms made explicit. -/
theorem degreeOne_twistContribution_eq_of_genus_two
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (u v : G.V)
    (hOneU : rank G (one_chip u) = 0)
    (hOneV : rank G (one_chip v) = 0)
    (hRankZero : ∀ X : CFDiv G, deg X = 1 → 0 ≤ rank G X → rank G X = 0)
    (D : CFDiv G) (b : ℤ) :
    markedRankDelta G u v (fixedDegreeTwist G u v D 1 b) *
        rankPlusOne G (canonical_divisor G - fixedDegreeTwist G u v D 1 b) =
      rankPlusOne G (fixedDegreeTwist G u v D 1 b) -
        rankPlusOne G (fixedDegreeTwist G u v D 0 b) -
        rankPlusOne G (fixedDegreeTwist G u v D 0 (b + 1)) := by
  let X1 := fixedDegreeTwist G u v D 1 b
  let X0 := fixedDegreeTwist G u v D 0 b
  let X0next := fixedDegreeTwist G u v D 0 (b + 1)
  let Rdual := rankPlusOne G (canonical_divisor G - X1)
  have hDelta : markedRankDelta G u v X1 =
      rankPlusOne G X1 - rankPlusOne G X0 - rankPlusOne G X0next := by
    have hU : X1 - one_chip u = X0 := by
      simpa [X1, X0] using fixedDegreeTwist_sub_u G u v D 1 b
    have hV : X1 - one_chip v = X0next := by
      simpa [X1, X0next] using fixedDegreeTwist_sub_v G u v D 1 b
    have hUVDeg : deg (X1 - one_chip u - one_chip v) < 0 := by
      rw [deg.map_sub, deg.map_sub, deg_one_chip, deg_one_chip]
      simp [X1]
    have hUVRank := rank_neg_one_of_deg_neg G
      (X1 - one_chip u - one_chip v) hUVDeg
    have hUVRank' : rank G (X0 - one_chip v) = -1 := by
      rw [← hU]
      exact hUVRank
    unfold markedRankDelta rankPlusOne
    rw [hU, hV, hUVRank']
    ring
  have hMain : rankPlusOne G X1 * Rdual = rankPlusOne G X1 := by
    simpa [Rdual] using degreeOne_slice_eq_rankPlusOne_of_genus_two
      G hConnected hGenus hRankZero X1
      (deg_fixedDegreeTwist G u v D 1 b)
  have hLeft : rankPlusOne G X0 * Rdual = rankPlusOne G X0 := by
    have hX1 : X1 = X0 + one_chip u := by
      simpa [X1, X0] using fixedDegreeTwist_one_eq_zero_add_u G u v D b
    simpa [Rdual, hX1] using
      degreeZero_mul_canonical_sub_add_one_chip_of_genus_two
        G hConnected hGenus X0 u hOneU (by simp [X0])
  have hRight : rankPlusOne G X0next * Rdual = rankPlusOne G X0next := by
    have hX1 : X1 = X0next + one_chip v := by
      simpa [X1, X0next] using fixedDegreeTwist_one_eq_next_zero_add_v G u v D b
    simpa [Rdual, hX1] using
      degreeZero_mul_canonical_sub_add_one_chip_of_genus_two
        G hConnected hGenus X0next v hOneV (by simp [X0next])
  change markedRankDelta G u v X1 * Rdual = _
  rw [hDelta]
  calc
    (rankPlusOne G X1 - rankPlusOne G X0 - rankPlusOne G X0next) * Rdual =
        rankPlusOne G X1 * Rdual - rankPlusOne G X0 * Rdual -
          rankPlusOne G X0next * Rdual := by ring
    _ = _ := by rw [hMain, hLeft, hRight]

/-- After the degree-two cancellation, only the degree-zero correction
product survives. -/
theorem degreeTwo_twistContribution_eq_of_genus_two
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (u v : G.V)
    (hOneU : rank G (one_chip u) = 0)
    (hOneV : rank G (one_chip v) = 0)
    (D : CFDiv G) (b : ℤ) :
    markedRankDelta G u v (fixedDegreeTwist G u v D 2 b) *
        rankPlusOne G (canonical_divisor G - fixedDegreeTwist G u v D 2 b) =
      rankPlusOne G (fixedDegreeTwist G u v D 0 (b + 1)) *
        rankPlusOne G (canonical_divisor G - fixedDegreeTwist G u v D 2 b) := by
  let X2 := fixedDegreeTwist G u v D 2 b
  let X0next := fixedDegreeTwist G u v D 0 (b + 1)
  let Rdual := rankPlusOne G (canonical_divisor G - X2)
  have hUV : X2 - one_chip u - one_chip v = X0next := by
    simpa [X2, X0next] using fixedDegreeTwist_sub_uv G u v D 2 b
  have hCancel := degreeTwo_first_three_cancel_of_genus_two
    G hConnected hGenus u v hOneU hOneV X2
      (deg_fixedDegreeTwist G u v D 2 b)
  have hExpand : markedRankDelta G u v X2 =
      rankPlusOne G X2 - rankPlusOne G (X2 - one_chip u) -
        rankPlusOne G (X2 - one_chip v) + rankPlusOne G X0next := by
    unfold markedRankDelta rankPlusOne
    rw [hUV]
    ring
  change markedRankDelta G u v X2 * Rdual = rankPlusOne G X0next * Rdual
  rw [hExpand]
  calc
    (rankPlusOne G X2 - rankPlusOne G (X2 - one_chip u) -
          rankPlusOne G (X2 - one_chip v) + rankPlusOne G X0next) * Rdual =
        (rankPlusOne G X2 - rankPlusOne G (X2 - one_chip u) -
          rankPlusOne G (X2 - one_chip v)) * Rdual +
          rankPlusOne G X0next * Rdual := by ring
    _ = rankPlusOne G X0next * Rdual := by
      rw [hCancel]
      ring

/-- Pointwise telescoping of the three fixed-degree slices, now independent
of a theta presentation. -/
theorem threeDegreeTwistContribution_eq_telescoping_of_genus_two
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (u v : G.V)
    (hOneU : rank G (one_chip u) = 0)
    (hOneV : rank G (one_chip v) = 0)
    (hRankZero : ∀ X : CFDiv G, deg X = 1 → 0 ≤ rank G X → rank G X = 0)
    (D : CFDiv G) (b : ℤ) :
    threeDegreeTwistContribution G u v D b =
      rankPlusOne G (fixedDegreeTwist G u v D 1 b) +
        rankPlusOne G (fixedDegreeTwist G u v D 0 b) -
        rankPlusOne G (fixedDegreeTwist G u v D 0 (b + 1)) +
        rankPlusOne G (fixedDegreeTwist G u v D 0 (b + 1)) *
          rankPlusOne G
            (canonical_divisor G - fixedDegreeTwist G u v D 2 b) := by
  unfold threeDegreeTwistContribution
  rw [degreeZero_twistContribution_eq_of_genus_two G hConnected hGenus,
    degreeOne_twistContribution_eq_of_genus_two G hConnected hGenus u v
      hOneU hOneV hRankZero,
    degreeTwo_twistContribution_eq_of_genus_two G hConnected hGenus u v
      hOneU hOneV]
  ring

/-- The three possible complementary-rank values at a selected corner of an
arbitrary connected genus-two graph. -/
noncomputable def bridgelessGenusTwoCornerWeight (G : CFGraph) (X : CFDiv G) : ℤ := by
  classical
  exact if deg X = 0 then 2
    else if deg X = 1 then 1
    else if deg X = 2 ∧ linear_equiv G X (canonical_divisor G) then 1
    else 0

private theorem complement_rank_add_one_eq_two_of_corner_degree_zero'
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (u v : G.V) (X : CFDiv G)
    (hDelta : rankDelta (mark G u v) X = 1) (hDeg : deg X = 0) :
    rank G (canonical_divisor G - X) + 1 = 2 := by
  have hRank := rank_nonneg_of_rankDelta_eq_one (mark G u v) X hDelta
  have hXZero := linearEquiv_zero_of_rank_nonneg_degree_zero'
    G X hRank hDeg
  have hComp : linear_equiv G (canonical_divisor G - X)
      (canonical_divisor G) := by
    unfold linear_equiv at hXZero ⊢
    simpa [sub_eq_add_neg] using hXZero
  have hRankEq := rank_eq_of_linear_equiv G hComp
  have hRR := riemann_roch_for_graphs hConnected (canonical_divisor G)
  have hZero : canonical_divisor G - canonical_divisor G = 0 := by abel
  rw [degree_of_canonical_divisor, hGenus, hZero, zero_divisor_rank] at hRR
  rw [hRankEq]
  omega

private theorem complement_rank_add_one_eq_one_of_corner_degree_one'
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (u v : G.V)
    (hRankZero : ∀ X : CFDiv G, deg X = 1 → 0 ≤ rank G X → rank G X = 0)
    (X : CFDiv G) (hDelta : rankDelta (mark G u v) X = 1)
    (hDeg : deg X = 1) :
    rank G (canonical_divisor G - X) + 1 = 1 := by
  have hNonneg := rank_nonneg_of_rankDelta_eq_one (mark G u v) X hDelta
  have hXRank : rank G X = 0 := hRankZero X hDeg hNonneg
  have hRR := riemann_roch_for_graphs hConnected X
  rw [hGenus, hDeg, hXRank] at hRR
  omega

private theorem complement_rank_add_one_eq_one_iff_canonical_of_degree_two'
    (G : CFGraph) (hGenus : genus G = 2) (X : CFDiv G) (hDeg : deg X = 2) :
    rank G (canonical_divisor G - X) + 1 = 1 ↔
      linear_equiv G X (canonical_divisor G) := by
  have hCompDeg : deg (canonical_divisor G - X) = 0 := by
    rw [deg.map_sub, degree_of_canonical_divisor, hGenus, hDeg]
    norm_num
  rw [rank_add_one_eq_one_iff_linearEquiv_zero_of_degree_zero G _ hCompDeg]
  constructor
  · intro hComp
    unfold linear_equiv at hComp ⊢
    simpa [sub_eq_add_neg] using AddSubgroup.neg_mem (principal_divisors G) hComp
  · intro hCanon
    unfold linear_equiv at hCanon ⊢
    simpa [sub_eq_add_neg] using AddSubgroup.neg_mem (principal_divisors G) hCanon

private theorem complement_rank_add_one_eq_zero_of_three_le_degree'
    (G : CFGraph) (hGenus : genus G = 2) (X : CFDiv G) (hDeg : 3 ≤ deg X) :
    rank G (canonical_divisor G - X) + 1 = 0 := by
  have hCompDeg : deg (canonical_divisor G - X) < 0 := by
    rw [deg.map_sub, degree_of_canonical_divisor, hGenus]
    omega
  rw [rank_neg_one_of_deg_neg G _ hCompDeg]
  norm_num

/-- Exact pointwise genus-two reduction of a selected transmission corner's
complementary rank, without a theta presentation. -/
theorem complement_rank_add_one_eq_bridgelessGenusTwoCornerWeight
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (u v : G.V)
    (hRankZero : ∀ X : CFDiv G, deg X = 1 → 0 ≤ rank G X → rank G X = 0)
    (X : CFDiv G) (hDelta : rankDelta (mark G u v) X = 1) :
    rank G (canonical_divisor G - X) + 1 =
      bridgelessGenusTwoCornerWeight G X := by
  have hDegNonneg : 0 ≤ deg X :=
    degree_nonneg_of_rankDelta_eq_one (mark G u v) X hDelta
  unfold bridgelessGenusTwoCornerWeight
  by_cases hDegZero : deg X = 0
  · simp only [hDegZero, if_pos]
    exact complement_rank_add_one_eq_two_of_corner_degree_zero'
      G hConnected hGenus u v X hDelta hDegZero
  simp only [hDegZero, if_false]
  by_cases hDegOne : deg X = 1
  · simp only [hDegOne, if_pos]
    exact complement_rank_add_one_eq_one_of_corner_degree_one'
      G hConnected hGenus u v hRankZero X hDelta hDegOne
  simp only [hDegOne, if_false]
  by_cases hDegTwo : deg X = 2
  · by_cases hCanon : linear_equiv G X (canonical_divisor G)
    · simp only [hDegTwo, hCanon, and_self, if_pos]
      exact (complement_rank_add_one_eq_one_iff_canonical_of_degree_two'
        G hGenus X hDegTwo).mpr hCanon
    · simp only [hDegTwo, hCanon, and_false, if_false]
      have hLower := rank_geq_neg_one G (canonical_divisor G - X)
      have hCompDeg : deg (canonical_divisor G - X) = 0 := by
        rw [deg.map_sub, degree_of_canonical_divisor, hGenus, hDegTwo]
        norm_num
      have hUpper : rank G (canonical_divisor G - X) ≤ 0 := by
        by_cases hNonneg : 0 ≤ rank G (canonical_divisor G - X)
        · have hBound := rank_le_degree G (canonical_divisor G - X)
            (rank G (canonical_divisor G - X)) hNonneg
            ((rank_geq_iff G _ _).mpr le_rfl)
          omega
        · omega
      have hNe : rank G (canonical_divisor G - X) + 1 ≠ 1 := fun hOne => hCanon
        ((complement_rank_add_one_eq_one_iff_canonical_of_degree_two'
          G hGenus X hDegTwo).mp hOne)
      omega
  · have hThree : 3 ≤ deg X := by omega
    simp only [hDegTwo, false_and, if_false]
    exact complement_rank_add_one_eq_zero_of_three_le_degree'
      G hGenus X hThree

/-- The finite inversion count is the sum of the three-valued corner weights
on every connected genus-two graph satisfying the bridgeless degree-one rank
condition.  This removes the theta presentation from the first half of Lemma
4.10. -/
theorem intCast_kInversionCount_eq_sum_bridgelessGenusTwoCornerWeight
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (u v : G.V)
    (hRankZero : ∀ X : CFDiv G, deg X = 1 → 0 ≤ rank G X → rank G X = 0)
    (D : CFDiv G) (k : ℕ) (tau : ℤ → ℤ) (hk : 0 < k)
    (hTau : IsTransmissionPermutation (mark G u v) D tau)
    (hAffine : IsKAffine k tau) :
    (kInversionCount k tau : ℤ) =
      ∑ b : Fin k, bridgelessGenusTwoCornerWeight G
        (D + tau b • one_chip u - (b : ℤ) • one_chip v) := by
  rw [intCast_kInversionCount_eq_sum_complement_rank
    (mark G u v) D hConnected k tau hk hTau hAffine]
  apply Finset.sum_congr rfl
  intro b _
  have hCorner :
      canonical_divisor G - D - tau b • one_chip u + (b : ℤ) • one_chip v =
        canonical_divisor G - (D + tau b • one_chip u - (b : ℤ) • one_chip v) := by
    abel
  change rank G
      (canonical_divisor G - D - tau b • one_chip u + (b : ℤ) • one_chip v) + 1 = _
  rw [hCorner]
  have hDelta : rankDelta (mark G u v)
      (D + tau b • one_chip u - (b : ℤ) • one_chip v) = 1 := by
    have h := hTau.2 (tau b) b
    change (if tau b = tau b then (1 : ℤ) else 0) =
      rankDelta (mark G u v)
        (D + tau b • one_chip u - (b : ℤ) • one_chip v) at h
    simpa using h.symm
  exact complement_rank_add_one_eq_bridgelessGenusTwoCornerWeight
    G hConnected hGenus u v hRankZero _ hDelta

/-- A selected transmission corner contributes exactly its matching one of
the three fixed-degree slices. -/
theorem bridgelessGenusTwoCornerWeight_eq_threeDegreeTwistContribution
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (u v : G.V)
    (hRankZero : ∀ X : CFDiv G, deg X = 1 → 0 ≤ rank G X → rank G X = 0)
    (D : CFDiv G) (tau : ℤ → ℤ)
    (hTau : IsTransmissionPermutation (mark G u v) D tau) (b : ℤ) :
    bridgelessGenusTwoCornerWeight G (transmissionCorner (mark G u v) D tau b) =
      threeDegreeTwistContribution G u v D b := by
  let C : CFDiv G := D + tau b • one_chip u - b • one_chip v
  have hDeltaC : rankDelta (mark G u v) C = 1 := by
    have h := hTau.2 (tau b) b
    change (if tau b = tau b then (1 : ℤ) else 0) =
      rankDelta (mark G u v) C at h
    simpa using h.symm
  have hNonneg : 0 ≤ deg C :=
    degree_nonneg_of_rankDelta_eq_one (mark G u v) C hDeltaC
  have hDegC : deg C = deg D + tau b - b := by
    unfold C
    rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul, deg_one_chip, deg_one_chip]
    ring
  have hDelta (d : ℤ) :
      markedRankDelta G u v (fixedDegreeTwist G u v D d b) =
        if deg C = d then 1 else 0 := by
    rw [markedRankDelta_eq_rankDelta]
    change rankDelta (mark G u v)
        (D + (d - deg D + b) • one_chip u - b • one_chip v) = _
    have hs := hTau.2 (d - deg D + b) b
    change (if tau b = d - deg D + b then (1 : ℤ) else 0) =
      rankDelta (mark G u v)
        (D + (d - deg D + b) • one_chip u - b • one_chip v) at hs
    by_cases hd : deg C = d
    · rw [if_pos hd]
      have hTauEq : tau b = d - deg D + b := by omega
      simpa [hTauEq] using hs.symm
    · rw [if_neg hd]
      have hTauNe : tau b ≠ d - deg D + b := by
        intro hEq
        apply hd
        omega
      simpa [hTauNe] using hs.symm
  unfold threeDegreeTwistContribution rankPlusOne
  change bridgelessGenusTwoCornerWeight G C = _
  by_cases h0 : deg C = 0
  · have hC0 : C = fixedDegreeTwist G u v D 0 b := by
      unfold C fixedDegreeTwist
      have hCoeff : tau b = 0 - deg D + b := by omega
      rw [hCoeff]
    have hComp := complement_rank_add_one_eq_two_of_corner_degree_zero'
      G hConnected hGenus u v C hDeltaC h0
    rw [hDelta 0, hDelta 1, hDelta 2]
    simp only [h0, if_pos, OfNat.zero_ne_ofNat, if_false, zero_mul, add_zero, one_mul]
    rw [← hC0]
    simpa [bridgelessGenusTwoCornerWeight, h0] using hComp.symm
  by_cases h1 : deg C = 1
  · have hC1 : C = fixedDegreeTwist G u v D 1 b := by
      unfold C fixedDegreeTwist
      have hCoeff : tau b = 1 - deg D + b := by omega
      rw [hCoeff]
    have hComp := complement_rank_add_one_eq_one_of_corner_degree_one'
      G hConnected hGenus u v hRankZero C hDeltaC h1
    rw [hDelta 0, hDelta 1, hDelta 2]
    have h10 : deg C ≠ 0 := by omega
    simp only [h1, if_pos, one_mul]
    rw [← hC1]
    simpa [bridgelessGenusTwoCornerWeight, h10, h1] using hComp.symm
  by_cases h2 : deg C = 2
  · have hC2 : C = fixedDegreeTwist G u v D 2 b := by
      unfold C fixedDegreeTwist
      have hCoeff : tau b = 2 - deg D + b := by omega
      rw [hCoeff]
    have h20 : deg C ≠ 0 := by omega
    have h21 : deg C ≠ 1 := by omega
    rw [hDelta 0, hDelta 1, hDelta 2]
    simp only [h2, if_pos, one_mul]
    rw [← hC2]
    by_cases hCanon : linear_equiv G C (canonical_divisor G)
    · have hComp :=
        (complement_rank_add_one_eq_one_iff_canonical_of_degree_two'
          G hGenus C h2).mpr hCanon
      simpa [bridgelessGenusTwoCornerWeight, h20, h21, h2, hCanon] using hComp.symm
    · have hCompNe :=
        (complement_rank_add_one_eq_one_iff_canonical_of_degree_two'
          G hGenus C h2).not.mpr hCanon
      have hLower := rank_geq_neg_one G (canonical_divisor G - C)
      have hCompDeg : deg (canonical_divisor G - C) = 0 := by
        rw [deg.map_sub, degree_of_canonical_divisor, hGenus, h2]
        norm_num
      have hUpper : rank G (canonical_divisor G - C) ≤ 0 := by
        by_cases hR : 0 ≤ rank G (canonical_divisor G - C)
        · have := rank_le_degree G (canonical_divisor G - C)
            (rank G (canonical_divisor G - C)) hR
            ((rank_geq_iff G _ _).mpr le_rfl)
          omega
        · omega
      have hCompZero : rank G (canonical_divisor G - C) + 1 = 0 := by omega
      simpa [bridgelessGenusTwoCornerWeight, h20, h21, h2, hCanon] using hCompZero.symm
  · have h3 : 3 ≤ deg C := by omega
    have h30 : deg C ≠ 0 := by omega
    have h31 : deg C ≠ 1 := by omega
    rw [hDelta 0, hDelta 1, hDelta 2]
    unfold bridgelessGenusTwoCornerWeight
    simp only [h30, h31, h2, if_false, false_and, zero_mul, add_zero]

/-- Finite three-degree form of the inversion sum on an arbitrary bridgeless
genus-two graph. -/
theorem intCast_kInversionCount_eq_sum_threeDegreeTwistContribution_of_genus_two
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (u v : G.V)
    (hRankZero : ∀ X : CFDiv G, deg X = 1 → 0 ≤ rank G X → rank G X = 0)
    (D : CFDiv G) (k : ℕ) (tau : ℤ → ℤ) (hk : 0 < k)
    (hTau : IsTransmissionPermutation (mark G u v) D tau)
    (hAffine : IsKAffine k tau) :
    (kInversionCount k tau : ℤ) =
      ∑ b : Fin k, threeDegreeTwistContribution G u v D b := by
  rw [intCast_kInversionCount_eq_sum_bridgelessGenusTwoCornerWeight
    G hConnected hGenus u v hRankZero D k tau hk hTau hAffine]
  apply Finset.sum_congr rfl
  intro b _
  have hCorner :
      D + tau b • one_chip u - (b : ℤ) • one_chip v =
        transmissionCorner (mark G u v) D tau b := rfl
  rw [hCorner]
  exact bridgelessGenusTwoCornerWeight_eq_threeDegreeTwistContribution
    G hConnected hGenus u v hRankZero D tau hTau b

private theorem rankPlusOne_fixedDegreeTwist_add_torsion'
    (G : CFGraph) (u v : G.V) (D : CFDiv G) (d b : ℤ) (k : ℕ)
    (hk : TorsionWitness (mark G u v) k) :
    rankPlusOne G (fixedDegreeTwist G u v D d (b + k)) =
      rankPlusOne G (fixedDegreeTwist G u v D d b) := by
  have hEquiv := degreeTwistInt_add_torsion_linearEquiv hk D d b
  have hRank := rank_eq_of_linear_equiv G hEquiv
  change rank G
      (D + (d - deg D + (b + k)) • one_chip u - (b + k) • one_chip v) =
    rank G (D + (d - deg D + b) • one_chip u - b • one_chip v) at hRank
  unfold rankPlusOne
  simpa [fixedDegreeTwist] using congrArg (fun r : ℤ ↦ r + 1) hRank

private theorem sum_rankPlusOne_fixedDegreeTwist_zero_sub_next_eq_zero'
    (G : CFGraph) (u v : G.V) (D : CFDiv G) (k : ℕ)
    (hk : TorsionWitness (mark G u v) k) :
    ∑ b : Fin k,
        (rankPlusOne G (fixedDegreeTwist G u v D 0 b.val) -
          rankPlusOne G (fixedDegreeTwist G u v D 0 (b.val + 1))) = 0 := by
  let f : ℕ → ℤ := fun n ↦ rankPlusOne G (fixedDegreeTwist G u v D 0 n)
  let g : ℕ → ℤ := fun n ↦ f n - f (n + 1)
  change ∑ b : Fin k, g b.val = 0
  rw [Fin.sum_univ_eq_sum_range]
  change ∑ n ∈ Finset.range k, (f n - f (n + 1)) = 0
  rw [Finset.sum_range_sub']
  have hPeriod := rankPlusOne_fixedDegreeTwist_add_torsion'
    G u v D 0 0 k hk
  have hPeriod' : f k = f 0 := by simpa [f] using hPeriod
  rw [hPeriod']
  simp

private theorem correctionProduct_eq_zero_of_not_mark_pair_canonical'
    (G : CFGraph) (hGenus : genus G = 2) (u v : G.V) (D : CFDiv G) (b : ℤ)
    (hRigid : ¬ linear_equiv G (one_chip u + one_chip v) (canonical_divisor G)) :
    rankPlusOne G (fixedDegreeTwist G u v D 0 (b + 1)) *
      rankPlusOne G (canonical_divisor G - fixedDegreeTwist G u v D 2 b) = 0 := by
  let A : CFDiv G := fixedDegreeTwist G u v D 0 (b + 1)
  let Y : CFDiv G := canonical_divisor G - fixedDegreeTwist G u v D 2 b
  have hDegA : deg A = 0 := by simp [A]
  have hDegY : deg Y = 0 := by simp [Y, degree_of_canonical_divisor, hGenus]
  by_cases hA : linear_equiv G A 0
  · by_cases hY : linear_equiv G Y 0
    · exfalso
      apply hRigid
      unfold linear_equiv at hA hY ⊢
      have hSum := AddSubgroup.add_mem (principal_divisors G) hA hY
      have hNeg := AddSubgroup.neg_mem (principal_divisors G) hSum
      convert hNeg using 1
      ext x
      simp [A, Y, fixedDegreeTwist]
      ring
    · have hZero := rankPlusOne_eq_zero_of_degree_zero_not_principal G Y hDegY hY
      change rankPlusOne G A * rankPlusOne G Y = 0
      rw [hZero, mul_zero]
  · have hZero := rankPlusOne_eq_zero_of_degree_zero_not_principal G A hDegA hA
    change rankPlusOne G A * rankPlusOne G Y = 0
    rw [hZero, zero_mul]

private theorem sum_rankPlusOne_degreeOne_eq_effectiveResidues_ncard'
    (G : CFGraph)
    (hRankZero : ∀ X : CFDiv G, deg X = 1 → 0 ≤ rank G X → rank G X = 0)
    (u v : G.V) (D : CFDiv G) (k : ℕ) :
    ∑ b : Fin k, rankPlusOne G (fixedDegreeTwist G u v D 1 b.val) =
      ((effectiveDegreeOneTwistResidues (mark G u v) D k).ncard : ℤ) := by
  classical
  let S : Set (Fin k) := effectiveDegreeOneTwistResidues (mark G u v) D k
  have hS : S.Finite := Set.toFinite S
  calc
    ∑ b : Fin k, rankPlusOne G (fixedDegreeTwist G u v D 1 b.val) =
        ∑ b : Fin k, if b ∈ S then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : b ∈ S
      · have hNonneg : 0 ≤ rank G (fixedDegreeTwist G u v D 1 b.val) := by
          change 0 ≤ rank G
            (D + (1 - deg D + b.val) • one_chip u - b.val • one_chip v)
          change 0 ≤ rank G
            (D + (1 - deg D + b.val) • one_chip u - b.val • one_chip v) at hb
          exact hb
        have hRank := hRankZero (fixedDegreeTwist G u v D 1 b.val)
          (deg_fixedDegreeTwist G u v D 1 b.val) hNonneg
        simp [rankPlusOne, hb, hRank]
      · have hNotNonneg : ¬ 0 ≤ rank G (fixedDegreeTwist G u v D 1 b.val) := by
          intro hNonneg
          apply hb
          change 0 ≤ rank G
            (D + (1 - deg D + b.val) • one_chip u - b.val • one_chip v)
          simpa [fixedDegreeTwist] using hNonneg
        have hRank := rank_neg_one_of_not_nonneg G
          (fixedDegreeTwist G u v D 1 b.val) hNotNonneg
        simp [rankPlusOne, hb, hRank]
    _ = ∑ _b ∈ hS.toFinset, (1 : ℤ) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext b
        simp []
      intro b _
      simp []
    _ = (S.ncard : ℤ) := by
      rw [Set.ncard_eq_toFinset_card S hS]
      simp
    _ = ((effectiveDegreeOneTwistResidues (mark G u v) D k).ncard : ℤ) := by
      rfl

/-- Correction-free, arbitrary bridgeless genus-two form of Lemma 4.10. -/
theorem intCast_kInversionCount_eq_effectiveResidues_ncard_of_bridgeless_rigid
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (u v : G.V)
    (hOneU : rank G (one_chip u) = 0)
    (hOneV : rank G (one_chip v) = 0)
    (hRankZero : ∀ X : CFDiv G, deg X = 1 → 0 ≤ rank G X → rank G X = 0)
    (D : CFDiv G) (k : ℕ) (tau : ℤ → ℤ)
    (hk : TorsionWitness (mark G u v) k)
    (hTau : IsTransmissionPermutation (mark G u v) D tau)
    (hAffine : IsKAffine k tau)
    (hRigid : ¬ linear_equiv G (one_chip u + one_chip v) (canonical_divisor G)) :
    (kInversionCount k tau : ℤ) =
      ((effectiveDegreeOneTwistResidues (mark G u v) D k).ncard : ℤ) := by
  have hkPos : 0 < k := hk.1
  rw [intCast_kInversionCount_eq_sum_threeDegreeTwistContribution_of_genus_two
    G hConnected hGenus u v hRankZero D k tau hkPos hTau hAffine]
  calc
    ∑ b : Fin k, threeDegreeTwistContribution G u v D b =
        ∑ b : Fin k,
          (rankPlusOne G (fixedDegreeTwist G u v D 1 b.val) +
            (rankPlusOne G (fixedDegreeTwist G u v D 0 b.val) -
              rankPlusOne G (fixedDegreeTwist G u v D 0 (b.val + 1))) +
            rankPlusOne G (fixedDegreeTwist G u v D 0 (b.val + 1)) *
              rankPlusOne G (canonical_divisor G - fixedDegreeTwist G u v D 2 b.val)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [threeDegreeTwistContribution_eq_telescoping_of_genus_two
        G hConnected hGenus u v hOneU hOneV hRankZero]
      ring
    _ = ((∑ b : Fin k, rankPlusOne G (fixedDegreeTwist G u v D 1 b.val)) +
          ∑ b : Fin k, (rankPlusOne G (fixedDegreeTwist G u v D 0 b.val) -
            rankPlusOne G (fixedDegreeTwist G u v D 0 (b.val + 1)))) +
        ∑ b : Fin k, rankPlusOne G (fixedDegreeTwist G u v D 0 (b.val + 1)) *
          rankPlusOne G (canonical_divisor G - fixedDegreeTwist G u v D 2 b.val) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = ((effectiveDegreeOneTwistResidues (mark G u v) D k).ncard : ℤ) := by
      rw [sum_rankPlusOne_fixedDegreeTwist_zero_sub_next_eq_zero' G u v D k hk,
        sum_rankPlusOne_degreeOne_eq_effectiveResidues_ncard' G hRankZero u v D k]
      have hCorrection :
          ∑ b : Fin k, rankPlusOne G (fixedDegreeTwist G u v D 0 (b.val + 1)) *
            rankPlusOne G (canonical_divisor G - fixedDegreeTwist G u v D 2 b.val) = 0 := by
        apply Finset.sum_eq_zero
        intro b _
        exact correctionProduct_eq_zero_of_not_mark_pair_canonical'
          G hGenus u v D b hRigid
      rw [hCorrection]
      ring

/-- Natural-number form of the correction-free bridgeless genus-two
inversion identity. -/
theorem kInversionCount_eq_effectiveResidues_ncard_of_bridgeless_rigid
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (u v : G.V)
    (hOneU : rank G (one_chip u) = 0)
    (hOneV : rank G (one_chip v) = 0)
    (hRankZero : ∀ X : CFDiv G, deg X = 1 → 0 ≤ rank G X → rank G X = 0)
    (D : CFDiv G) (k : ℕ) (tau : ℤ → ℤ)
    (hk : TorsionWitness (mark G u v) k)
    (hTau : IsTransmissionPermutation (mark G u v) D tau)
    (hAffine : IsKAffine k tau)
    (hRigid : ¬ linear_equiv G (one_chip u + one_chip v) (canonical_divisor G)) :
    kInversionCount k tau =
      (effectiveDegreeOneTwistResidues (mark G u v) D k).ncard := by
  exact_mod_cast
    intCast_kInversionCount_eq_effectiveResidues_ncard_of_bridgeless_rigid
      G hConnected hGenus u v hOneU hOneV hRankZero D k tau hk hTau hAffine hRigid

/-- The full arbitrary-bridgeless version of Theorem 4.8.  `TwoEdgeCutCondition`
is the library's literal no-bridge condition; the nontriviality hypothesis
excludes the vacuous one-vertex graph, where a one-chip divisor has rank one.
-/
theorem bridgelessGenusTwoRigid_kGeneral_iff_nonRecurrent
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hCut : TwoEdgeCutCondition G) (hNontrivial : ∃ p q : G.V, p ≠ q)
    (hGenus : genus G = 2) (u v : G.V) (k : ℕ)
    (hSub : AllSubmodular (mark G u v))
    (hTO : IsTorsionOrder (mark G u v) k)
    (hRigid : ¬ linear_equiv G (one_chip u + one_chip v) (canonical_divisor G)) :
    KGeneralTransmission (mark G u v) k ↔ NonRecurrent (mark G u v) k := by
  have hOne (w : G.V) : rank G (one_chip w) = 0 :=
    rank_one_chip_eq_zero_of_twoEdgeCutCondition G hConnected hCut hNontrivial w
  have hRankZero : ∀ X : CFDiv G, deg X = 1 → 0 ≤ rank G X → rank G X = 0 :=
    fun X hDeg hRank =>
      rank_eq_zero_of_degree_one_rank_nonneg_of_twoEdgeCutCondition
        G hConnected hCut hNontrivial X hDeg hRank
  constructor
  · intro hKGT
    apply nonRecurrent_of_kGeneralTransmission_of_effectiveResidueFormula
      G u v k hConnected hCut hNontrivial hGenus
    · intro w tau hTau hAffine
      exact kInversionCount_eq_effectiveResidues_ncard_of_bridgeless_rigid
        G hConnected hGenus u v (hOne u) (hOne v) hRankZero (one_chip w)
          k tau hTO.1 hTau hAffine hRigid
    · exact hKGT
  · intro hNonrec
    refine ⟨hTO.1, hSub, ?_⟩
    intro D
    obtain ⟨tau, hTau, hAffine, hFinite⟩ :=
      exists_affine_transmission_of_allSubmodular hConnected hTO.1 hSub D
    refine ⟨tau, hTau, hAffine, hFinite, ?_⟩
    have hCount :=
      effectiveDegreeOneTwistResidues_ncard_le_two_of_nonRecurrent_bridgeless
        G u v D k hConnected hCut hNontrivial hTO hNonrec
    rw [kInversionCount_eq_effectiveResidues_ncard_of_bridgeless_rigid
      G hConnected hGenus u v (hOne u) (hOne v) hRankZero D k tau
        hTO.1 hTau hAffine hRigid]
    have hGenusNat : Int.toNat (genus (mark G u v).graph) = 2 := by
      change Int.toNat (genus G) = 2
      rw [hGenus]
      rfl
    simpa [hGenusNat] using hCount

private theorem fin_eq_of_shifted_degreeTwist_linearEquiv_zero'
    {G : CFGraph} {u v : G.V} {D : CFDiv G} {k : ℕ}
    (hk : IsTorsionOrder (mark G u v) k) {b c : Fin k}
    (hb : linear_equiv G (fixedDegreeTwist G u v D 0 ((b : ℤ) + 1)) 0)
    (hc : linear_equiv G (fixedDegreeTwist G u v D 0 ((c : ℤ) + 1)) 0) :
    b = c := by
  have hbc : linear_equiv G
      (degreeTwistInt (mark G u v) D 0 ((b : ℤ) + 1))
      (degreeTwistInt (mark G u v) D 0 ((c : ℤ) + 1)) := hb.trans hc.symm
  have hDvd := isTorsionOrder_dvd_natAbs_sub_of_degreeTwistInt_linearEquiv
    hk D 0 ((b : ℤ) + 1) ((c : ℤ) + 1) hbc
  have hbLt : (b : ℤ) < k := by exact_mod_cast b.isLt
  have hcLt : (c : ℤ) < k := by exact_mod_cast c.isLt
  have hb0 : (0 : ℤ) ≤ (b : ℤ) := by positivity
  have hc0 : (0 : ℤ) ≤ (c : ℤ) := by positivity
  by_contra hne
  have hDiff : ((b : ℤ) + 1) - ((c : ℤ) + 1) ≠ 0 := by
    intro h
    exact hne (Fin.ext (by exact_mod_cast (by omega : (b : ℤ) = (c : ℤ))))
  have hPos : 0 < (((b : ℤ) + 1) - ((c : ℤ) + 1)).natAbs :=
    Int.natAbs_pos.mpr hDiff
  have hkLe : k ≤ (((b : ℤ) + 1) - ((c : ℤ) + 1)).natAbs :=
    Nat.le_of_dvd hPos hDvd
  have hLt : ((((b : ℤ) + 1) - ((c : ℤ) + 1)).natAbs : ℤ) < k := by
    rw [Int.natCast_natAbs, abs_lt]
    omega
  have hkLe' : (k : ℤ) ≤ ((((b : ℤ) + 1) - ((c : ℤ) + 1)).natAbs : ℤ) := by
    exact_mod_cast hkLe
  omega

private theorem sum_correctionProduct_eq_invTauCorrection_of_genus_two
    (G : CFGraph) (hGenus : genus G = 2) (u v : G.V)
    (D : CFDiv G) (k : ℕ) (hk : IsTorsionOrder (mark G u v) k) :
    ∑ b : Fin k,
        rankPlusOne G (fixedDegreeTwist G u v D 0 ((b : ℤ) + 1)) *
          rankPlusOne G (canonical_divisor G - fixedDegreeTwist G u v D 2 (b : ℤ)) =
      invTauCorrection (mark G u v) D := by
  classical
  have hDegA : ∀ b : ℤ, deg (fixedDegreeTwist G u v D 0 b) = 0 := by
    intro b
    exact deg_fixedDegreeTwist G u v D 0 b
  have hDegY : ∀ b : ℤ,
      deg (canonical_divisor G - fixedDegreeTwist G u v D 2 b) = 0 := by
    intro b
    rw [deg.map_sub, degree_of_canonical_divisor, hGenus, deg_fixedDegreeTwist]
    norm_num
  have hYiff : ∀ b : ℤ,
      linear_equiv G (fixedDegreeTwist G u v D 0 (b + 1)) 0 →
        (linear_equiv G (canonical_divisor G - fixedDegreeTwist G u v D 2 b) 0 ↔
          linear_equiv G (one_chip u + one_chip v) (canonical_divisor G)) := by
    intro b hA
    rw [fixedDegreeTwist_two_eq_next_zero_add_uv]
    exact canonical_sub_add_marks_linearEquiv_zero_iff hA
  by_cases hCond :
      (∃ b : ℤ, linear_equiv G (degreeTwistInt (mark G u v) D 0 b) 0) ∧
        linear_equiv G (one_chip u + one_chip v) (canonical_divisor G)
  · obtain ⟨⟨b₀, hb₀⟩, hUV⟩ := hCond
    have hkPos : 0 < k := hk.1.1
    have hkZ : (0 : ℤ) < k := by exact_mod_cast hkPos
    have hRes0 : 0 ≤ (b₀ - 1) % k := Int.emod_nonneg _ (by omega)
    have hResLt : (b₀ - 1) % k < k := Int.emod_lt_of_pos _ hkZ
    have hcLt : ((b₀ - 1) % k).toNat < k := by
      have := (Int.toNat_lt hRes0).mpr hResLt
      exact_mod_cast this
    have hval : ((((b₀ - 1) % k).toNat : ℤ) + 1) % k = b₀ % k := by
      rw [Int.toNat_of_nonneg hRes0, Int.emod_add_emod]
      congr 1
      ring
    have hA : linear_equiv G
        (fixedDegreeTwist G u v D 0 ((((b₀ - 1) % k).toNat : ℤ) + 1)) 0 :=
      degreeTwistInt_linearEquiv_zero_of_emod_eq hk.1 D 0 _ b₀ hval hb₀
    refine (Finset.sum_eq_single (⟨((b₀ - 1) % k).toNat, hcLt⟩ : Fin k)
      ?_ ?_).trans ?_
    · intro b _ hbne
      apply rankPlusOne_mul_eq_zero_of_not_linearEquiv_zero_left
        _ _ (hDegA _)
      intro hb
      exact hbne (fin_eq_of_shifted_degreeTwist_linearEquiv_zero' hk hb hA)
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
    · have hY : linear_equiv G (canonical_divisor G -
          fixedDegreeTwist G u v D 2 (((b₀ - 1) % k).toNat : ℤ)) 0 :=
        (hYiff _ hA).mpr hUV
      have hOne := rankPlusOne_mul_eq_one_of_linearEquiv_zero
        (fixedDegreeTwist G u v D 0 ((((b₀ - 1) % k).toNat : ℤ) + 1))
        (canonical_divisor G - fixedDegreeTwist G u v D 2
          (((b₀ - 1) % k).toNat : ℤ))
        (hDegA _) (hDegY _) hA hY
      rw [hOne, invTauCorrection_mark, if_pos ⟨⟨b₀, hb₀⟩, hUV⟩]
  · have hZero : ∀ b : Fin k,
        rankPlusOne G (fixedDegreeTwist G u v D 0 ((b : ℤ) + 1)) *
          rankPlusOne G (canonical_divisor G - fixedDegreeTwist G u v D 2 (b : ℤ)) = 0 := by
      intro b
      by_cases hA : linear_equiv G
          (fixedDegreeTwist G u v D 0 ((b : ℤ) + 1)) 0
      · apply rankPlusOne_mul_eq_zero_of_not_linearEquiv_zero_right
          _ _ (hDegY _)
        intro hY
        exact hCond ⟨⟨(b : ℤ) + 1, hA⟩, (hYiff _ hA).mp hY⟩
      · exact rankPlusOne_mul_eq_zero_of_not_linearEquiv_zero_left
          _ _ (hDegA _) hA
    rw [Finset.sum_congr rfl (fun b _ => hZero b), invTauCorrection_mark,
      if_neg hCond]
    simp

/-- Full arbitrary-bridgeless genus-two form of Lemma 4.10, including the
canonical correction term. -/
theorem intCast_kInversionCount_eq_effectiveResidues_add_correction_of_bridgeless
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hGenus : genus G = 2) (u v : G.V)
    (hOneU : rank G (one_chip u) = 0)
    (hOneV : rank G (one_chip v) = 0)
    (hRankZero : ∀ X : CFDiv G, deg X = 1 → 0 ≤ rank G X → rank G X = 0)
    (D : CFDiv G) (k : ℕ) (tau : ℤ → ℤ)
    (hk : IsTorsionOrder (mark G u v) k)
    (hTau : IsTransmissionPermutation (mark G u v) D tau)
    (hAffine : IsKAffine k tau) :
    (kInversionCount k tau : ℤ) =
      ((effectiveDegreeOneTwistResidues (mark G u v) D k).ncard : ℤ) +
        invTauCorrection (mark G u v) D := by
  rw [intCast_kInversionCount_eq_sum_threeDegreeTwistContribution_of_genus_two
    G hConnected hGenus u v hRankZero D k tau hk.1.1 hTau hAffine]
  calc
    ∑ b : Fin k, threeDegreeTwistContribution G u v D b =
        ∑ b : Fin k,
          (rankPlusOne G (fixedDegreeTwist G u v D 1 b.val) +
            (rankPlusOne G (fixedDegreeTwist G u v D 0 b.val) -
              rankPlusOne G (fixedDegreeTwist G u v D 0 (b.val + 1))) +
            rankPlusOne G (fixedDegreeTwist G u v D 0 (b.val + 1)) *
              rankPlusOne G (canonical_divisor G - fixedDegreeTwist G u v D 2 b.val)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [threeDegreeTwistContribution_eq_telescoping_of_genus_two
        G hConnected hGenus u v hOneU hOneV hRankZero]
      ring
    _ = ((∑ b : Fin k, rankPlusOne G (fixedDegreeTwist G u v D 1 b.val)) +
          ∑ b : Fin k, (rankPlusOne G (fixedDegreeTwist G u v D 0 b.val) -
            rankPlusOne G (fixedDegreeTwist G u v D 0 (b.val + 1)))) +
        ∑ b : Fin k, rankPlusOne G (fixedDegreeTwist G u v D 0 (b.val + 1)) *
          rankPlusOne G (canonical_divisor G - fixedDegreeTwist G u v D 2 b.val) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = ((effectiveDegreeOneTwistResidues (mark G u v) D k).ncard : ℤ) +
          invTauCorrection (mark G u v) D := by
      rw [sum_rankPlusOne_fixedDegreeTwist_zero_sub_next_eq_zero' G u v D k hk.1,
        sum_rankPlusOne_degreeOne_eq_effectiveResidues_ncard' G hRankZero u v D k,
        sum_correctionProduct_eq_invTauCorrection_of_genus_two G hGenus u v D k hk]
      ring

/-- TeX label: `lem:invtau` (Lemma 4.10), at the paper's full bridgeless
genus-two scope.

`TwoEdgeCutCondition` is the formal no-bridge condition.  The explicit
nontriviality hypothesis excludes the one-vertex edgeless graph, whose
degree-one class has rank one and is not covered by the paper's intended
bridgeless convention. -/
theorem bridgeless_genusTwo_invTau_formula
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hCut : TwoEdgeCutCondition G) (hNontrivial : ∃ p q : G.V, p ≠ q)
    (hGenus : genus G = 2) (u v : G.V) (D : CFDiv G)
    (k : ℕ) (τ : ℤ → ℤ)
    (hTO : IsTorsionOrder (mark G u v) k)
    (hτ : IsTransmissionPermutation (mark G u v) D τ)
    (hAffine : IsKAffine k τ) :
    (kInversionCount k τ : ℤ) =
      ((effectiveDegreeOneTwistResidues (mark G u v) D k).ncard : ℤ) +
        invTauCorrection (mark G u v) D := by
  have hOne (w : G.V) : rank G (one_chip w) = 0 :=
    rank_one_chip_eq_zero_of_twoEdgeCutCondition G hConnected hCut hNontrivial w
  have hRankZero : ∀ X : CFDiv G, deg X = 1 → 0 ≤ rank G X → rank G X = 0 :=
    fun X hDeg hRank =>
      rank_eq_zero_of_degree_one_rank_nonneg_of_twoEdgeCutCondition
        G hConnected hCut hNontrivial X hDeg hRank
  exact intCast_kInversionCount_eq_effectiveResidues_add_correction_of_bridgeless
    G hConnected hGenus u v (hOne u) (hOne v) hRankZero D k τ hTO hτ hAffine

/-- TeX label: `lem:invtau` (Lemma 4.10), at the paper's full bridgeless
genus-two scope. -/
theorem bridgeless_genusTwo_rigid_kGeneral_iff_nonRecurrent
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hCut : TwoEdgeCutCondition G) (hNontrivial : ∃ p q : G.V, p ≠ q)
    (hGenus : genus G = 2) (u v : G.V) (k : ℕ)
    (hSub : AllSubmodular (mark G u v))
    (hTO : IsTorsionOrder (mark G u v) k)
    (hRigid : ¬ linear_equiv G
      (one_chip u + one_chip v) (canonical_divisor G)) :
    KGeneralTransmission (mark G u v) k ↔ NonRecurrent (mark G u v) k :=
  bridgelessGenusTwoRigid_kGeneral_iff_nonRecurrent
    G hConnected hCut hNontrivial hGenus u v k hSub hTO hRigid

end Bananas
