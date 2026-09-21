/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaGenusTwoTwistIdentities

/-!
# Genus-two transmission-corner decomposition

This file reduces the finite complementary-rank sum in paper Lemma 4.10 to
the three degrees which can contribute in genus two.  It is deliberately
separate from the later comparison with *all* effective degree-one twists:
the latter comparison is where the endpoint and canonical correction terms
enter.
-/

namespace Bananas

open Utilities

/-- Rank plus one, the nonnegative multiplicity used throughout the paper's
inclusion--exclusion formula. -/
noncomputable def rankPlusOne (G : CFGraph) (X : CFDiv G) : ℤ :=
  rank G X + 1

/-- A fixed-degree twist with graph and marks as separate arguments. -/
def fixedDegreeTwist
    (G : CFGraph) (u v : G.V) (D : CFDiv G) (d b : ℤ) : CFDiv G :=
  D + (d - deg D + b) • one_chip u - b • one_chip v

theorem fixedDegreeTwist_sub_u
    (G : CFGraph) (u v : G.V) (D : CFDiv G) (d b : ℤ) :
    fixedDegreeTwist G u v D d b - one_chip u =
      fixedDegreeTwist G u v D (d - 1) b := by
  unfold fixedDegreeTwist
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

theorem fixedDegreeTwist_sub_v
    (G : CFGraph) (u v : G.V) (D : CFDiv G) (d b : ℤ) :
    fixedDegreeTwist G u v D d b - one_chip v =
      fixedDegreeTwist G u v D (d - 1) (b + 1) := by
  unfold fixedDegreeTwist
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

theorem fixedDegreeTwist_sub_uv
    (G : CFGraph) (u v : G.V) (D : CFDiv G) (d b : ℤ) :
    fixedDegreeTwist G u v D d b - one_chip u - one_chip v =
      fixedDegreeTwist G u v D (d - 2) (b + 1) := by
  rw [fixedDegreeTwist_sub_u, fixedDegreeTwist_sub_v]
  congr 1
  ring

theorem fixedDegreeTwist_one_eq_zero_add_u
    (G : CFGraph) (u v : G.V) (D : CFDiv G) (b : ℤ) :
    fixedDegreeTwist G u v D 1 b =
      fixedDegreeTwist G u v D 0 b + one_chip u := by
  unfold fixedDegreeTwist
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

theorem fixedDegreeTwist_one_eq_next_zero_add_v
    (G : CFGraph) (u v : G.V) (D : CFDiv G) (b : ℤ) :
    fixedDegreeTwist G u v D 1 b =
      fixedDegreeTwist G u v D 0 (b + 1) + one_chip v := by
  unfold fixedDegreeTwist
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

@[simp] theorem deg_fixedDegreeTwist
    (G : CFGraph) (u v : G.V) (D : CFDiv G) (d b : ℤ) :
    deg (fixedDegreeTwist G u v D d b) = d := by
  unfold fixedDegreeTwist
  rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul,
    deg_one_chip, deg_one_chip]
  ring

/-- The marked second difference with graph and marks kept as separate
arguments, avoiding dependent coercions through the `TwiceMarked` bundle. -/
noncomputable def markedRankDelta
    (G : CFGraph) (u v : G.V) (X : CFDiv G) : ℤ :=
  rank G X - rank G (X - one_chip u) - rank G (X - one_chip v) +
    rank G (X - one_chip u - one_chip v)

@[simp] theorem markedRankDelta_eq_rankDelta
    (G : CFGraph) (u v : G.V) (X : CFDiv G) :
    markedRankDelta G u v X = rankDelta (mark G u v) X := by
  rfl

/-- Rewriting `rankDelta` in the `rank + 1` notation makes its
inclusion--exclusion shape literal. -/
theorem rankDelta_eq_rankPlusOne_inclusionExclusion
    (M : TwiceMarked) (X : CFDiv M.graph) :
    rankDelta M X =
      rankPlusOne M.graph X -
        rankPlusOne M.graph (X - one_chip M.u) -
        rankPlusOne M.graph (X - one_chip M.v) +
        rankPlusOne M.graph (X - one_chip M.u - one_chip M.v) := by
  unfold rankDelta rankPlusOne
  ring

/-- The divisor at the graph point `(tau b,b)` of a transmission
permutation. -/
noncomputable def transmissionCorner
    (M : TwiceMarked) (D : CFDiv M.graph) (tau : ℤ → ℤ) (b : ℤ) :
    CFDiv M.graph :=
  D + (tau b) • one_chip M.u - b • one_chip M.v

@[simp] theorem deg_transmissionCorner
    (M : TwiceMarked) (D : CFDiv M.graph) (tau : ℤ → ℤ) (b : ℤ) :
    deg (transmissionCorner M D tau b) = deg D + tau b - b := by
  unfold transmissionCorner
  rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul,
    deg_one_chip, deg_one_chip]
  ring

/-- A transmission corner, indexed by its degree, is exactly the paper's
fixed-degree twist at the same second coordinate. -/
theorem transmissionCorner_eq_degreeTwistInt
    (M : TwiceMarked) (D : CFDiv M.graph) (tau : ℤ → ℤ) (b : ℤ) :
    transmissionCorner M D tau b =
      degreeTwistInt M D (deg D + tau b - b) b := by
  unfold transmissionCorner degreeTwistInt
  congr 1
  ring

/-- Conversely, if a transmission corner has prescribed degree `d`, it is
the degree-`d` twist with the same residue index. -/
theorem transmissionCorner_eq_degreeTwistInt_of_degree
    (M : TwiceMarked) (D : CFDiv M.graph) (tau : ℤ → ℤ) (b d : ℤ)
    (hDegree : deg (transmissionCorner M D tau b) = d) :
    transmissionCorner M D tau b = degreeTwistInt M D d b := by
  rw [transmissionCorner_eq_degreeTwistInt]
  rw [deg_transmissionCorner] at hDegree
  rw [hDegree]

/-- Every graph point selected by a transmission permutation has marked
second rank difference one. -/
theorem rankDelta_transmissionCorner_eq_one
    {M : TwiceMarked} {D : CFDiv M.graph} {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation M D tau) (b : ℤ) :
    rankDelta M (transmissionCorner M D tau b) = 1 := by
  have h := hTau.2 (tau b) b
  simpa [transmissionCorner] using h.symm

/-- The transmission equation evaluates the second rank difference of every
fixed-degree twist as the indicator that the selected corner has that
degree. -/
theorem rankDelta_degreeTwistInt_eq_degree_indicator
    {M : TwiceMarked} {D : CFDiv M.graph} {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation M D tau) (d b : ℤ) :
    rankDelta M (degreeTwistInt M D d b) =
      if deg (transmissionCorner M D tau b) = d then 1 else 0 := by
  have h := hTau.2 (d - deg D + b) b
  have hTwist :
      D + (d - deg D + b) • one_chip M.u - b • one_chip M.v =
        degreeTwistInt M D d b := by
    rfl
  rw [hTwist] at h
  rw [deg_transmissionCorner]
  by_cases hEq : tau b = d - deg D + b
  · have hDegree : deg D + tau b - b = d := by omega
    rw [if_pos hDegree]
    simpa [hEq] using h.symm
  · have hDegree : deg D + tau b - b ≠ d := by omega
    rw [if_neg hDegree]
    simpa [hEq] using h.symm

/-- A divisor with marked second rank difference one is winnable. -/
theorem rank_nonneg_of_rankDelta_eq_one
    (M : TwiceMarked) (X : CFDiv M.graph)
    (hDelta : rankDelta M X = 1) :
    0 ≤ rank M.graph X := by
  by_contra hNot
  have hX : rank M.graph X = -1 :=
    rank_neg_one_of_not_nonneg M.graph X hNot
  have hXuLe := rank_sub_one_chip_le_rank M.graph X M.u
  have hXvLe := rank_sub_one_chip_le_rank M.graph X M.v
  have hXuLower := rank_geq_neg_one M.graph (X - one_chip M.u)
  have hXvLower := rank_geq_neg_one M.graph (X - one_chip M.v)
  have hXu : rank M.graph (X - one_chip M.u) = -1 := by omega
  have hXv : rank M.graph (X - one_chip M.v) = -1 := by omega
  have hXuvLe := rank_sub_one_chip_le_rank M.graph
    (X - one_chip M.u) M.v
  have hXuvLower := rank_geq_neg_one M.graph
    (X - one_chip M.u - one_chip M.v)
  have hXuv :
      rank M.graph (X - one_chip M.u - one_chip M.v) = -1 := by
    omega
  unfold rankDelta at hDelta
  omega

/-- A winnable degree-zero divisor is principal. -/
theorem linearEquiv_zero_of_rank_nonneg_degree_zero'
    (G : CFGraph) (X : CFDiv G)
    (hRank : 0 ≤ rank G X) (hDeg : deg X = 0) :
    linear_equiv G X 0 := by
  obtain ⟨E, hEff, hXE⟩ := (rank_nonneg_iff_winnable G X).mp
    ((rank_geq_iff G X 0).mpr hRank)
  have hEDeg : deg E = 0 := by
    rw [← linear_equiv_preserves_deg G X E hXE, hDeg]
  have hE : E = 0 := eff_degree_zero E hEff hEDeg
  simpa [hE] using hXE

/-- At a selected genus-two theta corner of degree zero, the complementary
rank summand is two. -/
theorem complement_rank_add_one_eq_two_of_corner_degree_zero
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph)
    (hDelta : rankDelta (mark B.graph u v) X = 1)
    (hDeg : deg X = 0) :
    rank B.graph (canonical_divisor B.graph - X) + 1 = 2 := by
  have hRank := rank_nonneg_of_rankDelta_eq_one
    (mark B.graph u v) X hDelta
  have hXZero := linearEquiv_zero_of_rank_nonneg_degree_zero'
    B.graph X hRank hDeg
  have hComp : linear_equiv B.graph
      (canonical_divisor B.graph - X) (canonical_divisor B.graph) := by
    unfold linear_equiv at hXZero ⊢
    simpa [sub_eq_add_neg] using hXZero
  have hRankEq := rank_eq_of_linear_equiv B.graph hComp
  have hRR := riemann_roch_for_graphs
    (Bananas.graph_connected B)
    (canonical_divisor B.graph)
  have hZero :
      canonical_divisor B.graph - canonical_divisor B.graph = 0 := by abel
  rw [degree_of_canonical_divisor, B.genus_graph, hZero,
    zero_divisor_rank] at hRR
  rw [hRankEq]
  omega

/-- At a selected genus-two theta corner of degree one, both dual divisors
have rank zero, so the complementary-rank summand is one. -/
theorem complement_rank_add_one_eq_one_of_corner_degree_one
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph)
    (hDelta : rankDelta (mark B.graph u v) X = 1)
    (hDeg : deg X = 1) :
    rank B.graph (canonical_divisor B.graph - X) + 1 = 1 := by
  have hNonneg := rank_nonneg_of_rankDelta_eq_one
    (mark B.graph u v) X hDelta
  have hXRank : rank B.graph X = 0 :=
    rank_eq_zero_of_deg_one_rank_nonneg_banana_two B X hDeg hNonneg
  have hRR := riemann_roch_for_graphs
    (Bananas.graph_connected B) X
  rw [B.genus_graph, hDeg, hXRank] at hRR
  omega

/-- A degree-zero divisor has complementary-corner contribution one exactly
when it is principal. -/
theorem rank_add_one_eq_one_iff_linearEquiv_zero_of_degree_zero
    (G : CFGraph) (X : CFDiv G) (hDeg : deg X = 0) :
    rank G X + 1 = 1 ↔ linear_equiv G X 0 := by
  constructor
  · intro hRank
    apply linearEquiv_zero_of_rank_nonneg_degree_zero' G X (by omega) hDeg
  · intro hZero
    have hRankEq := rank_eq_of_linear_equiv G hZero
    calc
      rank G X + 1 = rank G (0 : CFDiv G) + 1 := by rw [hRankEq]
      _ = 1 := by rw [zero_divisor_rank]; norm_num

/-- A nonprincipal degree-zero divisor has `rank + 1 = 0`. -/
theorem rankPlusOne_eq_zero_of_degree_zero_not_principal
    (G : CFGraph) (X : CFDiv G) (hDeg : deg X = 0)
    (hNot : ¬ linear_equiv G X 0) :
    rankPlusOne G X = 0 := by
  have hLower := rank_geq_neg_one G X
  have hNotOne : rank G X + 1 ≠ 1 := fun h => hNot
    ((rank_add_one_eq_one_iff_linearEquiv_zero_of_degree_zero
      G X hDeg).mp h)
  have hUpper : rank G X ≤ 0 := by
    by_cases hR : 0 ≤ rank G X
    · have := rank_le_degree G X (rank G X) hR
        ((rank_geq_iff G X _).mpr le_rfl)
      omega
    · omega
  unfold rankPlusOne
  omega

/-- On a connected genus-two graph, a degree-zero twist contributes twice
its principality indicator against the canonical complement. -/
theorem degreeZero_slice_eq_two_mul_rankPlusOne
    (B : Banana 2) (X : CFDiv B.graph) (hDeg : deg X = 0) :
    rankPlusOne B.graph X *
        rankPlusOne B.graph (canonical_divisor B.graph - X) =
      2 * rankPlusOne B.graph X := by
  by_cases hZero : linear_equiv B.graph X 0
  · have hRX : rankPlusOne B.graph X = 1 := by
      unfold rankPlusOne
      exact (rank_add_one_eq_one_iff_linearEquiv_zero_of_degree_zero
        B.graph X hDeg).mpr hZero
    have hComp : linear_equiv B.graph
        (canonical_divisor B.graph - X) (canonical_divisor B.graph) := by
      unfold linear_equiv at hZero ⊢
      simpa [sub_eq_add_neg] using hZero
    have hRankEq := rank_eq_of_linear_equiv B.graph hComp
    have hRR := riemann_roch_for_graphs
      (Bananas.graph_connected B) (canonical_divisor B.graph)
    have hSub : canonical_divisor B.graph - canonical_divisor B.graph = 0 := by
      abel
    have hRK : rankPlusOne B.graph (canonical_divisor B.graph - X) = 2 := by
      unfold rankPlusOne
      rw [degree_of_canonical_divisor, B.genus_graph,
        hSub, zero_divisor_rank] at hRR
      rw [hRankEq]
      omega
    rw [hRX, hRK]
    norm_num
  · have hRX : rankPlusOne B.graph X = 0 := by
      have hLower := rank_geq_neg_one B.graph X
      have hNotOne : rank B.graph X + 1 ≠ 1 := fun h => hZero
        ((rank_add_one_eq_one_iff_linearEquiv_zero_of_degree_zero
          B.graph X hDeg).mp h)
      have hUpper : rank B.graph X ≤ 0 := by
        by_cases hR : 0 ≤ rank B.graph X
        · have := rank_le_degree B.graph X (rank B.graph X) hR
            ((rank_geq_iff B.graph X _).mpr le_rfl)
          omega
        · omega
      unfold rankPlusOne
      omega
    rw [hRX]
    ring

/-- Every canonical divisor with one chip removed has rank zero on a theta
graph. -/
theorem rank_canonical_sub_one_chip_zero_banana_two
    (B : Banana 2) (q : B.graph.V) :
    rank B.graph (canonical_divisor B.graph - one_chip q) = 0 := by
  have hRR := riemann_roch_for_graphs
    (Bananas.graph_connected B) (one_chip q)
  rw [deg_one_chip, B.genus_graph,
    rank_one_chip_zero_banana_two B q] at hRR
  omega

/-- Multiplication by a canonical complement with one marked chip removed
acts as the identity on the degree-zero principality indicator. -/
theorem degreeZero_mul_canonical_sub_add_one_chip
    (B : Banana 2) (X : CFDiv B.graph) (q : B.graph.V)
    (hDeg : deg X = 0) :
    rankPlusOne B.graph X *
        rankPlusOne B.graph
          (canonical_divisor B.graph - (X + one_chip q)) =
      rankPlusOne B.graph X := by
  by_cases hZero : linear_equiv B.graph X 0
  · have hRX : rankPlusOne B.graph X = 1 := by
      unfold rankPlusOne
      exact (rank_add_one_eq_one_iff_linearEquiv_zero_of_degree_zero
        B.graph X hDeg).mpr hZero
    have hComp : linear_equiv B.graph
        (canonical_divisor B.graph - (X + one_chip q))
        (canonical_divisor B.graph - one_chip q) := by
      unfold linear_equiv at hZero ⊢
      have hX := AddSubgroup.neg_mem (principal_divisors B.graph) hZero
      convert hX using 1 ; abel
    have hRankEq := rank_eq_of_linear_equiv B.graph hComp
    have hRComp : rankPlusOne B.graph
        (canonical_divisor B.graph - (X + one_chip q)) = 1 := by
      unfold rankPlusOne
      rw [hRankEq, rank_canonical_sub_one_chip_zero_banana_two]
      norm_num
    rw [hRX, hRComp]
    norm_num
  · have hRX : rankPlusOne B.graph X = 0 := by
      have hLower := rank_geq_neg_one B.graph X
      have hNotOne : rank B.graph X + 1 ≠ 1 := fun h => hZero
        ((rank_add_one_eq_one_iff_linearEquiv_zero_of_degree_zero
          B.graph X hDeg).mp h)
      have hUpper : rank B.graph X ≤ 0 := by
        by_cases hR : 0 ≤ rank B.graph X
        · have := rank_le_degree B.graph X (rank B.graph X) hR
            ((rank_geq_iff B.graph X _).mpr le_rfl)
          omega
        · omega
      unfold rankPlusOne
      omega
    rw [hRX]
    ring

/-- In genus two, a degree-one divisor and its canonical complement have
the same `rank + 1`, which is an idempotent (`0` or `1`). -/
theorem degreeOne_slice_eq_rankPlusOne
    (B : Banana 2) (X : CFDiv B.graph) (hDeg : deg X = 1) :
    rankPlusOne B.graph X *
        rankPlusOne B.graph (canonical_divisor B.graph - X) =
      rankPlusOne B.graph X := by
  have hRR := riemann_roch_for_graphs
    (Bananas.graph_connected B) X
  rw [B.genus_graph, hDeg] at hRR
  have hRanks : rank B.graph (canonical_divisor B.graph - X) =
      rank B.graph X := by omega
  by_cases hNonneg : 0 ≤ rank B.graph X
  · have hRankZero := rank_eq_zero_of_deg_one_rank_nonneg_banana_two
      B X hDeg hNonneg
    unfold rankPlusOne
    rw [hRanks, hRankZero]
    norm_num
  · have hRankNeg := rank_neg_one_of_not_nonneg B.graph X hNonneg
    unfold rankPlusOne
    rw [hRanks, hRankNeg]
    norm_num

/-- For a degree-two divisor, the first three terms of the marked
inclusion--exclusion expansion cancel after multiplication by its canonical
complement. -/
theorem degreeTwo_first_three_cancel
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph)
    (hDeg : deg X = 2) :
    (rankPlusOne B.graph X -
        rankPlusOne B.graph (X - one_chip u) -
        rankPlusOne B.graph (X - one_chip v)) *
      rankPlusOne B.graph (canonical_divisor B.graph - X) = 0 := by
  let Y : CFDiv B.graph := canonical_divisor B.graph - X
  have hYDeg : deg Y = 0 := by
    dsimp [Y]
    rw [deg.map_sub, degree_of_canonical_divisor, B.genus_graph, hDeg]
    norm_num
  by_cases hYZero : linear_equiv B.graph Y 0
  · have hXK : linear_equiv B.graph X (canonical_divisor B.graph) := by
      unfold linear_equiv at hYZero ⊢
      have hNeg := AddSubgroup.neg_mem (principal_divisors B.graph) hYZero
      dsimp [Y] at hNeg
      convert hNeg using 1 ; abel
    have hXu : linear_equiv B.graph (X - one_chip u)
        (canonical_divisor B.graph - one_chip u) := by
      unfold linear_equiv at hXK ⊢
      convert hXK using 1 ; abel
    have hXv : linear_equiv B.graph (X - one_chip v)
        (canonical_divisor B.graph - one_chip v) := by
      unfold linear_equiv at hXK ⊢
      convert hXK using 1 ; abel
    have hRankX := rank_eq_of_linear_equiv B.graph hXK
    have hRankXu := rank_eq_of_linear_equiv B.graph hXu
    have hRankXv := rank_eq_of_linear_equiv B.graph hXv
    have hRR := riemann_roch_for_graphs
      (Bananas.graph_connected B) (canonical_divisor B.graph)
    have hSub : canonical_divisor B.graph - canonical_divisor B.graph = 0 := by
      abel
    rw [degree_of_canonical_divisor, B.genus_graph,
      hSub, zero_divisor_rank] at hRR
    have hRankK : rank B.graph (canonical_divisor B.graph) = 1 := by omega
    have hRankYEq := rank_eq_of_linear_equiv B.graph hYZero
    have hRankY : rank B.graph
        (canonical_divisor B.graph - X) = 0 := by
      dsimp [Y] at hRankYEq
      rw [hRankYEq, zero_divisor_rank]
    unfold rankPlusOne
    rw [hRankX, hRankXu, hRankXv,
      rank_canonical_sub_one_chip_zero_banana_two,
      rank_canonical_sub_one_chip_zero_banana_two, hRankK, hRankY]
    norm_num
  · have hRY : rankPlusOne B.graph Y = 0 := by
      have hLower := rank_geq_neg_one B.graph Y
      have hNotOne : rank B.graph Y + 1 ≠ 1 := fun h => hYZero
        ((rank_add_one_eq_one_iff_linearEquiv_zero_of_degree_zero
          B.graph Y hYDeg).mp h)
      have hUpper : rank B.graph Y ≤ 0 := by
        by_cases hR : 0 ≤ rank B.graph Y
        · have := rank_le_degree B.graph Y (rank B.graph Y) hR
            ((rank_geq_iff B.graph Y _).mpr le_rfl)
          omega
        · omega
      unfold rankPlusOne
      omega
    change _ * rankPlusOne B.graph Y = 0
    rw [hRY]
    ring

/-- In degree zero, all three deleted divisors have negative degree, so the
marked second difference is simply `rank + 1`. -/
theorem markedRankDelta_eq_rankPlusOne_of_degree_zero
    (G : CFGraph) (u v : G.V) (X : CFDiv G) (hDeg : deg X = 0) :
    markedRankDelta G u v X = rankPlusOne G X := by
  have hU : deg (X - one_chip u) < 0 := by
    rw [deg.map_sub, deg_one_chip, hDeg]
    norm_num
  have hV : deg (X - one_chip v) < 0 := by
    rw [deg.map_sub, deg_one_chip, hDeg]
    norm_num
  have hUV : deg (X - one_chip u - one_chip v) < 0 := by
    rw [deg.map_sub, deg.map_sub, deg_one_chip, deg_one_chip, hDeg]
    norm_num
  unfold markedRankDelta rankPlusOne
  rw [rank_neg_one_of_deg_neg G _ hU,
    rank_neg_one_of_deg_neg G _ hV,
    rank_neg_one_of_deg_neg G _ hUV]
  ring

/-- The degree-zero slice in the finite three-degree formula. -/
theorem degreeZero_twistContribution_eq
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph) (b : ℤ) :
    markedRankDelta B.graph u v (fixedDegreeTwist B.graph u v D 0 b) *
        rankPlusOne B.graph
          (canonical_divisor B.graph - fixedDegreeTwist B.graph u v D 0 b) =
      2 * rankPlusOne B.graph (fixedDegreeTwist B.graph u v D 0 b) := by
  rw [markedRankDelta_eq_rankPlusOne_of_degree_zero B.graph u v _
    (deg_fixedDegreeTwist B.graph u v D 0 b)]
  exact degreeZero_slice_eq_two_mul_rankPlusOne B _
    (deg_fixedDegreeTwist B.graph u v D 0 b)

/-- The degree-one slice equals the effective degree-one indicator minus its
two adjacent degree-zero endpoint indicators. -/
theorem degreeOne_twistContribution_eq
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph) (b : ℤ) :
    markedRankDelta B.graph u v (fixedDegreeTwist B.graph u v D 1 b) *
        rankPlusOne B.graph
          (canonical_divisor B.graph - fixedDegreeTwist B.graph u v D 1 b) =
      rankPlusOne B.graph (fixedDegreeTwist B.graph u v D 1 b) -
        rankPlusOne B.graph (fixedDegreeTwist B.graph u v D 0 b) -
        rankPlusOne B.graph (fixedDegreeTwist B.graph u v D 0 (b + 1)) := by
  let X1 := fixedDegreeTwist B.graph u v D 1 b
  let X0 := fixedDegreeTwist B.graph u v D 0 b
  let X0next := fixedDegreeTwist B.graph u v D 0 (b + 1)
  let Rdual := rankPlusOne B.graph (canonical_divisor B.graph - X1)
  have hDelta : markedRankDelta B.graph u v X1 =
      rankPlusOne B.graph X1 - rankPlusOne B.graph X0 -
        rankPlusOne B.graph X0next := by
    have hU : X1 - one_chip u = X0 := by
      simpa [X1, X0] using
        fixedDegreeTwist_sub_u B.graph u v D 1 b
    have hV : X1 - one_chip v = X0next := by
      simpa [X1, X0next] using
        fixedDegreeTwist_sub_v B.graph u v D 1 b
    have hUVDeg : deg (X1 - one_chip u - one_chip v) < 0 := by
      rw [deg.map_sub, deg.map_sub, deg_one_chip, deg_one_chip]
      simp [X1]
    have hUVRank := rank_neg_one_of_deg_neg B.graph
      (X1 - one_chip u - one_chip v) hUVDeg
    have hUVRank' : rank B.graph (X0 - one_chip v) = -1 := by
      rw [← hU]
      exact hUVRank
    unfold markedRankDelta rankPlusOne
    rw [hU, hV, hUVRank']
    ring
  have hMain : rankPlusOne B.graph X1 * Rdual =
      rankPlusOne B.graph X1 := by
    simpa [Rdual] using degreeOne_slice_eq_rankPlusOne B X1
      (deg_fixedDegreeTwist B.graph u v D 1 b)
  have hLeft : rankPlusOne B.graph X0 * Rdual =
      rankPlusOne B.graph X0 := by
    have hX1 : X1 = X0 + one_chip u := by
      simpa [X1, X0] using
        fixedDegreeTwist_one_eq_zero_add_u B.graph u v D b
    simpa [Rdual, hX1] using degreeZero_mul_canonical_sub_add_one_chip
      B X0 u (by simp [X0])
  have hRight : rankPlusOne B.graph X0next * Rdual =
      rankPlusOne B.graph X0next := by
    have hX1 : X1 = X0next + one_chip v := by
      simpa [X1, X0next] using
        fixedDegreeTwist_one_eq_next_zero_add_v B.graph u v D b
    simpa [Rdual, hX1] using degreeZero_mul_canonical_sub_add_one_chip
      B X0next v (by simp [X0next])
  change markedRankDelta B.graph u v X1 * Rdual = _
  rw [hDelta]
  calc
    (rankPlusOne B.graph X1 - rankPlusOne B.graph X0 -
        rankPlusOne B.graph X0next) * Rdual =
      rankPlusOne B.graph X1 * Rdual -
        rankPlusOne B.graph X0 * Rdual -
        rankPlusOne B.graph X0next * Rdual := by ring
    _ = _ := by rw [hMain, hLeft, hRight]

/-- After the canonical cancellation, the degree-two slice is exactly the
paper's correction product. -/
theorem degreeTwo_twistContribution_eq
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph) (b : ℤ) :
    markedRankDelta B.graph u v (fixedDegreeTwist B.graph u v D 2 b) *
        rankPlusOne B.graph
          (canonical_divisor B.graph - fixedDegreeTwist B.graph u v D 2 b) =
      rankPlusOne B.graph (fixedDegreeTwist B.graph u v D 0 (b + 1)) *
        rankPlusOne B.graph
          (canonical_divisor B.graph - fixedDegreeTwist B.graph u v D 2 b) := by
  let X2 := fixedDegreeTwist B.graph u v D 2 b
  let X0next := fixedDegreeTwist B.graph u v D 0 (b + 1)
  let Rdual := rankPlusOne B.graph (canonical_divisor B.graph - X2)
  have hUV : X2 - one_chip u - one_chip v = X0next := by
    simpa [X2, X0next] using
      fixedDegreeTwist_sub_uv B.graph u v D 2 b
  have hCancel := degreeTwo_first_three_cancel B u v X2
    (deg_fixedDegreeTwist B.graph u v D 2 b)
  have hExpand : markedRankDelta B.graph u v X2 =
      rankPlusOne B.graph X2 -
        rankPlusOne B.graph (X2 - one_chip u) -
        rankPlusOne B.graph (X2 - one_chip v) +
        rankPlusOne B.graph X0next := by
    unfold markedRankDelta rankPlusOne
    rw [hUV]
    ring
  change markedRankDelta B.graph u v X2 * Rdual =
    rankPlusOne B.graph X0next * Rdual
  rw [hExpand]
  calc
    (rankPlusOne B.graph X2 -
          rankPlusOne B.graph (X2 - one_chip u) -
          rankPlusOne B.graph (X2 - one_chip v) +
          rankPlusOne B.graph X0next) * Rdual =
        (rankPlusOne B.graph X2 -
          rankPlusOne B.graph (X2 - one_chip u) -
          rankPlusOne B.graph (X2 - one_chip v)) * Rdual +
          rankPlusOne B.graph X0next * Rdual := by ring
    _ = rankPlusOne B.graph X0next * Rdual := by
      rw [hCancel]
      ring

/-- At a selected genus-two corner of degree two, the summand is the
indicator that the corner itself is canonical. -/
theorem complement_rank_add_one_eq_one_iff_corner_canonical
    (B : Banana 2) (X : CFDiv B.graph) (hDeg : deg X = 2) :
    rank B.graph (canonical_divisor B.graph - X) + 1 = 1 ↔
      linear_equiv B.graph X (canonical_divisor B.graph) := by
  have hCompDeg : deg (canonical_divisor B.graph - X) = 0 := by
    rw [deg.map_sub, degree_of_canonical_divisor, B.genus_graph, hDeg]
    norm_num
  rw [rank_add_one_eq_one_iff_linearEquiv_zero_of_degree_zero
    B.graph _ hCompDeg]
  constructor
  · intro hComp
    unfold linear_equiv at hComp ⊢
    simpa [sub_eq_add_neg] using
      AddSubgroup.neg_mem (principal_divisors B.graph) hComp
  · intro hCanon
    unfold linear_equiv at hCanon ⊢
    simpa [sub_eq_add_neg] using
      AddSubgroup.neg_mem (principal_divisors B.graph) hCanon

/-- Corners of degree at least three make no contribution to the
complementary-rank sum in genus two. -/
theorem complement_rank_add_one_eq_zero_of_three_le_degree
    (B : Banana 2) (X : CFDiv B.graph) (hDeg : 3 ≤ deg X) :
    rank B.graph (canonical_divisor B.graph - X) + 1 = 0 := by
  have hCompDeg : deg (canonical_divisor B.graph - X) < 0 := by
    rw [deg.map_sub, degree_of_canonical_divisor, B.genus_graph]
    omega
  rw [rank_neg_one_of_deg_neg B.graph _ hCompDeg]
  norm_num

/-- A selected corner cannot have negative degree. -/
theorem degree_nonneg_of_rankDelta_eq_one
    (M : TwiceMarked) (X : CFDiv M.graph)
    (hDelta : rankDelta M X = 1) :
    0 ≤ deg X := by
  have hRank := rank_nonneg_of_rankDelta_eq_one M X hDelta
  obtain ⟨E, hEff, hXE⟩ := (rank_nonneg_iff_winnable M.graph X).mp
    ((rank_geq_iff M.graph X 0).mpr hRank)
  have hDegEq := linear_equiv_preserves_deg M.graph X E hXE
  have hEDeg := deg_of_eff_nonneg E hEff
  omega

/-- The three possible nonzero contributions of a selected transmission
corner in genus two. -/
noncomputable def genusTwoCornerWeight
    (B : Banana 2) (X : CFDiv B.graph) : ℤ := by
  classical
  exact if deg X = 0 then 2
    else if deg X = 1 then 1
    else if deg X = 2 ∧
        linear_equiv B.graph X (canonical_divisor B.graph) then 1
    else 0

/-- The three degree slices which survive the genus-two specialization of
the paper's general inclusion--exclusion formula. -/
noncomputable def threeDegreeTwistContribution
    (G : CFGraph) (u v : G.V) (D : CFDiv G) (b : ℤ) : ℤ :=
  markedRankDelta G u v (fixedDegreeTwist G u v D 0 b) *
      rankPlusOne G
        (canonical_divisor G - fixedDegreeTwist G u v D 0 b) +
    markedRankDelta G u v (fixedDegreeTwist G u v D 1 b) *
      rankPlusOne G
        (canonical_divisor G - fixedDegreeTwist G u v D 1 b) +
    markedRankDelta G u v (fixedDegreeTwist G u v D 2 b) *
      rankPlusOne G
        (canonical_divisor G - fixedDegreeTwist G u v D 2 b)

/-- Pointwise telescoping form of the three degree slices. -/
theorem threeDegreeTwistContribution_eq_telescoping
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph) (b : ℤ) :
    threeDegreeTwistContribution B.graph u v D b =
      rankPlusOne B.graph (fixedDegreeTwist B.graph u v D 1 b) +
        rankPlusOne B.graph (fixedDegreeTwist B.graph u v D 0 b) -
        rankPlusOne B.graph (fixedDegreeTwist B.graph u v D 0 (b + 1)) +
        rankPlusOne B.graph (fixedDegreeTwist B.graph u v D 0 (b + 1)) *
          rankPlusOne B.graph
            (canonical_divisor B.graph - fixedDegreeTwist B.graph u v D 2 b) := by
  unfold threeDegreeTwistContribution
  rw [degreeZero_twistContribution_eq,
    degreeOne_twistContribution_eq,
    degreeTwo_twistContribution_eq]
  ring

/-- At each residue, the selected-corner weight is the sum of the three
degree slices. -/
theorem genusTwoCornerWeight_eq_threeDegreeTwistContribution
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph)
    (tau : ℤ → ℤ)
    (hTau : IsTransmissionPermutation (mark B.graph u v) D tau)
    (b : ℤ) :
    genusTwoCornerWeight B (transmissionCorner (mark B.graph u v) D tau b) =
      threeDegreeTwistContribution B.graph u v D b := by
  let C : CFDiv B.graph :=
    D + tau b • one_chip u - b • one_chip v
  have hDeltaC : rankDelta (mark B.graph u v) C = 1 := by
    have h := hTau.2 (tau b) b
    change (if tau b = tau b then (1 : ℤ) else 0) =
      rankDelta (mark B.graph u v) C at h
    simpa using h.symm
  have hNonneg : 0 ≤ deg C := degree_nonneg_of_rankDelta_eq_one
    (mark B.graph u v) C hDeltaC
  have hDegC : deg C = deg D + tau b - b := by
    unfold C
    rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul,
      deg_one_chip, deg_one_chip]
    ring
  have hDelta (d : ℤ) :
      markedRankDelta B.graph u v (fixedDegreeTwist B.graph u v D d b) =
        if deg C = d then 1 else 0 := by
    rw [markedRankDelta_eq_rankDelta]
    change rankDelta (mark B.graph u v)
        (D + (d - deg D + b) • one_chip u - b • one_chip v) = _
    have hs := hTau.2 (d - deg D + b) b
    change (if tau b = d - deg D + b then (1 : ℤ) else 0) =
      rankDelta (mark B.graph u v)
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
  change genusTwoCornerWeight B C = _
  by_cases h0 : deg C = 0
  · have hCDeg : deg D + tau b - b = 0 := hDegC.symm.trans h0
    have hC0 : C = fixedDegreeTwist B.graph u v D 0 b := by
      unfold C fixedDegreeTwist
      have hCoeff : tau b = 0 - deg D + b := by omega
      rw [hCoeff]
    have hComp := complement_rank_add_one_eq_two_of_corner_degree_zero
      B u v C hDeltaC h0
    rw [hDelta 0, hDelta 1, hDelta 2]
    simp only [h0, if_pos, OfNat.zero_ne_ofNat, if_false,
      zero_mul, add_zero, one_mul]
    rw [← hC0]
    simpa [genusTwoCornerWeight, h0] using hComp.symm
  by_cases h1 : deg C = 1
  · have hCDeg : deg D + tau b - b = 1 := hDegC.symm.trans h1
    have hC1 : C = fixedDegreeTwist B.graph u v D 1 b := by
      unfold C fixedDegreeTwist
      have hCoeff : tau b = 1 - deg D + b := by omega
      rw [hCoeff]
    have hComp := complement_rank_add_one_eq_one_of_corner_degree_one
      B u v C hDeltaC h1
    rw [hDelta 0, hDelta 1, hDelta 2]
    have h10 : deg C ≠ 0 := by omega
    have h12 : deg C ≠ 2 := by omega
    simp only [h1, if_pos,
      one_mul]
    rw [← hC1]
    simpa [genusTwoCornerWeight, h10, h1] using hComp.symm
  by_cases h2 : deg C = 2
  · have hCDeg : deg D + tau b - b = 2 := hDegC.symm.trans h2
    have hC2 : C = fixedDegreeTwist B.graph u v D 2 b := by
      unfold C fixedDegreeTwist
      have hCoeff : tau b = 2 - deg D + b := by omega
      rw [hCoeff]
    have h20 : deg C ≠ 0 := by omega
    have h21 : deg C ≠ 1 := by omega
    rw [hDelta 0, hDelta 1, hDelta 2]
    simp only [h2, if_pos,
      one_mul]
    rw [← hC2]
    by_cases hCanon : linear_equiv B.graph C (canonical_divisor B.graph)
    · have hComp :=
        (complement_rank_add_one_eq_one_iff_corner_canonical B C h2).mpr hCanon
      simpa [genusTwoCornerWeight, h20, h21, h2, hCanon] using hComp.symm
    · have hCompNe :=
        (complement_rank_add_one_eq_one_iff_corner_canonical B C h2).not.mpr hCanon
      have hLower := rank_geq_neg_one B.graph
        (canonical_divisor B.graph - C)
      have hCompDeg : deg (canonical_divisor B.graph - C) = 0 := by
        rw [deg.map_sub, degree_of_canonical_divisor, B.genus_graph, h2]
        norm_num
      have hUpper : rank B.graph (canonical_divisor B.graph - C) ≤ 0 := by
        by_cases hR : 0 ≤ rank B.graph (canonical_divisor B.graph - C)
        · have := rank_le_degree B.graph
            (canonical_divisor B.graph - C)
            (rank B.graph (canonical_divisor B.graph - C)) hR
            ((rank_geq_iff B.graph _ _).mpr le_rfl)
          omega
        · omega
      have hCompZero :
          rank B.graph (canonical_divisor B.graph - C) + 1 = 0 := by omega
      simpa [genusTwoCornerWeight, h20, h21, h2, hCanon] using hCompZero.symm
  · have h3 : 3 ≤ deg C := by omega
    have h30 : deg C ≠ 0 := by omega
    have h31 : deg C ≠ 1 := by omega
    have h32 : deg C ≠ 2 := h2
    rw [hDelta 0, hDelta 1, hDelta 2]
    unfold genusTwoCornerWeight
    simp only [h30, h31, h32, if_false, false_and,
      zero_mul, add_zero]

/-- Exact pointwise genus-two reduction of a selected corner's complementary
rank. -/
theorem complement_rank_add_one_eq_genusTwoCornerWeight
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph)
    (hDelta : rankDelta (mark B.graph u v) X = 1) :
    rank B.graph (canonical_divisor B.graph - X) + 1 =
      genusTwoCornerWeight B X := by
  have hDegNonneg : 0 ≤ deg X := degree_nonneg_of_rankDelta_eq_one
    (mark B.graph u v) X hDelta
  unfold genusTwoCornerWeight
  by_cases hDegZero : deg X = 0
  · simp only [hDegZero, if_pos]
    exact complement_rank_add_one_eq_two_of_corner_degree_zero
      B u v X hDelta hDegZero
  simp only [hDegZero, if_false]
  by_cases hDegOne : deg X = 1
  · simp only [hDegOne, if_pos]
    exact complement_rank_add_one_eq_one_of_corner_degree_one
      B u v X hDelta hDegOne
  simp only [hDegOne, if_false]
  by_cases hDegTwo : deg X = 2
  · by_cases hCanon :
        linear_equiv B.graph X (canonical_divisor B.graph)
    · simp only [hDegTwo, hCanon, and_self, if_pos]
      exact (complement_rank_add_one_eq_one_iff_corner_canonical
        B X hDegTwo).mpr hCanon
    · simp only [hDegTwo, hCanon, and_false, if_false]
      have hLower := rank_geq_neg_one B.graph
        (canonical_divisor B.graph - X)
      have hCompDeg : deg (canonical_divisor B.graph - X) = 0 := by
        rw [deg.map_sub, degree_of_canonical_divisor, B.genus_graph, hDegTwo]
        norm_num
      have hUpper : rank B.graph (canonical_divisor B.graph - X) ≤ 0 := by
        by_cases hNonneg : 0 ≤ rank B.graph
            (canonical_divisor B.graph - X)
        · have hBound := rank_le_degree B.graph
            (canonical_divisor B.graph - X)
            (rank B.graph (canonical_divisor B.graph - X)) hNonneg
            ((rank_geq_iff B.graph _ _).mpr le_rfl)
          omega
        · omega
      have hNe :
          rank B.graph (canonical_divisor B.graph - X) + 1 ≠ 1 :=
        fun hOne => hCanon
          ((complement_rank_add_one_eq_one_iff_corner_canonical
            B X hDegTwo).mp hOne)
      omega
  · have hThree : 3 ≤ deg X := by omega
    simp only [hDegTwo, false_and, if_false]
    exact complement_rank_add_one_eq_zero_of_three_le_degree B X hThree

/-- The finite inversion count is exactly the sum of the genus-two corner
weights.  This is the finite replacement for the paper's infinite
`S_D(E)` inclusion--exclusion notation. -/
theorem intCast_kInversionCount_eq_sum_genusTwoCornerWeight
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph)
    (k : ℕ) (tau : ℤ → ℤ)
    (hk : 0 < k)
    (hTau : IsTransmissionPermutation (mark B.graph u v) D tau)
    (hAffine : IsKAffine k tau) :
    (kInversionCount k tau : ℤ) =
      ∑ b : Fin k, genusTwoCornerWeight B
        (D + tau b • one_chip u - (b : ℤ) • one_chip v) := by
  rw [intCast_kInversionCount_eq_sum_complement_rank
    (mark B.graph u v) D (Bananas.graph_connected B)
    k tau hk hTau hAffine]
  apply Finset.sum_congr rfl
  intro b _
  have hCorner :
      canonical_divisor B.graph - D -
          tau b • one_chip u + (b : ℤ) • one_chip v =
        canonical_divisor B.graph -
          (D + tau b • one_chip u - (b : ℤ) • one_chip v) := by
    abel
  change rank B.graph
      (canonical_divisor B.graph - D -
          tau b • one_chip u + (b : ℤ) • one_chip v) + 1 = _
  rw [hCorner]
  have hDelta : rankDelta (mark B.graph u v)
      (D + tau b • one_chip u - (b : ℤ) • one_chip v) = 1 := by
    have h := hTau.2 (tau b) b
    change (if tau b = tau b then (1 : ℤ) else 0) =
      rankDelta (mark B.graph u v)
        (D + tau b • one_chip u - (b : ℤ) • one_chip v) at h
    simpa using h.symm
  exact complement_rank_add_one_eq_genusTwoCornerWeight B u v _ hDelta

/-- Finite three-degree form of the paper's general inclusion--exclusion
identity.  Unlike `S_D(E)`, every sum here is literally over `Fin k`. -/
theorem intCast_kInversionCount_eq_sum_threeDegreeTwistContribution
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph)
    (k : ℕ) (tau : ℤ → ℤ)
    (hk : 0 < k)
    (hTau : IsTransmissionPermutation (mark B.graph u v) D tau)
    (hAffine : IsKAffine k tau) :
    (kInversionCount k tau : ℤ) =
      ∑ b : Fin k, threeDegreeTwistContribution B.graph u v D b := by
  rw [intCast_kInversionCount_eq_sum_genusTwoCornerWeight
    B u v D k tau hk hTau hAffine]
  apply Finset.sum_congr rfl
  intro b _
  have hCorner :
      D + tau b • one_chip u - (b : ℤ) • one_chip v =
        transmissionCorner (mark B.graph u v) D tau b := by
    rfl
  rw [hCorner]
  exact genusTwoCornerWeight_eq_threeDegreeTwistContribution
    B u v D tau hTau b

/-! ## Finite-period bookkeeping -/

/-- Rank plus one of a fixed-degree twist is periodic with any torsion
witness.  This is the only input needed to close the boundary term in the
finite telescoping sum. -/
theorem rankPlusOne_fixedDegreeTwist_add_torsion
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph)
    (d b : ℤ) (k : ℕ)
    (hk : TorsionWitness (mark B.graph u v) k) :
    rankPlusOne B.graph (fixedDegreeTwist B.graph u v D d (b + k)) =
      rankPlusOne B.graph (fixedDegreeTwist B.graph u v D d b) := by
  have hEquiv := degreeTwistInt_add_torsion_linearEquiv hk D d b
  have hRank := rank_eq_of_linear_equiv B.graph hEquiv
  change rank B.graph
      (D + (d - deg D + (b + k)) • one_chip u - (b + k) • one_chip v) =
    rank B.graph
      (D + (d - deg D + b) • one_chip u - b • one_chip v) at hRank
  unfold rankPlusOne
  simpa [fixedDegreeTwist] using
    congrArg (fun r : ℤ ↦ r + 1) hRank

/-- The two degree-zero terms in consecutive slices cancel cyclically over
one torsion period. -/
theorem sum_rankPlusOne_fixedDegreeTwist_zero_sub_next_eq_zero
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph) (k : ℕ)
    (hk : TorsionWitness (mark B.graph u v) k) :
    ∑ b : Fin k,
        (rankPlusOne B.graph (fixedDegreeTwist B.graph u v D 0 b.val) -
          rankPlusOne B.graph
            (fixedDegreeTwist B.graph u v D 0 (b.val + 1))) = 0 := by
  let f : ℕ → ℤ := fun n ↦
    rankPlusOne B.graph (fixedDegreeTwist B.graph u v D 0 n)
  let g : ℕ → ℤ := fun n ↦ f n - f (n + 1)
  change ∑ b : Fin k, g b.val = 0
  rw [Fin.sum_univ_eq_sum_range]
  change ∑ n ∈ Finset.range k, (f n - f (n + 1)) = 0
  rw [Finset.sum_range_sub']
  have hPeriod := rankPlusOne_fixedDegreeTwist_add_torsion
    B u v D 0 0 k hk
  have hPeriod' : f k = f 0 := by
    simpa [f] using hPeriod
  rw [hPeriod']
  simp

/-- If the sum of the marked points is not canonical, the residual
degree-zero product in the degree-two slice vanishes pointwise. -/
theorem correctionProduct_eq_zero_of_not_mark_pair_canonical
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph) (b : ℤ)
    (hRigid : ¬ linear_equiv B.graph
      (one_chip u + one_chip v) (canonical_divisor B.graph)) :
    rankPlusOne B.graph
        (fixedDegreeTwist B.graph u v D 0 (b + 1)) *
      rankPlusOne B.graph
        (canonical_divisor B.graph -
          fixedDegreeTwist B.graph u v D 2 b) = 0 := by
  let A : CFDiv B.graph := fixedDegreeTwist B.graph u v D 0 (b + 1)
  let Y : CFDiv B.graph := canonical_divisor B.graph -
    fixedDegreeTwist B.graph u v D 2 b
  have hDegA : deg A = 0 := by simp [A]
  have hDegY : deg Y = 0 := by
    simp [Y, degree_of_canonical_divisor, B.genus_graph]
  by_cases hA : linear_equiv B.graph A 0
  · by_cases hY : linear_equiv B.graph Y 0
    · exfalso
      apply hRigid
      unfold linear_equiv at hA hY ⊢
      have hSum := AddSubgroup.add_mem
        (principal_divisors B.graph) hA hY
      have hNeg := AddSubgroup.neg_mem
        (principal_divisors B.graph) hSum
      convert hNeg using 1
      ext x
      simp [A, Y, fixedDegreeTwist]
      ring
    · have hZero := rankPlusOne_eq_zero_of_degree_zero_not_principal
        B.graph Y hDegY hY
      change rankPlusOne B.graph A * rankPlusOne B.graph Y = 0
      rw [hZero, mul_zero]
  · have hZero := rankPlusOne_eq_zero_of_degree_zero_not_principal
      B.graph A hDegA hA
    change rankPlusOne B.graph A * rankPlusOne B.graph Y = 0
    rw [hZero, zero_mul]

/-- The degree-one rank-plus-one sum is the cardinality of the effective
degree-one twists in the fundamental torsion period. -/
theorem sum_rankPlusOne_degreeOne_eq_effectiveResidues_ncard
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph) (k : ℕ) :
    ∑ b : Fin k,
        rankPlusOne B.graph
          (fixedDegreeTwist B.graph u v D 1 b.val) =
      ((effectiveDegreeOneTwistResidues
        (mark B.graph u v) D k).ncard : ℤ) := by
  classical
  let S : Set (Fin k) :=
    effectiveDegreeOneTwistResidues (mark B.graph u v) D k
  have hS : S.Finite := Set.toFinite S
  calc
    ∑ b : Fin k,
        rankPlusOne B.graph
          (fixedDegreeTwist B.graph u v D 1 b.val) =
        ∑ b : Fin k, if b ∈ S then (1 : ℤ) else 0 := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases hb : b ∈ S
          · have hNonneg : 0 ≤ rank B.graph
                (fixedDegreeTwist B.graph u v D 1 b.val) := by
              change 0 ≤ rank B.graph
                (D + (1 - deg D + b.val) • one_chip u -
                  b.val • one_chip v)
              change 0 ≤ rank B.graph
                (D + (1 - deg D + b.val) • one_chip u -
                  b.val • one_chip v) at hb
              exact hb
            have hRank := rank_eq_zero_of_deg_one_rank_nonneg_banana_two
              B (fixedDegreeTwist B.graph u v D 1 b.val)
              (deg_fixedDegreeTwist B.graph u v D 1 b.val) hNonneg
            simp [rankPlusOne, hb, hRank]
          · have hNotNonneg : ¬ 0 ≤ rank B.graph
                (fixedDegreeTwist B.graph u v D 1 b.val) := by
              intro hNonneg
              apply hb
              change 0 ≤ rank B.graph
                (D + (1 - deg D + b.val) • one_chip u -
                  b.val • one_chip v)
              simpa [fixedDegreeTwist] using hNonneg
            have hRank := rank_neg_one_of_not_nonneg B.graph
              (fixedDegreeTwist B.graph u v D 1 b.val) hNotNonneg
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
    _ = ((effectiveDegreeOneTwistResidues
        (mark B.graph u v) D k).ncard : ℤ) := by rfl

/-- Correction-free genus-two form of paper Lemma 4.10: when the marked
pair is not canonical, the inversion count is exactly the number of
effective degree-one twists in a torsion period. -/
theorem intCast_kInversionCount_eq_effectiveResidues_ncard_of_rigid
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph)
    (k : ℕ) (tau : ℤ → ℤ)
    (hk : TorsionWitness (mark B.graph u v) k)
    (hTau : IsTransmissionPermutation (mark B.graph u v) D tau)
    (hAffine : IsKAffine k tau)
    (hRigid : ¬ linear_equiv B.graph
      (one_chip u + one_chip v) (canonical_divisor B.graph)) :
    (kInversionCount k tau : ℤ) =
      ((effectiveDegreeOneTwistResidues
        (mark B.graph u v) D k).ncard : ℤ) := by
  rw [intCast_kInversionCount_eq_sum_threeDegreeTwistContribution
    B u v D k tau hk.1 hTau hAffine]
  calc
    ∑ b : Fin k, threeDegreeTwistContribution B.graph u v D b.val =
        ∑ b : Fin k,
          (rankPlusOne B.graph
              (fixedDegreeTwist B.graph u v D 1 b.val) +
            (rankPlusOne B.graph
                (fixedDegreeTwist B.graph u v D 0 b.val) -
              rankPlusOne B.graph
                (fixedDegreeTwist B.graph u v D 0 (b.val + 1)))) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [threeDegreeTwistContribution_eq_telescoping]
          rw [correctionProduct_eq_zero_of_not_mark_pair_canonical
            B u v D b.val hRigid]
          ring
    _ = (∑ b : Fin k,
          rankPlusOne B.graph
            (fixedDegreeTwist B.graph u v D 1 b.val)) +
        ∑ b : Fin k,
          (rankPlusOne B.graph
              (fixedDegreeTwist B.graph u v D 0 b.val) -
            rankPlusOne B.graph
              (fixedDegreeTwist B.graph u v D 0 (b.val + 1))) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ b : Fin k,
          rankPlusOne B.graph
            (fixedDegreeTwist B.graph u v D 1 b.val) := by
          rw [sum_rankPlusOne_fixedDegreeTwist_zero_sub_next_eq_zero
            B u v D k hk]
          simp
    _ = ((effectiveDegreeOneTwistResidues
        (mark B.graph u v) D k).ncard : ℤ) :=
      sum_rankPlusOne_degreeOne_eq_effectiveResidues_ncard B u v D k

/-- Natural-number version of the correction-free genus-two identity. -/
theorem kInversionCount_eq_effectiveResidues_ncard_of_rigid
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph)
    (k : ℕ) (tau : ℤ → ℤ)
    (hk : TorsionWitness (mark B.graph u v) k)
    (hTau : IsTransmissionPermutation (mark B.graph u v) D tau)
    (hAffine : IsKAffine k tau)
    (hRigid : ¬ linear_equiv B.graph
      (one_chip u + one_chip v) (canonical_divisor B.graph)) :
    kInversionCount k tau =
      (effectiveDegreeOneTwistResidues
        (mark B.graph u v) D k).ncard := by
  exact_mod_cast
    intCast_kInversionCount_eq_effectiveResidues_ncard_of_rigid
      B u v D k tau hk hTau hAffine hRigid

/-- Under nonrecurrence, the correction-free genus-two identity gives the
required inversion bound two. -/
theorem kInversionCount_le_two_of_nonRecurrent_of_rigid
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph)
    (k : ℕ) (tau : ℤ → ℤ)
    (hk : IsTorsionOrder (mark B.graph u v) k)
    (hTau : IsTransmissionPermutation (mark B.graph u v) D tau)
    (hAffine : IsKAffine k tau)
    (hNonrec : NonRecurrent (mark B.graph u v) k)
    (hRigid : ¬ linear_equiv B.graph
      (one_chip u + one_chip v) (canonical_divisor B.graph)) :
    kInversionCount k tau ≤ 2 := by
  rw [kInversionCount_eq_effectiveResidues_ncard_of_rigid
    B u v D k tau hk.1 hTau hAffine hRigid]
  exact effectiveDegreeOneTwistResidues_ncard_le_two_of_nonRecurrent
    B u v D k hk hNonrec

end Bananas
