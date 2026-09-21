/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeDivisors
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankOne

/-!
# Rank one across a bridge

Rank-one divisors on two factors combine to a rank-one divisor on their bridge
sum after removing one chip at a bridge endpoint. The loss of one degree is the
familiar bridge gluing correction.
-/

namespace MarkedGraphs

open Utilities

universe u v

/-- Zero extension from the left commutes with subtracting one chip. -/
theorem liftLeftDivisor_sub_one_chip
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (a : G.V) :
    liftLeftDivisor G H x y (D - one_chip a) =
      liftLeftDivisor G H x y D - one_chip (Sum.inl a) := by
  funext z
  cases z with
  | inl p =>
      change D p - one_chip a p =
        D p - (if (Sum.inl p : Sum G.V H.V) = Sum.inl a then 1 else 0)
      simp [one_chip]
  | inr q =>
      unfold liftLeftDivisor bridgeGraph
      simp [Pi.sub_apply, one_chip]

/-- Zero extension from the right commutes with subtracting one chip. -/
theorem liftRightDivisor_sub_one_chip
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv H) (b : H.V) :
    liftRightDivisor G H x y (D - one_chip b) =
      liftRightDivisor G H x y D - one_chip (Sum.inr b) := by
  funext z
  cases z with
  | inl p =>
      unfold liftRightDivisor bridgeGraph
      simp [Pi.sub_apply, one_chip]
  | inr q =>
      change D q - one_chip b q =
        D q - (if (Sum.inr q : Sum G.V H.V) = Sum.inr b then 1 else 0)
      simp [one_chip]

/-- Winnable divisors on the two factors have a winnable sum after zero
extension to the bridge graph. -/
theorem winnable_add_liftDivisors
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    {D : CFDiv G} {E : CFDiv H}
    (hD : winnable G D) (hE : winnable H E) :
    winnable (bridgeGraph G H x y)
      (liftLeftDivisor G H x y D + liftRightDivisor G H x y E) :=
  winnable_add_winnable (bridgeGraph G H x y)
    (liftLeftDivisor G H x y D) (liftRightDivisor G H x y E)
    (winnable_liftLeftDivisor G H x y hD)
    (winnable_liftRightDivisor G H x y hE)

/-- Subtracting the right bridge-end chip is linearly equivalent to
subtracting the left bridge-end chip. -/
theorem linear_equiv_sub_bridge_endpoints
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (P : CFDiv (bridgeGraph G H x y)) :
    linear_equiv (bridgeGraph G H x y)
      (P - one_chip (Sum.inr y)) (P - one_chip (Sum.inl x)) := by
  unfold linear_equiv
  apply (principal_iff_eq_prin (bridgeGraph G H x y)
    ((P - one_chip (G := bridgeGraph G H x y) (Sum.inl x)) -
      (P - one_chip (G := bridgeGraph G H x y) (Sum.inr y)))).mpr
  refine ⟨leftSideIndicator G H x y, ?_⟩
  rw [prin_leftSideIndicator]
  abel

/-- The divisor obtained by gluing `D` and `E` across the bridge and removing
one chip at the left bridge endpoint. -/
def bridgeRankOneDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) : CFDiv (bridgeGraph G H x y) :=
  liftLeftDivisor G H x y D + liftRightDivisor G H x y E -
    one_chip (Sum.inl x)

/-- Rank-one divisors on two factors glue to a rank-one divisor of degree one
less than the sum of their degrees. -/
theorem rank_bridgeGraph_ge_one
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H)
    (hD : rank G D ≥ 1) (hE : rank H E ≥ 1) :
    rank (bridgeGraph G H x y)
      (liftLeftDivisor G H x y D + liftRightDivisor G H x y E -
        one_chip (Sum.inl x)) ≥ 1 := by
  rw [rank_ge_one_iff_winnable_sub_one_chip]
  intro z
  cases z with
  | inl a =>
      have hDa : winnable G (D - one_chip a) :=
        (rank_ge_one_iff_winnable_sub_one_chip G D).mp hD a
      have hEy : winnable H (E - one_chip y) :=
        (rank_ge_one_iff_winnable_sub_one_chip H E).mp hE y
      have hBase : winnable (bridgeGraph G H x y)
          (liftLeftDivisor G H x y (D - one_chip a) +
            liftRightDivisor G H x y (E - one_chip y)) :=
        winnable_add_liftDivisors G H x y hDa hEy
      let P : CFDiv (bridgeGraph G H x y) :=
        liftLeftDivisor G H x y (D - one_chip a) +
          liftRightDivisor G H x y E
      have hRight : winnable (bridgeGraph G H x y)
          (P - one_chip (Sum.inr y)) := by
        have hEq :
            P - one_chip (Sum.inr y) =
              liftLeftDivisor G H x y (D - one_chip a) +
                liftRightDivisor G H x y (E - one_chip y) := by
          dsimp [P]
          rw [liftRightDivisor_sub_one_chip]
          abel
        rw [hEq]
        exact hBase
      have hLeft : winnable (bridgeGraph G H x y)
          (P - one_chip (Sum.inl x)) :=
        winnable_equiv_winnable (bridgeGraph G H x y)
          (P - one_chip (Sum.inr y)) (P - one_chip (Sum.inl x))
          hRight (linear_equiv_sub_bridge_endpoints G H x y P)
      have hEq :
          liftLeftDivisor G H x y D + liftRightDivisor G H x y E -
                one_chip (Sum.inl x) - one_chip (Sum.inl a) =
            P - one_chip (Sum.inl x) := by
        dsimp [P]
        rw [liftLeftDivisor_sub_one_chip]
        abel
      rw [hEq]
      exact hLeft
  | inr b =>
      have hDx : winnable G (D - one_chip x) :=
        (rank_ge_one_iff_winnable_sub_one_chip G D).mp hD x
      have hEb : winnable H (E - one_chip b) :=
        (rank_ge_one_iff_winnable_sub_one_chip H E).mp hE b
      have hBase : winnable (bridgeGraph G H x y)
          (liftLeftDivisor G H x y (D - one_chip x) +
            liftRightDivisor G H x y (E - one_chip b)) :=
        winnable_add_liftDivisors G H x y hDx hEb
      have hEq :
          liftLeftDivisor G H x y D + liftRightDivisor G H x y E -
                one_chip (Sum.inl x) - one_chip (Sum.inr b) =
            liftLeftDivisor G H x y (D - one_chip x) +
              liftRightDivisor G H x y (E - one_chip b) := by
        rw [liftLeftDivisor_sub_one_chip,
          liftRightDivisor_sub_one_chip]
        abel
      rw [hEq]
      exact hBase

/-- The named bridge divisor has rank at least one whenever both factor
divisors do. -/
theorem rank_bridgeRankOneDivisor_ge_one
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H)
    (hD : rank G D ≥ 1) (hE : rank H E ≥ 1) :
    rank (bridgeGraph G H x y) (bridgeRankOneDivisor G H x y D E) ≥ 1 := by
  exact rank_bridgeGraph_ge_one G H x y D E hD hE
/-- The glued rank-one candidate has the expected corrected degree. -/
theorem deg_bridgeRankOneDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) :
    deg (bridgeRankOneDivisor G H x y D E) = deg D + deg E - 1 := by
  unfold bridgeRankOneDivisor
  rw [deg.map_sub, deg.map_add, deg_liftLeftDivisor,
    deg_liftRightDivisor, deg_one_chip]

/-- Rank-one Brill--Noether witnesses glue across a bridge with the expected
loss of one degree. -/
theorem BNExists_bridgeGraph_rank_one
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    {d₁ d₂ : ℤ} (hG : BNExists G 1 d₁) (hH : BNExists H 1 d₂) :
    BNExists (bridgeGraph G H x y) 1 (d₁ + d₂ - 1) := by
  obtain ⟨D, hDDegree, hDRank⟩ := hG
  obtain ⟨E, hEDegree, hERank⟩ := hH
  refine ⟨bridgeRankOneDivisor G H x y D E, ?_, ?_⟩
  · rw [deg_bridgeRankOneDivisor, hDDegree, hEDegree]
  · exact rank_bridgeRankOneDivisor_ge_one G H x y D E hDRank hERank

end MarkedGraphs
