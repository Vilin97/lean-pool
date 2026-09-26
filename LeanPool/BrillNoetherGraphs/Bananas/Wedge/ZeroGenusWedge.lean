/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Basics.Definitions
public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.MarkedRankProfile
public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionSpecial

/-!
# Removing genus-zero factors from a vertex wedge

A connected genus-zero factor has the rank profile of a point: the rank of a
divisor is its degree when that degree is nonnegative, and is `-1` otherwise.
Substitution in the exact vertex-wedge rank formula therefore absorbs the
whole factor into the coefficient of the gluing vertex on the other factor.

This is the zero-genus reduction needed at the endpoints of the balancing
argument in Corollary 6.16(2) of the banana-graph paper.
-/

@[expose] public section

namespace Bananas

open Utilities

universe u v

/-- On a connected genus-zero graph, every divisor of nonnegative degree has
rank equal to its degree. -/
theorem rank_eq_degree_of_connected_genus_zero
    (H : CFGraph.{v}) (hConnected : graphConnected H)
    (hGenus : genus H = 0) (E : CFDiv H) (hDegree : 0 ≤ deg E) :
    rank H E = deg E := by
  have hLower : deg E ≤ rank H E := by
    have hRR := rank_ge_degree_sub_genus hConnected E
    rw [hGenus] at hRR
    simpa using hRR
  have hRankNonnegative : 0 ≤ rank H E := le_trans hDegree hLower
  have hUpper : rank H E ≤ deg E := by
    apply rank_le_degree H E (rank H E) hRankNonnegative
    exact (rank_geq_iff H E (rank H E)).mpr le_rfl
  exact le_antisymm hUpper hLower

/-- Complete rank formula on a connected genus-zero graph. -/
theorem rank_eq_degree_or_neg_one_of_connected_genus_zero
    (H : CFGraph.{v}) (hConnected : graphConnected H)
    (hGenus : genus H = 0) (E : CFDiv H) :
    rank H E = if deg E < 0 then -1 else deg E := by
  by_cases hDegree : deg E < 0
  · rw [ite_eq_left hDegree]
    exact rank_neg_one_of_deg_neg H E hDegree
  · rw [ite_eq_right hDegree]
    exact rank_eq_degree_of_connected_genus_zero H hConnected hGenus E
      (le_of_not_gt hDegree)

/-- Adding `t` marked chips, for natural `t`, cannot increase rank by more
than `t`.  This is the iterated form of the one-chip Lipschitz bound. -/
private theorem rank_shift_le_add_nat
    (G : CFGraph.{u}) (D : CFDiv G) (x : G.V) (n : ℤ) (t : ℕ) :
    rank G (D + (n + (t : ℤ)) • oneChip x) ≤
      rank G (D + n • oneChip x) + (t : ℤ) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hStep :=
        (rank_add_zsmul_one_chip_step G D x (n + (t : ℤ))).2
      have hRewrite : n + ((t + 1 : ℕ) : ℤ) =
          (n + (t : ℤ)) + 1 := by omega
      rw [hRewrite]
      omega

/-- Adding a natural number of marked chips cannot decrease rank. -/
private theorem rank_shift_mono_nat
    (G : CFGraph.{u}) (D : CFDiv G) (x : G.V) (n : ℤ) (t : ℕ) :
    rank G (D + n • oneChip x) ≤
      rank G (D + (n + (t : ℤ)) • oneChip x) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hStep :=
        (rank_add_zsmul_one_chip_step G D x (n + (t : ℤ))).1
      have hRewrite : n + ((t + 1 : ℕ) : ℤ) =
          (n + (t : ℤ)) + 1 := by omega
      rw [hRewrite]
      exact le_trans ih hStep

/-- A connected genus-zero factor in a vertex wedge can be absorbed into the
gluing coefficient on the other factor.  This is an exact rank identity for
arbitrary divisors, not merely a Brill--Noether implication. -/
theorem rank_vertexWedge_genus_zero_right
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (hConnected : graphConnected H) (hGenus : genus H = 0)
    (D : CFDiv G) (E : CFDiv H) :
    rank (vertexWedge G H x y) (wedgeAddDivisor G H x y D E) =
      rank G (D + deg E • oneChip x) := by
  let r : ℤ := rank G (D + deg E • oneChip x)
  apply (vertexWedge_rank_eq_iff_profile_inequalities_and_attained
    G H x y D E r).2
  constructor
  · intro ell
    have hLeftDivisor :
        D - (ell + 1) • oneChip x =
          D + (-(ell + 1)) • oneChip x := by
      funext z
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hLeftDivisor]
    rw [rank_eq_degree_or_neg_one_of_connected_genus_zero
      H hConnected hGenus]
    rw [deg_add_zsmul_one_chip]
    by_cases hNegative : deg E + ell < 0
    · rw [ite_eq_left hNegative]
      have hGap : 0 ≤ -(ell + 1) - deg E := by omega
      let t : ℕ := (-(ell + 1) - deg E).toNat
      have ht : (t : ℤ) = -(ell + 1) - deg E := by
        exact Int.toNat_of_nonneg hGap
      have hMono := rank_shift_mono_nat G D x (deg E) t
      have hShift : deg E + (t : ℤ) = -(ell + 1) := by omega
      rw [hShift] at hMono
      dsimp [r]
      simpa using hMono
    · rw [ite_eq_right hNegative]
      have hGap : 0 ≤ deg E + ell + 1 := by omega
      let t : ℕ := (deg E + ell + 1).toNat
      have ht : (t : ℤ) = deg E + ell + 1 := by
        exact Int.toNat_of_nonneg hGap
      have hBound := rank_shift_le_add_nat G D x (-(ell + 1)) t
      have hShift : -(ell + 1) + (t : ℤ) = deg E := by omega
      rw [hShift] at hBound
      dsimp [r]
      omega
  · refine ⟨-deg E - 1, ?_⟩
    rw [rank_eq_degree_or_neg_one_of_connected_genus_zero
      H hConnected hGenus]
    rw [deg_add_zsmul_one_chip]
    have hDegree : deg E + (-deg E - 1) < 0 := by omega
    rw [ite_eq_left hDegree]
    dsimp [r]
    have hLeftDivisor :
        D - (-deg E - 1 + 1) • oneChip x =
          D + deg E • oneChip x := by
      funext z
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hLeftDivisor]
    omega

/-- Wedging on a connected genus-zero right factor preserves
Brill--Noether generality. -/
theorem brillNoetherGeneral_vertexWedge_genus_zero_right
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (hConnected : graphConnected H) (hGenus : genus H = 0)
    (hGeneral : BrillNoetherGeneral G) :
    BrillNoetherGeneral (vertexWedge G H x y) := by
  intro r d hRankNonnegative hExists
  obtain ⟨Q, hQDegree, hQRank⟩ := hExists
  let D := wedgeRestrictLeftDivisor G H x y Q
  let E := wedgeRestrictRightDivisor G H x y Q
  let D' : CFDiv G := D + deg E • oneChip x
  have hSplit : wedgeAddDivisor G H x y D E = Q := by
    exact wedgeAddDivisor_restrict G H x y Q
  have hDegreeSplit : deg D + deg E = deg Q := by
    exact deg_wedgeRestrictions G H x y Q
  have hD'Degree : deg D' = d := by
    dsimp [D']
    rw [deg_add_zsmul_one_chip]
    omega
  have hD'Rank : rank G D' ≥ r := by
    rw [← rank_vertexWedge_genus_zero_right
      G H x y hConnected hGenus D E]
    rw [hSplit]
    exact hQRank
  have hBase := hGeneral r d hRankNonnegative ⟨D', hD'Degree, hD'Rank⟩
  simpa [bnNumber, rectangleWidth, hGenus] using hBase

end Bananas
