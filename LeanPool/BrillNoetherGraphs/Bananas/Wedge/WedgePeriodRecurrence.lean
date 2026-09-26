/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Wedge.WedgeTorsionRestriction
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.NonrecurrenceWitness

/-!
# Unequal periods force recurrence on an opposite-side genus-one wedge

This is the period-comparison calculation in the distinct-loop branch of
Theorem 4.13.  The generic residue contradiction is kept in
`NonrecurrenceWitness`; this file supplies the wedge rank witnesses.
-/

@[expose] public section

namespace Bananas

open Utilities

private theorem rank_eq_zero_of_degree_one_genus_one
    (H : CFGraph) (hConnected : _root_.graphConnected H)
    (hGenus : genus H = 1) (E : CFDiv H) (hDegree : deg E = 1) :
    rank H E = 0 := by
  have hNeg : rank H (canonicalDivisor H - E) = -1 :=
    rank_neg_one_of_deg_neg H _ (by
      rw [deg.map_sub, degree_of_canonical_divisor, hGenus, hDegree]
      norm_num)
  have hRR := riemann_roch_for_graphs hConnected E
  rw [hNeg, hGenus, hDegree] at hRR
  omega

private theorem linearEquiv_marked_multiple
    (G : CFGraph) (u x : G.V) (a : ℕ)
    (h : linearEquiv G ((a : ℤ) • (oneChip u - oneChip x)) 0) :
    linearEquiv G ((a : ℤ) • oneChip u) ((a : ℤ) • oneChip x) := by
  unfold linearEquiv at h ⊢
  rw [smul_sub] at h
  convert h using 1
  abel

private theorem wedge_vertex_twist_eq_factor_sum
    (G H : CFGraph) (x : G.V) (y : H.V) (u : G.V) (v : H.V) (a : ℕ) :
    oneChip (G := vertexWedge G H x y) (wedgeRightVertex G H x y v) +
        (a : ℤ) •
          (oneChip (G := vertexWedge G H x y) (Sum.inl u) -
            oneChip (G := vertexWedge G H x y)
              (wedgeRightVertex G H x y v)) =
      wedgeAddDivisor G H x y ((a : ℤ) • oneChip u)
        ((1 - (a : ℤ)) • oneChip v) := by
  have h := wedgeAddDivisor_transmissionTwist G H x y
    (0 : CFDiv G) (oneChip v) u v (a : ℤ) (a : ℤ)
  have hE : (1 - (a : ℤ)) • oneChip v =
      oneChip v - (a : ℤ) • oneChip v := by
    rw [sub_smul, one_smul]
  rw [wedgeAddDivisor_one_chip_right G H x y v] at h
  have hL :
      oneChip (G := vertexWedge G H x y) (wedgeRightVertex G H x y v) +
          (a : ℤ) •
            (oneChip (G := vertexWedge G H x y) (Sum.inl u) -
              oneChip (G := vertexWedge G H x y)
                (wedgeRightVertex G H x y v)) =
        oneChip (G := vertexWedge G H x y) (wedgeRightVertex G H x y v) +
          (a : ℤ) • oneChip (G := vertexWedge G H x y) (Sum.inl u) -
          (a : ℤ) • oneChip (G := vertexWedge G H x y)
            (wedgeRightVertex G H x y v) := by
      rw [smul_sub]
      abel
  rw [hL, hE]
  simpa only [zero_add] using h

private theorem wedge_factor_transfer_eq
    (G H : CFGraph) (x : G.V) (y : H.V) (v : H.V) (a : ℕ) :
    wedgeAddDivisor G H x y ((a : ℤ) • oneChip x)
      ((1 - (a : ℤ)) • oneChip v) =
      wedgeAddDivisor G H x y 0
        ((a : ℤ) • oneChip y + (1 - (a : ℤ)) • oneChip v) := by
  let F : CFDiv H := (a : ℤ) • oneChip y + (1 - (a : ℤ)) • oneChip v
  have h := wedgeAddDivisor_chipShift_cancel G H x y
    (0 : CFDiv G) F (a : ℤ)
  have hLeft : chipShift G (0 : CFDiv G) x (a : ℤ) =
      (a : ℤ) • oneChip x := by
    unfold chipShift
    abel
  have hRight : chipShift H F y (-((a : ℤ))) =
      (1 - (a : ℤ)) • oneChip v := by
    funext z
    simp [chipShift, F]
  rw [hLeft, hRight] at h
  simpa only [F] using h

/-- A nontrivial torsion witness on the left factor which is strictly smaller
than the wedge period produces two distinct effective twists of the right
marked vertex.  Hence the wedge difference is recurrent. -/
theorem not_nonRecurrent_of_left_torsionWitness_lt_wedge_period
    (G H : CFGraph) (x : G.V) (y : H.V) (u : G.V) (v : H.V)
    (a k : ℕ) (hHConnected : _root_.graphConnected H)
    (hHGenus : genus H = 1)
    (ha : TorsionWitness (mark G u x) a)
    (haOne : 1 < a) (haK : a < k) :
    ¬ NonRecurrent
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) k := by
  let W := vertexWedge G H x y
  let w : W.V := wedgeRightVertex G H x y v
  let A : CFDiv G := (a : ℤ) • oneChip u
  let AX : CFDiv G := (a : ℤ) • oneChip x
  let E : CFDiv H := (1 - (a : ℤ)) • oneChip v
  let F : CFDiv H := (a : ℤ) • oneChip y + E
  have hAUx : linearEquiv G A AX :=
    linearEquiv_marked_multiple G u x a ha.2
  have hEquiv : linearEquiv W
      (wedgeAddDivisor G H x y A E)
      (wedgeAddDivisor G H x y AX E) :=
    linear_equiv_wedgeAddDivisor G H x y A AX E E hAUx (linearEquiv.refl H E)
  have hFdegree : deg F = 1 := by
    dsimp [F, E]
    rw [deg.map_add, map_zsmul, map_zsmul, deg_one_chip, deg_one_chip]
    ring
  have hFwin : winnable H F := by
    apply (rank_nonneg_iff_winnable H F).mp
    rw [rank_geq_iff H F 0,
      rank_eq_zero_of_degree_one_genus_one H hHConnected hHGenus F hFdegree]
  have hZeroWin : winnable G (0 : CFDiv G) :=
    winnable_of_effective G 0 (by intro z; simp)
  have hAXEwin : winnable W (wedgeAddDivisor G H x y AX E) := by
    rw [wedge_factor_transfer_eq G H x y v a]
    exact winnable_wedgeAddDivisor G H x y 0 F hZeroWin hFwin
  have hAEwin : winnable W (wedgeAddDivisor G H x y A E) :=
    winnable_equiv_winnable W _ _ hAXEwin hEquiv.symm
  have hOne : 0 ≤ rank W
      (oneChip (G := W) w + (1 : ℤ) •
        (oneChip (G := W) (Sum.inl u) - oneChip (G := W) w)) := by
    have hEq : oneChip (G := W) w + (1 : ℤ) •
        (oneChip (G := W) (Sum.inl u) - oneChip (G := W) w) =
        oneChip (G := W) (Sum.inl u) := by abel
    rw [hEq]
    exact (rank_geq_iff W _ 0).mp
      ((rank_nonneg_iff_winnable W _).mpr
        (winnable_of_effective W _ (eff_one_chip _)))
  have hA : 0 ≤ rank W
      (oneChip (G := W) w + (a : ℤ) •
        (oneChip (G := W) (Sum.inl u) - oneChip (G := W) w)) := by
    rw [wedge_vertex_twist_eq_factor_sum G H x y u v a]
    exact (rank_geq_iff W _ 0).mp
      ((rank_nonneg_iff_winnable W _).mpr hAEwin)
  apply not_nonRecurrent_of_rank_nonneg_one_and_period
    (M := mark W (Sum.inl u) w) w haOne haK
  · exact hOne
  · exact hA

/-- In the distinct-factor situation, once the left period is chosen no
larger than the right period, nonrecurrence forces the two exact periods to
coincide.  The hypotheses `1 < a` and genus one on the right are exactly the
nondegenerate cycle conditions used by the paper's period comparison. -/
theorem left_torsionOrder_eq_of_nonRecurrent_of_le
    (G H : CFGraph) (x : G.V) (y : H.V) (u : G.V) (v : H.V)
    (a b k : ℕ) (hHConnected : _root_.graphConnected H)
    (hHGenus : genus H = 1)
    (hA : IsTorsionOrder (mark G u x) a)
    (hB : IsTorsionOrder (mark H y v) b)
    (hW : IsTorsionOrder
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) k)
    (hNonrec : NonRecurrent
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) k)
    (haOne : 1 < a) (hAB : a ≤ b) :
    a = b := by
  have hLcm := isTorsionOrder_vertexWedge_opposite_lcm
    G H x y u v a b hA hB
  have hk : k = Nat.lcm a b :=
    IsTorsionOrder.eq_of_same_marked_graph hW hLcm
  by_contra hne
  have hab : a < b := lt_of_le_of_ne hAB hne
  have hLcmPos : 0 < Nat.lcm a b := Nat.lcm_pos hA.1.1 hB.1.1
  have hbLcm : b ≤ Nat.lcm a b :=
    Nat.le_of_dvd hLcmPos (Nat.dvd_lcm_right a b)
  have haK : a < k := by rw [hk]; omega
  exact (not_nonRecurrent_of_left_torsionWitness_lt_wedge_period
    G H x y u v a k hHConnected hHGenus hA.1 haOne haK) hNonrec

end Bananas
