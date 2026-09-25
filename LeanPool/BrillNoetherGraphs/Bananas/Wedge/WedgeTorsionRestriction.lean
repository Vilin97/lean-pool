/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedgeGenusOne
import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionWedge
import LeanPool.BrillNoetherGraphs.Bananas.Basics.Definitions
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.ExactTorsionAPI
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.EqualTorsionKGeneral
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TorsionOrderExact

/-!
# Restricting torsion from an opposite-side vertex wedge

The Jacobian of a vertex wedge is a product.  This file records the
torsion-witness direction needed in the genus-two wedge branch: a torsion
witness for an opposite-side pair restricts to witnesses for the two factor
pairs.  The proof uses the exact winnability convolution, avoiding a separate
Jacobian-product construction.
-/

namespace Bananas

open Utilities

private theorem wedge_marked_torsion_divisor_eq_factor_sum
    (G H : CFGraph) (x : G.V) (y : H.V) (u : G.V) (v : H.V) (k : ℕ) :
    (k : ℤ) •
        (oneChip (G := vertexWedge G H x y) (Sum.inl u) -
          oneChip (G := vertexWedge G H x y)
            (wedgeRightVertex G H x y v)) =
      wedgeAddDivisor G H x y
        ((k : ℤ) • (oneChip u - oneChip x))
        ((k : ℤ) • (oneChip y - oneChip v)) := by
  have hBase := wedgeAddDivisor_transmissionTwist G H x y
    (0 : CFDiv G) (0 : CFDiv H) u v (k : ℤ) (k : ℤ)
  have hLeft :
      chipShift G ((k : ℤ) • oneChip u) x (-((k : ℤ))) =
        (k : ℤ) • (oneChip u - oneChip x) := by
    unfold chipShift
    rw [smul_sub]
    ring
  have hRight :
      chipShift H (-((k : ℤ) • oneChip v)) y (k : ℤ) =
        (k : ℤ) • (oneChip y - oneChip v) := by
    unfold chipShift
    rw [smul_sub]
    abel
  have hZero : wedgeAddDivisor G H x y (0 : CFDiv G) (0 : CFDiv H) = 0 := by
    funext z
    cases z with
    | inl a =>
        rw [wedgeAddDivisor_left]
        change (0 : ℤ) + (if a = x then 0 else 0) = 0
        split <;> rfl
    | inr b =>
        rw [wedgeAddDivisor_right]
        rfl
  have hBase' :
      (k : ℤ) •
          (oneChip (G := vertexWedge G H x y) (Sum.inl u) -
            oneChip (G := vertexWedge G H x y)
              (wedgeRightVertex G H x y v)) =
        wedgeAddDivisor G H x y ((k : ℤ) • oneChip u)
          (-((k : ℤ) • oneChip v)) := by
    simpa only [hZero, smul_sub, zero_add, zero_sub] using hBase
  have hCancel := wedgeAddDivisor_chipShift_cancel G H x y
    ((k : ℤ) • oneChip u) (-((k : ℤ) • oneChip v)) (-((k : ℤ)))
  calc
    (k : ℤ) •
        (oneChip (G := vertexWedge G H x y) (Sum.inl u) -
          oneChip (G := vertexWedge G H x y)
            (wedgeRightVertex G H x y v)) =
        wedgeAddDivisor G H x y ((k : ℤ) • oneChip u)
          (-((k : ℤ) • oneChip v)) := hBase'
    _ = wedgeAddDivisor G H x y
        (chipShift G ((k : ℤ) • oneChip u) x (-((k : ℤ))))
        (chipShift H (-((k : ℤ) • oneChip v)) y (k : ℤ)) := by
          convert hCancel.symm using 1
          · simp
    _ = wedgeAddDivisor G H x y
        ((k : ℤ) • (oneChip u - oneChip x))
        ((k : ℤ) • (oneChip y - oneChip v)) := by rw [hLeft, hRight]

/-- A torsion witness for an opposite-side marked vertex wedge restricts to
torsion witnesses of the same period on the two factor markings. -/
theorem torsionWitness_factors_of_vertexWedge_opposite
    (G H : CFGraph) (x : G.V) (y : H.V) (u : G.V) (v : H.V) (k : ℕ)
    (hW : TorsionWitness
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) k) :
    TorsionWitness (mark G u x) k ∧ TorsionWitness (mark H y v) k := by
  let DG : CFDiv G := (k : ℤ) • (oneChip u - oneChip x)
  let EH : CFDiv H := (k : ℤ) • (oneChip y - oneChip v)
  have hWinnable : winnable (vertexWedge G H x y)
      (wedgeAddDivisor G H x y DG EH) := by
    refine ⟨0, ?_, ?_⟩
    · intro z
      simp
    · rw [← wedge_marked_torsion_divisor_eq_factor_sum G H x y u v k]
      exact hW.2
  obtain ⟨t, hGwin, hHwin⟩ :=
    (winnable_vertexWedge_iff_exists_chipShift G H x y DG EH).mp hWinnable
  have hDegG : deg DG = 0 := by
    dsimp [DG]
    rw [map_zsmul, deg.map_sub, deg_one_chip, deg_one_chip]
    ring
  have hDegH : deg EH = 0 := by
    dsimp [EH]
    rw [map_zsmul, deg.map_sub, deg_one_chip, deg_one_chip]
    ring
  have htNonneg : 0 ≤ t := by
    have h := deg_nonneg_of_winnable G (chipShift G DG x t) hGwin
    have hShift : deg (chipShift G DG x t) = t := by
      calc
        deg (chipShift G DG x t) = deg DG + deg (t • oneChip x) := by
          rw [chipShift, deg.map_add]
        _ = t := by rw [hDegG, map_zsmul, deg_one_chip]; ring
    rw [hShift] at h
    exact h
  have htNonpos : t ≤ 0 := by
    have h := deg_nonneg_of_winnable H (chipShift H EH y (-t)) hHwin
    have hShift : deg (chipShift H EH y (-t)) = -t := by
      calc
        deg (chipShift H EH y (-t)) = deg EH + deg ((-t) • oneChip y) := by
          rw [chipShift, deg.map_add]
        _ = -t := by rw [hDegH, map_zsmul, deg_one_chip]; ring
    rw [hShift] at h
    omega
  have ht : t = 0 := by omega
  constructor
  · refine ⟨hW.1, ?_⟩
    apply linear_equiv_zero_of_winnable_deg_zero G DG
    · simpa [ht, chipShift] using hGwin
    · exact hDegG
  · refine ⟨hW.1, ?_⟩
    apply linear_equiv_zero_of_winnable_deg_zero H EH
    · simpa [ht, chipShift] using hHwin
    · exact hDegH

/-- A positive torsion witness on an opposite-side wedge supplies exact
torsion orders for both factor markings. -/
theorem exists_factor_torsionOrders_of_vertexWedge_opposite
    (G H : CFGraph) (x : G.V) (y : H.V) (u : G.V) (v : H.V) (k : ℕ)
    (hW : TorsionWitness
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) k) :
    ∃ a b : ℕ,
      IsTorsionOrder (mark G u x) a ∧ IsTorsionOrder (mark H y v) b := by
  obtain ⟨hG, hH⟩ :=
    torsionWitness_factors_of_vertexWedge_opposite G H x y u v k hW
  obtain ⟨a, ha⟩ := exists_isTorsionOrder_of_torsionWitness hG
  obtain ⟨b, hb⟩ := exists_isTorsionOrder_of_torsionWitness hH
  exact ⟨a, b, ha, hb⟩

/-- Exact torsion orders are unique.  This small API lemma is useful when a
normal form provides two independent descriptions of the same marked
Jacobian class. -/
theorem IsTorsionOrder.eq_of_same_marked_graph
    {M : TwiceMarked} {a b : ℕ}
    (ha : IsTorsionOrder M a) (hb : IsTorsionOrder M b) :
    a = b :=
  Nat.dvd_antisymm
    (isTorsionOrder_dvd_of_torsionWitness ha hb.1)
    (isTorsionOrder_dvd_of_torsionWitness hb ha.1)

/-- The exact order of an opposite-side marked wedge is the least common
multiple of the exact orders on its two factors.  Together with
`torsionWitness_factors_of_vertexWedge_opposite`, this is the precise
Jacobian-product statement needed for the distinct-loop branch of Theorem
4.13. -/
theorem isTorsionOrder_vertexWedge_opposite_lcm
    (G H : CFGraph) (x : G.V) (y : H.V) (u : G.V) (v : H.V)
    (a b : ℕ)
    (hG : IsTorsionOrder (mark G u x) a)
    (hH : IsTorsionOrder (mark H y v) b) :
    IsTorsionOrder
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) (Nat.lcm a b) := by
  have hLcmPos : 0 < Nat.lcm a b := Nat.lcm_pos hG.1.1 hH.1.1
  refine ⟨?_, ?_⟩
  · exact torsionWitness_vertexWedge_opposite G H x y u v (Nat.lcm a b)
      (torsionWitness_of_dvd hG.1 (Nat.dvd_lcm_left a b) hLcmPos)
      (torsionWitness_of_dvd hH.1 (Nat.dvd_lcm_right a b) hLcmPos)
  · intro n hn
    obtain ⟨hGn, hHn⟩ :=
      torsionWitness_factors_of_vertexWedge_opposite G H x y u v n hn
    exact Nat.le_of_dvd hGn.1 <| Nat.lcm_dvd
      (isTorsionOrder_dvd_of_torsionWitness hG hGn)
      (isTorsionOrder_dvd_of_torsionWitness hH hHn)

/-- For a general-transmission opposite-side wedge, the asserted period is
the least common multiple of the exact factor orders.  Unlike the usual
cycle presentation argument, this extracts the factor orders directly from
the wedge torsion witness. -/
theorem exists_factor_torsionOrders_lcm_eq_of_vertexWedge_opposite_kGeneral
    (G H : CFGraph) (x : G.V) (y : H.V) (u : G.V) (v : H.V) (k : ℕ)
    (hConn : _root_.graphConnected (vertexWedge G H x y))
    (hPos : 0 < genus (vertexWedge G H x y))
    (huv : (Sum.inl u : (vertexWedge G H x y).V) ≠
      wedgeRightVertex G H x y v)
    (hK : KGeneralTransmission
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) k) :
    ∃ a b : ℕ,
      IsTorsionOrder (mark G u x) a ∧
      IsTorsionOrder (mark H y v) b ∧ k = Nat.lcm a b := by
  obtain ⟨a, b, hA, hB⟩ :=
    exists_factor_torsionOrders_of_vertexWedge_opposite G H x y u v k hK.1
  have hW : IsTorsionOrder
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) k :=
    KGeneralTransmission.isTorsionOrder hK huv hConn (by
      change 0 < genus (vertexWedge G H x y)
      exact hPos)
  have hLcm := isTorsionOrder_vertexWedge_opposite_lcm
    G H x y u v a b hA hB
  exact ⟨a, b, hA, hB, hW.eq_of_same_marked_graph hLcm⟩

end Bananas
