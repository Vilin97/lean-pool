/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionRR

/-!
# Canonical duality for transmission witnesses

Riemann--Roch exchanges the two marks and inverts the ASP permutation.  With
the row convention used by `SatisfiesTransmission`, the literal canonical
complement is off by one in each marked coordinate.  The normalized complement
is therefore

`K - D + u + v`.

It has the degree prescribed by `τ⁻¹`, and its rows are exactly those required
for `τ⁻¹` at the swapped marks.
-/

namespace Utilities

/-- The marked normalization of the canonical complement appropriate to
transmission duality. -/
def transmissionDualDivisor {G : CFGraph} (u v : G.V) (D : CFDiv G) : CFDiv G :=
  canonical_divisor G - D + one_chip u + one_chip v

/-- The normalized canonical complement has the degree prescribed by the
inverse ASP permutation. -/
theorem degree_transmissionDualDivisor
    {G : CFGraph} {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (h : SatisfiesTransmission G u v τ D) :
    deg (transmissionDualDivisor u v D) = (genus G : ℤ) + (τ⁻¹).χ := by
  unfold transmissionDualDivisor
  rw [deg.map_add, deg.map_add, deg.map_sub,
    degree_of_canonical_divisor, h.1, deg_one_chip, deg_one_chip,
    AspPerm.chi_dual]
  ring

/-- The complementary marked twist is the canonical complement of the
original twist at the transposed, shifted lattice point. -/
theorem transmissionDualDivisor_twist
    {G : CFGraph} (u v : G.V) (D : CFDiv G) (a b : ℤ) :
    transmissionDualDivisor u v D + a • one_chip v - b • one_chip u =
      canonical_divisor G -
        (D + (b - 1) • one_chip u - (a + 1) • one_chip v) := by
  unfold transmissionDualDivisor
  rw [sub_zsmul, add_zsmul]
  simp only [one_zsmul]
  abel

/-- The dual row bound supplied by Riemann--Roch. -/
theorem transmissionDualDivisor_rank_ge
    {G : CFGraph} (hconn : graph_connected G)
    {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (h : SatisfiesTransmission G u v τ D) (a b : ℤ) :
    rank G (transmissionDualDivisor u v D + a • one_chip v - b • one_chip u) ≥
      (τ⁻¹).s (a + 1) b - 1 := by
  have hRow := rank_twist_of_satisfiesTransmission h (b - 1) (a + 1)
  have hRR := riemann_roch_for_graphs hconn
    (D + (b - 1) • one_chip u - (a + 1) • one_chip v)
  rw [degree_twist_of_satisfiesTransmission h (b - 1) (a + 1)] at hRR
  rw [← transmissionDualDivisor_twist u v D a b] at hRR
  have hRow' :
      rank G (D + (b - 1) • one_chip u - (a + 1) • one_chip v) ≥
        τ.s b (a + 1) - 1 := by
    have hIndex : b - 1 + 1 = b := by omega
    rw [hIndex] at hRow
    exact hRow
  have hRR' :
      rank G (D + (b - 1) • one_chip u - (a + 1) • one_chip v) -
          rank G (transmissionDualDivisor u v D + a • one_chip v -
            b • one_chip u) = τ.χ + b - a - 1 := by
    linarith [hRR]
  have hSlip := τ.duality b (a + 1)
  linarith [hRow', hRR', hSlip]

/-- A transmission witness canonically yields an inverse-permutation witness
at the swapped marks. -/
theorem satisfiesTransmission_dual
    {G : CFGraph} (hconn : graph_connected G)
    {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (h : SatisfiesTransmission G u v τ D) :
    SatisfiesTransmission G v u τ⁻¹ (transmissionDualDivisor u v D) := by
  refine ⟨degree_transmissionDualDivisor h, ?_⟩
  intro a b
  unfold TransmissionInequality
  have hStrong := transmissionDualDivisor_rank_ge hconn h a b
  linarith

/-- Transmission existence is preserved by Riemann--Roch duality, inversion,
and swapping the marked points. -/
theorem transmissionExists_dual
    {G : CFGraph} (hconn : graph_connected G) (u v : G.V) (τ : AspPerm) :
    TransmissionExists G u v τ → TransmissionExists G v u τ⁻¹ := by
  rintro ⟨D, hD⟩
  exact ⟨transmissionDualDivisor u v D, satisfiesTransmission_dual hconn hD⟩

/-- The duality transport is an equivalence after applying it twice. -/
theorem transmissionExists_dual_iff
    {G : CFGraph} (hconn : graph_connected G) (u v : G.V) (τ : AspPerm) :
    TransmissionExists G v u τ⁻¹ ↔ TransmissionExists G u v τ := by
  constructor
  · simpa only [inv_inv] using transmissionExists_dual hconn v u τ⁻¹
  · exact transmissionExists_dual hconn u v τ

end Utilities
