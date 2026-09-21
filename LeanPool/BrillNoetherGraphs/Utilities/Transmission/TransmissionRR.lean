/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Transmission.Transmission

/-!
# Riemann--Roch duality for transmission rows

For a transmission witness, every marked twist has known degree.  Riemann--Roch
therefore converts its rank inequality into an equivalent lower bound for the
canonical complement.  This file packages that conversion without yet using
any ASP-specific simplification of the complementary slipface expression.
-/

namespace Utilities

/-- Exact Riemann--Roch relation for a marked twist of a transmission witness. -/
theorem transmission_twist_rank_rr
    {G : CFGraph} (hconn : graph_connected G)
    {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (h : SatisfiesTransmission G u v τ D) (a b : ℤ) :
    rank G (D + a • one_chip u - b • one_chip v) -
        rank G (canonical_divisor G -
          (D + a • one_chip u - b • one_chip v)) =
      τ.χ + a - b + 1 := by
  have hRR := riemann_roch_for_graphs hconn
    (D + a • one_chip u - b • one_chip v)
  rw [degree_twist_of_satisfiesTransmission h a b] at hRR
  linarith

/-- Solved form of the marked Riemann--Roch relation. -/
theorem transmission_twist_rank_eq_complement_rank
    {G : CFGraph} (hconn : graph_connected G)
    {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (h : SatisfiesTransmission G u v τ D) (a b : ℤ) :
    rank G (D + a • one_chip u - b • one_chip v) =
      rank G (canonical_divisor G -
        (D + a • one_chip u - b • one_chip v)) +
        τ.χ + a - b + 1 := by
  linarith [transmission_twist_rank_rr hconn h a b]

/-- The transmission row inequality implies the corresponding canonical
complement lower bound. -/
theorem canonical_complement_rank_ge_of_satisfiesTransmission
    {G : CFGraph} (hconn : graph_connected G)
    {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (h : SatisfiesTransmission G u v τ D) (a b : ℤ) :
    rank G (canonical_divisor G -
      (D + a • one_chip u - b • one_chip v)) ≥
        τ.s (a + 1) b - τ.χ - a + b - 2 := by
  have hRow := rank_twist_of_satisfiesTransmission h a b
  have hRR := transmission_twist_rank_rr hconn h a b
  linarith

/-- For a transmission witness, the original row lower bound is equivalent to
the Riemann--Roch translated lower bound on its canonical complement. -/
theorem transmission_row_iff_canonical_complement_row
    {G : CFGraph} (hconn : graph_connected G)
    {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (hDegree : deg D = (genus G : ℤ) + τ.χ)
    (a b : ℤ) :
    TransmissionInequality G u v τ D a b ↔
      rank G (canonical_divisor G -
        (D + a • one_chip u - b • one_chip v)) ≥
          τ.s (a + 1) b - τ.χ - a + b - 2 := by
  have hTwistDegree :
      deg (D + a • one_chip u - b • one_chip v) =
        (genus G : ℤ) + τ.χ + a - b := by
    rw [deg_add_marked_twist, hDegree]
  have hRR := riemann_roch_for_graphs hconn
    (D + a • one_chip u - b • one_chip v)
  rw [hTwistDegree] at hRR
  unfold TransmissionInequality
  constructor <;> intro h <;> linarith

/-- Package the dual row inequalities for all lattice points. -/
theorem canonical_complement_rows_of_satisfiesTransmission
    {G : CFGraph} (hconn : graph_connected G)
    {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (h : SatisfiesTransmission G u v τ D) :
    ∀ a b : ℤ,
      rank G (canonical_divisor G -
        (D + a • one_chip u - b • one_chip v)) ≥
          τ.s (a + 1) b - τ.χ - a + b - 2 := by
  intro a b
  exact canonical_complement_rank_ge_of_satisfiesTransmission hconn h a b

end Utilities
