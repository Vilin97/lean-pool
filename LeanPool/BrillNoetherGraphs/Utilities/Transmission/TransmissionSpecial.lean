/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Transmission.Transmission
import LeanPool.BrillNoetherGraphs.Demazure.SlipFace

/-!
# Transmission inequalities outside the special slipface locus are automatic

For a divisor of transmission degree `g + χ`, the twist at `(a,b)` has degree
`g + χ + a - b`.  Graph Riemann--Roch gives the universal lower bound

`rank(T) ≥ deg(T) - g = χ + a - b`.

On the other hand a slipface is bounded below by
`max 0 (a+1-b+χ)`.  Therefore, whenever the slipface equals this generic
baseline, the corresponding transmission inequality is automatic:

* baseline `0` asks only for rank `≥ -1`;
* baseline `a+1-b+χ > 0` asks for rank `≥ χ+a-b`, exactly the RR lower bound.

Thus only rows with strict slipface excess over the generic baseline need to be
checked.  This is the Schubert-special locus on which an essential-set theorem
should operate.
-/

namespace Utilities

/-- Universal Riemann--Roch lower bound `r(D) ≥ deg(D)-g`. -/
theorem rank_ge_degree_sub_genus
    {G : CFGraph} (hconn : graphConnected G) (D : CFDiv G) :
    rank G D ≥ deg D - (genus G : ℤ) := by
  have hRR := riemann_roch_for_graphs hconn D
  have hDual : rank G (canonicalDivisor G - D) ≥ -1 :=
    rank_geq_neg_one G (canonicalDivisor G - D)
  linarith

/-- A row is special when its ASP slipface lies strictly above the generic
slipface of the same shift. -/
def SpecialTransmissionPair (τ : AspPerm) (a b : ℤ) : Prop :=
  τ.s (a + 1) b > max 0 (a + 1 - b + τ.χ)

/-- The special row set. -/
def SpecialTransmissionSet (τ : AspPerm) : Set (ℤ × ℤ) :=
  {p | SpecialTransmissionPair τ p.1 p.2}

/-- A nonspecial row is exactly on the generic slipface baseline. -/
theorem slipface_eq_baseline_of_not_special
    (τ : AspPerm) (a b : ℤ)
    (h : ¬ SpecialTransmissionPair τ a b) :
    τ.s (a + 1) b = max 0 (a + 1 - b + τ.χ) := by
  unfold SpecialTransmissionPair at h
  have hLower := τ.s.ge_max (a + 1) b
  rw [τ.s_chi_eq] at hLower
  omega

/-- Every nonspecial row is automatic for a connected graph once the divisor has
transmission degree. -/
theorem transmissionInequality_of_not_special
    {G : CFGraph} (hconn : graphConnected G)
    (u v : G.V) (τ : AspPerm) (D : CFDiv G)
    (hDegree : deg D = (genus G : ℤ) + τ.χ)
    (a b : ℤ) (h : ¬ SpecialTransmissionPair τ a b) :
    TransmissionInequality G u v τ D a b := by
  have hBase := slipface_eq_baseline_of_not_special τ a b h
  unfold TransmissionInequality
  rw [hBase]
  by_cases hPos : 0 < a + 1 - b + τ.χ
  · have hMax : max 0 (a + 1 - b + τ.χ) = a + 1 - b + τ.χ :=
      max_eq_right (le_of_lt hPos)
    rw [hMax]
    have hTwistDegree :
        deg (D + a • oneChip u - b • oneChip v) =
          (genus G : ℤ) + τ.χ + a - b := by
      rw [deg_add_marked_twist, hDegree]
    have hRank := rank_ge_degree_sub_genus hconn
      (D + a • oneChip u - b • oneChip v)
    rw [hTwistDegree] at hRank
    omega
  · have hNonpos : a + 1 - b + τ.χ ≤ 0 := le_of_not_gt hPos
    have hMax : max 0 (a + 1 - b + τ.χ) = 0 := max_eq_left hNonpos
    rw [hMax]
    simpa using rank_geq_neg_one G (D + a • oneChip u - b • oneChip v)

/-- Full transmission is equivalent, on a connected graph, to checking only the
special slipface rows together with the degree equation. -/
theorem satisfiesTransmission_iff_special
    {G : CFGraph} (hconn : graphConnected G)
    (u v : G.V) (τ : AspPerm) (D : CFDiv G) :
    SatisfiesTransmission G u v τ D ↔
      deg D = (genus G : ℤ) + τ.χ ∧
        ∀ a b : ℤ, SpecialTransmissionPair τ a b →
          TransmissionInequality G u v τ D a b := by
  constructor
  · intro h
    exact ⟨h.1, fun a b _ => h.2 a b⟩
  · rintro ⟨hDegree, hSpecial⟩
    refine ⟨hDegree, ?_⟩
    intro a b
    by_cases hab : SpecialTransmissionPair τ a b
    · exact hSpecial a b hab
    · exact transmissionInequality_of_not_special hconn u v τ D hDegree a b hab

/-- Set-level special-row formulation. -/
theorem satisfiesTransmission_iff_specialSet
    {G : CFGraph} (hconn : graphConnected G)
    (u v : G.V) (τ : AspPerm) (D : CFDiv G) :
    SatisfiesTransmission G u v τ D ↔
      deg D = (genus G : ℤ) + τ.χ ∧
        SatisfiesTransmissionOn G u v τ D (SpecialTransmissionSet τ) := by
  rw [satisfiesTransmission_iff_special hconn u v τ D]
  constructor
  · rintro ⟨hDegree, hRows⟩
    refine ⟨hDegree, ?_⟩
    intro p hp
    exact hRows p.1 p.2 hp
  · rintro ⟨hDegree, hRows⟩
    refine ⟨hDegree, ?_⟩
    intro a b hab
    exact hRows (a, b) hab

end Utilities
