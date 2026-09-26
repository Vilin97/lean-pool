/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.NormalizationCount
public import LeanPool.MarkoffModP.BGS.Markoff.Core.ConicParametrization

/-!
# The elementary small-order point count

This module connects matrix rotation order to the concrete split/nonsplit trace set and then to
the normalized fixed-fiber bound.  It is the counting step omitted from the paper's final
assembly; no dynamical assertion about escaping to the cage is assumed here.
-/

@[expose] public section

namespace BGS.Markoff

/-- Normalized Markoff points whose first two matrix rotation orders are below `bound`. -/
noncomputable def normalizedMarkoffPointsWithSmallFirstTwoRotationOrders
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)] (bound : ℕ) :
    Finset (NormalizedPoint (ZMod p)) := by
  classical
  exact Finset.univ.filter fun x =>
    IsNormalizedMarkoff x ∧ rotationOrder x.u1 < bound ∧ rotationOrder x.u2 < bound

@[simp]
theorem mem_normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_iff
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)] {bound : ℕ}
    {x : NormalizedPoint (ZMod p)} :
    x ∈ normalizedMarkoffPointsWithSmallFirstTwoRotationOrders p bound ↔
      IsNormalizedMarkoff x ∧ rotationOrder x.u1 < bound ∧ rotationOrder x.u2 < bound := by
  classical
  simp [normalizedMarkoffPointsWithSmallFirstTwoRotationOrders]

theorem normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_subset_traceSet
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)] (hpTwo : p ≠ 2) (bound : ℕ) :
    normalizedMarkoffPointsWithSmallFirstTwoRotationOrders p bound ⊆
      normalizedMarkoffPointsWithFirstTwoCoordinatesIn (concreteLowOrderTraceSet p bound) := by
  intro x hx
  rw [mem_normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_iff] at hx
  exact mem_normalizedMarkoffPointsWithFirstTwoCoordinatesIn_iff.mpr
    ⟨hx.1,
      mem_concreteLowOrderTraceSet_of_rotationOrder_lt p hpTwo x.u1 bound hx.2.1,
      mem_concreteLowOrderTraceSet_of_rotationOrder_lt p hpTwo x.u2 bound hx.2.2⟩

/-- The concrete low-order trace set, counted using the divisors of the two torus orders. -/
theorem concreteLowOrderTraceSet_card_le_divisor_sensitive
    {p : ℕ} [Fact p.Prime] (bound : ℕ) :
    (concreteLowOrderTraceSet p bound).card ≤
      2 + (bound - 1) * ((p - 1).divisors.card + (p + 1).divisors.card) := by
  have hsplit : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, Nat.card_zmod]
  have hnonsplit : Fintype.card (quadraticNormOneTorus p) = p + 1 := by
    rw [← Nat.card_eq_fintype_card, quadraticNormOneTorus_natCard]
  calc
    (concreteLowOrderTraceSet p bound).card ≤
        (normalizedParabolicTraceSet p).card + (bound - 1) *
          ((Fintype.card (ZMod p)ˣ).divisors.card +
            (Fintype.card (quadraticNormOneTorus p)).divisors.card) := by
      exact lowOrderTraceSet_card_le_parabolic_add_pred_mul_divisor_cards
        (normalizedParabolicTraceSet p) (splitTorusTrace : (ZMod p)ˣ → ZMod p)
          (quadraticNormOneTrace p) bound
    _ ≤ 2 + (bound - 1) * ((p - 1).divisors.card + (p + 1).divisors.card) := by
      rw [hsplit, hnonsplit]
      gcongr
      exact Finset.card_le_two

theorem concreteLowOrderTraceSet_succ_card_le_divisor_sensitive
    {p : ℕ} [Fact p.Prime] (d : ℕ) :
    (concreteLowOrderTraceSet p (d + 1)).card ≤
      2 + d * ((p - 1).divisors.card + (p + 1).divisors.card) := by
  simpa using (concreteLowOrderTraceSet_card_le_divisor_sensitive (p := p) (d + 1))

/-- The fully connected crude count used in the giant-orbit assembly. -/
theorem normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)] (hpTwo : p ≠ 2) (bound : ℕ) :
    (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).card ≤
      2 * (2 + 2 * bound ^ 2) ^ 2 := by
  calc
    (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).card ≤
        (normalizedMarkoffPointsWithFirstTwoCoordinatesIn
          (concreteLowOrderTraceSet p bound)).card :=
      Finset.card_mono
        (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_subset_traceSet
          hpTwo bound)
    _ ≤ 2 * (concreteLowOrderTraceSet p bound).card ^ 2 :=
      normalizedMarkoffPointsWithFirstTwoCoordinatesIn_card_le _
    _ ≤ 2 * (2 + 2 * bound ^ 2) ^ 2 := by
      gcongr
      exact concreteLowOrderTraceSet_card_le p bound

/-- The normalized small-order point count obtained from the divisor-sensitive trace count. -/
theorem normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le_divisor_sensitive
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)] (hpTwo : p ≠ 2) (bound : ℕ) :
    (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).card ≤
      2 * (2 + (bound - 1) *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 2 := by
  calc
    (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).card ≤
        (normalizedMarkoffPointsWithFirstTwoCoordinatesIn
          (concreteLowOrderTraceSet p bound)).card :=
      Finset.card_mono
        (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_subset_traceSet
          hpTwo bound)
    _ ≤ 2 * (concreteLowOrderTraceSet p bound).card ^ 2 :=
      normalizedMarkoffPointsWithFirstTwoCoordinatesIn_card_le _
    _ ≤ 2 *
        (2 + (bound - 1) *
          ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 2 := by
      gcongr
      exact concreteLowOrderTraceSet_card_le_divisor_sensitive bound

theorem normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_succ_card_le_divisor_sensitive
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)] (hpTwo : p ≠ 2) (d : ℕ) :
    (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders p (d + 1)).card ≤
      2 * (2 + d * ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 2 := by
  simpa using
    (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le_divisor_sensitive
      hpTwo (d + 1))

end BGS.Markoff
