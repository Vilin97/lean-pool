/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.ExactOrderTraceBudget
public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.NonparabolicPuncturedSmallOrderCount

/-!
# Exact-order square bound for punctured small-order points

The root-sum convention is retained: `combinedTruncatedOrderTotientSum` counts
eigenvalue roots, not traces.  Inversion pairing supplies the factor two
before the two-coordinate Markoff fiber estimate is squared.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

/-- The punctured two-coordinate low-order set is bounded by the square of
the exact combined split/nonsplit root budget. -/
theorem two_mul_puncturedSmallNonparabolicOrder_succ_card_le_rootSumSq
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpTwo : p ≠ 2) (bound : ℕ) :
    2 *
        (puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
          p (bound + 1)).card ≤
      (combinedTruncatedOrderTotientSum p bound) ^ 2 := by
  classical
  rw [
    puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders_card_eq_normalized
  ]
  let smallSet :=
    normalizedPuncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
      p (bound + 1)
  let traceSet :=
    nonparabolicConcreteLowOrderTraceSet p (bound + 1)
  have hpoints : smallSet.card ≤ 2 * traceSet.card ^ 2 := by
    rw [← Finset.card_map
      (f := ⟨Subtype.val, Subtype.val_injective⟩)]
    exact
      (Finset.card_mono
        (normalizedPuncturedSmallNonparabolicOrderValues_subset_traceSet
          hpTwo (bound + 1))).trans
        (normalizedMarkoffPointsWithFirstTwoCoordinatesIn_card_le traceSet)
  have htraces :
      2 * traceSet.card ≤
        combinedTruncatedOrderTotientSum p bound := by
    exact
      two_mul_nonparabolicConcreteLowOrderTraceSet_succ_card_le_totient
        bound
  change
    2 * smallSet.card ≤
      (combinedTruncatedOrderTotientSum p bound) ^ 2
  calc
    2 * smallSet.card ≤ 2 * (2 * traceSet.card ^ 2) :=
      Nat.mul_le_mul_left 2 hpoints
    _ = (2 * traceSet.card) ^ 2 := by ring
    _ ≤ (combinedTruncatedOrderTotientSum p bound) ^ 2 := by
      gcongr

end

end BGS.Markoff
