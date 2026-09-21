/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.PuncturedSmallOrderCount
import LeanPool.MarkoffModP.BGS.NumberTheory.MaximalDivisorBounds

/-!
# Small-order Markoff counts using maximal divisors

This is the counting half of the paper's maximal-divisor improvement,
formalized at the finite-set boundary used by the maximal-orbit argument.
-/

namespace BGS.Markoff

open BGS.NumberTheory

def maximalDivisorCountSum (p bound : ℕ) : ℕ :=
  (maximalDivisorsBelow (p - 1) bound).card +
    (maximalDivisorsBelow (p + 1) bound).card

theorem concreteLowOrderTraceSet_card_le_maximalDivisors
    {p : ℕ} [Fact p.Prime] (bound : ℕ) :
    (concreteLowOrderTraceSet p bound).card ≤
      2 + (bound - 1) * maximalDivisorCountSum p bound := by
  classical
  have hsplitCard : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, Nat.card_zmod]
  have hnonsplitCard : Fintype.card (quadraticNormOneTorus p) = p + 1 := by
    rw [← Nat.card_eq_fintype_card, quadraticNormOneTorus_natCard]
  have hsplit :
      (boundedOrderTraceSet
        (splitTorusTrace : (ZMod p)ˣ → ZMod p) bound).card ≤
        (bound - 1) *
          (maximalDivisorsBelow (Fintype.card (ZMod p)ˣ) bound).card := by
    calc
      (boundedOrderTraceSet
        (splitTorusTrace : (ZMod p)ˣ → ZMod p) bound).card ≤
          (elementsOfOrderLessThan (ZMod p)ˣ bound).card :=
        Finset.card_image_le
      _ ≤ (bound - 1) *
          (maximalDivisorsBelow (Fintype.card (ZMod p)ˣ) bound).card := by
        simpa [elementsOfOrderLessThan] using
          (BGS.NumberTheory.elementsOfOrderLessThan_card_le_maximalDivisors
            ((ZMod p)ˣ) bound)
  have hnonsplit :
      (boundedOrderTraceSet (quadraticNormOneTrace p) bound).card ≤
        (bound - 1) *
          (maximalDivisorsBelow
            (Fintype.card (quadraticNormOneTorus p)) bound).card := by
    calc
      (boundedOrderTraceSet (quadraticNormOneTrace p) bound).card ≤
          (elementsOfOrderLessThan (quadraticNormOneTorus p) bound).card :=
        Finset.card_image_le
      _ ≤ (bound - 1) *
          (maximalDivisorsBelow
            (Fintype.card (quadraticNormOneTorus p)) bound).card := by
        simpa [elementsOfOrderLessThan] using
          (BGS.NumberTheory.elementsOfOrderLessThan_card_le_maximalDivisors
            (quadraticNormOneTorus p) bound)
  unfold concreteLowOrderTraceSet lowOrderTraceSet
  calc
    (normalizedParabolicTraceSet p ∪
        boundedOrderTraceSet (splitTorusTrace : (ZMod p)ˣ → ZMod p) bound ∪
        boundedOrderTraceSet (quadraticNormOneTrace p) bound).card ≤
      (normalizedParabolicTraceSet p ∪
        boundedOrderTraceSet
          (splitTorusTrace : (ZMod p)ˣ → ZMod p) bound).card +
        (boundedOrderTraceSet (quadraticNormOneTrace p) bound).card :=
      Finset.card_union_le _ _
    _ ≤ ((normalizedParabolicTraceSet p).card +
        (boundedOrderTraceSet
          (splitTorusTrace : (ZMod p)ˣ → ZMod p) bound).card) +
        (boundedOrderTraceSet (quadraticNormOneTrace p) bound).card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ 2 +
        (bound - 1) *
          (maximalDivisorsBelow (Fintype.card (ZMod p)ˣ) bound).card +
        (bound - 1) *
          (maximalDivisorsBelow
            (Fintype.card (quadraticNormOneTorus p)) bound).card := by
      gcongr
      exact Finset.card_le_two
    _ = 2 + (bound - 1) * maximalDivisorCountSum p bound := by
      rw [hsplitCard, hnonsplitCard]
      simp only [maximalDivisorCountSum, Nat.mul_add]
      omega

theorem concreteLowOrderTraceSet_succ_card_le_maximalDivisors
    {p : ℕ} [Fact p.Prime] (d : ℕ) :
    (concreteLowOrderTraceSet p (d + 1)).card ≤
      2 + d * maximalDivisorCountSum p (d + 1) := by
  simpa using
    (concreteLowOrderTraceSet_card_le_maximalDivisors (p := p) (d + 1))

theorem normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le_maximalDivisors
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpTwo : p ≠ 2) (bound : ℕ) :
    (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).card ≤
      2 * (2 + (bound - 1) * maximalDivisorCountSum p bound) ^ 2 := by
  calc
    (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).card ≤
        (normalizedMarkoffPointsWithFirstTwoCoordinatesIn
          (concreteLowOrderTraceSet p bound)).card :=
      Finset.card_mono
        (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_subset_traceSet
          hpTwo bound)
    _ ≤ 2 * (concreteLowOrderTraceSet p bound).card ^ 2 :=
      normalizedMarkoffPointsWithFirstTwoCoordinatesIn_card_le _
    _ ≤ 2 * (2 + (bound - 1) *
        maximalDivisorCountSum p bound) ^ 2 := by
      gcongr
      exact concreteLowOrderTraceSet_card_le_maximalDivisors bound

theorem puncturedMarkoffPointsWithSmallFirstTwoRotationOrders_succ_card_le_maximalDivisors
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpTwo : p ≠ 2) (d : ℕ) :
    (puncturedMarkoffPointsWithSmallFirstTwoRotationOrders p (d + 1)).card ≤
      2 * (2 + d * maximalDivisorCountSum p (d + 1)) ^ 2 := by
  rw [puncturedMarkoffPointsWithSmallFirstTwoRotationOrders_card_eq_normalized]
  exact
    (normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le_ambient
      (d + 1)).trans
      (by
        simpa using
          (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le_maximalDivisors
            (p := p) hpTwo (d + 1)))

end BGS.Markoff
