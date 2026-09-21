/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.CriticalPointExistence

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# API checks for Berarducci critical points

The monomial `t⁻¹` has critical point `-1`, not zero: truncating exactly at its support exponent
turns it into a nonzero constant germ, while truncating strictly earlier gives zero. Squaring it
then exercises Berarducci's critical-product formula at the genuinely negative point `-2`.
-/

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace Tests

/-- The coefficient-one monomial `t⁻¹` as a nonpositive real Hahn series. -/
def criticalNegativeMonomial : Berarducci.Series ℚ :=
  HahnSeries.Nonpositive.single (-1) 1 (by norm_num)

private theorem coe_criticalNegativeMonomial :
    (criticalNegativeMonomial : ℚ⟦ℝ⟧) = HahnSeries.single (-1) 1 := by
  rw [criticalNegativeMonomial, HahnSeries.Nonpositive.coe_single]

private theorem criticalNegativeMonomial_ne_zero : criticalNegativeMonomial ≠ 0 := by
  intro hzero
  have hcoe := congrArg Subtype.val hzero
  rw [coe_criticalNegativeMonomial] at hcoe
  exact HahnSeries.single_ne_zero one_ne_zero hcoe

private theorem criticalNegativeMonomial_value :
    Berarducci.ordinalValue
      (Berarducci.translatedTruncation (criticalNegativeMonomial : ℚ⟦ℝ⟧) (-1)) = 1 := by
  rw [coe_criticalNegativeMonomial, Berarducci.translatedTruncation_single_cut,
    Berarducci.ordinalValue_C_of_ne one_ne_zero]

private theorem criticalNegativeMonomial_germ_zero_of_lt
    {y : ℝ} (hy : y < -1) :
    Berarducci.translatedTruncation (criticalNegativeMonomial : ℚ⟦ℝ⟧) y = 0 := by
  apply Subtype.ext
  ext d
  rw [Berarducci.coeff_translatedTruncation]
  by_cases hd : d ≤ 0
  · rw [if_pos hd, coe_criticalNegativeMonomial]
    have hne : y + d ≠ -1 := by linarith
    rw [HahnSeries.coeff_single_of_ne hne]
    simp
  · simp [hd]

/-- The exponent `-1` is the critical point of `t⁻¹`; this excludes a definition that
automatically chooses zero for every nonzero series. -/
theorem criticalNegativeMonomial_isCriticalPoint :
    Berarducci.IsCriticalPoint criticalNegativeMonomial (-1) := by
  rw [Berarducci.isCriticalPoint_iff]
  refine ⟨criticalNegativeMonomial_ne_zero, by norm_num, ?_, ?_⟩
  · intro y _hy
    rw [criticalNegativeMonomial_value]
    calc
      Berarducci.ordinalValue
          (Berarducci.translatedTruncation (criticalNegativeMonomial : ℚ⟦ℝ⟧) y) ≤
          NatOrdinal.of
            ((Berarducci.translatedTruncation
              (criticalNegativeMonomial : ℚ⟦ℝ⟧) y : Berarducci.Series ℚ) :
                ℚ⟦ℝ⟧).supportOrderType :=
        Berarducci.ordinalValue_le_supportOrderType _
      _ ≤ NatOrdinal.of (criticalNegativeMonomial : ℚ⟦ℝ⟧).supportOrderType := by
        apply NatOrdinal.of.monotone
        rw [Berarducci.coe_translatedTruncation, HahnSeries.supportOrderType_translate]
        apply HahnSeries.supportOrderType_mono
        rw [HahnSeries.support_truncLE]
        exact Set.sep_subset _ _
      _ = 1 := by
        rw [coe_criticalNegativeMonomial,
          HahnSeries.supportOrderType_single one_ne_zero]
        simp
  · intro y _hy hvalue
    apply le_of_not_gt
    intro hylt
    have hzero := criticalNegativeMonomial_germ_zero_of_lt hylt
    rw [hzero, Berarducci.ordinalValue_zero,
      criticalNegativeMonomial_value] at hvalue
    exact zero_ne_one hvalue

/-- The general existence theorem produces a critical point for the nondegenerate fixture. -/
theorem criticalNegativeMonomial_exists_isCriticalPoint :
    ∃ x : ℝ, Berarducci.IsCriticalPoint criticalNegativeMonomial x :=
  Berarducci.exists_isCriticalPoint criticalNegativeMonomial_ne_zero

/-- The product formula computes the critical value of `t⁻¹ * t⁻¹` at `-2`. -/
theorem criticalNegativeMonomial_square_value :
    Berarducci.ordinalValue
      (Berarducci.translatedTruncation
        (((criticalNegativeMonomial * criticalNegativeMonomial :
          Berarducci.Series ℚ) : ℚ⟦ℝ⟧)) (-2)) = 1 := by
  rw [show (-2 : ℝ) = -1 + -1 by norm_num]
  rw [Berarducci.criticalPoint_product_value
    criticalNegativeMonomial_isCriticalPoint criticalNegativeMonomial_isCriticalPoint,
    criticalNegativeMonomial_value, one_mul]

end Tests
