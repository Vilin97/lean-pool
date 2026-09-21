/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero
public import Mathlib.Order.UpperLower.Relative

/-!
# API check for final support segments and Berarducci's ordinal value

The approach-zero series with constant coefficient one has ordinal value greater than one and
support containing zero. Its strictly negative support is nonempty, so the final-segment theorem
gives the intended lower bound there.

This fixture separates strict negative support from the nearby incorrect full-support statement.
The singleton containing zero is a nonempty final segment of the full support and has order type
one, strictly below the series' ordinal value. Thus including the exponent zero would make the
claimed lower bound false rather than merely change its presentation.
-/

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace Tests

open Ordinal

/-- The approach-zero series with a nonzero constant coefficient. -/
def approachZeroPlusOne : Berarducci.Series ℚ :=
  approachZeroNonpositive + HahnSeries.Nonpositive.C 1

private theorem approachZero_ordinalValue_one_lt :
    1 < Berarducci.ordinalValue approachZeroNonpositive := by
  apply Berarducci.one_lt_ordinalValue_of_constantCoeff_eq_zero_of_supportSup_eq_zero
  · rw [HahnSeries.Nonpositive.constantCoeff_apply, coe_approachZeroNonpositive]
    exact not_ne_iff.mp (by
      simpa [HahnSeries.mem_support] using zero_not_mem_approachZero_support)
  · exact approachZero_supportSup

/-- Adding a nonzero constant coefficient does not place the approach-zero series in `J + K`. -/
theorem approachZeroPlusOne_ordinalValue_one_lt :
    1 < Berarducci.ordinalValue approachZeroPlusOne := by
  apply Berarducci.one_lt_ordinalValue_iff.mpr
  have happroach :=
    Berarducci.one_lt_ordinalValue_iff.mp approachZero_ordinalValue_one_lt
  intro hsum
  apply happroach
  have hconstant : HahnSeries.Nonpositive.C (1 : ℚ) ∈
      Berarducci.nearConstantSubgroup ℚ := by
    apply Berarducci.mem_nearConstantSubgroup_iff.mpr
    exact ⟨0, (HahnSeries.Nonpositive.negativeMonomialIdeal ℚ).zero_mem, 1, by simp⟩
  have hdifference :=
    (Berarducci.nearConstantSubgroup ℚ).sub_mem hsum hconstant
  simpa only [approachZeroPlusOne, add_sub_cancel_right] using hdifference

private theorem approachZeroPlusOne_zero_mem_support :
    (0 : ℝ) ∈ (approachZeroPlusOne : ℚ⟦ℝ⟧).support := by
  rw [HahnSeries.mem_support]
  have hzero : approachZero.coeff 0 = 0 := by
    rw [← not_ne_iff, ← HahnSeries.mem_support]
    exact zero_not_mem_approachZero_support
  simp [approachZeroPlusOne, hzero]

private theorem approachZeroPlusOne_neg_one_mem_support :
    (-1 : ℝ) ∈ (approachZeroPlusOne : ℚ⟦ℝ⟧).support := by
  rw [HahnSeries.mem_support]
  have hcoeff : approachZero.coeff (-1) = 1 := by
    rw [← show approachZeroEmbedding 0 = (-1 : ℝ) by norm_num]
    exact approachZero_coeff_embedding 0
  simp [approachZeroPlusOne, hcoeff]

/-- The public theorem bounds the ordinal value by the order type of the strictly negative
support in a concrete nonconstant example with nonzero constant coefficient. -/
theorem approachZeroPlusOne_strictNegativeSupport_bound :
    (Berarducci.ordinalValue approachZeroPlusOne).val ≤
      ((approachZeroPlusOne : ℚ⟦ℝ⟧).isPWO_support.mono
        (s := (approachZeroPlusOne : ℚ⟦ℝ⟧).support ∩ Set.Iio 0)
        Set.inter_subset_left).orderType := by
  apply Berarducci.ordinalValue_le_orderType_of_isRelUpperSet_negativeSupport
    (C := (approachZeroPlusOne : ℚ⟦ℝ⟧).support ∩ Set.Iio 0)
  · exact isRelUpperSet_self
  · exact ⟨-1, approachZeroPlusOne_neg_one_mem_support, by norm_num⟩

private theorem singletonZero_isRelUpperSet_approachZeroPlusOne_support :
    IsRelUpperSet ({0} : Set ℝ)
      (· ∈ (approachZeroPlusOne : ℚ⟦ℝ⟧).support) := by
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  refine ⟨approachZeroPlusOne_zero_mem_support, ?_⟩
  intro y h0y hy
  rw [Set.mem_singleton_iff]
  exact le_antisymm (HahnSeries.Nonpositive.support_subset approachZeroPlusOne hy) h0y

/-- Including exponent zero would give a nonempty final segment of order type one, although the
series has ordinal value strictly greater than one. -/
theorem approachZeroPlusOne_fullSupport_singleton_counterexample :
    let hsingleton : ({0} : Set ℝ).IsPWO := Set.isPWO_singleton 0
    IsRelUpperSet ({0} : Set ℝ)
        (· ∈ (approachZeroPlusOne : ℚ⟦ℝ⟧).support) ∧
      ({0} : Set ℝ).Nonempty ∧
      hsingleton.orderType = 1 ∧
      1 < (Berarducci.ordinalValue approachZeroPlusOne).val := by
  dsimp only
  refine ⟨singletonZero_isRelUpperSet_approachZeroPlusOne_support,
    Set.singleton_nonempty 0, ?_, ?_⟩
  · let hsingleton : ({0} : Set ℝ).IsPWO := Set.isPWO_singleton 0
    letI : WellFoundedLT ({0} : Set ℝ) := ⟨hsingleton.isWF⟩
    calc
      hsingleton.orderType = typeLT ({0} : Set ℝ) :=
        hsingleton.orderType_eq_typeLT_of_orderIso (OrderIso.refl _)
      _ = 1 := Ordinal.type_eq_one_of_unique _
  · exact NatOrdinal.of_lt_iff.mp approachZeroPlusOne_ordinalValue_one_lt

end Tests
