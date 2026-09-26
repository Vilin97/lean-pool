/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PrincipalAddition

/-!
# API checks for addition of principal series

The approach-zero series and the constant one give a compiled counterexample to LM24,
Proposition 3.6.2 as printed: both summands are principal and the degree of the sum equals the
degree of the first summand, but the nonzero terminal constant makes the sum nonprincipal.

Adding the approach-zero series to itself exercises the corrected equal-degree theorem on a
nonconstant, infinite-support example. This is the author-confirmed repair used by later LM24
arguments; the broader author-suggested repair for two simultaneously zero or nonzero degrees is
not assumed here.
-/

public noncomputable section

namespace Tests

open HahnSeries
open scoped NatOrdinal

private theorem one_nonpositive_degree_eq_zero :
    ((1 : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).degree =
      (0 : WithBot NatOrdinal) := by
  rw [← map_one (HahnSeries.Nonpositive.C :
      ℚ →+* HahnSeries.Nonpositive ℝ ℚ), HahnSeries.Nonpositive.coe_C]
  change (HahnSeries.C (Γ := ℝ) (1 : ℚ)).degree =
    (0 : WithBot NatOrdinal)
  rw [HahnSeries.C_apply, HahnSeries.degree_eq_cantorDegree,
    HahnSeries.supportOrderType_single one_ne_zero,
    Ordinal.cantorDegree_one]

private theorem approachZero_add_one_degree_eq_one :
    (((approachZeroNonpositive + 1 : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧)).degree =
      (1 : WithBot NatOrdinal) := by
  have h := HahnSeries.degree_add_eq_left_of_lt
    (x := (approachZeroNonpositive : ℚ⟦ℝ⟧))
    (y := ((1 : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧))
    (by rw [approachZero_degree_eq_one, one_nonpositive_degree_eq_zero]; norm_num)
  simpa using h.trans approachZero_degree_eq_one

private theorem approachZero_constantCoeff_eq_zero :
    HahnSeries.Nonpositive.constantCoeff approachZeroNonpositive = 0 := by
  rw [HahnSeries.Nonpositive.constantCoeff_apply, coe_approachZeroNonpositive]
  apply not_ne_iff.mp
  simpa [HahnSeries.mem_support] using zero_not_mem_approachZero_support

/-- The printed formulation of LM24, Proposition 3.6.2 is false. -/
theorem printed_proposition_3_6_2_counterexample :
    ∃ b c : HahnSeries.Nonpositive ℝ ℚ,
      HahnSeries.Nonpositive.IsPrincipal b ∧
        HahnSeries.Nonpositive.IsPrincipal c ∧
        (((b + c : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧)).degree =
          (b : ℚ⟦ℝ⟧).degree ∧
        ¬HahnSeries.Nonpositive.IsPrincipal (b + c) := by
  refine ⟨approachZeroNonpositive, 1, approachZero_isPrincipal,
    HahnSeries.Nonpositive.isPrincipal_one, ?_, ?_⟩
  · rw [approachZero_add_one_degree_eq_one, approachZero_degree_eq_one]
  · intro hprincipal
    have hconstant := hprincipal.constantCoeff_eq_zero_of_degree_pos
      approachZero_add_one_degree_eq_one (by norm_num)
    rw [map_add, approachZero_constantCoeff_eq_zero, map_one, zero_add] at hconstant
    exact one_ne_zero hconstant

private theorem approachZero_add_self_degree_eq_one :
    (((approachZeroNonpositive + approachZeroNonpositive :
      HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧)).degree =
        (1 : WithBot NatOrdinal) := by
  have hsupport :
      (((approachZeroNonpositive + approachZeroNonpositive :
        HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧)).support =
          (approachZeroNonpositive : ℚ⟦ℝ⟧).support := by
    ext x
    simp only [HahnSeries.mem_support, Subring.coe_add, HahnSeries.coeff_add]
    rw [coe_approachZeroNonpositive]
    constructor
    · intro hsum hzero
      exact hsum (by simp [hzero])
    · intro hcoeff hsum
      apply hcoeff
      linarith
  have htype :
      (((approachZeroNonpositive + approachZeroNonpositive :
        HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧)).supportOrderType =
          (approachZeroNonpositive : ℚ⟦ℝ⟧).supportOrderType :=
    HahnSeries.supportOrderType_eq_setOrderType _ |>.trans
      (((approachZeroNonpositive + approachZeroNonpositive :
        HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).isPWO_support.orderType_congr
          (approachZeroNonpositive : ℚ⟦ℝ⟧).isPWO_support hsupport) |>.trans
        (HahnSeries.supportOrderType_eq_setOrderType _).symm
  calc
    (((approachZeroNonpositive + approachZeroNonpositive :
      HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧)).degree =
        Ordinal.cantorDegree
          (((approachZeroNonpositive + approachZeroNonpositive :
            HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧)).supportOrderType :=
      HahnSeries.degree_eq_cantorDegree _
    _ = Ordinal.cantorDegree
        (approachZeroNonpositive : ℚ⟦ℝ⟧).supportOrderType := congrArg _ htype
    _ = (approachZeroNonpositive : ℚ⟦ℝ⟧).degree :=
      (HahnSeries.degree_eq_cantorDegree _).symm
    _ = (1 : WithBot NatOrdinal) := approachZero_degree_eq_one

/-- The corrected equal-degree theorem applies to two genuine infinite principal series. -/
theorem approachZero_add_self_isPrincipal :
    HahnSeries.Nonpositive.IsPrincipal
      (approachZeroNonpositive + approachZeroNonpositive) := by
  apply approachZero_isPrincipal.add_of_degree_eq approachZero_isPrincipal
  · rfl
  · rw [approachZero_add_self_degree_eq_one, approachZero_degree_eq_one]

end Tests
