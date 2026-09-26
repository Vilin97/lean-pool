/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValue

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueConstantMul
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueDegree
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueSubmultiplicative
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue

/-!
# API checks for submultiplicativity of Berarducci's ordinal value

These certificates separate the submultiplicative bound from three nearby wrong statements: the
same inequality read with ordinary ordinal multiplication instead of the Hessenberg product,
constant-factor invariance without the nonzero hypothesis, and a bound holding only on `J` and
`J + K` rather than in the third branch of the ordinal value.
-/

universe v

public noncomputable section

namespace Tests

open scoped HahnSeries

/-- The submultiplicative bound is stated with Hessenberg multiplication: on the very ordinals it
ranges over, ordinary ordinal multiplication gives a strictly smaller value. -/
theorem naturalMul_ne_ordinalMul :
    ∃ x y : NatOrdinal, NatOrdinal.of (x.val * y.val) ≠ x * y := by
  refine ⟨2, NatOrdinal.of Ordinal.omega0, ?_⟩
  have hpos : (0 : NatOrdinal) < NatOrdinal.of Ordinal.omega0 := by
    simpa using NatOrdinal.of.lt_iff_lt.mpr Ordinal.omega0_pos
  have hval : NatOrdinal.of ((2 : NatOrdinal).val * (NatOrdinal.of Ordinal.omega0).val) =
      NatOrdinal.of Ordinal.omega0 := by
    rw [NatOrdinal.val_of]
    congr 1
    have h2 : ((2 : NatOrdinal).val) = ((2 : ℕ) : Ordinal) := by
      simpa using NatOrdinal.val_natCast 2
    rw [h2]
    exact Ordinal.natCast_mul_omega0 (by norm_num)
  rw [hval]
  refine ne_of_lt ?_
  calc NatOrdinal.of Ordinal.omega0
      < NatOrdinal.of Ordinal.omega0 + NatOrdinal.of Ordinal.omega0 := lt_add_of_pos_left _ hpos
    _ = 2 * NatOrdinal.of Ordinal.omega0 := (two_mul _).symm

/-- Constant-factor invariance genuinely needs the constant to be nonzero. -/
theorem ordinalValue_C_mul_needs_ne_zero :
    ∃ b : Berarducci.Series ℚ,
      Berarducci.ordinalValue (HahnSeries.Nonpositive.C (0 : ℚ) * b) ≠
        Berarducci.ordinalValue b := by
  refine ⟨HahnSeries.Nonpositive.C (1 : ℚ), ?_⟩
  rw [map_zero, zero_mul, Berarducci.ordinalValue_zero,
    Berarducci.ordinalValue_C_of_ne (one_ne_zero (α := ℚ))]
  exact zero_ne_one

/-- Multiplication by a nonzero constant preserves the ordinal value of a series whose value lies
in the third branch. -/
theorem ordinalValue_C_mul_approachZero :
    Berarducci.ordinalValue (HahnSeries.Nonpositive.C (2 : ℚ) * approachZeroNonpositive) =
      Berarducci.ordinalValue approachZeroNonpositive :=
  Berarducci.ordinalValue_C_mul (by norm_num) _

private theorem one_lt_ordinalValue_approachZero :
    1 < Berarducci.ordinalValue approachZeroNonpositive := by
  apply Berarducci.one_lt_ordinalValue_of_constantCoeff_eq_zero_of_supportSup_eq_zero
  · rw [HahnSeries.Nonpositive.constantCoeff_apply, coe_approachZeroNonpositive]
    exact not_ne_iff.mp (by
      simpa [HahnSeries.mem_support] using zero_not_mem_approachZero_support)
  · exact approachZero_supportSup

/-- The submultiplicative bound applies in the third branch of the ordinal value, where both
factors lie outside `J + K`. -/
theorem ordinalValue_mul_le_naturalMul_third_branch :
    ∃ b : Berarducci.Series ℚ,
      1 < Berarducci.ordinalValue b ∧
        Berarducci.ordinalValue (b * b) ≤ Berarducci.ordinalValue b * Berarducci.ordinalValue b :=
  ⟨approachZeroNonpositive, one_lt_ordinalValue_approachZero,
    Berarducci.ordinalValue_mul_le_naturalMul _ _⟩

/-- Berarducci, Theorem 9.7 applies to a nonconstant product in the third branch of the ordinal
value. -/
theorem ordinalValue_mul_approachZero :
    Berarducci.ordinalValue (approachZeroNonpositive * approachZeroNonpositive) =
      Berarducci.ordinalValue approachZeroNonpositive *
        Berarducci.ordinalValue approachZeroNonpositive :=
  Berarducci.ordinalValue_mul _ _

/-- In the ideal branch the submultiplicative bound is an equality with value zero. -/
theorem ordinalValue_mul_negative_monomial :
    Berarducci.ordinalValue
        (HahnSeries.Nonpositive.single (-1) (1 : ℚ) (by norm_num) * approachZeroNonpositive) =
      Berarducci.ordinalValue (HahnSeries.Nonpositive.single (-1) (1 : ℚ) (by norm_num)) *
        Berarducci.ordinalValue approachZeroNonpositive := by
  have hj : HahnSeries.Nonpositive.single (-1) (1 : ℚ) (by norm_num) ∈
      HahnSeries.Nonpositive.negativeMonomialIdeal ℚ :=
    HahnSeries.Nonpositive.single_one_mem_negativeMonomialIdeal (by norm_num)
  rw [Berarducci.ordinalValue_of_mem_negativeMonomialIdeal
      ((HahnSeries.Nonpositive.negativeMonomialIdeal ℚ).mul_mem_right _ hj),
    Berarducci.ordinalValue_of_mem_negativeMonomialIdeal hj, zero_mul]

end Tests
