/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalValue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponentDegree

/-!
# API checks for principal and residual ordinal values

The approach-zero Hahn series supplies a concrete nonzero input whose ordinal value is strictly
greater than one. The first certificate checks both ordinary and Hessenberg reconstruction on
that input, as well as the defining classes of the two factors. The constant-one certificate
checks that a nonzero series of ordinal value one is outside the exact domain.

The companion ordinal-factor client distinguishes the final principal factor from the first
factor by an asymmetric computation and checks the singleton residual convention. Together these
clients test the factorisation primitives and their application to Berarducci's ordinal value.
-/

public noncomputable section

namespace Tests

open scoped HahnSeries NatOrdinal

/-- The approach-zero series, packaged in the exact domain of principal and residual values. -/
def approachZeroWithOrdinalValueAboveOne :
    Berarducci.SeriesWithOrdinalValueAboveOne ℚ :=
  ⟨approachZeroNonpositive, by
    apply Berarducci.one_lt_ordinalValue_of_constantCoeff_eq_zero_of_supportSup_eq_zero
    · rw [HahnSeries.Nonpositive.constantCoeff_apply, coe_approachZeroNonpositive]
      exact not_ne_iff.mp (by
        simpa [HahnSeries.mem_support] using zero_not_mem_approachZero_support)
    · exact approachZero_supportSup⟩

/-- Principal and residual values satisfy all source characteristics on a concrete nonzero input
whose support is cofinal in zero. -/
theorem approachZero_principalResidualValue_certificate :
    (approachZeroWithOrdinalValueAboveOne : Berarducci.Series ℚ) ≠ 0 ∧
      Ordinal.IsInfiniteMultiplicativelyPrincipal
        approachZeroWithOrdinalValueAboveOne.principalValue.val ∧
      Ordinal.IsAdditivelyPrincipal
        approachZeroWithOrdinalValueAboveOne.residualValue.val ∧
      approachZeroWithOrdinalValueAboveOne.residualValue.val *
          approachZeroWithOrdinalValueAboveOne.principalValue.val =
        (Berarducci.ordinalValue approachZeroNonpositive).val ∧
      approachZeroWithOrdinalValueAboveOne.residualValue *
          approachZeroWithOrdinalValueAboveOne.principalValue =
        Berarducci.ordinalValue approachZeroNonpositive := by
  exact ⟨approachZero_ne_zero,
    approachZeroWithOrdinalValueAboveOne.principalValue_isInfiniteMultiplicativelyPrincipal,
    approachZeroWithOrdinalValueAboveOne.residualValue_isAdditivelyPrincipal,
    approachZeroWithOrdinalValueAboveOne.residualValue_val_mul_principalValue_val,
    approachZeroWithOrdinalValueAboveOne.residualValue_mul_principalValue⟩

private theorem approachZero_ordinalValue_eq_wpow_one :
    Berarducci.ordinalValue approachZeroNonpositive = ω^ (1 : NatOrdinal) :=
  Berarducci.ordinalValue_eq_wpow_of_isPrincipal
    approachZero_isPrincipal approachZero_degree_eq_one

/-- The successor-exponent formulas identify the two factors of the concrete degree-one
principal series. -/
theorem approachZero_successor_principalResidualValue :
    approachZeroWithOrdinalValueAboveOne.principalValue = ω^ (1 : NatOrdinal) ∧
      approachZeroWithOrdinalValueAboveOne.residualValue = 1 := by
  have hone : 0 < (1 : NatOrdinal).constantCoeff := by
    have h : (1 : NatOrdinal) = ((1 : ℕ) : NatOrdinal) := by norm_num
    rw [h, NatOrdinal.constantCoeff_natCast]
    norm_num
  constructor
  · exact approachZeroWithOrdinalValueAboveOne.principalValue_eq_wpow_one_of_ordinalValue_eq_wpow
      1 hone approachZero_ordinalValue_eq_wpow_one
  · have hremove : (1 : NatOrdinal).removeNat 1 = 0 := by
      symm
      apply (NatOrdinal.eq_removeNat_iff_add_natCast_eq
        (a := (1 : NatOrdinal)) (eta := 0) (n := 1)
        (Nat.succ_le_iff.mpr hone)).mpr
      simp
    simpa [hremove] using
      approachZeroWithOrdinalValueAboveOne.residualValue_eq_wpow_removeNat_of_ordinalValue_eq_wpow
        1 hone approachZero_ordinalValue_eq_wpow_one

/-- The nonzero constant-one series is excluded from the domain because its ordinal value is one. -/
theorem not_one_lt_ordinalValue_constant_one :
    ¬1 < Berarducci.ordinalValue (HahnSeries.Nonpositive.C (1 : ℚ)) := by
  have hvalue :
      Berarducci.ordinalValue (HahnSeries.Nonpositive.C (1 : ℚ)) = 1 := by
    apply Berarducci.ordinalValue_eq_one_iff.mpr
    constructor
    · apply Berarducci.mem_nearConstantSubgroup_iff.mpr
      exact ⟨0, (HahnSeries.Nonpositive.negativeMonomialIdeal ℚ).zero_mem, 1, by simp⟩
    · intro hmem
      have hcoeff := Berarducci.constantCoeff_eq_zero_of_mem_negativeMonomialIdeal hmem
      norm_num at hcoeff
  intro hlt
  rw [hvalue] at hlt
  exact lt_irrefl 1 hlt

end Tests
