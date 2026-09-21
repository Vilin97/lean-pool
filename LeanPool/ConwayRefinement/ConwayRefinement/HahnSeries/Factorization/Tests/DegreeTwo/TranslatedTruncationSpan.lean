/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.DegreeTwo.TranslatedTruncationSpan
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValue

/-!
# API checks for the Pommersheim--Shahriari translated-truncation span

The constant-one series separates the [PS06] quotient by `J + K` from Berarducci's quotient by
`J`: it vanishes in the former and remains nonzero in the latter. The approach-zero series then
shows that quotienting constants has not collapsed the whole space.
-/

public noncomputable section

namespace Tests

open scoped HahnSeries

/-- Constant one vanishes modulo `J + K`. -/
theorem constant_one_eq_zero_modulo_constants :
    PommersheimShahriari.toSeriesQuotientByJAddConstants
      (HahnSeries.Nonpositive.C (1 : ℚ)) = 0 := by
  rw [PommersheimShahriari.toSeriesQuotientByJAddConstants_eq_zero_iff]
  exact Berarducci.mem_nearConstantSubgroup_iff.mpr
    ⟨0, (HahnSeries.Nonpositive.negativeMonomialIdeal ℚ).zero_mem, 1, by simp⟩

/-- The same constant remains nonzero in Berarducci's quotient by `J` alone. -/
theorem constant_one_ne_zero_in_berarducci_germ :
    Berarducci.toGerm (HahnSeries.Nonpositive.C (1 : ℚ)) ≠ 0 := by
  intro hzero
  have hmem : HahnSeries.Nonpositive.C (1 : ℚ) ∈
      HahnSeries.Nonpositive.negativeMonomialIdeal ℚ := by
    rw [← sub_zero (HahnSeries.Nonpositive.C (1 : ℚ)),
      ← Berarducci.toGerm_eq_toGerm_iff]
    simpa using hzero
  have hcoeff := Berarducci.constantCoeff_eq_zero_of_mem_negativeMonomialIdeal hmem
  norm_num at hcoeff

/-- The approach-zero series is nonzero modulo `J + K`, so the [PS06] vector space is
nondegenerate. -/
theorem approachZero_ne_zero_modulo_constants :
    PommersheimShahriari.toSeriesQuotientByJAddConstants approachZeroNonpositive ≠ 0 := by
  intro hzero
  have hnear :=
    PommersheimShahriari.toSeriesQuotientByJAddConstants_eq_zero_iff.mp hzero
  exact (Berarducci.one_lt_ordinalValue_iff.mp
    (Berarducci.one_lt_ordinalValue_of_constantCoeff_eq_zero_of_supportSup_eq_zero
      (by
        rw [HahnSeries.Nonpositive.constantCoeff_apply, coe_approachZeroNonpositive]
        exact not_ne_iff.mp (by
          simpa [HahnSeries.mem_support] using zero_not_mem_approachZero_support))
      approachZero_supportSup)) hnear

end Tests
