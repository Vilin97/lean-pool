/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.NormalForm

/-!
# API checks for the Conway normal form of surreal numbers

The two-term example has distinct exponents and nonzero coefficients, so it separates the Conway
normal form from the false conversion that retains only the leading term. Both directions of the
normal-form equivalence are evaluated on this example.
-/

public noncomputable section

namespace Tests

open Set SurrealHahnSeries

theorem surrealNormalForm_zero :
    SurrealHahnSeries.toSurreal (Surreal.toHahnSeries 0) = 0 := by
  simp

theorem surrealNormalForm_single_real (r : ℝ) :
    SurrealHahnSeries.toSurreal (.single 0 r) = r := by
  simp

private theorem zero_lt_support_single_one {j : Surreal}
    (hj : j ∈ (SurrealHahnSeries.single 1 1).support) : 0 < j := by
  have : j = 1 := mem_singleton_iff.mp (support_single_subset hj)
  simp [this]

theorem surrealNormalForm_twoTerm :
    SurrealHahnSeries.toSurreal
        (SurrealHahnSeries.single 1 1 + SurrealHahnSeries.single 0 1) =
      ω^ (1 : Surreal) + 1 := by
  rw [SurrealHahnSeries.toSurreal_succ]
  · simp
  · exact fun j hj ↦ zero_lt_support_single_one hj

theorem surrealNormalForm_twoTerm_roundTrip :
    Surreal.toHahnSeries
        (SurrealHahnSeries.toSurreal
          (SurrealHahnSeries.single 1 1 + SurrealHahnSeries.single 0 1)) =
      SurrealHahnSeries.single 1 1 + SurrealHahnSeries.single 0 1 := by
  simp

theorem surrealNormalForm_twoTerm_ne_leadingTerm :
    SurrealHahnSeries.toSurreal
        (SurrealHahnSeries.single 1 1 + SurrealHahnSeries.single 0 1) ≠
      SurrealHahnSeries.toSurreal (SurrealHahnSeries.single 1 1) := by
  rw [surrealNormalForm_twoTerm]
  simp

end Tests
