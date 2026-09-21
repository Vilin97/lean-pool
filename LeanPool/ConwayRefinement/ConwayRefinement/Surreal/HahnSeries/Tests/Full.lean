/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.Full

/-!
# Checks for full Conway Hahn series

The square of `ω + 1` exercises two distinct nonzero exponents and the mixed convolution term.
Its coefficient at exponent one is two, separating genuine multiplication from a plausible wrong
operation that keeps only products of matching or leading exponents.
-/

universe u

public noncomputable section

namespace Tests

open Surreal

/-- The nondegenerate two-term surreal `ω + 1`. -/
def twoTermSurreal : Surreal.{u} :=
  ω^ (1 : Surreal.{u}) + ((1 : ℝ) : Surreal.{u})


/-- The full Hahn embedding preserves arbitrary surreal products. -/
example (x y : Surreal.{u}) :
    toFullHahnSeries (x * y) = toFullHahnSeries x * toFullHahnSeries y :=
  toFullHahnSeries_mul x y

/-- The full Conway map preserves the square of the nondegenerate two-term example. -/
theorem toFullHahnSeries_twoTerm_square :
    toFullHahnSeries
        ((twoTermSurreal : Surreal.{u}) * twoTermSurreal) =
      toFullHahnSeries (twoTermSurreal : Surreal.{u}) *
        toFullHahnSeries twoTermSurreal :=
  toFullHahnSeries_mul _ _

/-- The mixed coefficient in the nondegenerate square is two. -/
theorem toFullHahnSeries_twoTerm_square_coeff_one :
    (toFullHahnSeries
      ((twoTermSurreal : Surreal.{u}) * twoTermSurreal)).coeff
        (OrderDual.toDual (1 : Surreal.{u})) = 2 := by
  rw [toFullHahnSeries_twoTerm_square]
  simp only [twoTermSurreal, toFullHahnSeries_add,
    toFullHahnSeries_wpow, toFullHahnSeries_realCast]
  rw [add_mul, mul_add, mul_add]
  simp only [HahnSeries.single_mul_single]
  rw [HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add]
  simp only [HahnSeries.coeff_single]
  simp
  norm_num

end Tests
