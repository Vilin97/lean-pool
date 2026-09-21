/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.Multiplication

/-!
# Checks for omnific-integer normal-form multiplication

These checks exercise closure and the public characteristic theorem for the transported
normal-form product without unfolding its definition.
-/

public noncomputable section

namespace Tests

open Surreal

/-- Formal Hahn multiplication of omnific-integer normal forms again represents an omnific
integer. -/
example {x y : Surreal} (hx : x.IsOmnificInteger) (hy : y.IsOmnificInteger) :
    ((x.toHahnSeries * y.toHahnSeries).toSurreal).IsOmnificInteger :=
  hx.toHahnSeries_mul_toSurreal hy

/-- Compatibility on positive truncations is sufficient for arbitrary omnific integers. -/
example {x y : Surreal} (hx : x.IsOmnificInteger) (hy : y.IsOmnificInteger)
    (hpositive : (x.trunc 0 * y.trunc 0).toHahnSeries =
      x.toHahnSeries.trunc 0 * y.toHahnSeries.trunc 0) :
    (x * y).toHahnSeries = x.toHahnSeries * y.toHahnSeries :=
  hx.toHahnSeries_mul_of_trunc_zero hy hpositive

/-- The public normal form of the transported product computes to the Hahn product. -/
example (x y : Surreal.OmnificInteger) :
    (x.normalFormProduct y : Surreal).toHahnSeries =
      x.1.toHahnSeries * y.1.toHahnSeries :=
  Surreal.OmnificInteger.toHahnSeries_normalFormProduct x y

/-- Transported normal-form multiplication is the ordinary omnific-integer multiplication. -/
example (x y : Surreal.OmnificInteger) :
    x.normalFormProduct y = x * y :=
  Surreal.OmnificInteger.normalFormProduct_eq_mul x y

end Tests
