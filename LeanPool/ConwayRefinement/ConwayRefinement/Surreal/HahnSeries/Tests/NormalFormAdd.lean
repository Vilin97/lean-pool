/-
Copyright (c) 2026 Dan Abramov, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov, Violeta Hernández Palacios
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.NormalFormAdd

/-!
# API checks for additive Conway normal forms

These checks exercise additive compatibility through the public module boundary. The two-term
example is nondegenerate: its exponents are distinct and both coefficients are nonzero. Its
coefficient at exponent zero separates the result from the plausible but incorrect operation that
retains only the leading term.
-/

public noncomputable section

namespace Tests

open SurrealHahnSeries

theorem surrealNormalForm_add (x y : Surreal) :
    Surreal.toHahnSeries (x + y) = x.toHahnSeries + y.toHahnSeries :=
  Surreal.toHahnSeries_add x y

theorem surrealValue_add (x y : SurrealHahnSeries) :
    (x + y).toSurreal = x.toSurreal + y.toSurreal :=
  SurrealHahnSeries.toSurreal_add x y

theorem surrealNormalForm_neg (x : Surreal) :
    Surreal.toHahnSeries (-x) = -x.toHahnSeries :=
  Surreal.toHahnSeries_neg x

theorem surrealNormalForm_twoTerm_add :
    Surreal.toHahnSeries (ω^ (1 : Surreal) + 1) =
      single 1 1 + single 0 1 := by
  simp

theorem surrealNormalForm_twoTerm_add_constantCoeff :
    (Surreal.toHahnSeries (ω^ (1 : Surreal) + 1)).coeff 0 = 1 := by
  simp only [Surreal.toHahnSeries_add, Surreal.toHahnSeries_wpow,
    Surreal.toHahnSeries_one, coeff_add, Pi.add_apply, coeff_single_self, add_eq_right]
  exact coeff_single_of_ne one_ne_zero 1

end Tests
