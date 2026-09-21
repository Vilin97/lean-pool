/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DegreeValuation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportResidue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.Statements.Degree

/-!
# Multiplicativity of the degree valuation in characteristic zero

Hahn-series degree on `K((ℝ^{≤0}))` is a max-additive degree over every coefficient field,
bundled as `degreeValuation K` from the submultiplicative bound of LM24, Corollary 3.1.2 alone.
Over a field of characteristic zero it is exactly multiplicative (LM24, Theorem D, proved as
`degree_mul`), so it is LM24's multiplicative valuation `deg`. This module
records Theorem D once, as the instance `(degreeValuation K).IsMultiplicative`; the degree-graded
ring `gr_deg K((ℝ^{≤0}))` therefore has no homogeneous zero divisors under `[CharZero K]`, and
every statement that needs exact degrees of products reads this instance.
-/

universe v

open scoped HahnSeries

public noncomputable section

namespace HahnSeries.Nonpositive

variable (K : Type v) [Field K] [CharZero K]

/-- LM24, Theorem D: the degree valuation is multiplicative. -/
instance degreeValuation_isMultiplicative : (degreeValuation K).IsMultiplicative :=
  ⟨fun b c ↦ by
    simp only [degreeValuation_apply]
    exact degree_mul b c⟩

end HahnSeries.Nonpositive
