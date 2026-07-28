/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Odlyzko bound for root discriminants

Source: url:https://www.numdam.org/item/SDPP_1976-1977__18_1_A6_0/
Proposed by: Kevin Buzzard, Vasily Ilin
Status: open
Open declarations: `Challenge.Odlyzko.abs_discr_ge`
Tags: number-theory, discriminants, number-fields, flt-assumption
MSC: 11R29, 11R42
Estimated size: ~5000 lines of Lean

Informal statement:
* `Challenge.Odlyzko.abs_discr_ge` — For a totally complex number field K whose degree over the
  rationals is at least 18, the absolute value of the discriminant of K is at least 8.25 raised to
  the power of that degree.
-/

namespace Challenge.Odlyzko

open Module NumberField

/-- An **Odlyzko bound** for the root discriminant of a totally complex number field of degree
18 and above: such a field has root discriminant at least `8.25`. Minkowski's elementary
argument is not strong enough; the bound comes from analysing the zeros of the Dedekind zeta
function of `K`. Stated verbatim as the Fermat's Last Theorem project needs it, where it is
assumed as `FLT.Assumptions.Odlyzko_statement`. -/
theorem abs_discr_ge (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hdim : finrank ℚ K ≥ 18) : |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K := sorry

end Challenge.Odlyzko
