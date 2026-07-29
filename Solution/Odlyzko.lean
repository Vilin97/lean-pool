/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project, √2
-/

import LeanPool.Odlyzko

/-!
# Solution: Odlyzko bound for root discriminants

Challenge: `odlyzko-root-discriminant-bound` (`Challenge.Odlyzko`)
Proves: `Challenge.Odlyzko.abs_discr_ge`
Solved by: The FLT Project, √2
Pool project: `odlyzko-bound`

This module restates the challenge statement under its own name and proves it. It must not import
the challenge module: comparator exports both environments separately and checks that the statements
agree, which is what makes the verdict independent of the statement file.
-/

/-!
# Solution to the Odlyzko root-discriminant challenge
-/

namespace Challenge.Odlyzko

open Module NumberField

/-- A totally complex number field of degree at least 18 has absolute
discriminant at least `8.25` raised to its degree. -/
theorem abs_discr_ge (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hdim : finrank ℚ K ≥ 18) : |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K :=
  NumberField.Odlyzko.odlyzkoBound K hdim

end Challenge.Odlyzko
