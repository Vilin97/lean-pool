/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import LeanPool.Odlyzko

/-!
# Solution: Odlyzko bound for root discriminants

Challenge: `odlyzko-root-discriminant-bound` (`Challenge.Odlyzko`)
Proves: `Challenge.Odlyzko.abs_discr_ge`
Solved by: OpenAI Codex
Pool project: `odlyzko-root-discriminant`

This module restates the challenge statement under its own name and proves it. It must not import
the challenge module: comparator exports both environments separately and checks that the statements
agree, which is what makes the verdict independent of the statement file.
-/

namespace Challenge.Odlyzko

open Module NumberField

/-- A totally complex number field of degree at least eighteen has root
discriminant at least `8.25`. -/
theorem abs_discr_ge (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hdim : finrank ℚ K ≥ 18) :
    |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K :=
  DedekindResidue.abs_discr_ge K hdim

end Challenge.Odlyzko
