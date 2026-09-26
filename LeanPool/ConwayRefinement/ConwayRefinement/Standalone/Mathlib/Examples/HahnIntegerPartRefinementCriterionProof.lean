/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.Examples.HahnIntegerPartRefinementCriterion
import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.Support.HahnIntegerPartRefinementProof

/-! # Hahn Integer Part Refinement Criterion Proof -/

public noncomputable section

namespace ConwayRefinement.Standalone.Hahn.HahnIntegerPartRefinementCriterion

universe u v

variable {G : Type u} {R : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module ℚ G] [IsOrderedModule ℚ G]
variable [Field R]

/-- Conditions `(A1)`--`(A3)` and the common-tail conditions imply four-factor refinement. -/
theorem proof : HahnIntegerPartRefinementCriterion (G := G) (R := R) :=
  HahnIntegerPartRefinement.of_assumptions

end ConwayRefinement.Standalone.Hahn.HahnIntegerPartRefinementCriterion
