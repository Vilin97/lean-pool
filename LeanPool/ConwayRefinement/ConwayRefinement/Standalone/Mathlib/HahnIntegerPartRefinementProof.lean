/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.HahnIntegerPartRefinement
import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.Support.HahnIntegerPartRefinementProof

/-! # Hahn Integer Part Refinement Proof -/
public noncomputable section

namespace ConwayRefinement.Standalone.Hahn.HahnIntegerPartRefinement

universe u v

variable {G : Type u} {R : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Field R]
variable [Module ℚ G] [IsOrderedModule ℚ G] [CharZero R]

/-- Refinement for Hahn series with integer constant coefficient. -/
theorem proof : HahnIntegerPartRefinement (G := G) (R := R) :=
  of_saturation_integer_coefficients

end ConwayRefinement.Standalone.Hahn.HahnIntegerPartRefinement
