/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.InlineConwayRefinementProof

/-!
# Conway's refinement theorem

This module connects Palomar's advertised declaration to the proof.
-/

public noncomputable section

universe u

namespace ConwayRefinement.Palomar

/-- Conway's refinement theorem for omnific integers, stated from first principles. -/
theorem conwayRefinement :
    ConwayRefinement.Standalone.InlineConwayRefinement.Surreal.ConwayConjecture.{u} :=
  ConwayRefinement.Standalone.InlineConwayRefinement.Surreal.ConwayConjecture.proof

end ConwayRefinement.Palomar
