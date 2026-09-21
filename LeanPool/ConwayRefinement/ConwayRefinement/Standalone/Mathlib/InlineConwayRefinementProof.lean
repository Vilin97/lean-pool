/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.InlineConwayRefinement
import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.Support.InlineConwayRefinementProof

/-! # Inline Conway Refinement Proof -/
public noncomputable section

universe u

namespace ConwayRefinement.Standalone.InlineConwayRefinement.Surreal.ConwayConjecture

/-- Conway's refinement theorem for the fully displayed Mathlib construction of surreal numbers. -/
theorem proof : ConwayConjecture.{u} :=
  ConwayRefinement.Standalone.InlineConwayRefinement.Surreal.conwayRefinementProof

end ConwayRefinement.Standalone.InlineConwayRefinement.Surreal.ConwayConjecture
