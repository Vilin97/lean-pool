/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.CompleteHahnGerm
import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.Support.CompleteHahnGermProof

/-! # Complete Hahn Germ Proof -/

public noncomputable section

namespace ConwayRefinement.Standalone.CompleteHahnGerm

universe u v

namespace IsPolynomialRing

/-- The germ ring is a polynomial ring over its coefficient field. -/
theorem proof (G : Type u) (K : Type v)
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [NoMinOrder G] [Field K] :
    IsPolynomialRing G K := Support.isPolynomialRing G K

end IsPolynomialRing

namespace HasRefinement

/-- Polynomiality gives the four-factor refinement of germs. -/
theorem proof (G : Type u) (K : Type v)
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [NoMinOrder G] [Field K] :
    HasRefinement G K := Support.hasRefinement G K

end HasRefinement

end ConwayRefinement.Standalone.CompleteHahnGerm
