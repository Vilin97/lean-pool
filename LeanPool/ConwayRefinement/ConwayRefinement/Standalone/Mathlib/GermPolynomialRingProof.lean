/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.GermPolynomialRing
import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.Support.GermPolynomialRingProof

/-! # Germ Polynomial Ring Proof -/

public noncomputable section

namespace ConwayRefinement.Standalone.GermPolynomial

universe u

namespace GermIsPolynomialRing

/-- The ring of germs is a polynomial ring over its coefficient field. -/
theorem proof (K : Type u) [Field K] : GermIsPolynomialRing K := by
  exact of_polynomiality K

end GermIsPolynomialRing

namespace GermHasUniqueFactorization

/-- Every nonzero germ factors uniquely into irreducibles, up to order and association. -/
theorem proof (K : Type u) [Field K] : GermHasUniqueFactorization K := by
  exact of_polynomiality K

end GermHasUniqueFactorization

end ConwayRefinement.Standalone.GermPolynomial
