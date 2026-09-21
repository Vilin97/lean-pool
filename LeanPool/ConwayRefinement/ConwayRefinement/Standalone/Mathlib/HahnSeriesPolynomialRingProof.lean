/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.HahnSeriesPolynomialRing
import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.Support.HahnSeriesPolynomialRingProof

/-! # Hahn Series Polynomial Ring Proof -/

public noncomputable section

namespace ConwayRefinement.Standalone.HahnPolynomial.IsPolynomialRing

universe u

/-- The nonpositive Hahn-series ring is a polynomial ring over its finite-support subring. -/
theorem proof (K : Type u) [Field K] :
    ConwayRefinement.Standalone.HahnPolynomial.IsPolynomialRing K := by
  exact of_polynomiality K

end ConwayRefinement.Standalone.HahnPolynomial.IsPolynomialRing
