/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.PrincipalRVAlgebraicIndependence
import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.PrincipalRVAlgebraicIndependenceProof

/-! # Principal RVAlgebraic Independence Proof -/

public noncomputable section

namespace ConwayRefinement.Standalone.PrincipalRVAlgebraicIndependence

namespace MinimalFamiliesAlgebraicallyIndependent

universe u

/-- Every minimal homogeneous family in `P̂` is algebraically independent. -/
theorem proof (K : Type u) [Field K] :
    PrincipalRVAlgebraicIndependence.MinimalFamiliesAlgebraicallyIndependent K := by
  exact of_algebraicIndependence K

end MinimalFamiliesAlgebraicallyIndependent

end ConwayRefinement.Standalone.PrincipalRVAlgebraicIndependence
