/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Examples.OmegaOmegaBoundary

/-! # Omega Omega Boundary Proof -/

public noncomputable section

namespace ConwayRefinement.Standalone.Oz.OmegaOmegaBoundaryExample.ExistsAtBoundary

/-- The coefficient-one boundary normal form supplies the example. -/
theorem proof : OmegaOmegaBoundaryExample.ExistsAtBoundary := by
  rw [OmegaOmegaBoundaryExample.ExistsAtBoundary]
  refine ⟨OmegaOmegaBoundary.boundaryOz, ?_, ?_, ?_, ?_⟩
  · simpa only [OmegaOmegaBoundaryExample.IsOrdinary, Oz.IsOrdinaryInteger] using
      OmegaOmegaBoundary.boundaryOz_not_isOrdinaryInteger
  · simpa only [OmegaOmegaBoundaryExample.IsReduced, Oz.IsReduced] using
      OmegaOmegaBoundary.boundaryOz_isReduced
  · exact OmegaOmegaBoundary.boundaryOz_length
  · simpa only [OmegaOmegaBoundaryExample.HasFiniteDegree, Oz.HasFiniteDegree] using
      OmegaOmegaBoundary.boundaryOz_not_hasFiniteDegree

end ConwayRefinement.Standalone.Oz.OmegaOmegaBoundaryExample.ExistsAtBoundary
