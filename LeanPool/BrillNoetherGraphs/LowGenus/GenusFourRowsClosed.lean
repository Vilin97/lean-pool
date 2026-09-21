/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.Generated.GenusFourClosedRows
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourCubicCoverage
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow095Closed
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow097Closed
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow098Closed

/-!
# The six closed cubic genus-four rows

This is the small concrete ledger consumed by the public genus-four
pseudocore reduction.  Rows 095, 097, and 098 have readable structural
closed-face proofs.  Rows 096, 099, and 100 use kernel-checked generated
certificates for the boundary faces; row 096 additionally has a readable
symbolic proof on the positive orthant.
-/
namespace AtanasovRanganathan.GenusFourRowsClosed

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open AtanasovRanganathan.Configurations
open AtanasovRanganathan.GenusFourCubicAtlas
open AtanasovRanganathan.GenusFourCubicCoverage

/-- All six public cubic genus-four rows carry degree-three pencils throughout
their genus-preserving closed orthants. -/
theorem rowClosedCoverage : RowClosedCoverage := by
  intro row hRow length hForest hNotLoopy
  simp only [atlas, List.mem_cons, List.not_mem_nil, or_false] at hRow
  rcases hRow with rfl | rfl | rfl | rfl | rfl | rfl
  · exact GenusFourRow095Closed.row095_closed length hForest hNotLoopy
  · exact GenusFourGeneratedRows.row096_closed length hForest hNotLoopy
  · rw [faceSpec_eq_censusSpec]
    exact LowGenus.GenusFourRow097Closed.bnExists_closed
      length hForest hNotLoopy
  · exact GenusFourRow098Closed.bnExists_closed length hForest hNotLoopy
  · exact GenusFourGeneratedRows.row099_closed length hForest hNotLoopy
  · exact GenusFourGeneratedRows.row100_closed length hForest hNotLoopy

/-- The public classifier and the six-row ledger cover every connected
loopless cubic genus-four core. -/
theorem cubicClosedCoverage :
    GenusFourPseudocoreCoverage.CubicClosedCoverage :=
  cubicClosedCoverage_of_rows rowClosedCoverage

/-- Every connected finite graph of genus four carries a degree-three
rank-one divisor, using only public modules. -/
theorem genusFourRankOneExistence : GenusFourRankOneExistence :=
  GenusFourPseudocoreCoverage.genusFourRankOneExistence_of_cubicClosedCoverage
    cubicClosedCoverage

end AtanasovRanganathan.GenusFourRowsClosed
