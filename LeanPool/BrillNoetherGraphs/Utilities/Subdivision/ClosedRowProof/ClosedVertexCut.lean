/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateCoreVertexCut
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedFaceCensus
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SpanningTreeConnectivity

/-!
# Closed-face vertex-cut adapter for row certificates

The generic degenerate vertex-cut theorem is stated for an arbitrary
`DegSpec` whose representative map is known to encode contraction by its zero
slots.  Canonical closed faces use `compFold`, so that extra hypothesis is
automatic.  This small adapter presents the result in the exact form consumed
by the deep-embedded closed-row checker.
-/

@[expose] public section

namespace Utilities.Subdivision.ClosedRowProof

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ClosedFaceCensus
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.DegenerateSpec

variable {n p : ℕ}

/-- A canonical census face identifies exactly the vertices joined by its
zero-length slots. -/
theorem repIsContraction_censusSpec (core : ExplicitPotential.Core n p)
    (hn : 0 < n) (length : Fin p → ℕ)
    (hForest : IsForest core (zeroSet length))
    (hNotLoopy : ¬ IsLoopy core (zeroSet length)) :
    (censusSpec core hn length hForest hNotLoopy).RepIsContraction :=
  fun u v h => (compFold_iff core (zeroSet length) u v).mp h

/-- A checked genus-four core cut supplies a degree-three pencil on every
genus-preserving canonical closed face. -/
theorem bnExists_censusSpec_of_genusFourRankOneCheck
    (core : ExplicitPotential.Core n p) (hn : 0 < n)
    (cut : CoreVertexCut.Data core)
    (tree : MarkedGraphs.Certificate.SpanningTreeConnectivity.Certificate core)
    (hLoopless : ∀ e : Fin p, core.tail e ≠ core.head e)
    (hCheck : cut.genusFourRankOneCheck tree = true)
    (length : Fin p → ℕ) (hForest : IsForest core (zeroSet length))
    (hNotLoopy : ¬ IsLoopy core (zeroSet length)) :
    BNExists (censusSpec core hn length hForest hNotLoopy).graph 1 3 :=
  Utilities.Certificate.DegenerateCoreVertexCut.bnExists_one_three_of_genusFourRankOneCheck
    (censusSpec core hn length hForest hNotLoopy) cut tree
    (repIsContraction_censusSpec core hn length hForest hNotLoopy)
    hLoopless hCheck

end Utilities.Subdivision.ClosedRowProof
