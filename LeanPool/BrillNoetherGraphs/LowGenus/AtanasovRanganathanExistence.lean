/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveBridgeRows
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFivePseudocoreCoverage
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRowsClosed

/-!
# Brill--Noether existence through genus five

The complete Atanasov--Ranganathan theorem is assembled here entirely inside
the public `LowGenus` library.  Genus four reduces to six closed cubic rows.
Genus five reduces to the sixteen constructions from the source paper and
four bridge rows, all handled by one checked `(2,3)` articulation theorem.
Semantic loops in either genus are discharged uniformly after fossilization
by splitting off a rigid genus-one wedge factor.
-/
namespace AtanasovRanganathan

open Utilities

/-- Every connected finite graph of genus four carries a degree-three
rank-one divisor. -/
theorem genusFourRankOneExistence : GenusFourRankOneExistence :=
  GenusFourRowsClosed.genusFourRankOneExistence

/-- **Atanasov--Ranganathan existence through genus five.**  Every connected
finite graph of genus at most five satisfies Brill--Noether existence. -/
theorem brillNoetherExistenceThroughFive : BrillNoetherExistenceThroughFive :=
  GenusFivePseudocoreCoverage.brillNoetherExistenceThroughFive_of_bridgeCoverage
    genusFourRankOneExistence
    (GenusFiveBridgeRows.bridgeAtlasClosedCoverage genusFourRankOneExistence)

end AtanasovRanganathan
