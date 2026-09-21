/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.AtanasovRanganathanProgram
import LeanPool.BrillNoetherGraphs.LowGenus.AtanasovRanganathanExistence
import LeanPool.BrillNoetherGraphs.LowGenus.ClosedConstructionTail
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationBananaDoubleChip
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationBananaTail
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationChippedTriangle
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationCommon
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationEleven
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationFive
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedCommon
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedRow
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedThree
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedTripod
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationSeven
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationThree
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationThreeChain
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationTwo
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow096Pencil
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow097Closed
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow097Contractions
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow098Closed
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveClosedOrbit
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConfigurations
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConstructions
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveTwoPoleData
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveTwoPole
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveTwoPoleClosed
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCoreAtlas
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCubicAtlas
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCanonicalClassifier
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCubicCoverage
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveBridgeRows
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFivePseudocoreCoverage
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourCanonicalClassifier
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourCubicCoverage
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourPseudocoreCoverage
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRowsClosed
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow05
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow05Symmetry
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow06
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08ChamberOne
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08ChamberThree
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08ChamberTwo
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08Symmetry
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow09
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow10
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow10ChamberOne
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow10ChamberTwo
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow10Symmetry
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow11
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow12
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow12Tripod
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow12Guarding
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow14
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow15
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow16
import LeanPool.BrillNoetherGraphs.LowGenus.GuardingSet
import LeanPool.BrillNoetherGraphs.LowGenus.Highlights
import LeanPool.BrillNoetherGraphs.LowGenus.Infrastructure.CoreRelabelingClosed
import LeanPool.BrillNoetherGraphs.LowGenus.Infrastructure.TrivalentExpansionClosed
import LeanPool.BrillNoetherGraphs.LowGenus.LowGenusExistence

/-! # The Atanasov--Ranganathan low-genus formalization

Root module for the `LowGenus` library: the formalization of the
Atanasov--Ranganathan existence theorem in genera at most five. It builds on
the generic chip-firing, subdivision, and transmission theory of the
`Utilities` library.

Fifteen generated cover modules -- `GenusFiveRow03FixedCover`,
`GenusFiveRow14FixedCover`, the five-module row-04 chain and the eight-module
row-06 chain -- are not imported here. They are retained as independent
generated checks alongside the readable proofs used by the main library.

`GenusFiveClosedCover` supplies the affine-cover semantics for those generated
certificates and is outside the dependency closure of
`brillNoetherExistenceThroughFive`.

Add an import line above whenever a module is added under `LowGenus/`, or
`lake build LowGenus` will silently skip it. -/
