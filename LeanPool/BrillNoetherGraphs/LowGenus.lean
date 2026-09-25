/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.AtanasovRanganathanProgram
public import LeanPool.BrillNoetherGraphs.LowGenus.AtanasovRanganathanExistence
public import LeanPool.BrillNoetherGraphs.LowGenus.ClosedConstructionTail
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationBananaDoubleChip
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationBananaTail
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationChippedTriangle
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationCommon
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationEleven
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationFive
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedCommon
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedRow
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedThree
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedTripod
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationSeven
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationThree
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationThreeChain
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationTwo
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow096Pencil
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow097Closed
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow097Contractions
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow098Closed
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveClosedOrbit
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConfigurations
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConstructions
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveTwoPoleData
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveTwoPole
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveTwoPoleClosed
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCoreAtlas
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCubicAtlas
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCanonicalClassifier
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCubicCoverage
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveBridgeRows
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFivePseudocoreCoverage
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourCanonicalClassifier
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourCubicCoverage
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourPseudocoreCoverage
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRowsClosed
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow05
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow05Symmetry
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow06
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08ChamberOne
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08ChamberThree
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08ChamberTwo
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08Symmetry
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow09
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow10
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow10ChamberOne
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow10ChamberTwo
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow10Symmetry
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow11
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow12
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow12Tripod
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow12Guarding
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow14
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow15
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow16
public import LeanPool.BrillNoetherGraphs.LowGenus.GuardingSet
public import LeanPool.BrillNoetherGraphs.LowGenus.Highlights
public import LeanPool.BrillNoetherGraphs.LowGenus.Infrastructure.CoreRelabelingClosed
public import LeanPool.BrillNoetherGraphs.LowGenus.Infrastructure.TrivalentExpansionClosed
public import LeanPool.BrillNoetherGraphs.LowGenus.LowGenusExistence

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

@[expose] public section
