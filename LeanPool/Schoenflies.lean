/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

module

public import LeanPool.Schoenflies.Plane
public import LeanPool.Schoenflies.Topology
public import LeanPool.Schoenflies.UniformBound
public import LeanPool.Schoenflies.Direction
public import LeanPool.Schoenflies.Square
public import LeanPool.Schoenflies.Bounded
public import LeanPool.Schoenflies.SegmentCut
public import LeanPool.Schoenflies.SegmentMeet
public import LeanPool.Schoenflies.SegmentOrder
public import LeanPool.Schoenflies.Subdivide
public import LeanPool.Schoenflies.Overlay
public import LeanPool.Schoenflies.OverlayGraph
public import LeanPool.Schoenflies.Line
public import LeanPool.Schoenflies.PolyPath
public import LeanPool.Schoenflies.Polygonal
public import LeanPool.Schoenflies.Curve
public import LeanPool.Schoenflies.Subarc
public import LeanPool.Schoenflies.Concatenate
public import LeanPool.Schoenflies.TwoArcs
public import LeanPool.Schoenflies.Graph.Walk
public import LeanPool.Schoenflies.Graph.Degree
public import LeanPool.Schoenflies.Graph.Cycle
public import LeanPool.Schoenflies.Graph.TwoConnected
public import LeanPool.Schoenflies.Graph.PathGraph
public import LeanPool.Schoenflies.Graph.TwoPaths
public import LeanPool.Schoenflies.Graph.Tree
public import LeanPool.Schoenflies.Graph.Component
public import LeanPool.Schoenflies.Graph.Ear
public import LeanPool.Schoenflies.Graph.Drawing
public import LeanPool.Schoenflies.Graph.OuterFace
public import LeanPool.Schoenflies.Graph.CycleJordan
public import LeanPool.Schoenflies.Compose
public import LeanPool.Schoenflies.PolygonalCarrier
public import LeanPool.Schoenflies.LocallyPolygonal
public import LeanPool.Schoenflies.Graph.VertexSquares
public import LeanPool.Schoenflies.PolyLocal
public import LeanPool.Schoenflies.Accessible
public import LeanPool.Schoenflies.Graph.Redrawing
public import LeanPool.Schoenflies.Graph.RelativeEar
public import LeanPool.Schoenflies.CrosscutCells
public import LeanPool.Schoenflies.ModelCurve
public import LeanPool.Schoenflies.CombinatorialInvariance
public import LeanPool.Schoenflies.Strip
public import LeanPool.Schoenflies.SquareMover
public import LeanPool.Schoenflies.StripConstants
public import LeanPool.Schoenflies.StripConnected
public import LeanPool.Schoenflies.Parity
public import LeanPool.Schoenflies.StripLocal
public import LeanPool.Schoenflies.PolygonBridge
public import LeanPool.Schoenflies.Graph.K33
public import LeanPool.Schoenflies.PolygonalJordan
public import LeanPool.Schoenflies.SimpleArc
public import LeanPool.Schoenflies.ParitySplitting
public import LeanPool.Schoenflies.PolygonalCrosscut
public import LeanPool.Schoenflies.AlternatingCrosscuts
public import LeanPool.Schoenflies.FaceCycles
public import LeanPool.Schoenflies.Graph.K33Planar
public import LeanPool.Schoenflies.Realization
public import LeanPool.Schoenflies.Graph.K33Closed
public import LeanPool.Schoenflies.FaceCyclesProof
public import LeanPool.Schoenflies.PrePolygonSep
public import LeanPool.Schoenflies.PrePolygonArc
public import LeanPool.Schoenflies.FaceCyclesLand
public import LeanPool.Schoenflies.Graph.K33Land
public import LeanPool.Schoenflies.AccessibleJoin
public import LeanPool.Schoenflies.CrosscutAtMostTwo
public import LeanPool.Schoenflies.SkeletonLocal
public import LeanPool.Schoenflies.SquareMesh
public import LeanPool.Schoenflies.ArcComplementPrep
public import LeanPool.Schoenflies.JordanSeparates
public import LeanPool.Schoenflies.OuterChain
public import LeanPool.Schoenflies.CrosscutExists
public import LeanPool.Schoenflies.CrosscutEncloses
public import LeanPool.Schoenflies.OuterChainClosed
public import LeanPool.Schoenflies.ArcCollars
public import LeanPool.Schoenflies.SkeletonSectors
public import LeanPool.Schoenflies.SquareMeshConnected
public import LeanPool.Schoenflies.ArcComplement
public import LeanPool.Schoenflies.Jordan
public import LeanPool.Schoenflies.GeneralCrosscut
public import LeanPool.Schoenflies.SquareCycle
public import LeanPool.Schoenflies.PolyArcRealize
public import LeanPool.Schoenflies.JordanClosed
public import LeanPool.Schoenflies.Inversion
public import LeanPool.Schoenflies.SkeletonAccess
public import LeanPool.Schoenflies.InitialPair
public import LeanPool.Schoenflies.GeneratedStructure
public import LeanPool.Schoenflies.BoundaryCycles
public import LeanPool.Schoenflies.SquareMeshFixed
public import LeanPool.Schoenflies.RefinementStars
public import LeanPool.Schoenflies.InitialPairFixed
public import LeanPool.Schoenflies.LocalGrid
public import LeanPool.Schoenflies.BoundaryContinuity
public import LeanPool.Schoenflies.Endgame
public import LeanPool.Schoenflies.CellulationInvariants
public import LeanPool.Schoenflies.BoundaryCyclesGenerated
public import LeanPool.Schoenflies.LimitMap
public import LeanPool.Schoenflies.BoundaryContinuity2
public import LeanPool.Schoenflies.FiniteTransfer
public import LeanPool.Schoenflies.FreshAccess
public import LeanPool.Schoenflies.GridAttach
public import LeanPool.Schoenflies.Windows
public import LeanPool.Schoenflies.StageTransition
public import LeanPool.Schoenflies.StageTower
public import LeanPool.Schoenflies.RealizeSubdiv
public import LeanPool.Schoenflies.RealizeSplit
public import LeanPool.Schoenflies.InitialGenerated
public import LeanPool.Schoenflies.InitialOuterCycle
public import LeanPool.Schoenflies.InitialReverseTransfer
public import LeanPool.Schoenflies.SquareMeshClosed
public import LeanPool.Schoenflies.ArcMonotone
public import LeanPool.Schoenflies.RealizeSubdivHomeo
public import LeanPool.Schoenflies.CommonSubdivision
public import LeanPool.Schoenflies.FiniteTransferTarget
public import LeanPool.Schoenflies.FiniteTransferTargetMesh
public import LeanPool.Schoenflies.TargetOverlay
public import LeanPool.Schoenflies.FreshDenseSelection
public import LeanPool.Schoenflies.QuantitativeStages
public import LeanPool.Schoenflies.SourceOverlay
public import LeanPool.Schoenflies.SourceAttachment
public import LeanPool.Schoenflies.OverlayExtension
public import LeanPool.Schoenflies.SourceJoining
public import LeanPool.Schoenflies.QuantitativeForwardStages
public import LeanPool.Schoenflies.QuantitativeRecursion
public import LeanPool.Schoenflies.InteriorHomeomorphism
public import LeanPool.Schoenflies.BoundaryAnchors
public import LeanPool.Schoenflies.JordanSchoenflies
public import LeanPool.Schoenflies.MatchedSplit

/-!
# Jordan–Schönflies theorem

Source: url:https://github.com/alonamaloh/schoenflies-lean
Authors: Álvaro Begué
Status: verified
Main declarations: `Schoenflies.jordan_schoenflies_of_homeomorph`
Tags: jordan-curve, schoenflies-theorem, geometric-topology, homeomorphism
MSC: 57K10, 54C25
-/

/-!
## Proof provenance

The pinned upstream `formalization.yaml` at commit
`05a43d29cde026618777db3d4e4316204ccca237` records that AI coding agents produced the Lean
formalization under Álvaro Begué's mathematical direction and integration. It credits him with
selecting the source, architecture, statement targets, and integration decisions. The registry
therefore classifies proof provenance as `AI` under Lean Pool's rubric; mathematical authorship
and direction remain credited to Begué.
-/
