/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

import LeanPool.Schoenflies.Plane
import LeanPool.Schoenflies.Topology
import LeanPool.Schoenflies.UniformBound
import LeanPool.Schoenflies.Direction
import LeanPool.Schoenflies.Square
import LeanPool.Schoenflies.Bounded
import LeanPool.Schoenflies.SegmentCut
import LeanPool.Schoenflies.SegmentMeet
import LeanPool.Schoenflies.SegmentOrder
import LeanPool.Schoenflies.Subdivide
import LeanPool.Schoenflies.Overlay
import LeanPool.Schoenflies.OverlayGraph
import LeanPool.Schoenflies.Line
import LeanPool.Schoenflies.PolyPath
import LeanPool.Schoenflies.Polygonal
import LeanPool.Schoenflies.Curve
import LeanPool.Schoenflies.Subarc
import LeanPool.Schoenflies.Concatenate
import LeanPool.Schoenflies.TwoArcs
import LeanPool.Schoenflies.Graph.Walk
import LeanPool.Schoenflies.Graph.Degree
import LeanPool.Schoenflies.Graph.Cycle
import LeanPool.Schoenflies.Graph.TwoConnected
import LeanPool.Schoenflies.Graph.PathGraph
import LeanPool.Schoenflies.Graph.TwoPaths
import LeanPool.Schoenflies.Graph.Tree
import LeanPool.Schoenflies.Graph.Component
import LeanPool.Schoenflies.Graph.Ear
import LeanPool.Schoenflies.Graph.Drawing
import LeanPool.Schoenflies.Graph.OuterFace
import LeanPool.Schoenflies.Graph.CycleJordan
import LeanPool.Schoenflies.Compose
import LeanPool.Schoenflies.PolygonalCarrier
import LeanPool.Schoenflies.LocallyPolygonal
import LeanPool.Schoenflies.Graph.VertexSquares
import LeanPool.Schoenflies.PolyLocal
import LeanPool.Schoenflies.Accessible
import LeanPool.Schoenflies.Graph.Redrawing
import LeanPool.Schoenflies.Graph.RelativeEar
import LeanPool.Schoenflies.CrosscutCells
import LeanPool.Schoenflies.ModelCurve
import LeanPool.Schoenflies.CombinatorialInvariance
import LeanPool.Schoenflies.Strip
import LeanPool.Schoenflies.SquareMover
import LeanPool.Schoenflies.StripConstants
import LeanPool.Schoenflies.StripConnected
import LeanPool.Schoenflies.Parity
import LeanPool.Schoenflies.StripLocal
import LeanPool.Schoenflies.PolygonBridge
import LeanPool.Schoenflies.Graph.K33
import LeanPool.Schoenflies.PolygonalJordan
import LeanPool.Schoenflies.SimpleArc
import LeanPool.Schoenflies.ParitySplitting
import LeanPool.Schoenflies.PolygonalCrosscut
import LeanPool.Schoenflies.AlternatingCrosscuts
import LeanPool.Schoenflies.FaceCycles
import LeanPool.Schoenflies.Graph.K33Planar
import LeanPool.Schoenflies.Realization
import LeanPool.Schoenflies.Graph.K33Closed
import LeanPool.Schoenflies.FaceCyclesProof
import LeanPool.Schoenflies.PrePolygonSep
import LeanPool.Schoenflies.PrePolygonArc
import LeanPool.Schoenflies.FaceCyclesLand
import LeanPool.Schoenflies.Graph.K33Land
import LeanPool.Schoenflies.AccessibleJoin
import LeanPool.Schoenflies.CrosscutAtMostTwo
import LeanPool.Schoenflies.SkeletonLocal
import LeanPool.Schoenflies.SquareMesh
import LeanPool.Schoenflies.ArcComplementPrep
import LeanPool.Schoenflies.JordanSeparates
import LeanPool.Schoenflies.OuterChain
import LeanPool.Schoenflies.CrosscutExists
import LeanPool.Schoenflies.CrosscutEncloses
import LeanPool.Schoenflies.OuterChainClosed
import LeanPool.Schoenflies.ArcCollars
import LeanPool.Schoenflies.SkeletonSectors
import LeanPool.Schoenflies.SquareMeshConnected
import LeanPool.Schoenflies.ArcComplement
import LeanPool.Schoenflies.Jordan
import LeanPool.Schoenflies.GeneralCrosscut
import LeanPool.Schoenflies.SquareCycle
import LeanPool.Schoenflies.PolyArcRealize
import LeanPool.Schoenflies.JordanClosed
import LeanPool.Schoenflies.Inversion
import LeanPool.Schoenflies.SkeletonAccess
import LeanPool.Schoenflies.InitialPair
import LeanPool.Schoenflies.GeneratedStructure
import LeanPool.Schoenflies.BoundaryCycles
import LeanPool.Schoenflies.SquareMeshFixed
import LeanPool.Schoenflies.RefinementStars
import LeanPool.Schoenflies.InitialPairFixed
import LeanPool.Schoenflies.LocalGrid
import LeanPool.Schoenflies.BoundaryContinuity
import LeanPool.Schoenflies.Endgame
import LeanPool.Schoenflies.CellulationInvariants
import LeanPool.Schoenflies.BoundaryCyclesGenerated
import LeanPool.Schoenflies.LimitMap
import LeanPool.Schoenflies.BoundaryContinuity2
import LeanPool.Schoenflies.FiniteTransfer
import LeanPool.Schoenflies.FreshAccess
import LeanPool.Schoenflies.GridAttach
import LeanPool.Schoenflies.Windows
import LeanPool.Schoenflies.StageTransition
import LeanPool.Schoenflies.StageTower
import LeanPool.Schoenflies.RealizeSubdiv
import LeanPool.Schoenflies.RealizeSplit
import LeanPool.Schoenflies.InitialGenerated
import LeanPool.Schoenflies.InitialOuterCycle
import LeanPool.Schoenflies.InitialReverseTransfer
import LeanPool.Schoenflies.SquareMeshClosed
import LeanPool.Schoenflies.ArcMonotone
import LeanPool.Schoenflies.RealizeSubdivHomeo
import LeanPool.Schoenflies.CommonSubdivision
import LeanPool.Schoenflies.FiniteTransferTarget
import LeanPool.Schoenflies.FiniteTransferTargetMesh
import LeanPool.Schoenflies.TargetOverlay
import LeanPool.Schoenflies.FreshDenseSelection
import LeanPool.Schoenflies.QuantitativeStages
import LeanPool.Schoenflies.SourceOverlay
import LeanPool.Schoenflies.SourceAttachment
import LeanPool.Schoenflies.OverlayExtension
import LeanPool.Schoenflies.SourceJoining
import LeanPool.Schoenflies.QuantitativeForwardStages
import LeanPool.Schoenflies.QuantitativeRecursion
import LeanPool.Schoenflies.InteriorHomeomorphism
import LeanPool.Schoenflies.BoundaryAnchors
import LeanPool.Schoenflies.JordanSchoenflies
import LeanPool.Schoenflies.MatchedSplit

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
