/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.BonnetMyers.Statement
public import LeanPool.PoincareGeometry.BonnetMyers.Construction
public import LeanPool.PoincareGeometry.BonnetMyers.Algebra
public import LeanPool.PoincareGeometry.BonnetMyers.IndexForm
public import LeanPool.PoincareGeometry.BonnetMyers.Comparison
public import LeanPool.PoincareGeometry.BonnetMyers.SecondVariation
public import LeanPool.PoincareGeometry.BonnetMyers.MetricConsequences
public import LeanPool.PoincareGeometry.BonnetMyers.ODE
public import LeanPool.PoincareGeometry.BonnetMyers.Geodesic
public import LeanPool.PoincareGeometry.BonnetMyers.Parallel
public import LeanPool.PoincareGeometry.BonnetMyers.Transport
public import LeanPool.PoincareGeometry.BonnetMyers.IntrinsicGeodesic
public import LeanPool.PoincareGeometry.BonnetMyers.IntrinsicAcceleration
public import LeanPool.PoincareGeometry.BonnetMyers.CurveConnection
public import LeanPool.PoincareGeometry.BonnetMyers.ChartGluing
public import LeanPool.PoincareGeometry.BonnetMyers.MetricParallel
public import LeanPool.PoincareGeometry.BonnetMyers.MetricVariable
public import LeanPool.PoincareGeometry.BonnetMyers.LocalEnergy
public import LeanPool.PoincareGeometry.BonnetMyers.GeodesicFlow
public import LeanPool.PoincareGeometry.BonnetMyers.GeodesicCutoff
public import LeanPool.PoincareGeometry.BonnetMyers.GeodesicFlowRegularity
public import LeanPool.PoincareGeometry.BonnetMyers.StrongNormalNeighborhood
public import LeanPool.PoincareGeometry.BonnetMyers.NormalNeighborhood
public import LeanPool.PoincareGeometry.BonnetMyers.GaussLemma
public import LeanPool.PoincareGeometry.BonnetMyers.GeodesicLength
public import LeanPool.PoincareGeometry.BonnetMyers.GlobalDistance
public import LeanPool.PoincareGeometry.BonnetMyers.MetricBridge
public import LeanPool.PoincareGeometry.BonnetMyers.LocalDistanceRealization
public import LeanPool.PoincareGeometry.BonnetMyers.LocalCompactness
public import LeanPool.PoincareGeometry.BonnetMyers.RiemannianHopfRinow
public import LeanPool.PoincareGeometry.BonnetMyers.RiemannianMinimizer
public import LeanPool.PoincareGeometry.BonnetMyers.SecondVariationGeometry
public import LeanPool.PoincareGeometry.BonnetMyers.CoordinateCurvature
public import LeanPool.PoincareGeometry.BonnetMyers.CoordinateSecondVariation
public import LeanPool.PoincareGeometry.BonnetMyers.BrokenVariation
public import LeanPool.PoincareGeometry.BonnetMyers.VariationIntegral
public import LeanPool.PoincareGeometry.BonnetMyers.BrokenVariationIntegral
public import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentRegularity
public import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentLog
public import LeanPool.PoincareGeometry.BonnetMyers.DistanceRegularity
public import LeanPool.PoincareGeometry.BonnetMyers.CornerRigidity
public import LeanPool.PoincareGeometry.BonnetMyers.NormalCornerRigidity
public import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentCorner
public import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentGluing
public import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentTwoSided
public import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentDense
public import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentSmooth
public import LeanPool.PoincareGeometry.BonnetMyers.LocalParallelNorm
public import LeanPool.PoincareGeometry.BonnetMyers.ParallelConnection
public import LeanPool.PoincareGeometry.BonnetMyers.GlobalParallel
public import LeanPool.PoincareGeometry.BonnetMyers.ParallelReflection
public import LeanPool.PoincareGeometry.BonnetMyers.TransportContinuation
public import LeanPool.PoincareGeometry.BonnetMyers.ParallelFieldContinuation
public import LeanPool.PoincareGeometry.BonnetMyers.GlobalParallelTransport
public import LeanPool.PoincareGeometry.BonnetMyers.ManifoldSineTest
public import LeanPool.PoincareGeometry.BonnetMyers.GeometricComparison
public import LeanPool.PoincareGeometry.BonnetMyers.CurvatureRegularity
public import LeanPool.PoincareGeometry.BonnetMyers.GeometricIndex
public import LeanPool.PoincareGeometry.BonnetMyers.GlobalIntrinsicGeodesic
public import LeanPool.PoincareGeometry.BonnetMyers.FiniteGeodesicCover
public import LeanPool.PoincareGeometry.BonnetMyers.GlobalParallelField
public import LeanPool.PoincareGeometry.BonnetMyers.MinimizingGeodesic
public import LeanPool.PoincareGeometry.BonnetMyers.GlobalSecondVariation
public import LeanPool.PoincareGeometry.BonnetMyers.GlobalIndexNonnegative
public import LeanPool.PoincareGeometry.BonnetMyers.Complete

/-!
# Independent Bonnet--Myers theorem

The target `BonnetMyersEntry.completeStatement` is proved by
`BonnetMyersEntry.completeStatement_proved`. The former upstream wrappers are
superseded.
-/

@[expose] public section
