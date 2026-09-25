/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.BoundaryLayer
public import LeanPool.CoarseGraining.Homogenization.Geometry.BoundedConvexDomain
public import LeanPool.CoarseGraining.Homogenization.Geometry.BoundedMeasurableDomain
public import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
public import LeanPool.CoarseGraining.Homogenization.Geometry.CubeColoring
public import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
public import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMetric
public import LeanPool.CoarseGraining.Homogenization.Geometry.Domain
public import LeanPool.CoarseGraining.Homogenization.Geometry.OriginCubeBoundaryPush
public import LeanPool.CoarseGraining.Homogenization.Geometry.OriginCubeMeasureBridge
public import LeanPool.CoarseGraining.Homogenization.Geometry.OverlapCenters
public import LeanPool.CoarseGraining.Homogenization.Geometry.OverlapCube
public import LeanPool.CoarseGraining.Homogenization.Geometry.ScaleColoring
public import LeanPool.CoarseGraining.Homogenization.Geometry.SignedPermutation
public import LeanPool.CoarseGraining.Homogenization.Geometry.Translation
public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCube
public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation
public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicPartition

/-! Supporting modules for Coarse-graining theory for elliptic equations. -/

@[expose] public section
