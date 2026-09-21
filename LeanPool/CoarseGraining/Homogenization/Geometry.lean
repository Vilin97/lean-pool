/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.BoundaryLayer
import LeanPool.CoarseGraining.Homogenization.Geometry.BoundedConvexDomain
import LeanPool.CoarseGraining.Homogenization.Geometry.BoundedMeasurableDomain
import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
import LeanPool.CoarseGraining.Homogenization.Geometry.CubeColoring
import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMetric
import LeanPool.CoarseGraining.Homogenization.Geometry.Domain
import LeanPool.CoarseGraining.Homogenization.Geometry.OriginCubeBoundaryPush
import LeanPool.CoarseGraining.Homogenization.Geometry.OriginCubeMeasureBridge
import LeanPool.CoarseGraining.Homogenization.Geometry.OverlapCenters
import LeanPool.CoarseGraining.Homogenization.Geometry.OverlapCube
import LeanPool.CoarseGraining.Homogenization.Geometry.ScaleColoring
import LeanPool.CoarseGraining.Homogenization.Geometry.SignedPermutation
import LeanPool.CoarseGraining.Homogenization.Geometry.Translation
import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCube
import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation
import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicPartition

/-! Supporting modules for Coarse-graining theory for elliptic equations. -/
