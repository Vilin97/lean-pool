/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.AdjointSymmetry
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockFormalism
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockMatrixProperties
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CoarseBounds
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CubeMinimizer
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Definitions
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.HilbertMinimization
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.HilbertMinimizationMeasurability
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuAdmissibility
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuQuadratic
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecoveryBlockResponse
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuWellPosedness
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeOpenBridge
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeSymmetry
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.QuadraticStability
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.SharpBlockBounds
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Subadditivity
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Symmetric
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ThetaEllipticity
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Translation

/-! Supporting modules for Coarse-graining theory for elliptic equations. -/

@[expose] public section
