/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.AveragingUniform
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.BlockVarianceBound
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.FixedPhaseUniform
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.Polarize
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.ProbeMoment
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.Projection
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.RpowOpt
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.Scalar
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.ScalarBounds

/-! Supporting modules for Coarse-graining theory for elliptic equations. -/

@[expose] public section
