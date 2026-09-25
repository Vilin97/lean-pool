/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.AffineAverage
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.AxisCube
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CenteredCubeCalderonZygmundQTwo
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH10
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1Dilation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1Translation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveMeanZero
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveSmooth
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeBesovPoincare
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCoerciveH1
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.DifferenceQuotient
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.DifferenceQuotientH1
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.EuclideanL2CZ
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H10Graph
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H1Graph
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Hodge
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.HodgeCubeBridge
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.MeanZero
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareLp
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareLpIntegral
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareLpKernel
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareLpSmooth
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareMeanZero
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareSegment
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareZeroTrace
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.QuantitativeCutoff
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.WeakHessianEuclidean
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.ZeroTraceAverages

/-! Supporting modules for Coarse-graining theory for elliptic equations. -/

@[expose] public section
