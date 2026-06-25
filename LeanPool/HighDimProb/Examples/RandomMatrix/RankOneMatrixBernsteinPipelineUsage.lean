/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Examples.RandomMatrix.CenteredRankOneCovarianceAdapterUsage
import LeanPool.HighDimProb.Examples.RandomMatrix.CenteredSelfAdjointClosureUsage
import LeanPool.HighDimProb.Examples.RandomMatrix.GradientNormToOperatorBoundUsage
import LeanPool.HighDimProb.RandomMatrix.ConcentrationStatements

/-!
# Rank-one Matrix Bernstein pipeline usage example

This examples-only file composes the rank-one covariance, centering,
self-adjointness, operator-norm, and optimized Matrix Bernstein usage layers.
It does not prove independence, variance proxy bounds, Tropp/Lieb, Bernstein
CFC, or neural-network feature hypotheses.
-/

namespace HighDimProb.Examples.RandomMatrix.RankOneMatrixBernsteinPipelineUsage

open MeasureTheory
open HighDimProb.Examples.RandomMatrix.CenteredRankOneCovarianceAdapterUsage
open HighDimProb.Examples.RandomMatrix.CenteredSelfAdjointClosureUsage

noncomputable section

/-- The centered rank-one covariance family used as Matrix Bernstein summands. -/
def centeredRankOnePipelineSummands {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {I : Type*} {n : Nat}
    (X : I -> RandomRankOneVector Omega n) :
    I -> RandomMatrix Omega (n + 1) (n + 1) :=
  centeredRankOneCovarianceSummandFamily (P := P) X

/-- The pipeline summands are the core centered rank-one random-matrix family. -/
theorem centeredRankOnePipelineSummands_eq_centeredRankOneFamily {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {I : Type*} {n : Nat}
    (X : I -> RandomRankOneVector Omega n) :
    centeredRankOnePipelineSummands (P := P) X =
      centeredRankOneRandomMatrixFamily P X := by
  rfl

/-- Assumptions for the optimized Matrix Bernstein pipeline.

The first two fields are rank-one construction facts from vector-level
assumptions. The remaining fields are the Matrix Bernstein hypotheses that
still need to be supplied explicitly in the examples layer. -/
structure RankOneMatrixBernsteinPipelineAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {I : Type*} [Fintype I] {n : Nat}
    (X : I -> RandomRankOneVector Omega n)
    (R t sigmaSq : Real) : Prop where
  randomVector : forall i, IsRandomVector P (X i)
  coordinateMemLpTwo :
    forall i, forall j : Fin (n + 1),
      MemLpRealRandomVariable P (coord (X i) j) 2
  independentSelfAdjoint :
    IndependentSelfAdjointRandomMatrices P
      (centeredRankOnePipelineSummands (P := P) X)
  squareIntegrable :
    forall i,
      IntegrableRandomMatrix P
        (randomMatrixSquare (centeredRankOnePipelineSummands (P := P) X i))
  expIntegrable :
    forall i,
      IntegrableRandomMatrix P
        (matrixExpScaledFamily
          (centeredRankOnePipelineSummands (P := P) X)
          (bernsteinThetaChoice t sigmaSq R) i)
  traceExpIntegrable :
    IntegrableRealRandomVariable P
      (traceExpIntegrand
        (randomMatrixSum (centeredRankOnePipelineSummands (P := P) X))
        (bernsteinThetaChoice t sigmaSq R))
  operatorNormBound :
    PointwiseOperatorNormBound
      (centeredRankOnePipelineSummands (P := P) X) R
  sigmaPositive : 0 < sigmaSq
  radiusNonneg : 0 <= R
  deviationPositive : 0 < t
  varianceProxyNormBound :
    MatrixVarianceProxyNormBound P
      (centeredRankOnePipelineSummands (P := P) X) sigmaSq
  cfcPrimitive :
    forall i omega,
      bernsteinMatrixExpLeQuadraticStatement
        (centeredRankOnePipelineSummands (P := P) X i omega)
        (bernsteinThetaChoice t sigmaSq R) R
  troppPrimitive :
    troppMasterTraceMGFFiniteFamilyStatement
      (P := P)
      (centeredRankOnePipelineSummands (P := P) X)
      (bernsteinSecondMomentComparisonFamily P
        (centeredRankOnePipelineSummands (P := P) X)
        (bernsteinThetaChoice t sigmaSq R) R)
      (matrixVarianceProxy P
        (centeredRankOnePipelineSummands (P := P) X))
      (bernsteinThetaChoice t sigmaSq R) R

/-- The rank-one pipeline supplies the centered self-adjoint family predicate. -/
theorem centeredRankOnePipeline_centeredSelfAdjoint {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {I : Type*} {n : Nat}
    (X : I -> RandomRankOneVector Omega n)
    (hRandom : forall i, IsRandomVector P (X i))
    (hMemLp :
      forall i, forall j : Fin (n + 1),
        MemLpRealRandomVariable P (coord (X i) j) 2) :
    CenteredSelfAdjointRandomMatrixFamily P
      (centeredRankOnePipelineSummands (P := P) X) := by
  simpa [centeredRankOnePipelineSummands,
    centeredRankOneCovarianceSummandFamily] using
    (centeredRankOneRandomMatrix_centeredSelfAdjoint_of_memLp_two
      (P := P) (X := X) hRandom hMemLp)

/-- The rank-one pipeline supplies centered summand integrability. -/
theorem centeredRankOnePipeline_integrable {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {I : Type*} {n : Nat}
    (X : I -> RandomRankOneVector Omega n)
    (hMemLp :
      forall i, forall j : Fin (n + 1),
        MemLpRealRandomVariable P (coord (X i) j) 2)
    (i : I) :
    IntegrableRandomMatrix P
      (centeredRankOnePipelineSummands (P := P) X i) := by
  simpa [centeredRankOnePipelineSummands,
    centeredRankOneCovarianceSummandFamily] using
    (centeredRankOneRandomMatrix_integrable_of_memLp_two
      (P := P) (X := X i) (hMemLp i))

/-- Optimized Matrix Bernstein tail bound for the centered rank-one covariance
pipeline under explicit primitive assumptions. -/
theorem rankOnePipeline_quadraticForm_tail_optimized_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (X : I -> RandomRankOneVector Omega n)
    (R t sigmaSq : Real)
    (h : RankOneMatrixBernsteinPipelineAssumptions
      (P := P) X R t sigmaSq) :
    P (quadraticFormUpperTailEvent
        (randomMatrixSum (centeredRankOnePipelineSummands (P := P) X)) t) <=
      matrixBernsteinOptimizedScalarTailRHS (n + 1) R t sigmaSq := by
  simpa [matrixBernsteinOptimizedScalarTailRHS, Nat.cast_add, Nat.cast_one] using
    (matrixBernsteinQuadraticFormUpperTailOptimizedScalarRHSWithCoeff_under_primitives
      (centeredRankOnePipelineSummands (P := P) X) R t sigmaSq
      (centeredRankOnePipeline_centeredSelfAdjoint
        (P := P) X h.randomVector h.coordinateMemLpTwo)
      h.independentSelfAdjoint
      (centeredRankOnePipeline_integrable
        (P := P) X h.coordinateMemLpTwo)
      h.squareIntegrable h.expIntegrable h.traceExpIntegrable
      h.operatorNormBound h.sigmaPositive h.radiusNonneg
      h.deviationPositive h.varianceProxyNormBound h.cfcPrimitive
      h.troppPrimitive)

end

end HighDimProb.Examples.RandomMatrix.RankOneMatrixBernsteinPipelineUsage
