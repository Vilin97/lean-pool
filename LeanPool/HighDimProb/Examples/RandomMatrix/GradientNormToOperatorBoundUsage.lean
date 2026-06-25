/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Examples.RandomMatrix.GradientCovarianceUsage
import LeanPool.HighDimProb.Examples.RandomMatrix.RankOnePSDUsage

/-!
# Gradient norm to operator-bound usage example

This examples-only file records the intended bridge from gradient norm bounds
to Matrix Bernstein operator-norm assumptions for rank-one covariance
summands. The uncentered rank-one bridge now follows from the named
`rankOneRandomMatrix` operator-norm API. The centered bridge follows from the
named centered rank-one operator-norm API, so this example does not rederive
the expectation-contraction route locally.
-/

namespace HighDimProb.Examples.RandomMatrix.GradientNormToOperatorBoundUsage

open MeasureTheory
open scoped BigOperators
open HighDimProb.Examples.RandomMatrix.GradientCovarianceUsage
open HighDimProb.Examples.RandomMatrix.RankOnePSDUsage

noncomputable section

/-- Squared Euclidean norm of a finite gradient vector. -/
def gradientSqNorm {n : Nat} (g : GradientVector n) : Real :=
  Finset.univ.sum fun i : Fin (n + 1) => g i ^ 2

@[simp]
theorem gradientSqNorm_apply {n : Nat} (g : GradientVector n) :
    gradientSqNorm g =
      Finset.univ.sum fun i : Fin (n + 1) => g i ^ 2 := by
  rfl

/-- Squared gradient norm is nonnegative. -/
theorem gradientSqNorm_nonneg {n : Nat} (g : GradientVector n) :
    0 <= gradientSqNorm g := by
  unfold gradientSqNorm
  exact Finset.sum_nonneg fun i _hi => sq_nonneg (g i)

/-- The example-local gradient norm is the core squared-vector norm. -/
theorem gradientSqNorm_eq_vectorSqNorm {n : Nat} (g : GradientVector n) :
    gradientSqNorm g = vectorSqNorm g := by
  rfl

/-- A pointwise squared-gradient-norm bound for a random gradient table. -/
def GradientSqNormBound {Omega : Type*}
    {batch n : Nat} (G : RandomGradientTable Omega batch n) (R : Real) :
    Prop :=
  forall b omega, gradientSqNorm (G omega b) <= R

/-- Example-local bridge from a squared-gradient-norm bound to an operator-norm
bound on uncentered rank-one covariance contributions. -/
structure RankOneGradientOperatorNormBridge {Omega : Type*}
    [MeasurableSpace Omega] {batch n : Nat}
    (G : RandomGradientTable Omega batch n) (R : Real) : Prop where
  gradientSqNormBound : GradientSqNormBound G R

/-- The uncentered bridge supplies the Matrix Bernstein pointwise
operator-norm predicate for the uncentered rank-one family. -/
theorem uncenteredGradientCovariance_pointwiseOperatorNormBound
    {Omega : Type*} [MeasurableSpace Omega] {batch n : Nat}
    (G : RandomGradientTable Omega batch n) (R : Real)
    (h : RankOneGradientOperatorNormBridge G R) :
    PointwiseOperatorNormBound
      (randomGradientCovarianceContributionFamily G) R := by
  have hRankOne :
      PointwiseOperatorNormBound
        (rankOneRandomMatrixFamily (randomGradientVectorFamily G)) R :=
    PointwiseOperatorNormBound_rankOneRandomMatrix_of_sqNorm_bound
      (randomGradientVectorFamily G) R
      (by
        intro b omega
        simpa [gradientSqNorm_eq_vectorSqNorm] using
          h.gradientSqNormBound b omega)
  simpa [randomGradientCovarianceContributionFamily,
    randomGradientCovarianceContribution, randomGradientVector,
    gradientCovarianceContribution, gradientOuter, rankOneRandomMatrix,
    rankOneMatrix] using hRankOne

/-- Example-local bridge from gradient norm control to the centered summand
operator-norm bound used by the Matrix Bernstein examples.

This uses the public centered rank-one operator-norm adapter. The extra
random-vector and second-moment fields are exactly the hypotheses needed by
the core expectation-contraction step. -/
structure CenteredGradientCovarianceOperatorNormAdapter {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {batch n : Nat}
    (G : RandomGradientTable Omega batch n)
    (A : Fin batch -> RandomMatrix Omega (n + 1) (n + 1))
    (R : Real) : Prop where
  centeredAdapter : IsCenteredGradientCovarianceSummandFamily (P := P) G A
  randomVector :
    forall b, IsRandomVector P (randomGradientVectorFamily G b)
  coordinateMemLpTwo :
    forall b, forall j : Fin (n + 1),
      MemLpRealRandomVariable P (coord (randomGradientVectorFamily G b) j) 2
  gradientSqNormBound : GradientSqNormBound G R
  radiusNonneg : 0 <= R

/-- The centered adapter supplies the exact `PointwiseOperatorNormBound`
assumption consumed by the gradient covariance Matrix Bernstein examples. -/
theorem centeredGradientCovariance_pointwiseOperatorNormBound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {batch n : Nat}
    (G : RandomGradientTable Omega batch n)
    (A : Fin batch -> RandomMatrix Omega (n + 1) (n + 1))
    (R : Real)
    (h : CenteredGradientCovarianceOperatorNormAdapter (P := P) G A R) :
    PointwiseOperatorNormBound A (2 * R) := by
  have hSq :
      forall b omega,
        vectorSqNorm (randomGradientVectorFamily G b omega) <= R := by
    intro b omega
    simpa [randomGradientVectorFamily, randomGradientVector,
      gradientSqNorm_eq_vectorSqNorm] using h.gradientSqNormBound b omega
  have hCentered :
      PointwiseOperatorNormBound
        (centeredRankOneRandomMatrixFamily P (randomGradientVectorFamily G))
        (2 * R) :=
    PointwiseOperatorNormBound_centeredRankOneRandomMatrix_of_sqNorm_bound
      (P := P) (X := randomGradientVectorFamily G) (R := R)
      h.randomVector h.coordinateMemLpTwo hSq h.radiusNonneg
  rw [h.centeredAdapter]
  simpa [centeredGradientCovarianceSummands] using hCentered

/-- Rank-one gradient covariance contributions are structurally PSD; the
operator-norm part is separate from this PSD fact. -/
theorem gradientCovarianceContribution_structural_psd {batch n : Nat}
    (G : GradientTable batch n) (b : Fin batch) :
    IsPSDMatrix (gradientCovarianceContribution G b) := by
  exact gradientCovarianceContribution_psd G b

end

end HighDimProb.Examples.RandomMatrix.GradientNormToOperatorBoundUsage
