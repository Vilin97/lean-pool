/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Examples.RandomMatrix.RankOnePSDUsage
import LeanPool.HighDimProb.RandomMatrix.VarianceProxy

/-!
# Centered rank-one covariance adapter usage example

This examples-only file shows how an uncentered rank-one covariance
contribution can be converted into a centered random matrix summand
`X - E[X]` using the existing entrywise `matrixExpect` API.

It proves the expectation-zero property from existing matrix expectation
lemmas. The uncentered and centered rank-one contributions now reuse the named
`rankOneRandomMatrix`, `rankOneRandomMatrixFamily`,
`centeredRankOneRandomMatrix`, and `centeredRankOneRandomMatrixFamily` APIs, so
vector-level measurability and second-moment hypotheses supply the matrix-level
structural predicates.
-/

namespace HighDimProb.Examples.RandomMatrix.CenteredRankOneCovarianceAdapterUsage

open MeasureTheory
open HighDimProb.Examples.RandomMatrix.RankOnePSDUsage

noncomputable section

/-- A random vector used to form a rank-one covariance contribution. -/
abbrev RandomRankOneVector (Omega : Type*) (n : Nat) :=
  Omega -> RankOneVector n

/-- Uncentered rank-one covariance contribution `x x^T`. -/
def rankOneCovarianceContribution {Omega : Type*}
    {n : Nat} (X : RandomRankOneVector Omega n) :
    RandomMatrix Omega (n + 1) (n + 1) :=
  rankOneRandomMatrix X

/-- A finite family of uncentered rank-one covariance contributions. -/
def rankOneCovarianceContributionFamily {Omega : Type*}
    {I : Type*} {n : Nat}
    (X : I -> RandomRankOneVector Omega n) :
    I -> RandomMatrix Omega (n + 1) (n + 1) :=
  rankOneRandomMatrixFamily X

@[simp]
theorem rankOneCovarianceContributionFamily_apply {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} {n : Nat}
    (X : I -> RandomRankOneVector Omega n) (i : I) :
    rankOneCovarianceContributionFamily X i =
      rankOneCovarianceContribution (X i) := by
  rfl

@[simp]
theorem rankOneCovarianceContribution_apply {Omega : Type*}
    [MeasurableSpace Omega] {n : Nat} (X : RandomRankOneVector Omega n)
    (omega : Omega) (i j : Fin (n + 1)) :
    rankOneCovarianceContribution X omega i j = X omega i * X omega j := by
  rfl

/-- Centered rank-one covariance summand `X X^T - E[X X^T]`. -/
def centeredRankOneCovarianceSummand {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} (X : RandomRankOneVector Omega n) :
    RandomMatrix Omega (n + 1) (n + 1) :=
  centeredRankOneRandomMatrix P X

@[simp]
theorem centeredRankOneCovarianceSummand_apply {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (X : RandomRankOneVector Omega n) (omega : Omega)
    (i j : Fin (n + 1)) :
    centeredRankOneCovarianceSummand (P := P) X omega i j =
      X omega i * X omega j -
        matrixExpect P (rankOneCovarianceContribution X) i j := by
  rfl

/-- The uncentered rank-one contribution is pointwise self-adjoint. -/
theorem rankOneCovarianceContribution_selfAdjoint {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (X : RandomRankOneVector Omega n) :
    RandomSelfAdjointMatrix P (rankOneCovarianceContribution X) := by
  simpa [rankOneCovarianceContribution] using
    (randomSelfAdjointMatrix_rankOneRandomMatrix (P := P) (X := X))

/-- The uncentered rank-one contribution is pointwise PSD. -/
theorem rankOneCovarianceContribution_psd {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (X : RandomRankOneVector Omega n) :
    RandomPSDMatrix P (rankOneCovarianceContribution X) := by
  simpa [rankOneCovarianceContribution] using
    (randomPSDMatrix_rankOneRandomMatrix (P := P) (X := X))

/-- Vector measurability gives entrywise random-matrix measurability for the
uncentered rank-one covariance contribution. -/
theorem isRandomMatrix_rankOneCovarianceContribution {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    {X : RandomRankOneVector Omega n}
    (hX : IsRandomVector P X) :
    IsRandomMatrix P (rankOneCovarianceContribution X) := by
  simpa [rankOneCovarianceContribution] using
    (isRandomMatrix_rankOneRandomMatrix (P := P) (X := X) hX)

/-- Coordinate second moments give entrywise integrability of the uncentered
rank-one covariance contribution. -/
theorem integrable_rankOneCovarianceContribution_of_memLp_two {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    {X : RandomRankOneVector Omega n}
    (hX : forall j : Fin (n + 1),
      MemLpRealRandomVariable P (coord X j) 2) :
    IntegrableRandomMatrix P (rankOneCovarianceContribution X) := by
  simpa [rankOneCovarianceContribution] using
    (integrableRandomMatrix_rankOneRandomMatrix_of_memLp_two
      (P := P) (X := X) hX)

/-- Entrywise integrability of the uncentered rank-one contribution gives
entrywise integrability of its centered version. -/
theorem integrable_centeredRankOneCovarianceSummand {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsFiniteMeasure P]
    {n : Nat} {X : RandomRankOneVector Omega n}
    (hInt : IntegrableRandomMatrix P (rankOneCovarianceContribution X)) :
    IntegrableRandomMatrix P (centeredRankOneCovarianceSummand (P := P) X) := by
  have hRank : IntegrableRandomMatrix P (rankOneRandomMatrix X) := by
    simpa [rankOneCovarianceContribution] using hInt
  simpa [centeredRankOneCovarianceSummand, centeredRankOneRandomMatrix] using
    (integrableRandomMatrix_centeredRandomMatrix
      (P := P) (A := rankOneRandomMatrix X) hRank)

/-- Centering by entrywise matrix expectation gives zero entrywise expectation. -/
theorem matrixExpect_centeredRankOneCovarianceSummand {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {n : Nat} {X : RandomRankOneVector Omega n}
    (hInt : IntegrableRandomMatrix P (rankOneCovarianceContribution X)) :
    matrixExpect P (centeredRankOneCovarianceSummand (P := P) X) = 0 := by
  have hRank : IntegrableRandomMatrix P (rankOneRandomMatrix X) := by
    simpa [rankOneCovarianceContribution] using hInt
  simpa [centeredRankOneCovarianceSummand, centeredRankOneRandomMatrix] using
    (matrixExpect_centeredRandomMatrix
      (P := P) (A := rankOneRandomMatrix X) hRank)

/-- A finite family of centered rank-one covariance summands. -/
def centeredRankOneCovarianceSummandFamily {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {I : Type*}
    {n : Nat} (X : I -> RandomRankOneVector Omega n) :
    I -> RandomMatrix Omega (n + 1) (n + 1) :=
  centeredRankOneRandomMatrixFamily P X

@[simp]
theorem centeredRankOneCovarianceSummandFamily_apply {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {I : Type*}
    {n : Nat} (X : I -> RandomRankOneVector Omega n) (i : I) :
    centeredRankOneCovarianceSummandFamily (P := P) X i =
      centeredRankOneCovarianceSummand (P := P) (X i) := by
  rfl

/-- Local assumptions needed to expose the centered rank-one family through
the Matrix Bernstein centered self-adjoint predicate. -/
structure CenteredRankOneCovarianceMatrixAdapter {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {I : Type*} {n : Nat}
    (X : I -> RandomRankOneVector Omega n) : Prop where
  randomVector : forall i, IsRandomVector P (X i)
  coordinateMemLpTwo :
    forall i, forall j : Fin (n + 1),
      MemLpRealRandomVariable P (coord (X i) j) 2

/-- The centered rank-one covariance adapter supplies the centered
self-adjoint family predicate used by Matrix Bernstein. -/
theorem centeredRankOneCovariance_family_centeredSelfAdjoint
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} {n : Nat}
    (X : I -> RandomRankOneVector Omega n)
    (h : CenteredRankOneCovarianceMatrixAdapter (P := P) X) :
    CenteredSelfAdjointRandomMatrixFamily P
      (centeredRankOneCovarianceSummandFamily (P := P) X) := by
  simpa [centeredRankOneCovarianceSummandFamily] using
    (centeredRankOneRandomMatrix_centeredSelfAdjoint_of_memLp_two
      (P := P) (X := X) h.randomVector h.coordinateMemLpTwo)

end

end HighDimProb.Examples.RandomMatrix.CenteredRankOneCovarianceAdapterUsage
