/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.ConcentrationStatements

/-!
# Gradient covariance concentration usage example

This examples-only file shows how empirical gradient covariance and empirical
Fisher style matrices can be connected to the existing RandomMatrix Matrix
Bernstein API. It does not prove neural-network gradient hypotheses, SGD
dynamics, boundedness, independence, or the Tropp/Bernstein primitive
assumptions.
-/

namespace HighDimProb.Examples.RandomMatrix.GradientCovarianceUsage

open MeasureTheory

noncomputable section

/-! ## Deterministic gradient covariance vocabulary -/

/-- A gradient vector in a finite parameter/subspace dimension of size `n + 1`. -/
abbrev GradientVector (n : Nat) :=
  Fin (n + 1) -> Real

/-- Rank-one gradient covariance contribution `g g^T`. -/
def gradientOuter {n : Nat} (g : GradientVector n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  rankOneMatrix g

@[simp]
theorem gradientOuter_apply {n : Nat} (g : GradientVector n)
    (i j : Fin (n + 1)) :
    gradientOuter g i j = g i * g j := by
  rfl

/-- A finite table of gradient vectors, indexed by a batch/sample coordinate. -/
abbrev GradientTable (batch n : Nat) :=
  Fin batch -> GradientVector n

/-- One rank-one empirical gradient covariance contribution. -/
def gradientCovarianceContribution {batch n : Nat}
    (G : GradientTable batch n) (b : Fin batch) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  gradientOuter (G b)

@[simp]
theorem gradientCovarianceContribution_apply {batch n : Nat}
    (G : GradientTable batch n) (b : Fin batch)
    (i j : Fin (n + 1)) :
    gradientCovarianceContribution G b i j = G b i * G b j := by
  rfl

/-- Empirical gradient covariance matrix as a sum of rank-one contributions. -/
def empiricalGradientCovariance {batch n : Nat}
    (G : GradientTable batch n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  Finset.univ.sum fun b : Fin batch => gradientCovarianceContribution G b

/-- Optional batch-normalized empirical gradient covariance matrix. -/
def normalizedEmpiricalGradientCovariance {batch n : Nat}
    (G : GradientTable batch n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  SMul.smul (1 / (batch : Real)) (empiricalGradientCovariance G)

/-- The empirical gradient covariance is definitionally the sum of rank-one terms. -/
theorem empiricalGradientCovariance_eq_sum_rankOne {batch n : Nat}
    (G : GradientTable batch n) :
    empiricalGradientCovariance G =
      Finset.univ.sum fun b : Fin batch => gradientCovarianceContribution G b := by
  rfl

@[simp]
theorem empiricalGradientCovariance_apply {batch n : Nat}
    (G : GradientTable batch n) (i j : Fin (n + 1)) :
    empiricalGradientCovariance G i j =
      Finset.univ.sum fun b : Fin batch => G b i * G b j := by
  simpa [empiricalGradientCovariance, gradientCovarianceContribution,
    gradientOuter] using
    (Matrix.sum_apply i j Finset.univ
      (fun b : Fin batch => gradientCovarianceContribution G b))

@[simp]
theorem normalizedEmpiricalGradientCovariance_apply {batch n : Nat}
    (G : GradientTable batch n) (i j : Fin (n + 1)) :
    normalizedEmpiricalGradientCovariance G i j =
      (1 / (batch : Real)) *
        Finset.univ.sum fun b : Fin batch => G b i * G b j := by
  rw [normalizedEmpiricalGradientCovariance]
  change (1 / (batch : Real)) * empiricalGradientCovariance G i j = _
  rw [empiricalGradientCovariance_apply]

/-! ## Random gradient table and centered summand adapter -/

/-- A random finite table of gradient vectors. -/
abbrev RandomGradientTable (Omega : Type*)
    (batch n : Nat) :=
  Omega -> GradientTable batch n

/-- The random gradient vector associated with one batch/sample coordinate. -/
def randomGradientVector {Omega : Type*}
    {batch n : Nat} (G : RandomGradientTable Omega batch n) (b : Fin batch) :
    Omega -> GradientVector n :=
  fun omega => G omega b

@[simp]
theorem randomGradientVector_apply {Omega : Type*} [MeasurableSpace Omega]
    {batch n : Nat} (G : RandomGradientTable Omega batch n)
    (b : Fin batch) (omega : Omega) (i : Fin (n + 1)) :
    randomGradientVector G b omega i = G omega b i := by
  rfl

/-- Family of random gradient vectors indexed by the batch/sample coordinate. -/
def randomGradientVectorFamily {Omega : Type*}
    {batch n : Nat} (G : RandomGradientTable Omega batch n) :
    Fin batch -> RandomVector Omega (n + 1) :=
  randomGradientVector G

@[simp]
theorem randomGradientVectorFamily_apply {Omega : Type*} [MeasurableSpace Omega]
    {batch n : Nat} (G : RandomGradientTable Omega batch n) (b : Fin batch) :
    randomGradientVectorFamily G b = randomGradientVector G b := by
  rfl

/-- Random rank-one gradient covariance contribution from one batch coordinate. -/
def randomGradientCovarianceContribution {Omega : Type*}
    {batch n : Nat}
    (G : RandomGradientTable Omega batch n) (b : Fin batch) :
    RandomMatrix Omega (n + 1) (n + 1) :=
  rankOneRandomMatrix (randomGradientVector G b)

@[simp]
theorem randomGradientCovarianceContribution_apply {Omega : Type*}
    [MeasurableSpace Omega] {batch n : Nat}
    (G : RandomGradientTable Omega batch n) (b : Fin batch)
    (omega : Omega) (i j : Fin (n + 1)) :
    randomGradientCovarianceContribution G b omega i j =
      G omega b i * G omega b j := by
  rfl

/-- The uncentered family of rank-one gradient covariance contributions. -/
def randomGradientCovarianceContributionFamily {Omega : Type*}
    {batch n : Nat}
    (G : RandomGradientTable Omega batch n) :
    Fin batch -> RandomMatrix Omega (n + 1) (n + 1) :=
  rankOneRandomMatrixFamily (randomGradientVectorFamily G)

@[simp]
theorem randomGradientCovarianceContributionFamily_apply {Omega : Type*}
    [MeasurableSpace Omega] {batch n : Nat}
    (G : RandomGradientTable Omega batch n) (b : Fin batch) :
    randomGradientCovarianceContributionFamily G b =
      randomGradientCovarianceContribution G b := by
  rfl

/-- Random empirical gradient covariance matrix. -/
def randomEmpiricalGradientCovariance {Omega : Type*}
    {batch n : Nat}
    (G : RandomGradientTable Omega batch n) :
    RandomMatrix Omega (n + 1) (n + 1) :=
  fun omega => empiricalGradientCovariance (G omega)

@[simp]
theorem randomEmpiricalGradientCovariance_apply {Omega : Type*}
    [MeasurableSpace Omega] {batch n : Nat}
    (G : RandomGradientTable Omega batch n) (omega : Omega)
    (i j : Fin (n + 1)) :
    randomEmpiricalGradientCovariance G omega i j =
      Finset.univ.sum fun b : Fin batch => G omega b i * G omega b j := by
  simp [randomEmpiricalGradientCovariance]

/-- Centered rank-one gradient covariance contribution for one batch coordinate.

This is the gradient-facing name for the core centered rank-one random-matrix
API. The Matrix Bernstein examples still keep the gradient-level analytic
hypotheses explicit. -/
def centeredGradientCovarianceContribution {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {batch n : Nat}
    (G : RandomGradientTable Omega batch n) (b : Fin batch) :
    RandomMatrix Omega (n + 1) (n + 1) :=
  centeredRankOneRandomMatrix P (randomGradientVector G b)

/-- Centered gradient covariance summand family for Matrix Bernstein. -/
def centeredGradientCovarianceSummands {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {batch n : Nat}
    (G : RandomGradientTable Omega batch n) :
    Fin batch -> RandomMatrix Omega (n + 1) (n + 1) :=
  centeredRankOneRandomMatrixFamily P (randomGradientVectorFamily G)

/-- Example-local adapter from concrete gradient covariance summands to the
abstract family used by Matrix Bernstein.

This equality records the intended centered summand interpretation; it does not
prove the analytic Matrix Bernstein assumptions from gradient-level facts. -/
def IsCenteredGradientCovarianceSummandFamily {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {batch n : Nat}
    (G : RandomGradientTable Omega batch n)
    (A : Fin batch -> RandomMatrix Omega (n + 1) (n + 1)) : Prop :=
  A = centeredGradientCovarianceSummands (P := P) G

/-! ## Matrix Bernstein usage assumptions and tail wrappers -/

/-- Assumptions needed to use Matrix Bernstein for empirical gradient
covariance or empirical Fisher style matrices.

The `gradientAdapter` field is semantic glue connecting the abstract summand
family `A` to centered rank-one gradient covariance contributions. The
remaining fields are exactly the Matrix Bernstein assumptions consumed by the
library theorem. -/
structure GradientCovarianceMatrixBernsteinAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {batch n : Nat}
    (G : RandomGradientTable Omega batch n)
    (A : Fin batch -> RandomMatrix Omega (n + 1) (n + 1))
    (theta R sigmaSq : Real) : Prop where
  gradientAdapter : IsCenteredGradientCovarianceSummandFamily (P := P) G A
  centered : CenteredSelfAdjointRandomMatrixFamily P A
  independentSelfAdjoint : IndependentSelfAdjointRandomMatrices P A
  integrable : forall b, IntegrableRandomMatrix P (A b)
  squareIntegrable : forall b, IntegrableRandomMatrix P (randomMatrixSquare (A b))
  expIntegrable :
    forall b,
      IntegrableRandomMatrix P (matrixExpScaledFamily A theta b)
  traceExpIntegrable :
    IntegrableRealRandomVariable P
      (traceExpIntegrand (randomMatrixSum A) theta)
  operatorNormBound : PointwiseOperatorNormBound A R
  radiusNonneg : 0 <= R
  thetaRange : abs theta * R < 3
  thetaPositive : 0 < theta
  varianceProxyNormBound : MatrixVarianceProxyNormBound P A sigmaSq
  cfcPrimitive :
    forall b omega,
      bernsteinMatrixExpLeQuadraticStatement (A b omega) theta R
  troppPrimitive :
    troppMasterTraceMGFFiniteFamilyStatement
      (P := P) A (bernsteinSecondMomentComparisonFamily P A theta R)
      (matrixVarianceProxy P A) theta R

/-- Gradient covariance quadratic-form upper-tail bound with the normalized
scalar Matrix Bernstein RHS. -/
theorem gradientCovariance_quadraticForm_tail_scalar_exp_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {batch n : Nat}
    (G : RandomGradientTable Omega batch n)
    (A : Fin batch -> RandomMatrix Omega (n + 1) (n + 1))
    (theta R t sigmaSq : Real)
    (h : GradientCovarianceMatrixBernsteinAssumptions
      (P := P) G A theta R sigmaSq) :
    P (quadraticFormUpperTailEvent (randomMatrixSum A) t) <=
      ENNReal.ofReal
        ((n + 1 : Real) *
          Real.exp (-(theta * t) + bernsteinMGFCoeff theta R * sigmaSq)) := by
  exact
    matrixBernsteinQuadraticFormUpperTailScalarExpRHSWithCoeff_under_primitives
      A theta R t sigmaSq h.centered h.independentSelfAdjoint h.integrable
      h.squareIntegrable h.expIntegrable h.traceExpIntegrable
      h.operatorNormBound h.radiusNonneg h.thetaRange h.thetaPositive
      h.varianceProxyNormBound h.cfcPrimitive h.troppPrimitive

/-- Gradient covariance quadratic-form upper-tail bound retaining the
trace-exponential Matrix Bernstein RHS. -/
theorem gradientCovariance_quadraticForm_tail_traceExp_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {batch n : Nat}
    (G : RandomGradientTable Omega batch n)
    (A : Fin batch -> RandomMatrix Omega (n + 1) (n + 1))
    (theta R t sigmaSq : Real)
    (h : GradientCovarianceMatrixBernsteinAssumptions
      (P := P) G A theta R sigmaSq) :
    P (quadraticFormUpperTailEvent (randomMatrixSum A) t) <=
      ENNReal.ofReal (Real.exp (-(theta * t))) *
        ENNReal.ofReal
          (traceMatrixExp
            (SMul.smul (bernsteinMGFCoeff theta R)
              (matrixVarianceProxy P A))) := by
  exact
    matrixBernsteinQuadraticFormUpperTailWithCoeff_under_primitives
      A theta R t h.centered h.independentSelfAdjoint h.integrable
      h.squareIntegrable h.expIntegrable h.traceExpIntegrable
      h.operatorNormBound h.radiusNonneg h.thetaRange h.thetaPositive
      h.cfcPrimitive h.troppPrimitive

/-- Optimized-theta assumptions needed to use Matrix Bernstein for empirical
gradient covariance or empirical Fisher style matrices.

The analytic assumptions involving exponentials and Tropp are specialized at
the canonical Bernstein choice `bernsteinThetaChoice t sigmaSq R`. The
pointwise Bernstein CFC primitive is supplied by the core hardbone theorem, so
this optimized usage surface no longer exposes a CFC field. -/
structure GradientCovarianceOptimizedMatrixBernsteinAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {batch n : Nat}
    (G : RandomGradientTable Omega batch n)
    (A : Fin batch -> RandomMatrix Omega (n + 1) (n + 1))
    (R t sigmaSq : Real) : Prop where
  gradientAdapter : IsCenteredGradientCovarianceSummandFamily (P := P) G A
  matrixBernsteinSide :
    MatrixBernsteinPositiveSideTroppAssumptions (P := P) A R t sigmaSq

/-- Gradient covariance quadratic-form upper-tail bound with the optimized
scalar Matrix Bernstein RHS.

This usage theorem has no explicit theta parameter. The theta choice and scalar
optimization are supplied by the existing Matrix Bernstein theorem. -/
theorem gradientCovariance_quadraticForm_tail_optimized_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {batch n : Nat}
    (G : RandomGradientTable Omega batch n)
    (A : Fin batch -> RandomMatrix Omega (n + 1) (n + 1))
    (R t sigmaSq : Real)
    (h : GradientCovarianceOptimizedMatrixBernsteinAssumptions
      (P := P) G A R t sigmaSq) :
    P (quadraticFormUpperTailEvent (randomMatrixSum A) t) <=
      matrixBernsteinOptimizedScalarTailRHS (n + 1) R t sigmaSq := by
  exact
    matrixBernsteinQuadraticFormUpperTailOptimizedScalarRHSWithCoeff_of_troppAssumptions
      (P := P) A R t sigmaSq h.matrixBernsteinSide

end

end HighDimProb.Examples.RandomMatrix.GradientCovarianceUsage
