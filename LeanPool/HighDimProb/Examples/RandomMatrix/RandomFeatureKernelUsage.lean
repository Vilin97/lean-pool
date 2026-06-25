/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Examples.RandomMatrix.NTKGramUsage

/-!
# Random feature kernel concentration usage example

This examples-only file shows how a finite random-feature kernel approximation
can be connected to the existing RandomMatrix Matrix Bernstein API. It does not
prove feature-level centeredness, boundedness, neural-network training
dynamics, or the Tropp/Bernstein primitive assumptions.
-/

namespace HighDimProb.Examples.RandomMatrix.RandomFeatureKernelUsage

open MeasureTheory
open HighDimProb.Examples.RandomMatrix.NTKGramUsage

noncomputable section

/-! ## Deterministic random-feature kernel vocabulary -/

/-- A random-feature vector evaluated on a finite dataset of size `n + 1`. -/
abbrev FeatureVector (n : Nat) :=
  NTKFeatureVector n

/-- Rank-one kernel Gram contribution `phi phi^T`. -/
def featureKernelOuter {n : Nat} (phi : FeatureVector n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  ntkGramOuter phi

@[simp]
theorem featureKernelOuter_apply {n : Nat} (phi : FeatureVector n)
    (i j : Fin (n + 1)) :
    featureKernelOuter phi i j = phi i * phi j := by
  rfl

/-- A finite table of random-feature vectors. -/
abbrev FeatureTable (numFeatures n : Nat) :=
  Fin numFeatures -> FeatureVector n

/-- One rank-one kernel contribution from a finite feature table. -/
def featureKernelContribution {numFeatures n : Nat}
    (Phi : FeatureTable numFeatures n) (a : Fin numFeatures) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  featureKernelOuter (Phi a)

@[simp]
theorem featureKernelContribution_apply {numFeatures n : Nat}
    (Phi : FeatureTable numFeatures n) (a : Fin numFeatures)
    (i j : Fin (n + 1)) :
    featureKernelContribution Phi a i j = Phi a i * Phi a j := by
  rfl

/-- Empirical random-feature kernel matrix as a sum of rank-one contributions. -/
def empiricalFeatureKernel {numFeatures n : Nat}
    (Phi : FeatureTable numFeatures n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  Finset.univ.sum fun a : Fin numFeatures => featureKernelContribution Phi a

/-- Optional feature-count-normalized empirical random-feature kernel matrix. -/
def normalizedEmpiricalFeatureKernel {numFeatures n : Nat}
    (Phi : FeatureTable numFeatures n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  SMul.smul (1 / (numFeatures : Real)) (empiricalFeatureKernel Phi)

/-- The empirical feature kernel is definitionally the sum of rank-one terms. -/
theorem empiricalFeatureKernel_eq_sum_rankOne {numFeatures n : Nat}
    (Phi : FeatureTable numFeatures n) :
    empiricalFeatureKernel Phi =
      Finset.univ.sum fun a : Fin numFeatures => featureKernelContribution Phi a := by
  rfl

@[simp]
theorem empiricalFeatureKernel_apply {numFeatures n : Nat}
    (Phi : FeatureTable numFeatures n) (i j : Fin (n + 1)) :
    empiricalFeatureKernel Phi i j =
      Finset.univ.sum fun a : Fin numFeatures => Phi a i * Phi a j := by
  simpa [empiricalFeatureKernel, featureKernelContribution, featureKernelOuter,
    ntkGramOuter] using
    (Matrix.sum_apply i j Finset.univ
      (fun a : Fin numFeatures => featureKernelContribution Phi a))

@[simp]
theorem normalizedEmpiricalFeatureKernel_apply {numFeatures n : Nat}
    (Phi : FeatureTable numFeatures n) (i j : Fin (n + 1)) :
    normalizedEmpiricalFeatureKernel Phi i j =
      (1 / (numFeatures : Real)) *
        Finset.univ.sum fun a : Fin numFeatures => Phi a i * Phi a j := by
  rw [normalizedEmpiricalFeatureKernel]
  change (1 / (numFeatures : Real)) * empiricalFeatureKernel Phi i j = _
  rw [empiricalFeatureKernel_apply]

/-! ## Random feature table and centered summand adapter -/

/-- A random finite table of random-feature vectors. -/
abbrev RandomFeatureTable (Omega : Type*)
    (numFeatures n : Nat) :=
  Omega -> FeatureTable numFeatures n

/-- The random feature vector associated with one sampled feature coordinate. -/
def randomFeatureVector {Omega : Type*}
    {numFeatures n : Nat} (Phi : RandomFeatureTable Omega numFeatures n)
    (a : Fin numFeatures) :
    RandomNTKFeatureVector Omega n :=
  fun omega => Phi omega a

@[simp]
theorem randomFeatureVector_apply {Omega : Type*} [MeasurableSpace Omega]
    {numFeatures n : Nat} (Phi : RandomFeatureTable Omega numFeatures n)
    (a : Fin numFeatures) (omega : Omega) (i : Fin (n + 1)) :
    randomFeatureVector Phi a omega i = Phi omega a i := by
  rfl

/-- Family of random-feature vectors indexed by sampled feature coordinate. -/
def randomFeatureVectorFamily {Omega : Type*}
    {numFeatures n : Nat} (Phi : RandomFeatureTable Omega numFeatures n) :
    Fin numFeatures -> RandomNTKFeatureVector Omega n :=
  randomFeatureVector Phi

@[simp]
theorem randomFeatureVectorFamily_apply {Omega : Type*} [MeasurableSpace Omega]
    {numFeatures n : Nat} (Phi : RandomFeatureTable Omega numFeatures n)
    (a : Fin numFeatures) :
    randomFeatureVectorFamily Phi a = randomFeatureVector Phi a := by
  rfl

/-- Random rank-one kernel contribution from one feature coordinate. -/
def randomFeatureKernelContribution {Omega : Type*}
    {numFeatures n : Nat} (Phi : RandomFeatureTable Omega numFeatures n)
    (a : Fin numFeatures) :
    RandomMatrix Omega (n + 1) (n + 1) :=
  ntkGramContribution (randomFeatureVector Phi a)

@[simp]
theorem randomFeatureKernelContribution_apply {Omega : Type*}
    [MeasurableSpace Omega] {numFeatures n : Nat}
    (Phi : RandomFeatureTable Omega numFeatures n) (a : Fin numFeatures)
    (omega : Omega) (i j : Fin (n + 1)) :
    randomFeatureKernelContribution Phi a omega i j =
      Phi omega a i * Phi omega a j := by
  rfl

/-- Random empirical random-feature kernel matrix. -/
def randomEmpiricalFeatureKernel {Omega : Type*}
    {numFeatures n : Nat} (Phi : RandomFeatureTable Omega numFeatures n) :
    RandomMatrix Omega (n + 1) (n + 1) :=
  fun omega => empiricalFeatureKernel (Phi omega)

@[simp]
theorem randomEmpiricalFeatureKernel_apply {Omega : Type*}
    [MeasurableSpace Omega] {numFeatures n : Nat}
    (Phi : RandomFeatureTable Omega numFeatures n) (omega : Omega)
    (i j : Fin (n + 1)) :
    randomEmpiricalFeatureKernel Phi omega i j =
      Finset.univ.sum fun a : Fin numFeatures => Phi omega a i * Phi omega a j := by
  simp [randomEmpiricalFeatureKernel]

/-- Centered rank-one random-feature kernel contribution for one coordinate.

This reuses the NTK-facing centered rank-one adapter; feature-level analytic
hypotheses remain explicit in the Matrix Bernstein assumptions below. -/
def centeredRandomFeatureKernelContribution {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {numFeatures n : Nat}
    (Phi : RandomFeatureTable Omega numFeatures n) (a : Fin numFeatures) :
    RandomMatrix Omega (n + 1) (n + 1) :=
  centeredNTKGramContribution (P := P) (randomFeatureVector Phi a)

/-- Centered random-feature kernel summand family for Matrix Bernstein. -/
def centeredRandomFeatureKernelSummands {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {numFeatures n : Nat}
    (Phi : RandomFeatureTable Omega numFeatures n) :
    Fin numFeatures -> RandomMatrix Omega (n + 1) (n + 1) :=
  centeredNTKGramSummands (P := P) (randomFeatureVectorFamily Phi)

/-- Example-local adapter from concrete random-feature kernels to the abstract
summand family used by Matrix Bernstein.

This equality records the intended centered summand interpretation; it does not
prove the analytic Matrix Bernstein assumptions from feature-level facts. -/
def IsCenteredRandomFeatureKernelSummandFamily {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {numFeatures n : Nat}
    (Phi : RandomFeatureTable Omega numFeatures n)
    (A : Fin numFeatures -> RandomMatrix Omega (n + 1) (n + 1)) : Prop :=
  A = centeredRandomFeatureKernelSummands (P := P) Phi

/-! ## Matrix Bernstein usage assumptions and tail wrappers -/

/-- Assumptions needed to use Matrix Bernstein for a random-feature kernel.

The `featureAdapter` field is semantic glue connecting the abstract summand
family `A` to centered rank-one random-feature kernel contributions. The
remaining fields are the existing Matrix Bernstein assumptions consumed by the
library theorem. -/
structure RandomFeatureKernelMatrixBernsteinAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {numFeatures n : Nat}
    (Phi : RandomFeatureTable Omega numFeatures n)
    (A : Fin numFeatures -> RandomMatrix Omega (n + 1) (n + 1))
    (theta R sigmaSq : Real) : Prop where
  featureAdapter : IsCenteredRandomFeatureKernelSummandFamily (P := P) Phi A
  centered : CenteredSelfAdjointRandomMatrixFamily P A
  independentSelfAdjoint : IndependentSelfAdjointRandomMatrices P A
  integrable : forall a, IntegrableRandomMatrix P (A a)
  squareIntegrable : forall a, IntegrableRandomMatrix P (randomMatrixSquare (A a))
  expIntegrable :
    forall a,
      IntegrableRandomMatrix P (matrixExpScaledFamily A theta a)
  traceExpIntegrable :
    IntegrableRealRandomVariable P
      (traceExpIntegrand (randomMatrixSum A) theta)
  operatorNormBound : PointwiseOperatorNormBound A R
  radiusNonneg : 0 <= R
  thetaRange : abs theta * R < 3
  thetaPositive : 0 < theta
  varianceProxyNormBound : MatrixVarianceProxyNormBound P A sigmaSq
  cfcPrimitive :
    forall a omega,
      bernsteinMatrixExpLeQuadraticStatement (A a omega) theta R
  troppPrimitive :
    troppMasterTraceMGFFiniteFamilyStatement
      (P := P) A (bernsteinSecondMomentComparisonFamily P A theta R)
      (matrixVarianceProxy P A) theta R

/-- Random-feature kernel quadratic-form upper-tail bound with the normalized
scalar Matrix Bernstein RHS. -/
theorem randomFeatureKernel_quadraticForm_tail_scalar_exp_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {numFeatures n : Nat}
    (Phi : RandomFeatureTable Omega numFeatures n)
    (A : Fin numFeatures -> RandomMatrix Omega (n + 1) (n + 1))
    (theta R t sigmaSq : Real)
    (h : RandomFeatureKernelMatrixBernsteinAssumptions
      (P := P) Phi A theta R sigmaSq) :
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

/-- Random-feature kernel quadratic-form upper-tail bound retaining the
trace-exponential Matrix Bernstein RHS. -/
theorem randomFeatureKernel_quadraticForm_tail_traceExp_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {numFeatures n : Nat}
    (Phi : RandomFeatureTable Omega numFeatures n)
    (A : Fin numFeatures -> RandomMatrix Omega (n + 1) (n + 1))
    (theta R t sigmaSq : Real)
    (h : RandomFeatureKernelMatrixBernsteinAssumptions
      (P := P) Phi A theta R sigmaSq) :
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

/-- Optimized-theta assumptions needed to use Matrix Bernstein for a
random-feature kernel.

The analytic assumptions involving exponentials and Tropp are specialized at
the canonical Bernstein choice `bernsteinThetaChoice t sigmaSq R`. The
pointwise Bernstein CFC primitive is supplied by the core hardbone theorem, so
this optimized usage surface no longer exposes a CFC field. -/
structure RandomFeatureKernelOptimizedMatrixBernsteinAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {numFeatures n : Nat}
    (Phi : RandomFeatureTable Omega numFeatures n)
    (A : Fin numFeatures -> RandomMatrix Omega (n + 1) (n + 1))
    (R t sigmaSq : Real) : Prop where
  featureAdapter : IsCenteredRandomFeatureKernelSummandFamily (P := P) Phi A
  matrixBernsteinSide :
    MatrixBernsteinPositiveSideTroppAssumptions (P := P) A R t sigmaSq

/-- Random-feature kernel quadratic-form upper-tail bound with the optimized
scalar Matrix Bernstein RHS.

This usage theorem has no explicit theta parameter. The theta choice and scalar
optimization are supplied by the existing Matrix Bernstein theorem. -/
theorem randomFeatureKernel_quadraticForm_tail_optimized_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {numFeatures n : Nat}
    (Phi : RandomFeatureTable Omega numFeatures n)
    (A : Fin numFeatures -> RandomMatrix Omega (n + 1) (n + 1))
    (R t sigmaSq : Real)
    (h : RandomFeatureKernelOptimizedMatrixBernsteinAssumptions
      (P := P) Phi A R t sigmaSq) :
    P (quadraticFormUpperTailEvent (randomMatrixSum A) t) <=
      matrixBernsteinOptimizedScalarTailRHS (n + 1) R t sigmaSq := by
  exact
    matrixBernsteinQuadraticFormUpperTailOptimizedScalarRHSWithCoeff_of_troppAssumptions
      (P := P) A R t sigmaSq h.matrixBernsteinSide

end

end HighDimProb.Examples.RandomMatrix.RandomFeatureKernelUsage
