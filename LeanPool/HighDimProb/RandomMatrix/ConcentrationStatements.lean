/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.Assumptions
import LeanPool.HighDimProb.RandomMatrix.Algebra
import LeanPool.HighDimProb.RandomMatrix.MatrixOrder
import LeanPool.HighDimProb.RandomMatrix.OperatorNorm
import LeanPool.HighDimProb.RandomMatrix.Sums
import LeanPool.HighDimProb.RandomMatrix.VarianceProxy
import LeanPool.HighDimProb.RandomMatrix.Laplace
import LeanPool.HighDimProb.RandomMatrix.HardboneStatements
import LeanPool.HighDimProb.Tail
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Matrix concentration assumption vocabulary and typed statements

Verified Wikipedia references:
* Matrix Chernoff bound: https://en.wikipedia.org/wiki/Matrix_Chernoff_bound
* Bernstein inequalities: https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)
* Concentration inequality: https://en.wikipedia.org/wiki/Concentration_inequality
* Random matrix: https://en.wikipedia.org/wiki/Random_matrix

This file contains assumption vocabulary and theorem-target `Prop`
specifications for future matrix concentration work. It intentionally does not
prove matrix Bernstein, matrix Hoeffding, matrix Chernoff, Hanson-Wright, or
covariance estimation.
-/

namespace HighDimProb

open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-- Sample covariance centered at the identity, as a random matrix. -/
def sampleCovarianceMinusIdentity {Omega : Type*}
    {m n : Nat} (A : RandomMatrix Omega m n) : RandomMatrix Omega n n :=
  fun omega => sampleCovariance A omega - (1 : Matrix (Fin n) (Fin n) Real)

/-- Typed target for a future finite-dimensional matrix Bernstein theorem.

This is the original MC1/MC3 min-form statement. The PSD hypothesis on the
variance proxy remains explicit for compatibility with the earlier public API.
For the proof-oriented self-adjoint statement below, PSD is instead supplied by
`isPSD_matrixVarianceProxy_of_selfAdjoint` from centered self-adjoint summands
and per-summand square integrability. -/
abbrev matrixBernsteinStatement {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} [Fintype I] {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) (sigma2 R c t : Real) : Prop :=
  CenteredSelfAdjointRandomMatrixFamily P A ->
    IndependentSelfAdjointRandomMatrices P A ->
      PointwiseOperatorNormBound A R ->
        IsPSDMatrix (matrixVarianceProxy P A) ->
          matrixVarianceProxyNorm P A <= sigma2 ->
            0 <= t ->
              upperTailProb P (operatorNorm (randomMatrixSum A)) t <=
                ENNReal.ofReal
                  (2 * (n : Real) * Real.exp (-(c * min (t ^ 2 / sigma2) (t / R))))

/-- Refined matrix Bernstein statement with additive denominator form.

This is still a typed `Prop` target, not a theorem. It is proof-oriented:
entrywise integrability of each summand, entrywise integrability of each
matrix square, centered self-adjointness, matrix-valued independence, a
pointwise operator-norm bound, nonnegative scale parameters, positive
denominator constants, and denominator positivity are all visible assumptions.
The PSD variance-proxy condition is no longer a separate hypothesis here:
it follows from `isPSD_matrixVarianceProxy_of_selfAdjoint`.

The intended shape is
`P(||sum_i A_i|| >= t) <= 2 n exp ( -t^2 / (c1*sigma2 + c2*R*t) )`.
Constants are conservative proof targets, not sharp constants.

MC5 keeps this as an operator-norm tail statement. The future analytic route
should pass through the typed spectral, trace-exponential, and Laplace targets
in `Spectral`, `TraceExp`, and `Laplace`; the lambda-max/Rayleigh and
self-adjoint operator-norm endpoint bridges remain unproved. -/
abbrev matrixBernsteinSelfAdjointStatement {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} [Fintype I] {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) (sigma2 R c1 c2 t : Real) : Prop :=
  0 < n ->
    (forall i, IntegrableRandomMatrix P (A i)) ->
      (forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i))) ->
        CenteredSelfAdjointRandomMatrixFamily P A ->
          IndependentSelfAdjointRandomMatrices P A ->
            PointwiseOperatorNormBound A R ->
              matrixVarianceProxyNorm P A <= sigma2 ->
                0 <= sigma2 ->
                  0 <= R ->
                    0 < c1 ->
                      0 < c2 ->
                        0 <= t ->
                          0 < c1 * sigma2 + c2 * R * t ->
                            upperTailProb P (operatorNorm (randomMatrixSum A)) t <=
                              ENNReal.ofReal
                                (2 * (n : Real) *
                                  Real.exp (-(t ^ 2 / (c1 * sigma2 + c2 * R * t))))

/-- Typed dependency bundle for the future matrix Bernstein Laplace route.

This is not a theorem and does not assert matrix Bernstein. It records the
three bridge targets that remain between the current proof-ready Bernstein
statement and a trace-mgf argument: the self-adjoint operator-norm tail
reduction, the upper quadratic-form matrix Laplace step, and the two-sided
operator-norm Laplace step. -/
abbrev matrixBernsteinLaplacePrerequisitesStatement {Omega : Type*}
    [MeasurableSpace Omega] {n : Nat} (P : Measure Omega)
    (Y : RandomMatrix Omega n n) (theta t : Real) : Prop :=
  selfAdjointOperatorNormTailViaQuadraticFormStatement Y t ∧
    matrixLaplaceTransformLIntegralStatement P Y theta t ∧
      selfAdjointOperatorNormLaplaceLIntegralStatement P Y theta t

/-- Typed target for the future Matrix Bernstein trace-mgf provider.

This statement isolates the hard matrix-mgf comparison for the random sum from
the final Bernstein tail theorem. Proving it is expected to require
Golden-Thompson/Lieb or equivalent noncommutative trace-mgf machinery, plus the
matrix-valued independence and variance-proxy provider steps. -/
abbrev matrixBernsteinTraceMGFStatement {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} [Fintype I] {n : Nat}
    (P : Measure Omega) (A : I -> RandomMatrix Omega n n)
    (theta : Real) : Prop :=
  TraceMGFVarianceProxyBound P (randomMatrixSum A) (matrixVarianceProxy P A)
    theta

/-- Typed target for the bounded Matrix Bernstein trace-mgf provider.

This is the Bernstein-denominator variant of `matrixBernsteinTraceMGFStatement`.
It preserves the older `theta ^ 2 / 2` target for compatibility while exposing
the coefficient produced by the bounded single-summand MGF route. -/
abbrev matrixBernsteinTraceMGFWithCoeffStatement {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} [Fintype I] {n : Nat}
    (P : Measure Omega) (A : I -> RandomMatrix Omega n n)
    (theta R : Real) : Prop :=
  TraceMGFBernsteinVarianceProxyBound P (randomMatrixSum A)
    (matrixVarianceProxy P A) theta R

/-- Matrix-exponential family `i |-> exp(theta * A_i)`. -/
def matrixExpScaledFamily {Omega : Type*}
    {I : Type*} {n : Nat} (A : I -> RandomMatrix Omega n n)
    (theta : Real) :
    I -> RandomMatrix Omega n n :=
  fun i omega => matrixExp ((scaledRandomMatrixFamily theta A i) omega)

/-- Pointwise negation of a random-matrix family.

This names the negative-sign family used by two-sided Bernstein wrappers so
public theorem signatures avoid anonymous lambda expressions. -/
abbrev negRandomMatrixFamily {Omega : Type*}
    {I : Type*} {m n : Nat}
    (A : I -> RandomMatrix Omega m n) :
    I -> RandomMatrix Omega m n :=
  fun i => negRandomMatrix (A i)

@[simp]
theorem negRandomMatrixFamily_apply {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} {m n : Nat}
    (A : I -> RandomMatrix Omega m n) (i : I) (omega : Omega) :
    negRandomMatrixFamily A i omega = -(A i omega) :=
  rfl

/-- Pointwise negation preserves entrywise random-matrix measurability. -/
theorem isRandomMatrix_negRandomMatrixFamily {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {I : Type*} {m n : Nat}
    {A : I -> RandomMatrix Omega m n}
    (hA : forall i, IsRandomMatrix P (A i)) :
    forall i, IsRandomMatrix P ((negRandomMatrixFamily A) i) := by
  intro i
  simpa [negRandomMatrixFamily] using
    isRandomMatrix_negRandomMatrix (P := P) (A := A i) (hA i)

/-- Pointwise negation preserves entrywise random-matrix integrability. -/
theorem integrableRandomMatrix_negRandomMatrixFamily {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {I : Type*} {m n : Nat}
    {A : I -> RandomMatrix Omega m n}
    (hA : forall i, IntegrableRandomMatrix P (A i)) :
    forall i, IntegrableRandomMatrix P ((negRandomMatrixFamily A) i) := by
  intro i r c
  change Integrable (fun omega => -(A i omega r c)) P
  exact (hA i r c).neg

/-- Pointwise negation preserves self-adjoint random-matrix families. -/
theorem selfAdjointRandomMatrixFamily_negRandomMatrixFamily {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {I : Type*} {n : Nat}
    {A : I -> RandomMatrix Omega n n}
    (hA : SelfAdjointRandomMatrixFamily P A) :
    SelfAdjointRandomMatrixFamily P (negRandomMatrixFamily A) := by
  refine ⟨?_, ?_⟩
  · exact isRandomMatrix_negRandomMatrixFamily (P := P) (A := A) hA.1
  · intro i
    change RandomSelfAdjointMatrix P (fun omega => -(A i omega))
    exact randomSelfAdjointMatrix_neg (P := P) (A := A i) (hA.2 i)

/-- Pointwise negation preserves centered self-adjoint random-matrix families. -/
theorem centeredSelfAdjointRandomMatrixFamily_negRandomMatrixFamily
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {I : Type*} {n : Nat} {A : I -> RandomMatrix Omega n n}
    (hA : CenteredSelfAdjointRandomMatrixFamily P A) :
    CenteredSelfAdjointRandomMatrixFamily P (negRandomMatrixFamily A) := by
  refine ⟨selfAdjointRandomMatrixFamily_negRandomMatrixFamily
    (P := P) (A := A) hA.1, ?_⟩
  intro i
  have hNeg :
      matrixExpect P ((negRandomMatrixFamily A) i) =
        (-1 : Real) • matrixExpect P (A i) := by
    ext r c
    change expect P (fun omega => -(A i omega r c)) =
      (-1 : Real) * expect P (fun omega => A i omega r c)
    rw [expect_def, expect_def, MeasureTheory.integral_neg]
    ring
  rw [hNeg, hA.2 i]
  simp

/-- Pointwise negation preserves matrix-valued independence. -/
theorem independentRandomMatrices_negRandomMatrixFamily {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {I : Type*} {m n : Nat}
    {A : I -> RandomMatrix Omega m n}
    (hA : IndependentRandomMatrices P A) :
    IndependentRandomMatrices P (negRandomMatrixFamily A) := by
  have hNeg :
      Measurable (fun M : Matrix (Fin m) (Fin n) Real => -M) := by
    change Measurable
      (fun M : Matrix (Fin m) (Fin n) Real =>
        fun r : Fin m => fun c : Fin n => -M r c)
    exact measurable_pi_lambda
      (fun M : Matrix (Fin m) (Fin n) Real =>
        fun r : Fin m => fun c : Fin n => -M r c)
      (fun r =>
        measurable_pi_lambda
          (fun M : Matrix (Fin m) (Fin n) Real => fun c : Fin n => -M r c)
          (fun c => by
            have hCoord :
                Measurable (fun M : Matrix (Fin m) (Fin n) Real => M r c) :=
              (measurable_pi_apply c).comp (measurable_pi_apply r)
            simpa using hCoord.neg))
  change ProbabilityTheory.iIndepFun (fun i omega => -A i omega) P
  exact hA.comp (fun _i => Neg.neg) (fun _i => hNeg)

/-- Pointwise negation preserves independent self-adjoint random-matrix families. -/
theorem independentSelfAdjointRandomMatrices_negRandomMatrixFamily
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {I : Type*} {n : Nat} {A : I -> RandomMatrix Omega n n}
    (hA : IndependentSelfAdjointRandomMatrices P A) :
    IndependentSelfAdjointRandomMatrices P (negRandomMatrixFamily A) := by
  exact ⟨selfAdjointRandomMatrixFamily_negRandomMatrixFamily (P := P) (A := A) hA.1,
    independentRandomMatrices_negRandomMatrixFamily (P := P) (A := A) hA.2⟩

/-- Pointwise negation preserves a uniform operator-norm bound. -/
theorem PointwiseOperatorNormBound_negRandomMatrixFamily {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} {m n : Nat}
    {A : I -> RandomMatrix Omega m n} {R : Real}
    (hA : PointwiseOperatorNormBound A R) :
    PointwiseOperatorNormBound (negRandomMatrixFamily A) R := by
  intro i omega
  simpa [BoundedOperatorNorm, operatorNorm, negRandomMatrixFamily] using hA i omega

/-- Squaring a pointwise-negated square random-matrix family gives the
original square family. -/
theorem randomMatrixSquare_negRandomMatrixFamily {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} {n : Nat}
    (A : I -> RandomMatrix Omega n n) :
    forall i,
      randomMatrixSquare ((negRandomMatrixFamily A) i) =
        randomMatrixSquare (A i) := by
  intro i
  simp

/-- Square-integrability transfers from a square random-matrix family to its
pointwise negation because `(-X)^2 = X^2`. -/
theorem integrableRandomMatrix_randomMatrixSquare_negRandomMatrixFamily
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {I : Type*} {n : Nat} {A : I -> RandomMatrix Omega n n}
    (hA : forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i))) :
    forall i,
      IntegrableRandomMatrix P
        (randomMatrixSquare ((negRandomMatrixFamily A) i)) := by
  intro i
  simpa [randomMatrixSquare_negRandomMatrixFamily (A := A) i] using hA i

/-- The second-moment matrix is unchanged by pointwise family negation.

This is a variance-proxy boundary adapter for the negative-family Matrix
Bernstein route. It is only the algebraic square fact `(-A)^2 = A^2`; it does
not prove any Tropp/Lieb or integrability input. -/
theorem matrixSecondMoment_negRandomMatrixFamily {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {I : Type*} {n : Nat}
    (A : I -> RandomMatrix Omega n n) :
    forall i,
      matrixSecondMoment P ((negRandomMatrixFamily A) i) =
        matrixSecondMoment P (A i) := by
  intro i
  unfold matrixSecondMoment
  rw [randomMatrixSquare_negRandomMatrixFamily]

/-- The matrix variance proxy is unchanged by pointwise family negation.

This names the variance-proxy equality needed before any honest negative-family
Tropp boundary transfer can be stated. -/
theorem matrixVarianceProxy_negRandomMatrixFamily {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega}
    {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n) :
    matrixVarianceProxy P (negRandomMatrixFamily A) = matrixVarianceProxy P A := by
  unfold matrixVarianceProxy
  apply Finset.sum_congr rfl
  intro i _hi
  exact matrixSecondMoment_negRandomMatrixFamily (P := P) (A := A) i

@[simp]
theorem matrixExpScaledFamily_apply {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} {n : Nat} (A : I -> RandomMatrix Omega n n)
    (theta : Real) (i : I) (omega : Omega) :
    matrixExpScaledFamily A theta i omega =
      matrixExp (SMul.smul theta (A i omega)) :=
  rfl

/-- Matrix-exponential sign normalization for a pointwise-negated family.

This rewrites the negative family at `theta` to the original family at
`-theta`. It does not turn positive-theta integrability into negative-side
integrability. -/
theorem matrixExpScaledFamily_negRandomMatrixFamily {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} {n : Nat}
    (A : I -> RandomMatrix Omega n n) (theta : Real) :
    forall i,
      matrixExpScaledFamily (negRandomMatrixFamily A) theta i =
        matrixExpScaledFamily A (-theta) i := by
  intro i
  funext omega
  have harg :
      SMul.smul theta (-(A i omega)) = SMul.smul (-theta) (A i omega) := by
    ext r c
    simp [SMul.smul]
  simp [matrixExpScaledFamily, negRandomMatrixFamily, harg]

/-- Matrix-exponential integrability transfers to a pointwise-negated family
only from the original family at the opposite scalar parameter. -/
theorem integrableRandomMatrix_matrixExpScaledFamily_negRandomMatrixFamily
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {I : Type*} {n : Nat} {A : I -> RandomMatrix Omega n n}
    {theta : Real}
    (hA :
      forall i,
        IntegrableRandomMatrix P (matrixExpScaledFamily A (-theta) i)) :
    forall i,
      IntegrableRandomMatrix P
        (matrixExpScaledFamily (negRandomMatrixFamily A) theta i) := by
  intro i
  simpa [matrixExpScaledFamily_negRandomMatrixFamily (A := A) theta i] using hA i

/-- Finite sums commute with the named pointwise negation family. -/
theorem randomMatrixSum_negRandomMatrixFamily {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n) :
    randomMatrixSum (negRandomMatrixFamily A) =
      negRandomMatrix (randomMatrixSum A) := by
  funext omega
  ext r c
  simp [randomMatrixSum, negRandomMatrixFamily, negRandomMatrix, Matrix.sum_apply,
    Finset.sum_neg_distrib]

/-- Trace-exponential sign normalization for the finite sum of a
pointwise-negated family. -/
theorem traceExpIntegrand_randomMatrixSum_negRandomMatrixFamily
    {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n) (theta : Real) :
    traceExpIntegrand (randomMatrixSum (negRandomMatrixFamily A)) theta =
      traceExpIntegrand (randomMatrixSum A) (-theta) := by
  funext omega
  have hsum :
      randomMatrixSum (negRandomMatrixFamily A) omega =
        -(randomMatrixSum A omega) := by
    rw [randomMatrixSum_negRandomMatrixFamily]
    rfl
  have harg :
      SMul.smul theta (randomMatrixSum (negRandomMatrixFamily A) omega) =
        SMul.smul (-theta) (randomMatrixSum A omega) := by
    rw [hsum]
    ext r c
    simp [SMul.smul]
  change
    traceMatrixExp
        (SMul.smul theta (randomMatrixSum (negRandomMatrixFamily A) omega)) =
      traceMatrixExp (SMul.smul (-theta) (randomMatrixSum A omega))
  exact congrArg traceMatrixExp harg

/-- Trace-exponential integrability transfers to the finite sum of a
pointwise-negated family only from the original sum at the opposite scalar
parameter. -/
theorem integrableRealRandomVariable_traceExpIntegrand_randomMatrixSum_negRandomMatrixFamily
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {I : Type*} [Fintype I] {n : Nat} {A : I -> RandomMatrix Omega n n}
    {theta : Real}
    (hA :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum A) (-theta))) :
    IntegrableRealRandomVariable P
      (traceExpIntegrand (randomMatrixSum (negRandomMatrixFamily A)) theta) := by
  rw [traceExpIntegrand_randomMatrixSum_negRandomMatrixFamily (A := A) theta]
  exact hA

/-- Bernstein coefficient times the per-summand matrix second moment. -/
def bernsteinSecondMomentComparisonFamily {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} {n : Nat}
    (P : Measure Omega) (A : I -> RandomMatrix Omega n n)
    (theta R : Real) :
    I -> Matrix (Fin n) (Fin n) Real :=
  fun i =>
    SMul.smul (bernsteinMGFCoeff theta R)
      (matrixSecondMoment P (A i))

@[simp]
theorem bernsteinSecondMomentComparisonFamily_apply {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} {n : Nat}
    (P : Measure Omega) (A : I -> RandomMatrix Omega n n)
    (theta R : Real) (i : I) :
    bernsteinSecondMomentComparisonFamily P A theta R i =
      SMul.smul (bernsteinMGFCoeff theta R)
        (matrixSecondMoment P (A i)) :=
  rfl

/-- The canonical Bernstein second-moment comparison family is sign-normalized
by passing from `theta` on the pointwise-negated family to `-theta` on the
original family.

This is only the K-family equality used by the finite-family Tropp boundary. It
does not prove the Tropp/Lieb primitive or the per-summand MGF comparison. -/
theorem bernsteinSecondMomentComparisonFamily_negRandomMatrixFamily
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {I : Type*} {n : Nat}
    (A : I -> RandomMatrix Omega n n) (theta R : Real) :
    forall i,
      bernsteinSecondMomentComparisonFamily P (negRandomMatrixFamily A) theta R i =
        bernsteinSecondMomentComparisonFamily P A (-theta) R i := by
  intro i
  rw [bernsteinSecondMomentComparisonFamily_apply,
    bernsteinSecondMomentComparisonFamily_apply]
  rw [matrixSecondMoment_negRandomMatrixFamily (P := P) (A := A) i]
  rw [bernsteinMGFCoeff_neg]

/-- Transfer the canonical per-summand Matrix-MGF comparison input from the
original family at `-theta` to the pointwise-negated family at `theta`.

This is a Tropp-input adapter only. It assumes the original-family MGF
comparison at the opposite parameter and does not prove the finite-family
Tropp/Lieb primitive. -/
theorem bernsteinMGFComparison_negRandomMatrixFamily {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {I : Type*} {n : Nat}
    (A : I -> RandomMatrix Omega n n) (theta R : Real)
    (hA :
      forall i,
        MatrixLE
          (matrixExpect P (matrixExpScaledFamily A (-theta) i))
          (matrixExp (bernsteinSecondMomentComparisonFamily P A (-theta) R i))) :
    forall i,
      MatrixLE
        (matrixExpect P (matrixExpScaledFamily (negRandomMatrixFamily A) theta i))
        (matrixExp
          (bernsteinSecondMomentComparisonFamily P (negRandomMatrixFamily A) theta R i)) := by
  intro i
  rw [matrixExpScaledFamily_negRandomMatrixFamily (A := A) theta i]
  rw [bernsteinSecondMomentComparisonFamily_negRandomMatrixFamily
    (P := P) (A := A) theta R i]
  exact hA i

/-- Semantic bounded trace-MGF transfer from an original family at `-theta` to
the pointwise-negated family at `theta`.

This is a post-provider sign-normalization theorem. It transfers an already
supplied bounded trace-MGF statement; it does not prove Tropp/Lieb,
Golden-Thompson, or any trace-MGF provider. -/
theorem traceMGFBernsteinVarianceProxyBound_negRandomMatrixFamily
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n) (V : Matrix (Fin n) (Fin n) Real)
    (theta R : Real)
    (hA :
      TraceMGFBernsteinVarianceProxyBound P (randomMatrixSum A) V (-theta) R) :
    TraceMGFBernsteinVarianceProxyBound P
      (randomMatrixSum (negRandomMatrixFamily A)) V theta R := by
  unfold TraceMGFBernsteinVarianceProxyBound TraceMGFBound traceExpMoment at *
  rw [traceExpIntegrand_randomMatrixSum_negRandomMatrixFamily (A := A) theta]
  rw [bernsteinMGFCoeff_neg] at hA
  exact hA

/-- The bounded Matrix Bernstein trace-MGF statement sign-normalizes from the
original family at `-theta` to the pointwise-negated family at `theta`.

This theorem is downstream of a trace-MGF provider. It does not prove the
finite-family Tropp primitive; it only rewrites the already supplied semantic
trace-MGF statement through the negative-family variance-proxy and trace-exp
equalities. -/
theorem matrixBernsteinTraceMGFWithCoeff_negRandomMatrixFamily
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n) (theta R : Real)
    (hA : matrixBernsteinTraceMGFWithCoeffStatement P A (-theta) R) :
    matrixBernsteinTraceMGFWithCoeffStatement P
      (negRandomMatrixFamily A) theta R := by
  unfold matrixBernsteinTraceMGFWithCoeffStatement at *
  rw [matrixVarianceProxy_negRandomMatrixFamily (P := P) (A := A)]
  exact traceMGFBernsteinVarianceProxyBound_negRandomMatrixFamily A
    (matrixVarianceProxy P A) theta R hA

/-- Positive-side assumptions shared by optimized Matrix Bernstein tail wrappers.

This structure packages the long proof-facing hypothesis list for one
self-adjoint random-matrix family. It is intentionally semantic: it does not
derive integrability, boundedness, variance-proxy control, or Tropp/Lieb
inputs. The retained `cfcPrimitive` field is a compatibility surface; it can be
filled by `bernsteinMatrixExp_le_quadratic`. -/
structure MatrixBernsteinPositiveSideAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n) (R t sigmaSq : Real) : Prop where
  centered : CenteredSelfAdjointRandomMatrixFamily P A
  independentSelfAdjoint : IndependentSelfAdjointRandomMatrices P A
  integrable : forall i, IntegrableRandomMatrix P (A i)
  squareIntegrable :
    forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i))
  expIntegrable :
    forall i,
      IntegrableRandomMatrix P
        (matrixExpScaledFamily A (bernsteinThetaChoice t sigmaSq R) i)
  traceExpIntegrable :
    IntegrableRealRandomVariable P
      (traceExpIntegrand (randomMatrixSum A)
        (bernsteinThetaChoice t sigmaSq R))
  operatorNormBound : PointwiseOperatorNormBound A R
  sigmaPositive : 0 < sigmaSq
  radiusNonneg : 0 <= R
  deviationPositive : 0 < t
  varianceProxyNormBound : MatrixVarianceProxyNormBound P A sigmaSq
  cfcPrimitive :
    forall i omega,
      bernsteinMatrixExpLeQuadraticStatement (A i omega)
        (bernsteinThetaChoice t sigmaSq R) R
  troppPrimitive :
    troppMasterTraceMGFFiniteFamilyStatement
      (P := P) A
      (bernsteinSecondMomentComparisonFamily P A
        (bernsteinThetaChoice t sigmaSq R) R)
      (matrixVarianceProxy P A) (bernsteinThetaChoice t sigmaSq R) R

/-- Negative-side assumptions for optimized two-sided Matrix Bernstein wrappers.

The family is fixed to `negRandomMatrixFamily A`, so public users do not need to
repeat the anonymous negation family in theorem signatures. This is only an
assumption bundle; it does not prove any positive-to-negative transfer. The
shared threshold condition `0 < t` is carried by the paired positive-side bundle
in the current two-sided wrappers, so the same scalar proof is not duplicated
here. -/
structure MatrixBernsteinNegativeSideAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n) (Rneg t sigmaSqNeg : Real) : Prop where
  centered : CenteredSelfAdjointRandomMatrixFamily P (negRandomMatrixFamily A)
  independentSelfAdjoint :
    IndependentSelfAdjointRandomMatrices P (negRandomMatrixFamily A)
  integrable :
    forall i, IntegrableRandomMatrix P ((negRandomMatrixFamily A) i)
  squareIntegrable :
    forall i,
      IntegrableRandomMatrix P
        (randomMatrixSquare ((negRandomMatrixFamily A) i))
  expIntegrable :
    forall i,
      IntegrableRandomMatrix P
        (matrixExpScaledFamily (negRandomMatrixFamily A)
          (bernsteinThetaChoice t sigmaSqNeg Rneg) i)
  traceExpIntegrable :
    IntegrableRealRandomVariable P
      (traceExpIntegrand (randomMatrixSum (negRandomMatrixFamily A))
        (bernsteinThetaChoice t sigmaSqNeg Rneg))
  operatorNormBound :
    PointwiseOperatorNormBound (negRandomMatrixFamily A) Rneg
  sigmaPositive : 0 < sigmaSqNeg
  radiusNonneg : 0 <= Rneg
  varianceProxyNormBound :
    MatrixVarianceProxyNormBound P (negRandomMatrixFamily A) sigmaSqNeg
  cfcPrimitive :
    forall i omega,
      bernsteinMatrixExpLeQuadraticStatement
        ((negRandomMatrixFamily A) i omega)
        (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg
  troppPrimitive :
    troppMasterTraceMGFFiniteFamilyStatement
      (P := P) (negRandomMatrixFamily A)
      (bernsteinSecondMomentComparisonFamily P (negRandomMatrixFamily A)
        (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg)
      (matrixVarianceProxy P (negRandomMatrixFamily A))
      (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg

/-- Preferred positive-side assumptions after the Bernstein CFC hardbone leaf.

This bundle keeps the genuine remaining analytic primitive, the finite-family
Tropp/Lieb trace-MGF statement, but no longer asks users to provide the
pointwise Bernstein CFC inequality. The latter is supplied by
`bernsteinMatrixExp_le_quadratic` when converting to the compatibility bundle
`MatrixBernsteinPositiveSideAssumptions`. -/
structure MatrixBernsteinPositiveSideTroppAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n) (R t sigmaSq : Real) : Prop where
  centered : CenteredSelfAdjointRandomMatrixFamily P A
  independentSelfAdjoint : IndependentSelfAdjointRandomMatrices P A
  integrable : forall i, IntegrableRandomMatrix P (A i)
  squareIntegrable :
    forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i))
  expIntegrable :
    forall i,
      IntegrableRandomMatrix P
        (matrixExpScaledFamily A (bernsteinThetaChoice t sigmaSq R) i)
  traceExpIntegrable :
    IntegrableRealRandomVariable P
      (traceExpIntegrand (randomMatrixSum A)
        (bernsteinThetaChoice t sigmaSq R))
  operatorNormBound : PointwiseOperatorNormBound A R
  sigmaPositive : 0 < sigmaSq
  radiusNonneg : 0 <= R
  deviationPositive : 0 < t
  varianceProxyNormBound : MatrixVarianceProxyNormBound P A sigmaSq
  troppPrimitive :
    troppMasterTraceMGFFiniteFamilyStatement
      (P := P) A
      (bernsteinSecondMomentComparisonFamily P A
        (bernsteinThetaChoice t sigmaSq R) R)
      (matrixVarianceProxy P A) (bernsteinThetaChoice t sigmaSq R) R

/-- Preferred negative-side assumptions after the Bernstein CFC hardbone leaf.

This is the negative-family analogue of
`MatrixBernsteinPositiveSideTroppAssumptions`. It keeps the named
`negRandomMatrixFamily A` surface and only exposes the remaining Tropp/Lieb
primitive, not the already proved pointwise Bernstein CFC primitive. -/
structure MatrixBernsteinNegativeSideTroppAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n) (Rneg t sigmaSqNeg : Real) : Prop where
  centered : CenteredSelfAdjointRandomMatrixFamily P (negRandomMatrixFamily A)
  independentSelfAdjoint :
    IndependentSelfAdjointRandomMatrices P (negRandomMatrixFamily A)
  integrable :
    forall i, IntegrableRandomMatrix P ((negRandomMatrixFamily A) i)
  squareIntegrable :
    forall i,
      IntegrableRandomMatrix P
        (randomMatrixSquare ((negRandomMatrixFamily A) i))
  expIntegrable :
    forall i,
      IntegrableRandomMatrix P
        (matrixExpScaledFamily (negRandomMatrixFamily A)
          (bernsteinThetaChoice t sigmaSqNeg Rneg) i)
  traceExpIntegrable :
    IntegrableRealRandomVariable P
      (traceExpIntegrand (randomMatrixSum (negRandomMatrixFamily A))
        (bernsteinThetaChoice t sigmaSqNeg Rneg))
  operatorNormBound :
    PointwiseOperatorNormBound (negRandomMatrixFamily A) Rneg
  sigmaPositive : 0 < sigmaSqNeg
  radiusNonneg : 0 <= Rneg
  varianceProxyNormBound :
    MatrixVarianceProxyNormBound P (negRandomMatrixFamily A) sigmaSqNeg
  troppPrimitive :
    troppMasterTraceMGFFiniteFamilyStatement
      (P := P) (negRandomMatrixFamily A)
      (bernsteinSecondMomentComparisonFamily P (negRandomMatrixFamily A)
        (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg)
      (matrixVarianceProxy P (negRandomMatrixFamily A))
      (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg

namespace MatrixBernsteinPositiveSideTroppAssumptions

/-- Convert the preferred CFC-free positive-side bundle into the older
compatibility bundle by supplying the proved pointwise Bernstein CFC theorem. -/
theorem toPositiveSideAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {I : Type*} [Fintype I] {n : Nat}
    {A : I -> RandomMatrix Omega n n} {R t sigmaSq : Real}
    (h : MatrixBernsteinPositiveSideTroppAssumptions (P := P) A R t sigmaSq) :
    MatrixBernsteinPositiveSideAssumptions (P := P) A R t sigmaSq where
  centered := h.centered
  independentSelfAdjoint := h.independentSelfAdjoint
  integrable := h.integrable
  squareIntegrable := h.squareIntegrable
  expIntegrable := h.expIntegrable
  traceExpIntegrable := h.traceExpIntegrable
  operatorNormBound := h.operatorNormBound
  sigmaPositive := h.sigmaPositive
  radiusNonneg := h.radiusNonneg
  deviationPositive := h.deviationPositive
  varianceProxyNormBound := h.varianceProxyNormBound
  cfcPrimitive :=
    fun i omega =>
      bernsteinMatrixExp_le_quadratic (A i omega)
        (bernsteinThetaChoice t sigmaSq R) R
  troppPrimitive := h.troppPrimitive

end MatrixBernsteinPositiveSideTroppAssumptions

namespace MatrixBernsteinNegativeSideTroppAssumptions

/-- Convert the preferred CFC-free negative-side bundle into the older
compatibility bundle by supplying the proved pointwise Bernstein CFC theorem. -/
theorem toNegativeSideAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {I : Type*} [Fintype I] {n : Nat}
    {A : I -> RandomMatrix Omega n n} {Rneg t sigmaSqNeg : Real}
    (h :
      MatrixBernsteinNegativeSideTroppAssumptions
        (P := P) A Rneg t sigmaSqNeg) :
    MatrixBernsteinNegativeSideAssumptions (P := P) A Rneg t sigmaSqNeg where
  centered := h.centered
  independentSelfAdjoint := h.independentSelfAdjoint
  integrable := h.integrable
  squareIntegrable := h.squareIntegrable
  expIntegrable := h.expIntegrable
  traceExpIntegrable := h.traceExpIntegrable
  operatorNormBound := h.operatorNormBound
  sigmaPositive := h.sigmaPositive
  radiusNonneg := h.radiusNonneg
  varianceProxyNormBound := h.varianceProxyNormBound
  cfcPrimitive :=
    fun i omega =>
      bernsteinMatrixExp_le_quadratic ((negRandomMatrixFamily A) i omega)
        (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg
  troppPrimitive := h.troppPrimitive

end MatrixBernsteinNegativeSideTroppAssumptions

/-- Named scalar RHS for optimized one-sided Matrix Bernstein wrappers.

The dimension parameter is the actual matrix dimension. Nonempty wrappers for
`RandomMatrix Omega (n + 1) (n + 1)` therefore pass `n + 1`; arbitrary
operator-norm wrappers pass their actual dimension `n`. -/
abbrev matrixBernsteinOptimizedScalarTailRHS
    (dim : Nat) (R t sigmaSq : Real) : ENNReal :=
  ENNReal.ofReal
    ((dim : Real) *
      Real.exp (-(t ^ 2 / (2 * sigmaSq + (2 / 3) * R * t))))

/-- Named scalar RHS for optimized two-sided Matrix Bernstein wrappers. -/
abbrev matrixBernsteinTwoSidedOptimizedScalarTailRHS
    (dim : Nat) (R Rneg t sigmaSq sigmaSqNeg : Real) : ENNReal :=
  matrixBernsteinOptimizedScalarTailRHS dim R t sigmaSq +
    matrixBernsteinOptimizedScalarTailRHS dim Rneg t sigmaSqNeg

/-- Thin high-level bounded Matrix Bernstein trace-mgf wrapper from the
finite-family Tropp typed primitive.

This theorem does not prove the finite-family Tropp/Lieb primitive. It
specializes the semantic wrapper to the canonical variance proxy
`matrixVarianceProxy P A`, which is definitionally the RHS used by
`matrixBernsteinTraceMGFWithCoeffStatement`. -/
theorem matrixBernsteinTraceMGFWithCoeff_of_troppMasterTraceMGFFiniteFamily
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n)
    (K : I -> Matrix (Fin n) (Fin n) Real) (theta R : Real)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) A K (matrixVarianceProxy P A) theta R)
    (hRand : forall i, IsRandomMatrix P (A i))
    (hSA : forall i, RandomSelfAdjointMatrix P (A i))
    (hIndep : ProbabilityTheory.iIndepFun A P)
    (hExpInt :
      forall i,
        IntegrableRandomMatrix P (matrixExpScaledFamily A theta i))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum A) theta))
    (hKSA : forall i, IsSelfAdjointMatrix (K i))
    (hVSA : IsSelfAdjointMatrix (matrixVarianceProxy P A))
    (hR : 0 <= R)
    (hRange : abs theta * R < 3)
    (hMGF :
      forall i,
        MatrixLE
          (matrixExpect P (matrixExpScaledFamily A theta i))
          (matrixExp (K i)))
    (hNorm :
      Finset.univ.sum (fun i : I => K i) =
        SMul.smul (bernsteinMGFCoeff theta R) (matrixVarianceProxy P A)) :
    matrixBernsteinTraceMGFWithCoeffStatement P A theta R := by
  have hExpInt' :
      forall i,
        IntegrableRandomMatrix P
          (fun omega => matrixExp (SMul.smul theta (A i omega))) := by
    intro i
    change IntegrableRandomMatrix P (matrixExpScaledFamily A theta i)
    exact hExpInt i
  have hMGF' :
      forall i,
        MatrixLE
          (matrixExpect P
            (fun omega => matrixExp (SMul.smul theta (A i omega))))
          (matrixExp (K i)) := by
    intro i
    change MatrixLE
      (matrixExpect P (matrixExpScaledFamily A theta i)) (matrixExp (K i))
    exact hMGF i
  exact
    traceMGFBernsteinVarianceProxyBound_of_troppMasterTraceMGFFiniteFamily
      A K (matrixVarianceProxy P A) theta R hTropp hRand hSA hIndep hExpInt'
      hTraceInt hKSA hVSA hR hRange hMGF' hNorm

/-- Bounded Matrix Bernstein trace-mgf provider under explicit primitive
assumptions.

This theorem packages the ordinary finite-family Matrix Bernstein assumptions
with the explicit finite-family Tropp/Lieb primitive. The pointwise Bernstein
functional-calculus primitive can now be supplied by
`bernsteinMatrixExp_le_quadratic`, but this legacy wrapper keeps the explicit
field for compatibility. -/
theorem matrixBernsteinTraceMGFWithCoeff_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n) (theta R : Real)
    (hCentered : CenteredSelfAdjointRandomMatrixFamily P A)
    (hIndepSA : IndependentSelfAdjointRandomMatrices P A)
    (hIntX : forall i, IntegrableRandomMatrix P (A i))
    (hIntSq : forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i)))
    (hExpInt :
      forall i,
        IntegrableRandomMatrix P (matrixExpScaledFamily A theta i))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum A) theta))
    (hBound : PointwiseOperatorNormBound A R)
    (hR : 0 <= R)
    (hRange : abs theta * R < 3)
    (hCFC :
      forall i omega,
        bernsteinMatrixExpLeQuadraticStatement (A i omega) theta R)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) A (bernsteinSecondMomentComparisonFamily P A theta R)
        (matrixVarianceProxy P A) theta R) :
    matrixBernsteinTraceMGFWithCoeffStatement P A theta R := by
  have hFam : SelfAdjointRandomMatrixFamily P A := hCentered.1
  have hRand : forall i, IsRandomMatrix P (A i) := hFam.1
  have hSA : forall i, RandomSelfAdjointMatrix P (A i) := hFam.2
  have hMeanZero : forall i, matrixExpect P (A i) = 0 := hCentered.2
  have hIndep : ProbabilityTheory.iIndepFun A P := hIndepSA.2
  have hKSA :
      forall i,
        IsSelfAdjointMatrix
          (bernsteinSecondMomentComparisonFamily P A theta R i) := by
    intro i
    change IsSelfAdjointMatrix
      (SMul.smul (bernsteinMGFCoeff theta R) (matrixSecondMoment P (A i)))
    exact isSelfAdjointMatrix_smul (bernsteinMGFCoeff theta R)
      (isSelfAdjointMatrix_matrixSecondMoment (hSA i))
  have hVSA : IsSelfAdjointMatrix (matrixVarianceProxy P A) :=
    isSelfAdjointMatrix_matrixVarianceProxy P hSA
  have hMGF :
      forall i,
        MatrixLE
          (matrixExpect P (matrixExpScaledFamily A theta i))
          (matrixExp
            (SMul.smul (bernsteinMGFCoeff theta R)
              (matrixSecondMoment P (A i)))) := by
    intro i
    change MatrixLE
      (matrixExpect P
        (fun omega => matrixExp (SMul.smul theta (A i omega))))
      (matrixExp
        (SMul.smul (bernsteinMGFCoeff theta R)
          (matrixSecondMoment P (A i))))
    exact
      singleSummandMatrixMGFVarianceProxy_of_bernsteinMatrixExp_le_quadratic
        (A i) (matrixSecondMoment P (A i)) theta R (hCFC i)
        (hRand i) (hSA i) (hIntX i) (hIntSq i)
        (by
          change IntegrableRandomMatrix P (matrixExpScaledFamily A theta i)
          exact hExpInt i)
        (hMeanZero i) (hBound i) hR hRange
        (isSelfAdjointMatrix_matrixSecondMoment (hSA i))
        (isPSD_matrixSecondMoment_of_selfAdjoint (hSA i) (hIntSq i))
        (matrixLE_refl (matrixSecondMoment P (A i)))
  have hNorm :
      Finset.univ.sum
          (bernsteinSecondMomentComparisonFamily P A theta R) =
        SMul.smul (bernsteinMGFCoeff theta R) (matrixVarianceProxy P A) := by
    change
      Finset.univ.sum
          (fun i : I =>
            SMul.smul (bernsteinMGFCoeff theta R)
              (matrixSecondMoment P (A i))) =
        SMul.smul (bernsteinMGFCoeff theta R)
          (Finset.univ.sum fun i : I => matrixSecondMoment P (A i))
    exact (Finset.smul_sum (s := Finset.univ)
      (f := fun i : I => matrixSecondMoment P (A i))
      (r := bernsteinMGFCoeff theta R)).symm
  exact
    matrixBernsteinTraceMGFWithCoeff_of_troppMasterTraceMGFFiniteFamily
      A (bernsteinSecondMomentComparisonFamily P A theta R)
      theta R hTropp hRand hSA hIndep hExpInt hTraceInt hKSA hVSA hR hRange
      hMGF hNorm

/-- Bounded Matrix Bernstein trace-mgf provider under the finite-family Tropp
primitive, with the pointwise Bernstein CFC primitive supplied by
`bernsteinMatrixExp_le_quadratic`.

This is the preferred wrapper when the only remaining hard analytic input is
the finite-family Tropp/Lieb primitive. It still does not prove Tropp/Lieb,
trace-exp integrability, variance-proxy control, or a Matrix Bernstein tail
bound. -/
theorem matrixBernsteinTraceMGFWithCoeff_under_troppPrimitive
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n) (theta R : Real)
    (hCentered : CenteredSelfAdjointRandomMatrixFamily P A)
    (hIndepSA : IndependentSelfAdjointRandomMatrices P A)
    (hIntX : forall i, IntegrableRandomMatrix P (A i))
    (hIntSq : forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i)))
    (hExpInt :
      forall i,
        IntegrableRandomMatrix P (matrixExpScaledFamily A theta i))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum A) theta))
    (hBound : PointwiseOperatorNormBound A R)
    (hR : 0 <= R)
    (hRange : abs theta * R < 3)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) A (bernsteinSecondMomentComparisonFamily P A theta R)
        (matrixVarianceProxy P A) theta R) :
    matrixBernsteinTraceMGFWithCoeffStatement P A theta R :=
  matrixBernsteinTraceMGFWithCoeff_under_primitives
    A theta R hCentered hIndepSA hIntX hIntSq hExpInt hTraceInt hBound hR
    hRange (fun i omega => bernsteinMatrixExp_le_quadratic (A i omega) theta R)
    hTropp

/-- Explicit-theta quadratic-form Matrix Bernstein upper-tail wrapper under
explicit primitive assumptions.

This theorem only connects the bounded trace-MGF provider under primitives to
the existing lintegral Laplace route. The right-hand side remains the
trace-exponential expression; no dimension/norm reduction, theta optimization,
operator-norm tail theorem, Tropp/Lieb proof, or Bernstein CFC proof is
performed here. -/
theorem matrixBernsteinQuadraticFormUpperTailWithCoeff_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega (n + 1) (n + 1))
    (theta R t : Real)
    (hCentered : CenteredSelfAdjointRandomMatrixFamily P A)
    (hIndepSA : IndependentSelfAdjointRandomMatrices P A)
    (hIntX : forall i, IntegrableRandomMatrix P (A i))
    (hIntSq : forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i)))
    (hExpInt :
      forall i,
        IntegrableRandomMatrix P (matrixExpScaledFamily A theta i))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum A) theta))
    (hBound : PointwiseOperatorNormBound A R)
    (hR : 0 <= R)
    (hRange : abs theta * R < 3)
    (hTheta : 0 < theta)
    (hCFC :
      forall i omega,
        bernsteinMatrixExpLeQuadraticStatement (A i omega) theta R)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) A (bernsteinSecondMomentComparisonFamily P A theta R)
        (matrixVarianceProxy P A) theta R) :
    P (quadraticFormUpperTailEvent (randomMatrixSum A) t) <=
      ENNReal.ofReal (Real.exp (-(theta * t))) *
        ENNReal.ofReal
          (traceMatrixExp
            (SMul.smul (bernsteinMGFCoeff theta R)
              (matrixVarianceProxy P A))) := by
  have hReal :
      matrixBernsteinTraceMGFWithCoeffStatement P A theta R :=
    matrixBernsteinTraceMGFWithCoeff_under_primitives
      A theta R hCentered hIndepSA hIntX hIntSq hExpInt hTraceInt hBound
      hR hRange hCFC hTropp
  have hY : RandomSelfAdjointMatrix P (randomMatrixSum A) :=
    randomSelfAdjointMatrix_sum hCentered.1.2
  have hLInt :
      TraceMGFBernsteinVarianceProxyBoundLIntegral P (randomMatrixSum A)
        (matrixVarianceProxy P A) theta R :=
    traceMGFBernsteinVarianceProxyBoundLIntegral_of_traceMGFBernsteinVarianceProxyBound
      (randomMatrixSum A) (matrixVarianceProxy P A) theta R hY hTraceInt hReal
  have hMeas :
      AEMeasurable
        (fun omega =>
          ENNReal.ofReal
            (traceExpIntegrand (randomMatrixSum A) theta omega)) P :=
    hTraceInt.aemeasurable.ennreal_ofReal
  have hSubset :
      quadraticFormUpperTailEvent (randomMatrixSum A) t ⊆
        traceExpThresholdEvent (randomMatrixSum A) theta t :=
    quadraticFormUpperTailEvent_subset_traceExpThresholdEvent_of_traceExpDominates
      (randomMatrixSum A) theta t
      (traceExpDominatesQuadraticFormUpperTail_of_randomSelfAdjoint
        (randomMatrixSum A) theta t hY hTheta.le)
  exact
    quadraticFormUpperTail_laplace_bound_of_traceMGFBernsteinVarianceProxyBoundLIntegral
      (randomMatrixSum A) (matrixVarianceProxy P A) theta t R hMeas hSubset hLInt

/-- Variance-proxy specialization of the deterministic trace-exponential
dimension bound with the bounded Matrix Bernstein coefficient.

This only reduces the trace-exponential RHS to a scalar dimension/norm RHS. It
does not apply the tail theorem, multiply by `exp (-theta * t)`, or optimize
theta. -/
theorem traceMatrixExp_bernsteinMGFCoeff_matrixVarianceProxy_le_card_exp
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega (n + 1) (n + 1))
    (theta R sigmaSq : Real)
    (hSA : forall i, RandomSelfAdjointMatrix P (A i))
    (hRange : abs theta * R < 3)
    (hNorm : MatrixVarianceProxyNormBound P A sigmaSq) :
    traceMatrixExp
      (bernsteinMGFCoeff theta R • matrixVarianceProxy P A) <=
      (n + 1 : Real) * Real.exp (bernsteinMGFCoeff theta R * sigmaSq) := by
  let hV : IsSelfAdjointMatrix (matrixVarianceProxy P A) :=
    isSelfAdjointMatrix_matrixVarianceProxy P hSA
  have hNorm' :
      deterministicOperatorNorm (matrixVarianceProxy P A) <= sigmaSq := by
    simpa [MatrixVarianceProxyNormBound, matrixVarianceProxyNorm,
      deterministicMatrixVarianceProxyNorm] using hNorm
  have hSpec :
      lambdaMaxOrdered (matrixVarianceProxy P A) hV <= sigmaSq :=
    (lambdaMaxOrdered_le_deterministicOperatorNorm hV).trans hNorm'
  exact
    traceMatrixExp_smul_le_card_exp_of_lambdaMaxOrdered_le
      (bernsteinMGFCoeff theta R) sigmaSq
      (bernsteinMGFCoeff_nonneg hRange) hV hSpec

/-- Explicit-theta quadratic-form Matrix Bernstein upper-tail wrapper under
explicit primitive assumptions, with the trace-exponential RHS reduced to the
scalar dimension/norm form.

The right-hand side is intentionally left as the unnormalized product
`exp (-(theta * t)) * ((n + 1) * exp (bernsteinMGFCoeff theta R * sigmaSq))`.
No exponent-add normalization, theta optimization, operator-norm tail theorem,
Tropp/Lieb proof, or Bernstein CFC proof is performed here. -/
theorem matrixBernsteinQuadraticFormUpperTailScalarRHSWithCoeff_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega (n + 1) (n + 1))
    (theta R t sigmaSq : Real)
    (hCentered : CenteredSelfAdjointRandomMatrixFamily P A)
    (hIndepSA : IndependentSelfAdjointRandomMatrices P A)
    (hIntX : forall i, IntegrableRandomMatrix P (A i))
    (hIntSq : forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i)))
    (hExpInt :
      forall i,
        IntegrableRandomMatrix P (matrixExpScaledFamily A theta i))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum A) theta))
    (hBound : PointwiseOperatorNormBound A R)
    (hR : 0 <= R)
    (hRange : abs theta * R < 3)
    (hTheta : 0 < theta)
    (hNorm : MatrixVarianceProxyNormBound P A sigmaSq)
    (hCFC :
      forall i omega,
        bernsteinMatrixExpLeQuadraticStatement (A i omega) theta R)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) A (bernsteinSecondMomentComparisonFamily P A theta R)
        (matrixVarianceProxy P A) theta R) :
    P (quadraticFormUpperTailEvent (randomMatrixSum A) t) <=
      ENNReal.ofReal
        (Real.exp (-(theta * t)) *
          ((n + 1 : Real) *
            Real.exp (bernsteinMGFCoeff theta R * sigmaSq))) := by
  have hTail :=
    matrixBernsteinQuadraticFormUpperTailWithCoeff_under_primitives
      A theta R t hCentered hIndepSA hIntX hIntSq hExpInt hTraceInt hBound
      hR hRange hTheta hCFC hTropp
  have hDim :
      traceMatrixExp
        (SMul.smul (bernsteinMGFCoeff theta R) (matrixVarianceProxy P A)) <=
        (n + 1 : Real) *
          Real.exp (bernsteinMGFCoeff theta R * sigmaSq) :=
    traceMatrixExp_bernsteinMGFCoeff_matrixVarianceProxy_le_card_exp
      A theta R sigmaSq hCentered.1.2 hRange hNorm
  have hDimENN :
      ENNReal.ofReal
        (traceMatrixExp
          (SMul.smul (bernsteinMGFCoeff theta R)
            (matrixVarianceProxy P A))) <=
        ENNReal.ofReal
          ((n + 1 : Real) *
            Real.exp (bernsteinMGFCoeff theta R * sigmaSq)) :=
    ENNReal.ofReal_le_ofReal hDim
  calc
    P (quadraticFormUpperTailEvent (randomMatrixSum A) t)
        <= ENNReal.ofReal (Real.exp (-(theta * t))) *
          ENNReal.ofReal
            (traceMatrixExp
              (SMul.smul (bernsteinMGFCoeff theta R)
                (matrixVarianceProxy P A))) := hTail
    _ <= ENNReal.ofReal (Real.exp (-(theta * t))) *
          ENNReal.ofReal
            ((n + 1 : Real) *
              Real.exp (bernsteinMGFCoeff theta R * sigmaSq)) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_right hDimENN (ENNReal.ofReal (Real.exp (-(theta * t))))
    _ = ENNReal.ofReal
          (Real.exp (-(theta * t)) *
            ((n + 1 : Real) *
              Real.exp (bernsteinMGFCoeff theta R * sigmaSq))) :=
        (ENNReal.ofReal_mul (le_of_lt (Real.exp_pos (-(theta * t))))).symm

/-- Explicit-theta quadratic-form Matrix Bernstein upper-tail wrapper under
explicit primitive assumptions, with the scalar RHS normalized into compact
exponential-add form.

This is only a normalization wrapper around
`matrixBernsteinQuadraticFormUpperTailScalarRHSWithCoeff_under_primitives`.
It does not optimize theta, prove an operator-norm tail theorem, or prove the
Tropp/Lieb or Bernstein functional-calculus primitives. -/
theorem matrixBernsteinQuadraticFormUpperTailScalarExpRHSWithCoeff_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega (n + 1) (n + 1))
    (theta R t sigmaSq : Real)
    (hCentered : CenteredSelfAdjointRandomMatrixFamily P A)
    (hIndepSA : IndependentSelfAdjointRandomMatrices P A)
    (hIntX : forall i, IntegrableRandomMatrix P (A i))
    (hIntSq : forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i)))
    (hExpInt :
      forall i,
        IntegrableRandomMatrix P (matrixExpScaledFamily A theta i))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum A) theta))
    (hBound : PointwiseOperatorNormBound A R)
    (hR : 0 <= R)
    (hRange : abs theta * R < 3)
    (hTheta : 0 < theta)
    (hNorm : MatrixVarianceProxyNormBound P A sigmaSq)
    (hCFC :
      forall i omega,
        bernsteinMatrixExpLeQuadraticStatement (A i omega) theta R)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) A (bernsteinSecondMomentComparisonFamily P A theta R)
        (matrixVarianceProxy P A) theta R) :
    P (quadraticFormUpperTailEvent (randomMatrixSum A) t) <=
      ENNReal.ofReal
        ((n + 1 : Real) *
          Real.exp (-(theta * t) + bernsteinMGFCoeff theta R * sigmaSq)) := by
  have hUnnormalized :=
    matrixBernsteinQuadraticFormUpperTailScalarRHSWithCoeff_under_primitives
      A theta R t sigmaSq hCentered hIndepSA hIntX hIntSq hExpInt hTraceInt
      hBound hR hRange hTheta hNorm hCFC hTropp
  convert hUnnormalized using 1
  rw [Real.exp_add]
  ring_nf

/-- Theta-optimized quadratic-form Matrix Bernstein upper-tail wrapper under
explicit primitive assumptions.

This packages the explicit-theta scalar RHS using the conservative Bernstein
choice `theta = t / (sigmaSq + R * t / 3)`, yielding the usual denominator
exponent `-t^2 / (2*sigmaSq + (2/3)*R*t)`. It remains a one-sided
quadratic-form theorem under explicit Tropp/Lieb and Bernstein CFC primitives;
it is not an operator-norm Matrix Bernstein theorem. -/
theorem matrixBernsteinQuadraticFormUpperTailOptimizedScalarRHSWithCoeff_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega (n + 1) (n + 1))
    (R t sigmaSq : Real)
    (hCentered : CenteredSelfAdjointRandomMatrixFamily P A)
    (hIndepSA : IndependentSelfAdjointRandomMatrices P A)
    (hIntX : forall i, IntegrableRandomMatrix P (A i))
    (hIntSq : forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i)))
    (hExpInt :
      forall i,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily A (bernsteinThetaChoice t sigmaSq R) i))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum A)
          (bernsteinThetaChoice t sigmaSq R)))
    (hBound : PointwiseOperatorNormBound A R)
    (hSigma : 0 < sigmaSq)
    (hR : 0 <= R)
    (ht : 0 < t)
    (hNorm : MatrixVarianceProxyNormBound P A sigmaSq)
    (hCFC :
      forall i omega,
        bernsteinMatrixExpLeQuadraticStatement (A i omega)
          (bernsteinThetaChoice t sigmaSq R) R)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) A
        (bernsteinSecondMomentComparisonFamily P A
          (bernsteinThetaChoice t sigmaSq R) R)
        (matrixVarianceProxy P A) (bernsteinThetaChoice t sigmaSq R) R) :
    P (quadraticFormUpperTailEvent (randomMatrixSum A) t) <=
      ENNReal.ofReal
        ((n + 1 : Real) *
          Real.exp (-(t ^ 2 / (2 * sigmaSq + (2 / 3) * R * t)))) := by
  let theta := bernsteinThetaChoice t sigmaSq R
  have hden : 0 < sigmaSq + R * t / 3 :=
    bernsteinThetaChoice_den_pos hSigma hR ht.le
  have hTheta : 0 < theta := by
    simpa [theta] using bernsteinThetaChoice_pos ht hden
  have hRange : abs theta * R < 3 := by
    simpa [theta] using bernsteinThetaChoice_range hSigma hR ht.le
  have hExpIntTheta :
      forall i,
        IntegrableRandomMatrix P (matrixExpScaledFamily A theta i) := by
    simpa [theta] using hExpInt
  have hTraceIntTheta :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum A) theta) := by
    exact hTraceInt
  have hCFCTheta :
      forall i omega,
        bernsteinMatrixExpLeQuadraticStatement (A i omega) theta R := by
    exact hCFC
  have hTroppTheta :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) A (bernsteinSecondMomentComparisonFamily P A theta R)
        (matrixVarianceProxy P A) theta R := by
    simpa [theta] using hTropp
  have hTail :=
    matrixBernsteinQuadraticFormUpperTailScalarExpRHSWithCoeff_under_primitives
      A theta R t sigmaSq hCentered hIndepSA hIntX hIntSq hExpIntTheta
      hTraceIntTheta hBound hR hRange hTheta hNorm hCFCTheta hTroppTheta
  simpa [theta, bernsteinThetaChoice_exponent_eq hSigma hR ht.le] using hTail

/-- Optimized one-sided quadratic-form Matrix Bernstein wrapper using the
packaged positive-side assumptions. -/
theorem matrixBernsteinQuadraticFormUpperTailOptimizedScalarRHSWithCoeff_of_assumptions
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega (n + 1) (n + 1))
    (R t sigmaSq : Real)
    (h : MatrixBernsteinPositiveSideAssumptions (P := P) A R t sigmaSq) :
    P (quadraticFormUpperTailEvent (randomMatrixSum A) t) <=
      matrixBernsteinOptimizedScalarTailRHS (n + 1) R t sigmaSq := by
  simpa [matrixBernsteinOptimizedScalarTailRHS, Nat.cast_add, Nat.cast_one] using
    (matrixBernsteinQuadraticFormUpperTailOptimizedScalarRHSWithCoeff_under_primitives
      A R t sigmaSq
      h.centered
      h.independentSelfAdjoint
      h.integrable
      h.squareIntegrable
      h.expIntegrable
      h.traceExpIntegrable
      h.operatorNormBound
      h.sigmaPositive
      h.radiusNonneg
      h.deviationPositive
      h.varianceProxyNormBound
      h.cfcPrimitive
      h.troppPrimitive)

/-- Preferred optimized one-sided quadratic-form Matrix Bernstein wrapper after
the Bernstein CFC hardbone leaf.

This consumes the CFC-free positive-side bundle and reuses the compatibility
wrapper internally. The remaining hard primitive is the finite-family Tropp/Lieb
trace-MGF statement carried by the bundle. -/
theorem matrixBernsteinQuadraticFormUpperTailOptimizedScalarRHSWithCoeff_of_troppAssumptions
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega (n + 1) (n + 1))
    (R t sigmaSq : Real)
    (h :
      MatrixBernsteinPositiveSideTroppAssumptions
        (P := P) A R t sigmaSq) :
    P (quadraticFormUpperTailEvent (randomMatrixSum A) t) <=
      matrixBernsteinOptimizedScalarTailRHS (n + 1) R t sigmaSq :=
  matrixBernsteinQuadraticFormUpperTailOptimizedScalarRHSWithCoeff_of_assumptions
    (P := P) A R t sigmaSq h.toPositiveSideAssumptions

/-- Two-sided quadratic-form Matrix Bernstein wrapper under explicit primitive
assumptions for both `A` and the pointwise negated summand family.

This combines the existing optimized upper-tail theorem for `A` with the same
theorem applied to `negRandomMatrixFamily A`, then uses the finite union
bound for the existing `twoSidedQuadraticFormTailEvent`. It does not prove any
negation transfer for independence, variance proxies, CFC primitives, Tropp
primitives, or integrability. -/
theorem matrixBernsteinTwoSidedQuadraticFormTailOptimizedScalarRHSWithCoeff_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega (n + 1) (n + 1))
    (R Rneg t sigmaSq sigmaSqNeg : Real)
    (hCentered : CenteredSelfAdjointRandomMatrixFamily P A)
    (hIndepSA : IndependentSelfAdjointRandomMatrices P A)
    (hIntX : forall i, IntegrableRandomMatrix P (A i))
    (hIntSq : forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i)))
    (hExpInt :
      forall i,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily A (bernsteinThetaChoice t sigmaSq R) i))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum A)
          (bernsteinThetaChoice t sigmaSq R)))
    (hBound : PointwiseOperatorNormBound A R)
    (hSigma : 0 < sigmaSq)
    (hR : 0 <= R)
    (ht : 0 < t)
    (hNorm : MatrixVarianceProxyNormBound P A sigmaSq)
    (hCFC :
      forall i omega,
        bernsteinMatrixExpLeQuadraticStatement (A i omega)
          (bernsteinThetaChoice t sigmaSq R) R)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) A
        (bernsteinSecondMomentComparisonFamily P A
          (bernsteinThetaChoice t sigmaSq R) R)
        (matrixVarianceProxy P A) (bernsteinThetaChoice t sigmaSq R) R)
    (hCenteredNeg :
      CenteredSelfAdjointRandomMatrixFamily P
        (negRandomMatrixFamily A))
    (hIndepSANeg :
      IndependentSelfAdjointRandomMatrices P
        (negRandomMatrixFamily A))
    (hIntXNeg :
      forall i,
        IntegrableRandomMatrix P
          ((negRandomMatrixFamily A) i))
    (hIntSqNeg :
      forall i,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((negRandomMatrixFamily A) i)))
    (hExpIntNeg :
      forall i,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (negRandomMatrixFamily A)
            (bernsteinThetaChoice t sigmaSqNeg Rneg) i))
    (hTraceIntNeg :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (randomMatrixSum
            (negRandomMatrixFamily A))
          (bernsteinThetaChoice t sigmaSqNeg Rneg)))
    (hBoundNeg :
      PointwiseOperatorNormBound
        (negRandomMatrixFamily A) Rneg)
    (hSigmaNeg : 0 < sigmaSqNeg)
    (hRNeg : 0 <= Rneg)
    (hNormNeg :
      MatrixVarianceProxyNormBound P
        (negRandomMatrixFamily A) sigmaSqNeg)
    (hCFCNeg :
      forall i omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((negRandomMatrixFamily A) i omega)
          (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg)
    (hTroppNeg :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) (negRandomMatrixFamily A)
        (bernsteinSecondMomentComparisonFamily P
          (negRandomMatrixFamily A)
          (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg)
        (matrixVarianceProxy P
          (negRandomMatrixFamily A))
        (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg) :
    P (twoSidedQuadraticFormTailEvent (randomMatrixSum A) t) <=
      ENNReal.ofReal
        ((n + 1 : Real) *
          Real.exp (-(t ^ 2 / (2 * sigmaSq + (2 / 3) * R * t)))) +
        ENNReal.ofReal
          ((n + 1 : Real) *
            Real.exp (-(t ^ 2 / (2 * sigmaSqNeg + (2 / 3) * Rneg * t)))) := by
  let Aneg : I -> RandomMatrix Omega (n + 1) (n + 1) :=
    negRandomMatrixFamily A
  have hUpper :
      P (quadraticFormUpperTailEvent (randomMatrixSum A) t) <=
        ENNReal.ofReal
          ((n + 1 : Real) *
            Real.exp (-(t ^ 2 / (2 * sigmaSq + (2 / 3) * R * t)))) :=
    matrixBernsteinQuadraticFormUpperTailOptimizedScalarRHSWithCoeff_under_primitives
      (P := P) (A := A) (R := R) (t := t) (sigmaSq := sigmaSq)
      hCentered hIndepSA hIntX hIntSq hExpInt hTraceInt hBound
      hSigma hR ht hNorm hCFC hTropp
  have hUpperNeg :
      P (quadraticFormUpperTailEvent (randomMatrixSum Aneg) t) <=
        ENNReal.ofReal
          ((n + 1 : Real) *
            Real.exp (-(t ^ 2 / (2 * sigmaSqNeg + (2 / 3) * Rneg * t)))) :=
    matrixBernsteinQuadraticFormUpperTailOptimizedScalarRHSWithCoeff_under_primitives
      (P := P) (A := Aneg) (R := Rneg) (t := t) (sigmaSq := sigmaSqNeg)
      (by
        change CenteredSelfAdjointRandomMatrixFamily P
          (negRandomMatrixFamily A)
        exact hCenteredNeg)
      (by
        change IndependentSelfAdjointRandomMatrices P
          (negRandomMatrixFamily A)
        exact hIndepSANeg)
      (by
        change forall i,
          IntegrableRandomMatrix P
            ((negRandomMatrixFamily A) i)
        exact hIntXNeg)
      (by
        change forall i,
          IntegrableRandomMatrix P
            (randomMatrixSquare
              ((negRandomMatrixFamily A) i))
        exact hIntSqNeg)
      (by
        change forall i,
          IntegrableRandomMatrix P
            (matrixExpScaledFamily
              (negRandomMatrixFamily A)
              (bernsteinThetaChoice t sigmaSqNeg Rneg) i)
        exact hExpIntNeg)
      (by
        change IntegrableRealRandomVariable P
          (traceExpIntegrand
            (randomMatrixSum
              (negRandomMatrixFamily A))
            (bernsteinThetaChoice t sigmaSqNeg Rneg))
        exact hTraceIntNeg)
      (by
        change PointwiseOperatorNormBound
          (negRandomMatrixFamily A) Rneg
        exact hBoundNeg)
      hSigmaNeg hRNeg ht
      (by
        change MatrixVarianceProxyNormBound P
          (negRandomMatrixFamily A) sigmaSqNeg
        exact hNormNeg)
      (by
        change forall i omega,
          bernsteinMatrixExpLeQuadraticStatement
            ((negRandomMatrixFamily A) i omega)
            (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg
        exact hCFCNeg)
      (by
        change troppMasterTraceMGFFiniteFamilyStatement
          (P := P) (negRandomMatrixFamily A)
          (bernsteinSecondMomentComparisonFamily P
            (negRandomMatrixFamily A)
            (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg)
          (matrixVarianceProxy P
            (negRandomMatrixFamily A))
          (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg
        exact hTroppNeg)
  have hNegSum :
      randomMatrixSum Aneg =
        fun omega : Omega => -(randomMatrixSum A omega) := by
    funext omega
    ext r c
    dsimp [randomMatrixSum, Aneg]
    rw [Matrix.sum_apply]
    change (Finset.univ.sum fun i : I => (-(A i omega)) r c) =
      -((Finset.univ.sum fun i : I => A i omega) r c)
    rw [Matrix.sum_apply]
    change (Finset.univ.sum fun i : I => -(A i omega r c)) =
      -(Finset.univ.sum fun i : I => A i omega r c)
    exact
      Finset.sum_neg_distrib (s := (Finset.univ : Finset I))
        (f := fun i : I => A i omega r c)
  have hLowerSubset :
      quadraticFormLowerTailEvent (randomMatrixSum A) (-t) ⊆
        quadraticFormUpperTailEvent (randomMatrixSum Aneg) t := by
    simpa [hNegSum] using
      quadraticFormLowerTailEvent_subset_quadraticFormUpperTailEvent_neg
        (randomMatrixSum A) t
  have hLower :
      P (quadraticFormLowerTailEvent (randomMatrixSum A) (-t)) <=
        ENNReal.ofReal
          ((n + 1 : Real) *
            Real.exp (-(t ^ 2 / (2 * sigmaSqNeg + (2 / 3) * Rneg * t)))) :=
    (measure_mono hLowerSubset).trans hUpperNeg
  calc
    P (twoSidedQuadraticFormTailEvent (randomMatrixSum A) t)
        <= P (quadraticFormUpperTailEvent (randomMatrixSum A) t) +
          P (quadraticFormLowerTailEvent (randomMatrixSum A) (-t)) := by
            simpa [twoSidedQuadraticFormTailEvent] using
              (measure_union_le
                (quadraticFormUpperTailEvent (randomMatrixSum A) t)
                (quadraticFormLowerTailEvent (randomMatrixSum A) (-t)) :
                  P (quadraticFormUpperTailEvent (randomMatrixSum A) t ∪
                    quadraticFormLowerTailEvent (randomMatrixSum A) (-t)) <=
                    P (quadraticFormUpperTailEvent (randomMatrixSum A) t) +
                      P (quadraticFormLowerTailEvent (randomMatrixSum A) (-t)))
    _ <= ENNReal.ofReal
          ((n + 1 : Real) *
            Real.exp (-(t ^ 2 / (2 * sigmaSq + (2 / 3) * R * t)))) +
        ENNReal.ofReal
          ((n + 1 : Real) *
            Real.exp (-(t ^ 2 / (2 * sigmaSqNeg + (2 / 3) * Rneg * t)))) := by
            exact add_le_add hUpper hLower

/-- Two-sided quadratic-form Matrix Bernstein wrapper using packaged
positive- and negative-side assumptions.

This is the public convenience wrapper for the optimized primitive theorem.
It keeps the same mathematical content, but makes examples and downstream code
reuse one pair of named assumption bundles instead of repeating the full
positive and `negRandomMatrixFamily` hypothesis lists. -/
theorem matrixBernsteinTwoSidedQuadraticFormTailOptimizedScalarRHSWithCoeff_of_assumptions
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega (n + 1) (n + 1))
    (R Rneg t sigmaSq sigmaSqNeg : Real)
    (hPos : MatrixBernsteinPositiveSideAssumptions (P := P) A R t sigmaSq)
    (hNeg :
      MatrixBernsteinNegativeSideAssumptions (P := P) A Rneg t sigmaSqNeg) :
    P (twoSidedQuadraticFormTailEvent (randomMatrixSum A) t) <=
      matrixBernsteinTwoSidedOptimizedScalarTailRHS
        (n + 1) R Rneg t sigmaSq sigmaSqNeg := by
  simpa [matrixBernsteinTwoSidedOptimizedScalarTailRHS,
    matrixBernsteinOptimizedScalarTailRHS, Nat.cast_add, Nat.cast_one] using
    (matrixBernsteinTwoSidedQuadraticFormTailOptimizedScalarRHSWithCoeff_under_primitives
      (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
      (sigmaSq := sigmaSq) (sigmaSqNeg := sigmaSqNeg)
      hPos.centered
      hPos.independentSelfAdjoint
      hPos.integrable
      hPos.squareIntegrable
      hPos.expIntegrable
      hPos.traceExpIntegrable
      hPos.operatorNormBound
      hPos.sigmaPositive
      hPos.radiusNonneg
      hPos.deviationPositive
      hPos.varianceProxyNormBound
      hPos.cfcPrimitive
      hPos.troppPrimitive
      hNeg.centered
      hNeg.independentSelfAdjoint
      hNeg.integrable
      hNeg.squareIntegrable
      hNeg.expIntegrable
      hNeg.traceExpIntegrable
      hNeg.operatorNormBound
      hNeg.sigmaPositive
      hNeg.radiusNonneg
      hNeg.varianceProxyNormBound
      hNeg.cfcPrimitive
      hNeg.troppPrimitive)

/-- Preferred two-sided quadratic-form Matrix Bernstein wrapper after the
Bernstein CFC hardbone leaf.

This consumes CFC-free positive and negative Tropp bundles, converting them to
the older compatibility bundles internally. -/
theorem matrixBernsteinTwoSidedQuadraticFormTailOptimizedScalarRHSWithCoeff_of_troppAssumptions
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega (n + 1) (n + 1))
    (R Rneg t sigmaSq sigmaSqNeg : Real)
    (hPos :
      MatrixBernsteinPositiveSideTroppAssumptions (P := P) A R t sigmaSq)
    (hNeg :
      MatrixBernsteinNegativeSideTroppAssumptions
        (P := P) A Rneg t sigmaSqNeg) :
    P (twoSidedQuadraticFormTailEvent (randomMatrixSum A) t) <=
      matrixBernsteinTwoSidedOptimizedScalarTailRHS
        (n + 1) R Rneg t sigmaSq sigmaSqNeg :=
  matrixBernsteinTwoSidedQuadraticFormTailOptimizedScalarRHSWithCoeff_of_assumptions
    (P := P) A R Rneg t sigmaSq sigmaSqNeg
    hPos.toPositiveSideAssumptions hNeg.toNegativeSideAssumptions

/-- Self-adjoint operator-norm Matrix Bernstein wrapper under the explicit
operator-norm-to-two-sided-quadratic-form bridge.

This is the smallest honest operator-norm tail wrapper currently available:
it reuses the proved two-sided quadratic-form wrapper and assumes the existing
typed bridge `selfAdjointOperatorNormTailViaQuadraticFormStatement` for the
random sum. All analytic primitives and sign-specific assumptions remain
explicit exactly as in the two-sided quadratic-form theorem. -/
theorem matrixBernsteinOpNormTailOptimizedScalarRHSWithCoeff_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega (n + 1) (n + 1))
    (R Rneg t sigmaSq sigmaSqNeg : Real)
    (hCentered : CenteredSelfAdjointRandomMatrixFamily P A)
    (hIndepSA : IndependentSelfAdjointRandomMatrices P A)
    (hIntX : forall i, IntegrableRandomMatrix P (A i))
    (hIntSq : forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i)))
    (hExpInt :
      forall i,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily A (bernsteinThetaChoice t sigmaSq R) i))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum A)
          (bernsteinThetaChoice t sigmaSq R)))
    (hBound : PointwiseOperatorNormBound A R)
    (hSigma : 0 < sigmaSq)
    (hR : 0 <= R)
    (ht : 0 < t)
    (hOperatorBridge :
      selfAdjointOperatorNormTailViaQuadraticFormStatement
        (randomMatrixSum A) t)
    (hNorm : MatrixVarianceProxyNormBound P A sigmaSq)
    (hCFC :
      forall i omega,
        bernsteinMatrixExpLeQuadraticStatement (A i omega)
          (bernsteinThetaChoice t sigmaSq R) R)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) A
        (bernsteinSecondMomentComparisonFamily P A
          (bernsteinThetaChoice t sigmaSq R) R)
        (matrixVarianceProxy P A) (bernsteinThetaChoice t sigmaSq R) R)
    (hCenteredNeg :
      CenteredSelfAdjointRandomMatrixFamily P
        (negRandomMatrixFamily A))
    (hIndepSANeg :
      IndependentSelfAdjointRandomMatrices P
        (negRandomMatrixFamily A))
    (hIntXNeg :
      forall i,
        IntegrableRandomMatrix P
          ((negRandomMatrixFamily A) i))
    (hIntSqNeg :
      forall i,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((negRandomMatrixFamily A) i)))
    (hExpIntNeg :
      forall i,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (negRandomMatrixFamily A)
            (bernsteinThetaChoice t sigmaSqNeg Rneg) i))
    (hTraceIntNeg :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (randomMatrixSum
            (negRandomMatrixFamily A))
          (bernsteinThetaChoice t sigmaSqNeg Rneg)))
    (hBoundNeg :
      PointwiseOperatorNormBound
        (negRandomMatrixFamily A) Rneg)
    (hSigmaNeg : 0 < sigmaSqNeg)
    (hRNeg : 0 <= Rneg)
    (hNormNeg :
      MatrixVarianceProxyNormBound P
        (negRandomMatrixFamily A) sigmaSqNeg)
    (hCFCNeg :
      forall i omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((negRandomMatrixFamily A) i omega)
          (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg)
    (hTroppNeg :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) (negRandomMatrixFamily A)
        (bernsteinSecondMomentComparisonFamily P
          (negRandomMatrixFamily A)
          (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg)
        (matrixVarianceProxy P
          (negRandomMatrixFamily A))
        (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg) :
    P (SelfAdjointOperatorNormTailEvent (randomMatrixSum A) t) <=
      ENNReal.ofReal
        ((n + 1 : Real) *
          Real.exp (-(t ^ 2 / (2 * sigmaSq + (2 / 3) * R * t)))) +
        ENNReal.ofReal
          ((n + 1 : Real) *
            Real.exp (-(t ^ 2 / (2 * sigmaSqNeg + (2 / 3) * Rneg * t)))) := by
  have hSumSelfAdj :
      RandomSelfAdjointMatrix P (randomMatrixSum A) :=
    randomSelfAdjointMatrix_sum (P := P) (A := A) hCentered.1.2
  have hSubset :
      SelfAdjointOperatorNormTailEvent (randomMatrixSum A) t <=
        twoSidedQuadraticFormTailEvent (randomMatrixSum A) t :=
    hOperatorBridge hSumSelfAdj ht.le
  exact (measure_mono hSubset).trans
    (matrixBernsteinTwoSidedQuadraticFormTailOptimizedScalarRHSWithCoeff_under_primitives
      (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
      (sigmaSq := sigmaSq) (sigmaSqNeg := sigmaSqNeg)
      hCentered hIndepSA hIntX hIntSq hExpInt hTraceInt hBound
      hSigma hR ht hNorm hCFC hTropp hCenteredNeg hIndepSANeg
      hIntXNeg hIntSqNeg hExpIntNeg hTraceIntNeg hBoundNeg hSigmaNeg
      hRNeg hNormNeg hCFCNeg hTroppNeg)

/-- Self-adjoint operator-norm Matrix Bernstein wrapper in nonempty square
dimensions under explicit primitive assumptions.

This specializes the conditional operator-norm wrapper to matrices indexed by
`Fin (n + 1)`, where the S3 bridge
`selfAdjointOperatorNormTailViaQuadraticFormStatement_nonempty` discharges the
operator-norm-to-two-sided-quadratic-form event reduction. Variance proxies,
integrability, independence, CFC, and Tropp primitives remain explicit for both
signs. -/
theorem matrixBernsteinOpNormTailOptimizedScalarRHSWithCoeff_nonempty_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega (n + 1) (n + 1))
    (R Rneg t sigmaSq sigmaSqNeg : Real)
    (hCentered : CenteredSelfAdjointRandomMatrixFamily P A)
    (hIndepSA : IndependentSelfAdjointRandomMatrices P A)
    (hIntX : forall i, IntegrableRandomMatrix P (A i))
    (hIntSq : forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i)))
    (hExpInt :
      forall i,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily A (bernsteinThetaChoice t sigmaSq R) i))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum A)
          (bernsteinThetaChoice t sigmaSq R)))
    (hBound : PointwiseOperatorNormBound A R)
    (hSigma : 0 < sigmaSq)
    (hR : 0 <= R)
    (ht : 0 < t)
    (hNorm : MatrixVarianceProxyNormBound P A sigmaSq)
    (hCFC :
      forall i omega,
        bernsteinMatrixExpLeQuadraticStatement (A i omega)
          (bernsteinThetaChoice t sigmaSq R) R)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) A
        (bernsteinSecondMomentComparisonFamily P A
          (bernsteinThetaChoice t sigmaSq R) R)
        (matrixVarianceProxy P A) (bernsteinThetaChoice t sigmaSq R) R)
    (hCenteredNeg :
      CenteredSelfAdjointRandomMatrixFamily P
        (negRandomMatrixFamily A))
    (hIndepSANeg :
      IndependentSelfAdjointRandomMatrices P
        (negRandomMatrixFamily A))
    (hIntXNeg :
      forall i,
        IntegrableRandomMatrix P
          ((negRandomMatrixFamily A) i))
    (hIntSqNeg :
      forall i,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((negRandomMatrixFamily A) i)))
    (hExpIntNeg :
      forall i,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (negRandomMatrixFamily A)
            (bernsteinThetaChoice t sigmaSqNeg Rneg) i))
    (hTraceIntNeg :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (randomMatrixSum
            (negRandomMatrixFamily A))
          (bernsteinThetaChoice t sigmaSqNeg Rneg)))
    (hBoundNeg :
      PointwiseOperatorNormBound
        (negRandomMatrixFamily A) Rneg)
    (hSigmaNeg : 0 < sigmaSqNeg)
    (hRNeg : 0 <= Rneg)
    (hNormNeg :
      MatrixVarianceProxyNormBound P
        (negRandomMatrixFamily A) sigmaSqNeg)
    (hCFCNeg :
      forall i omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((negRandomMatrixFamily A) i omega)
          (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg)
    (hTroppNeg :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) (negRandomMatrixFamily A)
        (bernsteinSecondMomentComparisonFamily P
          (negRandomMatrixFamily A)
          (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg)
        (matrixVarianceProxy P
          (negRandomMatrixFamily A))
        (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg) :
    P (SelfAdjointOperatorNormTailEvent (randomMatrixSum A) t) <=
      ENNReal.ofReal
        ((n + 1 : Real) *
          Real.exp (-(t ^ 2 / (2 * sigmaSq + (2 / 3) * R * t)))) +
        ENNReal.ofReal
          ((n + 1 : Real) *
            Real.exp (-(t ^ 2 / (2 * sigmaSqNeg + (2 / 3) * Rneg * t)))) := by
  exact
    matrixBernsteinOpNormTailOptimizedScalarRHSWithCoeff_under_primitives
      (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
      (sigmaSq := sigmaSq) (sigmaSqNeg := sigmaSqNeg)
      hCentered hIndepSA hIntX hIntSq hExpInt hTraceInt hBound
      hSigma hR ht
      (selfAdjointOperatorNormTailViaQuadraticFormStatement_nonempty
        (randomMatrixSum A) t)
      hNorm hCFC hTropp hCenteredNeg hIndepSANeg hIntXNeg hIntSqNeg
      hExpIntNeg hTraceIntNeg hBoundNeg hSigmaNeg hRNeg hNormNeg
      hCFCNeg hTroppNeg

/-- Arbitrary-dimensional positive-threshold self-adjoint operator-norm Matrix
Bernstein wrapper under explicit primitive assumptions.

The `n = 0` branch is discharged by the zero-dimensional positive-threshold
operator-norm tail emptiness lemma. In successor dimensions, the theorem reuses
the conditional operator-norm wrapper and supplies the corrected positive-
threshold spectral bridge. Variance proxies, integrability, independence, CFC,
and Tropp primitives remain explicit for both signs. -/
theorem matrixBernsteinOpNormTailOptimizedScalarRHSWithCoeff_arbitrary_of_pos_under_primitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n)
    (R Rneg t sigmaSq sigmaSqNeg : Real)
    (hCentered : CenteredSelfAdjointRandomMatrixFamily P A)
    (hIndepSA : IndependentSelfAdjointRandomMatrices P A)
    (hIntX : forall i, IntegrableRandomMatrix P (A i))
    (hIntSq : forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i)))
    (hExpInt :
      forall i,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily A (bernsteinThetaChoice t sigmaSq R) i))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum A)
          (bernsteinThetaChoice t sigmaSq R)))
    (hBound : PointwiseOperatorNormBound A R)
    (hSigma : 0 < sigmaSq)
    (hR : 0 <= R)
    (ht : 0 < t)
    (hNorm : MatrixVarianceProxyNormBound P A sigmaSq)
    (hCFC :
      forall i omega,
        bernsteinMatrixExpLeQuadraticStatement (A i omega)
          (bernsteinThetaChoice t sigmaSq R) R)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) A
        (bernsteinSecondMomentComparisonFamily P A
          (bernsteinThetaChoice t sigmaSq R) R)
        (matrixVarianceProxy P A) (bernsteinThetaChoice t sigmaSq R) R)
    (hCenteredNeg :
      CenteredSelfAdjointRandomMatrixFamily P
        (negRandomMatrixFamily A))
    (hIndepSANeg :
      IndependentSelfAdjointRandomMatrices P
        (negRandomMatrixFamily A))
    (hIntXNeg :
      forall i,
        IntegrableRandomMatrix P
          ((negRandomMatrixFamily A) i))
    (hIntSqNeg :
      forall i,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((negRandomMatrixFamily A) i)))
    (hExpIntNeg :
      forall i,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (negRandomMatrixFamily A)
            (bernsteinThetaChoice t sigmaSqNeg Rneg) i))
    (hTraceIntNeg :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (randomMatrixSum
            (negRandomMatrixFamily A))
          (bernsteinThetaChoice t sigmaSqNeg Rneg)))
    (hBoundNeg :
      PointwiseOperatorNormBound
        (negRandomMatrixFamily A) Rneg)
    (hSigmaNeg : 0 < sigmaSqNeg)
    (hRNeg : 0 <= Rneg)
    (hNormNeg :
      MatrixVarianceProxyNormBound P
        (negRandomMatrixFamily A) sigmaSqNeg)
    (hCFCNeg :
      forall i omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((negRandomMatrixFamily A) i omega)
          (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg)
    (hTroppNeg :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P) (negRandomMatrixFamily A)
        (bernsteinSecondMomentComparisonFamily P
          (negRandomMatrixFamily A)
          (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg)
        (matrixVarianceProxy P
          (negRandomMatrixFamily A))
        (bernsteinThetaChoice t sigmaSqNeg Rneg) Rneg) :
    P (SelfAdjointOperatorNormTailEvent (randomMatrixSum A) t) <=
      ENNReal.ofReal
        ((n : Real) *
          Real.exp (-(t ^ 2 / (2 * sigmaSq + (2 / 3) * R * t)))) +
        ENNReal.ofReal
          ((n : Real) *
            Real.exp (-(t ^ 2 / (2 * sigmaSqNeg + (2 / 3) * Rneg * t)))) := by
  cases n with
  | zero =>
      have hEmpty :
          SelfAdjointOperatorNormTailEvent (randomMatrixSum A) t = ∅ :=
        selfAdjointOperatorNormTailEvent_empty_of_zero_dim_of_pos
          (randomMatrixSum A) ht
      rw [hEmpty, measure_empty]
      exact zero_le
  | succ n =>
      simpa using
        (matrixBernsteinOpNormTailOptimizedScalarRHSWithCoeff_under_primitives
          (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
          (sigmaSq := sigmaSq) (sigmaSqNeg := sigmaSqNeg)
          hCentered hIndepSA hIntX hIntSq hExpInt hTraceInt hBound
          hSigma hR ht
          (selfAdjointOperatorNormTailViaQuadraticFormStatement_of_pos
            (randomMatrixSum A) ht)
          hNorm hCFC hTropp hCenteredNeg hIndepSANeg hIntXNeg hIntSqNeg
          hExpIntNeg hTraceIntNeg hBoundNeg hSigmaNeg hRNeg hNormNeg
          hCFCNeg hTroppNeg)

/-- Arbitrary-dimensional self-adjoint operator-norm Matrix Bernstein wrapper
using packaged positive- and negative-side assumptions.

This is the assumption-bundle variant of
`matrixBernsteinOpNormTailOptimizedScalarRHSWithCoeff_arbitrary_of_pos_under_primitives`.
It is intended as the stable high-level entry point once both sign-specific
Matrix Bernstein primitive packages have already been supplied. -/
theorem matrixBernsteinOpNormTailOptimizedScalarRHSWithCoeff_arbitrary_of_assumptions
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n)
    (R Rneg t sigmaSq sigmaSqNeg : Real)
    (hPos : MatrixBernsteinPositiveSideAssumptions (P := P) A R t sigmaSq)
    (hNeg :
      MatrixBernsteinNegativeSideAssumptions (P := P) A Rneg t sigmaSqNeg) :
    P (SelfAdjointOperatorNormTailEvent (randomMatrixSum A) t) <=
      matrixBernsteinTwoSidedOptimizedScalarTailRHS
        n R Rneg t sigmaSq sigmaSqNeg := by
  simpa [matrixBernsteinTwoSidedOptimizedScalarTailRHS,
    matrixBernsteinOptimizedScalarTailRHS] using
    (matrixBernsteinOpNormTailOptimizedScalarRHSWithCoeff_arbitrary_of_pos_under_primitives
      (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
      (sigmaSq := sigmaSq) (sigmaSqNeg := sigmaSqNeg)
      hPos.centered
      hPos.independentSelfAdjoint
      hPos.integrable
      hPos.squareIntegrable
      hPos.expIntegrable
      hPos.traceExpIntegrable
      hPos.operatorNormBound
      hPos.sigmaPositive
      hPos.radiusNonneg
      hPos.deviationPositive
      hPos.varianceProxyNormBound
      hPos.cfcPrimitive
      hPos.troppPrimitive
      hNeg.centered
      hNeg.independentSelfAdjoint
      hNeg.integrable
      hNeg.squareIntegrable
      hNeg.expIntegrable
      hNeg.traceExpIntegrable
      hNeg.operatorNormBound
      hNeg.sigmaPositive
      hNeg.radiusNonneg
      hNeg.varianceProxyNormBound
      hNeg.cfcPrimitive
      hNeg.troppPrimitive)

/-- Preferred arbitrary-dimensional self-adjoint operator-norm Matrix
Bernstein wrapper after the Bernstein CFC hardbone leaf.

This is the high-level CFC-free assumption-bundle entry point. It still keeps
the sign-specific finite-family Tropp/Lieb primitives, variance proxies,
integrability, independence, and boundedness explicit through the two bundles. -/
theorem matrixBernsteinOpNormTailOptimizedScalarRHSWithCoeff_arbitrary_of_troppAssumptions
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n)
    (R Rneg t sigmaSq sigmaSqNeg : Real)
    (hPos :
      MatrixBernsteinPositiveSideTroppAssumptions (P := P) A R t sigmaSq)
    (hNeg :
      MatrixBernsteinNegativeSideTroppAssumptions
        (P := P) A Rneg t sigmaSqNeg) :
    P (SelfAdjointOperatorNormTailEvent (randomMatrixSum A) t) <=
      matrixBernsteinTwoSidedOptimizedScalarTailRHS
        n R Rneg t sigmaSq sigmaSqNeg :=
  matrixBernsteinOpNormTailOptimizedScalarRHSWithCoeff_arbitrary_of_assumptions
    (P := P) A R Rneg t sigmaSq sigmaSqNeg
    hPos.toPositiveSideAssumptions hNeg.toNegativeSideAssumptions

/-- Sample-covariance operator-norm event bridge to the unnormalized centered
row rank-one sum.

This is the operator-norm analogue of the normalization bridge used by the
quadratic-form sample-covariance wrapper. It transports the public centered
sample-covariance deviation event to the centered row rank-one sum at threshold
`(m : Real) * t`. The row rank-one integrability hypothesis is exactly the one
needed by `sampleCovariance_deviation_eq_normalized_centered_rowRankOne_sum`.
-/
theorem sampleCovariance_selfAdjointOperatorNormTailEvent_subset_centeredRowRankOneSum
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {m n : Nat}
    (A : RandomMatrix Omega m n) (t : Real)
    (hm : 0 < m)
    (hInt :
      forall k : Fin m,
        IntegrableRandomMatrix P (rankOneRandomMatrix (rowVector A k))) :
    SelfAdjointOperatorNormTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t ⊆
      SelfAdjointOperatorNormTailEvent
        (centeredSampleCovarianceRowRankOneSum (P := P) A)
        ((m : Real) * t) := by
  intro omega hTail
  change t <= operatorNorm (centeredRandomMatrix P (sampleCovariance A)) omega at hTail
  have hmReal : 0 < (m : Real) := by exact_mod_cast hm
  have hDevEq :=
    congrFun
      (sampleCovariance_deviation_eq_normalized_centered_rowRankOne_sum
        (P := P) A hInt) omega
  have hNorm :
      operatorNorm (centeredRandomMatrix P (sampleCovariance A)) omega =
        (1 / (m : Real)) *
          operatorNorm (centeredSampleCovarianceRowRankOneSum (P := P) A)
            omega := by
    calc
      operatorNorm (centeredRandomMatrix P (sampleCovariance A)) omega =
          norm (centeredRandomMatrix P (sampleCovariance A) omega) := rfl
      _ =
          norm ((1 / (m : Real)) •
            centeredSampleCovarianceRowRankOneSum (P := P) A omega) := by
            rw [hDevEq]
            rfl
      _ =
          |1 / (m : Real)| *
            norm (centeredSampleCovarianceRowRankOneSum (P := P) A omega) := by
            rw [norm_smul, Real.norm_eq_abs]
      _ =
          (1 / (m : Real)) *
            operatorNorm (centeredSampleCovarianceRowRankOneSum (P := P) A)
              omega := by
            rw [abs_of_nonneg (one_div_nonneg.mpr hmReal.le)]
            rfl
  change (m : Real) * t <=
    operatorNorm (centeredSampleCovarianceRowRankOneSum (P := P) A) omega
  rw [hNorm] at hTail
  have hScaled :=
    mul_le_mul_of_nonneg_left hTail hmReal.le
  calc
    (m : Real) * t <=
        (m : Real) *
          ((1 / (m : Real)) *
            operatorNorm (centeredSampleCovarianceRowRankOneSum (P := P) A)
              omega) := hScaled
    _ =
        operatorNorm (centeredSampleCovarianceRowRankOneSum (P := P) A)
          omega := by
          field_simp [ne_of_gt hmReal]

/-- Centered rank-one radius produced by a row squared-norm bound `R`. -/
abbrev sampleCovarianceCenteredRankOneRadius (R : Real) : Real :=
  2 * R

/-- Crude variance-proxy norm bound for the centered row-rank-one family under
a row squared-norm bound `R`. -/
abbrev sampleCovarianceCenteredRankOneVarianceProxyBound {m : Nat}
    (R : Real) : Real :=
  (m : Real) * sampleCovarianceCenteredRankOneRadius R ^ 2

/-- Explicit-row-count alias for the crude centered row-rank-one variance
proxy bound. -/
abbrev sampleCovarianceCenteredRankOneVarianceProxyBoundOfRows
    (m : Nat) (R : Real) : Real :=
  sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R

/-- Nonnegativity of the centered rank-one sample-covariance radius. -/
theorem sampleCovarianceCenteredRankOneRadius_nonneg {R : Real}
    (hR : 0 <= R) : 0 <= sampleCovarianceCenteredRankOneRadius R := by
  dsimp [sampleCovarianceCenteredRankOneRadius]
  nlinarith

/-- Positivity of the crude sample-covariance variance-proxy norm bound. -/
theorem sampleCovarianceCenteredRankOneVarianceProxyBound_pos {m : Nat}
    {R : Real} (hm : 0 < m) (hR : 0 < R) :
    0 < sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R := by
  have hmReal : 0 < (m : Real) := by
    exact_mod_cast hm
  have hRadius : 0 < sampleCovarianceCenteredRankOneRadius R := by
    have hTwo : 0 < (2 : Real) * R := by
      nlinarith
    simpa [sampleCovarianceCenteredRankOneRadius] using hTwo
  simpa [sampleCovarianceCenteredRankOneVarianceProxyBound] using
    mul_pos hmReal (sq_pos_of_pos hRadius)

/-- Positivity of the explicit-row-count sample-covariance variance proxy
bound. -/
theorem sampleCovarianceCenteredRankOneVarianceProxyBoundOfRows_pos
    {m : Nat} {R : Real} (hm : 0 < m) (hR : 0 < R) :
    0 < sampleCovarianceCenteredRankOneVarianceProxyBoundOfRows m R := by
  simpa [sampleCovarianceCenteredRankOneVarianceProxyBoundOfRows] using
    (sampleCovarianceCenteredRankOneVarianceProxyBound_pos (m := m) hm hR)

/-- Optimized Bernstein parameter for the sample-covariance tail wrapper. -/
abbrev sampleCovarianceTailTheta {m : Nat} (R t sigmaSq : Real) : Real :=
  bernsteinThetaChoice ((m : Real) * t) sigmaSq
    (sampleCovarianceCenteredRankOneRadius R)

/-- Explicit-row-count alias for the optimized sample-covariance Bernstein
parameter. -/
abbrev sampleCovarianceTailThetaOfRows
    (m : Nat) (R t sigmaSq : Real) : Real :=
  sampleCovarianceTailTheta (m := m) R t sigmaSq

/-- Named scalar RHS for sample-covariance Bernstein tail wrappers.

The dimension parameter `n` is the actual column dimension of the sample
matrix. Existing nonempty wrappers pass `n + 1` explicitly. -/
abbrev sampleCovarianceQuadraticFormTailRHS {m n : Nat}
    (R t sigmaSq : Real) : ENNReal :=
  ENNReal.ofReal
    ((n : Real) *
      Real.exp (-(((m : Real) * t) ^ 2 /
        (2 * sigmaSq + (2 / 3) *
          sampleCovarianceCenteredRankOneRadius R * ((m : Real) * t)))))

/-- Negative centered row-rank-one family for sample covariance wrappers. -/
abbrev centeredSampleCovarianceRowRankOneFamilyNeg
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {m n : Nat}
    (A : RandomMatrix Omega m n) :
    Fin m -> RandomMatrix Omega n n :=
  negRandomMatrixFamily
    (centeredSampleCovarianceRowRankOneFamily (P := P) A)

/-- Sum of the negative centered row-rank-one sample-covariance family. -/
abbrev centeredSampleCovarianceRowRankOneSumNeg
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {m n : Nat}
    (A : RandomMatrix Omega m n) :
    RandomMatrix Omega n n :=
  randomMatrixSum
    (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)

/--
Coordinate second-moment assumptions make the named negative centered
sample-covariance row-rank-one family entrywise integrable.

This is a thin negation adapter around the positive centered rank-one
integrability wrapper; it does not infer higher square/exponential
integrability.
-/
theorem centeredSampleCovarianceRowRankOneFamilyNeg_integrable_of_memLp_two
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsFiniteMeasure P] {m n : Nat} {A : RandomMatrix Omega m n}
    (hLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (matrixEntry A k j) 2) :
    forall k : Fin m,
      IntegrableRandomMatrix P
        ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k) := by
  have hPos :
      forall k : Fin m,
        IntegrableRandomMatrix P
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k) := by
    intro k
    change IntegrableRandomMatrix P
      (centeredRankOneRandomMatrix P (rowVector A k))
    exact centeredRankOneRandomMatrix_integrable_of_memLp_two
      (P := P) (X := rowVector A k) (by
        intro j
        change MemLpRealRandomVariable P (matrixEntry A k j) 2
        exact hLp k j)
  simpa [centeredSampleCovarianceRowRankOneFamilyNeg] using
    integrableRandomMatrix_negRandomMatrixFamily
      (P := P) (A := centeredSampleCovarianceRowRankOneFamily (P := P) A)
      hPos

/--
Coordinate measurability and second moments make the named negative centered
sample-covariance row-rank-one family centered and self-adjoint.

This transfers the already-proved positive centered rank-one structure through
the named negative-family adapter.
-/
theorem centeredSampleCovarianceRowRankOneFamilyNeg_centeredSelfAdjoint_of_memLp_two
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat} {A : RandomMatrix Omega m n}
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (matrixEntry A k j) 2) :
    CenteredSelfAdjointRandomMatrixFamily P
      (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) := by
  have hRowsRandom :
      forall k : Fin m, IsRandomVector P (rowVector A k) :=
    fun k => isRandomVector_rowVector hMeas k
  have hRowsLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (coord (rowVector A k) j) 2 := by
    intro k j
    change MemLpRealRandomVariable P (matrixEntry A k j) 2
    exact hLp k j
  have hPos :
      CenteredSelfAdjointRandomMatrixFamily P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) := by
    simpa [centeredSampleCovarianceRowRankOneFamily] using
      centeredRankOneRandomMatrix_centeredSelfAdjoint_of_memLp_two
        (P := P) (X := rowVector A) hRowsRandom hRowsLp
  simpa [centeredSampleCovarianceRowRankOneFamilyNeg] using
    centeredSelfAdjointRandomMatrixFamily_negRandomMatrixFamily
      (P := P) (A := centeredSampleCovarianceRowRankOneFamily (P := P) A)
      hPos

/--
A row squared-norm bound gives the pointwise operator-norm bound for the named
negative centered sample-covariance row-rank-one family.

The proof only uses `||-M|| = ||M||` through the generic negative-family
adapter; it does not discharge square/exponential integrability or Matrix
Bernstein primitives.
-/
theorem PointwiseOperatorNormBound_centeredSampleCovarianceRowRankOneFamilyNeg_of_rowSqNorm_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m n) {R : Real}
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hR : 0 <= R) :
    PointwiseOperatorNormBound
      (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
      (sampleCovarianceCenteredRankOneRadius R) := by
  have hRowsRandom :
      forall k : Fin m, IsRandomVector P (rowVector A k) := by
    intro k
    exact isRandomVector_rowVector hMeas k
  have hRowsLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (coord (rowVector A k) j) 2 := by
    intro k j
    change MemLpRealRandomVariable P (matrixEntry A k j) 2
    exact hLp k j
  have hPos :
      PointwiseOperatorNormBound
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (sampleCovarianceCenteredRankOneRadius R) := by
    simpa [centeredSampleCovarianceRowRankOneFamily,
      sampleCovarianceCenteredRankOneRadius] using
      PointwiseOperatorNormBound_centeredRankOneRandomMatrix_of_sqNorm_bound
        (P := P) (X := rowVector A) (R := R)
        hRowsRandom hRowsLp hSq hR
  simpa [centeredSampleCovarianceRowRankOneFamilyNeg] using
    PointwiseOperatorNormBound_negRandomMatrixFamily
      (A := centeredSampleCovarianceRowRankOneFamily (P := P) A)
      hPos

/--
Square-integrability of the positive centered sample-covariance row-rank-one
family transfers to the named negative family.

This is only the algebraic `(-X)^2 = X^2` transfer.  It does not infer matrix
exponential integrability, trace integrability, CFC, or Tropp/Lieb primitives.
-/
theorem centeredSampleCovarianceRowRankOneFamilyNeg_squareIntegrable_of_squareIntegrable
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {m n : Nat} {A : RandomMatrix Omega m n}
    (hSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k))) :
    forall k : Fin m,
      IntegrableRandomMatrix P
        (randomMatrixSquare
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k)) := by
  simpa [centeredSampleCovarianceRowRankOneFamilyNeg] using
    integrableRandomMatrix_randomMatrixSquare_negRandomMatrixFamily
      (P := P) (A := centeredSampleCovarianceRowRankOneFamily (P := P) A)
      hSq

/--
Matrix-exponential integrability for the named negative sample-covariance
row-rank-one family transfers from the original family at the opposite scalar
parameter.

This is a sample-covariance alias for
`integrableRandomMatrix_matrixExpScaledFamily_negRandomMatrixFamily`; it does
not prove exponential integrability from moment or row-norm assumptions.
-/
theorem centeredSampleCovarianceRowRankOneFamilyNeg_expIntegrable_of_expIntegrable_neg_theta
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {m n : Nat} {A : RandomMatrix Omega m n} {theta : Real}
    (hExp :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (-theta) k)) :
    forall k : Fin m,
      IntegrableRandomMatrix P
        (matrixExpScaledFamily
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
          theta k) := by
  change forall k : Fin m,
    IntegrableRandomMatrix P
      (matrixExpScaledFamily
        (negRandomMatrixFamily
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        theta k)
  exact integrableRandomMatrix_matrixExpScaledFamily_negRandomMatrixFamily
    (P := P) (A := centeredSampleCovarianceRowRankOneFamily (P := P) A)
    (theta := theta) hExp

/--
Trace-exponential integrability for the named negative sample-covariance
row-rank-one sum transfers from the original centered row-rank-one sum at the
opposite scalar parameter.

This is a sample-covariance alias for
`integrableRealRandomVariable_traceExpIntegrand_randomMatrixSum_negRandomMatrixFamily`;
it keeps the opposite-theta provider assumption explicit.
-/
theorem centeredSampleCovarianceRowRankOneSumNeg_traceExpIntegrable_of_traceExpIntegrable_neg_theta
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {m n : Nat} {A : RandomMatrix Omega m n} {theta : Real}
    (hTrace :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (-theta))) :
    IntegrableRealRandomVariable P
      (traceExpIntegrand
        (centeredSampleCovarianceRowRankOneSumNeg (P := P) A)
        theta) := by
  change IntegrableRealRandomVariable P
    (traceExpIntegrand
      (randomMatrixSum
        (negRandomMatrixFamily
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)))
      theta)
  exact integrableRealRandomVariable_traceExpIntegrand_randomMatrixSum_negRandomMatrixFamily
    (P := P) (A := centeredSampleCovarianceRowRankOneFamily (P := P) A)
    (theta := theta) hTrace

/--
A supplied Bernstein functional-calculus primitive for the original centered
sample-covariance row-rank-one family at `-theta` transfers to the named
negative family at `theta`.

This is only a sign-normalization wrapper around
`bernsteinMatrixExp_le_quadratic_neg_of_neg_theta`; it does not prove the CFC
primitive.
-/
theorem centeredSampleCovarianceRowRankOneFamilyNeg_cfcPrimitive_of_cfcPrimitive_neg_theta
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {m n : Nat} {A : RandomMatrix Omega m n} {theta R : Real}
    (hCFC :
      forall k : Fin m, forall omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega)
          (-theta) R) :
    forall k : Fin m, forall omega,
      bernsteinMatrixExpLeQuadraticStatement
        ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k omega)
        theta R := by
  intro k omega
  change bernsteinMatrixExpLeQuadraticStatement
    (-
      ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega))
    theta R
  exact bernsteinMatrixExp_le_quadratic_neg_of_neg_theta
    ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega)
    theta R (hCFC k omega)

/-- Sample-covariance row-rank-one variance-proxy norm bound from a row
squared-norm bound and explicit square-integrability of the centered
summands. -/
theorem MatrixVarianceProxyNormBound_centeredSampleCovarianceRowRankOneFamily_of_rowSqNorm_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m n) {R : Real}
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hR : 0 <= R)
    (hIntSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k))) :
    MatrixVarianceProxyNormBound P
      (centeredSampleCovarianceRowRankOneFamily (P := P) A)
      (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R) := by
  have hRowsRandom :
      forall k : Fin m, IsRandomVector P (rowVector A k) := by
    intro k
    exact isRandomVector_rowVector hMeas k
  have hRowsLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (coord (rowVector A k) j) 2 := by
    intro k j
    change MemLpRealRandomVariable P (matrixEntry A k j) 2
    exact hLp k j
  have hGeneric :
      MatrixVarianceProxyNormBound P
        (centeredRankOneRandomMatrixFamily P (rowVector A))
        (centeredRankOneVarianceProxyNormRHS (I := Fin m) R) :=
    MatrixVarianceProxyNormBound_centeredRankOneRandomMatrixFamily_of_sqNorm_bound
      (P := P) (X := rowVector A) hRowsRandom hRowsLp hSq hR hIntSq
  simpa [centeredSampleCovarianceRowRankOneFamily,
    sampleCovarianceCenteredRankOneVarianceProxyBound,
    sampleCovarianceCenteredRankOneRadius,
    centeredRankOneVarianceProxyNormRHS,
    pointwiseOperatorNormVarianceProxyNormRHS] using hGeneric

/-- Negative sample-covariance row-rank-one variance-proxy norm bound from
row-specific squared-norm bounds.

This is the negative-side exact-row provider for sample-covariance routes. It
does not prove a new sharp-variance chain: it reuses the positive exact-row
hardbone consumer and the algebraic fact that pointwise negation preserves the
matrix variance proxy. -/
theorem varianceProxyBound_centeredSampleCovarianceRowRankOneFamilyNeg_exactRowSqNorm_memLpTwo
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m n)
    (R : Fin m -> Real)
    (hChain :
      sampleCovarianceVarianceProxySharpStatement (P := P) (X := rowVector A)
        (fun i => matrixSecondMoment P (rankOneRandomMatrix (rowVector A i)))
        (rowSqNormVarianceProxyNormRHS R))
    (hLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R k)
    (hR : forall k : Fin m, 0 <= R k) :
    MatrixVarianceProxyNormBound P
      (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
      (rowSqNormVarianceProxyNormRHS R) := by
  have hRowsLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (coord (rowVector A k) j) 2 := by
    intro k j
    change MemLpRealRandomVariable P (matrixEntry A k j) 2
    exact hLp k j
  have hPos :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (rowSqNormVarianceProxyNormRHS R) := by
    change MatrixVarianceProxyNormBound P
      (centeredRankOneRandomMatrixFamily P (rowVector A))
      (rowSqNormVarianceProxyNormRHS R)
    exact
      sampleCovarianceVarianceProxy_sharp_of_exactRowSqNorm_bound_memLp_two
        (P := P) (X := rowVector A) (R := R)
        hChain hRowsLp hSq hR
  change
    matrixVarianceProxyNorm P
      (negRandomMatrixFamily
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)) <=
      rowSqNormVarianceProxyNormRHS R
  rw [matrixVarianceProxyNorm, matrixVarianceProxy_negRandomMatrixFamily]
  simpa [MatrixVarianceProxyNormBound, matrixVarianceProxyNorm] using hPos

/--
Sample covariance quadratic-form upper-tail wrapper under explicit Matrix
Bernstein primitive assumptions.

The wrapper rewrites the centered sample covariance as the normalized centered
row rank-one sum, applies the optimized quadratic-form Matrix Bernstein theorem
to the unnormalized centered row rank-one summands at threshold
`(m : Real) * t`, and transports the result back across the normalization.

The variance proxy remains explicit through
`MatrixVarianceProxyNormBound P (centeredSampleCovarianceRowRankOneFamily (P := P) A) sigmaSq`.
This theorem does not prove variance proxy control, independence, Tropp/Lieb,
Bernstein CFC, or an operator-norm tail bound.
-/
theorem sampleCovariance_quadraticForm_tail_optimized_under_explicit_variance_proxy
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m (n + 1))
    (R t sigmaSq : Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin (n + 1),
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hIntSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k)))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t sigmaSq)
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t sigmaSq)))
    (hSigma : 0 < sigmaSq)
    (hR : 0 <= R)
    (ht : 0 < t)
    (hNorm :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) sigmaSq)
    (hCFC :
      forall k : Fin m, forall omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) R t sigmaSq)
          (sampleCovarianceCenteredRankOneRadius R))
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t sigmaSq)
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t sigmaSq)
        (sampleCovarianceCenteredRankOneRadius R)) :
    P (quadraticFormUpperTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
        (m := m) (n := n + 1) R t sigmaSq := by
  have hmReal : 0 < (m : Real) := by
    exact_mod_cast hm
  have hRowsRandom :
      forall k : Fin m, IsRandomVector P (rowVector A k) := by
    intro k
    exact isRandomVector_rowVector hMeas k
  have hRowsLp :
      forall k : Fin m, forall j : Fin (n + 1),
        MemLpRealRandomVariable P (coord (rowVector A k) j) 2 := by
    intro k j
    change MemLpRealRandomVariable P (matrixEntry A k j) 2
    exact hLp k j
  have hRowsRankOneInt :
      forall k : Fin m,
        IntegrableRandomMatrix P (rankOneRandomMatrix (rowVector A k)) := by
    intro k
    exact integrableRandomMatrix_rankOneRandomMatrix_of_memLp_two
      (P := P) (X := rowVector A k) (hRowsLp k)
  have hCentered :
      CenteredSelfAdjointRandomMatrixFamily P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) :=
    centeredRankOneRandomMatrix_centeredSelfAdjoint_of_memLp_two
      (P := P) (X := rowVector A) hRowsRandom hRowsLp
  have hIndepSA :
      IndependentSelfAdjointRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) :=
    ⟨hCentered.1, hIndep⟩
  have hIntX :
      forall k : Fin m,
        IntegrableRandomMatrix P
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k) := by
    intro k
    change IntegrableRandomMatrix P
      (centeredRankOneRandomMatrix P (rowVector A k))
    exact centeredRankOneRandomMatrix_integrable_of_memLp_two
      (P := P) (X := rowVector A k) (hRowsLp k)
  have hBound :
      PointwiseOperatorNormBound
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (sampleCovarianceCenteredRankOneRadius R) :=
    PointwiseOperatorNormBound_centeredRankOneRandomMatrix_of_sqNorm_bound
      (P := P) (X := rowVector A) hRowsRandom hRowsLp hSq hR
  have hRadius : 0 <= sampleCovarianceCenteredRankOneRadius R := by
    simpa [sampleCovarianceCenteredRankOneRadius] using show 0 <= 2 * R by
      nlinarith
  have hmt : 0 < (m : Real) * t := by exact mul_pos hmReal ht
  have hMB :
      P (quadraticFormUpperTailEvent
          (randomMatrixSum
            (centeredSampleCovarianceRowRankOneFamily (P := P) A))
          ((m : Real) * t)) <=
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n + 1) R t sigmaSq := by
    simpa [sampleCovarianceQuadraticFormTailRHS, sampleCovarianceTailTheta,
      sampleCovarianceCenteredRankOneRadius] using
      matrixBernsteinQuadraticFormUpperTailOptimizedScalarRHSWithCoeff_under_primitives
        (P := P)
        (A := centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (R := sampleCovarianceCenteredRankOneRadius R)
        (t := (m : Real) * t) (sigmaSq := sigmaSq)
        hCentered hIndepSA hIntX hIntSq hExpInt
        (by
          change IntegrableRealRandomVariable P
            (traceExpIntegrand
              (centeredSampleCovarianceRowRankOneSum (P := P) A)
              (sampleCovarianceTailTheta (m := m) R t sigmaSq))
          exact hTraceInt)
        hBound hSigma hRadius hmt hNorm hCFC hTropp
  have hMBNamed :
      P (quadraticFormUpperTailEvent
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          ((m : Real) * t)) <=
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n + 1) R t sigmaSq := by
    change P (quadraticFormUpperTailEvent
          (randomMatrixSum
            (centeredSampleCovarianceRowRankOneFamily (P := P) A))
          ((m : Real) * t)) <=
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n + 1) R t sigmaSq
    exact hMB
  have hSubset :
      quadraticFormUpperTailEvent
          (centeredRandomMatrix P (sampleCovariance A)) t ⊆
        quadraticFormUpperTailEvent
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          ((m : Real) * t) := by
    intro omega hTail
    rcases hTail with ⟨x, hxUnit, htTail⟩
    refine ⟨x, hxUnit, ?_⟩
    have hDevEq :=
      congrFun
        (sampleCovariance_deviation_eq_normalized_centered_rowRankOne_sum
          (P := P) A hRowsRankOneInt) omega
    have hQuad :
        matrixQuadraticForm
            (centeredRandomMatrix P (sampleCovariance A) omega) x =
          (1 / (m : Real)) *
            matrixQuadraticForm
              (centeredSampleCovarianceRowRankOneSum (P := P) A omega) x := by
      rw [hDevEq]
      change matrixQuadraticForm
          ((1 / (m : Real)) •
            centeredSampleCovarianceRowRankOneSum (P := P) A omega) x =
        (1 / (m : Real)) *
          matrixQuadraticForm
            (centeredSampleCovarianceRowRankOneSum (P := P) A omega) x
      exact
        (matrixQuadraticForm_smul (1 / (m : Real))
          (centeredSampleCovarianceRowRankOneSum (P := P) A omega) x)
    have htScaled :
        t <=
          (1 / (m : Real)) *
            matrixQuadraticForm
              (centeredSampleCovarianceRowRankOneSum (P := P) A omega) x := by
      rw [hQuad] at htTail
      exact htTail
    have hMul :=
      mul_le_mul_of_nonneg_left htScaled hmReal.le
    calc
      (m : Real) * t <=
          (m : Real) *
            ((1 / (m : Real)) *
              matrixQuadraticForm
                (centeredSampleCovarianceRowRankOneSum (P := P) A omega) x) :=
        hMul
      _ =
          matrixQuadraticForm
            (centeredSampleCovarianceRowRankOneSum (P := P) A omega) x := by
        field_simp [ne_of_gt hmReal]
  exact le_trans (measure_mono hSubset) hMBNamed

/-- Sample-covariance quadratic-form upper-tail wrapper under explicit variance
proxy and the proved Bernstein CFC hardbone leaf.

This is the CFC-free variant of
`sampleCovariance_quadraticForm_tail_optimized_under_explicit_variance_proxy`:
the caller still supplies the finite-family Tropp/Lieb trace-MGF primitive and
analytic integrability assumptions, but not a pointwise Bernstein CFC field. -/
theorem sampleCovariance_quadraticForm_tail_explicitVarianceProxy_troppPrimitive
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m (n + 1))
    (R t sigmaSq : Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin (n + 1),
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hIntSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k)))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t sigmaSq)
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t sigmaSq)))
    (hSigma : 0 < sigmaSq)
    (hR : 0 <= R)
    (ht : 0 < t)
    (hNorm :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) sigmaSq)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t sigmaSq)
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t sigmaSq)
        (sampleCovarianceCenteredRankOneRadius R)) :
    P (quadraticFormUpperTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
        (m := m) (n := n + 1) R t sigmaSq := by
  exact
    sampleCovariance_quadraticForm_tail_optimized_under_explicit_variance_proxy
      (P := P) (A := A) (R := R) (t := t) (sigmaSq := sigmaSq)
      hm hMeas hLp hSq hIndep hIntSq hExpInt hTraceInt hSigma hR ht
      hNorm
      (fun k omega =>
        bernsteinMatrixExp_le_quadratic
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) R t sigmaSq)
          (sampleCovarianceCenteredRankOneRadius R))
      hTropp


/-- Positive-side assumption bundle for the exact-row centered-square-chain
sample-covariance route.

This packages the hypotheses consumed by
`sampleCovariance_quadraticForm_tail_exactRowSqNorm_centeredSquareChain_troppPrimitive`.
It is only a semantic bundle: the generic centered-square variance-proxy chain,
Tropp/Lieb trace-MGF primitive, independence, integrability, and radius
conditions remain explicit fields. -/
structure SampleCovarianceExactRowCenteredSquareTroppAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {m n : Nat}
    (A : RandomMatrix Omega m n) (R t : Real) (Rvar : Fin m -> Real) : Prop where
  nonemptyRows : 0 < m
  measurable : IsRandomMatrix P A
  rowMemLp :
    forall k : Fin m, forall j : Fin n,
      MemLpRealRandomVariable P (matrixEntry A k j) 2
  rowSqNormBound :
    forall k : Fin m, forall omega,
      vectorSqNorm (rowVector A k omega) <= R
  rowSqNormVarianceBound :
    forall k : Fin m, forall omega,
      vectorSqNorm (rowVector A k omega) <= Rvar k
  independentRows :
    IndependentRandomMatrices P
      (centeredSampleCovarianceRowRankOneFamily (P := P) A)
  expIntegrable :
    forall k : Fin m,
      IntegrableRandomMatrix P
        (matrixExpScaledFamily
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (rowSqNormVarianceProxyNormRHS Rvar))
          k)
  traceExpIntegrable :
    IntegrableRealRandomVariable P
      (traceExpIntegrand
        (centeredSampleCovarianceRowRankOneSum (P := P) A)
        (sampleCovarianceTailTheta (m := m) R t
          (rowSqNormVarianceProxyNormRHS Rvar)))
  variancePositive : 0 < rowSqNormVarianceProxyNormRHS Rvar
  radiusNonneg : 0 <= R
  varianceRadiiNonneg : forall i : Fin m, 0 <= Rvar i
  deviationPositive : 0 < t
  centeredSquareChain :
    @varianceProxyNormBoundOfCenteredSquareChainStatement
      Omega _ P (Fin m) _ n
      (rankOneRandomMatrixFamily (rowVector A))
      (fun i => matrixSecondMoment P (rankOneRandomMatrix (rowVector A i)))
      (rowSqNormVarianceProxyNormRHS Rvar)
  troppPrimitive :
    troppMasterTraceMGFFiniteFamilyStatement
      (P := P)
      (centeredSampleCovarianceRowRankOneFamily (P := P) A)
      (bernsteinSecondMomentComparisonFamily P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (sampleCovarianceTailTheta (m := m) R t
          (rowSqNormVarianceProxyNormRHS Rvar))
        (sampleCovarianceCenteredRankOneRadius R))
      (matrixVarianceProxy P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
      (sampleCovarianceTailTheta (m := m) R t
        (rowSqNormVarianceProxyNormRHS Rvar))
      (sampleCovarianceCenteredRankOneRadius R)

/-- Two-sided/operator-norm assumption bundle for the exact-row
centered-square-chain sample-covariance route.

The positive-side fields are reused through
`SampleCovarianceExactRowCenteredSquareTroppAssumptions`. Negative-side fields
remain explicit because they use the negative centered row-rank-one family and a
separate variance-radius family. -/
structure SampleCovarianceExactRowCenteredSquareTwoSidedTroppAssumptions
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m n) (R Rneg t : Real)
    (Rvar RvarNeg : Fin m -> Real) : Prop where
  positive :
    SampleCovarianceExactRowCenteredSquareTroppAssumptions
      (P := P) A R t Rvar
  negRowSqNormBound :
    forall k : Fin m, forall omega,
      vectorSqNorm (rowVector A k omega) <= Rneg
  negRowSqNormVarianceBound :
    forall k : Fin m, forall omega,
      vectorSqNorm (rowVector A k omega) <= RvarNeg k
  negExpIntegrable :
    forall k : Fin m,
      IntegrableRandomMatrix P
        (matrixExpScaledFamily
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (rowSqNormVarianceProxyNormRHS RvarNeg))
          k)
  negTraceExpIntegrable :
    IntegrableRealRandomVariable P
      (traceExpIntegrand
        (centeredSampleCovarianceRowRankOneSumNeg (P := P) A)
        (sampleCovarianceTailTheta (m := m) Rneg t
          (rowSqNormVarianceProxyNormRHS RvarNeg)))
  negVariancePositive : 0 < rowSqNormVarianceProxyNormRHS RvarNeg
  negRadiusNonneg : 0 <= Rneg
  negVarianceRadiiNonneg : forall i : Fin m, 0 <= RvarNeg i
  negCenteredSquareChain :
    @varianceProxyNormBoundOfCenteredSquareChainStatement
      Omega _ P (Fin m) _ n
      (rankOneRandomMatrixFamily (rowVector A))
      (fun i => matrixSecondMoment P (rankOneRandomMatrix (rowVector A i)))
      (rowSqNormVarianceProxyNormRHS RvarNeg)
  negTroppPrimitive :
    troppMasterTraceMGFFiniteFamilyStatement
      (P := P)
      (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
      (bernsteinSecondMomentComparisonFamily P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (sampleCovarianceTailTheta (m := m) Rneg t
          (rowSqNormVarianceProxyNormRHS RvarNeg))
        (sampleCovarianceCenteredRankOneRadius Rneg))
      (matrixVarianceProxy P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
      (sampleCovarianceTailTheta (m := m) Rneg t
        (rowSqNormVarianceProxyNormRHS RvarNeg))
      (sampleCovarianceCenteredRankOneRadius Rneg)

/-- Sample-covariance quadratic-form upper-tail wrapper using the exact-row
bounded-row variance-proxy consumer.

This is a positive-side, CFC-free wrapper. It uses a uniform row squared-norm
radius `R` for the Bernstein radius and a row-specific radius family `Rvar` for
the variance proxy RHS `rowSqNormVarianceProxyNormRHS Rvar`. The hardbone sharp-variance chain
remains explicit; Tropp/Lieb and analytic integrability assumptions remain
explicit as in the existing CFC-free sample-covariance wrapper. -/
theorem sampleCovariance_quadraticForm_tail_optimized_under_exactRowSqNorm_bound_of_troppPrimitive
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m (n + 1))
    (R t : Real)
    (Rvar : Fin m -> Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin (n + 1),
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hSqVar :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= Rvar k)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t
              (rowSqNormVarianceProxyNormRHS Rvar))
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (rowSqNormVarianceProxyNormRHS Rvar))))
    (hSigma : 0 < rowSqNormVarianceProxyNormRHS Rvar)
    (hR : 0 <= R)
    (hRvar : forall i : Fin m, 0 <= Rvar i)
    (ht : 0 < t)
    (hChain :
      sampleCovarianceVarianceProxySharpStatement (P := P) (X := rowVector A)
        (fun i => matrixSecondMoment P (rankOneRandomMatrix (rowVector A i)))
        (rowSqNormVarianceProxyNormRHS Rvar))
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (rowSqNormVarianceProxyNormRHS Rvar))
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t
          (rowSqNormVarianceProxyNormRHS Rvar))
        (sampleCovarianceCenteredRankOneRadius R)) :
    P (quadraticFormUpperTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
        (m := m) (n := n + 1) R t
        (rowSqNormVarianceProxyNormRHS Rvar) := by
  have hRowsLp :
      forall k : Fin m, forall j : Fin (n + 1),
        MemLpRealRandomVariable P (coord (rowVector A k) j) 2 := by
    intro k j
    change MemLpRealRandomVariable P (matrixEntry A k j) 2
    exact hLp k j
  have hIntSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k)) := by
    intro k
    change IntegrableRandomMatrix P
      (randomMatrixSquare ((centeredRankOneRandomMatrixFamily P (rowVector A)) k))
    exact
      integrableRandomMatrix_square_centeredRankOneFamily_of_sqNorm_bound_memLpTwo
        (P := P) (X := rowVector A) (R := R) hRowsLp hSq k
  have hNorm :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (rowSqNormVarianceProxyNormRHS Rvar) := by
    change MatrixVarianceProxyNormBound P
      (centeredRankOneRandomMatrixFamily P (rowVector A))
      (rowSqNormVarianceProxyNormRHS Rvar)
    exact
      sampleCovarianceVarianceProxy_sharp_of_exactRowSqNorm_bound_memLp_two
        (P := P) (X := rowVector A) (R := Rvar)
        hChain hRowsLp hSqVar hRvar
  exact
    sampleCovariance_quadraticForm_tail_explicitVarianceProxy_troppPrimitive
      (P := P) (A := A) (R := R) (t := t)
      (sigmaSq := rowSqNormVarianceProxyNormRHS Rvar)
      hm hMeas hLp hSq hIndep hIntSq hExpInt hTraceInt hSigma hR ht hNorm hTropp

/-- Sample-covariance quadratic-form upper-tail wrapper consuming the generic
centered-square variance-proxy chain.

This is the centered-square-chain variant of
`sampleCovariance_quadraticForm_tail_optimized_under_exactRowSqNorm_bound_of_troppPrimitive`.
It keeps the same positive-side Tropp primitive and analytic assumptions, but
replaces the sample-specific sharp-chain premise by
`varianceProxyNormBoundOfCenteredSquareChainStatement` for the rank-one row
family. The generic centered-square chain itself remains explicit. -/
theorem sampleCovariance_quadraticForm_tail_exactRowSqNorm_centeredSquareChain_troppPrimitive
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m (n + 1))
    (R t : Real)
    (Rvar : Fin m -> Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin (n + 1),
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hSqVar :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= Rvar k)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t
              (rowSqNormVarianceProxyNormRHS Rvar))
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (rowSqNormVarianceProxyNormRHS Rvar))))
    (hSigma : 0 < rowSqNormVarianceProxyNormRHS Rvar)
    (hR : 0 <= R)
    (hRvar : forall i : Fin m, 0 <= Rvar i)
    (ht : 0 < t)
    (hChain :
      @varianceProxyNormBoundOfCenteredSquareChainStatement
        Omega _ P (Fin m) _ (n + 1)
        (rankOneRandomMatrixFamily (rowVector A))
        (fun i => matrixSecondMoment P (rankOneRandomMatrix (rowVector A i)))
        (rowSqNormVarianceProxyNormRHS Rvar))
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (rowSqNormVarianceProxyNormRHS Rvar))
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t
          (rowSqNormVarianceProxyNormRHS Rvar))
        (sampleCovarianceCenteredRankOneRadius R)) :
    P (quadraticFormUpperTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
        (m := m) (n := n + 1) R t
        (rowSqNormVarianceProxyNormRHS Rvar) := by
  have hRowsLp :
      forall k : Fin m, forall j : Fin (n + 1),
        MemLpRealRandomVariable P (coord (rowVector A k) j) 2 := by
    intro k j
    change MemLpRealRandomVariable P (matrixEntry A k j) 2
    exact hLp k j
  have hSharp :
      sampleCovarianceVarianceProxySharpStatement (P := P) (X := rowVector A)
        (fun i => matrixSecondMoment P (rankOneRandomMatrix (rowVector A i)))
        (rowSqNormVarianceProxyNormRHS Rvar) :=
    sampleCovarianceVarianceProxy_sharp_centeredSquareChain_exactRowSqNorm_memLpTwo
      (P := P) (X := rowVector A) (R := Rvar)
      hChain
      (fun k => isRandomVector_rowVector hMeas k)
      hRowsLp
      hSqVar
  exact
    sampleCovariance_quadraticForm_tail_optimized_under_exactRowSqNorm_bound_of_troppPrimitive
      (P := P) (A := A) (R := R) (t := t) (Rvar := Rvar)
      hm hMeas hLp hSq hSqVar hIndep hExpInt hTraceInt hSigma hR hRvar ht
      hSharp hTropp

/-- Sample-covariance quadratic-form upper-tail wrapper consuming the bundled
exact-row centered-square-chain Tropp assumptions.

This is a thin natural-state wrapper over
`sampleCovariance_quadraticForm_tail_exactRowSqNorm_centeredSquareChain_troppPrimitive`.
It packages existing premises only and proves no new Tropp/Lieb, trace-MGF,
variance-proxy, or concentration theorem. -/
theorem sampleCovariance_quadraticForm_tail_exactRowSqNorm_centeredSquareChain_troppAssumptions
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m (n + 1))
    (R t : Real)
    (Rvar : Fin m -> Real)
    (h : SampleCovarianceExactRowCenteredSquareTroppAssumptions
      (P := P) A R t Rvar) :
    P (quadraticFormUpperTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
        (m := m) (n := n + 1) R t
        (rowSqNormVarianceProxyNormRHS Rvar) := by
  exact
    sampleCovariance_quadraticForm_tail_exactRowSqNorm_centeredSquareChain_troppPrimitive
      (P := P) (A := A) (R := R) (t := t) (Rvar := Rvar)
      h.nonemptyRows h.measurable h.rowMemLp h.rowSqNormBound
      h.rowSqNormVarianceBound h.independentRows h.expIntegrable
      h.traceExpIntegrable h.variancePositive h.radiusNonneg
      h.varianceRadiiNonneg h.deviationPositive h.centeredSquareChain
      h.troppPrimitive

/-- Sample-covariance quadratic-form upper-tail wrapper using the crude
bounded-row variance-proxy norm bound.

This removes the explicit `MatrixVarianceProxyNormBound` hypothesis from the
common bounded-row route. It still keeps independence, square-integrability,
trace-integrability, Tropp, and Bernstein CFC primitive assumptions explicit.
-/
theorem sampleCovariance_quadraticForm_tail_optimized_under_rowSqNorm_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m (n + 1))
    (R t : Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin (n + 1),
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hIntSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k)))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t
              (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))))
    (hR : 0 < R)
    (ht : 0 < t)
    (hCFC :
      forall k : Fin m, forall omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
          (sampleCovarianceCenteredRankOneRadius R))
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
        (sampleCovarianceCenteredRankOneRadius R)) :
    P (quadraticFormUpperTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
        (m := m) (n := n + 1) R t
        (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R) := by
  have hSigma :
      0 < sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R :=
    sampleCovarianceCenteredRankOneVarianceProxyBound_pos hm hR
  have hNorm :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R) :=
    MatrixVarianceProxyNormBound_centeredSampleCovarianceRowRankOneFamily_of_rowSqNorm_bound
      (P := P) A hMeas hLp hSq hR.le hIntSq
  exact
    sampleCovariance_quadraticForm_tail_optimized_under_explicit_variance_proxy
      (P := P) (A := A) (R := R) (t := t)
      (sigmaSq := sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R)
      hm hMeas hLp hSq hIndep hIntSq hExpInt hTraceInt hSigma hR.le ht
      hNorm hCFC hTropp

/-- Preferred sample-covariance quadratic-form wrapper after the Bernstein CFC
hardbone leaf.

This is the CFC-free bounded-row entry point: the caller still supplies the
finite-family Tropp/Lieb trace-MGF primitive and analytic integrability
assumptions, but no longer supplies a pointwise Bernstein CFC field. The
pointwise CFC inequality is filled by `bernsteinMatrixExp_le_quadratic`. -/
theorem sampleCovariance_quadraticForm_tail_optimized_under_rowSqNorm_bound_of_troppPrimitive
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m (n + 1))
    (R t : Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin (n + 1),
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hIntSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k)))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t
              (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))))
    (hR : 0 < R)
    (ht : 0 < t)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
        (sampleCovarianceCenteredRankOneRadius R)) :
    P (quadraticFormUpperTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
        (m := m) (n := n + 1) R t
        (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R) := by
  exact
    sampleCovariance_quadraticForm_tail_optimized_under_rowSqNorm_bound
      (P := P) A R t
      hm hMeas hLp hSq hIndep hIntSq hExpInt hTraceInt hR ht
      (fun k omega =>
        bernsteinMatrixExp_le_quadratic
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
          (sampleCovarianceCenteredRankOneRadius R))
      hTropp

/-- Sample-covariance self-adjoint operator-norm tail wrapper under explicit
variance-proxy and Matrix Bernstein primitive assumptions.

This transports the public centered sample-covariance operator-norm event to
the unnormalized centered row rank-one sum, then applies the conditional
self-adjoint operator-norm Matrix Bernstein wrapper. The operator-norm spectral
bridge remains explicit through
`selfAdjointOperatorNormTailViaQuadraticFormStatement`; variance proxies,
integrability, independence, CFC, and Tropp primitives remain explicit for both
signs.
-/
theorem sampleCovariance_selfAdjointOperatorNorm_tail_optimized_under_explicit_variance_proxy
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m (n + 1))
    (R Rneg t sigmaSq sigmaSqNeg : Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin (n + 1),
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hIntSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k)))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t sigmaSq)
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t sigmaSq)))
    (hSigma : 0 < sigmaSq)
    (hR : 0 <= R)
    (ht : 0 < t)
    (hOperatorBridge :
      selfAdjointOperatorNormTailViaQuadraticFormStatement
        (centeredSampleCovarianceRowRankOneSum (P := P) A)
        ((m : Real) * t))
    (hNorm :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) sigmaSq)
    (hCFC :
      forall k : Fin m, forall omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) R t sigmaSq)
          (sampleCovarianceCenteredRankOneRadius R))
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t sigmaSq)
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t sigmaSq)
        (sampleCovarianceCenteredRankOneRadius R))
    (hCenteredNeg :
      CenteredSelfAdjointRandomMatrixFamily P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
    (hIndepSANeg :
      IndependentSelfAdjointRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
    (hIntXNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k))
    (hIntSqNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k)))
    (hExpIntNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            (sampleCovarianceTailTheta (m := m) Rneg t sigmaSqNeg)
            k))
    (hTraceIntNeg :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSumNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t sigmaSqNeg)))
    (hBoundNeg :
      PointwiseOperatorNormBound
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (sampleCovarianceCenteredRankOneRadius Rneg))
    (hSigmaNeg : 0 < sigmaSqNeg)
    (hRNeg : 0 <= Rneg)
    (hNormNeg :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        sigmaSqNeg)
    (hCFCNeg :
      forall k : Fin m, forall omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            k omega)
          (sampleCovarianceTailTheta (m := m) Rneg t sigmaSqNeg)
          (sampleCovarianceCenteredRankOneRadius Rneg))
    (hTroppNeg :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t sigmaSqNeg)
          (sampleCovarianceCenteredRankOneRadius Rneg))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
        (sampleCovarianceTailTheta (m := m) Rneg t sigmaSqNeg)
        (sampleCovarianceCenteredRankOneRadius Rneg)) :
    P (SelfAdjointOperatorNormTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n + 1) R t sigmaSq +
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n + 1) Rneg t sigmaSqNeg := by
  have hmReal : 0 < (m : Real) := by
    exact_mod_cast hm
  have hRowsRandom :
      forall k : Fin m, IsRandomVector P (rowVector A k) := by
    intro k
    exact isRandomVector_rowVector hMeas k
  have hRowsLp :
      forall k : Fin m, forall j : Fin (n + 1),
        MemLpRealRandomVariable P (coord (rowVector A k) j) 2 := by
    intro k j
    change MemLpRealRandomVariable P (matrixEntry A k j) 2
    exact hLp k j
  have hRowsRankOneInt :
      forall k : Fin m,
        IntegrableRandomMatrix P (rankOneRandomMatrix (rowVector A k)) := by
    intro k
    exact integrableRandomMatrix_rankOneRandomMatrix_of_memLp_two
      (P := P) (X := rowVector A k) (hRowsLp k)
  have hCentered :
      CenteredSelfAdjointRandomMatrixFamily P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) :=
    centeredRankOneRandomMatrix_centeredSelfAdjoint_of_memLp_two
      (P := P) (X := rowVector A) hRowsRandom hRowsLp
  have hIndepSA :
      IndependentSelfAdjointRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) := by
    exact ⟨hCentered.1, hIndep⟩
  have hIntX :
      forall k : Fin m,
        IntegrableRandomMatrix P
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k) := by
    intro k
    change IntegrableRandomMatrix P
      (centeredRankOneRandomMatrix P (rowVector A k))
    exact centeredRankOneRandomMatrix_integrable_of_memLp_two
      (P := P) (X := rowVector A k) (hRowsLp k)
  have hBound :
      PointwiseOperatorNormBound
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (sampleCovarianceCenteredRankOneRadius R) :=
    PointwiseOperatorNormBound_centeredRankOneRandomMatrix_of_sqNorm_bound
      (P := P) (X := rowVector A) hRowsRandom hRowsLp hSq hR
  have hRadius := sampleCovarianceCenteredRankOneRadius_nonneg hR
  have hRadiusNeg := sampleCovarianceCenteredRankOneRadius_nonneg hRNeg
  have hmt : 0 < (m : Real) * t := by
    exact mul_pos hmReal ht
  have hSubset :
      SelfAdjointOperatorNormTailEvent
          (centeredRandomMatrix P (sampleCovariance A)) t ⊆
        SelfAdjointOperatorNormTailEvent
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          ((m : Real) * t) :=
    sampleCovariance_selfAdjointOperatorNormTailEvent_subset_centeredRowRankOneSum
      (P := P) A t hm hRowsRankOneInt
  have hMB :
      P (SelfAdjointOperatorNormTailEvent
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          ((m : Real) * t)) <=
        sampleCovarianceQuadraticFormTailRHS
            (m := m) (n := n + 1) R t sigmaSq +
          sampleCovarianceQuadraticFormTailRHS
            (m := m) (n := n + 1) Rneg t sigmaSqNeg := by
    change
      P (SelfAdjointOperatorNormTailEvent
          (randomMatrixSum (centeredSampleCovarianceRowRankOneFamily (P := P) A))
          ((m : Real) * t)) <=
        sampleCovarianceQuadraticFormTailRHS
            (m := m) (n := n + 1) R t sigmaSq +
          sampleCovarianceQuadraticFormTailRHS
            (m := m) (n := n + 1) Rneg t sigmaSqNeg
    simpa [sampleCovarianceQuadraticFormTailRHS,
      sampleCovarianceTailTheta, sampleCovarianceCenteredRankOneRadius] using
      matrixBernsteinOpNormTailOptimizedScalarRHSWithCoeff_under_primitives
        (P := P)
        (A := centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (R := sampleCovarianceCenteredRankOneRadius R)
        (Rneg := sampleCovarianceCenteredRankOneRadius Rneg)
        (t := (m : Real) * t) (sigmaSq := sigmaSq)
        (sigmaSqNeg := sigmaSqNeg)
        hCentered hIndepSA hIntX hIntSq hExpInt
        (by
          simpa [centeredSampleCovarianceRowRankOneSum] using hTraceInt)
        hBound hSigma hRadius hmt
        (by
          simpa [centeredSampleCovarianceRowRankOneSum] using hOperatorBridge)
        hNorm hCFC hTropp hCenteredNeg hIndepSANeg hIntXNeg hIntSqNeg
        hExpIntNeg hTraceIntNeg hBoundNeg hSigmaNeg hRadiusNeg hNormNeg
        hCFCNeg hTroppNeg
  exact (measure_mono hSubset).trans hMB

/-- Sample-covariance self-adjoint operator-norm tail wrapper in nonempty
dimensions under explicit variance-proxy and Matrix Bernstein primitive
assumptions.

This is the nonempty-square version of
`sampleCovariance_selfAdjointOperatorNorm_tail_optimized_under_explicit_variance_proxy`.
It transports the public centered sample-covariance operator-norm event to the
unnormalized centered row rank-one sum, then applies the S4 nonempty
self-adjoint operator-norm Matrix Bernstein wrapper. The spectral bridge is
therefore supplied internally by the Matrix Bernstein wrapper; variance
proxies, integrability, independence, CFC, and Tropp primitives remain explicit
for both signs.
-/
theorem sampleCovariance_opNorm_tail_nonempty_explicitVarianceProxy
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m (n + 1))
    (R Rneg t sigmaSq sigmaSqNeg : Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin (n + 1),
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hIntSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k)))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t sigmaSq)
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t sigmaSq)))
    (hSigma : 0 < sigmaSq)
    (hR : 0 <= R)
    (ht : 0 < t)
    (hNorm :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) sigmaSq)
    (hCFC :
      forall k : Fin m, forall omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) R t sigmaSq)
          (sampleCovarianceCenteredRankOneRadius R))
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t sigmaSq)
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t sigmaSq)
        (sampleCovarianceCenteredRankOneRadius R))
    (hCenteredNeg :
      CenteredSelfAdjointRandomMatrixFamily P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
    (hIndepSANeg :
      IndependentSelfAdjointRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
    (hIntXNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k))
    (hIntSqNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k)))
    (hExpIntNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            (sampleCovarianceTailTheta (m := m) Rneg t sigmaSqNeg)
            k))
    (hTraceIntNeg :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSumNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t sigmaSqNeg)))
    (hBoundNeg :
      PointwiseOperatorNormBound
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (sampleCovarianceCenteredRankOneRadius Rneg))
    (hSigmaNeg : 0 < sigmaSqNeg)
    (hRNeg : 0 <= Rneg)
    (hNormNeg :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        sigmaSqNeg)
    (hCFCNeg :
      forall k : Fin m, forall omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            k omega)
          (sampleCovarianceTailTheta (m := m) Rneg t sigmaSqNeg)
          (sampleCovarianceCenteredRankOneRadius Rneg))
    (hTroppNeg :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t sigmaSqNeg)
          (sampleCovarianceCenteredRankOneRadius Rneg))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
        (sampleCovarianceTailTheta (m := m) Rneg t sigmaSqNeg)
        (sampleCovarianceCenteredRankOneRadius Rneg)) :
    P (SelfAdjointOperatorNormTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n + 1) R t sigmaSq +
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n + 1) Rneg t sigmaSqNeg := by
  have hmReal : 0 < (m : Real) := by
    exact_mod_cast hm
  have hRowsRandom :
      forall k : Fin m, IsRandomVector P (rowVector A k) := by
    intro k
    exact isRandomVector_rowVector hMeas k
  have hRowsLp :
      forall k : Fin m, forall j : Fin (n + 1),
        MemLpRealRandomVariable P (coord (rowVector A k) j) 2 := by
    intro k j
    change MemLpRealRandomVariable P (matrixEntry A k j) 2
    exact hLp k j
  have hRowsRankOneInt :
      forall k : Fin m,
        IntegrableRandomMatrix P (rankOneRandomMatrix (rowVector A k)) := by
    intro k
    exact integrableRandomMatrix_rankOneRandomMatrix_of_memLp_two
      (P := P) (X := rowVector A k) (hRowsLp k)
  have hCentered :
      CenteredSelfAdjointRandomMatrixFamily P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) :=
    centeredRankOneRandomMatrix_centeredSelfAdjoint_of_memLp_two
      (P := P) (X := rowVector A) hRowsRandom hRowsLp
  have hIndepSA :
      IndependentSelfAdjointRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) := by
    exact ⟨hCentered.1, hIndep⟩
  have hIntX :
      forall k : Fin m,
        IntegrableRandomMatrix P
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k) := by
    intro k
    change IntegrableRandomMatrix P
      (centeredRankOneRandomMatrix P (rowVector A k))
    exact centeredRankOneRandomMatrix_integrable_of_memLp_two
      (P := P) (X := rowVector A k) (hRowsLp k)
  have hBound :
      PointwiseOperatorNormBound
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (sampleCovarianceCenteredRankOneRadius R) :=
    PointwiseOperatorNormBound_centeredRankOneRandomMatrix_of_sqNorm_bound
      (P := P) (X := rowVector A) hRowsRandom hRowsLp hSq hR
  have hRadius : 0 <= sampleCovarianceCenteredRankOneRadius R := by
    simpa [sampleCovarianceCenteredRankOneRadius] using show 0 <= 2 * R by
      nlinarith
  have hRadiusNeg : 0 <= sampleCovarianceCenteredRankOneRadius Rneg := by
    simpa [sampleCovarianceCenteredRankOneRadius] using show 0 <= 2 * Rneg by
      nlinarith
  have hmt : 0 < (m : Real) * t := by
    exact mul_pos hmReal ht
  have hSubset :
      SelfAdjointOperatorNormTailEvent
          (centeredRandomMatrix P (sampleCovariance A)) t <=
        SelfAdjointOperatorNormTailEvent
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          ((m : Real) * t) :=
    sampleCovariance_selfAdjointOperatorNormTailEvent_subset_centeredRowRankOneSum
      (P := P) A t hm hRowsRankOneInt
  have hMB :
      P (SelfAdjointOperatorNormTailEvent
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          ((m : Real) * t)) <=
        sampleCovarianceQuadraticFormTailRHS
            (m := m) (n := n + 1) R t sigmaSq +
          sampleCovarianceQuadraticFormTailRHS
            (m := m) (n := n + 1) Rneg t sigmaSqNeg := by
    change
      P (SelfAdjointOperatorNormTailEvent
          (randomMatrixSum (centeredSampleCovarianceRowRankOneFamily (P := P) A))
          ((m : Real) * t)) <=
        sampleCovarianceQuadraticFormTailRHS
            (m := m) (n := n + 1) R t sigmaSq +
          sampleCovarianceQuadraticFormTailRHS
            (m := m) (n := n + 1) Rneg t sigmaSqNeg
    simpa [sampleCovarianceQuadraticFormTailRHS,
      sampleCovarianceTailTheta, sampleCovarianceCenteredRankOneRadius] using
      matrixBernsteinOpNormTailOptimizedScalarRHSWithCoeff_nonempty_under_primitives
        (P := P)
        (A := centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (R := sampleCovarianceCenteredRankOneRadius R)
        (Rneg := sampleCovarianceCenteredRankOneRadius Rneg)
        (t := (m : Real) * t) (sigmaSq := sigmaSq)
        (sigmaSqNeg := sigmaSqNeg)
        hCentered hIndepSA hIntX hIntSq hExpInt
        (by
          change IntegrableRealRandomVariable P
            (traceExpIntegrand
              (centeredSampleCovarianceRowRankOneSum (P := P) A)
              (sampleCovarianceTailTheta (m := m) R t sigmaSq))
          exact hTraceInt)
        hBound hSigma hRadius hmt
        hNorm hCFC hTropp hCenteredNeg hIndepSANeg hIntXNeg hIntSqNeg
        hExpIntNeg hTraceIntNeg hBoundNeg hSigmaNeg hRadiusNeg hNormNeg
        hCFCNeg hTroppNeg
  exact (measure_mono hSubset).trans hMB

/-- Arbitrary-column sample-covariance self-adjoint operator-norm tail wrapper
under explicit variance-proxy and Matrix Bernstein primitive assumptions.

For positive thresholds, the zero-column endpoint is empty by the deterministic
operator-norm endpoint lemma. In positive dimension this is the existing
nonempty sample-covariance wrapper with the actual column dimension passed to
the named RHS helper. Variance proxies, integrability, independence, CFC, and
Tropp primitives remain explicit for both signs.
-/
theorem sampleCovariance_opNorm_tail_pos_explicitVarianceProxy
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m n)
    (R Rneg t sigmaSq sigmaSqNeg : Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hIntSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k)))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t sigmaSq)
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t sigmaSq)))
    (hSigma : 0 < sigmaSq)
    (hR : 0 <= R)
    (ht : 0 < t)
    (hNorm :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) sigmaSq)
    (hCFC :
      forall k : Fin m, forall omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) R t sigmaSq)
          (sampleCovarianceCenteredRankOneRadius R))
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t sigmaSq)
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t sigmaSq)
        (sampleCovarianceCenteredRankOneRadius R))
    (hCenteredNeg :
      CenteredSelfAdjointRandomMatrixFamily P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
    (hIndepSANeg :
      IndependentSelfAdjointRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
    (hIntXNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k))
    (hIntSqNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k)))
    (hExpIntNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            (sampleCovarianceTailTheta (m := m) Rneg t sigmaSqNeg)
            k))
    (hTraceIntNeg :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSumNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t sigmaSqNeg)))
    (hBoundNeg :
      PointwiseOperatorNormBound
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (sampleCovarianceCenteredRankOneRadius Rneg))
    (hSigmaNeg : 0 < sigmaSqNeg)
    (hRNeg : 0 <= Rneg)
    (hNormNeg :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        sigmaSqNeg)
    (hCFCNeg :
      forall k : Fin m, forall omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            k omega)
          (sampleCovarianceTailTheta (m := m) Rneg t sigmaSqNeg)
          (sampleCovarianceCenteredRankOneRadius Rneg))
    (hTroppNeg :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t sigmaSqNeg)
          (sampleCovarianceCenteredRankOneRadius Rneg))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
        (sampleCovarianceTailTheta (m := m) Rneg t sigmaSqNeg)
        (sampleCovarianceCenteredRankOneRadius Rneg)) :
    P (SelfAdjointOperatorNormTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS (m := m) (n := n) R t sigmaSq +
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) Rneg t sigmaSqNeg := by
  cases n with
  | zero =>
      have hEmpty :
          SelfAdjointOperatorNormTailEvent
              (centeredRandomMatrix P (sampleCovariance A)) t = ∅ :=
        selfAdjointOperatorNormTailEvent_empty_of_zero_dim_of_pos
          (centeredRandomMatrix P (sampleCovariance A)) ht
      rw [hEmpty, measure_empty]
      exact zero_le
  | succ n =>
      exact
        sampleCovariance_opNorm_tail_nonempty_explicitVarianceProxy
          (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
          (sigmaSq := sigmaSq) (sigmaSqNeg := sigmaSqNeg)
          hm hMeas hLp hSq hIndep hIntSq hExpInt hTraceInt hSigma hR ht
          hNorm hCFC hTropp hCenteredNeg hIndepSANeg hIntXNeg hIntSqNeg
          hExpIntNeg hTraceIntNeg hBoundNeg hSigmaNeg hRNeg hNormNeg
          hCFCNeg hTroppNeg

/-- Sample-covariance self-adjoint operator-norm tail wrapper using exact-row
variance proxies on both signs.

This is a CFC-free exact-row integration wrapper. It uses uniform row
squared-norm radii `R` and `Rneg` for the Bernstein radii, and row-specific
radius families `Rvar` and `RvarNeg` for the positive and negative variance
proxy RHS values. The two hardbone sharp-variance chain premises,
sign-specific exp/trace integrability, independence, and finite-family
Tropp/Lieb primitives remain explicit. -/
theorem sampleCovariance_opNorm_tail_pos_exactRowSqNorm_negSquare_troppPrimitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m n)
    (R Rneg t : Real)
    (Rvar RvarNeg : Fin m -> Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hSqNeg :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= Rneg)
    (hSqVar :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= Rvar k)
    (hSqVarNeg :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= RvarNeg k)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t
              (rowSqNormVarianceProxyNormRHS Rvar))
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (rowSqNormVarianceProxyNormRHS Rvar))))
    (hSigma : 0 < rowSqNormVarianceProxyNormRHS Rvar)
    (hR : 0 <= R)
    (hRvar : forall i : Fin m, 0 <= Rvar i)
    (ht : 0 < t)
    (hChain :
      sampleCovarianceVarianceProxySharpStatement (P := P) (X := rowVector A)
        (fun i => matrixSecondMoment P (rankOneRandomMatrix (rowVector A i)))
        (rowSqNormVarianceProxyNormRHS Rvar))
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (rowSqNormVarianceProxyNormRHS Rvar))
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t
          (rowSqNormVarianceProxyNormRHS Rvar))
        (sampleCovarianceCenteredRankOneRadius R))
    (hExpIntNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            (sampleCovarianceTailTheta (m := m) Rneg t
              (rowSqNormVarianceProxyNormRHS RvarNeg))
            k))
    (hTraceIntNeg :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSumNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (rowSqNormVarianceProxyNormRHS RvarNeg))))
    (hSigmaNeg : 0 < rowSqNormVarianceProxyNormRHS RvarNeg)
    (hRNeg : 0 <= Rneg)
    (hRvarNeg : forall i : Fin m, 0 <= RvarNeg i)
    (hChainNeg :
      sampleCovarianceVarianceProxySharpStatement (P := P) (X := rowVector A)
        (fun i => matrixSecondMoment P (rankOneRandomMatrix (rowVector A i)))
        (rowSqNormVarianceProxyNormRHS RvarNeg))
    (hTroppNeg :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (rowSqNormVarianceProxyNormRHS RvarNeg))
          (sampleCovarianceCenteredRankOneRadius Rneg))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
        (sampleCovarianceTailTheta (m := m) Rneg t
          (rowSqNormVarianceProxyNormRHS RvarNeg))
        (sampleCovarianceCenteredRankOneRadius Rneg)) :
    P (SelfAdjointOperatorNormTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) R t (rowSqNormVarianceProxyNormRHS Rvar) +
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) Rneg t
          (rowSqNormVarianceProxyNormRHS RvarNeg) := by
  have hRowsRandom :
      forall k : Fin m, IsRandomVector P (rowVector A k) := by
    intro k
    exact isRandomVector_rowVector hMeas k
  have hRowsLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (coord (rowVector A k) j) 2 := by
    intro k j
    change MemLpRealRandomVariable P (matrixEntry A k j) 2
    exact hLp k j
  have hCentered :
      CenteredSelfAdjointRandomMatrixFamily P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) := by
    simpa [centeredSampleCovarianceRowRankOneFamily] using
      centeredRankOneRandomMatrix_centeredSelfAdjoint_of_memLp_two
        (P := P) (X := rowVector A) hRowsRandom hRowsLp
  have hIndepSA :
      IndependentSelfAdjointRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) :=
    ⟨hCentered.1, hIndep⟩
  have hCenteredNeg :
      CenteredSelfAdjointRandomMatrixFamily P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) := by
    simpa [centeredSampleCovarianceRowRankOneFamilyNeg] using
      centeredSelfAdjointRandomMatrixFamily_negRandomMatrixFamily
        (P := P) (A := centeredSampleCovarianceRowRankOneFamily (P := P) A)
        hCentered
  have hIndepSANeg :
      IndependentSelfAdjointRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) := by
    simpa [centeredSampleCovarianceRowRankOneFamilyNeg] using
      independentSelfAdjointRandomMatrices_negRandomMatrixFamily
        (P := P) (A := centeredSampleCovarianceRowRankOneFamily (P := P) A)
        hIndepSA
  have hIntXNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k) :=
    centeredSampleCovarianceRowRankOneFamilyNeg_integrable_of_memLp_two
      (P := P) (A := A) hLp
  have hIntSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k)) := by
    intro k
    change IntegrableRandomMatrix P
      (randomMatrixSquare ((centeredRankOneRandomMatrixFamily P (rowVector A)) k))
    exact
      integrableRandomMatrix_square_centeredRankOneFamily_of_sqNorm_bound_memLpTwo
        (P := P) (X := rowVector A) (R := R) hRowsLp hSq k
  have hIntSqNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k)) :=
    centeredSampleCovarianceRowRankOneFamilyNeg_squareIntegrable_of_squareIntegrable
      (P := P) (A := A) hIntSq
  have hBoundNeg :
      PointwiseOperatorNormBound
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (sampleCovarianceCenteredRankOneRadius Rneg) :=
    PointwiseOperatorNormBound_centeredSampleCovarianceRowRankOneFamilyNeg_of_rowSqNorm_bound
      (P := P) A hMeas hLp hSqNeg hRNeg
  have hNorm :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (rowSqNormVarianceProxyNormRHS Rvar) := by
    change MatrixVarianceProxyNormBound P
      (centeredRankOneRandomMatrixFamily P (rowVector A))
      (rowSqNormVarianceProxyNormRHS Rvar)
    exact
      sampleCovarianceVarianceProxy_sharp_of_exactRowSqNorm_bound_memLp_two
        (P := P) (X := rowVector A) (R := Rvar)
        hChain hRowsLp hSqVar hRvar
  have hNormNeg :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (rowSqNormVarianceProxyNormRHS RvarNeg) :=
    varianceProxyBound_centeredSampleCovarianceRowRankOneFamilyNeg_exactRowSqNorm_memLpTwo
      (P := P) A RvarNeg hChainNeg hLp hSqVarNeg hRvarNeg
  exact
    sampleCovariance_opNorm_tail_pos_explicitVarianceProxy
      (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
      (sigmaSq := rowSqNormVarianceProxyNormRHS Rvar)
      (sigmaSqNeg := rowSqNormVarianceProxyNormRHS RvarNeg)
      hm hMeas hLp hSq hIndep hIntSq hExpInt hTraceInt hSigma hR ht
      hNorm
      (fun k omega =>
        bernsteinMatrixExp_le_quadratic
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) R t
            (rowSqNormVarianceProxyNormRHS Rvar))
          (sampleCovarianceCenteredRankOneRadius R))
      hTropp hCenteredNeg hIndepSANeg hIntXNeg hIntSqNeg hExpIntNeg
      hTraceIntNeg hBoundNeg hSigmaNeg hRNeg hNormNeg
      (fun k omega =>
        bernsteinMatrixExp_le_quadratic
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (rowSqNormVarianceProxyNormRHS RvarNeg))
          (sampleCovarianceCenteredRankOneRadius Rneg))
      hTroppNeg

/-- Sample-covariance self-adjoint operator-norm tail wrapper consuming the
generic centered-square variance-proxy chain on both signs.

This is the centered-square-chain variant of
`sampleCovariance_opNorm_tail_pos_exactRowSqNorm_negSquare_troppPrimitives`.
It keeps both sign-specific Tropp primitives and analytic assumptions explicit,
but replaces the two sample-specific sharp-chain premises by generic
`varianceProxyNormBoundOfCenteredSquareChainStatement` premises for the
rank-one row family. The generic centered-square chains themselves remain
explicit. -/
theorem sampleCovariance_opNorm_tail_pos_exactRowSqNorm_negSquare_centeredSquare_troppPrimitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m n)
    (R Rneg t : Real)
    (Rvar RvarNeg : Fin m -> Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hSqNeg :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= Rneg)
    (hSqVar :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= Rvar k)
    (hSqVarNeg :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= RvarNeg k)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t
              (rowSqNormVarianceProxyNormRHS Rvar))
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (rowSqNormVarianceProxyNormRHS Rvar))))
    (hSigma : 0 < rowSqNormVarianceProxyNormRHS Rvar)
    (hR : 0 <= R)
    (hRvar : forall i : Fin m, 0 <= Rvar i)
    (ht : 0 < t)
    (hChain :
      @varianceProxyNormBoundOfCenteredSquareChainStatement
        Omega _ P (Fin m) _ n
        (rankOneRandomMatrixFamily (rowVector A))
        (fun i => matrixSecondMoment P (rankOneRandomMatrix (rowVector A i)))
        (rowSqNormVarianceProxyNormRHS Rvar))
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (rowSqNormVarianceProxyNormRHS Rvar))
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t
          (rowSqNormVarianceProxyNormRHS Rvar))
        (sampleCovarianceCenteredRankOneRadius R))
    (hExpIntNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            (sampleCovarianceTailTheta (m := m) Rneg t
              (rowSqNormVarianceProxyNormRHS RvarNeg))
            k))
    (hTraceIntNeg :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSumNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (rowSqNormVarianceProxyNormRHS RvarNeg))))
    (hSigmaNeg : 0 < rowSqNormVarianceProxyNormRHS RvarNeg)
    (hRNeg : 0 <= Rneg)
    (hRvarNeg : forall i : Fin m, 0 <= RvarNeg i)
    (hChainNeg :
      @varianceProxyNormBoundOfCenteredSquareChainStatement
        Omega _ P (Fin m) _ n
        (rankOneRandomMatrixFamily (rowVector A))
        (fun i => matrixSecondMoment P (rankOneRandomMatrix (rowVector A i)))
        (rowSqNormVarianceProxyNormRHS RvarNeg))
    (hTroppNeg :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (rowSqNormVarianceProxyNormRHS RvarNeg))
          (sampleCovarianceCenteredRankOneRadius Rneg))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
        (sampleCovarianceTailTheta (m := m) Rneg t
          (rowSqNormVarianceProxyNormRHS RvarNeg))
        (sampleCovarianceCenteredRankOneRadius Rneg)) :
    P (SelfAdjointOperatorNormTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) R t (rowSqNormVarianceProxyNormRHS Rvar) +
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) Rneg t
          (rowSqNormVarianceProxyNormRHS RvarNeg) := by
  have hRowsLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (coord (rowVector A k) j) 2 := by
    intro k j
    change MemLpRealRandomVariable P (matrixEntry A k j) 2
    exact hLp k j
  have hSharp :
      sampleCovarianceVarianceProxySharpStatement (P := P) (X := rowVector A)
        (fun i => matrixSecondMoment P (rankOneRandomMatrix (rowVector A i)))
        (rowSqNormVarianceProxyNormRHS Rvar) :=
    sampleCovarianceVarianceProxy_sharp_centeredSquareChain_exactRowSqNorm_memLpTwo
      (P := P) (X := rowVector A) (R := Rvar)
      hChain
      (fun k => isRandomVector_rowVector hMeas k)
      hRowsLp
      hSqVar
  have hSharpNeg :
      sampleCovarianceVarianceProxySharpStatement (P := P) (X := rowVector A)
        (fun i => matrixSecondMoment P (rankOneRandomMatrix (rowVector A i)))
        (rowSqNormVarianceProxyNormRHS RvarNeg) :=
    sampleCovarianceVarianceProxy_sharp_centeredSquareChain_exactRowSqNorm_memLpTwo
      (P := P) (X := rowVector A) (R := RvarNeg)
      hChainNeg
      (fun k => isRandomVector_rowVector hMeas k)
      hRowsLp
      hSqVarNeg
  exact
    sampleCovariance_opNorm_tail_pos_exactRowSqNorm_negSquare_troppPrimitives
      (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
      (Rvar := Rvar) (RvarNeg := RvarNeg)
      hm hMeas hLp hSq hSqNeg hSqVar hSqVarNeg hIndep hExpInt hTraceInt
      hSigma hR hRvar ht hSharp hTropp hExpIntNeg hTraceIntNeg hSigmaNeg
      hRNeg hRvarNeg hSharpNeg hTroppNeg


/-- Arbitrary-column sample-covariance operator-norm wrapper consuming the
bundled exact-row centered-square-chain Tropp assumptions.

This is a thin natural-state wrapper over the corresponding `..._of_troppPrimitives`
route. It keeps the positive and negative centered-square chains and Tropp
primitives explicit inside the bundle. -/
theorem sampleCovariance_opNorm_tail_pos_exactRowSqNorm_negSquare_centeredSquare_troppAssumptions
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m n)
    (R Rneg t : Real)
    (Rvar RvarNeg : Fin m -> Real)
    (h : SampleCovarianceExactRowCenteredSquareTwoSidedTroppAssumptions
      (P := P) A R Rneg t Rvar RvarNeg) :
    P (SelfAdjointOperatorNormTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) R t (rowSqNormVarianceProxyNormRHS Rvar) +
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) Rneg t
          (rowSqNormVarianceProxyNormRHS RvarNeg) := by
  exact
    sampleCovariance_opNorm_tail_pos_exactRowSqNorm_negSquare_centeredSquare_troppPrimitives
      (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
      (Rvar := Rvar) (RvarNeg := RvarNeg)
      h.positive.nonemptyRows h.positive.measurable h.positive.rowMemLp
      h.positive.rowSqNormBound h.negRowSqNormBound
      h.positive.rowSqNormVarianceBound h.negRowSqNormVarianceBound
      h.positive.independentRows h.positive.expIntegrable
      h.positive.traceExpIntegrable h.positive.variancePositive
      h.positive.radiusNonneg h.positive.varianceRadiiNonneg
      h.positive.deviationPositive h.positive.centeredSquareChain
      h.positive.troppPrimitive h.negExpIntegrable h.negTraceExpIntegrable
      h.negVariancePositive h.negRadiusNonneg h.negVarianceRadiiNonneg
      h.negCenteredSquareChain h.negTroppPrimitive

/-- Arbitrary-column sample-covariance self-adjoint operator-norm tail wrapper
using crude bounded-row variance-proxy norm bounds.

This removes the explicit variance-proxy norm assumptions for both the
centered row-rank-one family and the negative family. The remaining analytic
primitive, independence, integrability, and negative-family structural
assumptions stay explicit.
-/
theorem sampleCovariance_opNorm_tail_pos_rowSqNorm
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m n)
    (R Rneg t : Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hIntSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k)))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t
              (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))))
    (hR : 0 < R)
    (ht : 0 < t)
    (hCFC :
      forall k : Fin m, forall omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
          (sampleCovarianceCenteredRankOneRadius R))
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
        (sampleCovarianceCenteredRankOneRadius R))
    (hCenteredNeg :
      CenteredSelfAdjointRandomMatrixFamily P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
    (hIndepSANeg :
      IndependentSelfAdjointRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
    (hIntXNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k))
    (hIntSqNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k)))
    (hExpIntNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            (sampleCovarianceTailTheta (m := m) Rneg t
              (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
            k))
    (hTraceIntNeg :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSumNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))))
    (hBoundNeg :
      PointwiseOperatorNormBound
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (sampleCovarianceCenteredRankOneRadius Rneg))
    (hRNeg : 0 < Rneg)
    (hCFCNeg :
      forall k : Fin m, forall omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            k omega)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
          (sampleCovarianceCenteredRankOneRadius Rneg))
    (hTroppNeg :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
          (sampleCovarianceCenteredRankOneRadius Rneg))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
        (sampleCovarianceTailTheta (m := m) Rneg t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
        (sampleCovarianceCenteredRankOneRadius Rneg)) :
    P (SelfAdjointOperatorNormTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R) +
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) Rneg t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg) := by
  have hSigma :
      0 < sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R :=
    sampleCovarianceCenteredRankOneVarianceProxyBound_pos hm hR
  have hSigmaNeg :
      0 < sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg :=
    sampleCovarianceCenteredRankOneVarianceProxyBound_pos hm hRNeg
  have hNorm :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R) :=
    MatrixVarianceProxyNormBound_centeredSampleCovarianceRowRankOneFamily_of_rowSqNorm_bound
      (P := P) A hMeas hLp hSq hR.le hIntSq
  have hRadiusNeg :
      0 <= sampleCovarianceCenteredRankOneRadius Rneg := by
    simpa [sampleCovarianceCenteredRankOneRadius] using show 0 <= 2 * Rneg by
      nlinarith
  have hNormNegRaw :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (pointwiseOperatorNormVarianceProxyNormRHS (I := Fin m)
          (sampleCovarianceCenteredRankOneRadius Rneg)) :=
    MatrixVarianceProxyNormBound_of_pointwiseOperatorNormBound
      (P := P)
      (A := centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
      (R := sampleCovarianceCenteredRankOneRadius Rneg)
      hIntSqNeg hBoundNeg hRadiusNeg
  have hNormNeg :
      MatrixVarianceProxyNormBound P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg) := by
    simpa [sampleCovarianceCenteredRankOneVarianceProxyBound,
      pointwiseOperatorNormVarianceProxyNormRHS] using hNormNegRaw
  exact
    sampleCovariance_opNorm_tail_pos_explicitVarianceProxy
      (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
      (sigmaSq := sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R)
      (sigmaSqNeg :=
        sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg)
      hm hMeas hLp hSq hIndep hIntSq hExpInt hTraceInt hSigma hR.le ht
      hNorm hCFC hTropp hCenteredNeg hIndepSANeg hIntXNeg hIntSqNeg
      hExpIntNeg hTraceIntNeg hBoundNeg hSigmaNeg hRNeg.le hNormNeg
      hCFCNeg hTroppNeg

/-- Bounded-row sample-covariance operator-norm wrapper using the negative-family adapters.

Compared with
`sampleCovariance_opNorm_tail_pos_rowSqNorm`,
this version derives the negative centered/self-adjoint structure, negative
independence, negative summand integrability, and negative pointwise
operator-norm bound from named adapters.  It still keeps the negative-side
square/exponential/trace integrability, CFC, and Tropp primitive assumptions
explicit.
-/
theorem sampleCovariance_opNorm_tail_pos_rowSqNorm_negAdapters
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m n)
    (R Rneg t : Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hSqNeg :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= Rneg)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hIntSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k)))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t
              (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))))
    (hR : 0 < R)
    (ht : 0 < t)
    (hCFC :
      forall k : Fin m, forall omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
          (sampleCovarianceCenteredRankOneRadius R))
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
        (sampleCovarianceCenteredRankOneRadius R))
    (hIntSqNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k)))
    (hExpIntNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            (sampleCovarianceTailTheta (m := m) Rneg t
              (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
            k))
    (hTraceIntNeg :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSumNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))))
    (hRNeg : 0 < Rneg)
    (hCFCNeg :
      forall k : Fin m, forall omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            k omega)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
          (sampleCovarianceCenteredRankOneRadius Rneg))
    (hTroppNeg :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
          (sampleCovarianceCenteredRankOneRadius Rneg))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
        (sampleCovarianceTailTheta (m := m) Rneg t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
        (sampleCovarianceCenteredRankOneRadius Rneg)) :
    P (SelfAdjointOperatorNormTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R) +
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) Rneg t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg) := by
  have hCentered :
      CenteredSelfAdjointRandomMatrixFamily P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) := by
    have hRowsRandom :
        forall k : Fin m, IsRandomVector P (rowVector A k) := by
      intro k
      exact isRandomVector_rowVector hMeas k
    have hRowsLp :
        forall k : Fin m, forall j : Fin n,
          MemLpRealRandomVariable P (coord (rowVector A k) j) 2 := by
      intro k j
      change MemLpRealRandomVariable P (matrixEntry A k j) 2
      exact hLp k j
    simpa [centeredSampleCovarianceRowRankOneFamily] using
      centeredRankOneRandomMatrix_centeredSelfAdjoint_of_memLp_two
        (P := P) (X := rowVector A) hRowsRandom hRowsLp
  have hIndepSA :
      IndependentSelfAdjointRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A) :=
    ⟨hCentered.1, hIndep⟩
  have hCenteredNeg :
      CenteredSelfAdjointRandomMatrixFamily P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) :=
    by
      simpa [centeredSampleCovarianceRowRankOneFamilyNeg] using
        centeredSelfAdjointRandomMatrixFamily_negRandomMatrixFamily
          (P := P) (A := centeredSampleCovarianceRowRankOneFamily (P := P) A)
          hCentered
  have hIndepSANeg :
      IndependentSelfAdjointRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) := by
    simpa [centeredSampleCovarianceRowRankOneFamilyNeg] using
      independentSelfAdjointRandomMatrices_negRandomMatrixFamily
        (P := P) (A := centeredSampleCovarianceRowRankOneFamily (P := P) A)
        hIndepSA
  have hIntXNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k) :=
    centeredSampleCovarianceRowRankOneFamilyNeg_integrable_of_memLp_two
      (P := P) (A := A) hLp
  have hBoundNeg :
      PointwiseOperatorNormBound
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (sampleCovarianceCenteredRankOneRadius Rneg) :=
    PointwiseOperatorNormBound_centeredSampleCovarianceRowRankOneFamilyNeg_of_rowSqNorm_bound
      (P := P) A hMeas hLp hSqNeg hRNeg.le
  exact
    sampleCovariance_opNorm_tail_pos_rowSqNorm
      (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
      hm hMeas hLp hSq hIndep hIntSq hExpInt hTraceInt hR ht hCFC
      hTropp hCenteredNeg hIndepSANeg hIntXNeg hIntSqNeg hExpIntNeg
      hTraceIntNeg hBoundNeg hRNeg hCFCNeg hTroppNeg

/-- Bounded-row sample-covariance operator-norm wrapper using negative-family
adapters and the proved Bernstein CFC hardbone leaf.

This is the CFC-free variant of
`sampleCovariance_opNorm_tail_pos_rowSqNorm_negAdapters`:
it still leaves negative square/exponential/trace integrability and both
sign-specific finite-family Tropp/Lieb primitives explicit. -/
theorem sampleCovariance_opNorm_tail_pos_rowSqNorm_negAdapters_troppPrimitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m n)
    (R Rneg t : Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hSqNeg :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= Rneg)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hIntSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k)))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t
              (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))))
    (hR : 0 < R)
    (ht : 0 < t)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
        (sampleCovarianceCenteredRankOneRadius R))
    (hIntSqNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k)))
    (hExpIntNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            (sampleCovarianceTailTheta (m := m) Rneg t
              (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
            k))
    (hTraceIntNeg :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSumNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))))
    (hRNeg : 0 < Rneg)
    (hTroppNeg :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
          (sampleCovarianceCenteredRankOneRadius Rneg))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
        (sampleCovarianceTailTheta (m := m) Rneg t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
        (sampleCovarianceCenteredRankOneRadius Rneg)) :
    P (SelfAdjointOperatorNormTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R) +
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) Rneg t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg) := by
  exact
    sampleCovariance_opNorm_tail_pos_rowSqNorm_negAdapters
      (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
      hm hMeas hLp hSq hSqNeg hIndep hIntSq hExpInt hTraceInt hR ht
      (fun k omega =>
        bernsteinMatrixExp_le_quadratic
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
          (sampleCovarianceCenteredRankOneRadius R))
      hTropp hIntSqNeg hExpIntNeg hTraceIntNeg hRNeg
      (fun k omega =>
        bernsteinMatrixExp_le_quadratic
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
          (sampleCovarianceCenteredRankOneRadius Rneg))
      hTroppNeg

/--
Bounded-row sample-covariance operator-norm wrapper with negative-family
adapters and the square-integrability transfer `(-X)^2 = X^2`.

Compared with
`sampleCovariance_opNorm_tail_pos_rowSqNorm_negAdapters`,
this removes the explicit negative-side square-integrability hypothesis.  The
negative-side matrix-exponential integrability, trace-integrability, CFC, and
Tropp primitives remain explicit because they are not pointwise square rewrites.
-/
theorem sampleCovariance_opNorm_tail_pos_rowSqNorm_negSquareAdapters
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m n)
    (R Rneg t : Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hSqNeg :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= Rneg)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hIntSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k)))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t
              (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))))
    (hR : 0 < R)
    (ht : 0 < t)
    (hCFC :
      forall k : Fin m, forall omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
          (sampleCovarianceCenteredRankOneRadius R))
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
        (sampleCovarianceCenteredRankOneRadius R))
    (hExpIntNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            (sampleCovarianceTailTheta (m := m) Rneg t
              (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
            k))
    (hTraceIntNeg :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSumNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))))
    (hRNeg : 0 < Rneg)
    (hCFCNeg :
      forall k : Fin m, forall omega,
        bernsteinMatrixExpLeQuadraticStatement
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            k omega)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
          (sampleCovarianceCenteredRankOneRadius Rneg))
    (hTroppNeg :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
          (sampleCovarianceCenteredRankOneRadius Rneg))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
        (sampleCovarianceTailTheta (m := m) Rneg t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
        (sampleCovarianceCenteredRankOneRadius Rneg)) :
    P (SelfAdjointOperatorNormTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R) +
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) Rneg t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg) := by
  have hIntSqNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k)) :=
    centeredSampleCovarianceRowRankOneFamilyNeg_squareIntegrable_of_squareIntegrable
      (P := P) (A := A) hIntSq
  exact
    sampleCovariance_opNorm_tail_pos_rowSqNorm_negAdapters
      (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
      hm hMeas hLp hSq hSqNeg hIndep hIntSq hExpInt hTraceInt hR ht
      hCFC hTropp hIntSqNeg hExpIntNeg hTraceIntNeg hRNeg hCFCNeg
      hTroppNeg

/--
Preferred bounded-row sample-covariance operator-norm wrapper after the
Bernstein CFC hardbone leaf.

This is the CFC-free version of
`sampleCovariance_opNorm_tail_pos_rowSqNorm_negSquareAdapters`.
It still keeps the sign-specific finite-family Tropp/Lieb primitives and
integrability assumptions explicit, but fills both pointwise Bernstein CFC
premises with the proved theorem `bernsteinMatrixExp_le_quadratic`. -/
theorem sampleCovariance_opNorm_tail_pos_rowSqNorm_negSquare_troppPrimitives
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m n)
    (R Rneg t : Real)
    (hm : 0 < m)
    (hMeas : IsRandomMatrix P A)
    (hLp :
      forall k : Fin m, forall j : Fin n,
        MemLpRealRandomVariable P (matrixEntry A k j) 2)
    (hSq :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= R)
    (hSqNeg :
      forall k : Fin m, forall omega,
        vectorSqNorm (rowVector A k omega) <= Rneg)
    (hIndep :
      IndependentRandomMatrices P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
    (hIntSq :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (randomMatrixSquare
            ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k)))
    (hExpInt :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamily (P := P) A)
            (sampleCovarianceTailTheta (m := m) R t
              (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
            k))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSum (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))))
    (hR : 0 < R)
    (ht : 0 < t)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
          (sampleCovarianceCenteredRankOneRadius R))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamily (P := P) A))
        (sampleCovarianceTailTheta (m := m) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
        (sampleCovarianceCenteredRankOneRadius R))
    (hExpIntNeg :
      forall k : Fin m,
        IntegrableRandomMatrix P
          (matrixExpScaledFamily
            (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
            (sampleCovarianceTailTheta (m := m) Rneg t
              (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
            k))
    (hTraceIntNeg :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (centeredSampleCovarianceRowRankOneSumNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))))
    (hRNeg : 0 < Rneg)
    (hTroppNeg :
      troppMasterTraceMGFFiniteFamilyStatement
        (P := P)
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (bernsteinSecondMomentComparisonFamily P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
          (sampleCovarianceCenteredRankOneRadius Rneg))
        (matrixVarianceProxy P
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
        (sampleCovarianceTailTheta (m := m) Rneg t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
        (sampleCovarianceCenteredRankOneRadius Rneg)) :
    P (SelfAdjointOperatorNormTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R) +
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) Rneg t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg) := by
  exact
    sampleCovariance_opNorm_tail_pos_rowSqNorm_negSquareAdapters
      (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
      hm hMeas hLp hSq hSqNeg hIndep hIntSq hExpInt hTraceInt hR ht
      (fun k omega =>
        bernsteinMatrixExp_le_quadratic
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
          (sampleCovarianceCenteredRankOneRadius R))
      hTropp hExpIntNeg hTraceIntNeg hRNeg
      (fun k omega =>
        bernsteinMatrixExp_le_quadratic
          ((centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A) k omega)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
          (sampleCovarianceCenteredRankOneRadius Rneg))
      hTroppNeg

/-- Explicit-row-count variance-proxy aliases unfold to the implicit form. -/
theorem sampleCovarianceCenteredRankOneVarianceProxyBoundOfRows_eq
    (m : Nat) (R : Real) :
    sampleCovarianceCenteredRankOneVarianceProxyBoundOfRows m R =
      sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R :=
  rfl

/-- Public target axis for the compact bounded-row sample-covariance tail route.

This keeps the target choice explicit without encoding it into a separate
top-level theorem name for each route. -/
inductive SampleCovarianceTailTarget where
  | quadraticFormUpper
  | selfAdjointOperatorNorm
deriving DecidableEq

namespace SampleCovarianceTailTarget

/-- Tail event selected by `SampleCovarianceTailTarget`. -/
def event {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {m n : Nat} (target : SampleCovarianceTailTarget)
    (A : RandomMatrix Omega m n) (t : Real) : Set Omega :=
  match target with
  | quadraticFormUpper =>
      quadraticFormUpperTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t
  | selfAdjointOperatorNorm =>
      SelfAdjointOperatorNormTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t

/-- Scalar tail RHS selected by `SampleCovarianceTailTarget`. -/
def rhs (target : SampleCovarianceTailTarget) (m n : Nat)
    (R Rneg t : Real) : ENNReal :=
  match target with
  | quadraticFormUpper =>
      sampleCovarianceQuadraticFormTailRHS
        (m := m) (n := n) R t
        (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R)
  | selfAdjointOperatorNorm =>
      sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R) +
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n) Rneg t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg)

end SampleCovarianceTailTarget

/-- Assumption record for the compact bounded-row sample-covariance Tropp route.

This is the preferred public surface when users want a single readable package
for the uniform bounded-row route. It exposes the common positive-side row
assumptions and the remaining negative-side Tropp/integrability providers, but
does not include any finite-family tail conclusion as a field. For a
positive-side-only quadratic-form statement with fewer assumptions, keep using
the lower-level quadratic-form wrapper directly. -/
structure SampleCovarianceBoundedRowTroppAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {m n : Nat}
    (A : RandomMatrix Omega m (n + 1))
    (R Rneg t : Real) : Prop where
  sampleCountPositive : 0 < m
  randomMatrix : IsRandomMatrix P A
  coordinateMemLpTwo :
    forall k : Fin m, forall j : Fin (n + 1),
      MemLpRealRandomVariable P (matrixEntry A k j) 2
  rowSqNormBound :
    forall k : Fin m, forall omega,
      vectorSqNorm (rowVector A k omega) <= R
  rowSqNormBoundNeg :
    forall k : Fin m, forall omega,
      vectorSqNorm (rowVector A k omega) <= Rneg
  independentRows :
    IndependentRandomMatrices P
      (centeredSampleCovarianceRowRankOneFamily (P := P) A)
  squareIntegrable :
    forall k : Fin m,
      IntegrableRandomMatrix P
        (randomMatrixSquare
          ((centeredSampleCovarianceRowRankOneFamily (P := P) A) k))
  expIntegrable :
    forall k : Fin m,
      IntegrableRandomMatrix P
        (matrixExpScaledFamily
          (centeredSampleCovarianceRowRankOneFamily (P := P) A)
          (sampleCovarianceTailTheta (m := m) R t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
          k)
  traceExpIntegrable :
    IntegrableRealRandomVariable P
      (traceExpIntegrand
        (centeredSampleCovarianceRowRankOneSum (P := P) A)
        (sampleCovarianceTailTheta (m := m) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R)))
  radiusPositive : 0 < R
  deviationPositive : 0 < t
  troppPrimitive :
    troppMasterTraceMGFFiniteFamilyStatement
      (P := P)
      (centeredSampleCovarianceRowRankOneFamily (P := P) A)
      (bernsteinSecondMomentComparisonFamily P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A)
        (sampleCovarianceTailTheta (m := m) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
        (sampleCovarianceCenteredRankOneRadius R))
      (matrixVarianceProxy P
        (centeredSampleCovarianceRowRankOneFamily (P := P) A))
      (sampleCovarianceTailTheta (m := m) R t
        (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R))
      (sampleCovarianceCenteredRankOneRadius R)
  expIntegrableNeg :
    forall k : Fin m,
      IntegrableRandomMatrix P
        (matrixExpScaledFamily
          (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
          (sampleCovarianceTailTheta (m := m) Rneg t
            (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
          k)
  traceExpIntegrableNeg :
    IntegrableRealRandomVariable P
      (traceExpIntegrand
        (centeredSampleCovarianceRowRankOneSumNeg (P := P) A)
        (sampleCovarianceTailTheta (m := m) Rneg t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg)))
  negativeRadiusPositive : 0 < Rneg
  troppPrimitiveNeg :
    troppMasterTraceMGFFiniteFamilyStatement
      (P := P)
      (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
      (bernsteinSecondMomentComparisonFamily P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A)
        (sampleCovarianceTailTheta (m := m) Rneg t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
        (sampleCovarianceCenteredRankOneRadius Rneg))
      (matrixVarianceProxy P
        (centeredSampleCovarianceRowRankOneFamilyNeg (P := P) A))
      (sampleCovarianceTailTheta (m := m) Rneg t
        (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg))
      (sampleCovarianceCenteredRankOneRadius Rneg)

/-- Compact bounded-row sample-covariance tail theorem.

The target parameter selects either the quadratic-form upper tail or the
self-adjoint operator-norm tail. This theorem is a consolidation layer over the
existing proved wrappers; it avoids making every target/provider/adapter
combination a separate recommended public theorem name. -/
theorem sampleCovariance_tail_optimized_under_boundedRowTroppAssumptions
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m (n + 1))
    (R Rneg t : Real)
    (target : SampleCovarianceTailTarget)
    (h : SampleCovarianceBoundedRowTroppAssumptions (P := P) A R Rneg t) :
    P (SampleCovarianceTailTarget.event (P := P) target A t) <=
      SampleCovarianceTailTarget.rhs target m (n + 1) R Rneg t := by
  cases target with
  | quadraticFormUpper =>
      simpa [SampleCovarianceTailTarget.event,
        SampleCovarianceTailTarget.rhs] using
        sampleCovariance_quadraticForm_tail_optimized_under_rowSqNorm_bound_of_troppPrimitive
          (P := P) A R t
          h.sampleCountPositive h.randomMatrix h.coordinateMemLpTwo
          h.rowSqNormBound h.independentRows h.squareIntegrable
          h.expIntegrable h.traceExpIntegrable h.radiusPositive
          h.deviationPositive h.troppPrimitive
  | selfAdjointOperatorNorm =>
      simpa [SampleCovarianceTailTarget.event,
        SampleCovarianceTailTarget.rhs] using
        sampleCovariance_opNorm_tail_pos_rowSqNorm_negSquare_troppPrimitives
          (P := P) A R Rneg t
          h.sampleCountPositive h.randomMatrix h.coordinateMemLpTwo
          h.rowSqNormBound h.rowSqNormBoundNeg h.independentRows
          h.squareIntegrable h.expIntegrable h.traceExpIntegrable
          h.radiusPositive h.deviationPositive h.troppPrimitive
          h.expIntegrableNeg h.traceExpIntegrableNeg
          h.negativeRadiusPositive h.troppPrimitiveNeg

/-- Typed contract from a trace-MGF bound to the quadratic-form Laplace tail step. -/
abbrev matrixBernsteinTraceMGFToLaplaceContractStatement {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} [Fintype I] {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) (theta t R : Real) : Prop :=
  AEMeasurable
    (fun omega => ENNReal.ofReal (traceExpIntegrand (randomMatrixSum A) theta omega)) P ->
    (quadraticFormUpperTailEvent (randomMatrixSum A) t ⊆
      traceExpThresholdEvent (randomMatrixSum A) theta t) ->
      TraceMGFBernsteinVarianceProxyBoundLIntegral P (randomMatrixSum A)
        (matrixVarianceProxy P A) theta R ->
        P (quadraticFormUpperTailEvent (randomMatrixSum A) t) <=
          ENNReal.ofReal (Real.exp (-(theta * t))) *
            ENNReal.ofReal
              (traceMatrixExp
                (SMul.smul (bernsteinMGFCoeff theta R) (matrixVarianceProxy P A)))

/-- Typed contract for feeding the proved MB-S9 bounded trace-MGF result into the
Laplace/tail layer.

The proved theorem under primitives supplies the premise
`matrixBernsteinTraceMGFWithCoeffStatement P A theta R`; this contract
keeps the remaining downstream gaps visible instead of hiding them:
1. AEMeasurability of the trace-exp integrand ENNReal lift,
2. The event-subset bridge `quadraticFormUpperTailEvent ⊆ traceExpThresholdEvent`,
3. The real-to-lintegral trace-MGF bridge from `TraceMGFBernsteinVarianceProxyBound`
   to `TraceMGFBernsteinVarianceProxyBoundLIntegral`.
-/
abbrev matrixBernsteinTraceMGFToLaplaceContractUnderPrimitivesStatement
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    {I : Type*} [Fintype I] {n : Nat}
    (A : I -> RandomMatrix Omega n n) (theta t R : Real) : Prop :=
  let Y := randomMatrixSum A
  let V := matrixVarianceProxy P A
  AEMeasurable (fun omega => ENNReal.ofReal (traceExpIntegrand Y theta omega)) P ->
    (quadraticFormUpperTailEvent Y t ⊆ traceExpThresholdEvent Y theta t) ->
      IntegrableRealRandomVariable P (traceExpIntegrand Y theta) ->
        (forall omega, 0 <= traceExpIntegrand Y theta omega) ->
          matrixBernsteinTraceMGFWithCoeffStatement P A theta R ->
            P (quadraticFormUpperTailEvent Y t) <=
              ENNReal.ofReal (Real.exp (-(theta * t))) *
                ENNReal.ofReal
                  (traceMatrixExp (SMul.smul (bernsteinMGFCoeff theta R) V))

/-- Named assumption bundle for the S10 conditioning trace-MGF to tail route.

This structure packages exactly the explicit S9 conditioning trace-MGF premises
and the two tail-side bridge premises consumed by
`matrixBernsteinQuadraticFormUpperTail_of_conditioningTraceMGFBridge`. It is an
assumption contract only: it does not prove conditioning, tail domination,
integrability propagation, variance-proxy control, or an unconditional Matrix
Bernstein theorem. -/
structure MatrixBernsteinConditioningTraceMGFTailAssumptions
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P] {m n : Nat}
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real)
    (V : Matrix (Fin n) (Fin n) Real)
    (theta R t : Real)
    (mHist : Fin m -> MeasurableSpace Omega) : Prop where
  chain :
    @troppConditionalStepOfIIndepFunStatement Omega mOmega P m n
      theta X K mHist
  historyMeasurable :
    @troppNaturalHistoryMeasurableStatement Omega mOmega m n
      theta X K mHist
  historyStepIndependent :
    @troppHistoryStepIndependentOfIIndepFunStatement Omega mOmega P m n
      theta X K
  conditionalExpectation :
    forall i,
      @condExpTraceExpHistoryAddIndependentStepStatement
        Omega mOmega P n
        (mHist i) (@troppStateHistory Omega m n theta X K i)
        (@troppCurrentRandomStep Omega m n theta X i) (K i)
  historySub : forall i, mHist i <= mOmega
  historyRandom :
    forall i,
      @IsRandomMatrix Omega mOmega n n P
        (troppStateHistory theta X K i)
  stepRandom :
    forall i,
      @IsRandomMatrix Omega mOmega n n P
        (troppCurrentRandomStep theta X i)
  historySelfAdjoint :
    forall i omega, IsSelfAdjointMatrix (troppStateHistory theta X K i omega)
  stepSelfAdjoint :
    forall i,
      @RandomSelfAdjointMatrix Omega mOmega n P
        (troppCurrentRandomStep theta X i)
  conditionalTraceIntegrable :
    forall i,
      @IntegrableRealRandomVariable Omega mOmega P
        (fun omega =>
          traceMatrixExp
            (troppStateHistory theta X K i omega +
              troppCurrentRandomStep theta X i omega))
  stepExpIntegrable :
    forall i,
      @IntegrableRandomMatrix Omega mOmega n n P
        (fun omega => matrixExp (troppCurrentRandomStep theta X i omega))
  expMeanSelfAdjoint :
    forall i,
      IsSelfAdjointMatrix
        (@matrixExpect Omega mOmega n n P
          (fun omega => matrixExp (troppCurrentRandomStep theta X i omega)))
  expMeanStrictlyPositive :
    forall i,
      IsStrictlyPositive
        (@matrixExpect Omega mOmega n n P
          (fun omega => matrixExp (troppCurrentRandomStep theta X i omega)))
  sigmaFiniteHistory : forall i, SigmaFinite (P.trim (historySub i))
  rhsTraceIntegrable :
    forall i,
      @IntegrableRealRandomVariable Omega mOmega P
        (fun omega =>
          traceMatrixExp (troppStateHistory theta X K i omega + K i))
  randomMatrix : forall i, IsRandomMatrix P (X i)
  selfAdjoint : forall i, RandomSelfAdjointMatrix P (X i)
  independent : ProbabilityTheory.iIndepFun X P
  expIntegrable :
    forall i,
      IntegrableRandomMatrix P
        (fun omega => matrixExp (SMul.smul theta (X i omega)))
  traceIntegrable :
    IntegrableRealRandomVariable P
      (traceExpIntegrand (randomMatrixSum X) theta)
  comparisonSelfAdjoint : forall i, IsSelfAdjointMatrix (K i)
  varianceProxySelfAdjoint : IsSelfAdjointMatrix V
  radiusNonneg : 0 <= R
  thetaRange : abs theta * R < 3
  mgfComparison :
    forall i,
      MatrixLE
        (matrixExpect P
          (fun omega => matrixExp (SMul.smul theta (X i omega))))
        (matrixExp (K i))
  varianceProxyNormalization :
    Finset.univ.sum (fun i : Fin m => K i) =
      SMul.smul (bernsteinMGFCoeff theta R) V
  tailAEMeasurable :
    AEMeasurable
      (fun omega => ENNReal.ofReal
        (traceExpIntegrand (randomMatrixSum X) theta omega)) P
  tailEventSubset :
    quadraticFormUpperTailEvent (randomMatrixSum X) t ⊆
      traceExpThresholdEvent (randomMatrixSum X) theta t

/-- Progress-first composition from the S9 conditioning trace-MGF bridge to the
quadratic-form Laplace/tail bound.

This wrapper is intentionally thin.  It first obtains the finite-family
Bernstein trace-MGF conclusion from
`traceMGFBernsteinVarianceProxyBound_of_conditioningBridge`, then uses the
already-proved real-to-`lintegral` bridge and the explicit tail-side
`quadraticFormUpperTailEvent ⊆ traceExpThresholdEvent` assumption to enter the
Laplace route.  It does not prove the tail event domination, Tropp/Lieb,
conditional-expectation, integrability propagation, variance-proxy facts, or a
full Matrix Bernstein theorem. -/
theorem matrixBernsteinQuadraticFormUpperTail_of_conditioningTraceMGFBridge
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P] {m n : Nat}
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real)
    (V : Matrix (Fin n) (Fin n) Real)
    (theta R t : Real)
    (mHist : Fin m -> MeasurableSpace Omega)
    (hChain :
      @troppConditionalStepOfIIndepFunStatement Omega mOmega P m n
        theta X K mHist)
    (hHist :
      @troppNaturalHistoryMeasurableStatement Omega mOmega m n
        theta X K mHist)
    (hHistIndep :
      @troppHistoryStepIndependentOfIIndepFunStatement Omega mOmega P m n
        theta X K)
    (hCondExp :
      forall i,
        @condExpTraceExpHistoryAddIndependentStepStatement
          Omega mOmega P n
          (mHist i) (@troppStateHistory Omega m n theta X K i)
          (@troppCurrentRandomStep Omega m n theta X i) (K i))
    (hHistSub : forall i, mHist i <= mOmega)
    (hHistRand :
      forall i,
        @IsRandomMatrix Omega mOmega n n P
          (troppStateHistory theta X K i))
    (hZRand :
      forall i,
        @IsRandomMatrix Omega mOmega n n P
          (troppCurrentRandomStep theta X i))
    (hHistSA :
      forall i omega, IsSelfAdjointMatrix (troppStateHistory theta X K i omega))
    (hZSA :
      forall i,
        @RandomSelfAdjointMatrix Omega mOmega n P
          (troppCurrentRandomStep theta X i))
    (hCondTraceInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega =>
            traceMatrixExp
              (troppStateHistory theta X K i omega +
                troppCurrentRandomStep theta X i omega)))
    (hExpIntStep :
      forall i,
        @IntegrableRandomMatrix Omega mOmega n n P
          (fun omega => matrixExp (troppCurrentRandomStep theta X i omega)))
    (hExpMeanSA :
      forall i,
        IsSelfAdjointMatrix
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (troppCurrentRandomStep theta X i omega))))
    (hExpMeanPos :
      forall i,
        IsStrictlyPositive
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (troppCurrentRandomStep theta X i omega))))
    (hSigma : forall i, SigmaFinite (P.trim (hHistSub i)))
    (hRhsInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega =>
            traceMatrixExp (troppStateHistory theta X K i omega + K i)))
    (hRand : forall i, IsRandomMatrix P (X i))
    (hSA : forall i, RandomSelfAdjointMatrix P (X i))
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hExpInt :
      forall i,
        IntegrableRandomMatrix P
          (fun omega => matrixExp (SMul.smul theta (X i omega))))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum X) theta))
    (hKSA : forall i, IsSelfAdjointMatrix (K i))
    (hVSA : IsSelfAdjointMatrix V)
    (hR : 0 <= R)
    (hRange : abs theta * R < 3)
    (hMGF :
      forall i,
        MatrixLE
          (matrixExpect P
            (fun omega => matrixExp (SMul.smul theta (X i omega))))
          (matrixExp (K i)))
    (hNorm :
      Finset.univ.sum (fun i : Fin m => K i) =
        SMul.smul (bernsteinMGFCoeff theta R) V)
    (hTailMeas :
      AEMeasurable
        (fun omega => ENNReal.ofReal
          (traceExpIntegrand (randomMatrixSum X) theta omega)) P)
    (hTailSubset :
      quadraticFormUpperTailEvent (randomMatrixSum X) t ⊆
        traceExpThresholdEvent (randomMatrixSum X) theta t) :
    P (quadraticFormUpperTailEvent (randomMatrixSum X) t) <=
      ENNReal.ofReal (Real.exp (-(theta * t))) *
        ENNReal.ofReal
          (traceMatrixExp (SMul.smul (bernsteinMGFCoeff theta R) V)) := by
  have hTraceMGF :
      TraceMGFBernsteinVarianceProxyBound P (randomMatrixSum X) V theta R :=
    traceMGFBernsteinVarianceProxyBound_of_conditioningBridge
      X K V theta R mHist hChain hHist hHistIndep hCondExp hHistSub
      hHistRand hZRand hHistSA hZSA hCondTraceInt hExpIntStep hExpMeanSA
      hExpMeanPos hSigma hRhsInt hRand hSA hIndep hExpInt hTraceInt hKSA
      hVSA hR hRange hMGF hNorm
  have hY : RandomSelfAdjointMatrix P (randomMatrixSum X) :=
    randomSelfAdjointMatrix_sum hSA
  have hLInt :
      TraceMGFBernsteinVarianceProxyBoundLIntegral P (randomMatrixSum X)
        V theta R :=
    traceMGFBernsteinVarianceProxyBoundLIntegral_of_traceMGFBernsteinVarianceProxyBound
      (randomMatrixSum X) V theta R hY hTraceInt hTraceMGF
  exact
    quadraticFormUpperTail_laplace_bound_of_traceMGFBernsteinVarianceProxyBoundLIntegral
      (randomMatrixSum X) V theta t R hTailMeas hTailSubset hLInt

/-- Bundle-based S10 wrapper for the conditioning trace-MGF to tail route.

This is only a field-access wrapper around
`matrixBernsteinQuadraticFormUpperTail_of_conditioningTraceMGFBridge`; the
bundle name records that the assumptions are still tail/conditioning premises,
not a full or unconditional Matrix Bernstein theorem. -/
theorem matrixBernsteinQuadraticFormUpperTail_of_conditioningTraceMGFTailAssumptions
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P] {m n : Nat}
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real)
    (V : Matrix (Fin n) (Fin n) Real)
    (theta R t : Real)
    (mHist : Fin m -> MeasurableSpace Omega)
    (h : MatrixBernsteinConditioningTraceMGFTailAssumptions
      (P := P) X K V theta R t mHist) :
    P (quadraticFormUpperTailEvent (randomMatrixSum X) t) <=
      ENNReal.ofReal (Real.exp (-(theta * t))) *
        ENNReal.ofReal
          (traceMatrixExp (SMul.smul (bernsteinMGFCoeff theta R) V)) := by
  exact
    matrixBernsteinQuadraticFormUpperTail_of_conditioningTraceMGFBridge
      X K V theta R t mHist
      h.chain h.historyMeasurable h.historyStepIndependent
      h.conditionalExpectation h.historySub h.historyRandom h.stepRandom
      h.historySelfAdjoint h.stepSelfAdjoint h.conditionalTraceIntegrable
      h.stepExpIntegrable h.expMeanSelfAdjoint h.expMeanStrictlyPositive
      h.sigmaFiniteHistory h.rhsTraceIntegrable h.randomMatrix h.selfAdjoint
      h.independent h.expIntegrable h.traceIntegrable h.comparisonSelfAdjoint
      h.varianceProxySelfAdjoint h.radiusNonneg h.thetaRange h.mgfComparison
      h.varianceProxyNormalization h.tailAEMeasurable h.tailEventSubset

/-- Typed target for the spectral-radius reduction for self-adjoint matrices.

This records a future bridge between HighDimProb's deterministic L2 operator
norm wrapper and Mathlib's spectral radius. It is not a theorem. -/
abbrev operatorNormEqSpectralRadiusOfSelfAdjointStatement {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) : Prop :=
  IsSelfAdjointMatrix A ->
    deterministicOperatorNorm A = (spectralRadius ℝ A).toReal

/-- Lightweight high-probability bound notation.

`HighProbabilityBound P event rhs` means that `P(event) <= rhs`.
This is a thin wrapper around measure comparison for readability. -/
def HighProbabilityBound {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (event : Set Omega) (rhs : ENNReal) : Prop :=
  P event <= rhs

/-- Variant of `HighProbabilityBound` for events given as `Set Omega`. -/
abbrev highProbabilityBound {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (event : Set Omega) (rhs : ENNReal) : Prop :=
  HighProbabilityBound P event rhs

/-- Typed target for a future matrix Hoeffding theorem. -/
abbrev matrixHoeffdingStatement {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} [Fintype I] {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) (R c t : Real) : Prop :=
  CenteredRandomSelfAdjointMatrices P A ->
    IndependentRandomMatrices P A ->
      PointwiseOperatorNormBound A R ->
        0 <= t ->
          upperTailProb P (operatorNorm (randomMatrixSum A)) t <=
            ENNReal.ofReal
              (2 * (n : Real) * Real.exp (-(c * t ^ 2 / ((Fintype.card I : Real) * R ^ 2))))

/-- Typed target for a future matrix Chernoff theorem for PSD summands. -/
abbrev matrixChernoffStatement {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} [Fintype I] {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) (R c t : Real) : Prop :=
  (forall i, RandomPSDMatrix P (A i)) ->
    IndependentRandomMatrices P A ->
      PointwiseOperatorNormBound A R ->
        0 <= t ->
          upperTailProb P (operatorNorm (randomMatrixSum A)) t <=
            ENNReal.ofReal (2 * (n : Real) * Real.exp (-(c * t / R)))

/-- Typed target for future operator-norm covariance estimation from subGaussian isotropic rows. -/
abbrev covarianceEstimationStatement {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (P : Measure Omega) (A : RandomMatrix Omega m n)
    (K c t : Real) : Prop :=
  IsRandomMatrix P A ->
    SubGaussianRowsOrlicz P A K ->
      IsotropicRowsSecondMoment P A ->
        0 <= t ->
          upperTailProb P (operatorNorm (sampleCovarianceMinusIdentity A)) t <=
            ENNReal.ofReal (2 * Real.exp (-(c * t ^ 2)))

/-- Absolute quadratic-form deviation of the centered sample covariance. -/
def sampleCovarianceQuadraticFormDeviation {Omega : Type*}
    {m n : Nat} (A : RandomMatrix Omega m n) (x : Fin n -> Real) :
    RealRandomVariable Omega :=
  fun omega => abs (matrixQuadraticForm (sampleCovarianceMinusIdentity A omega) x)

/-- Typed target for a future unit-sphere reduction of sample-covariance
operator-norm tails. This is a statement dependency, not a proved concentration
or covering theorem. -/
abbrev sampleCovarianceOperatorNormViaUnitSphereStatement {Omega : Type*}
    [MeasurableSpace Omega] {m n : Nat} (P : Measure Omega)
    (A : RandomMatrix Omega m n) (t bound : Real) : Prop :=
  0 <= bound ->
    (forall x : Fin n -> Real,
      IsUnitVector x ->
        upperTailProb P (sampleCovarianceQuadraticFormDeviation A x) t <=
          ENNReal.ofReal bound) ->
      upperTailProb P (operatorNorm (sampleCovarianceMinusIdentity A)) t <=
        ENNReal.ofReal bound

/-- Typed target for a generic sample-covariance operator-norm tail statement. -/
abbrev sampleCovarianceOperatorNormStatement {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (P : Measure Omega) (A : RandomMatrix Omega m n)
    (t bound : Real) : Prop :=
  0 <= bound ->
    upperTailProb P (operatorNorm (sampleCovariance A)) t <= ENNReal.ofReal bound

end

end HighDimProb
