/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import Mathlib.Probability.Independence.Basic
import LeanPool.HighDimProb.RandomMatrix.Expectation
import LeanPool.HighDimProb.RandomMatrix.OperatorNorm
import LeanPool.HighDimProb.RandomMatrix.RowsCols
import LeanPool.HighDimProb.RandomMatrix.SelfAdjoint
import LeanPool.HighDimProb.RandomMatrix.VarianceProxy
import LeanPool.HighDimProb.SubGaussianVector
import LeanPool.HighDimProb.Isotropic

/-!
# Random matrix assumption predicates and adapters

This module is the RandomMatrix theorem-interface layer.  The name
`Assumptions` means "hypotheses consumed by matrix concentration statements",
not "all possible matrix facts".

Keep the boundary as follows:
* Core objects and pointwise algebra belong in `Basic`, `Expectation`,
  `SelfAdjoint`, `MatrixOrder`, and `OperatorNorm`.
* This file may define assumption predicates such as entrywise subGaussian,
  centered/self-adjoint family, independence, and operator-norm boundedness.
* This file may also define thin adapters that turn those assumptions into the
  exact hypotheses needed by Matrix Bernstein examples, such as centered
  structural wrappers and rank-one boundedness wrappers.
* Avoid adding domain-specific objects here.  Prefer a named object in the
  object layer, then add only the reusable assumption/adapter theorem here.

Verified Wikipedia references:
* Random matrix: https://en.wikipedia.org/wiki/Random_matrix
* Sub-Gaussian distribution: https://en.wikipedia.org/wiki/Sub-Gaussian_distribution
* Isotropic position: https://en.wikipedia.org/wiki/Isotropic_position
* Self-adjoint operator: https://en.wikipedia.org/wiki/Self-adjoint_operator
* Operator norm: https://en.wikipedia.org/wiki/Operator_norm
* Independence: https://en.wikipedia.org/wiki/Independence_(probability_theory)
-/

namespace HighDimProb

open MeasureTheory
open scoped Matrix.Norms.L2Operator

/-! ## Statement-level assumption predicates -/

/-- Entrywise Orlicz subGaussian assumption with common scale `K`. -/
def SubGaussianEntriesOrlicz {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (P : Measure Omega) (A : RandomMatrix Omega m n) (K : Real) : Prop :=
  forall i : Fin m, forall j : Fin n, SubGaussianOrlicz P (matrixEntry A i j) K

/-- Entrywise tail-form subGaussian assumption with common scale `K`. -/
def SubGaussianEntriesTail {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (P : Measure Omega) (A : RandomMatrix Omega m n) (K : Real) : Prop :=
  forall i : Fin m, forall j : Fin n, SubGaussianTail P (matrixEntry A i j) K

/-- Rowwise Orlicz subGaussian assumption with common scale `K`. -/
def SubGaussianRowsOrlicz {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (P : Measure Omega) (A : RandomMatrix Omega m n) (K : Real) : Prop :=
  forall i : Fin m, SubGaussianVectorOrlicz P (rowVector A i) K

/-- Each row is isotropic in the second-moment formulation. -/
def IsotropicRowsSecondMoment {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (P : Measure Omega) (A : RandomMatrix Omega m n) : Prop :=
  forall i : Fin m, IsotropicSecondMoment P (rowVector A i)

/-- Each row is isotropic in the covariance formulation. -/
def IsotropicRowsCovariance {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (P : Measure Omega) (A : RandomMatrix Omega m n) : Prop :=
  forall i : Fin m, IsotropicCovariance P (rowVector A i)

/-- Entrywise centeredness assumption. -/
def CenteredEntries {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (P : Measure Omega) (A : RandomMatrix Omega m n) : Prop :=
  forall i : Fin m, forall j : Fin n, Centered P (matrixEntry A i j)

/-- Matrix-valued independence wrapper around Mathlib `ProbabilityTheory.iIndepFun`. -/
abbrev IndependentRandomMatrices {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} {m n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega m n) : Prop :=
  ProbabilityTheory.iIndepFun A P

/-- A finite or indexed family of random self-adjoint square matrices. -/
def SelfAdjointRandomMatrixFamily {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) : Prop :=
  (forall i, IsRandomMatrix P (A i)) /\
    (forall i, RandomSelfAdjointMatrix P (A i))

/-- Independent self-adjoint random matrix family. -/
def IndependentSelfAdjointRandomMatrices {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) : Prop :=
  SelfAdjointRandomMatrixFamily P A /\ IndependentRandomMatrices P A

/-- Pointwise self-adjoint family with entrywise zero mean expressed through
the entrywise matrix expectation. -/
def CenteredSelfAdjointRandomMatrixFamily {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) : Prop :=
  SelfAdjointRandomMatrixFamily P A /\ forall i, matrixExpect P (A i) = 0

/-! ## Centering and rank-one structural adapters -/

/-- The entrywise expectation of a pointwise self-adjoint random matrix is self-adjoint. -/
theorem isSelfAdjointMatrix_matrixExpect_of_randomSelfAdjoint {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    {A : RandomMatrix Omega n n} (hA : RandomSelfAdjointMatrix P A) :
    IsSelfAdjointMatrix (matrixExpect P A) := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star (∫ omega, matrixEntry A j i omega ∂P) =
    ∫ omega, matrixEntry A i j omega ∂P
  have hIntegral :
      (∫ omega, matrixEntry A j i omega ∂P) =
        ∫ omega, matrixEntry A i j omega ∂P := by
    apply integral_congr_ae
    filter_upwards with omega
    simpa [matrixEntry] using Matrix.IsHermitian.apply (hA omega) i j
  exact hIntegral

/-- Centering preserves pointwise self-adjointness of a random matrix. -/
theorem randomSelfAdjointMatrix_centeredRandomMatrix {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    {A : RandomMatrix Omega n n} (hA : RandomSelfAdjointMatrix P A) :
    RandomSelfAdjointMatrix P (centeredRandomMatrix P A) := by
  intro omega
  have hExp : IsSelfAdjointMatrix (matrixExpect P A) :=
    isSelfAdjointMatrix_matrixExpect_of_randomSelfAdjoint (P := P) (A := A) hA
  change IsSelfAdjointMatrix (A omega - matrixExpect P A)
  exact (hA omega).sub hExp

/-- Centering a self-adjoint random matrix lowers its second moment in the
explicit Loewner order. The correction term is the PSD square of the entrywise
mean matrix. -/
theorem matrixSecondMoment_centeredRandomMatrix_le_matrixSecondMoment {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {n : Nat} {A : RandomMatrix Omega n n}
    (hA : IntegrableRandomMatrix P A)
    (hSq : IntegrableRandomMatrix P (randomMatrixSquare A))
    (hSA : RandomSelfAdjointMatrix P A) :
    MatrixLE
      (matrixSecondMoment P (centeredRandomMatrix P A))
      (matrixSecondMoment P A) := by
  have hExpansion :=
    matrixSecondMoment_centeredRandomMatrix (P := P) (A := A) hA hSq
  rw [hExpansion]
  have hMeanSA : IsSelfAdjointMatrix (matrixExpect P A) :=
    isSelfAdjointMatrix_matrixExpect_of_randomSelfAdjoint (P := P) (A := A) hSA
  exact matrixLE_sub_right_of_isPSD
    (matrixSecondMoment P A) (matrixSquare (matrixExpect P A))
    (isPSD_matrixSquare_of_selfAdjoint hMeanSA)

/-- Centering every member of a self-adjoint random-matrix family preserves the family predicate. -/
theorem selfAdjointRandomMatrixFamily_centeredRandomMatrixFamily {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {I : Type*} {n : Nat}
    {A : I -> RandomMatrix Omega n n}
    (hA : SelfAdjointRandomMatrixFamily P A) :
    SelfAdjointRandomMatrixFamily P (centeredRandomMatrixFamily P A) := by
  refine ⟨?_, ?_⟩
  · intro i
    simpa [centeredRandomMatrixFamily] using
      isRandomMatrix_centeredRandomMatrix (P := P) (A := A i) (hA.1 i)
  · intro i
    simpa [centeredRandomMatrixFamily] using
      randomSelfAdjointMatrix_centeredRandomMatrix (P := P) (A := A i) (hA.2 i)

/--
Centering an integrable self-adjoint random-matrix family gives a centered
self-adjoint random-matrix family.
-/
theorem centeredSelfAdjointRandomMatrixFamily_centeredRandomMatrixFamily
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} {n : Nat}
    {A : I -> RandomMatrix Omega n n}
    (hA : SelfAdjointRandomMatrixFamily P A)
    (hInt : forall i, IntegrableRandomMatrix P (A i)) :
    CenteredSelfAdjointRandomMatrixFamily P (centeredRandomMatrixFamily P A) := by
  refine ⟨selfAdjointRandomMatrixFamily_centeredRandomMatrixFamily (P := P)
    (A := A) hA, ?_⟩
  intro i
  simpa [centeredRandomMatrixFamily] using
    matrixExpect_centeredRandomMatrix (P := P) (A := A i) (hInt i)

/--
The centered version of a rank-one random matrix is random whenever the source
vector is random.
-/
theorem centeredRankOneRandomMatrix_isRandomMatrix {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    {X : RandomVector Omega n} (hX : IsRandomVector P X) :
    IsRandomMatrix P (centeredRankOneRandomMatrix P X) := by
  exact isRandomMatrix_centeredRandomMatrix (P := P)
    (A := rankOneRandomMatrix X) (isRandomMatrix_rankOneRandomMatrix hX)

/--
Second-moment coordinates make the centered rank-one random matrix entrywise
integrable.
-/
theorem centeredRankOneRandomMatrix_integrable_of_memLp_two {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsFiniteMeasure P] {n : Nat}
    {X : RandomVector Omega n}
    (hX : forall i : Fin n, MemLpRealRandomVariable P (coord X i) 2) :
    IntegrableRandomMatrix P (centeredRankOneRandomMatrix P X) := by
  exact integrableRandomMatrix_centeredRandomMatrix (P := P)
    (A := rankOneRandomMatrix X)
    (integrableRandomMatrix_rankOneRandomMatrix_of_memLp_two (P := P) (X := X) hX)

/--
Centered rank-one random matrices form a centered self-adjoint family under
random-vector measurability and coordinate second-moment assumptions.
-/
theorem centeredRankOneRandomMatrix_centeredSelfAdjoint_of_memLp_two
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} {n : Nat}
    {X : I -> RandomVector Omega n}
    (hMeas : forall i, IsRandomVector P (X i))
    (hLp : forall i, forall j : Fin n,
      MemLpRealRandomVariable P (coord (X i) j) 2) :
    CenteredSelfAdjointRandomMatrixFamily P
      (centeredRankOneRandomMatrixFamily P X) := by
  have hFamily :
      SelfAdjointRandomMatrixFamily P
        (rankOneRandomMatrixFamily X) := by
    refine ⟨?_, ?_⟩
    · intro i
      exact isRandomMatrix_rankOneRandomMatrix (hMeas i)
    · intro i
      exact randomSelfAdjointMatrix_rankOneRandomMatrix (P := P) (X := X i)
  have hInt :
      forall i, IntegrableRandomMatrix P (rankOneRandomMatrixFamily X i) := by
    intro i
    exact integrableRandomMatrix_rankOneRandomMatrix_of_memLp_two
      (P := P) (X := X i) (hLp i)
  simpa [centeredRankOneRandomMatrixFamily] using
    centeredSelfAdjointRandomMatrixFamily_centeredRandomMatrixFamily
      (P := P) (A := rankOneRandomMatrixFamily X) hFamily hInt

/-- Compatibility predicate from the MC1 statement layer: centeredness is
entrywise centeredness rather than the bundled matrix-expectation equality. -/
def CenteredRandomSelfAdjointMatrices {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) : Prop :=
  (forall i, IsRandomMatrix P (A i)) /\
    (forall i, RandomSelfAdjointMatrix P (A i)) /\
      (forall i, CenteredEntries P (A i))

/-! ## Operator-norm boundedness assumptions and adapters -/

/-- Pointwise operator-norm bound for one random matrix. -/
def BoundedOperatorNorm {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) (R : Real) : Prop :=
  forall omega, operatorNorm A omega <= R

/--
A pointwise operator-norm bound controls the operator norm of the entrywise
matrix expectation.

The proof uses `matrixExpect_eq_integral` to bridge the entrywise expectation
to Mathlib's Bochner integral, then applies Mathlib's norm-of-integral bound.
The measurability hypothesis is kept in the signature for downstream API
compatibility, but the contraction step itself uses entrywise integrability and
the pointwise operator-norm bound.
-/
theorem deterministicOperatorNorm_matrixExpect_le_of_boundedOperatorNorm
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat} {X : RandomMatrix Omega m n}
    {R : Real}
    (_hMeas : IsRandomMatrix P X)
    (hInt : IntegrableRandomMatrix P X)
    (hBound : BoundedOperatorNorm X R)
    (_hR : 0 <= R) :
    deterministicOperatorNorm (matrixExpect P X) <= R := by
  have hBridge : matrixExpect P X = ∫ omega, X omega ∂P :=
    matrixExpect_eq_integral (P := P) (A := X) hInt
  calc
    deterministicOperatorNorm (matrixExpect P X)
        = ‖matrixExpect P X‖ := rfl
    _ = ‖∫ omega, X omega ∂P‖ := by rw [hBridge]
    _ <= R * P.real Set.univ := by
          apply MeasureTheory.norm_integral_le_of_norm_le_const
          filter_upwards with omega
          simpa [operatorNorm] using hBound omega
    _ = R := by simp

/--
A pointwise squared-vector-norm bound gives an operator-norm bound for the
named rank-one random matrix `rankOneRandomMatrix X`.

Formula reference: the deterministic ingredient is
`||v v^T||op <= ||v||_2^2` for a rank-one outer product; see
https://en.wikipedia.org/wiki/Outer_product and
https://en.wikipedia.org/wiki/Operator_norm
-/
theorem BoundedOperatorNorm_rankOneRandomMatrix_of_sqNorm_bound {Omega : Type*}
    [MeasurableSpace Omega] {n : Nat}
    (X : RandomVector Omega n) (R : Real)
    (hX : forall omega, vectorSqNorm (X omega) <= R) :
    BoundedOperatorNorm (rankOneRandomMatrix X) R := by
  intro omega
  exact (rankOneOperatorNorm_le_vectorSqNorm (X omega)).trans (hX omega)

/--
If a random matrix and its deterministic entrywise expectation have explicit
operator-norm bounds, then the centered random matrix is bounded by the sum of
those two bounds.

This is only an algebraic triangle-inequality wrapper around the existing
`matrixExpect` / `centeredRandomMatrix` vocabulary. It does not prove
entrywise integrability, measurability, or any contraction theorem bounding
`||E X||op` from the pointwise bound on `X`; the expectation norm bound is an
explicit hypothesis.

Formula reference: centering uses `X(omega) - E X`, and the proof is the
operator-norm triangle inequality `||X(omega) - E X|| <= ||X(omega)|| +
||E X||`; see https://en.wikipedia.org/wiki/Operator_norm and the sample
covariance/expectation background at
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
theorem BoundedOperatorNorm_centered_of_bound_expect_bound {Omega : Type*}
    [MeasurableSpace Omega] {m n : Nat}
    (P : Measure Omega) (X : RandomMatrix Omega m n) (R Rexp : Real)
    (hX : BoundedOperatorNorm X R)
    (hExp : deterministicOperatorNorm (matrixExpect P X) <= Rexp) :
    BoundedOperatorNorm (centeredRandomMatrix P X) (R + Rexp) := by
  intro omega
  have hTri :
      deterministicOperatorNorm (X omega - matrixExpect P X) <=
        deterministicOperatorNorm (X omega) +
          deterministicOperatorNorm (matrixExpect P X) :=
    deterministicOperatorNorm_sub_le_add (X omega) (matrixExpect P X)
  have hBound :
      deterministicOperatorNorm (X omega) +
          deterministicOperatorNorm (matrixExpect P X) <= R + Rexp :=
    add_le_add (hX omega) hExp
  exact hTri.trans hBound

/-- Pointwise uniform operator-norm bound for a matrix family. -/
def PointwiseOperatorNormBound {Omega : Type*}
    {I : Type*} {m n : Nat} (A : I -> RandomMatrix Omega m n)
    (R : Real) : Prop :=
  forall i, BoundedOperatorNorm (A i) R

/-- A pointwise operator-norm bound controls the variance-proxy norm by the
crude bound `cardinality * R^2`, provided the squared summands are entrywise
integrable. -/
theorem MatrixVarianceProxyNormBound_of_pointwiseOperatorNormBound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    {A : I -> RandomMatrix Omega n n} {R : Real}
    (hInt : forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i)))
    (hBound : PointwiseOperatorNormBound A R)
    (hR : 0 <= R) :
    MatrixVarianceProxyNormBound P A
      (pointwiseOperatorNormVarianceProxyNormRHS (I := I) R) := by
  dsimp [MatrixVarianceProxyNormBound]
  exact matrixVarianceProxyNorm_le_pointwiseOperatorNormVarianceProxyNormRHS
    (P := P) (A := A) (R := R) hInt
    (fun i omega => by
      simpa [operatorNorm, deterministicOperatorNorm] using hBound i omega)
    hR

/--
Family wrapper for expectation operator-norm contraction under a pointwise
operator-norm bound.
-/
theorem expectationOperatorNormBound_of_pointwiseOperatorNormBound {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {I : Type*} {m n : Nat} {X : I -> RandomMatrix Omega m n} {R : Real}
    (hMeas : forall i, IsRandomMatrix P (X i))
    (hInt : forall i, IntegrableRandomMatrix P (X i))
    (hBound : PointwiseOperatorNormBound X R)
    (hR : 0 <= R) :
    forall i, deterministicOperatorNorm (matrixExpect P (X i)) <= R := by
  intro i
  exact deterministicOperatorNorm_matrixExpect_le_of_boundedOperatorNorm
    (P := P) (X := X i) (R := R) (hMeas i) (hInt i) (hBound i) hR

/--
Family version of the named rank-one operator-norm bridge: if every vector
sample has `vectorSqNorm <= R`, then the associated rank-one matrix family is
pointwise operator-norm bounded by `R`.

Formula reference: this packages the outer-product bound
`||v v^T||op <= ||v||_2^2`; see
https://en.wikipedia.org/wiki/Outer_product and
https://en.wikipedia.org/wiki/Operator_norm
-/
theorem PointwiseOperatorNormBound_rankOneRandomMatrix_of_sqNorm_bound {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} {n : Nat}
    (X : I -> RandomVector Omega n) (R : Real)
    (hX : forall i omega, vectorSqNorm (X i omega) <= R) :
    PointwiseOperatorNormBound (rankOneRandomMatrixFamily X) R := by
  intro i
  exact BoundedOperatorNorm_rankOneRandomMatrix_of_sqNorm_bound (X i) R (hX i)

/--
Family version of the centered operator-norm bridge under an explicit bound on
each deterministic expectation.

This is the family form of the algebraic wrapper above. It intentionally keeps
the expectation operator-norm bound as a hypothesis and does not establish
integrability or expectation contraction.

Formula reference: this packages the triangle-bound route
`||X_i(omega) - E X_i|| <= ||X_i(omega)|| + ||E X_i||`; see
https://en.wikipedia.org/wiki/Operator_norm and
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
theorem PointwiseOperatorNormBound_centered_of_bound_expect_bound {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} {m n : Nat}
    (P : Measure Omega) (X : I -> RandomMatrix Omega m n) (R Rexp : Real)
    (hX : PointwiseOperatorNormBound X R)
    (hExp : forall i, deterministicOperatorNorm (matrixExpect P (X i)) <= Rexp) :
    PointwiseOperatorNormBound (centeredRandomMatrixFamily P X) (R + Rexp) := by
  intro i
  exact BoundedOperatorNorm_centered_of_bound_expect_bound P (X i) R Rexp
    (hX i) (hExp i)

/--
Same-radius centered operator-norm wrapper: if both `X_i(omega)` and
`E X_i` are bounded by `R`, then the centered family is bounded by `R + R`.

This remains an explicit-bound wrapper; the hypothesis on `E X_i` is not
derived from the pointwise bound on `X_i`.

Formula reference: this is the special case `R_exp = R` of the operator-norm
triangle inequality; see https://en.wikipedia.org/wiki/Operator_norm
-/
theorem PointwiseOperatorNormBound_centered_of_bound_expect_bound_same {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} {m n : Nat}
    (P : Measure Omega) (X : I -> RandomMatrix Omega m n) (R : Real)
    (hX : PointwiseOperatorNormBound X R)
    (hExp : forall i, deterministicOperatorNorm (matrixExpect P (X i)) <= R) :
    PointwiseOperatorNormBound (centeredRandomMatrixFamily P X) (R + R) := by
  exact PointwiseOperatorNormBound_centered_of_bound_expect_bound P X R R hX hExp

/--
If a random matrix is pointwise bounded by `R`, then its centered version is
pointwise bounded by `2 * R`.

This is the contraction-based centered wrapper: the expectation bound is derived
from `deterministicOperatorNorm_matrixExpect_le_of_boundedOperatorNorm`, then
the existing triangle wrapper supplies the centered bound.
-/
theorem BoundedOperatorNorm_centered_of_boundedOperatorNorm {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {m n : Nat} {X : RandomMatrix Omega m n} {R : Real}
    (hMeas : IsRandomMatrix P X)
    (hInt : IntegrableRandomMatrix P X)
    (hX : BoundedOperatorNorm X R)
    (hR : 0 <= R) :
    BoundedOperatorNorm (centeredRandomMatrix P X) (2 * R) := by
  have hCentered :
      BoundedOperatorNorm (centeredRandomMatrix P X) (R + R) :=
    BoundedOperatorNorm_centered_of_bound_expect_bound P X R R hX
      (deterministicOperatorNorm_matrixExpect_le_of_boundedOperatorNorm
        hMeas hInt hX hR)
  simpa [two_mul] using hCentered

/--
Family version of `BoundedOperatorNorm_centered_of_boundedOperatorNorm` with
the conceptual `2 * R` centered bound.
-/
theorem PointwiseOperatorNormBound_centered_of_pointwiseOperatorNormBound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} {m n : Nat}
    {X : I -> RandomMatrix Omega m n} {R : Real}
    (hMeas : forall i, IsRandomMatrix P (X i))
    (hInt : forall i, IntegrableRandomMatrix P (X i))
    (hX : PointwiseOperatorNormBound X R)
    (hR : 0 <= R) :
    PointwiseOperatorNormBound (centeredRandomMatrixFamily P X) (2 * R) := by
  intro i
  exact BoundedOperatorNorm_centered_of_boundedOperatorNorm
    (P := P) (X := X i) (R := R) (hMeas i) (hInt i) (hX i) hR

/--
Same-radius family wrapper in the existing `R + R` style.
-/
theorem PointwiseOperatorNormBound_centered_of_pointwiseOperatorNormBound_same
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} {m n : Nat}
    {X : I -> RandomMatrix Omega m n} {R : Real}
    (hMeas : forall i, IsRandomMatrix P (X i))
    (hInt : forall i, IntegrableRandomMatrix P (X i))
    (hX : PointwiseOperatorNormBound X R)
    (hR : 0 <= R) :
    PointwiseOperatorNormBound (centeredRandomMatrixFamily P X) (R + R) := by
  have hCentered :
      PointwiseOperatorNormBound (centeredRandomMatrixFamily P X) (2 * R) :=
    PointwiseOperatorNormBound_centered_of_pointwiseOperatorNormBound
      (P := P) (X := X) (R := R) hMeas hInt hX hR
  simpa [two_mul] using hCentered

/--
Centered rank-one operator-norm wrapper from a pointwise squared-vector-norm
bound.

This composes the rank-one operator-norm bridge with the contraction-based
centered operator-norm wrapper. Coordinate `MemLp ... 2` assumptions remain
explicit; this theorem does not derive integrability from boundedness.
-/
theorem BoundedOperatorNorm_centeredRankOneRandomMatrix_of_sqNorm_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {n : Nat} {X : RandomVector Omega n} {R : Real}
    (hMeas : IsRandomVector P X)
    (hLp : forall j : Fin n, MemLpRealRandomVariable P (coord X j) 2)
    (hSq : forall omega, vectorSqNorm (X omega) <= R)
    (hR : 0 <= R) :
    BoundedOperatorNorm
      (centeredRankOneRandomMatrix P X) (2 * R) := by
  exact BoundedOperatorNorm_centered_of_boundedOperatorNorm
    (P := P) (X := rankOneRandomMatrix X) (R := R)
    (isRandomMatrix_rankOneRandomMatrix hMeas)
    (integrableRandomMatrix_rankOneRandomMatrix_of_memLp_two
      (P := P) (X := X) hLp)
    (BoundedOperatorNorm_rankOneRandomMatrix_of_sqNorm_bound X R hSq)
    hR

/--
Family centered rank-one operator-norm wrapper from pointwise squared-vector
norm bounds.

This is the indexed version of the centered rank-one boundedness adapter. It
reuses the existing rank-one pointwise operator-norm bridge and the S2 centered
operator-norm family wrapper.
-/
theorem PointwiseOperatorNormBound_centeredRankOneRandomMatrix_of_sqNorm_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} {n : Nat}
    {X : I -> RandomVector Omega n} {R : Real}
    (hMeas : forall i, IsRandomVector P (X i))
    (hLp : forall i, forall j : Fin n,
      MemLpRealRandomVariable P (coord (X i) j) 2)
    (hSq : forall i omega, vectorSqNorm (X i omega) <= R)
    (hR : 0 <= R) :
    PointwiseOperatorNormBound
      (centeredRankOneRandomMatrixFamily P X) (2 * R) := by
  have hRankRandom :
      forall i, IsRandomMatrix P (rankOneRandomMatrixFamily X i) := by
    intro i
    exact isRandomMatrix_rankOneRandomMatrix (hMeas i)
  have hRankInt :
      forall i, IntegrableRandomMatrix P (rankOneRandomMatrixFamily X i) := by
    intro i
    exact integrableRandomMatrix_rankOneRandomMatrix_of_memLp_two
      (P := P) (X := X i) (hLp i)
  simpa [centeredRankOneRandomMatrixFamily] using
    PointwiseOperatorNormBound_centered_of_pointwiseOperatorNormBound
    (P := P) (X := rankOneRandomMatrixFamily X) (R := R)
    hRankRandom
    hRankInt
    (PointwiseOperatorNormBound_rankOneRandomMatrix_of_sqNorm_bound X R hSq)
    hR

/-- Crude centered rank-one variance-proxy norm RHS from a pointwise
squared-vector-norm bound. -/
abbrev centeredRankOneVarianceProxyNormRHS {I : Type*} [Fintype I]
    (R : Real) : Real :=
  pointwiseOperatorNormVarianceProxyNormRHS (I := I) (2 * R)

/-- Centered rank-one variance-proxy norm bound from a pointwise squared-vector
norm bound and explicit square-integrability of the centered summands. -/
theorem MatrixVarianceProxyNormBound_centeredRankOneRandomMatrixFamily_of_sqNorm_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    {X : I -> RandomVector Omega n} {R : Real}
    (hMeas : forall i, IsRandomVector P (X i))
    (hLp : forall i, forall j : Fin n,
      MemLpRealRandomVariable P (coord (X i) j) 2)
    (hSq : forall i omega, vectorSqNorm (X i omega) <= R)
    (hR : 0 <= R)
    (hIntSq :
      forall i,
        IntegrableRandomMatrix P
          (randomMatrixSquare ((centeredRankOneRandomMatrixFamily P X) i))) :
    MatrixVarianceProxyNormBound P
      (centeredRankOneRandomMatrixFamily P X)
      (centeredRankOneVarianceProxyNormRHS (I := I) R) := by
  have hRadius : 0 <= 2 * R := by
    nlinarith
  exact MatrixVarianceProxyNormBound_of_pointwiseOperatorNormBound
    (P := P) (A := centeredRankOneRandomMatrixFamily P X) (R := 2 * R)
    hIntSq
    (PointwiseOperatorNormBound_centeredRankOneRandomMatrix_of_sqNorm_bound
      (P := P) (X := X) hMeas hLp hSq hR)
    hRadius

/-- Centered rank-one variance-proxy norm bound from a pointwise squared-vector
norm bound, with centered square-integrability supplied by the rank-one
bounded-row provider. -/
theorem MatrixVarianceProxyNormBound_centeredRankOneRandomMatrixFamily_of_sqNorm_bound_memLp_two
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    {X : I -> RandomVector Omega n} {R : Real}
    (hMeas : forall i, IsRandomVector P (X i))
    (hLp : forall i, forall j : Fin n,
      MemLpRealRandomVariable P (coord (X i) j) 2)
    (hSq : forall i omega, vectorSqNorm (X i omega) <= R)
    (hR : 0 <= R) :
    MatrixVarianceProxyNormBound P
      (centeredRankOneRandomMatrixFamily P X)
      (centeredRankOneVarianceProxyNormRHS (I := I) R) := by
  exact MatrixVarianceProxyNormBound_centeredRankOneRandomMatrixFamily_of_sqNorm_bound
    (P := P) (X := X) (R := R)
    hMeas hLp hSq hR
    (integrableRandomMatrix_square_centeredRankOneFamily_of_sqNorm_bound_memLpTwo
      (P := P) (X := X) (R := R) hLp hSq)

/-- Alias emphasizing that the uniform bound is pointwise, not a.e. -/
abbrev UniformOperatorNormBound {Omega : Type*}
    {I : Type*} {m n : Nat} (A : I -> RandomMatrix Omega m n)
    (R : Real) : Prop :=
  PointwiseOperatorNormBound A R

/-- A.e. operator-norm bound for a matrix family. This is recorded separately
from the pointwise predicate so theorem statements do not hide the distinction. -/
def AeOperatorNormBound {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} {m n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega m n) (R : Real) : Prop :=
  forall i, ∀ᵐ omega ∂P, operatorNorm (A i) omega <= R

end HighDimProb
