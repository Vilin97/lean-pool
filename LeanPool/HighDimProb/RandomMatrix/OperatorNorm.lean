/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import LeanPool.HighDimProb.RandomMatrix.Action
import LeanPool.HighDimProb.RandomMatrix.UnitSphere

/-!
# Operator norm vocabulary for random matrices

This module uses Mathlib's `Matrix.Norms.L2Operator` scoped norm, i.e. the norm transported from
continuous linear maps between finite-dimensional Euclidean spaces. It is kept in its own
experimental submodule so the rest of the random-matrix layer does not accidentally depend on a
matrix norm convention.

Verified Wikipedia references:
* Operator norm: https://en.wikipedia.org/wiki/Operator_norm
* Matrix norm: https://en.wikipedia.org/wiki/Matrix_norm
* Unit sphere: https://en.wikipedia.org/wiki/Unit_sphere
-/

namespace HighDimProb

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The scoped L2 operator-norm topology on finite real matrices has open sets
measurable for the existing product measurable-space convention.

Formula reference: the operator norm is a matrix norm induced by vector norms;
for finite real matrices this is the L2-induced norm
`||A|| = sup_{||x||_2 = 1} ||A x||_2`.  This instance supports its measurable
random-matrix use. See
https://en.wikipedia.org/wiki/Operator_norm
-/
instance instOpensMeasurableSpaceMatrixL2Operator {m n : Nat} :
    OpensMeasurableSpace (Matrix (Fin m) (Fin n) Real) := by
  change OpensMeasurableSpace (Fin m -> Fin n -> Real)
  infer_instance

/--
Spectral/operator norm random variable for a real random matrix.

Formula reference: for each sample `omega`, this is the induced L2 operator
norm `||A(omega)|| = sup_{||x||_2 = 1} ||A(omega) x||_2`; see
https://en.wikipedia.org/wiki/Operator_norm
-/
def operatorNorm {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) : RealRandomVariable Omega :=
  fun omega => ‖A omega‖

/--
Formula reference: this unfolds `operatorNorm A omega` to the scoped matrix
norm `||A omega||`, whose intended formula is
`sup_{||x||_2 = 1} ||A(omega) x||_2`; see
https://en.wikipedia.org/wiki/Operator_norm
-/
@[simp]
theorem operatorNorm_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (omega : Omega) :
    operatorNorm A omega = ‖A omega‖ :=
  rfl

/--
Deterministic version of the scoped L2 matrix operator norm.

Formula reference: deterministic version of
`||A|| = sup_{||x||_2 = 1} ||A x||_2` for a finite matrix; see
https://en.wikipedia.org/wiki/Operator_norm
-/
def deterministicOperatorNorm {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) : Real :=
  norm A

/--
Formula reference: this unfolds `deterministicOperatorNorm A` to the scoped
matrix norm `||A||`, the induced L2 operator norm; see
https://en.wikipedia.org/wiki/Operator_norm
-/
@[simp]
theorem deterministicOperatorNorm_apply {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) :
    deterministicOperatorNorm A = norm A :=
  rfl

/--
The deterministic operator norm satisfies the triangle inequality for
subtraction.

Formula reference: this is the norm triangle inequality
`||A - B|| <= ||A|| + ||B||` for the matrix norm induced by the Euclidean
operator norm; see https://en.wikipedia.org/wiki/Operator_norm and
https://en.wikipedia.org/wiki/Matrix_norm
-/
theorem deterministicOperatorNorm_sub_le_add {m n : Nat}
    (A B : Matrix (Fin m) (Fin n) Real) :
    deterministicOperatorNorm (A - B) <=
      deterministicOperatorNorm A + deterministicOperatorNorm B := by
  simpa [deterministicOperatorNorm] using norm_sub_le A B

/--
Rank-one self-outer products have operator norm bounded by the squared
Euclidean norm of the vector.

Formula reference: for the outer product `v vᵀ`, multiplication sends
`x` to `<v, x> v`; Cauchy--Schwarz gives
`||<v, x> v||₂ <= ||v||₂^2 ||x||₂`, hence the induced operator-norm bound.
See https://en.wikipedia.org/wiki/Outer_product and
https://en.wikipedia.org/wiki/Operator_norm
-/
theorem rankOneOperatorNorm_le_vectorSqNorm {n : Nat}
    (v : Fin n -> Real) :
    deterministicOperatorNorm (rankOneMatrix v) <= vectorSqNorm v := by
  rw [deterministicOperatorNorm, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (vectorSqNorm_nonneg v) ?_
  intro y
  have happly :
      (((Matrix.toEuclideanLin (𝕜 := Real) (m := Fin n) (n := Fin n)).trans
            LinearMap.toContinuousLinearMap)
          (rankOneMatrix v) y) =
        (inner Real (WithLp.toLp 2 v : EuclideanSpace Real (Fin n)) y) •
          (WithLp.toLp 2 v : EuclideanSpace Real (Fin n)) := by
    ext i
    simp only [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap',
      Matrix.ofLp_toLpLin, Matrix.toLin'_apply, PiLp.smul_apply,
      Matrix.mulVec, dotProduct, inner, rankOneMatrix_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [RCLike.re_to_real, TrivialStar.star_trivial]
    ring
  rw [happly]
  calc
    ‖(inner Real (WithLp.toLp 2 v : EuclideanSpace Real (Fin n)) y) •
          (WithLp.toLp 2 v : EuclideanSpace Real (Fin n))‖
        = |inner Real (WithLp.toLp 2 v : EuclideanSpace Real (Fin n)) y| *
            ‖(WithLp.toLp 2 v : EuclideanSpace Real (Fin n))‖ := by
          rw [norm_smul, Real.norm_eq_abs]
    _ <= ‖(WithLp.toLp 2 v : EuclideanSpace Real (Fin n))‖ * ‖y‖ *
            ‖(WithLp.toLp 2 v : EuclideanSpace Real (Fin n))‖ := by
          exact mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (norm_nonneg _)
    _ = vectorSqNorm v * ‖y‖ := by
          rw [vectorSqNorm_eq_norm_sq_toLp]
          ring

/--
Squared Euclidean norm of the deterministic matrix-vector product.

Formula reference: this is the squared vector norm
`||A x||_2^2 = sum_i (sum_j A_ij * x_j)^2`, the numerator appearing inside the
operator-norm supremum; see https://en.wikipedia.org/wiki/Operator_norm
-/
def matVecSqNorm {m n : Nat} (A : Matrix (Fin m) (Fin n) Real)
    (x : Fin n -> Real) : Real :=
  vectorSqNorm (fun i : Fin m => Finset.univ.sum fun j : Fin n => A i j * x j)

/--
Formula reference: this unfolds
`matVecSqNorm A x = sum_i (sum_j A_ij * x_j)^2`, i.e. `||A x||_2^2`; see
https://en.wikipedia.org/wiki/Operator_norm
-/
@[simp]
theorem matVecSqNorm_apply {m n : Nat} (A : Matrix (Fin m) (Fin n) Real)
    (x : Fin n -> Real) :
    matVecSqNorm A x =
      Finset.univ.sum fun i : Fin m =>
        (Finset.univ.sum fun j : Fin n => A i j * x j) ^ 2 :=
  rfl

/--
Formula reference: the squared matrix-vector norm is nonnegative because it is
a sum of squares; see https://en.wikipedia.org/wiki/Operator_norm
-/
theorem matVecSqNorm_nonneg {m n : Nat} (A : Matrix (Fin m) (Fin n) Real)
    (x : Fin n -> Real) :
    0 <= matVecSqNorm A x :=
  vectorSqNorm_nonneg _

/-- Explicit matrix-vector squared norm agrees with Mathlib's L2 norm after
viewing the output vector as Euclidean space.

Formula reference: this proves the finite-sum expression
`sum_i (sum_j A_ij * x_j)^2` equals Mathlib's Euclidean `||A x||_2^2`; see
https://en.wikipedia.org/wiki/Operator_norm
-/
theorem matVecSqNorm_eq_norm_sq_toLp_mulVec {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (x : Fin n -> Real) :
    matVecSqNorm A x =
      norm ((EuclideanSpace.equiv (Fin m) Real).symm (Matrix.mulVec A x) :
        EuclideanSpace Real (Fin m)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [matVecSqNorm, vectorSqNorm, Matrix.mulVec, dotProduct]

/--
Formula reference: reverse direction of the identity
`||A x||_2^2 = sum_i (sum_j A_ij * x_j)^2`; see
https://en.wikipedia.org/wiki/Operator_norm
-/
theorem norm_sq_toLp_mulVec_eq_matVecSqNorm {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (x : Fin n -> Real) :
    norm ((EuclideanSpace.equiv (Fin m) Real).symm (Matrix.mulVec A x) :
      EuclideanSpace Real (Fin m)) ^ 2 = matVecSqNorm A x :=
  (matVecSqNorm_eq_norm_sq_toLp_mulVec A x).symm

/--
Random-variable version of deterministic matrix-vector squared norm.

Formula reference: for fixed `x`, this random variable is
`omega |-> ||A(omega) x||_2^2`, the pointwise squared image norm used in
operator-norm bounds; see
https://en.wikipedia.org/wiki/Operator_norm
-/
def randomMatVecSqNorm {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) (x : Fin n -> Real) : RealRandomVariable Omega :=
  fun omega => matVecSqNorm (A omega) x

/--
Formula reference: this unfolds
`randomMatVecSqNorm A x omega = ||A(omega) x||_2^2` in the explicit
finite-sum convention; see https://en.wikipedia.org/wiki/Operator_norm
-/
@[simp]
theorem randomMatVecSqNorm_apply {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : RandomMatrix Omega m n) (x : Fin n -> Real)
    (omega : Omega) :
    randomMatVecSqNorm A x omega = matVecSqNorm (A omega) x :=
  rfl

/-- The explicit random-vector squared norm of `matVec` is the deterministic
matrix-vector squared norm at each sample.

Formula reference: this identifies `sqNorm (matVec A x) omega` with the same
quantity `||A(omega) x||_2^2`; see
https://en.wikipedia.org/wiki/Operator_norm
-/
theorem sqNorm_matVec_eq_matVecSqNorm {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : RandomMatrix Omega m n) (x : Fin n -> Real)
    (omega : Omega) :
    sqNorm (matVec A x) omega = matVecSqNorm (A omega) x :=
  rfl

/--
Formula reference: measurability of `omega |-> ||A(omega) x||_2^2` is needed
before taking probabilities or expectations of operator-norm ingredients; see
https://en.wikipedia.org/wiki/Operator_norm
-/
theorem isRealRandomVariable_randomMatVecSqNorm {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IsRandomMatrix P A) (x : Fin n -> Real) :
    IsRealRandomVariable P (randomMatVecSqNorm A x) := by
  change IsRealRandomVariable P (sqNorm (matVec A x))
  exact isRealRandomVariable_sqNorm (isRandomVector_matVec hA x)

/-- Explicit squared operator-norm upper-bound predicate, avoiding the exact
Mathlib operator-norm bridge.

Formula reference: the operator norm is the supremum over unit vectors, so an
upper bound can be stated by requiring
`0 <= L` and `forall x, ||x||_2 = 1 -> ||A x||_2^2 <= L^2`; see
https://en.wikipedia.org/wiki/Operator_norm and
https://en.wikipedia.org/wiki/Unit_sphere
-/
def OperatorNormBoundSq {m n : Nat} (A : Matrix (Fin m) (Fin n) Real)
    (L : Real) : Prop :=
  0 <= L /\ forall x : Fin n -> Real, IsUnitVector x -> matVecSqNorm A x <= L ^ 2

/--
Pointwise explicit squared operator-norm upper-bound predicate for random matrices.

Formula reference: pointwise random version of
`forall x, ||x||_2 = 1 -> ||A(omega) x||_2^2 <= L^2`; see
https://en.wikipedia.org/wiki/Operator_norm
-/
def RandomOperatorNormBoundSq {Omega : Type*}
    {m n : Nat} (A : RandomMatrix Omega m n) (L : Real) : Prop :=
  forall omega, OperatorNormBoundSq (A omega) L

/--
Formula reference: the explicit upper-bound predicate carries the required
nonnegative bound `L`; see https://en.wikipedia.org/wiki/Operator_norm
-/
theorem operatorNormBoundSq_nonneg {m n : Nat}
    {A : Matrix (Fin m) (Fin n) Real} {L : Real}
    (hA : OperatorNormBoundSq A L) :
    0 <= L :=
  hA.1

/--
Formula reference: this extracts the bound
`||A x||_2^2 <= L^2` under the unit-vector assumption `||x||_2 = 1`; see
https://en.wikipedia.org/wiki/Operator_norm
-/
theorem matVecSqNorm_le_of_operatorNormBoundSq {m n : Nat}
    {A : Matrix (Fin m) (Fin n) Real} {L : Real}
    (hA : OperatorNormBoundSq A L) {x : Fin n -> Real}
    (hx : IsUnitVector x) :
    matVecSqNorm A x <= L ^ 2 :=
  hA.2 x hx

/-- Mathlib's scoped L2 matrix operator-norm bound implies the explicit
squared unit-vector bound predicate.

Formula reference: from `||A|| <= L`, the induced norm definition gives
`||A x||_2 <= L` for every `||x||_2 = 1`, hence the squared bound; see
https://en.wikipedia.org/wiki/Operator_norm
-/
theorem operatorNormBoundSq_of_operatorNorm_le {m n : Nat}
    {A : Matrix (Fin m) (Fin n) Real} {L : Real}
    (hL_nonneg : 0 <= L) (hA : deterministicOperatorNorm A <= L) :
    OperatorNormBoundSq A L := by
  refine ⟨hL_nonneg, ?_⟩
  intro x hx
  have hxnorm :
      norm (WithLp.toLp 2 x : EuclideanSpace Real (Fin n)) = 1 :=
    norm_toLp_eq_one_of_isUnitVector hx
  have hmul :=
    Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x : EuclideanSpace Real (Fin n))
  have hnorm :
      norm ((EuclideanSpace.equiv (Fin m) Real).symm (Matrix.mulVec A x) :
        EuclideanSpace Real (Fin m)) <= L := by
    have hnormA : norm A <= L := by
      simpa [deterministicOperatorNorm] using hA
    have hmul' :
        norm ((EuclideanSpace.equiv (Fin m) Real).symm (Matrix.mulVec A x) :
          EuclideanSpace Real (Fin m)) <= norm A := by
      simpa [hxnorm] using hmul
    exact hmul'.trans hnormA
  rw [matVecSqNorm_eq_norm_sq_toLp_mulVec]
  have hnonneg :
      0 <= norm ((EuclideanSpace.equiv (Fin m) Real).symm (Matrix.mulVec A x) :
        EuclideanSpace Real (Fin m)) :=
    norm_nonneg _
  nlinarith

/-- The explicit squared unit-vector bound predicate controls Mathlib's scoped
L2 matrix operator norm.

Formula reference: if `||A x||_2^2 <= L^2` for every `||x||_2 = 1`, then the
unit-sphere supremum formula gives `||A|| <= L`; see
https://en.wikipedia.org/wiki/Operator_norm
-/
theorem operatorNorm_le_of_operatorNormBoundSq {m n : Nat}
    {A : Matrix (Fin m) (Fin n) Real} {L : Real}
    (hA : OperatorNormBoundSq A L) :
    deterministicOperatorNorm A <= L := by
  rw [deterministicOperatorNorm, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hA.1 fun x hx => ?_
  have hxUnit : IsUnitVector (WithLp.ofLp x) := by
    apply isUnitVector_of_norm_toLp_eq_one
    simpa using hx
  have hsq :
      norm ((EuclideanSpace.equiv (Fin m) Real).symm
          (Matrix.mulVec A (WithLp.ofLp x)) : EuclideanSpace Real (Fin m)) ^ 2 <=
        L ^ 2 := by
    rw [norm_sq_toLp_mulVec_eq_matVecSqNorm]
    exact hA.2 _ hxUnit
  have htarget :
      norm (((Matrix.toEuclideanLin (𝕜 := Real) (m := Fin m) (n := Fin n)).trans
          LinearMap.toContinuousLinearMap) A x) ^ 2 <= L ^ 2 := by
    simpa [Matrix.toLpLin_apply] using hsq
  exact le_of_sq_le_sq htarget hA.1

/-- Entrywise random-matrix measurability makes the scoped L2 operator norm a
real random variable.

Formula reference: this states measurability of
`omega |-> ||A(omega)||`, where `||A(omega)||` is the induced operator norm;
see https://en.wikipedia.org/wiki/Operator_norm
-/
theorem isRealRandomVariable_operatorNorm {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IsRandomMatrix P A) :
    IsRealRandomVariable P (operatorNorm A) := by
  dsimp [IsRealRandomVariable, IsRandomVariable, operatorNorm]
  exact measurable_norm.comp (measurable_randomMatrix_of_isRandomMatrix hA)

/-- Typed target for the future exact bridge from explicit squared bounds to
Mathlib's scoped L2 operator norm.

Formula reference: target statement for proving
`(forall ||x||_2 = 1, ||A x||_2^2 <= L^2) -> ||A|| <= L`; see
https://en.wikipedia.org/wiki/Operator_norm
-/
def operatorNormLeOfOperatorNormBoundSqStatement {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (L : Real) : Prop :=
  OperatorNormBoundSq A L -> deterministicOperatorNorm A <= L

/-- Typed target for the future reverse bridge from Mathlib's scoped L2 operator
norm to explicit squared unit-vector bounds.

Formula reference: target statement for proving
`||A|| <= L -> forall ||x||_2 = 1, ||A x||_2^2 <= L^2`; see
https://en.wikipedia.org/wiki/Operator_norm
-/
def operatorNormBoundSqOfOperatorNormLeStatement {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (L : Real) : Prop :=
  0 <= L -> deterministicOperatorNorm A <= L -> OperatorNormBoundSq A L

/-- Typed target for the future measurability bridge for Mathlib's scoped L2
operator norm.

Formula reference: target measurability statement for
`omega |-> sup_{||x||_2 = 1} ||A(omega) x||_2`; see
https://en.wikipedia.org/wiki/Operator_norm
-/
def operatorNormMeasurabilityStatement {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (P : Measure Omega) (A : RandomMatrix Omega m n) : Prop :=
  IsRandomMatrix P A -> IsRealRandomVariable P (operatorNorm A)

end

end HighDimProb
