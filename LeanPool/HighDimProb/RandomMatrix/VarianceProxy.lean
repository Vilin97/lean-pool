/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.Expectation
import LeanPool.HighDimProb.RandomMatrix.MatrixOrder
import LeanPool.HighDimProb.RandomMatrix.OperatorNorm
import LeanPool.HighDimProb.RandomMatrix.Sums

/-!
# Matrix variance proxy vocabulary

Verified Wikipedia references:
* Variance: https://en.wikipedia.org/wiki/Variance
* Random matrix: https://en.wikipedia.org/wiki/Random_matrix
* Matrix multiplication: https://en.wikipedia.org/wiki/Matrix_multiplication
* Operator norm: https://en.wikipedia.org/wiki/Operator_norm

Note: Wikipedia does not provide a dedicated `variance proxy` page; this file
uses the standard matrix-concentration proxy `sum_i E[A_i^2]`.

This leaf prepares the deterministic variance-proxy objects used by future
matrix Bernstein statements. Expectations remain entrywise through
`matrixExpect`, matching the current random-matrix object layer.
-/

namespace HighDimProb

open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

/-- Square of a deterministic square matrix. -/
def matrixSquare {n : Nat} (A : Matrix (Fin n) (Fin n) Real) :
    Matrix (Fin n) (Fin n) Real :=
  A * A

@[simp]
theorem matrixSquare_apply {n : Nat} (A : Matrix (Fin n) (Fin n) Real)
    (i j : Fin n) :
    matrixSquare A i j = Finset.univ.sum fun k : Fin n => A i k * A k j := by
  simp [matrixSquare, Matrix.mul_apply]

/-- Matrix squaring is invariant under pointwise negation. -/
@[simp]
theorem matrixSquare_neg {n : Nat} (A : Matrix (Fin n) (Fin n) Real) :
    matrixSquare (-A) = matrixSquare A := by
  ext i j
  simp [matrixSquare, Matrix.mul_apply]

/-- Pointwise square of a square random matrix. -/
def randomMatrixSquare {Omega : Type*} {n : Nat}
    (A : RandomMatrix Omega n n) : RandomMatrix Omega n n :=
  fun omega => matrixSquare (A omega)

@[simp]
theorem randomMatrixSquare_apply {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} (A : RandomMatrix Omega n n) (omega : Omega) :
    randomMatrixSquare A omega = matrixSquare (A omega) :=
  rfl

/-- Pointwise random-matrix squaring is invariant under pointwise negation. -/
@[simp]
theorem randomMatrixSquare_neg {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} (A : RandomMatrix Omega n n) :
    randomMatrixSquare (negRandomMatrix A) = randomMatrixSquare A := by
  funext omega
  simp [randomMatrixSquare, negRandomMatrix]

/-- Entrywise measurability of the pointwise matrix square. -/
theorem isRandomMatrix_matrixSquare {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} {A : RandomMatrix Omega n n}
    (hA : IsRandomMatrix P A) :
    IsRandomMatrix P (randomMatrixSquare A) := by
  intro i j
  dsimp [IsRealRandomVariable, IsRandomVariable, matrixEntry, randomMatrixSquare]
  change Measurable (fun omega => ∑ k, A omega i k * A omega k j)
  exact
    Finset.measurable_sum Finset.univ fun k _ => (hA i k).mul (hA k j)

/-- Rank-one square integrability from explicit four-coordinate product
integrability.

For `rankOneRandomMatrix X`, each entry of the pointwise square is a finite sum
of terms `(X_i * X_k) * (X_k * X_j)`. This provider deliberately keeps those
four-coordinate product integrability assumptions explicit; it does not prove a
general fourth-moment or `MemLp 4` theorem. -/
theorem integrableRandomMatrix_randomMatrixSquare_rankOneRandomMatrix_of_integrable_four_products
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    {X : RandomVector Omega n}
    (hProd4 : forall i k j : Fin n,
      IntegrableRealRandomVariable P
        (fun omega => (X omega i * X omega k) * (X omega k * X omega j))) :
    IntegrableRandomMatrix P (randomMatrixSquare (rankOneRandomMatrix X)) := by
  intro i j
  change IntegrableRealRandomVariable P
    (fun omega =>
      Finset.univ.sum fun k : Fin n =>
        (X omega i * X omega k) * (X omega k * X omega j))
  exact integrable_finsetSum Finset.univ fun k _ => hProd4 i k j

/-- Rank-one square integrability from coordinate `L^4` assumptions.

The proof factors each four-coordinate product as a product of two `L^2`
pair-products, using Mathlib's `MemLp.mul` / `MemLp.integrable_mul` Hölder API,
and then reuses
`integrableRandomMatrix_randomMatrixSquare_rankOneRandomMatrix_of_integrable_four_products`.
This theorem is only a square-integrability provider; it does not prove a
variance-proxy norm bound or a sample-covariance tail theorem. -/
theorem integrableRandomMatrix_randomMatrixSquare_rankOneRandomMatrix_of_memLp_four
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    {X : RandomVector Omega n}
    (hX : forall j : Fin n,
      MemLpRealRandomVariable P (coord X j) (4 : ENNReal)) :
    IntegrableRandomMatrix P (randomMatrixSquare (rankOneRandomMatrix X)) := by
  haveI : ENNReal.HolderTriple (4 : ENNReal) (4 : ENNReal) (2 : ENNReal) := by
    have hReal : Real.HolderTriple (4 : Real) (4 : Real) (2 : Real) := by
      refine ⟨?_, by norm_num, by norm_num⟩
      norm_num
    simpa using Real.HolderTriple.ennrealOfReal hReal
  apply integrableRandomMatrix_randomMatrixSquare_rankOneRandomMatrix_of_integrable_four_products
  intro i k j
  have hik : MemLp (fun omega => X omega i * X omega k) (2 : ENNReal) P := by
    change MemLp (fun omega => coord X i omega * coord X k omega) (2 : ENNReal) P
    exact (hX k).mul (hX i)
  have hkj : MemLp (fun omega => X omega k * X omega j) (2 : ENNReal) P := by
    change MemLp (fun omega => coord X k omega * coord X j omega) (2 : ENNReal) P
    exact (hX j).mul (hX k)
  exact hik.integrable_mul hkj

/-- Rank-one square integrability from coordinate `L^2` assumptions and a
pointwise squared-vector-norm bound.

This is a square-integrability provider, not a variance-proxy norm bound.  It
uses the existing four-products provider: the middle coordinate square is a
bounded multiplier because `X_k^2 <= vectorSqNorm X <= R`, while the remaining
rank-one entry `X_i * X_j` is integrable by the `MemLp 2` rank-one API. -/
theorem integrableRandomMatrix_randomMatrixSquare_rankOneRandomMatrix_of_sqNorm_bound_memLp_two
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    {X : RandomVector Omega n} {R : Real}
    (hLp : forall j : Fin n,
      MemLpRealRandomVariable P (coord X j) (2 : ENNReal))
    (hSq : forall omega, vectorSqNorm (X omega) <= R) :
    IntegrableRandomMatrix P (randomMatrixSquare (rankOneRandomMatrix X)) := by
  apply integrableRandomMatrix_randomMatrixSquare_rankOneRandomMatrix_of_integrable_four_products
  intro i k j
  have hij : IntegrableRealRandomVariable P (fun omega => X omega i * X omega j) := by
    change Integrable ((coord X i) * (coord X j)) P
    exact (hLp i).integrable_mul (hLp j)
  have hk_aesm :
      AEStronglyMeasurable (fun omega => X omega k * X omega k) P := by
    exact ((hLp k).aestronglyMeasurable.mul (hLp k).aestronglyMeasurable)
  have hk_bound :
      ∀ᵐ omega ∂P, ‖X omega k * X omega k‖ <= R := by
    filter_upwards with omega
    have hk_sq : X omega k ^ 2 <= vectorSqNorm (X omega) :=
      coordinate_sq_le_vectorSqNorm (X omega) k
    have hk_nonneg : 0 <= X omega k * X omega k := mul_self_nonneg (X omega k)
    have hk_eq : ‖X omega k * X omega k‖ = X omega k * X omega k := by
      exact Real.norm_of_nonneg hk_nonneg
    rw [hk_eq]
    have : X omega k * X omega k <= R := by
      nlinarith [hk_sq, hSq omega]
    exact this
  have hprod :
      Integrable (fun omega => (X omega k * X omega k) * (X omega i * X omega j)) P :=
    hij.bdd_mul hk_aesm hk_bound
  convert hprod using 1
  ext omega
  ring


/-- Entrywise second-moment matrix `E[A^2]` for a square random matrix. -/
def matrixSecondMoment {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (P : Measure Omega) (A : RandomMatrix Omega n n) :
    Matrix (Fin n) (Fin n) Real :=
  matrixExpect P (randomMatrixSquare A)

@[simp]
theorem matrixSecondMoment_apply {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} (P : Measure Omega) (A : RandomMatrix Omega n n)
    (i j : Fin n) :
    matrixSecondMoment P A i j =
      expect P (matrixEntry (randomMatrixSquare A) i j) :=
  rfl

/-- Matrix variance proxy candidate `sum_i E[A_i^2]`. -/
def matrixVarianceProxy {Omega : Type*} [MeasurableSpace Omega] {I : Type*}
    [Fintype I] {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) : Matrix (Fin n) (Fin n) Real :=
  Finset.univ.sum fun i : I => matrixSecondMoment P (A i)

@[simp]
theorem matrixVarianceProxy_apply {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} [Fintype I] {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) (r c : Fin n) :
    matrixVarianceProxy P A r c =
      Finset.univ.sum fun i : I => matrixSecondMoment P (A i) r c := by
  simpa [matrixVarianceProxy] using
    Matrix.sum_apply r c Finset.univ (fun i : I => matrixSecondMoment P (A i))

/-- Compatibility alias for the MC1 capitalized variance-proxy name. -/
abbrev MatrixVarianceProxy {Omega : Type*} [MeasurableSpace Omega] {I : Type*}
    [Fintype I] {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) : Matrix (Fin n) (Fin n) Real :=
  matrixVarianceProxy P A

/-- Upper bound on a matrix variance proxy in the explicit Loewner-style order. -/
def matrixVarianceProxyBound {n : Nat} (V : Matrix (Fin n) (Fin n) Real)
    (sigma2 : Real) : Prop :=
  MatrixLE V (Matrix.scalar (Fin n) sigma2)

/-- Compatibility alias for the MC1 capitalized variance-proxy bound name. -/
abbrev MatrixVarianceProxyBound {n : Nat} (V : Matrix (Fin n) (Fin n) Real)
    (sigma2 : Real) : Prop :=
  matrixVarianceProxyBound V sigma2

/-- Semantic assertion that the variance proxy of a random matrix family is
bounded above by a deterministic matrix. -/
def MatrixVarianceProxyUpperBound {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} [Fintype I] {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) (V : Matrix (Fin n) (Fin n) Real) :
    Prop :=
  MatrixLE (matrixVarianceProxy P A) V

/-- Deterministic operator norm of a matrix variance proxy. -/
def deterministicMatrixVarianceProxyNorm {n : Nat}
    (V : Matrix (Fin n) (Fin n) Real) : Real :=
  deterministicOperatorNorm V

@[simp]
theorem deterministicMatrixVarianceProxyNorm_apply {n : Nat}
    (V : Matrix (Fin n) (Fin n) Real) :
    deterministicMatrixVarianceProxyNorm V = deterministicOperatorNorm V :=
  rfl

/-- The deterministic variance-proxy norm of a finite sum is bounded by the sum
of the deterministic variance-proxy norms. -/
theorem deterministicMatrixVarianceProxyNorm_sum_le_sum
    {I : Type*} [Fintype I] {n : Nat}
    (V : I -> Matrix (Fin n) (Fin n) Real) :
    deterministicMatrixVarianceProxyNorm (Finset.univ.sum fun i => V i) <=
      Finset.univ.sum fun i => deterministicMatrixVarianceProxyNorm (V i) := by
  dsimp [deterministicMatrixVarianceProxyNorm, deterministicOperatorNorm]
  simpa using (norm_sum_le (s := Finset.univ) (f := fun i : I => V i))

/-- Scalar variance proxy norm `‖sum_i E[A_i^2]‖`. -/
def matrixVarianceProxyNorm {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} [Fintype I] {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) : Real :=
  deterministicMatrixVarianceProxyNorm (matrixVarianceProxy P A)

@[simp]
theorem matrixVarianceProxyNorm_apply {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} [Fintype I] {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) :
    matrixVarianceProxyNorm P A =
      deterministicOperatorNorm (matrixVarianceProxy P A) :=
  rfl

/-- Semantic scalar-norm bound for the variance proxy of a random matrix
family. This packages the scalar parameter used in Matrix Bernstein statements
without changing the underlying `matrixVarianceProxyNorm` definition. -/
def MatrixVarianceProxyNormBound {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} [Fintype I] {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) (sigma2 : Real) : Prop :=
  matrixVarianceProxyNorm P A <= sigma2

/-- Crude scalar RHS for variance-proxy norm control from a pointwise
operator-norm bound. -/
abbrev pointwiseOperatorNormVarianceProxyNormRHS {I : Type*} [Fintype I]
    (R : Real) : Real :=
  (Fintype.card I : Real) * R ^ 2

/-- Row-specific scalar RHS for variance-proxy norm control from per-index
squared-vector-norm bounds. This names the common `rowSqNormVarianceProxyNormRHS R` expression used
by exact-row sample-covariance variance-proxy routes. -/
abbrev rowSqNormVarianceProxyNormRHS {I : Type*} [Fintype I]
    (R : I -> Real) : Real :=
  Finset.univ.sum fun i : I => (R i) ^ 2

/-- The deterministic operator norm of a matrix square is bounded by the square
of the deterministic operator norm. -/
theorem deterministicOperatorNorm_matrixSquare_le_sq {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) :
    deterministicOperatorNorm (matrixSquare A) <=
      deterministicOperatorNorm A ^ 2 := by
  simpa [deterministicOperatorNorm, matrixSquare, pow_two] using norm_mul_le A A

/-- A deterministic operator-norm bound controls the operator norm of the matrix
square with the squared radius. -/
theorem deterministicOperatorNorm_matrixSquare_le_sq_of_le {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} {R : Real}
    (hA : deterministicOperatorNorm A <= R) (hR : 0 <= R) :
    deterministicOperatorNorm (matrixSquare A) <= R ^ 2 := by
  have hsq :
      deterministicOperatorNorm (matrixSquare A) <=
        deterministicOperatorNorm A ^ 2 :=
    deterministicOperatorNorm_matrixSquare_le_sq A
  have hnorm_nonneg : 0 <= deterministicOperatorNorm A := by
    exact norm_nonneg A
  have hsqR : deterministicOperatorNorm A ^ 2 <= R ^ 2 := by
    nlinarith
  exact hsq.trans hsqR

/-- A pointwise operator-norm bound on a random matrix controls the operator
norm of its matrix second moment, provided the squared random matrix is
entrywise integrable. -/
theorem deterministicOperatorNorm_matrixSecondMoment_le_sq_of_forall
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {n : Nat} {A : RandomMatrix Omega n n}
    {R : Real}
    (hInt : IntegrableRandomMatrix P (randomMatrixSquare A))
    (hBound : forall omega, deterministicOperatorNorm (A omega) <= R)
    (hR : 0 <= R) :
    deterministicOperatorNorm (matrixSecondMoment P A) <= R ^ 2 := by
  have hBridge :
      matrixSecondMoment P A =
        MeasureTheory.integral P (fun omega => randomMatrixSquare A omega) := by
    exact matrixExpect_eq_integral (P := P) (A := randomMatrixSquare A) hInt
  calc
    deterministicOperatorNorm (matrixSecondMoment P A)
        = norm (matrixSecondMoment P A) := rfl
    _ =
        norm (MeasureTheory.integral P (fun omega => randomMatrixSquare A omega)) := by
          rw [hBridge]
    _ <= R ^ 2 * P.real Set.univ := by
          apply MeasureTheory.norm_integral_le_of_norm_le_const
          filter_upwards with omega
          have hsq :
              deterministicOperatorNorm (matrixSquare (A omega)) <= R ^ 2 :=
            deterministicOperatorNorm_matrixSquare_le_sq_of_le (hBound omega) hR
          simpa [randomMatrixSquare, deterministicOperatorNorm] using hsq
    _ = R ^ 2 := by
          simp

/-- A pointwise squared-vector-norm bound controls the deterministic variance
proxy norm of the exact uncentered rank-one second moment.

This is the single-row provider for exact-row sample-covariance variance-proxy
routes. Square-integrability of the rank-one square remains explicit; this
theorem does not prove fourth-moment or product-integrability assumptions. -/
theorem deterministicVarianceProxyNorm_rankOneSecondMoment_le_sq_of_sqNorm_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {n : Nat} {X : RandomVector Omega n}
    {R : Real}
    (hInt :
      IntegrableRandomMatrix P (randomMatrixSquare (rankOneRandomMatrix X)))
    (hSq : forall omega, vectorSqNorm (X omega) <= R)
    (hR : 0 <= R) :
    deterministicMatrixVarianceProxyNorm
        (matrixSecondMoment P (rankOneRandomMatrix X)) <= R ^ 2 := by
  change deterministicOperatorNorm
      (matrixSecondMoment P (rankOneRandomMatrix X)) <= R ^ 2
  exact deterministicOperatorNorm_matrixSecondMoment_le_sq_of_forall
    (P := P) (A := rankOneRandomMatrix X) (R := R) hInt
    (fun omega => (rankOneOperatorNorm_le_vectorSqNorm (X omega)).trans (hSq omega))
    hR

/-- Row-specific exact rank-one second-moment norm control.

This combines the generic deterministic variance-proxy norm subadditivity with
the single-row rank-one second-moment provider. It is distinct from the uniform
crude bounded-row theorem: the right side is `rowSqNormVarianceProxyNormRHS R`, not
`cardinality * R^2`. -/
theorem deterministicVarianceProxyNorm_sum_rankOneSecondMoment_le_sumSq_of_sqNorm_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    {X : I -> RandomVector Omega n} {R : I -> Real}
    (hInt : forall i,
      IntegrableRandomMatrix P (randomMatrixSquare (rankOneRandomMatrix (X i))))
    (hSq : forall i omega, vectorSqNorm (X i omega) <= R i)
    (hR : forall i, 0 <= R i) :
    deterministicMatrixVarianceProxyNorm
        (Finset.univ.sum fun i : I =>
          matrixSecondMoment P (rankOneRandomMatrix (X i))) <=
      rowSqNormVarianceProxyNormRHS R := by
  calc
    deterministicMatrixVarianceProxyNorm
        (Finset.univ.sum fun i : I =>
          matrixSecondMoment P (rankOneRandomMatrix (X i)))
        <= Finset.univ.sum fun i : I =>
          deterministicMatrixVarianceProxyNorm
            (matrixSecondMoment P (rankOneRandomMatrix (X i))) := by
          exact deterministicMatrixVarianceProxyNorm_sum_le_sum
            (fun i : I => matrixSecondMoment P (rankOneRandomMatrix (X i)))
    _ <= Finset.univ.sum fun i : I => (R i) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact
            deterministicVarianceProxyNorm_rankOneSecondMoment_le_sq_of_sqNorm_bound
              (P := P) (X := X i) (R := R i) (hInt i) (hSq i) (hR i)

/-- A pointwise operator-norm bound on every summand controls the scalar norm of
the matrix variance proxy by the crude finite-family bound
`cardinality * R^2`. -/
theorem matrixVarianceProxyNorm_le_pointwiseOperatorNormVarianceProxyNormRHS
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {I : Type*} [Fintype I] {n : Nat}
    {A : I -> RandomMatrix Omega n n} {R : Real}
    (hInt : forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i)))
    (hBound : forall i omega, deterministicOperatorNorm (A i omega) <= R)
    (hR : 0 <= R) :
    matrixVarianceProxyNorm P A <=
      pointwiseOperatorNormVarianceProxyNormRHS (I := I) R := by
  dsimp [matrixVarianceProxyNorm, deterministicMatrixVarianceProxyNorm,
    matrixVarianceProxy, pointwiseOperatorNormVarianceProxyNormRHS]
  calc
    norm (Finset.univ.sum fun i : I => matrixSecondMoment P (A i))
        <= Finset.univ.sum fun i : I => norm (matrixSecondMoment P (A i)) := by
          exact norm_sum_le _ _
    _ <= Finset.univ.sum fun _i : I => R ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact deterministicOperatorNorm_matrixSecondMoment_le_sq_of_forall
            (P := P) (A := A i) (R := R) (hInt i) (hBound i) hR
    _ = (Fintype.card I : Real) * R ^ 2 := by
          simp

/-- The square of a self-adjoint real matrix is self-adjoint. -/
theorem isSelfAdjointMatrix_matrixSquare_of_isSelfAdjointMatrix {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsSelfAdjointMatrix A) :
    IsSelfAdjointMatrix (matrixSquare A) := by
  apply Matrix.IsHermitian.ext
  intro i j
  calc
    star (matrixSquare A j i)
        = Finset.univ.sum fun k : Fin n => star (A j k * A k i) := by
          simp [matrixSquare, Matrix.mul_apply]
    _ = Finset.univ.sum fun k : Fin n => A i k * A k j := by
          apply Finset.sum_congr rfl
          intro k _
          have hki : star (A k i) = A i k := Matrix.IsHermitian.apply hA i k
          have hjk : star (A j k) = A k j := Matrix.IsHermitian.apply hA k j
          calc
            star (A j k * A k i) = star (A k i) * star (A j k) := by
              simpa using (star_mul (A j k) (A k i))
            _ = A i k * A k j := by
              rw [hki, hjk]
    _ = matrixSquare A i j := by
          simp [matrixSquare, Matrix.mul_apply]

/-! ## PSD structure of matrix squares, second moments, and variance proxies -/

/-- Quadratic form of the square of a self-adjoint real matrix is the squared
Euclidean norm of the matrix-vector product. -/
theorem matrixQuadraticForm_matrixSquare_eq_matVecSqNorm_of_selfAdjoint {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsSelfAdjointMatrix A)
    (x : Fin n -> Real) :
    matrixQuadraticForm (matrixSquare A) x = matVecSqNorm A x := by
  have hsymm : forall i j : Fin n, A i j = A j i := by
    intro i j
    have h := Matrix.IsHermitian.apply hA i j
    simpa using h.symm
  have hsq : forall u : Fin n -> Real,
      (Finset.univ.sum fun i : Fin n =>
        Finset.univ.sum fun j : Fin n => u i * u j) =
        (Finset.univ.sum fun i : Fin n => u i) ^ 2 := by
    intro u
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc
    matrixQuadraticForm (matrixSquare A) x
        = Finset.univ.sum fun i : Fin n =>
            Finset.univ.sum fun j : Fin n =>
              (x i * Finset.univ.sum (fun k : Fin n => A i k * A k j)) * x j := by
          simp [matrixQuadraticForm, matrixSquare, Matrix.mul_apply]
    _ = Finset.univ.sum fun i : Fin n =>
          Finset.univ.sum fun j : Fin n =>
            Finset.univ.sum fun k : Fin n => (A k i * x i) * (A k j * x j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          rw [hsymm i k]
          ring
    _ = Finset.univ.sum fun k : Fin n =>
          Finset.univ.sum fun i : Fin n =>
            Finset.univ.sum fun j : Fin n => (A k i * x i) * (A k j * x j) := by
          calc
            (Finset.univ.sum fun i : Fin n =>
              Finset.univ.sum fun j : Fin n =>
                Finset.univ.sum fun k : Fin n => (A k i * x i) * (A k j * x j))
                = Finset.univ.sum fun i : Fin n =>
                    Finset.univ.sum fun k : Fin n =>
                      Finset.univ.sum fun j : Fin n => (A k i * x i) * (A k j * x j) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [Finset.sum_comm]
            _ = Finset.univ.sum fun k : Fin n =>
                  Finset.univ.sum fun i : Fin n =>
                    Finset.univ.sum fun j : Fin n => (A k i * x i) * (A k j * x j) := by
                  rw [Finset.sum_comm]
    _ = Finset.univ.sum fun k : Fin n =>
          (Finset.univ.sum fun i : Fin n => A k i * x i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _
          exact hsq (fun i : Fin n => A k i * x i)
    _ = matVecSqNorm A x := by
          simp [matVecSqNorm, vectorSqNorm]

/-- The square of a self-adjoint real matrix is PSD in the explicit
HighDimProb quadratic-form order. -/
theorem isPSD_matrixSquare_of_selfAdjoint {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsSelfAdjointMatrix A) :
    IsPSDMatrix (matrixSquare A) := by
  refine ⟨?_, ?_⟩
  · have hsqAdj : IsSelfAdjointMatrix (matrixSquare A) :=
      isSelfAdjointMatrix_matrixSquare_of_isSelfAdjointMatrix hA
    apply Matrix.IsSymm.ext
    intro i j
    have h := Matrix.IsHermitian.apply hsqAdj i j
    simpa using h
  · intro x
    rw [matrixQuadraticForm_matrixSquare_eq_matVecSqNorm_of_selfAdjoint hA]
    exact matVecSqNorm_nonneg A x

/-- Entrywise matrix expectation commutes with the explicit quadratic form,
under entrywise integrability. -/
theorem matrixQuadraticForm_matrixExpect {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} {A : RandomMatrix Omega n n}
    (hA : IntegrableRandomMatrix P A) (x : Fin n -> Real) :
    matrixQuadraticForm (matrixExpect P A) x =
      expect P (fun omega => matrixQuadraticForm (A omega) x) := by
  calc
    matrixQuadraticForm (matrixExpect P A) x
        = Finset.univ.sum fun i : Fin n =>
            Finset.univ.sum fun j : Fin n =>
              x i * (∫ omega, A omega i j ∂P) * x j := by
          simp [matrixQuadraticForm, matrixExpect, expect, matrixEntry]
    _ = Finset.univ.sum fun i : Fin n =>
          Finset.univ.sum fun j : Fin n =>
            ∫ omega, x i * A omega i j * x j ∂P := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          calc
            x i * (∫ omega, A omega i j ∂P) * x j
                = (∫ omega, x i * A omega i j ∂P) * x j := by
                  rw [MeasureTheory.integral_const_mul]
            _ = ∫ omega, (x i * A omega i j) * x j ∂P := by
                  rw [MeasureTheory.integral_mul_const]
            _ = ∫ omega, x i * A omega i j * x j ∂P := by
                  rfl
    _ = ∫ omega, Finset.univ.sum fun i : Fin n =>
          Finset.univ.sum fun j : Fin n => x i * A omega i j * x j ∂P := by
          have houter :
              (∫ omega, Finset.univ.sum fun i : Fin n =>
                Finset.univ.sum fun j : Fin n => x i * A omega i j * x j ∂P) =
                Finset.univ.sum fun i : Fin n =>
                  ∫ omega, Finset.univ.sum fun j : Fin n => x i * A omega i j * x j ∂P :=
            MeasureTheory.integral_finsetSum Finset.univ fun i _ =>
              integrable_finsetSum Finset.univ fun j _ =>
                ((hA i j).const_mul (x i)).mul_const (x j)
          rw [houter]
          apply Finset.sum_congr rfl
          intro i _
          have hinner :
              (∫ omega, Finset.univ.sum fun j : Fin n => x i * A omega i j * x j ∂P) =
                Finset.univ.sum fun j : Fin n =>
                  ∫ omega, x i * A omega i j * x j ∂P :=
            MeasureTheory.integral_finsetSum Finset.univ fun j _ =>
              ((hA i j).const_mul (x i)).mul_const (x j)
          rw [hinner]
    _ = expect P (fun omega => matrixQuadraticForm (A omega) x) := by
          simp [expect, matrixQuadraticForm]

/-- Entrywise integrability is closed under pointwise matrix subtraction. -/
theorem integrableRandomMatrix_sub {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A B : RandomMatrix Omega m n}
    (hA : IntegrableRandomMatrix P A)
    (hB : IntegrableRandomMatrix P B) :
    IntegrableRandomMatrix P (fun omega => B omega - A omega) := by
  intro i j
  change Integrable (fun omega => B omega i j - A omega i j) P
  exact (hB i j).sub (hA i j)

/-- Entrywise integrability is closed under pointwise matrix addition. -/
theorem integrableRandomMatrix_add {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A B : RandomMatrix Omega m n}
    (hA : IntegrableRandomMatrix P A)
    (hB : IntegrableRandomMatrix P B) :
    IntegrableRandomMatrix P (fun omega => A omega + B omega) := by
  intro i j
  change Integrable (fun omega => A omega i j + B omega i j) P
  exact (hA i j).add (hB i j)

/-- Entrywise integrability is closed under deterministic scalar multiplication. -/
theorem integrableRandomMatrix_smul {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} (c : Real)
    {A : RandomMatrix Omega m n} (hA : IntegrableRandomMatrix P A) :
    IntegrableRandomMatrix P (fun omega => c • A omega) := by
  intro i j
  change Integrable (fun omega => c * A omega i j) P
  exact (hA i j).const_mul c

/-- Entrywise integrability is closed under deterministic left matrix
multiplication. -/
theorem integrableRandomMatrix_const_mul {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {l m n : Nat}
    (C : Matrix (Fin l) (Fin m) Real)
    {A : RandomMatrix Omega m n} (hA : IntegrableRandomMatrix P A) :
    IntegrableRandomMatrix P (fun omega => C * A omega) := by
  intro i j
  change Integrable
    (fun omega => Finset.univ.sum fun k : Fin m => C i k * A omega k j) P
  exact integrable_finsetSum Finset.univ fun k _ =>
    (hA k j).const_mul (C i k)

/-- Entrywise integrability is closed under deterministic right matrix
multiplication. -/
theorem integrableRandomMatrix_mul_const {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {l m n : Nat}
    {A : RandomMatrix Omega l m}
    (C : Matrix (Fin m) (Fin n) Real)
    (hA : IntegrableRandomMatrix P A) :
    IntegrableRandomMatrix P (fun omega => A omega * C) := by
  intro i j
  change Integrable
    (fun omega => Finset.univ.sum fun k : Fin m => A omega i k * C k j) P
  exact integrable_finsetSum Finset.univ fun k _ =>
    (hA i k).mul_const (C k j)
/-- The zero random matrix is entrywise integrable. -/
theorem integrableRandomMatrix_zero {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} :
    IntegrableRandomMatrix P (fun _omega => (0 : Matrix (Fin m) (Fin n) Real)) := by
  intro i j
  change Integrable (fun _omega : Omega => (0 : Real)) P
  exact MeasureTheory.integrable_zero Omega Real P

/-- Constant random matrices are entrywise integrable over finite measures. -/
theorem integrableRandomMatrix_const {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsFiniteMeasure P] {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) :
    IntegrableRandomMatrix P (fun _omega => A) := by
  intro i j
  change Integrable (fun _omega : Omega => A i j) P
  exact MeasureTheory.integrable_const (A i j)

/-- Entrywise matrix expectation commutes with pointwise matrix subtraction. -/
theorem matrixExpect_sub {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A B : RandomMatrix Omega m n}
    (hA : IntegrableRandomMatrix P A)
    (hB : IntegrableRandomMatrix P B) :
    matrixExpect P (fun omega => B omega - A omega) =
      matrixExpect P B - matrixExpect P A := by
  ext i j
  simp only [matrixExpect_apply, expect_def, matrixEntry_apply, Matrix.sub_apply]
  exact MeasureTheory.integral_sub (hB i j) (hA i j)

/-- Entrywise matrix expectation commutes with pointwise matrix addition. -/
theorem matrixExpect_add {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A B : RandomMatrix Omega m n}
    (hA : IntegrableRandomMatrix P A)
    (hB : IntegrableRandomMatrix P B) :
    matrixExpect P (fun omega => A omega + B omega) =
      matrixExpect P A + matrixExpect P B := by
  ext i j
  simp only [matrixExpect_apply, expect_def, matrixEntry_apply, Matrix.add_apply]
  exact MeasureTheory.integral_add (hA i j) (hB i j)

/-- Entrywise matrix expectation commutes with deterministic scalar multiplication. -/
theorem matrixExpect_smul {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} (c : Real)
    {A : RandomMatrix Omega m n} :
    matrixExpect P (fun omega => c • A omega) =
      c • matrixExpect P A := by
  ext i j
  simp only [matrixExpect_apply, expect_def, matrixEntry_apply, Matrix.smul_apply,
    smul_eq_mul]
  exact MeasureTheory.integral_smul c (fun omega => A omega i j)

/-- Entrywise matrix expectation commutes with deterministic left matrix
multiplication. -/
theorem matrixExpect_const_mul {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {l m n : Nat}
    (C : Matrix (Fin l) (Fin m) Real)
    {A : RandomMatrix Omega m n}
    (hA : IntegrableRandomMatrix P A) :
    matrixExpect P (fun omega => C * A omega) = C * matrixExpect P A := by
  ext i j
  change
    (∫ omega, Finset.univ.sum (fun k : Fin m => C i k * A omega k j) ∂P) =
      Finset.univ.sum (fun k : Fin m => C i k * matrixExpect P A k j)
  rw [MeasureTheory.integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro k _
    rw [MeasureTheory.integral_const_mul]
    rfl
  · intro k _
    exact (hA k j).const_mul (C i k)

/-- Entrywise matrix expectation commutes with deterministic right matrix
multiplication. -/
theorem matrixExpect_mul_const {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {l m n : Nat}
    {A : RandomMatrix Omega l m}
    (C : Matrix (Fin m) (Fin n) Real)
    (hA : IntegrableRandomMatrix P A) :
    matrixExpect P (fun omega => A omega * C) = matrixExpect P A * C := by
  ext i j
  change
    (∫ omega, Finset.univ.sum (fun k : Fin m => A omega i k * C k j) ∂P) =
      Finset.univ.sum (fun k : Fin m => matrixExpect P A i k * C k j)
  rw [MeasureTheory.integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro k _
    rw [MeasureTheory.integral_mul_const]
    rfl
  · intro k _
    exact (hA i k).mul_const (C k j)
/-- The expectation of the zero random matrix is zero. -/
theorem matrixExpect_zero {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} :
    matrixExpect P (fun _omega => (0 : Matrix (Fin m) (Fin n) Real)) = 0 := by
  ext i j
  simp [matrixExpect, expect, matrixEntry]

/-- Entrywise expectation of a constant random matrix. -/
theorem matrixExpect_const {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} (A : Matrix (Fin m) (Fin n) Real) :
    matrixExpect P (fun _omega => A) = (P.real Set.univ) • A := by
  ext i j
  simp [matrixExpect, expect, matrixEntry, Matrix.smul_apply]

/-- Entrywise expectation of a constant matrix over a probability measure. -/
theorem matrixExpect_const_of_isProbabilityMeasure {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {m n : Nat} (A : Matrix (Fin m) (Fin n) Real) :
    matrixExpect P (fun _omega => A) = A := by
  rw [matrixExpect_const]
  ext i j
  simp [Matrix.smul_apply]

/-- Entrywise expectation of the identity matrix over a probability measure. -/
theorem matrixExpect_one_of_isProbabilityMeasure {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {n : Nat} :
    matrixExpect P (fun _omega => (1 : Matrix (Fin n) (Fin n) Real)) = 1 := by
  simpa using
    (matrixExpect_const_of_isProbabilityMeasure
      (P := P) (A := (1 : Matrix (Fin n) (Fin n) Real)))

/-- Pointwise algebraic expansion of the square of a centered random matrix.

This is a deterministic matrix-ring identity. It does not use expectation
linearity or integrability. -/
theorem randomMatrixSquare_centeredRandomMatrix_expand {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (A : RandomMatrix Omega n n) :
    randomMatrixSquare (centeredRandomMatrix P A) =
      fun omega =>
        randomMatrixSquare A omega - A omega * matrixExpect P A -
          matrixExpect P A * A omega + matrixSquare (matrixExpect P A) := by
  funext omega
  change matrixSquare (A omega - matrixExpect P A) =
    matrixSquare (A omega) - A omega * matrixExpect P A -
      matrixExpect P A * A omega + matrixSquare (matrixExpect P A)
  simp only [matrixSquare]
  noncomm_ring

/-- The centered matrix square is entrywise integrable when `A` and `A^2` are
entrywise integrable over a finite measure. -/
theorem integrableRandomMatrix_randomMatrixSquare_centeredRandomMatrix
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsFiniteMeasure P] {n : Nat} {A : RandomMatrix Omega n n}
    (hA : IntegrableRandomMatrix P A)
    (hSq : IntegrableRandomMatrix P (randomMatrixSquare A)) :
    IntegrableRandomMatrix P (randomMatrixSquare (centeredRandomMatrix P A)) := by
  let M : Matrix (Fin n) (Fin n) Real := matrixExpect P A
  have hAM : IntegrableRandomMatrix P (fun omega => A omega * M) :=
    integrableRandomMatrix_mul_const M hA
  have hMA : IntegrableRandomMatrix P (fun omega => M * A omega) :=
    integrableRandomMatrix_const_mul M hA
  have hM2 : IntegrableRandomMatrix P (fun _omega => matrixSquare M) :=
    integrableRandomMatrix_const (P := P) (matrixSquare M)
  have hSub1 :
      IntegrableRandomMatrix P
        (fun omega => randomMatrixSquare A omega - A omega * M) :=
    integrableRandomMatrix_sub hAM hSq
  have hSub2 :
      IntegrableRandomMatrix P
        (fun omega => randomMatrixSquare A omega - A omega * M - M * A omega) :=
    integrableRandomMatrix_sub hMA hSub1
  have hExpanded :
      IntegrableRandomMatrix P
        (fun omega =>
          randomMatrixSquare A omega - A omega * M - M * A omega + matrixSquare M) :=
    integrableRandomMatrix_add hSub2 hM2
  simpa [M, randomMatrixSquare_centeredRandomMatrix_expand (P := P) A] using hExpanded

/-- Centered rank-one family square integrability from coordinate `L^4` assumptions.

This is a family-level provider. It reuses the generic centered-square bridge,
the uncentered rank-one integrability API, and the uncentered rank-one square
integrability provider; it does not prove a variance-proxy norm bound. -/
theorem integrableRandomMatrix_randomMatrixSquare_centeredRankOneRandomMatrixFamily_of_memLp_four
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsFiniteMeasure P] {I : Type*} {n : Nat}
    {X : I -> RandomVector Omega n}
    (hX : forall i, forall j : Fin n,
      MemLpRealRandomVariable P (coord (X i) j) (4 : ENNReal)) :
    forall i,
      IntegrableRandomMatrix P
        (randomMatrixSquare ((centeredRankOneRandomMatrixFamily P X) i)) := by
  intro i
  rw [centeredRankOneRandomMatrixFamily_apply]
  have hX2 : forall j : Fin n,
      MemLpRealRandomVariable P (coord (X i) j) (2 : ENNReal) := by
    intro j
    exact (hX i j).mono_exponent (by norm_num : (2 : ENNReal) <= 4)
  exact integrableRandomMatrix_randomMatrixSquare_centeredRandomMatrix
    (P := P) (A := rankOneRandomMatrix (X i))
    (integrableRandomMatrix_rankOneRandomMatrix_of_memLp_two
      (P := P) (X := X i) hX2)
    (integrableRandomMatrix_randomMatrixSquare_rankOneRandomMatrix_of_memLp_four
      (P := P) (X := X i) (hX i))

/-- Centered rank-one family square integrability from coordinate `L^2`
assumptions and a pointwise squared-vector-norm bound.

This provider discharges the centered-square integrability premise only. It
keeps variance-proxy norm control separate from integrability. -/
theorem integrableRandomMatrix_square_centeredRankOneFamily_of_sqNorm_bound_memLpTwo
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsFiniteMeasure P] {I : Type*} {n : Nat}
    {X : I -> RandomVector Omega n} {R : Real}
    (hLp : forall i, forall j : Fin n,
      MemLpRealRandomVariable P (coord (X i) j) (2 : ENNReal))
    (hSq : forall i omega, vectorSqNorm (X i omega) <= R) :
    forall i,
      IntegrableRandomMatrix P
        (randomMatrixSquare ((centeredRankOneRandomMatrixFamily P X) i)) := by
  intro i
  rw [centeredRankOneRandomMatrixFamily_apply]
  exact integrableRandomMatrix_randomMatrixSquare_centeredRandomMatrix
    (P := P) (A := rankOneRandomMatrix (X i))
    (integrableRandomMatrix_rankOneRandomMatrix_of_memLp_two
      (P := P) (X := X i) (hLp i))
    (integrableRandomMatrix_randomMatrixSquare_rankOneRandomMatrix_of_sqNorm_bound_memLp_two
      (P := P) (X := X i) (R := R) (hLp i) (hSq i))

/-- Centered-square expectation expansion.

For a square random matrix `A`, entrywise expectation gives
`E[(A - E A)^2] = E[A^2] - (E A)^2`. The proof is purely entrywise expectation
algebra plus deterministic noncommutative matrix-ring expansion; it does not
prove any Loewner comparison or variance-proxy norm control. -/
theorem matrixSecondMoment_centeredRandomMatrix {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {n : Nat} {A : RandomMatrix Omega n n}
    (hA : IntegrableRandomMatrix P A)
    (hSq : IntegrableRandomMatrix P (randomMatrixSquare A)) :
    matrixSecondMoment P (centeredRandomMatrix P A) =
      matrixSecondMoment P A - matrixSquare (matrixExpect P A) := by
  let M : Matrix (Fin n) (Fin n) Real := matrixExpect P A
  have hExpand := randomMatrixSquare_centeredRandomMatrix_expand (P := P) A
  have hAM : IntegrableRandomMatrix P (fun omega => A omega * M) :=
    integrableRandomMatrix_mul_const M hA
  have hMA : IntegrableRandomMatrix P (fun omega => M * A omega) :=
    integrableRandomMatrix_const_mul M hA
  have hM2 : IntegrableRandomMatrix P (fun _omega => matrixSquare M) :=
    integrableRandomMatrix_const (P := P) (matrixSquare M)
  have hLeft :
      matrixExpect P (randomMatrixSquare (centeredRandomMatrix P A)) =
        matrixExpect P
          (fun omega =>
            randomMatrixSquare A omega - A omega * M - M * A omega + matrixSquare M) := by
    rw [hExpand]
  have hSub1Int :
      IntegrableRandomMatrix P
        (fun omega => randomMatrixSquare A omega - A omega * M) :=
    integrableRandomMatrix_sub hAM hSq
  calc
    matrixSecondMoment P (centeredRandomMatrix P A) =
        matrixExpect P (randomMatrixSquare (centeredRandomMatrix P A)) := rfl
    _ = matrixExpect P
          (fun omega =>
            randomMatrixSquare A omega - A omega * M - M * A omega + matrixSquare M) := hLeft
    _ = matrixExpect P
          (fun omega => randomMatrixSquare A omega - A omega * M - M * A omega) +
          matrixExpect P (fun _omega => matrixSquare M) := by
        rw [matrixExpect_add]
        · exact integrableRandomMatrix_sub hMA hSub1Int
        · exact hM2
    _ = matrixExpect P (fun omega => randomMatrixSquare A omega - A omega * M) -
          matrixExpect P (fun omega => M * A omega) +
          matrixExpect P (fun _omega => matrixSquare M) := by
        rw [matrixExpect_sub hMA hSub1Int]
    _ = (matrixSecondMoment P A - matrixExpect P (fun omega => A omega * M)) -
          matrixExpect P (fun omega => M * A omega) +
          matrixExpect P (fun _omega => matrixSquare M) := by
        rw [matrixExpect_sub hAM hSq]
        rfl
    _ = (matrixSecondMoment P A - M * M) - M * M + matrixSquare M := by
        rw [matrixExpect_mul_const M hA, matrixExpect_const_mul M hA,
          matrixExpect_const_of_isProbabilityMeasure]
    _ = matrixSecondMoment P A - matrixSquare (matrixExpect P A) := by
        simp [M, matrixSquare]
/-- Entrywise expectation preserves pointwise PSD matrices. -/
theorem isPSDMatrix_matrixExpect_of_pointwise_isPSD {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega}
    {n : Nat} {A : RandomMatrix Omega n n}
    (hInt : IntegrableRandomMatrix P A)
    (hPSD : forall omega, IsPSDMatrix (A omega)) :
    IsPSDMatrix (matrixExpect P A) := by
  refine ⟨?_, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    dsimp [matrixExpect, expect]
    refine integral_congr_ae ?_
    filter_upwards with omega
    exact isSymmetricMatrix_apply (hPSD omega).1 i j
  · intro x
    rw [matrixQuadraticForm_matrixExpect hInt x]
    change 0 <= ∫ omega, matrixQuadraticForm (A omega) x ∂P
    exact MeasureTheory.integral_nonneg fun omega => (hPSD omega).2 x

/-- Entrywise matrix expectation is monotone for the explicit matrix order. -/
theorem matrixExpect_matrixLE_of_pointwise_matrixLE {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega}
    {n : Nat} {A B : RandomMatrix Omega n n}
    (hIntA : IntegrableRandomMatrix P A)
    (hIntB : IntegrableRandomMatrix P B)
    (hLE : forall omega, MatrixLE (A omega) (B omega)) :
    MatrixLE (matrixExpect P A) (matrixExpect P B) := by
  unfold MatrixLE
  have hIntSub : IntegrableRandomMatrix P (fun omega => B omega - A omega) :=
    integrableRandomMatrix_sub hIntA hIntB
  have hPSD :
      IsPSDMatrix (matrixExpect P (fun omega => B omega - A omega)) :=
    isPSDMatrix_matrixExpect_of_pointwise_isPSD hIntSub hLE
  have hSub :
      matrixExpect P (fun omega => B omega - A omega) =
        matrixExpect P B - matrixExpect P A :=
    matrixExpect_sub hIntA hIntB
  rw [← hSub]
  exact hPSD

/-- Typed target: the square of a self-adjoint real matrix is PSD.

The proof requires the identity `xᵀ A² x = (Ax)ᵀ (Ax) = ‖Ax‖² ≥ 0`.
When A is self-adjoint, `A² = Aᵀ A`, and `xᵀ Aᵀ A x = ‖Ax‖²` is true
for any real matrix A by expanding the finite sums and using
`Finset.sum_comm` and `Finset.mul_sum`.

The corresponding theorem `isPSD_matrixSquare_of_selfAdjoint` is now proved. -/
abbrev isPSDMatrixSquareOfSelfAdjointStatement {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) : Prop :=
  IsSelfAdjointMatrix A ->
    IsPSDMatrix (matrixSquare A)

/-- The second moment matrix of a self-adjoint random matrix family is self-adjoint.
This is proven: each `(A ω)^2` is self-adjoint, and entrywise expectation preserves
self-adjointness because `star` is identity on ℝ and the integral is linear. -/
theorem isSelfAdjointMatrix_matrixSecondMoment {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} {A : RandomMatrix Omega n n}
    (hA : RandomSelfAdjointMatrix P A) :
    IsSelfAdjointMatrix (matrixSecondMoment P A) := by
  apply Matrix.IsHermitian.ext
  intro i j
  -- For real matrices, star = id.
  -- We need: (E[A^2])_ji = (E[A^2])_ij
  dsimp [matrixSecondMoment, matrixExpect, expect]
  -- Goal:
  -- (∫ ω, (randomMatrixSquare A) ω j i ∂P) =
  --   (∫ ω, (randomMatrixSquare A) ω i j ∂P)
  have h_entry_eq : ∀ ω, (randomMatrixSquare A) ω j i = (randomMatrixSquare A) ω i j := by
    intro ω
    simp [randomMatrixSquare]
    have h_sq_herm : IsSelfAdjointMatrix (matrixSquare (A ω)) :=
      isSelfAdjointMatrix_matrixSquare_of_isSelfAdjointMatrix (hA ω)
    -- h_sq_herm : IsHermitian (A ω)^2, so (A ω)^2_{ji} = (A ω)^2_{ij} (real case)
    have h_eq := Matrix.IsHermitian.apply h_sq_herm j i
    -- h_eq : star ((A ω)^2_{i j}) = (A ω)^2_{j i}
    -- For ℝ, star = id, so this gives (A ω)^2_{ij} = (A ω)^2_{ji}
    -- Goal: (A ω)^2_{ji} = (A ω)^2_{ij}, which is h_eq.symm
    simpa using h_eq.symm
  -- Now the two functions are equal pointwise, so their integrals are equal
  refine integral_congr_ae ?_
  filter_upwards with ω
  exact h_entry_eq ω

/-- The second moment matrix `E[A^2]` of a self-adjoint random matrix is PSD,
provided the squared random matrix is entrywise integrable. -/
theorem isPSD_matrixSecondMoment_of_selfAdjoint {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} {A : RandomMatrix Omega n n}
    (hA : RandomSelfAdjointMatrix P A)
    (hInt : IntegrableRandomMatrix P (randomMatrixSquare A)) :
    IsPSDMatrix (matrixSecondMoment P A) := by
  refine ⟨?_, ?_⟩
  · have hAdj : IsSelfAdjointMatrix (matrixSecondMoment P A) :=
      isSelfAdjointMatrix_matrixSecondMoment hA
    apply Matrix.IsSymm.ext
    intro i j
    have h := Matrix.IsHermitian.apply hAdj i j
    simpa using h
  · intro x
    change 0 <= matrixQuadraticForm (matrixExpect P (randomMatrixSquare A)) x
    rw [matrixQuadraticForm_matrixExpect hInt]
    change 0 <= ∫ omega, matrixQuadraticForm (randomMatrixSquare A omega) x ∂P
    exact MeasureTheory.integral_nonneg fun omega => by
      simpa [randomMatrixSquare] using
        (isPSD_matrixSquare_of_selfAdjoint (hA omega)).2 x

/-- Typed target: the second moment matrix `E[A^2]` of a self-adjoint random matrix is PSD.

The proof requires: `matrixQuadraticForm (E[A^2]) x = E[matrixQuadraticForm(A^2) x]`
(linearity of expectation over finite sums), and then pointwise nonnegativity
of `matrixQuadraticForm (A ω^2) x` gives the result.

The corresponding theorem `isPSD_matrixSecondMoment_of_selfAdjoint` is now
proved with the explicit additional assumption
`IntegrableRandomMatrix P (randomMatrixSquare A)`. -/
abbrev isPSDMatrixSecondMomentOfSelfAdjointStatement {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat} {A : RandomMatrix Omega n n}
    : Prop :=
  RandomSelfAdjointMatrix P A ->
    IsPSDMatrix (matrixSecondMoment P A)

/-- The matrix variance proxy `sum_i E[A_i^2]` is self-adjoint when each term is. -/
theorem isSelfAdjointMatrix_matrixVarianceProxy {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} [Fintype I] {n : Nat} (P : Measure Omega)
    {A : I -> RandomMatrix Omega n n}
    (hA : forall i, RandomSelfAdjointMatrix P (A i)) :
    IsSelfAdjointMatrix (matrixVarianceProxy P A) := by
  apply isSelfAdjointMatrix_sum
  intro i
  exact isSelfAdjointMatrix_matrixSecondMoment (hA i)

/-- The matrix variance proxy `sum_i E[A_i^2]` is PSD when every summand is
self-adjoint and every squared summand is entrywise integrable. -/
theorem isPSD_matrixVarianceProxy_of_selfAdjoint {Omega : Type*} [MeasurableSpace Omega]
    {I : Type*} [Fintype I] {n : Nat} (P : Measure Omega)
    {A : I -> RandomMatrix Omega n n}
    (hA : forall i, RandomSelfAdjointMatrix P (A i))
    (hInt : forall i, IntegrableRandomMatrix P (randomMatrixSquare (A i))) :
    IsPSDMatrix (matrixVarianceProxy P A) := by
  dsimp [matrixVarianceProxy]
  apply isPSDMatrix_sum
  intro i
  exact isPSD_matrixSecondMoment_of_selfAdjoint (hA i) (hInt i)

/-- Typed target: the matrix variance proxy `sum_i E[A_i^2]` is PSD.

The proof follows from each `E[A_i^2]` being PSD and the fact that
`matrixQuadraticForm` is linear in the matrix, distributing over finite sums.

The corresponding theorem `isPSD_matrixVarianceProxy_of_selfAdjoint` is now
proved with explicit per-summand square-integrability assumptions. -/
abbrev isPSDMatrixVarianceProxyOfSelfAdjointStatement {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} [Fintype I] {n : Nat} (P : Measure Omega)
    (A : I -> RandomMatrix Omega n n) : Prop :=
  (forall i, RandomSelfAdjointMatrix P (A i)) ->
    IsPSDMatrix (matrixVarianceProxy P A)



end

end HighDimProb
