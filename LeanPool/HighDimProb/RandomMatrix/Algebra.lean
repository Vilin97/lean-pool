/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.SampleCovariance
import LeanPool.HighDimProb.RandomMatrix.Expectation
import LeanPool.HighDimProb.RandomMatrix.QuadraticForm
import LeanPool.HighDimProb.RandomMatrix.RowsCols
import LeanPool.HighDimProb.RandomMatrix.Sums

/-!
# Algebraic bridges for random matrices

Verified Wikipedia references:
* Dot product: https://en.wikipedia.org/wiki/Dot_product
* Quadratic form: https://en.wikipedia.org/wiki/Quadratic_form
* Sample mean and covariance: https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/

namespace HighDimProb

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Dot product of one random-matrix row with a deterministic vector. -/
def rowDot {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) (x : Fin n -> Real) (k : Fin m)
    (omega : Omega) : Real :=
  Finset.univ.sum fun i : Fin n => A omega k i * x i

@[simp]
theorem rowDot_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (x : Fin n -> Real) (k : Fin m)
    (omega : Omega) :
    rowDot A x k omega = Finset.univ.sum fun i : Fin n => A omega k i * x i :=
  rfl

/-- A squared row marginal is nonnegative. -/
theorem rowDot_sq_nonneg {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (x : Fin n -> Real) (k : Fin m)
    (omega : Omega) :
    0 <= (rowDot A x k omega) ^ 2 :=
  sq_nonneg _

/-- A finite sum of squared row marginals is nonnegative. -/
theorem sum_rowDot_sq_nonneg {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (x : Fin n -> Real) (omega : Omega) :
    0 <= Finset.univ.sum fun k : Fin m => (rowDot A x k omega) ^ 2 :=
  Finset.sum_nonneg fun k _ => rowDot_sq_nonneg A x k omega

/-- Row rank-one family behind the sample covariance. -/
abbrev sampleCovarianceRowRankOneFamily {Omega : Type*}
    {m n : Nat} (A : RandomMatrix Omega m n) :
    Fin m -> RandomMatrix Omega n n :=
  rankOneRandomMatrixFamily (rowVector A)

@[simp]
theorem sampleCovarianceRowRankOneFamily_apply {Omega : Type*}
    [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (k : Fin m) :
    sampleCovarianceRowRankOneFamily A k =
      rankOneRandomMatrix (rowVector A k) :=
  rfl

/-- Centered row rank-one family behind the centered sample covariance. -/
abbrev centeredSampleCovarianceRowRankOneFamily {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {m n : Nat}
    (A : RandomMatrix Omega m n) :
    Fin m -> RandomMatrix Omega n n :=
  centeredRankOneRandomMatrixFamily P (rowVector A)

@[simp]
theorem centeredSampleCovarianceRowRankOneFamily_apply {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {m n : Nat}
    (A : RandomMatrix Omega m n) (k : Fin m) :
    centeredSampleCovarianceRowRankOneFamily (P := P) A k =
      centeredRankOneRandomMatrix P (rowVector A k) :=
  rfl

/--
Unnormalized sum of the row rank-one random matrices behind the sample
covariance.

This names the reusable right-hand side before the scalar `(1 / m)` factor is
applied.
-/
def sampleCovarianceRowRankOneSum {Omega : Type*}
    {m n : Nat} (A : RandomMatrix Omega m n) : RandomMatrix Omega n n :=
  randomMatrixSum (sampleCovarianceRowRankOneFamily A)

/--
Normalized row rank-one sum with the same scaling convention as
`sampleCovariance`.
-/
def normalizedSampleCovarianceRowRankOneSum {Omega : Type*}
    {m n : Nat}
    (A : RandomMatrix Omega m n) : RandomMatrix Omega n n :=
  fun omega => (1 / (m : Real)) • sampleCovarianceRowRankOneSum A omega

/--
Unnormalized sum of centered row rank-one random matrices.

This is the named summand family used by the centered sample-covariance
deviation bridge.
-/
def centeredSampleCovarianceRowRankOneSum {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {m n : Nat}
    (A : RandomMatrix Omega m n) : RandomMatrix Omega n n :=
  randomMatrixSum (centeredSampleCovarianceRowRankOneFamily (P := P) A)

/--
Normalized centered row rank-one sum with the same `(1 / m)` scaling convention
as `sampleCovariance`.
-/
def normalizedCenteredSampleCovarianceRowRankOneSum {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {m n : Nat}
    (A : RandomMatrix Omega m n) : RandomMatrix Omega n n :=
  fun omega =>
    (1 / (m : Real)) • centeredSampleCovarianceRowRankOneSum (P := P) A omega

/--
Matrix-level rank-one sum form of the uncentered sample covariance.

This rewrites the existing entrywise definition `(1 / m) A^T A` as a
named normalized finite sum of the existing row rank-one random matrices.
-/
theorem sampleCovariance_eq_normalized_rowRankOne_sum
    {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) :
    sampleCovariance A = normalizedSampleCovarianceRowRankOneSum A := by
  funext omega
  ext i j
  have hEntry :
      sampleCovarianceRowRankOneSum A omega i j =
        Finset.univ.sum fun k : Fin m => A omega k i * A omega k j := by
    simp [sampleCovarianceRowRankOneSum, randomMatrixSum, Matrix.sum_apply]
  calc
    sampleCovariance A omega i j =
        (1 / (m : Real)) *
          Finset.univ.sum (fun k : Fin m => A omega k i * A omega k j) := by
      rfl
    _ = (1 / (m : Real)) *
        sampleCovarianceRowRankOneSum A omega i j := by
      rw [hEntry]
    _ = normalizedSampleCovarianceRowRankOneSum A omega i j := by
      rfl

/--
Centered sample covariance as a normalized sum of centered row rank-one
summands.

This is the deviation form of `sampleCovariance_eq_normalized_rowRankOne_sum`:
the left side is `sampleCovariance A - E[sampleCovariance A]`, and the right
side centers each row outer product before summing.
-/
theorem sampleCovariance_deviation_eq_normalized_centered_rowRankOne_sum
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {m n : Nat}
    (A : RandomMatrix Omega m n)
    (hInt : forall k : Fin m,
      IntegrableRandomMatrix P (rankOneRandomMatrix (rowVector A k))) :
    centeredRandomMatrix P (sampleCovariance A) =
      normalizedCenteredSampleCovarianceRowRankOneSum (P := P) A := by
  funext omega
  ext i j
  have hIntEntry :
      forall k : Fin m, Integrable (fun omega => A omega k i * A omega k j) P := by
    intro k
    change Integrable (matrixEntry (rankOneRandomMatrix (rowVector A k)) i j) P
    exact hInt k i j
  have hExpect :
      matrixExpect P (sampleCovariance A) i j =
        (1 / (m : Real)) *
          Finset.univ.sum
            (fun k : Fin m =>
              matrixExpect P (rankOneRandomMatrix (rowVector A k)) i j) := by
    calc
      matrixExpect P (sampleCovariance A) i j =
          ∫ omega, (1 / (m : Real)) *
            Finset.univ.sum (fun k : Fin m => A omega k i * A omega k j) ∂P := by
        rfl
      _ = (1 / (m : Real)) *
          ∫ omega, Finset.univ.sum (fun k : Fin m => A omega k i * A omega k j) ∂P := by
        rw [integral_const_mul]
      _ = (1 / (m : Real)) *
          Finset.univ.sum
            (fun k : Fin m => ∫ omega, A omega k i * A omega k j ∂P) := by
        rw [integral_finsetSum]
        intro k _
        exact hIntEntry k
      _ = (1 / (m : Real)) *
          Finset.univ.sum
            (fun k : Fin m =>
              matrixExpect P (rankOneRandomMatrix (rowVector A k)) i j) := by
        rfl
  calc
    centeredRandomMatrix P (sampleCovariance A) omega i j =
        (1 / (m : Real)) *
          Finset.univ.sum (fun k : Fin m => A omega k i * A omega k j) -
        (1 / (m : Real)) *
          Finset.univ.sum
            (fun k : Fin m =>
              matrixExpect P (rankOneRandomMatrix (rowVector A k)) i j) := by
      rw [centeredRandomMatrix_apply, hExpect]
      rfl
    _ = (1 / (m : Real)) *
        (Finset.univ.sum (fun k : Fin m => A omega k i * A omega k j) -
          Finset.univ.sum
            (fun k : Fin m =>
              matrixExpect P (rankOneRandomMatrix (rowVector A k)) i j)) := by
      ring
    _ = (1 / (m : Real)) *
        Finset.univ.sum
          (fun k : Fin m =>
            A omega k i * A omega k j -
              matrixExpect P (rankOneRandomMatrix (rowVector A k)) i j) := by
      rw [Finset.sum_sub_distrib]
    _ = normalizedCenteredSampleCovarianceRowRankOneSum (P := P) A omega i j := by
      unfold normalizedCenteredSampleCovarianceRowRankOneSum
        centeredSampleCovarianceRowRankOneSum randomMatrixSum
        centeredSampleCovarianceRowRankOneFamily centeredRankOneRandomMatrixFamily
        centeredRandomMatrixFamily rankOneRandomMatrixFamily centeredRandomMatrix
        rankOneRandomMatrix rankOneMatrix rowVector
      rw [Matrix.smul_apply]
      rw [Matrix.sum_apply]
      rw [smul_eq_mul]
      simp only [Function.comp_apply]

private theorem sum_sum_mul_eq_sq {n : Nat} (u : Fin n -> Real) :
    (Finset.univ.sum fun i : Fin n =>
      Finset.univ.sum fun j : Fin n => u i * u j) =
      (Finset.univ.sum fun i : Fin n => u i) ^ 2 := by
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

private theorem sum_sum_const_mul_eq_mul_sum_sq {n : Nat} (c : Real)
    (u : Fin n -> Real) :
    (Finset.univ.sum fun i : Fin n =>
      Finset.univ.sum fun j : Fin n => c * (u i * u j)) =
      c * (Finset.univ.sum fun i : Fin n => u i) ^ 2 := by
  calc
    (Finset.univ.sum fun i : Fin n =>
      Finset.univ.sum fun j : Fin n => c * (u i * u j))
        = Finset.univ.sum fun i : Fin n =>
            c * (Finset.univ.sum fun j : Fin n => u i * u j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = c * (Finset.univ.sum fun i : Fin n =>
          Finset.univ.sum fun j : Fin n => u i * u j) := by
          rw [Finset.mul_sum]
    _ = c * (Finset.univ.sum fun i : Fin n => u i) ^ 2 := by
          rw [sum_sum_mul_eq_sq]

/--
Finite-sum algebra bridge for the uncentered sample covariance quadratic form.

The normal form keeps the row marginal explicit:
`sum k, (sum i, A omega k i * x i)^2`.
-/
theorem quadraticForm_sampleCovariance_eq_sum_sq {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : RandomMatrix Omega m n) (x : Fin n -> Real) (omega : Omega) :
    quadraticForm (sampleCovariance A) x omega =
      (1 / (m : Real)) * Finset.univ.sum
        (fun k : Fin m => (Finset.univ.sum fun i : Fin n => A omega k i * x i) ^ 2) := by
  calc
    quadraticForm (sampleCovariance A) x omega
        = Finset.univ.sum fun i : Fin n =>
            Finset.univ.sum fun j : Fin n =>
              x i * ((1 / (m : Real)) * Finset.univ.sum
                (fun k : Fin m => A omega k i * A omega k j)) * x j := by
          simp only [quadraticForm, sampleCovariance, sampleCovarianceEntry, gramMatrixEntry]
    _ = Finset.univ.sum fun i : Fin n =>
          Finset.univ.sum fun j : Fin n =>
            Finset.univ.sum fun k : Fin m =>
              (1 / (m : Real)) * ((A omega k i * x i) * (A omega k j * x j)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = Finset.univ.sum fun k : Fin m =>
          Finset.univ.sum fun i : Fin n =>
            Finset.univ.sum fun j : Fin n =>
              (1 / (m : Real)) * ((A omega k i * x i) * (A omega k j * x j)) := by
          calc
            (Finset.univ.sum fun i : Fin n =>
              Finset.univ.sum fun j : Fin n =>
                Finset.univ.sum fun k : Fin m =>
                  (1 / (m : Real)) * ((A omega k i * x i) * (A omega k j * x j)))
                = Finset.univ.sum fun i : Fin n =>
                    Finset.univ.sum fun k : Fin m =>
                      Finset.univ.sum fun j : Fin n =>
                        (1 / (m : Real)) * ((A omega k i * x i) * (A omega k j * x j)) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [Finset.sum_comm]
            _ = Finset.univ.sum fun k : Fin m =>
                  Finset.univ.sum fun i : Fin n =>
                    Finset.univ.sum fun j : Fin n =>
                      (1 / (m : Real)) * ((A omega k i * x i) * (A omega k j * x j)) := by
                  rw [Finset.sum_comm]
    _ = Finset.univ.sum fun k : Fin m =>
          (1 / (m : Real)) *
            (Finset.univ.sum fun i : Fin n => A omega k i * x i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _
          exact sum_sum_const_mul_eq_mul_sum_sq (1 / (m : Real))
            (fun i : Fin n => A omega k i * x i)
    _ = (1 / (m : Real)) * Finset.univ.sum
          (fun k : Fin m => (Finset.univ.sum fun i : Fin n => A omega k i * x i) ^ 2) := by
          rw [Finset.mul_sum]

/-- Row-dot normal form for the uncentered sample covariance quadratic form. -/
theorem quadraticForm_sampleCovariance_eq_scaled_sum_rowDot_sq
    {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (x : Fin n -> Real) (omega : Omega) :
    quadraticForm (sampleCovariance A) x omega =
      (1 / (m : Real)) *
        Finset.univ.sum (fun k : Fin m => (rowDot A x k omega) ^ 2) := by
  simpa [rowDot] using quadraticForm_sampleCovariance_eq_sum_sq A x omega

/-- The uncentered sample covariance quadratic form is pointwise nonnegative. -/
theorem quadraticForm_sampleCovariance_nonneg {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : RandomMatrix Omega m n) (x : Fin n -> Real) (omega : Omega) :
    0 <= quadraticForm (sampleCovariance A) x omega := by
  rw [quadraticForm_sampleCovariance_eq_scaled_sum_rowDot_sq]
  exact mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg m))
    (sum_rowDot_sq_nonneg A x omega)

end

end HighDimProb
