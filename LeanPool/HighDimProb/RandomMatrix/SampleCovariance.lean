/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.Basic

/-!
# Sample covariance vocabulary for random matrices

Verified Wikipedia reference:
* Sample mean and covariance:
  https://en.wikipedia.org/wiki/Sample_mean_and_covariance

Note: `wiki.md` listed `Sample_covariance_matrix`; the verifiable Wikipedia
article is the canonical `Sample_mean_and_covariance` page, which contains the
sample covariance matrix formula
`q_jk = (1 / (N - 1)) * sum_i (x_ij - xbar_j) * (x_ik - xbar_k)`.
The declarations below deliberately use the uncentered normalization
`(1 / m) * A^T A`; this matches the same Gram-matrix shape when rows have
already been centered, but it is not the unbiased `N - 1` convention.
-/

namespace HighDimProb

open MeasureTheory
open scoped BigOperators

noncomputable section

/--
Entry of the Gram matrix `A(omega)^T A(omega)`, written as an explicit row sum.

Formula reference: for rows `A_k` interpreted as observations, this entry is
`G_ij(omega) = sum_k A_ki(omega) * A_kj(omega)`, the unnormalized
Gram-matrix numerator behind sample covariance formulas; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
def gramMatrixEntry {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) (i j : Fin n) : RealRandomVariable Omega :=
  fun omega => Finset.univ.sum fun k : Fin m => A omega k i * A omega k j

/--
Gram matrix `omega |-> A(omega)^T A(omega)`, represented entrywise.

Formula reference: this matrix has entries
`G_ij = sum_k A_ki * A_kj`, i.e. the unnormalized `A^T A` product used before
dividing by the sample size or by `N - 1`; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
def gramMatrix {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) : RandomMatrix Omega n n :=
  fun omega i j => gramMatrixEntry A i j omega

/--
Entry of the row Gram matrix `A(omega) A(omega)^T`, written as an explicit column sum.

Formula reference: this row-Gram entry is
`R_ij(omega) = sum_k A_ik(omega) * A_jk(omega)`, the `A A^T` analogue of the
sample covariance Gram product; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
def rowGramMatrixEntry {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) (i j : Fin m) : RealRandomVariable Omega :=
  fun omega => Finset.univ.sum fun k : Fin n => A omega i k * A omega j k

/--
Row Gram matrix `omega |-> A(omega) A(omega)^T`, represented entrywise.

Formula reference: this row-Gram matrix has entries
`R_ij = sum_k A_ik * A_jk`, giving the `A A^T` product rather than `A^T A`;
see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
def rowGramMatrix {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) : RandomMatrix Omega m m :=
  fun omega i j => rowGramMatrixEntry A i j omega

/--
Entry of the uncentered sample covariance `(1 / m) A(omega)^T A(omega)`.

Formula reference: this entry is
`sampleCovarianceEntry_ij = (1 / m) * sum_k A_ki * A_kj`.  Wikipedia's
centered sample covariance subtracts sample means and often uses denominator
`N - 1`; this file records the uncentered `1 / m` Gram convention. See
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
def sampleCovarianceEntry {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) (i j : Fin n) : RealRandomVariable Omega :=
  fun omega => (1 / (m : Real)) * gramMatrixEntry A i j omega

/--
Uncentered sample covariance matrix with rows interpreted as samples.

Formula reference: this matrix is `(1 / m) * A^T A`, entrywise.  It is the
uncentered counterpart of Wikipedia's sample covariance matrix, which uses
centered observations `(x_i - xbar)`; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
def sampleCovariance {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) : RandomMatrix Omega n n :=
  fun omega i j => sampleCovarianceEntry A i j omega

/--
Formula reference: this unfolds the Gram entry sum
`sum_k A_ki A_kj`; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
@[simp]
theorem gramMatrixEntry_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (i j : Fin n) (omega : Omega) :
    gramMatrixEntry A i j omega =
      Finset.univ.sum fun k : Fin m => A omega k i * A omega k j :=
  rfl

/--
Formula reference: this unfolds `gramMatrix A omega i j` to
`sum_k A_ki(omega) * A_kj(omega)` through `gramMatrixEntry`; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
@[simp]
theorem gramMatrix_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (omega : Omega) (i j : Fin n) :
    gramMatrix A omega i j = gramMatrixEntry A i j omega :=
  rfl

/--
Formula reference: this unfolds the row-Gram entry sum
`sum_k A_ik A_jk`; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
@[simp]
theorem rowGramMatrixEntry_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (i j : Fin m) (omega : Omega) :
    rowGramMatrixEntry A i j omega =
      Finset.univ.sum fun k : Fin n => A omega i k * A omega j k :=
  rfl

/--
Formula reference: this unfolds `rowGramMatrix A omega i j` to
`sum_k A_ik(omega) * A_jk(omega)` through `rowGramMatrixEntry`; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
@[simp]
theorem rowGramMatrix_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (omega : Omega) (i j : Fin m) :
    rowGramMatrix A omega i j = rowGramMatrixEntry A i j omega :=
  rfl

/--
Formula reference: this unfolds the uncentered sample covariance entry
`(1 / m) * sum_k A_ki A_kj`; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
@[simp]
theorem sampleCovarianceEntry_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (i j : Fin n) (omega : Omega) :
    sampleCovarianceEntry A i j omega =
      (1 / (m : Real)) * Finset.univ.sum
        (fun k : Fin m => A omega k i * A omega k j) :=
  rfl

/--
Formula reference: this unfolds the matrix-valued sample covariance to the
entry formula `(1 / m) * sum_k A_ki * A_kj`; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
@[simp]
theorem sampleCovariance_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (omega : Omega) (i j : Fin n) :
    sampleCovariance A omega i j = sampleCovarianceEntry A i j omega :=
  rfl

/--
Gram-matrix entries of an `IsRandomMatrix` are real random variables.

Formula reference: measurability follows because each Gram entry is the finite
sum `sum_k A_ki * A_kj` of products of measurable entries; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
theorem isRealRandomVariable_gramMatrixEntry {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IsRandomMatrix P A) (i j : Fin n) :
    IsRealRandomVariable P (gramMatrixEntry A i j) := by
  dsimp [IsRealRandomVariable, IsRandomVariable, gramMatrixEntry]
  exact Finset.measurable_sum _ fun k _ => (hA k i).mul (hA k j)

/--
Row-Gram entries of an `IsRandomMatrix` are real random variables.

Formula reference: measurability follows because each row-Gram entry is the
finite sum `sum_k A_ik * A_jk` of products of measurable entries; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
theorem isRealRandomVariable_rowGramMatrixEntry {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IsRandomMatrix P A) (i j : Fin m) :
    IsRealRandomVariable P (rowGramMatrixEntry A i j) := by
  dsimp [IsRealRandomVariable, IsRandomVariable, rowGramMatrixEntry]
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul (hA j k)

/--
Sample covariance entries of an `IsRandomMatrix` are real random variables.

Formula reference: measurability follows by multiplying the measurable Gram
entry `sum_k A_ki * A_kj` by the deterministic factor `1 / m`; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
theorem isRealRandomVariable_sampleCovarianceEntry {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IsRandomMatrix P A) (i j : Fin n) :
    IsRealRandomVariable P (sampleCovarianceEntry A i j) := by
  dsimp [IsRealRandomVariable, IsRandomVariable, sampleCovarianceEntry]
  exact (isRealRandomVariable_gramMatrixEntry hA i j).const_mul (1 / (m : Real))

/--
Diagonal entries of the uncentered sample covariance are nonnegative.

Formula reference: the diagonal entry is
`(1 / m) * sum_k (A_ki)^2`, a nonnegative normalized sum of squares; see
https://en.wikipedia.org/wiki/Sample_mean_and_covariance
-/
theorem sampleCovarianceEntry_diag_nonneg {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : RandomMatrix Omega m n) (i : Fin n) (omega : Omega) :
    0 <= sampleCovarianceEntry A i i omega := by
  dsimp [sampleCovarianceEntry, gramMatrixEntry]
  exact mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg m))
    (Finset.sum_nonneg fun k _ => by
      simpa [pow_two] using sq_nonneg (A omega k i))

end

end HighDimProb
