/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Scalar.Variance
import LeanPool.HighDimProb.RandomVector

/-!
# Means, centeredness, and covariance

Scalar centering, variance, covariance, and second-moment vocabulary now live in
`HighDimProb.Scalar.Centering` and `HighDimProb.Scalar.Variance`. This module keeps the
vector covariance vocabulary entrywise over the concrete `Fin n → ℝ` random-vector model.

Verified Wikipedia references:
* Covariance: https://en.wikipedia.org/wiki/Covariance
* Expected value: https://en.wikipedia.org/wiki/Expected_value
-/

namespace HighDimProb

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

/--
Mean vector, represented coordinatewise.

Formula reference: vector means are coordinatewise expected values; see
https://en.wikipedia.org/wiki/Expected_value
-/
def meanVector {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) : Fin n → ℝ :=
  fun i => mean P (coord X i)

/-- Centered version of a finite-dimensional random vector. -/
def centeredVector {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) : RandomVector Ω n :=
  fun ω i => X ω i - meanVector P X i

/-- Coordinatewise centered random vector predicate. -/
abbrev CenteredVector {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) : Prop :=
  ∀ i : Fin n, Centered P (coord X i)

theorem centeredVector_iff_forall_centered_coord {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (P : Measure Ω) (X : RandomVector Ω n) :
    CenteredVector P X ↔ ∀ i : Fin n, Centered P (coord X i) :=
  Iff.rfl

/--
Entry of the uncentered second moment matrix `E[X X^T]`.

Formula reference: second-moment matrices use entries `E[X_i X_j]`; see
https://en.wikipedia.org/wiki/Moment_(mathematics)
-/
abbrev secondMomentMatrixEntry {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) (i j : Fin n) : ℝ :=
  secondMoment P (coord X i) (coord X j)

/--
Uncentered second moment matrix `E[X X^T]`, represented entrywise.

Formula reference: this is the matrix form of coordinatewise second moments;
see https://en.wikipedia.org/wiki/Moment_(mathematics)
-/
def secondMomentMatrix {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => secondMomentMatrixEntry P X i j

/--
Entry of the covariance matrix.

Formula reference: covariance matrix entries are `Cov(X_i, X_j)`; see
https://en.wikipedia.org/wiki/Covariance
-/
abbrev covarianceMatrixEntry {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) (i j : Fin n) : ℝ :=
  covariance P (coord X i) (coord X j)

/--
Covariance matrix, represented entrywise.

Formula reference: covariance matrices collect pairwise covariances; see
https://en.wikipedia.org/wiki/Covariance
-/
def covarianceMatrix {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => covarianceMatrixEntry P X i j

@[simp]
theorem meanVector_apply {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) (i : Fin n) :
    meanVector P X i = mean P (coord X i) :=
  rfl

@[simp]
theorem centeredVector_apply {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) (ω : Ω) (i : Fin n) :
    centeredVector P X ω i = X ω i - meanVector P X i :=
  rfl

@[simp]
theorem coord_centeredVector {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) (i : Fin n) :
    coord (centeredVector P X) i = centered P (coord X i) :=
  rfl

@[simp]
theorem secondMomentMatrix_apply {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) (i j : Fin n) :
    secondMomentMatrix P X i j = secondMomentMatrixEntry P X i j :=
  rfl

@[simp]
theorem covarianceMatrix_apply {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) (i j : Fin n) :
    covarianceMatrix P X i j = covarianceMatrixEntry P X i j :=
  rfl

/-- Centering preserves random-vector coordinatewise measurability. -/
theorem isRandomVector_centeredVector {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {X : RandomVector Ω n} (hX : IsRandomVector P X) :
    IsRandomVector P (centeredVector P X) := by
  intro i
  change IsRealRandomVariable P (centered P (coord X i))
  exact isRealRandomVariable_centered (hX i)

end

end HighDimProb
