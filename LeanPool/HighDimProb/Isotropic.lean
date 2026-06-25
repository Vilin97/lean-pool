/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Covariance

/-!
# Isotropic random vectors

Verified Wikipedia reference:
https://en.wikipedia.org/wiki/Isotropic_position

Note: wiki.md listed `https://en.wikipedia.org/wiki/Isotropic_vector`, but the
verified probability/random-vector page is `Isotropic_position`.
-/

namespace HighDimProb

open MeasureTheory
open scoped BigOperators

noncomputable section

/--
Entrywise second-moment isotropicity: `E[X_i X_j]` is the identity matrix.

Formula reference: this is the coordinate statement
`E[X_i X_j] = delta_ij`, equivalent to the matrix identity
`E[X X^T] = I` for an isotropic-position distribution; see
https://en.wikipedia.org/wiki/Isotropic_position
-/
def IsotropicSecondMoment {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) : Prop :=
  ∀ i j : Fin n, secondMomentMatrixEntry P X i j = if i = j then 1 else 0

/--
Matrix-form second-moment isotropicity. The entrywise predicate is the primary API.

Formula reference: this is the compact matrix form `E[X X^T] = I`, where the
identity matrix has entries `delta_ij`; see
https://en.wikipedia.org/wiki/Isotropic_position
-/
def IsotropicSecondMomentMatrix {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) : Prop :=
  secondMomentMatrix P X = 1

/--
Covariance-form isotropicity: centered coordinates and identity covariance matrix.

Formula reference: after adding the centeredness condition `E[X_i] = 0`, this
uses the covariance form `Cov(X_i, X_j) = delta_ij`, i.e. covariance matrix
`I`; see https://en.wikipedia.org/wiki/Isotropic_position
-/
def IsotropicCovariance {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) : Prop :=
  CenteredVector P X ∧
    ∀ i j : Fin n,
      covarianceMatrixEntry P X i j = if i = j then 1 else 0

/--
Marginal-form isotropicity: every linear marginal has second moment
`sum_i a_i^2`.

Formula reference: this is the one-dimensional marginal form
`E[(sum_i a_i X_i)^2] = sum_i a_i^2`, equivalent to `E[X X^T] = I`; see
https://en.wikipedia.org/wiki/Isotropic_position
-/
def IsotropicMarginal {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) : Prop :=
  ∀ a : Fin n → ℝ,
    secondMoment P (linearForm X a) (linearForm X a) = ∑ i, a i ^ 2

/-- Compatibility alias for the older scaffold name. Prefer `IsotropicCovariance`. -/
abbrev IsIsotropic {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) : Prop :=
  IsotropicCovariance P X

theorem isotropicSecondMoment_iff {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) :
    IsotropicSecondMoment P X ↔
      ∀ i j : Fin n, secondMomentMatrixEntry P X i j = if i = j then 1 else 0 :=
  Iff.rfl

theorem isotropicSecondMomentMatrix_iff {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) :
    IsotropicSecondMomentMatrix P X ↔ secondMomentMatrix P X = 1 :=
  Iff.rfl

theorem isotropicSecondMomentMatrix_iff_isotropicSecondMoment {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω) (X : RandomVector Ω n) :
    IsotropicSecondMomentMatrix P X ↔ IsotropicSecondMoment P X := by
  constructor
  · intro h i j
    have hM : secondMomentMatrix P X = 1 := h
    have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hM
    simpa only [secondMomentMatrix, Matrix.one_apply] using hentry
  · intro h
    change secondMomentMatrix P X = 1
    exact Matrix.ext fun i j => by
      simpa only [secondMomentMatrix, Matrix.one_apply] using h i j

theorem isotropicCovariance_iff {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) :
    IsotropicCovariance P X ↔
      CenteredVector P X ∧
        ∀ i j : Fin n, covarianceMatrixEntry P X i j = if i = j then 1 else 0 :=
  Iff.rfl

/-- Covariance-form isotropicity includes coordinatewise centeredness. -/
theorem IsotropicCovariance.centeredVector {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {P : Measure Ω} {X : RandomVector Ω n} (hX : IsotropicCovariance P X) :
    CenteredVector P X :=
  hX.1

theorem isotropicMarginal_iff {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) :
    IsotropicMarginal P X ↔
      ∀ a : Fin n → ℝ,
        secondMoment P (linearForm X a) (linearForm X a) = ∑ i, a i ^ 2 :=
  Iff.rfl

theorem isIsotropic_iff_isotropicCovariance {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) :
    IsIsotropic P X ↔ IsotropicCovariance P X :=
  Iff.rfl

end

end HighDimProb
