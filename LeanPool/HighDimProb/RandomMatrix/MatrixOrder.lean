/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import Mathlib.Analysis.Matrix.Order
import LeanPool.HighDimProb.RandomMatrix.Algebra
import LeanPool.HighDimProb.RandomMatrix.SelfAdjoint

/-!
# Explicit matrix PSD and Loewner-style vocabulary

Verified Wikipedia references:
* Loewner order: https://en.wikipedia.org/wiki/Loewner_order
* Definite matrix: https://en.wikipedia.org/wiki/Definite_matrix
* Quadratic form: https://en.wikipedia.org/wiki/Quadratic_form

This module deliberately does not install a global order instance on matrices.
For the matrix concentration statement layer, `IsPSDMatrix` means symmetric
plus nonnegative quadratic form in the existing HighDimProb double-sum normal
form. `MatrixLE A B` is the corresponding Loewner-style predicate
`IsPSDMatrix (B - A)`.
-/

namespace HighDimProb

open MeasureTheory
open scoped BigOperators MatrixOrder

noncomputable section

/-- Deterministic quadratic form `x^T A x` in HighDimProb's double-sum normal form. -/
def matrixQuadraticForm {n : Nat} (A : Matrix (Fin n) (Fin n) Real)
    (x : Fin n -> Real) : Real :=
  Finset.univ.sum fun i : Fin n =>
    Finset.univ.sum fun j : Fin n => x i * A i j * x j

@[simp]
theorem matrixQuadraticForm_apply {n : Nat} (A : Matrix (Fin n) (Fin n) Real)
    (x : Fin n -> Real) :
    matrixQuadraticForm A x =
      Finset.univ.sum fun i : Fin n =>
        Finset.univ.sum fun j : Fin n => x i * A i j * x j :=
  rfl

/-- PSD predicate used by the current matrix concentration scaffolding:
symmetric plus nonnegative quadratic form. -/
def IsPSDMatrix {n : Nat} (A : Matrix (Fin n) (Fin n) Real) : Prop :=
  IsSymmetricMatrix A /\ forall x : Fin n -> Real, 0 <= matrixQuadraticForm A x

/-- HighDimProb's explicit real PSD predicate implies Mathlib's
`Matrix.PosSemidef` predicate. -/
theorem posSemidef_of_isPSDMatrix {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsPSDMatrix A) :
    A.PosSemidef := by
  classical
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa using isSymmetricMatrix_apply hA.1 i j
  · intro x
    have hquad := hA.2 (fun i : Fin n => x i)
    simpa [matrixQuadraticForm, Finsupp.sum_fintype] using hquad

/-- Pointwise PSD random square matrix. -/
def RandomPSDMatrix {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (P : Measure Omega) (A : RandomMatrix Omega n n) : Prop :=
  let _ := P
  forall omega, IsPSDMatrix (A omega)

/--
Rank-one self outer products are PSD in the explicit quadratic-form order.

Formula reference: for a real vector `x`, the quadratic form of `x x^T` at
`y` is `(y^T x)^2`, hence nonnegative; see
https://en.wikipedia.org/wiki/Outer_product and
https://en.wikipedia.org/wiki/Definite_matrix .
-/
theorem isPSDMatrix_rankOneMatrix {n : Nat} (x : Fin n -> Real) :
    IsPSDMatrix (rankOneMatrix x) := by
  refine ⟨?_, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    simp [rankOneMatrix, mul_comm]
  · intro y
    have hquad :
        matrixQuadraticForm (rankOneMatrix x) y =
          (Finset.univ.sum fun i : Fin n => y i * x i) ^ 2 := by
      simp only [matrixQuadraticForm_apply, rankOneMatrix_apply]
      rw [sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hquad]
    exact sq_nonneg _

/-- The rank-one random matrix associated to a real random vector is pointwise PSD. -/
theorem randomPSDMatrix_rankOneRandomMatrix {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (X : RandomVector Omega n) :
    RandomPSDMatrix P (rankOneRandomMatrix X) := by
  intro omega
  exact isPSDMatrix_rankOneMatrix (X omega)

/-- Loewner-style comparison without declaring a global matrix order instance. -/
def MatrixLE {n : Nat} (A B : Matrix (Fin n) (Fin n) Real) : Prop :=
  IsPSDMatrix (B - A)

/-- HighDimProb's explicit PSD predicate gives nonnegativity in Mathlib's
scoped matrix Loewner order. -/
theorem matrix_nonneg_of_isPSDMatrix {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsPSDMatrix A) :
    (0 : Matrix (Fin n) (Fin n) Real) <= A :=
  Matrix.PosSemidef.nonneg (posSemidef_of_isPSDMatrix hA)

/-- HighDimProb's explicit `MatrixLE` predicate gives Mathlib's scoped matrix
Loewner order. -/
theorem matrix_le_of_matrixLE {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Real} (hAB : MatrixLE A B) :
    A <= B := by
  rw [Matrix.le_iff]
  exact posSemidef_of_isPSDMatrix hAB

theorem matrixQuadraticForm_sub {n : Nat}
    (B A : Matrix (Fin n) (Fin n) Real) (x : Fin n -> Real) :
    matrixQuadraticForm (B - A) x =
      matrixQuadraticForm B x - matrixQuadraticForm A x := by
  simp only [matrixQuadraticForm_apply, Matrix.sub_apply]
  rw [<- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [<- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem isPSDMatrix_quadraticForm_nonneg {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsPSDMatrix A)
    (x : Fin n -> Real) :
    0 <= matrixQuadraticForm A x :=
  hA.2 x

/-- Quadratic forms distribute over finite sums of deterministic matrices. -/
theorem matrixQuadraticForm_sum {I : Type*} [Fintype I] {n : Nat}
    (A : I -> Matrix (Fin n) (Fin n) Real) (x : Fin n -> Real) :
    matrixQuadraticForm (Finset.univ.sum fun i : I => A i) x =
      Finset.univ.sum fun i : I => matrixQuadraticForm (A i) x := by
  calc
    matrixQuadraticForm (Finset.univ.sum fun i : I => A i) x
        = Finset.univ.sum fun r : Fin n =>
            Finset.univ.sum fun c : Fin n =>
              x r * (Finset.univ.sum fun i : I => A i r c) * x c := by
          simp [matrixQuadraticForm, Matrix.sum_apply]
    _ = Finset.univ.sum fun r : Fin n =>
          Finset.univ.sum fun c : Fin n =>
            Finset.univ.sum fun i : I => x r * A i r c * x c := by
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.mul_sum, Finset.sum_mul]
    _ = Finset.univ.sum fun i : I =>
          Finset.univ.sum fun r : Fin n =>
            Finset.univ.sum fun c : Fin n => x r * A i r c * x c := by
          calc
            (Finset.univ.sum fun r : Fin n =>
              Finset.univ.sum fun c : Fin n =>
                Finset.univ.sum fun i : I => x r * A i r c * x c)
                = Finset.univ.sum fun r : Fin n =>
                    Finset.univ.sum fun i : I =>
                      Finset.univ.sum fun c : Fin n => x r * A i r c * x c := by
                  apply Finset.sum_congr rfl
                  intro r _
                  rw [Finset.sum_comm]
            _ = Finset.univ.sum fun i : I =>
                  Finset.univ.sum fun r : Fin n =>
                    Finset.univ.sum fun c : Fin n => x r * A i r c * x c := by
                  rw [Finset.sum_comm]
    _ = Finset.univ.sum fun i : I => matrixQuadraticForm (A i) x := by
          simp [matrixQuadraticForm]

/-- Finite sums of PSD matrices are PSD in the explicit quadratic-form order. -/
theorem isPSDMatrix_sum {I : Type*} [Fintype I] {n : Nat}
    {A : I -> Matrix (Fin n) (Fin n) Real}
    (hA : forall i, IsPSDMatrix (A i)) :
    IsPSDMatrix (Finset.univ.sum fun i : I => A i) := by
  refine ⟨?_, ?_⟩
  · apply Matrix.IsSymm.ext
    intro r c
    calc
      (Finset.univ.sum fun i : I => A i) c r
          = Finset.univ.sum fun i : I => A i c r := by
            rw [Matrix.sum_apply]
      _ = Finset.univ.sum fun i : I => A i r c := by
            apply Finset.sum_congr rfl
            intro i _
            exact isSymmetricMatrix_apply (hA i).1 r c
      _ = (Finset.univ.sum fun i : I => A i) r c := by
            rw [Matrix.sum_apply]
  · intro x
    rw [matrixQuadraticForm_sum]
    exact Finset.sum_nonneg fun i _ => (hA i).2 x

/-- Quadratic forms distribute over deterministic matrix addition. -/
theorem matrixQuadraticForm_add {n : Nat}
    (A B : Matrix (Fin n) (Fin n) Real) (x : Fin n -> Real) :
    matrixQuadraticForm (A + B) x =
      matrixQuadraticForm A x + matrixQuadraticForm B x := by
  simp only [matrixQuadraticForm_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Quadratic forms commute with scalar multiplication of deterministic matrices. -/
theorem matrixQuadraticForm_smul {n : Nat}
    (c : Real) (A : Matrix (Fin n) (Fin n) Real) (x : Fin n -> Real) :
    matrixQuadraticForm (c • A) x =
      c * matrixQuadraticForm A x := by
  simp only [matrixQuadraticForm_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The zero matrix is PSD in the explicit quadratic-form order. -/
theorem isPSDMatrix_zero {n : Nat} :
    IsPSDMatrix (0 : Matrix (Fin n) (Fin n) Real) := by
  refine ⟨?_, ?_⟩
  · apply Matrix.IsSymm.ext
    intro r c
    simp
  · intro x
    simp [matrixQuadraticForm]

/-- The sum of two PSD matrices is PSD. -/
theorem isPSDMatrix_add {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Real}
    (hA : IsPSDMatrix A) (hB : IsPSDMatrix B) :
    IsPSDMatrix (A + B) := by
  refine ⟨?_, ?_⟩
  · apply Matrix.IsSymm.ext
    intro r c
    simp [Matrix.add_apply, isSymmetricMatrix_apply hA.1 r c,
      isSymmetricMatrix_apply hB.1 r c]
  · intro x
    rw [matrixQuadraticForm_add]
    exact add_nonneg (hA.2 x) (hB.2 x)

/-- Nonnegative scalar multiples of PSD matrices are PSD. -/
theorem isPSDMatrix_smul_of_nonneg {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} {c : Real}
    (hc : 0 <= c) (hA : IsPSDMatrix A) :
    IsPSDMatrix (c • A) := by
  refine ⟨?_, ?_⟩
  · apply Matrix.IsSymm.ext
    intro r c'
    simp [Matrix.smul_apply, isSymmetricMatrix_apply hA.1 r c']
  · intro x
    rw [matrixQuadraticForm_smul]
    exact mul_nonneg hc (hA.2 x)

/-- Reflexivity of the explicit Loewner-style matrix comparison. -/
theorem matrixLE_refl {n : Nat} (A : Matrix (Fin n) (Fin n) Real) :
    MatrixLE A A := by
  unfold MatrixLE
  have hEq : A - A = (0 : Matrix (Fin n) (Fin n) Real) := by
    ext r c
    simp [Matrix.sub_apply]
  rw [hEq]
  exact isPSDMatrix_zero

/-- Equality gives the explicit Loewner-style matrix comparison. -/
theorem matrixLE_of_eq {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Real} (h : A = B) :
    MatrixLE A B := by
  subst h
  exact matrixLE_refl A

/-- Subtracting a PSD matrix lowers a matrix in the explicit Loewner-style
order. -/
theorem matrixLE_sub_right_of_isPSD {n : Nat}
    (A C : Matrix (Fin n) (Fin n) Real) (hC : IsPSDMatrix C) :
    MatrixLE (A - C) A := by
  unfold MatrixLE
  have hEq : A - (A - C) = C := by
    ext r c
    simp [Matrix.sub_apply]
  simpa [hEq] using hC

/-- Transitivity of the explicit Loewner-style matrix comparison. -/
theorem matrixLE_trans {n : Nat}
    {A B C : Matrix (Fin n) (Fin n) Real}
    (hAB : MatrixLE A B) (hBC : MatrixLE B C) :
    MatrixLE A C := by
  unfold MatrixLE at *
  have hsum : IsPSDMatrix ((B - A) + (C - B)) :=
    isPSDMatrix_add hAB hBC
  have hEq : C - A = (B - A) + (C - B) := by
    ext r c
    simp [Matrix.sub_apply, Matrix.add_apply]
  rw [hEq]
  exact hsum

/-- Addition preserves the explicit Loewner-style matrix comparison. -/
theorem matrixLE_add {n : Nat}
    {A B C D : Matrix (Fin n) (Fin n) Real}
    (hAB : MatrixLE A B) (hCD : MatrixLE C D) :
    MatrixLE (A + C) (B + D) := by
  unfold MatrixLE at *
  have hsum : IsPSDMatrix ((B - A) + (D - C)) :=
    isPSDMatrix_add hAB hCD
  have hEq : (B + D) - (A + C) = (B - A) + (D - C) := by
    ext r c
    simp [Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [hEq]
  exact hsum

/-- Finite sums preserve the explicit Loewner-style matrix comparison. -/
theorem matrixLE_sum {I : Type*} [Fintype I] {n : Nat}
    {A B : I -> Matrix (Fin n) (Fin n) Real}
    (hAB : forall i, MatrixLE (A i) (B i)) :
    MatrixLE (Finset.univ.sum fun i : I => A i)
      (Finset.univ.sum fun i : I => B i) := by
  unfold MatrixLE at *
  have hsum : IsPSDMatrix (Finset.univ.sum fun i : I => B i - A i) :=
    isPSDMatrix_sum hAB
  have hEq :
      (Finset.univ.sum fun i : I => B i) -
          (Finset.univ.sum fun i : I => A i) =
        Finset.univ.sum fun i : I => B i - A i := by
    ext r c
    simp [Matrix.sub_apply, Matrix.sum_apply, Finset.sum_sub_distrib]
  rw [hEq]
  exact hsum

/-- Adding the same matrix on the left preserves `MatrixLE`. -/
theorem matrixLE_add_left {n : Nat}
    (C : Matrix (Fin n) (Fin n) Real)
    {A B : Matrix (Fin n) (Fin n) Real}
    (hAB : MatrixLE A B) :
    MatrixLE (C + A) (C + B) :=
  matrixLE_add (matrixLE_refl C) hAB

/-- Adding the same matrix on the right preserves `MatrixLE`. -/
theorem matrixLE_add_right {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Real}
    (C : Matrix (Fin n) (Fin n) Real)
    (hAB : MatrixLE A B) :
    MatrixLE (A + C) (B + C) :=
  matrixLE_add hAB (matrixLE_refl C)

/-- Nonnegative scalar multiplication preserves `MatrixLE`. -/
theorem matrixLE_smul_of_nonneg {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Real} {c : Real}
    (hc : 0 <= c) (hAB : MatrixLE A B) :
    MatrixLE (c • A) (c • B) := by
  unfold MatrixLE at *
  have hsmul : IsPSDMatrix (c • (B - A)) :=
    isPSDMatrix_smul_of_nonneg hc hAB
  have hEq : c • B - c • A = c • (B - A) := by
    ext r c'
    simp [Matrix.sub_apply, Matrix.smul_apply]
    ring
  rw [hEq]
  exact hsmul

/-- Loewner-style matrix comparison implies quadratic-form comparison. -/
theorem quadraticForm_le_of_matrixLE {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Real} (hAB : MatrixLE A B)
    (x : Fin n -> Real) :
    matrixQuadraticForm A x <= matrixQuadraticForm B x := by
  have hnonneg := isPSDMatrix_quadraticForm_nonneg hAB x
  rw [matrixQuadraticForm_sub] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Pointwise random-matrix version of `quadraticForm_le_of_matrixLE`. -/
theorem quadraticForm_apply_le_of_matrixLE {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} {A B : RandomMatrix Omega n n}
    (hAB : forall omega, MatrixLE (A omega) (B omega))
    (x : Fin n -> Real) (omega : Omega) :
    quadraticForm A x omega <= quadraticForm B x omega := by
  simpa [quadraticForm, matrixQuadraticForm] using
    quadraticForm_le_of_matrixLE (hAB omega) x

theorem randomPSDMatrix_apply {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} {A : RandomMatrix Omega n n}
    (hA : RandomPSDMatrix P A) (omega : Omega) :
    IsPSDMatrix (A omega) :=
  hA omega

/-- The uncentered sample covariance matrix is symmetric pointwise. -/
theorem isSymmetricMatrix_sampleCovariance {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : RandomMatrix Omega m n) (omega : Omega) :
    IsSymmetricMatrix (sampleCovariance A omega) := by
  apply Matrix.IsSymm.ext
  intro i j
  dsimp [sampleCovariance, sampleCovarianceEntry, gramMatrixEntry]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The uncentered sample covariance matrix is PSD pointwise. -/
theorem isPSD_sampleCovariance {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : RandomMatrix Omega m n) (omega : Omega) :
    IsPSDMatrix (sampleCovariance A omega) := by
  exact And.intro (isSymmetricMatrix_sampleCovariance A omega) (by
    intro x
    simpa [matrixQuadraticForm, quadraticForm] using
      quadraticForm_sampleCovariance_nonneg A x omega)

/-- The sample covariance random matrix is pointwise PSD. -/
theorem randomPSDMatrix_sampleCovariance {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} (A : RandomMatrix Omega m n) :
    RandomPSDMatrix P (sampleCovariance A) := by
  intro omega
  exact isPSD_sampleCovariance A omega

end

end HighDimProb
