/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import LeanPool.Monlib4.LinearAlgebra.Matrix.Basic
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.FiniteDimensional

/-!
# Kronecker product to the tensor product

This file contains the definition of `tensorToKronecker` and
`kroneckerToTensor`, the algebra equivalences between `⊗ₜ` and `⊗ₖ`.

-/


open scoped TensorProduct BigOperators Kronecker

section

variable {R m n : Type _} [CommSemiring R] [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- Convert a tensor of square matrices into its Kronecker-product matrix. -/
noncomputable def TensorProduct.toKronecker :
    Matrix m m R ⊗[R] Matrix n n R →ₗ[R] Matrix (m × n) (m × n) R :=
  (kroneckerLinearEquiv m m n n R).toLinearMap

theorem TensorProduct.toKronecker_apply (x : Matrix m m R) (y : Matrix n n R) :
    toKronecker (x ⊗ₜ[R] y) = x ⊗ₖ y := by
  exact kroneckerLinearEquiv_tmul x y

/-- Convert a Kronecker-product matrix back to the tensor of matrix algebras. -/
noncomputable def Matrix.kroneckerToTensorProduct :
    Matrix (m × n) (m × n) R →ₗ[R] Matrix m m R ⊗[R] Matrix n n R :=
  (kroneckerLinearEquiv m m n n R).symm.toLinearMap

theorem TensorProduct.toKronecker_to_tensorProduct (x : Matrix m m R ⊗[R] Matrix n n R) :
    Matrix.kroneckerToTensorProduct (toKronecker x) = x := by
  exact (kroneckerLinearEquiv m m n n R).symm_apply_apply x

theorem Matrix.kroneckerToTensorProduct_apply (x : Matrix m m R) (y : Matrix n n R) :
    kroneckerToTensorProduct (x ⊗ₖ y) = x ⊗ₜ[R] y := by
  exact kroneckerLinearEquiv_symm_kronecker x y

theorem Matrix.kroneckerToTensorProduct_toKronecker (x : Matrix (m × n) (m × n) R) :
    TensorProduct.toKronecker (kroneckerToTensorProduct x) = x := by
  exact (kroneckerLinearEquiv m m n n R).apply_symm_apply x

open scoped Matrix

theorem TensorProduct.matrix_star {R m n : Type _} [Field R] [StarRing R]
    (x : Matrix m m R) (y : Matrix n n R) : star (x ⊗ₜ[R] y) = xᴴ ⊗ₜ yᴴ :=
  TensorProduct.star_tmul _ _

theorem TensorProduct.toKronecker_star {R m n : Type _} [Field R] [StarRing R]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (x : Matrix m m R ⊗[R] Matrix n n R) :
    star (toKronecker x) = toKronecker (star x) := by
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset x
  simp only [map_sum, star_sum,
    TensorProduct.matrix_star, TensorProduct.toKronecker_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_kronecker]

open Matrix

theorem Matrix.kronecker_eq_sum_std_basis (x : Matrix (m × n) (m × n) R) :
    x = ∑ i, ∑ j, ∑ k, ∑ l, x (i, k) (j, l) • single i j 1 ⊗ₖ single k l 1 := by
  ext a b
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  simp [Matrix.sum_apply, Matrix.kroneckerMap, Matrix.of_apply,
    Matrix.single, mul_ite, mul_one, mul_zero, ite_and, eq_comm]

theorem TensorProduct.matrix_eq_sum_std_basis (x : Matrix m m R ⊗[R] Matrix n n R) :
    x =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (toKronecker x) (i, k) (j, l) • single i j 1 ⊗ₜ single k l 1 := by
  rw [eq_comm]
  calc
    ∑ i, ∑ j, ∑ k, ∑ l,
          (toKronecker x) (i, k) (j, l) •
            single i j (1 : R) ⊗ₜ single k l (1 : R) =
        ∑ i, ∑ j, ∑ k, ∑ l,
          (toKronecker x) (i, k) (j, l) •
            kroneckerToTensorProduct (toKronecker (single i j (1 : R) ⊗ₜ
                  single k l (1 : R))) :=
      by simp_rw [TensorProduct.toKronecker_to_tensorProduct]
    _ =
        ∑ i, ∑ j, ∑ k, ∑ l,
          toKronecker x (i, k) (j, l) •
            kroneckerToTensorProduct (single i j (1 : R) ⊗ₖ
                single k l (1 : R)) :=
      by simp_rw [TensorProduct.toKronecker_apply]
    _ =
        kroneckerToTensorProduct (∑ i, ∑ j, ∑ k, ∑ l,
            toKronecker x (i, k) (j, l) •
              single i j (1 : R) ⊗ₖ
                single k l (1 : R)) :=
      by simp_rw [map_sum, _root_.map_smul]
    _ = kroneckerToTensorProduct (toKronecker x) := by rw [← Matrix.kronecker_eq_sum_std_basis]
    _ = x := TensorProduct.toKronecker_to_tensorProduct _

theorem TensorProduct.toKronecker_hMul (x y : Matrix m m R ⊗[R] Matrix n n R) :
    toKronecker (x * y) = toKronecker x * toKronecker y :=
x.induction_on
 (by simp only [zero_mul, map_zero])
 (y.induction_on
  (by simp only [mul_zero, map_zero, implies_true])
  (fun _ _ _ _ => by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, toKronecker_apply, Matrix.mul_kronecker_mul])
  (fun _ _ h1 h2 _ _ => by simp only [_root_.map_add, h1, h2, mul_add]))
  (fun _ _ h1 h2 => by simp only [_root_.map_add, add_mul, h1, h2])

theorem Matrix.kroneckerToTensorProduct_hMul (x y : Matrix m m R) (z w : Matrix n n R) :
    kroneckerToTensorProduct (x ⊗ₖ z * y ⊗ₖ w) =
      kroneckerToTensorProduct (x ⊗ₖ z) * kroneckerToTensorProduct (y ⊗ₖ w) := by
  simp_rw [← Matrix.mul_kronecker_mul, Matrix.kroneckerToTensorProduct_apply,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- Algebra equivalence from the tensor product of matrix algebras to Kronecker matrices. -/
@[simps!]
noncomputable def tensorToKronecker :
    Matrix m m R ⊗[R] Matrix n n R ≃ₐ[R] Matrix (m × n) (m × n) R :=
  Matrix.kroneckerAlgEquiv m n R

/-- Algebra equivalence from Kronecker matrices to the tensor product of matrix algebras. -/
@[simps!]
noncomputable def kroneckerToTensor :
    Matrix (m × n) (m × n) R ≃ₐ[R] Matrix m m R ⊗[R] Matrix n n R :=
  (Matrix.kroneckerAlgEquiv m n R).symm

theorem Matrix.kroneckerToTensorProduct_star {R m n : Type _} [Field R] [StarRing R]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (x : Matrix (m × n) (m × n) R) :
    star (kroneckerToTensorProduct x) = kroneckerToTensorProduct (star x) := by
  apply_fun TensorProduct.toKronecker using AlgEquiv.injective tensorToKronecker
  simp only [← TensorProduct.toKronecker_star, kroneckerToTensorProduct_toKronecker]

theorem kroneckerToTensor_toLinearMap_eq :
    (kroneckerToTensor : Matrix (n × m) (n × m) R ≃ₐ[R] _).toLinearMap =
      (kroneckerToTensorProduct : Matrix (n × m) (n × m) R →ₗ[R] Matrix n n R ⊗[R] Matrix m m R) :=
  rfl

theorem tensorToKronecker_toLinearMap_eq :
    ((@tensorToKronecker R m n _ _ _ _ _ :
        Matrix m m R ⊗[R] Matrix n n R ≃ₐ[R] _).toLinearMap :
        Matrix m m R ⊗[R] Matrix n n R →ₗ[R] Matrix (m × n) (m × n) R) =
      (TensorProduct.toKronecker : Matrix m m R ⊗[R] Matrix n n R →ₗ[R] Matrix (m × n) (m × n) R) :=
  rfl

end
