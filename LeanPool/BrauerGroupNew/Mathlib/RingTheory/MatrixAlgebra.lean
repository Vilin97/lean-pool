/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import Mathlib.RingTheory.MatrixAlgebra

/-!
# Matrix algebra tensor compatibility

This file restores an upstream matrix/tensor equivalence in the opposite direction.
-/

open scoped TensorProduct

/-- Matrix algebras over `A` as scalar extension from matrices over `R`. -/
def matrixEquivTensor' (n R A : Type*) [CommSemiring R] [CommSemiring A]
    [Algebra R A] [Fintype n] [DecidableEq n] :
    Matrix n n A ≃ₐ[A] A ⊗[R] Matrix n n R :=
  .symm <| .ofRingEquiv (f := (matrixEquivTensor n R A).symm) fun a ↦ by
    ext i j
    simp [matrixEquivTensor, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, Matrix.one_apply]

@[simp] lemma matrixEquivTensor'_symm_apply (n R A : Type*) [CommSemiring R] [CommSemiring A]
    [Algebra R A] [Fintype n] [DecidableEq n] (a : A) (m : Matrix n n R) :
    (matrixEquivTensor' n R A).symm (a ⊗ₜ m) = a • (m.map (algebraMap R A)) := rfl
