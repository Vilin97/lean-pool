/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import LeanPool.Monlib4.Preq.Ites

/-!
 # Conjugate of a matrix

This file defines the conjugate of a matrix, `matrix.conj` with the notation `ᴴᵀ`
(i.e., `xᴴᵀ i j = star (x i j)`), and shows basic properties about it.
-/


namespace Matrix

open scoped Matrix

variable {α n₁ n₂ : Type _}

/--
conjugate of matrix defined as $\bar{x} := {(x^*)}^\top$, i.e., $\bar{x}_{ij}=\overline{x_{ij}}$ -/
def conj [Star α] (x : Matrix n₁ n₂ α) : Matrix n₁ n₂ α :=
  xᴴᵀ

/-- Postfix notation `ᴴᵀ` for `Matrix.conj`. -/
scoped postfix:1024 "ᴴᵀ" => Matrix.conj

theorem conj_apply [Star α] (x : Matrix n₁ n₂ α) (i : n₁) (j : n₂) : xᴴᵀ i j = star (x i j) :=
  rfl

theorem conj_conj [InvolutiveStar α] (x : Matrix n₁ n₂ α) : xᴴᵀᴴᵀ = x :=
  calc
    xᴴᵀᴴᵀ = xᵀᵀᴴᴴ := rfl
    _ = xᵀᵀ := (conjTranspose_conjTranspose _)
    _ = x := transpose_transpose _

theorem conj_add [AddMonoid α] [StarAddMonoid α] (x y : Matrix n₁ n₂ α) : (x + y)ᴴᵀ = xᴴᵀ + yᴴᵀ :=
  by simp_rw [conj, ← transpose_add, ← conjTranspose_add]

theorem conj_smul {R : Type _} [Star R] [Star α] [SMul R α] [StarModule R α] (c : R)
    (x : Matrix n₁ n₂ α) : (c • x)ᴴᵀ = star c • xᴴᵀ := by
  simp_rw [conj, ← transpose_smul, ← conjTranspose_smul]

theorem conj_conjTranspose [InvolutiveStar α] (x : Matrix n₁ n₂ α) : xᴴᵀᴴ = xᵀ :=
  calc
    xᴴᵀᴴ = xᵀᴴᴴ := rfl
    _ = xᵀ := conjTranspose_conjTranspose _

theorem conjTranspose_conj [InvolutiveStar α] (x : Matrix n₁ n₂ α) : xᴴᴴᵀ = xᵀ :=
  calc
    xᴴᴴᵀ = xᴴᵀᴴ := rfl
    _ = xᵀ := conj_conjTranspose _

theorem transpose_conj_eq_conjTranspose [Star α] (x : Matrix n₁ n₂ α) : xᴴᵀᵀ = xᴴ :=
  rfl

namespace IsHermitian

theorem conj {α n : Type _} [Star α] {x : Matrix n n α} (hx : x.IsHermitian) :
    xᴴᵀ = xᵀ := by simp_rw [Matrix.conj, hx.eq]

end IsHermitian

theorem conj_mul {α m n p : Type _} [Fintype n] [CommSemiring α] [StarRing α] (x : Matrix m n α)
    (y : Matrix n p α) : (x * y)ᴴᵀ = xᴴᵀ * yᴴᵀ :=
  by
  ext
  simp_rw [conj_apply, mul_apply, star_sum, StarMul.star_mul, conj_apply, mul_comm]

theorem conj_one {α n : Type _} [DecidableEq n] [Semiring α] [StarRing α] :
    (1 : Matrix n n α)ᴴᵀ = 1 := by
  ext
  simp_rw [conj_apply, one_apply, star_ite, star_one, star_zero]

theorem conj_zero {α n₁ n₂ : Type _} [AddMonoid α] [StarAddMonoid α] :
  (0 : Matrix n₁ n₂ α)ᴴᵀ = 0 := by
  ext
  simp_rw [conj_apply, zero_apply, star_zero]

end Matrix
