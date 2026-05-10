/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF

import Mathlib.Data.Real.Basic

open Finset Real

namespace Matrix

variable {m n β : Type*} [Fintype m]

omit [Fintype m] in
lemma mul_diagonal_mulVec
  [DecidableEq n] [Fintype n] (d : n → ℝ) (x : n → ℝ) (A : Matrix m n ℝ) :
  (A * Matrix.diagonal d) *ᵥ x = ∑ i, d i • x i • A.col i := by
  ext j
  simp only [mulVec, dotProduct, mul_diagonal, sum_apply, Pi.smul_apply, col_apply, smul_eq_mul]
  apply sum_congr rfl
  intro i hi
  ring_nf

omit [Fintype m] in
lemma mulVec_apply [Fintype n]
  (A : Matrix m n ℝ) (x : n → ℝ) (j : m) :
  (A *ᵥ x) j = ∑ i, A j i * x i := by
  simp [mulVec, dotProduct]

section square

variable {A : Matrix m m ℝ}

lemma dotProduct_transpose_mulVec (x y : m → ℝ) :
   x ⬝ᵥ Aᵀ *ᵥ y = y ⬝ᵥ A *ᵥ x := by
  nth_rw 1 [dotProduct_mulVec]
  rw [dotProduct_comm]
  rw [vecMul_transpose]

lemma vecMul_diagonal_dotProduct
  [DecidableEq m] (d x y : m → ℝ) :
  x ᵥ* Matrix.diagonal d ⬝ᵥ y = ∑ i, d i * x i * y i := by
  simp only [dotProduct, vecMul, diagonal, of_apply, mul_ite, mul_zero, sum_ite_eq', mem_univ,
    ↓reduceIte]
  apply sum_congr rfl
  ring_nf
  simp

end square

end Matrix
