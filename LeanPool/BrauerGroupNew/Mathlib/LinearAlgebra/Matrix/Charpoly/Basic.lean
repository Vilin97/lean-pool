/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Matrix characteristic polynomial helpers

This file restores upstream helper lemmas for block diagonal characteristic polynomials.
-/

variable {F : Type*} [Field F]

/-- A subtype of a product that depends only on the second component. -/
@[simps]
def Equiv.prodSubtypeSndEquivProdSubtype {α β} {p : β → Prop} :
    {s : α × β // p s.2} ≃ α × {b // p b} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The fiber of a product projection over a fixed second coordinate. -/
@[simps!]
def thing' {α β : Type*} (b : β) : {i : α × β // i.2 = b} ≃ α :=
  Equiv.prodSubtypeSndEquivProdSubtype.trans (Equiv.prodUnique α {i : β // i = b})

open Matrix in
theorem Matrix.blockDiagonal_toSquareBlock {r} {n : Type*}
    (A : Fin r → Matrix n n F) {i} :
    (blockDiagonal A).toSquareBlock Prod.snd i = (A i).reindex (thing' _).symm (thing' _).symm := by
  classical
  aesop (add simp toSquareBlock_def)

theorem Matrix.blockDiagonal_charpoly_aux {r} {n : Type*} [DecidableEq n] [Fintype n]
    (A : Fin r → Matrix n n F) {i} :
    ((Matrix.blockDiagonal A).toSquareBlock Prod.snd i).charpoly = (A i).charpoly := by
  rw [blockDiagonal_toSquareBlock, Matrix.charpoly_reindex]

theorem Matrix.blockDiagonal_charpoly {r} {n : Type*} [DecidableEq n] [Fintype n]
    (A : Fin r → Matrix n n F) :
    (Matrix.blockDiagonal A).charpoly = ∏ i : Fin r, (A i).charpoly := by
  have hM := Matrix.blockTriangular_blockDiagonal A
  simp only [Matrix.charpoly, hM.charmatrix.det_fintype, ← Matrix.charmatrix_toSquareBlock]
  congr! with i hi
  exact blockDiagonal_charpoly_aux _

theorem Matrix.blockDiagonal_const_charpoly (r n : ℕ)
    (A : Matrix (Fin n) (Fin n) F) :
    (Matrix.blockDiagonal fun _ : Fin r => A).charpoly = A.charpoly ^ r := by
  rw [blockDiagonal_charpoly]
  simp

lemma Matrix.reindex_diagonal_charpoly (r n m : ℕ) (eq : m = r * n)
    (A : Matrix (Fin n) (Fin n) F) :
    (Matrix.reindexAlgEquiv F F
      (finProdFinEquiv.trans (finCongr (by rw [eq, mul_comm])) : Fin n × Fin r ≃ Fin m)
    ((Matrix.blockDiagonalRingHom (Fin n) (Fin r) F) fun _ ↦ A)).charpoly =
    A.charpoly ^ r := by
  rw [Matrix.blockDiagonalRingHom_apply, Matrix.coe_reindexAlgEquiv,
    Matrix.charpoly_reindex, blockDiagonal_charpoly]
  simp
