/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# General linear group characteristic polynomial helpers

This file restores a similarity invariance lemma for matrix characteristic polynomials.
-/

variable {F : Type*} [Field F]

open Matrix Polynomial in
lemma Matrix.charpoly.similar_eq (n : ℕ) (u : (Matrix (Fin n) (Fin n) F)ˣ)
    (A B : Matrix (Fin n) (Fin n) F) (h : A = u * B * u⁻¹) :
    A.charpoly = B.charpoly := by
  have h2 : A.charmatrix = C.mapMatrix u.1 * B.charmatrix * C.mapMatrix u.1⁻¹ := by
    simp only [charmatrix, h, coe_units_inv, RingHom.mapMatrix_apply, Matrix.map_mul, mul_sub,
      sub_mul]
    simp [(by aesop : u.1.map C * (diagonal fun x ↦ X) = (diagonal fun x ↦ X) * u.1.map C),
      mul_assoc]
  rw [charpoly, charpoly, h2, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul]
  simp
