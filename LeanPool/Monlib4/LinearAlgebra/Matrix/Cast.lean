/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Data.Matrix.Basic

/-!
# LeanPool.Monlib4.LinearAlgebra.Matrix.Cast

Imported Lean Pool material for `LeanPool.Monlib4.LinearAlgebra.Matrix.Cast`.
-/

variable {R k : Type*} {s : k → Type _}

theorem Matrix.cast_apply {i j : k} (x : Matrix (s i) (s i) R) (h : i = j) (p q : s j) :
  (by rw [h] : Matrix (s i) (s i) R = Matrix (s j) (s j) R).mp x p q =
    x (by rw [h]; exact p) (by rw [h]; exact q) :=
by aesop
theorem Matrix.cast_apply' {i j : k} (x : Matrix (s j) (s j) R) (h : j = i) (p q : s i) :
  (by rw [h] : Matrix (s i) (s i) R = Matrix (s j) (s j) R).mpr x p q =
    x (by rw [h]; exact p) (by rw [h]; exact q) :=
by aesop

theorem Matrix.cast_hMul [Semiring R] [Π i, Fintype (s i)]
  {i j : k} (x y : Matrix (s i) (s i) R) (h : i = j) :
  (by rw [h] : Matrix (s i) (s i) R = Matrix (s j) (s j) R).mp (x * y) =
    (by rw [h] : Matrix (s i) (s i) R = Matrix (s j) (s j) R).mp x *
      (by rw [h] : Matrix (s i) (s i) R = Matrix (s j) (s j) R).mp y :=
by aesop
