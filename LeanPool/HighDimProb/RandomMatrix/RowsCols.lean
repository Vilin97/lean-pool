/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.Basic

/-!
# Rows and columns of random matrices
-/

namespace HighDimProb

open MeasureTheory

/-- Row `i` of a random matrix as a random vector. -/
def rowVector {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) (i : Fin m) : RandomVector Omega n :=
  fun omega j => A omega i j

/-- Column `j` of a random matrix as a random vector. -/
def colVector {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) (j : Fin n) : RandomVector Omega m :=
  fun omega i => A omega i j

@[simp]
theorem rowVector_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (i : Fin m) (omega : Omega) (j : Fin n) :
    rowVector A i omega j = A omega i j :=
  rfl

@[simp]
theorem colVector_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (j : Fin n) (omega : Omega) (i : Fin m) :
    colVector A j omega i = A omega i j :=
  rfl

@[simp]
theorem coord_rowVector {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (i : Fin m) (j : Fin n) :
    coord (rowVector A i) j = matrixEntry A i j :=
  rfl

@[simp]
theorem coord_colVector {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (j : Fin n) (i : Fin m) :
    coord (colVector A j) i = matrixEntry A i j :=
  rfl

/-- Rows of an `IsRandomMatrix` are random vectors. -/
theorem isRandomVector_rowVector {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IsRandomMatrix P A) (i : Fin m) :
    IsRandomVector P (rowVector A i) := by
  intro j
  exact hA i j

/-- Columns of an `IsRandomMatrix` are random vectors. -/
theorem isRandomVector_colVector {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IsRandomMatrix P A) (j : Fin n) :
    IsRandomVector P (colVector A j) := by
  intro i
  exact hA i j

end HighDimProb
