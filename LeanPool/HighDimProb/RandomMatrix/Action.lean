/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.RowsCols

/-!
# Matrix-vector actions for random matrices

Verified Wikipedia references:
* Random matrix: https://en.wikipedia.org/wiki/Random_matrix
* Matrix multiplication: https://en.wikipedia.org/wiki/Matrix_multiplication
* Multivariate random variable: https://en.wikipedia.org/wiki/Multivariate_random_variable
-/

namespace HighDimProb

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Random vector `omega |-> A(omega) x`, written with an explicit finite sum. -/
def matVec {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) (x : Fin n -> Real) : RandomVector Omega m :=
  fun omega i => Finset.univ.sum fun j : Fin n => A omega i j * x j

/-- Random vector `omega |-> A(omega)^T y`, written with an explicit finite sum. -/
def vecMat {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) (y : Fin m -> Real) : RandomVector Omega n :=
  fun omega j => Finset.univ.sum fun i : Fin m => A omega i j * y i

@[simp]
theorem matVec_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (x : Fin n -> Real) (omega : Omega) (i : Fin m) :
    matVec A x omega i = Finset.univ.sum fun j : Fin n => A omega i j * x j :=
  rfl

@[simp]
theorem vecMat_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (y : Fin m -> Real) (omega : Omega) (j : Fin n) :
    vecMat A y omega j = Finset.univ.sum fun i : Fin m => A omega i j * y i :=
  rfl

/-- Matrix-vector actions of an `IsRandomMatrix` are random vectors. -/
theorem isRandomVector_matVec {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IsRandomMatrix P A) (x : Fin n -> Real) :
    IsRandomVector P (matVec A x) := by
  intro i
  dsimp [IsRealRandomVariable, IsRandomVariable, matVec]
  exact Finset.measurable_sum _ fun j _ => (hA i j).mul_const (x j)

/-- Transposed matrix-vector actions of an `IsRandomMatrix` are random vectors. -/
theorem isRandomVector_vecMat {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IsRandomMatrix P A) (y : Fin m -> Real) :
    IsRandomVector P (vecMat A y) := by
  intro j
  dsimp [IsRealRandomVariable, IsRandomVariable, vecMat]
  exact Finset.measurable_sum _ fun i _ => (hA i j).mul_const (y i)

end

end HighDimProb
