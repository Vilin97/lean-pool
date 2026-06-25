/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.Basic

/-!
# Norm vocabulary for random matrices

Verified Wikipedia reference:
* Matrix norm: https://en.wikipedia.org/wiki/Matrix_norm
-/

namespace HighDimProb

open MeasureTheory
open scoped BigOperators NNReal

noncomputable section

/--
Squared Frobenius norm random variable, represented entrywise.

Formula reference: the Frobenius norm is a matrix norm obtained from the
square root of the sum of squared entries; see
https://en.wikipedia.org/wiki/Matrix_norm
-/
def frobeniusSq {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) : RealRandomVariable Omega :=
  fun omega => Finset.univ.sum fun i : Fin m =>
    Finset.univ.sum fun j : Fin n => (A omega i j) ^ 2

/--
Frobenius norm random variable.

Formula reference: this is the square root of the squared Frobenius norm,
one of the standard matrix norms; see
https://en.wikipedia.org/wiki/Matrix_norm
-/
def frobeniusNorm {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) : RealRandomVariable Omega :=
  fun omega => Real.sqrt (frobeniusSq A omega)

/--
Entrywise maximum absolute value, using `0` on empty index products.

Formula reference: this is the entrywise max norm vocabulary for finite
matrices, related to matrix-norm conventions; see
https://en.wikipedia.org/wiki/Matrix_norm
-/
def entrywiseMaxAbs {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) : RealRandomVariable Omega :=
  fun omega =>
    ((Finset.univ.product Finset.univ).sup
      (fun ij : Fin m × Fin n => nnnorm (A omega ij.1 ij.2)) : NNReal)

/--
Formula reference: this unfolds the squared Frobenius norm as the sum of
squared matrix entries; see https://en.wikipedia.org/wiki/Matrix_norm
-/
@[simp]
theorem frobeniusSq_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (omega : Omega) :
    frobeniusSq A omega = Finset.univ.sum fun i : Fin m =>
      Finset.univ.sum fun j : Fin n => (A omega i j) ^ 2 :=
  rfl

/--
Formula reference: this unfolds the Frobenius norm as the square root of the
entrywise squared sum; see https://en.wikipedia.org/wiki/Matrix_norm
-/
@[simp]
theorem frobeniusNorm_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (omega : Omega) :
    frobeniusNorm A omega = Real.sqrt (frobeniusSq A omega) :=
  rfl

/--
Formula reference: this unfolds the entrywise maximum absolute value norm
proxy; see https://en.wikipedia.org/wiki/Matrix_norm
-/
@[simp]
theorem entrywiseMaxAbs_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (omega : Omega) :
    entrywiseMaxAbs A omega =
      ((Finset.univ.product Finset.univ).sup
        (fun ij : Fin m × Fin n => nnnorm (A omega ij.1 ij.2)) : NNReal) :=
  rfl

/--
Squared Frobenius norm is nonnegative pointwise.

Formula reference: the squared Frobenius norm is a sum of squares; see
https://en.wikipedia.org/wiki/Matrix_norm
-/
theorem frobeniusSq_nonneg {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (omega : Omega) :
    0 <= frobeniusSq A omega := by
  dsimp [frobeniusSq]
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

/--
Squared Frobenius norm of an `IsRandomMatrix` is a real random variable.

Formula reference: this is the random-variable measurability statement for
the entrywise squared Frobenius norm; see
https://en.wikipedia.org/wiki/Matrix_norm
-/
theorem isRealRandomVariable_frobeniusSq {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IsRandomMatrix P A) :
    IsRealRandomVariable P (frobeniusSq A) := by
  dsimp [IsRealRandomVariable, IsRandomVariable, frobeniusSq]
  exact Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => (hA i j).pow_const 2

/--
Frobenius norm of an `IsRandomMatrix` is a real random variable.

Formula reference: this is the random-variable measurability statement for
the Frobenius norm; see https://en.wikipedia.org/wiki/Matrix_norm
-/
theorem isRealRandomVariable_frobeniusNorm {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IsRandomMatrix P A) :
    IsRealRandomVariable P (frobeniusNorm A) := by
  dsimp [IsRealRandomVariable, IsRandomVariable, frobeniusNorm]
  exact (isRealRandomVariable_frobeniusSq hA).sqrt

end

end HighDimProb
