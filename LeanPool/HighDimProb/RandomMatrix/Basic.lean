/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomVector

/-!
# Basic random matrix vocabulary

Verified Wikipedia reference:
* Random matrix: https://en.wikipedia.org/wiki/Random_matrix
-/

namespace HighDimProb

open MeasureTheory

/--
Product measurable-space structure for finite matrices.

Formula reference: a random matrix is a matrix-valued random object; the
product measurable-space instance supplies the measurable side of that
vocabulary. See
https://en.wikipedia.org/wiki/Random_matrix
-/
instance instMeasurableSpaceMatrix {m n alpha : Type*} [MeasurableSpace alpha] :
    MeasurableSpace (Matrix m n alpha) := by
  change MeasurableSpace (m -> n -> alpha)
  infer_instance

/--
An `m x n` real random matrix with concrete finite dimensions.

Formula reference: this is the Lean type for a finite-dimensional random
matrix; see https://en.wikipedia.org/wiki/Random_matrix
-/
abbrev RandomMatrix (Omega : Type*) (m n : Nat) :=
  Omega -> Matrix (Fin m) (Fin n) Real

/--
Entry random variable of a random matrix.

Formula reference: matrix-valued randomness is checked entrywise here; see
https://en.wikipedia.org/wiki/Random_matrix
-/
def matrixEntry {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) (i : Fin m) (j : Fin n) : RealRandomVariable Omega :=
  fun omega => A omega i j

/--
Entrywise measurability predicate for random matrices.

Formula reference: this predicate records that each matrix entry is a real
random variable, matching the entrywise view of a random matrix; see
https://en.wikipedia.org/wiki/Random_matrix
-/
abbrev IsRandomMatrix {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (P : Measure Omega) (A : RandomMatrix Omega m n) : Prop :=
  forall i : Fin m, forall j : Fin n, IsRealRandomVariable P (matrixEntry A i j)

/--
Formula reference: this unfolds the entry random variable `A_ij`; see
https://en.wikipedia.org/wiki/Random_matrix
-/
@[simp]
theorem matrixEntry_apply {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (i : Fin m) (j : Fin n) (omega : Omega) :
    matrixEntry A i j omega = A omega i j :=
  rfl

/--
Pointwise scalar multiple of a random matrix.

This names the object-level adapter so theorem statements can refer to a
scaled random matrix without exposing an anonymous lambda.
-/
def scaledRandomMatrix {Omega : Type*} {m n : Nat}
    (theta : Real) (A : RandomMatrix Omega m n) : RandomMatrix Omega m n :=
  fun omega => SMul.smul theta (A omega)

/--
Indexed family of pointwise scalar multiples of random matrices.

This is the family-level adapter used by trace-MGF and Matrix Bernstein routes
when a finite family is rescaled by a scalar parameter.
-/
def scaledRandomMatrixFamily {Omega : Type*}
    {I : Type*} {m n : Nat} (theta : Real)
    (A : I -> RandomMatrix Omega m n) :
    I -> RandomMatrix Omega m n :=
  fun i => scaledRandomMatrix theta (A i)

/--
Pointwise negation of a random matrix.

This names the object-level negative adapter so public theorem statements can
refer to a negated random matrix without exposing an anonymous lambda.
-/
def negRandomMatrix {Omega : Type*} {m n : Nat}
    (A : RandomMatrix Omega m n) : RandomMatrix Omega m n :=
  fun omega => -(A omega)

@[simp]
theorem scaledRandomMatrix_apply {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (theta : Real) (A : RandomMatrix Omega m n)
    (omega : Omega) :
    scaledRandomMatrix theta A omega = SMul.smul theta (A omega) :=
  rfl

@[simp]
theorem scaledRandomMatrixFamily_apply {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} {m n : Nat} (theta : Real)
    (A : I -> RandomMatrix Omega m n) (i : I) :
    scaledRandomMatrixFamily theta A i = scaledRandomMatrix theta (A i) :=
  rfl

@[simp]
theorem scaledRandomMatrixFamily_apply_apply {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} {m n : Nat} (theta : Real)
    (A : I -> RandomMatrix Omega m n) (i : I) (omega : Omega) :
    scaledRandomMatrixFamily theta A i omega = SMul.smul theta (A i omega) :=
  rfl

@[simp]
theorem negRandomMatrix_apply {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (A : RandomMatrix Omega m n) (omega : Omega) :
    negRandomMatrix A omega = -(A omega) :=
  rfl

/-- Pointwise scalar multiplication preserves entrywise random-matrix
measurability. -/
theorem isRandomMatrix_scaledRandomMatrix {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {m n : Nat}
    {A : RandomMatrix Omega m n} (theta : Real)
    (hA : IsRandomMatrix P A) :
    IsRandomMatrix P (scaledRandomMatrix theta A) := by
  intro i j
  change Measurable (fun omega => theta * A omega i j)
  exact (hA i j).const_mul theta

/-- Pointwise scalar multiplication preserves entrywise random-matrix
measurability for indexed families. -/
theorem isRandomMatrix_scaledRandomMatrixFamily {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {I : Type*} {m n : Nat}
    {A : I -> RandomMatrix Omega m n} (theta : Real)
    (hA : forall i, IsRandomMatrix P (A i)) :
    forall i, IsRandomMatrix P (scaledRandomMatrixFamily theta A i) := by
  intro i
  simpa [scaledRandomMatrixFamily] using
    isRandomMatrix_scaledRandomMatrix (P := P) (A := A i) theta (hA i)

/-- Pointwise negation preserves entrywise random-matrix measurability. -/
theorem isRandomMatrix_negRandomMatrix {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {m n : Nat}
    {A : RandomMatrix Omega m n}
    (hA : IsRandomMatrix P A) :
    IsRandomMatrix P (negRandomMatrix A) := by
  intro i j
  change Measurable (fun omega => -(A omega i j))
  exact (hA i j).neg

/--
Deterministic rank-one self outer-product matrix associated to a vector.

Formula reference: the outer product has entries `x_i * x_j`; see
https://en.wikipedia.org/wiki/Outer_product .
-/
def rankOneMatrix {n : Nat} (x : Fin n -> Real) : Matrix (Fin n) (Fin n) Real :=
  fun i j => x i * x j

/--
Formula reference: this unfolds the rank-one outer-product entry `x_i * x_j`;
see https://en.wikipedia.org/wiki/Outer_product .
-/
@[simp]
theorem rankOneMatrix_apply {n : Nat} (x : Fin n -> Real) (i j : Fin n) :
    rankOneMatrix x i j = x i * x j :=
  rfl

/--
Rank-one self outer-product random matrix associated to a random vector.

Formula reference: the outer product has entries `x_i * x_j`; see
https://en.wikipedia.org/wiki/Outer_product .  This declaration only exposes
the object-level vector-to-matrix map; measurability and integrability remain
separate assumptions/bridges, matching the random-vector convention at
https://en.wikipedia.org/wiki/Random_vector .
-/
def rankOneRandomMatrix {Omega : Type*} {n : Nat}
    (X : RandomVector Omega n) : RandomMatrix Omega n n :=
  fun omega => rankOneMatrix (X omega)

/--
Indexed family of rank-one self outer-product random matrices.

This names the family-level adapter so downstream APIs can refer to the
rank-one matrix family directly.
-/
def rankOneRandomMatrixFamily {Omega : Type*}
    {I : Type*} {n : Nat} (X : I -> RandomVector Omega n) :
    I -> RandomMatrix Omega n n :=
  rankOneRandomMatrix ∘ X

/--
Formula reference: this unfolds the rank-one outer-product entry
`X_i(omega) * X_j(omega)`; see https://en.wikipedia.org/wiki/Outer_product .
-/
@[simp]
theorem rankOneRandomMatrix_apply {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (X : RandomVector Omega n) (omega : Omega) (i j : Fin n) :
    rankOneRandomMatrix X omega i j = X omega i * X omega j :=
  rfl

@[simp]
theorem rankOneRandomMatrixFamily_apply {Omega : Type*}
    [MeasurableSpace Omega] {I : Type*} {n : Nat}
    (X : I -> RandomVector Omega n) (i : I) :
    rankOneRandomMatrixFamily X i = rankOneRandomMatrix (X i) :=
  rfl

/--
Formula reference: the matrix entry of a rank-one outer product is the product
of the corresponding vector coordinates; see
https://en.wikipedia.org/wiki/Outer_product .
-/
@[simp]
theorem matrixEntry_rankOneRandomMatrix {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} (X : RandomVector Omega n) (i j : Fin n) (omega : Omega) :
    matrixEntry (rankOneRandomMatrix X) i j omega = X omega i * X omega j :=
  rfl

/--
Entries of an `IsRandomMatrix` are real random variables.

Formula reference: entrywise random-variable structure is the finite-matrix
specialization of random matrices; see
https://en.wikipedia.org/wiki/Random_matrix
-/
theorem isRealRandomVariable_matrixEntry {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IsRandomMatrix P A) (i : Fin m) (j : Fin n) :
    IsRealRandomVariable P (matrixEntry A i j) :=
  hA i j

/--
Rank-one self outer products of random vectors are random matrices.

Formula reference: each entry is the product `X_i * X_j`; measurability follows
from closure of measurable real functions under multiplication.  See
https://en.wikipedia.org/wiki/Outer_product and
https://en.wikipedia.org/wiki/Measurable_function .
-/
theorem isRandomMatrix_rankOneRandomMatrix {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} {X : RandomVector Omega n}
    (hX : IsRandomVector P X) :
    IsRandomMatrix P (rankOneRandomMatrix X) := by
  intro i j
  dsimp [IsRealRandomVariable, IsRandomVariable, matrixEntry, rankOneRandomMatrix]
  exact (hX i).mul (hX j)

/--
Entrywise measurability gives measurability of the matrix-valued map.

Formula reference: this upgrades entrywise measurable random variables to a
matrix-valued random object; see
https://en.wikipedia.org/wiki/Random_matrix
-/
theorem measurable_randomMatrix_of_isRandomMatrix {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {m n : Nat} {A : RandomMatrix Omega m n}
    (hA : IsRandomMatrix P A) : Measurable A := by
  change Measurable fun omega => fun i : Fin m => fun j : Fin n => A omega i j
  exact measurable_pi_lambda (fun omega i => fun j : Fin n => A omega i j) fun i =>
    measurable_pi_lambda (fun omega j => A omega i j) fun j => hA i j

/-- Entrywise measurability in a smaller measurable space gives ambient
random-matrix measurability when the smaller space is below the ambient one. -/
theorem isRandomMatrix_of_sub_measurable_entries {Omega : Type*}
    [mOmega : MeasurableSpace Omega] {P : Measure Omega} {m n : Nat}
    {A : RandomMatrix Omega m n} (mSub : MeasurableSpace Omega)
    (hSub : mSub <= mOmega)
    (hA :
      forall i j,
        @Measurable Omega Real mSub inferInstance
          (fun omega => A omega i j)) :
    @IsRandomMatrix Omega mOmega m n P A := by
  intro i j
  change @Measurable Omega Real mOmega inferInstance (fun omega => A omega i j)
  exact (hA i j).mono hSub le_rfl

end HighDimProb
