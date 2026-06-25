/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Symmetric
import LeanPool.HighDimProb.RandomMatrix.Basic

/-!
# Symmetric and self-adjoint real matrix vocabulary

This file keeps the real square-matrix vocabulary thin. `IsSymmetricMatrix`
wraps Mathlib's transpose equality `Matrix.IsSymm`, while
`IsSelfAdjointMatrix` wraps Mathlib's Hermitian/self-adjoint matrix predicate.
For the current real-valued branch these are kept as separate names so future
complex Hermitian work does not silently change theorem statements.

Verified Wikipedia reference:
* Self-adjoint operator:
  https://en.wikipedia.org/wiki/Self-adjoint_operator
-/

namespace HighDimProb

open MeasureTheory

/--
Real square matrix symmetry, backed by Mathlib `Matrix.IsSymm`.

Formula reference: in finite dimensions, self-adjoint/Hermitian structure is
represented by equality to the adjoint; over real matrices this aligns with
symmetry. See https://en.wikipedia.org/wiki/Self-adjoint_operator
-/
abbrev IsSymmetricMatrix {n : Nat} (A : Matrix (Fin n) (Fin n) Real) : Prop :=
  A.IsSymm

/--
Real square matrix self-adjointness, backed by Mathlib `Matrix.IsHermitian`.

Formula reference: a self-adjoint operator is equal to its adjoint; in finite
matrix form this is the Hermitian condition. See
https://en.wikipedia.org/wiki/Self-adjoint_operator
-/
abbrev IsSelfAdjointMatrix {n : Nat} (A : Matrix (Fin n) (Fin n) Real) : Prop :=
  A.IsHermitian

/-- Pointwise symmetric random square matrix. The measure parameter is present
for consistency with other HighDimProb random-matrix predicates.

Formula reference: pointwise symmetry is the real finite-dimensional analogue
of self-adjointness; see
https://en.wikipedia.org/wiki/Self-adjoint_operator
-/
def RandomSymmetricMatrix {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (P : Measure Omega) (A : RandomMatrix Omega n n) : Prop :=
  let _ := P
  forall omega, IsSymmetricMatrix (A omega)

/-- Pointwise self-adjoint random square matrix. The measure parameter is present
for consistency with other HighDimProb random-matrix predicates.

Formula reference: each sample matrix satisfies the finite-dimensional
self-adjoint/Hermitian condition; see
https://en.wikipedia.org/wiki/Self-adjoint_operator
-/
def RandomSelfAdjointMatrix {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (P : Measure Omega) (A : RandomMatrix Omega n n) : Prop :=
  let _ := P
  forall omega, IsSelfAdjointMatrix (A omega)

/--
Formula reference: symmetry gives the transposed-entry equality for real
finite matrices; see https://en.wikipedia.org/wiki/Self-adjoint_operator
-/
theorem isSymmetricMatrix_apply {n : Nat} {A : Matrix (Fin n) (Fin n) Real}
    (hA : IsSymmetricMatrix A) (i j : Fin n) :
    A j i = A i j :=
  Matrix.IsSymm.apply hA i j

/--
Formula reference: this extracts the pointwise symmetric matrix condition from
the random-matrix predicate; see
https://en.wikipedia.org/wiki/Self-adjoint_operator
-/
theorem randomSymmetricMatrix_apply {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} {A : RandomMatrix Omega n n}
    (hA : RandomSymmetricMatrix P A) (omega : Omega) :
    IsSymmetricMatrix (A omega) :=
  hA omega

/--
Formula reference: this extracts the pointwise self-adjoint matrix condition
from the random-matrix predicate; see
https://en.wikipedia.org/wiki/Self-adjoint_operator
-/
theorem randomSelfAdjointMatrix_apply {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} {A : RandomMatrix Omega n n}
    (hA : RandomSelfAdjointMatrix P A) (omega : Omega) :
    IsSelfAdjointMatrix (A omega) :=
  hA omega

/--
Rank-one self outer products are self-adjoint.

Formula reference: the real outer product `x x^T` is symmetric, hence
self-adjoint in finite dimensions; see https://en.wikipedia.org/wiki/Outer_product
and https://en.wikipedia.org/wiki/Self-adjoint_operator .
-/
theorem isSelfAdjointMatrix_rankOneMatrix {n : Nat} (x : Fin n -> Real) :
    IsSelfAdjointMatrix (rankOneMatrix x) := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [rankOneMatrix, mul_comm]

/--
The rank-one random matrix associated to a real random vector is pointwise
self-adjoint.
-/
theorem randomSelfAdjointMatrix_rankOneRandomMatrix {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (X : RandomVector Omega n) :
    RandomSelfAdjointMatrix P (rankOneRandomMatrix X) := by
  intro omega
  exact isSelfAdjointMatrix_rankOneMatrix (X omega)

/--
Formula reference: multiplying a real self-adjoint finite matrix by a real
scalar preserves self-adjointness; see
https://en.wikipedia.org/wiki/Self-adjoint_operator
-/
theorem isSelfAdjointMatrix_smul {n : Nat} (c : Real)
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsSelfAdjointMatrix A) :
    IsSelfAdjointMatrix (c • A) := by
  exact hA.smul (IsSelfAdjoint.all c)

/--
Formula reference: negating a real self-adjoint finite matrix preserves
self-adjointness; see https://en.wikipedia.org/wiki/Self-adjoint_operator
-/
theorem isSelfAdjointMatrix_neg {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsSelfAdjointMatrix A) :
    IsSelfAdjointMatrix (-A) := by
  exact hA.neg

/--
Formula reference: pointwise real scalar multiplication preserves the
self-adjoint random-matrix predicate; see
https://en.wikipedia.org/wiki/Self-adjoint_operator
-/
theorem randomSelfAdjointMatrix_smul {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} (c : Real)
    {A : RandomMatrix Omega n n} (hA : RandomSelfAdjointMatrix P A) :
    RandomSelfAdjointMatrix P (fun omega => c • A omega) := by
  intro omega
  exact isSelfAdjointMatrix_smul c (hA omega)

/-- Pointwise scalar multiplication preserves self-adjoint random matrices
through the named `scaledRandomMatrix` adapter. -/
theorem randomSelfAdjointMatrix_scaledRandomMatrix {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat} (c : Real)
    {A : RandomMatrix Omega n n} (hA : RandomSelfAdjointMatrix P A) :
    RandomSelfAdjointMatrix P (scaledRandomMatrix c A) := by
  change RandomSelfAdjointMatrix P (fun omega => c • A omega)
  exact randomSelfAdjointMatrix_smul (P := P) c hA

/--
Formula reference: pointwise negation preserves the self-adjoint random-matrix
predicate; see https://en.wikipedia.org/wiki/Self-adjoint_operator
-/
theorem randomSelfAdjointMatrix_neg {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} {A : RandomMatrix Omega n n}
    (hA : RandomSelfAdjointMatrix P A) :
    RandomSelfAdjointMatrix P (fun omega => -A omega) := by
  intro omega
  exact isSelfAdjointMatrix_neg (hA omega)

end HighDimProb
