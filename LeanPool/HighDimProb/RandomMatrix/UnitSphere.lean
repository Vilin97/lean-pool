/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import LeanPool.HighDimProb.RandomMatrix.Basic

/-!
# Unit-vector vocabulary for random-matrix norm statements

This module uses the existing explicit finite-sum Euclidean convention instead
of introducing a full topological sphere API.

Verified Wikipedia references:
* Unit sphere: https://en.wikipedia.org/wiki/Unit_sphere
* Euclidean distance: https://en.wikipedia.org/wiki/Euclidean_distance
-/

namespace HighDimProb

open scoped BigOperators

noncomputable section

/--
Squared Euclidean norm of a deterministic finite vector.

Formula reference: this is the squared Euclidean norm used to define the unit
sphere; see https://en.wikipedia.org/wiki/Unit_sphere and
https://en.wikipedia.org/wiki/Euclidean_distance
-/
def vectorSqNorm {n : Nat} (x : Fin n -> Real) : Real :=
  Finset.univ.sum fun i : Fin n => x i ^ 2

/--
Formula reference: this unfolds the squared Euclidean norm as a finite sum of
squares; see https://en.wikipedia.org/wiki/Euclidean_distance
-/
@[simp]
theorem vectorSqNorm_apply {n : Nat} (x : Fin n -> Real) :
    vectorSqNorm x = Finset.univ.sum fun i : Fin n => x i ^ 2 :=
  rfl

/--
Formula reference: the squared Euclidean norm is nonnegative because it is a
sum of squares; see https://en.wikipedia.org/wiki/Euclidean_distance
-/
theorem vectorSqNorm_nonneg {n : Nat} (x : Fin n -> Real) :
    0 <= vectorSqNorm x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (x i)

/-- Each coordinate square is bounded by the squared Euclidean norm. -/
theorem coordinate_sq_le_vectorSqNorm {n : Nat} (x : Fin n -> Real)
    (i : Fin n) :
    x i ^ 2 <= vectorSqNorm x := by
  simpa [vectorSqNorm] using
    Finset.single_le_sum
      (fun j _hj => sq_nonneg (x j))
      (Finset.mem_univ i)

/--
Explicit squared norm agrees with Mathlib's L2 norm on `EuclideanSpace`.

Formula reference: this bridges the finite sum-of-squares convention with the
Euclidean norm used in the unit sphere definition; see
https://en.wikipedia.org/wiki/Unit_sphere
-/
theorem vectorSqNorm_eq_norm_sq_toLp {n : Nat} (x : Fin n -> Real) :
    vectorSqNorm x = norm (WithLp.toLp 2 x : EuclideanSpace Real (Fin n)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [vectorSqNorm]

/--
Formula reference: reverse direction of the same Euclidean norm identity; see
https://en.wikipedia.org/wiki/Unit_sphere
-/
theorem norm_sq_toLp_eq_vectorSqNorm {n : Nat} (x : Fin n -> Real) :
    norm (WithLp.toLp 2 x : EuclideanSpace Real (Fin n)) ^ 2 = vectorSqNorm x :=
  (vectorSqNorm_eq_norm_sq_toLp x).symm

/--
Explicit unit-vector predicate: squared Euclidean norm is one.

Formula reference: the unit sphere consists of vectors with norm `1`; see
https://en.wikipedia.org/wiki/Unit_sphere
-/
def IsUnitVector {n : Nat} (x : Fin n -> Real) : Prop :=
  vectorSqNorm x = 1

/--
Unit sphere as a set of deterministic finite vectors.

Formula reference: this is the finite-dimensional set of vectors with
Euclidean norm `1`; see https://en.wikipedia.org/wiki/Unit_sphere
-/
def unitSphere (n : Nat) : Set (Fin n -> Real) :=
  {x | IsUnitVector x}

/--
Formula reference: membership in the unit sphere is the unit-vector predicate;
see https://en.wikipedia.org/wiki/Unit_sphere
-/
theorem mem_unitSphere_iff {n : Nat} (x : Fin n -> Real) :
    x ∈ unitSphere n ↔ IsUnitVector x :=
  Iff.rfl

/--
Formula reference: a unit vector has squared Euclidean norm `1`; see
https://en.wikipedia.org/wiki/Unit_sphere
-/
theorem vectorSqNorm_eq_one_of_isUnitVector {n : Nat} {x : Fin n -> Real}
    (hx : IsUnitVector x) :
    vectorSqNorm x = 1 :=
  hx

/--
Formula reference: the unit-vector squared norm remains nonnegative; see
https://en.wikipedia.org/wiki/Unit_sphere
-/
theorem isUnitVector_vectorSqNorm_nonneg {n : Nat} {x : Fin n -> Real}
    (_hx : IsUnitVector x) :
    0 <= vectorSqNorm x :=
  vectorSqNorm_nonneg x

/--
Formula reference: this converts the explicit squared-norm equation into the
Mathlib Euclidean norm equation `norm x = 1`; see
https://en.wikipedia.org/wiki/Unit_sphere
-/
theorem norm_toLp_eq_one_of_isUnitVector {n : Nat} {x : Fin n -> Real}
    (hx : IsUnitVector x) :
    norm (WithLp.toLp 2 x : EuclideanSpace Real (Fin n)) = 1 := by
  have hsq : norm (WithLp.toLp 2 x : EuclideanSpace Real (Fin n)) ^ 2 = 1 := by
    rw [norm_sq_toLp_eq_vectorSqNorm, hx]
  have hnonneg : 0 <= norm (WithLp.toLp 2 x : EuclideanSpace Real (Fin n)) :=
    norm_nonneg _
  nlinarith

/--
Formula reference: this converts the Mathlib Euclidean norm equation
`norm x = 1` back into the explicit unit-vector predicate; see
https://en.wikipedia.org/wiki/Unit_sphere
-/
theorem isUnitVector_of_norm_toLp_eq_one {n : Nat} {x : Fin n -> Real}
    (hx : norm (WithLp.toLp 2 x : EuclideanSpace Real (Fin n)) = 1) :
    IsUnitVector x := by
  rw [IsUnitVector, vectorSqNorm_eq_norm_sq_toLp, hx]
  norm_num

end

end HighDimProb
