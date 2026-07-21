/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Distance geometry: core definitions

This file sets up the basic objects of Euclidean distance geometry: the
squared-distance matrix of a point configuration, the predicate that a given
matrix is such a matrix, embeddability in a fixed dimension, and the centered
Gram matrix that underlies Schoenberg's characterization.

A configuration of points indexed by `ι` in `k`-dimensional Euclidean space is a
map `x : ι → EuclideanSpace ℝ (Fin k)`. The *squared-distance matrix* `sqDistMatrix x`
records `dist (x i) (x j) ^ 2`. Schoenberg's theorem characterizes which symmetric
hollow matrices arise this way through their *centered Gram matrix*.

## Main definitions

* `DistanceGeometry.sqDistMatrix x` : the squared-distance matrix of `x`.
* `DistanceGeometry.IsSqDistMatrix D x` : `D` is the squared-distance matrix of `x`.
* `DistanceGeometry.EmbedsIn D k` : `D` embeds as a squared-distance matrix in
  `EuclideanSpace ℝ (Fin k)`.
* `DistanceGeometry.IsPreDistMatrix D` : `D` is symmetric and hollow.
* `DistanceGeometry.centeredGram D` : the Gram matrix obtained by centering `D` at
  the base index `0`.

## Implementation notes

`centeredGram` is centered at the fixed base index `0 : Fin n` (hence `[NeZero n]`);
this is a gauge choice. Any base index yields a Gram matrix congruent to this one,
with the same rank and positive-semidefiniteness, so the Schoenberg conditions are
base-point independent. The point index is taken to be `Fin n` here because the
base-`0` choice uses the order on `Fin n`; the squared-distance machinery itself
only needs `Fintype` and `DecidableEq`.

## References

* J. von Neumann and I. J. Schoenberg, *Fourier integrals and metric geometry*, 1941.
* I. J. Schoenberg, *Remarks to Maurice Fréchet's article ...*, 1935.
-/

@[expose] public section

namespace DistanceGeometry

open scoped RealInnerProductSpace

variable {n k : ℕ}

/-- The squared-distance matrix of a configuration `x`: its `(i, j)` entry is the
squared Euclidean distance between `x i` and `x j`. -/
noncomputable def sqDistMatrix (x : Fin n → EuclideanSpace ℝ (Fin k)) :
    Matrix (Fin n) (Fin n) ℝ :=
  .of fun i j => dist (x i) (x j) ^ 2

@[simp]
theorem sqDistMatrix_apply (x : Fin n → EuclideanSpace ℝ (Fin k)) (i j : Fin n) :
    sqDistMatrix x i j = dist (x i) (x j) ^ 2 := rfl

/-- `D` is the squared-distance matrix of the configuration `x` when every entry
`D i j` equals the squared Euclidean distance between points `x i` and `x j`. -/
def IsSqDistMatrix (D : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin k)) : Prop :=
  ∀ i j, D i j = dist (x i) (x j) ^ 2

theorem IsSqDistMatrix.eq_sqDistMatrix {D : Matrix (Fin n) (Fin n) ℝ}
    {x : Fin n → EuclideanSpace ℝ (Fin k)} (hD : IsSqDistMatrix D x) :
    D = sqDistMatrix x :=
  Matrix.ext hD

/-- A squared-distance matrix is symmetric: `D i j = D j i`. -/
theorem IsSqDistMatrix.symm {D : Matrix (Fin n) (Fin n) ℝ}
    {x : Fin n → EuclideanSpace ℝ (Fin k)} (hD : IsSqDistMatrix D x) (i j : Fin n) :
    D i j = D j i := by
  rw [hD i j, hD j i, dist_comm]

/-- A squared-distance matrix is hollow: its diagonal vanishes. -/
theorem IsSqDistMatrix.hollow {D : Matrix (Fin n) (Fin n) ℝ}
    {x : Fin n → EuclideanSpace ℝ (Fin k)} (hD : IsSqDistMatrix D x) (i : Fin n) :
    D i i = 0 := by
  rw [hD i i, dist_self]; simp

/-- `D` is embeddable in dimension `k` when it is the squared-distance matrix of
some configuration of points in `EuclideanSpace ℝ (Fin k)`. -/
def EmbedsIn (D : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : Prop :=
  ∃ x : Fin n → EuclideanSpace ℝ (Fin k), IsSqDistMatrix D x

/-- `D` is a pre-distance matrix: symmetric and hollow (zero diagonal). Every
squared-distance matrix is a pre-distance matrix; this is the structural hypothesis
of the sufficiency direction of Schoenberg's theorem. -/
def IsPreDistMatrix (D : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, D i j = D j i) ∧ (∀ i, D i i = 0)

/-- A pre-distance matrix is symmetric. -/
theorem IsPreDistMatrix.symm {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsPreDistMatrix D)
    (i j : Fin n) : D i j = D j i := hD.1 i j

/-- A pre-distance matrix is hollow. -/
theorem IsPreDistMatrix.hollow {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsPreDistMatrix D)
    (i : Fin n) : D i i = 0 := hD.2 i

/-- Every squared-distance matrix is a pre-distance matrix. -/
theorem IsSqDistMatrix.isPreDistMatrix {D : Matrix (Fin n) (Fin n) ℝ}
    {x : Fin n → EuclideanSpace ℝ (Fin k)} (hD : IsSqDistMatrix D x) :
    IsPreDistMatrix D :=
  ⟨hD.symm, hD.hollow⟩

/-- The centered Gram matrix of a squared-distance matrix `D`, centered at the base
index `0` (requires `n ≥ 1`, i.e. `[NeZero n]`, for the index `0 : Fin n` to exist).
When `D` holds the squared distances of a configuration `x`, this matrix equals
`⟪x i - x 0, x j - x 0⟫` (proved in `Schoenberg.lean`), hence it is the Gram matrix
of the recentred vectors `x i - x 0`. -/
noncomputable def centeredGram [NeZero n] (D : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  .of fun i j => (D 0 i + D 0 j - D i j) / 2

@[simp]
theorem centeredGram_apply [NeZero n] (D : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    centeredGram D i j = (D 0 i + D 0 j - D i j) / 2 := rfl

/-- The centered Gram matrix of a symmetric matrix is symmetric. -/
theorem centeredGram_symm [NeZero n] {D : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : ∀ i j, D i j = D j i) (i j : Fin n) :
    centeredGram D i j = centeredGram D j i := by
  simp only [centeredGram_apply]
  rw [hsymm i j, add_comm (D 0 i)]

end DistanceGeometry
