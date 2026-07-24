/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.DistanceGeometry.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Order.Star.Real

/-!
# Schoenberg's characterization: the easy direction

Given a real configuration `x : Fin n → EuclideanSpace ℝ (Fin k)` with
squared-distance matrix `D`, the basepoint-centered Gram matrix `centeredGram D` is

* positive semidefinite, and
* of rank at most `k`.

These are exactly the two necessary conditions in Schoenberg's theorem
characterizing Euclidean squared-distance matrices. The converse (sufficiency) is
proved in `SchoenbergHard.lean`.

The proof goes through the polarization identity
`centeredGram D i j = ⟪x i - x 0, x j - x 0⟫`, exhibiting `centeredGram D` as the
Gram matrix of the recentred vectors `x i - x 0`. Positive semidefiniteness is then
`Matrix.posSemidef_gram`; the rank bound comes from the factorization
`gram = mᴴ * m` over the standard orthonormal basis of `EuclideanSpace ℝ (Fin k)`
together with `Matrix.rank_conjTranspose_mul_self` and `Matrix.rank_le_card_height`.

## Main results

* `DistanceGeometry.centeredGram_apply_eq_inner` : the polarization identity.
* `DistanceGeometry.centeredGram_eq_gram` : `centeredGram D` is a Gram matrix.
* `DistanceGeometry.posSemidef_centeredGram`, `DistanceGeometry.rank_centeredGram_le`,
  `DistanceGeometry.schoenberg_easy` : the necessary conditions.
-/

@[expose] public section

namespace DistanceGeometry

open Matrix
open scoped RealInnerProductSpace

variable {n k : ℕ} [NeZero n]

/-- The polarization identity. When `D` is the squared-distance matrix of `x`, the
`(i, j)` entry of the basepoint-centered Gram matrix is the inner product of the recentred
vectors `x i - x 0` and `x j - x 0`. -/
theorem centeredGram_apply_eq_inner
    {D : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → EuclideanSpace ℝ (Fin k)}
    (hD : IsSqDistMatrix D x) (i j : Fin n) :
    centeredGram D i j = ⟪x i - x 0, x j - x 0⟫ := by
  have key := real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
    (x i - x 0) (x j - x 0)
  -- unfold the basepoint-centered Gram entry and replace each `D` entry by its squared distance
  rw [centeredGram_apply, hD 0 i, hD 0 j, hD i j, key]
  -- turn distances into norms
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  -- `‖x 0 - x i‖ = ‖x i - x 0‖`, etc.; `(x i - x 0) - (x j - x 0) = x i - x j`
  rw [norm_sub_rev (x 0) (x i), norm_sub_rev (x 0) (x j)]
  have hsub : (x i - x 0) - (x j - x 0) = x i - x j := by abel
  rw [hsub]
  ring

/-- The basepoint-centered Gram matrix is the Gram matrix of the recentred vectors. -/
theorem centeredGram_eq_gram
    {D : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → EuclideanSpace ℝ (Fin k)}
    (hD : IsSqDistMatrix D x) :
    centeredGram D = gram ℝ (fun i => x i - x 0) := by
  ext i j
  rw [centeredGram_apply_eq_inner hD i j, gram_apply]

/-- The basepoint-centered Gram matrix of a squared-distance matrix is positive semidefinite.
This is the positive-semidefiniteness half of Schoenberg's necessary conditions. -/
theorem posSemidef_centeredGram
    {D : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → EuclideanSpace ℝ (Fin k)}
    (hD : IsSqDistMatrix D x) :
    (centeredGram D).PosSemidef := by
  rw [centeredGram_eq_gram hD]
  exact posSemidef_gram ℝ _

/-- The basepoint-centered Gram matrix of a squared-distance matrix of a configuration in
dimension `k` has rank at most `k`. This is the rank half of Schoenberg's necessary
conditions. -/
theorem rank_centeredGram_le
    {D : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → EuclideanSpace ℝ (Fin k)}
    (hD : IsSqDistMatrix D x) :
    (centeredGram D).rank ≤ k := by
  rw [centeredGram_eq_gram hD]
  -- factor the Gram matrix as `mᴴ * m` over the standard orthonormal basis
  set b : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)) :=
    EuclideanSpace.basisFun (Fin k) ℝ with hb
  rw [gram_eq_conjTranspose_mul b (fun i => x i - x 0)]
  set m : Matrix (Fin k) (Fin n) ℝ := of fun i j => b.repr ((fun i => x i - x 0) j) i with hm
  rw [rank_conjTranspose_mul_self m]
  calc m.rank ≤ Fintype.card (Fin k) := rank_le_card_height m
    _ = k := Fintype.card_fin k

/-- The necessary conditions in Schoenberg's theorem: the basepoint-centered Gram matrix of a
squared-distance matrix of a configuration in `EuclideanSpace ℝ (Fin k)` is positive
semidefinite and has rank at most `k`. -/
theorem schoenberg_easy
    {D : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → EuclideanSpace ℝ (Fin k)}
    (hD : IsSqDistMatrix D x) :
    (centeredGram D).PosSemidef ∧ (centeredGram D).rank ≤ k :=
  ⟨posSemidef_centeredGram hD, rank_centeredGram_le hD⟩

end DistanceGeometry
