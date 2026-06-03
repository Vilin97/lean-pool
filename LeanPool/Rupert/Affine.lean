/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Geometry.Euclidean.Projection

/-!
# LeanPool.Rupert.Affine

Imported Lean Pool material for `LeanPool.Rupert.Affine`.
-/

/-- The Rupert Property for a pair of subsets X, Y of an arbitrary
    finite-dimensional real affine space P. X has the Rupert property
    with respect to Y if there exist
    - affine isometries transforming X and Y respectively
    - an maximal nontrivial affine subspace Q of P
    such that the orthogonal projection onto Q of the transformed image of X fits
    "comfortably" within the projection onto Q of the transformed image of Y.

    By "comfortably" we mean the closure of one set is a subset of the
    interior of the other. This definition rules out trivial cases of
    a set fitting inside itself. -/
def IsAffineRupertPair {P : Type*} {V : Type*} [MetricSpace P] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
    (inner outer : Set P) : Prop :=
    ∃ (inner_isometry outer_isometry : AffineIsometry ℝ P P)
      (Q : AffineSubspace ℝ P) (_ : Nonempty Q) (_ : IsCoatom Q),
    let proj := EuclideanGeometry.orthogonalProjection Q
    let inner_shadow := (proj ∘ inner_isometry) '' inner
    let outerShadow: Set Q := (proj ∘ outer_isometry) '' outer
    closure inner_shadow ⊆ interior outerShadow

/-- The Rupert Property for a subset S of affine space P. S has the Rupert property
    if it has the pairwise Rupert property with respect to itself. -/
def IsAffineRupertSet {P : Type*} {V : Type*} [MetricSpace P] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
    (S : Set P) : Prop :=
    IsAffineRupertPair S S
