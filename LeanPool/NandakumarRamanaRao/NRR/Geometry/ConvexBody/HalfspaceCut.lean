/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Analysis.InnerProductSpace.Continuous
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Basic

/-!
# `NRR.Geometry.ConvexBody` — cutting a convex body by a closed halfspace

This module provides a reusable API for intersecting a solid `ConvexBody` with a **closed
halfspace** determined by a normal vector `u` and a threshold `t`. It is a core primitive for
cutting convex bodies by hyperplanes and building partitions.

## Setup

`E` is a real inner product space. For a normal vector `u : E` and threshold `t : ℝ` we
define the two closed halfspaces

* `lowerClosedHalfspace u t = {x | inner ℝ u x ≤ t}`;
* `upperClosedHalfspace u t = {x | t ≤ inner ℝ u x}`.

Each is convex (from linearity of the inner product) and closed (as the sublevel/superlevel
set of a continuous functional).

## Cuts

Intersecting a convex body `K` with a closed halfspace always yields a **compact convex**
set (a closed subset of the compact `K`, and an intersection of convex sets). It is again a
solid `ConvexBody` only when its interior is nonempty, so the constructors

* `ConvexBody.cutLowerClosed K u t hInt`
* `ConvexBody.cutUpperClosed K u t hInt`

*require* the nonempty-interior hypothesis `hInt` explicitly. We do **not** claim the cut is a
`ConvexBody` unconditionally, and we do **not** introduce an axiom for the nonempty interior.

## Halfspace definitions are local

There is no oriented-hyperplane file over a general inner product space in the library yet
(the plane-specific `NRR.Halfspace` lives in a different, `E2`-specific development), so
the halfspace definitions are kept minimal here; downstream modules may generalize them.

## Note on `inner`

In the current Mathlib the real inner product is written `inner ℝ u x` (the scalar field is an
explicit argument), which is what appears throughout this file.

## Import policy

Following the library-wide policy, `Basic.lean` already pulls in `import Mathlib`, so no extra
imports are required here.
-/

namespace NRR.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Closed halfspaces -/

/-- The closed **lower** halfspace with normal `u` and threshold `t`: `{x | inner ℝ u x ≤ t}`. -/
def lowerClosedHalfspace (u : E) (t : ℝ) : Set E :=
  {x | inner ℝ u x ≤ t}

/-- The closed **upper** halfspace with normal `u` and threshold `t`: `{x | t ≤ inner ℝ u x}`. -/
def upperClosedHalfspace (u : E) (t : ℝ) : Set E :=
  {x | t ≤ inner ℝ u x}

@[simp] theorem mem_lowerClosedHalfspace (u : E) (t : ℝ) (x : E) :
    x ∈ lowerClosedHalfspace u t ↔ inner ℝ u x ≤ t := Iff.rfl

@[simp] theorem mem_upperClosedHalfspace (u : E) (t : ℝ) (x : E) :
    x ∈ upperClosedHalfspace u t ↔ t ≤ inner ℝ u x := Iff.rfl

theorem lowerClosedHalfspace_convex (u : E) (t : ℝ) :
    Convex ℝ (lowerClosedHalfspace u t) := by
  intro x hx y hy a b ha hb hab
  simp only [lowerClosedHalfspace, Set.mem_ofPred_eq] at *
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have ht : a * t + b * t = t := by rw [← add_mul, hab, one_mul]
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb
  linarith

theorem upperClosedHalfspace_convex (u : E) (t : ℝ) :
    Convex ℝ (upperClosedHalfspace u t) := by
  intro x hx y hy a b ha hb hab
  simp only [upperClosedHalfspace, Set.mem_ofPred_eq] at *
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have ht : a * t + b * t = t := by rw [← add_mul, hab, one_mul]
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb
  linarith

theorem lowerClosedHalfspace_isClosed (u : E) (t : ℝ) :
    IsClosed (lowerClosedHalfspace u t) := by
  apply isClosed_le _ continuous_const
  fun_prop

theorem upperClosedHalfspace_isClosed (u : E) (t : ℝ) :
    IsClosed (upperClosedHalfspace u t) := by
  apply isClosed_le continuous_const
  fun_prop

namespace ConvexBody

/-! ### Compactness of the intersection -/

theorem inter_lowerClosedHalfspace_isCompact
    (K : ConvexBody E) (u : E) (t : ℝ) :
    IsCompact ((K : Set E) ∩ lowerClosedHalfspace u t) :=
  K.isCompact.inter_right (lowerClosedHalfspace_isClosed u t)

theorem inter_upperClosedHalfspace_isCompact
    (K : ConvexBody E) (u : E) (t : ℝ) :
    IsCompact ((K : Set E) ∩ upperClosedHalfspace u t) :=
  K.isCompact.inter_right (upperClosedHalfspace_isClosed u t)

/-! ### The cuts -/

/-- The cut of a convex body `K` by the closed lower halfspace `{x | inner ℝ u x ≤ t}`, as a
`ConvexBody`. Solidity is **not** automatic, so the nonempty-interior hypothesis `hInt` is
required explicitly. -/
def cutLowerClosed
    (K : ConvexBody E) (u : E) (t : ℝ)
    (hInt : (interior ((K : Set E) ∩ lowerClosedHalfspace u t)).Nonempty) :
    ConvexBody E where
  carrier := (K : Set E) ∩ lowerClosedHalfspace u t
  convex' := K.convex.inter (lowerClosedHalfspace_convex u t)
  isCompact' := K.inter_lowerClosedHalfspace_isCompact u t
  interior_nonempty' := hInt

/-- The cut of a convex body `K` by the closed upper halfspace `{x | t ≤ inner ℝ u x}`, as a
`ConvexBody`. Solidity is **not** automatic, so the nonempty-interior hypothesis `hInt` is
required explicitly. -/
def cutUpperClosed
    (K : ConvexBody E) (u : E) (t : ℝ)
    (hInt : (interior ((K : Set E) ∩ upperClosedHalfspace u t)).Nonempty) :
    ConvexBody E where
  carrier := (K : Set E) ∩ upperClosedHalfspace u t
  convex' := K.convex.inter (upperClosedHalfspace_convex u t)
  isCompact' := K.inter_upperClosedHalfspace_isCompact u t
  interior_nonempty' := hInt

@[simp] theorem cutLowerClosed_carrier
    (K : ConvexBody E) (u : E) (t : ℝ)
    (hInt : (interior ((K : Set E) ∩ lowerClosedHalfspace u t)).Nonempty) :
    (K.cutLowerClosed u t hInt : Set E) =
      (K : Set E) ∩ lowerClosedHalfspace u t := rfl

@[simp] theorem cutUpperClosed_carrier
    (K : ConvexBody E) (u : E) (t : ℝ)
    (hInt : (interior ((K : Set E) ∩ upperClosedHalfspace u t)).Nonempty) :
    (K.cutUpperClosed u t hInt : Set E) =
      (K : Set E) ∩ upperClosedHalfspace u t := rfl

@[simp] theorem mem_cutLowerClosed
    (K : ConvexBody E) (u : E) (t : ℝ)
    (hInt : (interior ((K : Set E) ∩ lowerClosedHalfspace u t)).Nonempty) (x : E) :
    x ∈ (K.cutLowerClosed u t hInt : Set E) ↔
      x ∈ (K : Set E) ∧ inner ℝ u x ≤ t := Iff.rfl

@[simp] theorem mem_cutUpperClosed
    (K : ConvexBody E) (u : E) (t : ℝ)
    (hInt : (interior ((K : Set E) ∩ upperClosedHalfspace u t)).Nonempty) (x : E) :
    x ∈ (K.cutUpperClosed u t hInt : Set E) ↔
      x ∈ (K : Set E) ∧ t ≤ inner ℝ u x := Iff.rfl

end ConvexBody

end NRR.Geometry
