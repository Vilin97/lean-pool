/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Operations

/-!
# `NRR.Multivalued.PerimeterObservable` — normalized perimeter as a nice multivalued function

This module builds the concrete nice multivalued function representing perimeter on the lower-area
convex-body hyperspace `BodySpace K A` (with `A > 0`).

The planar Cauchy perimeter of the solid bridge `C.toGeometryConvexBody hA` is normalized by the
strictly positive constant `1 + K.perimeter`. Since the underlying body of every element is
contained in the parent body `K`, perimeter monotonicity under inclusion bounds the normalized
value strictly below `1`; nonnegativity of the perimeter bounds it below by `0`. The normalized
perimeter is therefore a continuous map into `[0, 1)`, so `|normalizedPerimeter C| < 1` and the
canonical observable constructor `NiceMV.ofObservable` applies.

The resulting nice multivalued function `perimeterNiceMV` evaluates by `(t : ℝ) -
normalizedPerimeter C`, following the fixed sign convention (negative at `-1`, positive at `1`); its
zero relation is exactly `(t : ℝ) = normalizedPerimeter C`.
-/

@[expose] public section

open NRR.Geometry

namespace NRR

variable {K : Geometry.ConvexBody Plane} {A : ℝ}

/-- The **normalized perimeter** observable on `BodySpace K A` (`A > 0`): the planar perimeter of
the solid bridge divided by the strictly positive constant `1 + K.perimeter`. It is continuous, as
the perimeter of the solid bridge is continuous and the denominator is a positive constant. -/
noncomputable def normalizedPerimeter
    (K : Geometry.ConvexBody Plane) (A : ℝ) (hA : 0 < A) :
    C(BodySpace K A, ℝ) :=
  ⟨fun C => (C.toGeometryConvexBody hA).perimeter / (1 + K.perimeter),
    (BodySpace.continuous_perimeter hA).div_const _⟩

@[simp] theorem normalizedPerimeter_apply
    (hA : 0 < A) (C : BodySpace K A) :
    normalizedPerimeter K A hA C =
      (C.toGeometryConvexBody hA).perimeter /
        (1 + K.perimeter) := rfl

/-- The denominator `1 + K.perimeter` is strictly positive. -/
theorem one_add_perimeter_pos (K : Geometry.ConvexBody Plane) :
    0 < 1 + K.perimeter := by
  have := K.perimeter_nonneg
  linarith

theorem normalizedPerimeter_nonneg
    (hA : 0 < A) (C : BodySpace K A) :
    0 ≤ normalizedPerimeter K A hA C := by
  rw [normalizedPerimeter_apply]
  apply div_nonneg
  · exact (C.toGeometryConvexBody hA).perimeter_nonneg
  · exact le_of_lt (one_add_perimeter_pos K)

theorem normalizedPerimeter_lt_one
    (hA : 0 < A) (C : BodySpace K A) :
    normalizedPerimeter K A hA C < 1 := by
  rw [normalizedPerimeter_apply, div_lt_one (one_add_perimeter_pos K)]
  have hmono : (C.toGeometryConvexBody hA).perimeter ≤ K.perimeter := by
    apply Geometry.ConvexBody.perimeter_mono
    rw [BodySpace.toGeometryConvexBody_carrier]
    exact C.body.subset_parent
  linarith

theorem abs_normalizedPerimeter_lt_one
    (hA : 0 < A) (C : BodySpace K A) :
    |normalizedPerimeter K A hA C| < 1 := by
  rw [abs_lt]
  refine ⟨by linarith [normalizedPerimeter_nonneg hA C], normalizedPerimeter_lt_one hA C⟩

/-- The **nice multivalued function representing perimeter** on `BodySpace K A`, obtained from the
normalized perimeter observable via the canonical constructor. It evaluates by `(t : ℝ) -
normalizedPerimeter C`, so its zero set is the graph `(t : ℝ) = normalizedPerimeter C`. -/
noncomputable def perimeterNiceMV
    (K : Geometry.ConvexBody Plane) (A : ℝ) (hA : 0 < A) :
    NiceMV (BodySpace K A) :=
  NiceMV.ofObservable
    (normalizedPerimeter K A hA)
    (abs_normalizedPerimeter_lt_one
      (K := K) (A := A) hA)

theorem perimeterNiceMV_eval
    (hA : 0 < A) (C : BodySpace K A) (t : SignedInterval) :
    (perimeterNiceMV K A hA).eval C t =
      (t : ℝ) - normalizedPerimeter K A hA C := rfl

theorem perimeterNiceMV_zero_iff
    (hA : 0 < A) (C : BodySpace K A) (t : SignedInterval) :
    (perimeterNiceMV K A hA).Zero C t ↔
      (t : ℝ) = normalizedPerimeter K A hA C :=
  NiceMV.ofObservable_zero_iff _ _ C t

end NRR
