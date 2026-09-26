/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Basic

/-!
# `NRR.Geometry.ConvexBody` — translations and positive scalings

This module provides a reusable API for **translations** `K.translate v` and **positive
scalings** `K.scalePos r hr` of solid convex bodies over a real normed vector space.

The two constructors are

* `ConvexBody.translate K v : ConvexBody E` with carrier `(fun x => v + x) '' K`;
* `ConvexBody.scalePos K r hr : ConvexBody E` with carrier `(fun x => r • x) '' K`
 (requiring `0 < r`, so that scaling is a homeomorphism preserving the interior).

together with carrier/membership `simp` lemmas, the identity/composition laws, and the
translation–scaling interaction.

## Why `0 < r`

Scaling by `r = 0` collapses everything to a point and destroys the nonempty-interior
(solidity) field of a `ConvexBody`; it is therefore excluded. For any `r ≠ 0` scaling is a
homeomorphism (`Homeomorph.smulOfNeZero`), and we specialise to the positive case as required
by the downstream width / support-function development.

## Mathlib lemmas reused

* `Convex.translate`, `Convex.smul` — convexity of translates and scalings.
* `IsCompact.image`, `continuous_const_smul`, `continuous_add` — compactness of images.
* `Homeomorph.addLeft`, `Homeomorph.smulOfNeZero`, `Homeomorph.image_interior` — interior
 preservation.
* `Set.image_smul`, `Set.image_image` — carrier bookkeeping.

## Import policy

Following the library-wide policy, `Basic.lean` already pulls in `import Mathlib`, so no extra
imports are required here.
-/

@[expose] public section

namespace NRR.Geometry

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Translation -/

/-- The translate of a convex body by a vector `v`, as a convex body with carrier
`(fun x => v + x) '' K`. Translation is a homeomorphism, so solidity is preserved. -/
def translate (K : ConvexBody E) (v : E) : ConvexBody E where
  carrier := (fun x => v + x) '' (K : Set E)
  convex' := K.convex.translate v
  isCompact' := K.isCompact.image (continuous_const.add continuous_id)
  interior_nonempty' := by
    have h : (fun x => v + x) '' interior (K : Set E)
        = interior ((fun x => v + x) '' (K : Set E)) := by
      simpa using (Homeomorph.addLeft v).image_interior (K : Set E)
    rw [← h]
    exact K.interior_nonempty.image _

@[simp] theorem translate_carrier (K : ConvexBody E) (v : E) :
    (K.translate v : Set E) = (fun x => v + x) '' (K : Set E) := rfl

theorem mem_translate (K : ConvexBody E) (v x : E) :
    x ∈ (K.translate v : Set E) ↔ x - v ∈ (K : Set E) := by
  rw [translate_carrier]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x - v, hx, by abel_nf⟩

@[simp] theorem translate_zero (K : ConvexBody E) :
    K.translate 0 = K := by
  ext x
  rw [translate_carrier]
  simp

theorem translate_translate (K : ConvexBody E) (v w : E) :
    (K.translate v).translate w = K.translate (w + v) := by
  ext x
  rw [translate_carrier, translate_carrier, translate_carrier, Set.image_image]
  simp only [add_assoc]

/-! ### Positive scaling -/

/-- The positive scaling of a convex body by `r > 0`, as a convex body with carrier
`(fun x => r • x) '' K`. Scaling by a nonzero scalar is a homeomorphism, so solidity is
preserved. -/
def scalePos (K : ConvexBody E) (r : ℝ) (hr : 0 < r) : ConvexBody E where
  carrier := (fun x => r • x) '' (K : Set E)
  convex' := by
    rw [Set.image_smul]; exact K.convex.smul r
  isCompact' := K.isCompact.image (continuous_const_smul r)
  interior_nonempty' := by
    have h : (fun x => r • x) '' interior (K : Set E)
        = interior ((fun x => r • x) '' (K : Set E)) := by
      simpa using (Homeomorph.smulOfNeZero r hr.ne').image_interior (K : Set E)
    rw [← h]
    exact K.interior_nonempty.image _

@[simp] theorem scalePos_carrier (K : ConvexBody E) {r : ℝ} (hr : 0 < r) :
    (K.scalePos r hr : Set E) = (fun x => r • x) '' (K : Set E) := rfl

theorem mem_scalePos (K : ConvexBody E) {r : ℝ} (hr : 0 < r) (x : E) :
    x ∈ (K.scalePos r hr : Set E) ↔ (r⁻¹) • x ∈ (K : Set E) := by
  rw [scalePos_carrier]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change r⁻¹ • r • y ∈ (K : Set E)
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    exact hy
  · intro hx
    refine ⟨r⁻¹ • x, hx, ?_⟩
    change r • r⁻¹ • x = x
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

@[simp] theorem scalePos_one (K : ConvexBody E) :
    K.scalePos 1 zero_lt_one = K := by
  ext x
  rw [scalePos_carrier]
  simp

theorem scalePos_scalePos (K : ConvexBody E) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (K.scalePos r hr).scalePos s hs = K.scalePos (s * r) (mul_pos hs hr) := by
  ext x
  rw [scalePos_carrier, scalePos_carrier, scalePos_carrier, Set.image_image]
  simp only [smul_smul]

/-! ### Interaction of scaling and translation -/

theorem scalePos_translate (K : ConvexBody E) {r : ℝ} (hr : 0 < r) (v : E) :
    (K.translate v).scalePos r hr = (K.scalePos r hr).translate (r • v) := by
  ext x
  rw [scalePos_carrier, translate_carrier, translate_carrier, scalePos_carrier,
    Set.image_image, Set.image_image]
  simp only [smul_add]

end ConvexBody

end NRR.Geometry
