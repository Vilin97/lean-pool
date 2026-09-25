/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Basic

/-!
# `NRR.Geometry.ConvexBody` — images under continuous linear equivalences

This module provides an API for images and preimages of `ConvexBody`s under **continuous
linear equivalences** `e : E ≃L[ℝ] F`. Only linear *equivalences* are treated: an arbitrary
continuous linear map `L : E →L[ℝ] F` may be non-injective and collapse the interior, so it
never preserves the solidity (`interior_nonempty'`) field of a `ConvexBody` and is
intentionally excluded here (and by module design).

The two constructors are

* `ConvexBody.imageLinearEquiv K e : ConvexBody F` with carrier `e '' K`;
* `ConvexBody.preimageLinearEquiv K e : ConvexBody E` with carrier `e ⁻¹' K`
 (defined as the image under `e.symm`).

together with carrier/membership `simp` lemmas, the structural facts (convex, compact,
nonempty, nonempty interior), and the identity / composition / inverse laws.

## Why no finite-dimensionality hypothesis is needed

Unlike an `AffineEquiv`, a `ContinuousLinearEquiv` bundles continuity of both `e` and `e.symm`
by definition, and is in particular a homeomorphism via `ContinuousLinearEquiv.toHomeomorph`.
Consequently *no* finite-dimensionality assumption is required: continuity (for compactness of
the image) and openness (for interior preservation) come for free. The declarations below only
assume that `E`, `F` (and, for composition, `G`) are real normed spaces.

## Mathlib lemmas reused

* `ContinuousLinearEquiv.toHomeomorph` — a continuous linear equivalence as a homeomorphism.
* `ContinuousLinearEquiv.coe_toHomeomorph` — its underlying function is `e`.
* `Homeomorph.image_interior` — `h '' interior s = interior (h '' s)`.
* `Convex.linear_image` — linear image of a convex set is convex.
* `IsCompact.image` — continuous image of a compact set is compact.
* `ContinuousLinearEquiv.image_eq_preimage_symm`, `ContinuousLinearEquiv.coe_refl`,
 `ContinuousLinearEquiv.symm_trans` and friends — carrier bookkeeping.

## Import policy

Following the library-wide policy, `Basic.lean` already pulls in `import Mathlib`, so no extra
imports are required here.
-/

@[expose] public section

namespace NRR.Geometry

namespace ConvexBody

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A continuous linear equivalence preserves interiors:
`e '' interior s = interior (e '' s)`. This is `Homeomorph.image_interior` transported along
`ContinuousLinearEquiv.toHomeomorph`. -/
theorem continuousLinearEquiv_image_interior (e : E ≃L[ℝ] F) (s : Set E) :
    e '' interior s = interior (e '' s) := by
  have h := (e.toHomeomorph).image_interior s
  rwa [ContinuousLinearEquiv.coe_toHomeomorph] at h

/-- The image of a convex body under a continuous linear equivalence, as a convex body with
carrier `e '' K`. Solidity is preserved because a continuous linear equivalence is a
homeomorphism. -/
def imageLinearEquiv (K : ConvexBody E) (e : E ≃L[ℝ] F) : ConvexBody F where
  carrier := e '' (K : Set E)
  convex' := K.convex.linear_image (e : E →ₗ[ℝ] F)
  isCompact' := K.isCompact.image e.continuous
  interior_nonempty' := by
    rw [← continuousLinearEquiv_image_interior]
    exact K.interior_nonempty.image e

@[simp] theorem imageLinearEquiv_carrier (K : ConvexBody E) (e : E ≃L[ℝ] F) :
    ((K.imageLinearEquiv e : ConvexBody F) : Set F) = e '' (K : Set E) := rfl

theorem mem_imageLinearEquiv (K : ConvexBody E) (e : E ≃L[ℝ] F) (y : F) :
    y ∈ (K.imageLinearEquiv e : Set F) ↔ e.symm y ∈ (K : Set E) := by
  rw [imageLinearEquiv_carrier]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨e.symm y, hy, by simp⟩

/-- The preimage of a convex body under a continuous linear equivalence, as a convex body with
carrier `e ⁻¹' K`. Implemented as the image under `e.symm`. -/
def preimageLinearEquiv (K : ConvexBody F) (e : E ≃L[ℝ] F) : ConvexBody E :=
  K.imageLinearEquiv e.symm

@[simp] theorem preimageLinearEquiv_carrier (K : ConvexBody F) (e : E ≃L[ℝ] F) :
    ((K.preimageLinearEquiv e : ConvexBody E) : Set E) = e ⁻¹' (K : Set F) := by
  rw [preimageLinearEquiv, imageLinearEquiv_carrier,
    ContinuousLinearEquiv.image_eq_preimage_symm, ContinuousLinearEquiv.symm_symm]

theorem mem_preimageLinearEquiv (K : ConvexBody F) (e : E ≃L[ℝ] F) (x : E) :
    x ∈ (K.preimageLinearEquiv e : Set E) ↔ e x ∈ (K : Set F) := by
  rw [preimageLinearEquiv_carrier]; rfl

/-- Convexity of a linear-equivalence image. -/
theorem imageLinearEquiv_convex (K : ConvexBody E) (e : E ≃L[ℝ] F) :
    Convex ℝ ((K.imageLinearEquiv e : ConvexBody F) : Set F) :=
  (K.imageLinearEquiv e).convex

/-- Compactness of a linear-equivalence image. -/
theorem imageLinearEquiv_isCompact (K : ConvexBody E) (e : E ≃L[ℝ] F) :
    IsCompact ((K.imageLinearEquiv e : ConvexBody F) : Set F) :=
  (K.imageLinearEquiv e).isCompact

/-- Nonemptiness of a linear-equivalence image. -/
theorem imageLinearEquiv_nonempty (K : ConvexBody E) (e : E ≃L[ℝ] F) :
    ((K.imageLinearEquiv e : ConvexBody F) : Set F).Nonempty :=
  (K.imageLinearEquiv e).nonempty

/-- Nonempty interior of a linear-equivalence image. -/
theorem imageLinearEquiv_interior_nonempty (K : ConvexBody E) (e : E ≃L[ℝ] F) :
    (interior ((K.imageLinearEquiv e : ConvexBody F) : Set F)).Nonempty :=
  (K.imageLinearEquiv e).interior_nonempty

@[simp] theorem imageLinearEquiv_id (K : ConvexBody E) :
    K.imageLinearEquiv (ContinuousLinearEquiv.refl ℝ E) = K := by
  ext x
  simp only [imageLinearEquiv_carrier, ContinuousLinearEquiv.coe_refl', Set.image_id]

theorem imageLinearEquiv_comp (K : ConvexBody E) (e₁ : E ≃L[ℝ] F) (e₂ : F ≃L[ℝ] G) :
    (K.imageLinearEquiv e₁).imageLinearEquiv e₂ = K.imageLinearEquiv (e₁.trans e₂) := by
  ext x
  rw [imageLinearEquiv_carrier, imageLinearEquiv_carrier, imageLinearEquiv_carrier,
    Set.image_image]
  rfl

@[simp] theorem imageLinearEquiv_symm (K : ConvexBody E) (e : E ≃L[ℝ] F) :
    (K.imageLinearEquiv e).imageLinearEquiv e.symm = K := by
  ext x
  simp only [imageLinearEquiv_carrier, Set.image_image,
    ContinuousLinearEquiv.symm_apply_apply, Set.image_id']

end ConvexBody

end NRR.Geometry
