/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunctionBasic

/-!
# `NRR.Geometry.ConvexBody` — support-function transformation API

This module completes the transformation API for the support function of a `ConvexBody` under

* **translations** `K.translate a`,
* **positive scalings** `K.scalePos r hr`,
* **negation / reflection** `K.neg`,
* **linear isometry equivalences** `K.imageLinearIsometryEquiv e`, and
* **general continuous linear equivalences** `K.imageLinearEquiv e` (via the *adjoint*).

The goal is that later width and perimeter proofs become pure rewriting.

## Contents

* `supportFunction_scalePos_body` (`@[simp]`) — `h_{rK}(u) = r · h_K(u)` for `0 < r`, the
 transformation-API spelling of the base-module lemma `supportFunction_scalePos`.
* `ConvexBody.neg`, with carrier/membership `simp` lemmas, and
 `supportFunction_neg_body` (`@[simp]`) — `h_{-K}(u) = h_K(-u)`.
* `ConvexBody.imageLinearIsometryEquiv`, with carrier/membership `simp` lemmas, and
 `supportFunction_imageLinearIsometryEquiv` — `h_{eK}(u) = h_K(e⁻¹ u)`.
* `supportFunction_imageLinearEquiv_adjoint` — `h_{eK}(u) = h_K(eᵀ u)` for a general
 continuous linear equivalence, the transformation-API spelling of the base-module lemma
 `supportFunction_imageLinearEquiv`.

## Reused results

* **Translation** is already provided by `supportFunction_translate` in
 `NRR.Geometry.ConvexBody.SupportFunctionBasic`
 (`h_{K+a}(u) = ⟪a, u⟫ + h_K(u)`); it is re-exported through this module's imports and needs
 no restatement here.
* The base-module lemmas `supportFunction_scalePos` and `supportFunction_imageLinearEquiv`
 are wrapped under the transformation-API names required by This module.

## Design notes

All proofs go through the order-theoretic interfaces `inner_le_supportFunction` (upper bound)
and `supportFunction_le` (least upper bound), together with the attainment lemma
`exists_supportPoint`; no `sSup` is manipulated directly.

For an inner product space the correct direction-pullback under a linear equivalence is the
**adjoint**, not `e.symm`. For a linear *isometry* equivalence the adjoint coincides with
`e.symm`, which is why the clean `e.symm` formula is available (and proved directly from
`LinearIsometryEquiv.inner_map_map`, needing no completeness hypothesis). The general
`imageLinearEquiv` formula uses `ContinuousLinearMap.adjoint` and hence requires the spaces to
be complete (automatic in finite dimensions).

## Import policy

Only `SupportFunctionBasic` is imported; it transitively provides the whole `ConvexBody`,
support-function, `AffineOps` and `LinearImage` API (and, through `Basic`, `import Mathlib`).
-/

@[expose] public section

namespace NRR.Geometry

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### Translation (re-exported)

The translation identity `supportFunction (K.translate a) u = ⟪a, u⟫ + supportFunction K u`
is `NRR.Geometry.ConvexBody.supportFunction_translate`, proved in
`SupportFunctionBasic` and available through this module's imports. It is not restated here to
avoid a duplicate declaration. -/

/-! ### Positive scaling of the body -/

/-- **Positive scaling of the body.** `h_{rK}(u) = r · h_K(u)` for `0 < r`.

This is the transformation-API spelling of the base-module lemma `supportFunction_scalePos`. -/
theorem supportFunction_scalePos_body
    (K : ConvexBody E) {r : ℝ} (hr : 0 < r) (u : E) :
    supportFunction (K.scalePos r hr) u = r * supportFunction K u :=
  K.supportFunction_scalePos hr u

/-! ### Negation / reflection -/

/-- The **reflection** `-K` of a convex body through the origin, as a convex body with carrier
`(-·) '' K = -K`. Implemented as the image under the negation linear isometry equivalence, so
solidity is preserved. -/
def neg (K : ConvexBody E) : ConvexBody E where
  carrier := Neg.neg '' (K : Set E)
  convex' := by
    rw [Set.image_neg_eq_neg]; exact K.convex.neg
  isCompact' := by
    rw [Set.image_neg_eq_neg]; exact K.isCompact.neg
  interior_nonempty' := by
    have h : Neg.neg '' interior (K : Set E) = interior (Neg.neg '' (K : Set E)) := by
      simpa using (Homeomorph.neg E).image_interior (K : Set E)
    rw [← h]
    exact K.interior_nonempty.image _

@[simp] theorem neg_carrier (K : ConvexBody E) :
    (K.neg : Set E) = Neg.neg '' (K : Set E) := rfl

theorem mem_neg (K : ConvexBody E) (x : E) :
    x ∈ (K.neg : Set E) ↔ -x ∈ (K : Set E) := by
  rw [neg_carrier]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨-x, hx, by simp⟩

/-- **Reflection.** `h_{-K}(u) = h_K(-u)`. -/
@[simp] theorem supportFunction_neg_body
    (K : ConvexBody E) (u : E) :
    supportFunction K.neg u = supportFunction K (-u) := by
  apply le_antisymm
  · apply K.neg.supportFunction_le
    intro y hy
    rw [mem_neg] at hy
    have : (inner ℝ y u : ℝ) = (inner ℝ (-y) (-u) : ℝ) := by
      rw [inner_neg_neg]
    rw [this]
    exact K.inner_le_supportFunction hy
  · obtain ⟨x, hx, hxeq⟩ := K.exists_supportPoint (-u)
    have hmem : -x ∈ (K.neg : Set E) := by
      rw [mem_neg]; simpa using hx
    calc supportFunction K (-u) = (inner ℝ x (-u) : ℝ) := hxeq.symm
      _ = (inner ℝ (-x) u : ℝ) := by rw [inner_neg_left, inner_neg_right]
      _ ≤ supportFunction K.neg u := K.neg.inner_le_supportFunction hmem

/-! ### Linear isometry equivalence -/

/-- The image of a convex body under a **linear isometry equivalence** `e : E ≃ₗᵢ[ℝ] F`, as a
convex body with carrier `e '' K`. Implemented as the image under the underlying continuous
linear equivalence `e.toContinuousLinearEquiv`. -/
def imageLinearIsometryEquiv (K : ConvexBody E) (e : E ≃ₗᵢ[ℝ] F) : ConvexBody F :=
  K.imageLinearEquiv e.toContinuousLinearEquiv

@[simp] theorem imageLinearIsometryEquiv_carrier (K : ConvexBody E) (e : E ≃ₗᵢ[ℝ] F) :
    (K.imageLinearIsometryEquiv e : Set F) = e '' (K : Set E) := rfl

theorem mem_imageLinearIsometryEquiv (K : ConvexBody E) (e : E ≃ₗᵢ[ℝ] F) (y : F) :
    y ∈ (K.imageLinearIsometryEquiv e : Set F) ↔ e.symm y ∈ (K : Set E) := by
  rw [imageLinearIsometryEquiv, mem_imageLinearEquiv]
  rfl

/-- **Image under a linear isometry equivalence.** `h_{eK}(u) = h_K(e⁻¹ u)`.

Unlike a general linear equivalence, an isometry pulls the direction back through `e.symm`,
because the adjoint of a linear isometry equivalence is its inverse. No completeness hypothesis
is required. -/
theorem supportFunction_imageLinearIsometryEquiv
    (K : ConvexBody E) (e : E ≃ₗᵢ[ℝ] F) (u : F) :
    supportFunction (K.imageLinearIsometryEquiv e) u =
      supportFunction K (e.symm u) := by
  have key : ∀ x : E, (inner ℝ (e x) u : ℝ) = inner ℝ x (e.symm u) := by
    intro x
    calc (inner ℝ (e x) u : ℝ)
        = inner ℝ (e x) (e (e.symm u)) := by rw [e.apply_symm_apply]
      _ = inner ℝ x (e.symm u) := e.inner_map_map x (e.symm u)
  apply le_antisymm
  · apply (K.imageLinearIsometryEquiv e).supportFunction_le
    intro y hy
    rw [mem_imageLinearIsometryEquiv] at hy
    have hthis : (inner ℝ y u : ℝ) = inner ℝ (e.symm y) (e.symm u) := by
      rw [← key (e.symm y), e.apply_symm_apply]
    rw [hthis]
    exact K.inner_le_supportFunction hy
  · obtain ⟨x, hx, hxeq⟩ := K.exists_supportPoint (e.symm u)
    have hmem : e x ∈ (K.imageLinearIsometryEquiv e : Set F) := by
      rw [mem_imageLinearIsometryEquiv]; simpa using hx
    calc supportFunction K (e.symm u) = (inner ℝ x (e.symm u) : ℝ) := hxeq.symm
      _ = (inner ℝ (e x) u : ℝ) := (key x).symm
      _ ≤ supportFunction (K.imageLinearIsometryEquiv e) u :=
          (K.imageLinearIsometryEquiv e).inner_le_supportFunction hmem

/-! ### General continuous linear equivalence (adjoint form) -/

/-- **Image under a continuous linear equivalence (adjoint form).** `h_{eK}(u) = h_K(eᵀ u)`,
where `eᵀ = ContinuousLinearMap.adjoint (e : E →L[ℝ] F)`.

This is the transformation-API spelling of the base-module lemma
`supportFunction_imageLinearEquiv`. The naive `e.symm` form is false unless `e` is an isometry
(compare `supportFunction_imageLinearIsometryEquiv`). Completeness of `E` and `F` is required
for the adjoint to exist (automatic in finite dimensions). -/
theorem supportFunction_imageLinearEquiv_adjoint
    [CompleteSpace E] [CompleteSpace F]
    (K : ConvexBody E) (e : E ≃L[ℝ] F) (u : F) :
    supportFunction (K.imageLinearEquiv e) u =
      supportFunction K (ContinuousLinearMap.adjoint (e : E →L[ℝ] F) u) :=
  K.supportFunction_imageLinearEquiv e u

/-! ### Reflection via the linear isometry API

For completeness we record that `K.neg` is the image of `K` under the negation linear isometry
equivalence, so the reflection identity is a special case of the isometry identity. -/
theorem neg_eq_imageLinearIsometryEquiv_neg (K : ConvexBody E) :
    K.neg = K.imageLinearIsometryEquiv (LinearIsometryEquiv.neg ℝ) := by
  ext x
  rw [neg_carrier, imageLinearIsometryEquiv_carrier]
  rfl

end ConvexBody

end NRR.Geometry
