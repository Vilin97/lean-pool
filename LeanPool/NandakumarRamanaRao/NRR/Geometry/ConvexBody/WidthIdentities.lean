/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Width
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunctionTransform

/-!
# `NRR.Geometry.ConvexBody` — width function transformation identities

This module records how the **width function** `w_K(u) = h_K(u) + h_K(-u)` transforms under the
standard operations on a `ConvexBody` `K` in a real inner product space `E`:

* **translation invariance** (`widthFunction_translate`),
* **positive scaling of the body** (`widthFunction_scalePos_body`),
* **scaling of the direction** (`widthFunction_smul_direction`), and
* **linear isometry equivalences** (`widthFunction_imageLinearIsometryEquiv`).

## Design notes

Every identity is reduced to the corresponding support-function transformation lemma from
`SupportFunction.lean`, `SupportFunctionBasic.lean` and `SupportFunctionTransform.lean`:

* `supportFunction_translate` — `h_{K+a}(u) = ⟪a, u⟫ + h_K(u)`,
* `supportFunction_scalePos_body` — `h_{rK}(u) = r · h_K(u)` for `0 < r`,
* `supportFunction_smul_direction_of_nonneg` — `h_K(c u) = c · h_K(u)` for `0 ≤ c`,
* `supportFunction_imageLinearIsometryEquiv` — `h_{eK}(u) = h_K(e⁻¹ u)`.

No structure internals or `sSup` are unfolded here.

## Import policy

`Width.lean` and `SupportFunctionTransform.lean` (both transitively via `Basic.lean`) already
pull in `import Mathlib`, so no extra imports are required here.
-/

namespace NRR.Geometry

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Translation invariance.** The width is unchanged under translating the body. -/
theorem widthFunction_translate
    (K : ConvexBody E) (a u : E) :
    widthFunction (K.translate a) u = widthFunction K u := by
  simp only [widthFunction_def, supportFunction_translate, inner_neg_right]
  ring

/-- **Positive scaling of the body.** `w_{rK}(u) = r · w_K(u)` for `0 < r`. -/
theorem widthFunction_scalePos_body
    (K : ConvexBody E) {r : ℝ} (hr : 0 < r) (u : E) :
    widthFunction (K.scalePos r hr) u =
      r * widthFunction K u := by
  simp only [widthFunction_def, supportFunction_scalePos_body]
  ring

/-- **Direction scaling.** `w_K(c u) = |c| · w_K(u)` for any real `c`. -/
theorem widthFunction_smul_direction
    (K : ConvexBody E) (c : ℝ) (u : E) :
    widthFunction K (c • u) = |c| * widthFunction K u := by
  rcases le_total 0 c with hc | hc
  · rw [widthFunction_smul_direction_of_nonneg K hc u, abs_of_nonneg hc]
  · have h : c • u = -((-c) • u) := by rw [neg_smul, neg_neg]
    rw [h, widthFunction_neg,
      widthFunction_smul_direction_of_nonneg K (by linarith : (0:ℝ) ≤ -c) u,
      abs_of_nonpos hc]

/-- **Image under a linear isometry equivalence.** `w_{eK}(u) = w_K(e⁻¹ u)`. -/
theorem widthFunction_imageLinearIsometryEquiv
    (K : ConvexBody E) (e : E ≃ₗᵢ[ℝ] F) (u : F) :
    widthFunction (K.imageLinearIsometryEquiv e) u =
      widthFunction K (e.symm u) := by
  simp only [widthFunction_def, supportFunction_imageLinearIsometryEquiv, map_neg]

end ConvexBody

end NRR.Geometry
