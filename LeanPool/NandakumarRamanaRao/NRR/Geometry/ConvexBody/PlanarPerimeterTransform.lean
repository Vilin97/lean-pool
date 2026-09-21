/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeter
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.WidthIdentities

/-!
# `NRR.Geometry.ConvexBody` — transformation laws for the planar perimeter

This module records the deterministic transformation laws of the **planar (Cauchy) perimeter**
`planarPerimeter` under the standard body operations from `AffineOps.lean` and
`SupportFunctionTransform.lean`:

* **translation invariance** (`planarPerimeter_translate`),
* **positive scaling** (`planarPerimeter_scalePos`), and
* **reflection / negation invariance** (`planarPerimeter_neg`).

## Design notes

Each law reduces to the corresponding *pointwise* width-function identity from
`WidthIdentities.lean` / `Width.lean` / `SupportFunctionTransform.lean`, applied under the
interval integral defining `planarPerimeter`:

* translation: `widthFunction_translate` makes the integrand pointwise equal, so
 `intervalIntegral.integral_congr` closes the goal;
* scaling: `widthFunction_scalePos_body` turns the integrand into `r • w_K`, and the constant is
 pulled out with `intervalIntegral.integral_const_mul`;
* reflection: `supportFunction_neg_body` (via the local `widthFunction_neg_body`) shows the
 integrand is pointwise equal.

## Rotation

A rotation body operation (`rotate`) is **not** available in this development, and the required
interval change-of-variables theorem is likewise not readily available, so arbitrary rotation
invariance is intentionally *not* attempted here (see the design's explicit prohibition).

## Import policy

Only `PlanarPerimeter.lean` and `WidthIdentities.lean` are imported; they transitively provide
all of Mathlib together with the perimeter, width and support-function APIs. No extra imports are
required.
-/

namespace NRR.Geometry

open Real MeasureTheory ConvexBody

/-- **Reflection of the width function.** The width of the reflected body `-K` equals the width
of `K` in every direction: `w_{-K}(u) = w_K(u)`. -/
theorem widthFunction_neg_body
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : ConvexBody E) (u : E) :
    ConvexBody.widthFunction K.neg u = ConvexBody.widthFunction K u := by
  simp only [widthFunction_def, supportFunction_neg_body, neg_neg]
  ring

/-- **Translation invariance** of the planar perimeter. -/
@[simp] theorem planarPerimeter_translate
    (K : ConvexBody Plane) (a : Plane) :
    planarPerimeter (K.translate a) = planarPerimeter K := by
  simp only [planarPerimeter_def]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  exact widthFunction_translate K a (circleVec θ)

/-- **Positive scaling** of the planar perimeter: `perimeter (rK) = r · perimeter K`. -/
@[simp] theorem planarPerimeter_scalePos
    (K : ConvexBody Plane) {r : ℝ} (hr : 0 < r) :
    planarPerimeter (K.scalePos r hr) = r * planarPerimeter K := by
  simp only [planarPerimeter_def]
  rw [show (∫ θ in (0:ℝ)..(2 * Real.pi), widthFunction (K.scalePos r hr) (circleVec θ))
        = ∫ θ in (0:ℝ)..(2 * Real.pi), r * widthFunction K (circleVec θ) from
      intervalIntegral.integral_congr (fun θ _ => widthFunction_scalePos_body K hr (circleVec θ)),
    intervalIntegral.integral_const_mul]
  ring

/-- **Reflection / negation invariance** of the planar perimeter. -/
@[simp] theorem planarPerimeter_neg
    (K : ConvexBody Plane) :
    planarPerimeter K.neg = planarPerimeter K := by
  simp only [planarPerimeter_def]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  exact widthFunction_neg_body K (circleVec θ)

end NRR.Geometry
