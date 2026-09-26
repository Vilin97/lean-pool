/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarCircle

/-!
# `NRR.Geometry.ConvexBody` — the planar Cauchy perimeter

This module defines the **planar perimeter** of a convex body via **Cauchy's width formula**,
using the deterministic angle parameterization of the unit circle from `PlanarCircle.lean`.
Directions are parameterized over `[0, 2π]` by `θ ↦ (cos θ, sin θ)` (`circleVec`), and the
perimeter is the (normalized) interval integral of the width function along that parameterization:

```text
perimeter K = (1 / 2) * ∫ θ in 0..2π, w_K(circleVec θ).
```

The normalization factor `1 / 2` accounts for the fact that the width function is *even*
(each direction and its antipode are counted, so the integral over `[0, 2π]` double-counts the
projected extent), giving the classical Cauchy perimeter.

## Design notes

* We reuse `circleVec` and `continuous_circleVec` from the project (`PlanarCircle.lean`), and
 the width-function API (`widthFunction`, `widthFunction_nonneg`, `continuous_widthFunction`,
 `supportFunction_congr`) from preceding modules.
* Integrability of the integrand is inherited from continuity on the compact interval `[0, 2π]`
 (`Continuous.intervalIntegrable`); this is exactly `intervalIntegrable_width_circleVec` from
 the project, restated here as part of this module's API.
* Nonnegativity follows because the factor `1 / 2` is nonnegative and the integrand is
 pointwise nonnegative (`widthFunction_nonneg`), so `intervalIntegral.integral_nonneg` applies
 (the endpoints satisfy `0 ≤ 2π`).
* Congruence (equal underlying sets ⇒ equal perimeter) follows from `supportFunction_congr`,
 which makes the whole integrand pointwise equal.

## Import policy

Only `PlanarCircle.lean` is imported; it transitively provides all of Mathlib together with the
`circleVec` and width-function APIs. No extra imports are required.
-/

@[expose] public section

namespace NRR.Geometry

open Real MeasureTheory ConvexBody

/-- The **planar perimeter** of a convex body `K`, defined by Cauchy's width formula as the
normalized interval integral of the width function along the angle parameterization
`circleVec` over `[0, 2π]`. -/
noncomputable def planarPerimeter (K : ConvexBody Plane) : ℝ :=
  (1 / 2 : ℝ) * ∫ θ in 0..(2 * Real.pi),
    widthFunction K (circleVec θ)

/-- Definitional unfolding of `planarPerimeter`. -/
theorem planarPerimeter_def
    (K : ConvexBody Plane) :
    planarPerimeter K =
      (1 / 2 : ℝ) * ∫ θ in 0..(2 * Real.pi),
        widthFunction K (circleVec θ) :=
  rfl

/-- The Cauchy perimeter integrand `θ ↦ w_K(circleVec θ)` is continuous. -/
theorem continuous_planarPerimeter_integrand
    (K : ConvexBody Plane) :
    Continuous fun θ : ℝ => widthFunction K (circleVec θ) :=
  K.continuous_widthFunction.comp continuous_circleVec

/-- The Cauchy perimeter integrand is interval-integrable on `[0, 2π]`. -/
theorem intervalIntegrable_planarPerimeter_integrand
    (K : ConvexBody Plane) :
    IntervalIntegrable
      (fun θ : ℝ => widthFunction K (circleVec θ))
      volume 0 (2 * Real.pi) :=
  (continuous_planarPerimeter_integrand K).intervalIntegrable 0 (2 * Real.pi)

/-- The planar perimeter is nonnegative. -/
theorem planarPerimeter_nonneg
    (K : ConvexBody Plane) :
    0 ≤ planarPerimeter K := by
  rw [planarPerimeter_def]
  apply mul_nonneg
  · norm_num
  · apply intervalIntegral.integral_nonneg
    · positivity
    · intro θ _
      exact widthFunction_nonneg K (circleVec θ)

/-- **Congruence.** The planar perimeter depends only on the underlying set of the convex body. -/
theorem planarPerimeter_congr
    {K L : ConvexBody Plane} (h : (K : Set Plane) = (L : Set Plane)) :
    planarPerimeter K = planarPerimeter L := by
  simp only [planarPerimeter_def]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [widthFunction_def, supportFunction_congr h]

end NRR.Geometry
