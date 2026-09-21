/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeter
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Width

/-!
# `NRR.Geometry.ConvexBody` — monotonicity of the planar perimeter

This module records the **monotonicity** of the planar (Cauchy) perimeter `planarPerimeter`
with respect to set inclusion of convex bodies:

* `planarPerimeter_mono` — `K ⊆ L ⇒ planarPerimeter K ≤ planarPerimeter L`,
* `planarPerimeter_eq_of_mutual_subset` — mutual inclusion forces equality.

## Design notes

The proof reduces to the *pointwise* width-function monotonicity `widthFunction_mono` from
`Width.lean`: for every angle `θ`, the width of `K` along `circleVec θ` is at most the width of
`L`. Applying `intervalIntegral.integral_mono_on` over the compact interval `[0, 2π]` (using the
interval-integrability of both integrands, `intervalIntegrable_planarPerimeter_integrand`) yields
the inequality of integrals, and multiplying by the nonnegative factor `1 / 2` gives the result.

Equality under mutual subset then follows from antisymmetry of `≤`.

## Import policy

Only `PlanarPerimeter.lean` and `Width.lean` are imported; they transitively provide all of
Mathlib together with the perimeter and width APIs. No extra imports are required.
-/

namespace NRR.Geometry

open Real MeasureTheory ConvexBody

/-- **Monotonicity of the planar perimeter.** A larger convex body has a larger Cauchy
perimeter. -/
theorem planarPerimeter_mono
    {K L : ConvexBody Plane}
    (hKL : (K : Set Plane) ⊆ (L : Set Plane)) :
    planarPerimeter K ≤ planarPerimeter L := by
  simp only [planarPerimeter_def]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply intervalIntegral.integral_mono_on (by positivity)
    (intervalIntegrable_planarPerimeter_integrand K)
    (intervalIntegrable_planarPerimeter_integrand L)
  intro θ _
  exact widthFunction_mono hKL (circleVec θ)

/-- **Equality from mutual inclusion.** If two convex bodies contain each other (as sets), their
planar perimeters coincide. -/
theorem planarPerimeter_eq_of_mutual_subset
    {K L : ConvexBody Plane}
    (hKL : (K : Set Plane) ⊆ (L : Set Plane))
    (hLK : (L : Set Plane) ⊆ (K : Set Plane)) :
    planarPerimeter K = planarPerimeter L :=
  le_antisymm (planarPerimeter_mono hKL) (planarPerimeter_mono hLK)

end NRR.Geometry
