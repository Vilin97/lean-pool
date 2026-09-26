/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
public import LeanPool.NandakumarRamanaRao.NRR.SupportFunction
public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeter
public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeterBasic
public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeterTransform
public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeterMonotonicity
public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeterContinuity

/-!
# `NRR.AreaPerimeter` — planar Cauchy perimeter

This module exposes the public perimeter of a planar convex body as the implemented Cauchy
mean-width integral. It provides nonnegativity, the integral formula, monotonicity, and continuity
for explicitly parameterized convex-body families with jointly continuous angle-width functions.

No topology on the type of all convex bodies is assumed.
-/

@[expose] public section

open NRR
open scoped RealInnerProductSpace

namespace NRR.Geometry.ConvexBody

/-- **Perimeter** of a planar convex body, defined by Cauchy's mean-width formula: an alias of
the implemented `NRR.Geometry.planarPerimeter`. -/
noncomputable def perimeter (K : ConvexBody Plane) : ℝ :=
  NRR.Geometry.planarPerimeter K

/-- Definitional unfolding of `perimeter`. -/
theorem perimeter_def (K : ConvexBody Plane) :
    K.perimeter = NRR.Geometry.planarPerimeter K := rfl

/-- The perimeter is nonnegative. -/
theorem perimeter_nonneg (K : ConvexBody Plane) : 0 ≤ K.perimeter :=
  NRR.Geometry.planarPerimeter_nonneg K

/-- **Cauchy's formula**: `perimeter K = ½ ∫₀^{2π} width_K(circleVec θ) dθ`, integrating over
unit directions parametrized by angle. -/
theorem perimeter_eq_integral_width (K : ConvexBody Plane) :
    K.perimeter =
      (1 / 2 : ℝ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        K.width (Geometry.circleVec θ) := by
  simp only [perimeter_def, NRR.Geometry.planarPerimeter_def, width_eq]

/-- Monotonicity of perimeter under inclusion of convex bodies. -/
theorem perimeter_mono {K L : ConvexBody Plane} (h : (K : Set Plane) ⊆ (L : Set Plane)) :
    K.perimeter ≤ L.perimeter :=
  NRR.Geometry.planarPerimeter_mono h

/-- **Continuity of perimeter** for a family of convex bodies whose angle-width integrand is
jointly continuous. There is no metric topology on `Geometry.ConvexBody`; continuity is therefore
stated for an
explicit family with a jointly continuous angle-width integrand. -/
theorem continuous_perimeter_of_angleWidth
    {α : Type*} [TopologicalSpace α]
    (K : α → ConvexBody Plane)
    (hK : Geometry.AngleWidthContinuousFamily K) :
    Continuous fun a => (K a).perimeter :=
  NRR.Geometry.continuous_planarPerimeter_of_angleWidth K hK

end NRR.Geometry.ConvexBody

namespace NRR.SolidConvexBody

/-- A solid convex body has strictly positive perimeter, wrapping the implemented
`planarPerimeter_pos`. -/
theorem perimeter_pos (K : SolidConvexBody) : 0 < K.toConvexBody.perimeter :=
  NRR.Geometry.planarPerimeter_pos K.toConvexBody

end NRR.SolidConvexBody
