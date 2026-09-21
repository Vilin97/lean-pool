/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.SupportWidthContinuity
import LeanPool.NandakumarRamanaRao.NRR.AreaPerimeter

/-!
# `NRR.BodySpace` — perimeter continuity for positive lower area

For the lower-area subspace `BodySpace K A` with `A > 0`, every element repackages as a solid
geometry body via `BodySpace.toGeometryConvexBody`, and this solid bridge is Hausdorff-continuous.
Prompt `09` recorded that the bridge is a `WidthContinuousFamily`; the planar (Cauchy) perimeter of
a width-continuous family is continuous (`continuous_perimeter_of_angleWidth`), so the perimeter of
the solid bridge is continuous in the subbody.

This combines the analytic ingredients: area (`BodySpace.continuous_toGeometryConvexBody`
composed with `Geometry.ConvexBody.area`) and perimeter both vary continuously over the compact
lower-area hyperspace `BodySpace K A`.
-/

open Filter Topology

open NRR.Geometry

namespace NRR

namespace BodySpace

variable {K : Geometry.ConvexBody Plane} {A : ℝ}

/-- **Perimeter continuity for positive lower area.** When `A > 0`, the planar (Cauchy) perimeter
of the solid bridge `toGeometryConvexBody` is continuous over `BodySpace K A`. This applies the
angle-width perimeter-continuity theorem `Geometry.ConvexBody.continuous_perimeter_of_angleWidth`
to the width-continuous family `BodySpace.widthContinuousFamily`. -/
theorem continuous_perimeter
    (hA : 0 < A) :
    Continuous fun C : BodySpace K A =>
      (C.toGeometryConvexBody hA).perimeter :=
  Geometry.ConvexBody.continuous_perimeter_of_angleWidth
    (fun C : BodySpace K A => C.toGeometryConvexBody hA)
    (Geometry.AngleWidthContinuousFamily.of_widthFamily
      (BodySpace.widthContinuousFamily hA))

/-- **Filter form of perimeter continuity.** Along any Hausdorff-convergent family in
`BodySpace K A` (with `A > 0`), the perimeters of the solid bridges converge to the perimeter of
the limit body. -/
theorem tendsto_perimeter
    (hA : 0 < A)
    {α : Type*} {l : Filter α}
    {C : α → BodySpace K A} {C₀ : BodySpace K A}
    (hC : Tendsto C l (𝓝 C₀)) :
    Tendsto
      (fun a => ((C a).toGeometryConvexBody hA).perimeter)
      l
      (𝓝 ((C₀.toGeometryConvexBody hA).perimeter)) :=
  ((continuous_perimeter hA).tendsto C₀).comp hC

end BodySpace

end NRR
