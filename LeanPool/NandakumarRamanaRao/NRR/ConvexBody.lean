/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Analysis.Convex.Body
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Interior
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarCircle

/-!
# `NRR.ConvexBody` — public convex‑body API (unified over the geometry layer)

This module is the **public entry point** for planar convex bodies. It no longer maintains
an independent convex‑body type: everything is a thin wrapper/alias over the implemented
geometry layer

```
NRR.Geometry.ConvexBody (NRR/Geometry/ConvexBody/*)
```

whose bundled bodies are compact, convex, and **solid** (nonempty interior) by construction.

## Public surface

* `NRR.E2` — the Euclidean plane, an alias of `Geometry.Plane`.
* `NRR.Body` — planar convex bodies, an alias of `Geometry.ConvexBody E2`.
* Area API in `NRR.Geometry.ConvexBody`: `area`, `IsSolid`, `isSolid`, `area_nonneg`,
 `area_lt_top`, and the robust positivity lemma `area_pos_of_contains_closedBall`.
* `NRR.SolidConvexBody` — a bundled solid body wrapping `Geometry.ConvexBody`, with
 `ofConvexBody`, `coe_ofConvexBody`, and the derived positivity `area_pos_of_solid`
 (also exposed as `area_pos`).

Every geometry `ConvexBody` is already solid, so `IsSolid`/`SolidConvexBody` are provided for
downstream compatibility rather than as genuine extra data.
-/

open MeasureTheory

namespace NRR

/-- The Euclidean plane `ℝ²`, the ambient space fixed throughout the development.
Definitional alias of `NRR.Geometry.Plane`. -/
abbrev E2 := Geometry.Plane

/-- Planar convex bodies. Definitional alias of the implemented geometry convex‑body type
`NRR.Geometry.ConvexBody E2`. -/
abbrev Body := Geometry.ConvexBody E2

end NRR

namespace NRR.Geometry.ConvexBody

/-- The **forgetful map** from a solid geometry convex body to Mathlib's root `ConvexBody`,
dropping the solidity (nonempty-interior) witness and keeping only compactness, convexity, and
nonemptiness. This names the map inducing the Hausdorff-metric topology below. -/
def toMathlib
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : NRR.Geometry.ConvexBody E) :
    _root_.ConvexBody E :=
  ⟨(K : Set E), K.convex, K.isCompact, K.nonempty⟩

@[simp] theorem toMathlib_carrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : NRR.Geometry.ConvexBody E) :
    ((K.toMathlib : _root_.ConvexBody E) : Set E) = (K : Set E) :=
  rfl

end NRR.Geometry.ConvexBody

/-- The **Hausdorff‑metric topology** on geometry convex bodies, induced from Mathlib's
`ConvexBody` metric via the named forgetful map `Geometry.ConvexBody.toMathlib` that drops the
solidity witness. This lets the public API speak about Hausdorff continuity of body‑valued and
body‑indexed functionals. -/
noncomputable instance instTopologicalSpaceGeometryConvexBody
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    TopologicalSpace (NRR.Geometry.ConvexBody E) :=
  TopologicalSpace.induced NRR.Geometry.ConvexBody.toMathlib inferInstance

namespace NRR.Geometry.ConvexBody

open MeasureTheory

/-- **Area** of a planar convex body: the (real‑valued) Lebesgue measure of its carrier. -/
noncomputable def area (K : ConvexBody Plane) : ℝ :=
  (volume (K : Set Plane)).toReal

/-- **Solidity**: the body has nonempty interior. Every geometry convex body satisfies this
by construction (see `isSolid`); the predicate is kept for downstream compatibility. -/
def IsSolid (K : ConvexBody Plane) : Prop :=
  (interior (K : Set Plane)).Nonempty

/-- Every geometry convex body is solid: it has nonempty interior by construction. -/
theorem isSolid (K : ConvexBody Plane) : K.IsSolid :=
  K.interior_nonempty

/-- The Lebesgue measure of a convex body is finite (its carrier is compact). -/
theorem area_lt_top (K : ConvexBody Plane) : volume (K : Set Plane) < ⊤ :=
  K.isCompact.measure_lt_top

/-- The area of a convex body is nonnegative. -/
theorem area_nonneg (K : ConvexBody Plane) : 0 ≤ K.area :=
  ENNReal.toReal_nonneg

/-- **Robust positivity.** If a convex body contains a closed ball of positive radius then it
has strictly positive area. -/
theorem area_pos_of_contains_closedBall
    (K : ConvexBody Plane) {x : Plane} {r : ℝ}
    (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ (K : Set Plane)) :
    0 < K.area := by
  have hball_pos : 0 < volume (Metric.closedBall x r) :=
    lt_of_lt_of_le (Metric.measure_ball_pos volume x hr)
      (measure_mono Metric.ball_subset_closedBall)
  have hpos : 0 < volume (K : Set Plane) :=
    lt_of_lt_of_le hball_pos (measure_mono hball)
  exact ENNReal.toReal_pos hpos.ne' K.area_lt_top.ne

end NRR.Geometry.ConvexBody

namespace NRR

/-- A **solid convex body**: a bundled `Geometry.ConvexBody Geometry.Plane` together with the
(automatic) solidity witness. This is the input type of the fair‑partition theorem. -/
structure SolidConvexBody where
  /-- The underlying convex body. -/
  toConvexBody : Geometry.ConvexBody Geometry.Plane
  /-- The body has nonempty interior. -/
  isSolid : toConvexBody.IsSolid

namespace SolidConvexBody

/-- Bundle any geometry convex body as a `SolidConvexBody`: geometry bodies are always solid. -/
def ofConvexBody (K : Geometry.ConvexBody Geometry.Plane) : SolidConvexBody :=
  ⟨K, K.isSolid⟩

@[simp] theorem coe_ofConvexBody (K : Geometry.ConvexBody Geometry.Plane) :
    (SolidConvexBody.ofConvexBody K).toConvexBody = K := rfl

/-- A solid convex body has strictly positive area, derived from the interior closed‑ball
theorem of the geometry layer (`exists_closedBall_subset`) and
`area_pos_of_contains_closedBall`. -/
theorem area_pos_of_solid (K : SolidConvexBody) : 0 < K.toConvexBody.area := by
  obtain ⟨x, r, hr, hsub⟩ := K.toConvexBody.exists_closedBall_subset
  exact Geometry.ConvexBody.area_pos_of_contains_closedBall _ hr hsub

/-- A solid convex body has strictly positive area. (Alias of `area_pos_of_solid`.) -/
theorem area_pos (K : SolidConvexBody) : 0 < K.toConvexBody.area :=
  K.area_pos_of_solid

end SolidConvexBody

end NRR
