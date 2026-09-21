/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.Compactness
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.AreaContinuity
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PositiveAreaInterior

/-!
# `NRR.BodySpace` — lower-area subspace and the positive-area solid bridge

This module studies the closed lower-area subspace

```
NRR.BodySpace (K : Geometry.ConvexBody Plane) (A : ℝ) =
  {C : ConvexSubbody K // A ≤ C.area}
```

of the fixed-parent hyperspace `ConvexSubbody K`. Its elements are convex subbodies of `K` whose
area is at least `A`.

* The lower-area condition is closed (`continuous_area` and `isClosed_Ici`), so `BodySpace K A`
  is a closed subtype of the compact hyperspace `ConvexSubbody K`, hence compact.
* When `A > 0` every element has strictly positive area, so its carrier has nonempty interior and
  it can be repackaged as a solid geometry body `Geometry.ConvexBody Plane`. This solid bridge is
  continuous for the induced Hausdorff topology (via the named forgetful map
  `Geometry.ConvexBody.toMathlib`).
* Membership and a.e. indicator convergence lemmas are lifted from `ConvexSubbody` by composing
  with the continuous projection `BodySpace.body`.
-/

open MeasureTheory Metric Filter Topology

open NRR.Geometry

namespace NRR

namespace BodySpace

variable {K : Geometry.ConvexBody Plane} {A : ℝ}

/-- The inherited **Hausdorff metric** on `BodySpace K A`, taken as a subtype of the hyperspace
`ConvexSubbody K`. Because `BodySpace` is a `def` over a subtype, this instance is stated
explicitly rather than inferred. -/
noncomputable instance instMetricSpace : MetricSpace (BodySpace K A) :=
  inferInstanceAs (MetricSpace {C : ConvexSubbody K // A ≤ C.area})

/-- `BodySpace K A` is Hausdorff (inherited from its metric). -/
instance instT2Space : T2Space (BodySpace K A) :=
  inferInstanceAs (T2Space {C : ConvexSubbody K // A ≤ C.area})

/-- The underlying convex subbody of an element of `BodySpace K A`. -/
def body (C : BodySpace K A) : ConvexSubbody K := C.1

/-- The area lower bound satisfied by every element of `BodySpace K A`. -/
theorem area_lower (C : BodySpace K A) :
    A ≤ C.body.area :=
  C.2

/-- The projection to the underlying subbody is continuous (it is the subtype inclusion). -/
theorem continuous_body :
    Continuous (BodySpace.body (K := K) (A := A)) :=
  continuous_subtype_val

/-- **Closedness of the lower-area condition.** The locus of subbodies with area at least `A` is
closed in the hyperspace `ConvexSubbody K`, since the area functional is continuous. -/
theorem isClosed_lowerArea :
    IsClosed {C : ConvexSubbody K | A ≤ C.area} :=
  isClosed_le continuous_const (ConvexSubbody.continuous_area K)

/-- **Compactness of `BodySpace K A`.** The whole space is compact: it is a closed subtype of the
compact hyperspace `ConvexSubbody K`. -/
theorem isCompact_univ :
    IsCompact (Set.univ : Set (BodySpace K A)) :=
  isCompact_iff_isCompact_univ.mp (isClosed_lowerArea.isCompact)

/-- The canonical **compact-space** instance on `BodySpace K A`. -/
noncomputable instance instCompactSpace :
    CompactSpace (BodySpace K A) :=
  ⟨isCompact_univ⟩

/-- **Positive area.** When `A > 0` every element of `BodySpace K A` has strictly positive area. -/
theorem area_pos
    (hA : 0 < A) (C : BodySpace K A) :
    0 < C.body.area :=
  lt_of_lt_of_le hA C.area_lower

/-- **Positive-area solid bridge.** When `A > 0`, an element of `BodySpace K A` repackages as a
solid geometry body: its carrier is convex and compact (from the underlying subbody) and has
nonempty interior (from positive area). -/
noncomputable def toGeometryConvexBody
    (C : BodySpace K A) (hA : 0 < A) :
    Geometry.ConvexBody Plane where
  carrier := (C.body : Set Plane)
  convex' := C.body.convex
  isCompact' := C.body.isCompact
  interior_nonempty' :=
    Geometry.ConvexBody.interior_nonempty_of_convex_compact_positive_area
      C.body.convex C.body.isCompact (area_pos hA C)

@[simp] theorem toGeometryConvexBody_carrier
    (C : BodySpace K A) (hA : 0 < A) :
    (C.toGeometryConvexBody hA : Set Plane) =
      (C.body : Set Plane) :=
  rfl

@[simp] theorem toGeometryConvexBody_area
    (C : BodySpace K A) (hA : 0 < A) :
    (C.toGeometryConvexBody hA).area = C.body.area :=
  rfl

/-- **Continuity of the solid bridge.** The map sending an element of `BodySpace K A` to its solid
geometry body is continuous for the induced Hausdorff topology on `Geometry.ConvexBody Plane`.
By `continuous_induced_rng` it suffices to be continuous after the named forgetful map
`Geometry.ConvexBody.toMathlib`, and the resulting composite is the continuous projection to the
underlying root Mathlib body. -/
theorem continuous_toGeometryConvexBody
    (hA : 0 < A) :
    Continuous fun C : BodySpace K A =>
      C.toGeometryConvexBody hA := by
  rw [continuous_induced_rng]
  have h : (Geometry.ConvexBody.toMathlib ∘
      fun C : BodySpace K A => C.toGeometryConvexBody hA)
      = fun C : BodySpace K A => (C.body.body : _root_.ConvexBody Plane) := by
    funext C
    exact _root_.ConvexBody.ext rfl
  rw [h]
  exact continuous_subtype_val.comp continuous_body

/-- **Frontier-complement equivalence** on `BodySpace K A`: off the frontier of the limit body,
membership in the approximating bodies eventually agrees with membership in the limit body. -/
theorem eventually_mem_iff_of_not_mem_frontier
    {α : Type*} {l : Filter α}
    {C : α → BodySpace K A} {C₀ : BodySpace K A}
    (hC : Tendsto C l (𝓝 C₀))
    {x : Plane} (hx : x ∉ frontier (C₀.body : Set Plane)) :
    ∀ᶠ a in l,
      (x ∈ ((C a).body : Set Plane) ↔
       x ∈ (C₀.body : Set Plane)) :=
  ConvexSubbody.eventually_mem_iff_of_not_mem_frontier
    ((continuous_body.tendsto C₀).comp hC) hx

/-- **Almost-everywhere indicator convergence** on `BodySpace K A`: along a Hausdorff-convergent
family the `0/1` carrier indicators converge pointwise almost everywhere. -/
theorem tendsto_mem_ae
    {α : Type*} {l : Filter α}
    {C : α → BodySpace K A} {C₀ : BodySpace K A}
    (hC : Tendsto C l (𝓝 C₀)) :
    ∀ᵐ x ∂volume,
      Tendsto
        (fun a =>
          ((C a).body : Set Plane).indicator (fun _ => (1 : ℝ)) x)
        l
        (𝓝
          ((C₀.body : Set Plane).indicator (fun _ => (1 : ℝ)) x)) :=
  ConvexSubbody.tendsto_indicator_ae ((continuous_body.tendsto C₀).comp hC)

end BodySpace

end NRR
