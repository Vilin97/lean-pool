/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.CanonicalCellContinuity

/-!
# `NRR.EMP.VariableBody.Children` — canonical children in the lower-area `BodySpace`

Each canonical power cell `canonicalCell sites hA hn z i` has area exactly `z.1.body.area / n`, and
`z.1.body.area ≥ A`, so the cell area is at least `A / n`. This lets us package every canonical cell
as a genuine element of the lower-area hyperspace `BodySpace K (A / (n : ℝ))`.

* `child` — the canonical cell packaged in `BodySpace K (A / (n : ℝ))`.
* `child_body`, `child_area_eq`, `child_subset_parent`, `child_lower_area`,
  `child_lower_bound_pos` — the basic bookkeeping of the child body.
* `continuous_child`, `continuous_children` — Hausdorff continuity of the child family, obtained by
  packaging `continuous_canonicalCell` through the subtype constructor of `BodySpace`.
* `continuous_child_area` — continuity of the child area, from the continuous area map.
* `continuous_child_perimeter`, `continuous_child_perimeters` — continuity of the child perimeter as
  a direct composition through the solid bridge `BodySpace.toGeometryConvexBody`.
-/

@[expose] public section

open NRR NRR.Geometry NRR.Geometry.ConvexBody
open Filter Topology

namespace NRR.EMP.VariableBody

variable {X : Type*} [MetricSpace X] [CompactSpace X] {n : ℕ}
variable {K : Geometry.ConvexBody Plane} {A : ℝ}
variable (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)

/-- **Positivity of the child lower area.** When `0 < A` and `0 < n`, the lower area `A / n` of the
child hyperspace is strictly positive. -/
theorem child_lower_bound_pos (hA : 0 < A) (hn : 0 < n) :
    0 < A / (n : ℝ) :=
  div_pos hA (by exact_mod_cast hn)

/-- The **canonical child** of site `i`: the canonical power cell of the parameter `z`, packaged as
an element of the lower-area hyperspace `BodySpace K (A / (n : ℝ))`. The lower-area condition
follows
from `A ≤ z.1.body.area`, `0 < n`, and `canonicalCell.area = z.1.body.area / n`. -/
noncomputable def child
    (z : BodySpace K A × X) (i : Fin n) :
    BodySpace K (A / (n : ℝ)) :=
  ⟨canonicalCell sites hA hn z i, by
    rw [canonicalCell_area_eq_target]
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    gcongr
    exact z.1.area_lower⟩

omit [CompactSpace X] in
@[simp] theorem child_body
    (z : BodySpace K A × X) (i : Fin n) :
    (child sites hA hn z i).body = canonicalCell sites hA hn z i :=
  rfl

omit [CompactSpace X] in
theorem child_area_eq
    (z : BodySpace K A × X) (i : Fin n) :
    (child sites hA hn z i).body.area = z.1.body.area / (n : ℝ) := by
  rw [child_body]
  exact canonicalCell_area_eq_target sites hA hn z i

omit [CompactSpace X] in
theorem child_subset_parent
    (z : BodySpace K A × X) (i : Fin n) :
    ((child sites hA hn z i).body : Set Plane) ⊆ (K : Set Plane) :=
  (canonicalCell sites hA hn z i).subset_parent

omit [CompactSpace X] in
theorem child_lower_area
    (z : BodySpace K A × X) (i : Fin n) :
    A / (n : ℝ) ≤ (child sites hA hn z i).body.area :=
  (child sites hA hn z i).area_lower

/-- **Continuity of the child.** Each canonical child depends continuously on the parameter, valued
in the compact Hausdorff hyperspace `BodySpace K (A / (n : ℝ))`. -/
theorem continuous_child (i : Fin n) :
    Continuous fun z : BodySpace K A × X =>
      child sites hA hn z i :=
  (continuous_canonicalCell sites hA hn i).subtype_mk _

/-- **Continuity of the child family.** The whole finite family of canonical children depends
continuously on the parameter. -/
theorem continuous_children :
    Continuous fun z : BodySpace K A × X =>
      fun i => child sites hA hn z i :=
  continuous_pi (fun i => continuous_child sites hA hn i)

/-- **Continuity of the child area.** The area of each child varies continuously in the parameter,
by composing `continuous_child` with the continuous area map. -/
theorem continuous_child_area (i : Fin n) :
    Continuous fun z : BodySpace K A × X =>
      (child sites hA hn z i).body.area :=
  (ConvexSubbody.continuous_area K).comp
    ((BodySpace.continuous_body).comp (continuous_child sites hA hn i))

/-- **Continuity of the child perimeter.** The planar (Cauchy) perimeter of each child's solid
bridge varies continuously, as a direct composition:
`continuous_child`, `BodySpace.continuous_perimeter` at lower bound `A / (n : ℝ)`. -/
theorem continuous_child_perimeter (i : Fin n) :
    Continuous fun z : BodySpace K A × X =>
      (BodySpace.toGeometryConvexBody
        (child sites hA hn z i)
        (child_lower_bound_pos hA hn)).perimeter :=
  (BodySpace.continuous_perimeter (child_lower_bound_pos hA hn)).comp
    (continuous_child sites hA hn i)

/-- **Continuity of the child perimeter family.** The whole finite family of child perimeters
depends continuously on the parameter. -/
theorem continuous_child_perimeters :
    Continuous fun z : BodySpace K A × X =>
      fun i =>
        (BodySpace.toGeometryConvexBody
          (child sites hA hn z i)
          (child_lower_bound_pos hA hn)).perimeter :=
  continuous_pi (fun i => continuous_child_perimeter sites hA hn i)

end NRR.EMP.VariableBody
