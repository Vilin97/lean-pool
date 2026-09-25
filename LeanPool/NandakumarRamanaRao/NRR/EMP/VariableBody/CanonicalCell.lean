/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.AreaVector
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.NormalizedWeightContinuity

/-!
# `NRR.EMP.VariableBody.CanonicalCell` — the canonical variable-body power cell

For a compact metric parameter space `X` carrying a continuous site family
`sites : SiteFamily X n`, a positive lower area `A`, and `0 < n`, we bundle the restricted power
cell of site `i`, computed with the canonical normalized equal-area weight, as a genuine convex
subbody of the fixed parent `K`.

The carrier of `canonicalCell sites hA hn z i` is exactly the set-level power cell

```
cellSet hA z.1 (sites z.2) (normalizedWeight hA hn z.1 (sites z.2)) i,
```

which is convex and compact by the general cell API and nonempty because the equal-area property
gives it positive area (indeed nonempty interior). The cell area equals the target average area
`z.1.body.area / n`.
-/

@[expose] public section

open NRR NRR.Geometry NRR.Geometry.ConvexBody

namespace NRR.EMP.VariableBody

variable {X : Type*} [MetricSpace X] [CompactSpace X] {n : ℕ}
variable {K : Geometry.ConvexBody Plane} {A : ℝ}

omit [CompactSpace X]

/-- The canonical power cell has nonempty interior: the equal-area property of the selected weight
forces positive cell area, hence nonempty interior by the project's positive-area theorem. -/
theorem canonicalCell_interior_nonempty
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (z : BodySpace K A × X) (i : Fin n) :
    (interior (cellSet hA z.1 (sites z.2)
      (normalizedWeight hA hn z.1 (sites z.2)) i)).Nonempty := by
  have hK : 0 < (solidBody hA z.1).area := by simpa using BodySpace.area_pos hA z.1
  have hw := normalizedWeight_isEqualArea hA hn z.1 (sites z.2)
  exact PowerDiagram.bodyCellSet_interior_nonempty_of_equalArea
    (solidBody hA z.1) (sites z.2).pts _ hn hK hw i

/-- The **canonical variable-body power cell** of site `i`: the restricted power cell computed with
the canonical normalized equal-area weight, bundled as a convex subbody of the fixed parent `K`. -/
noncomputable def canonicalCell
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (z : BodySpace K A × X) (i : Fin n) :
    ConvexSubbody K :=
  ⟨{ carrier := cellSet hA z.1 (sites z.2) (normalizedWeight hA hn z.1 (sites z.2)) i
     convex' := cellSet_convex hA z.1 (sites z.2) _ i
     isCompact' := cellSet_isCompact hA z.1 (sites z.2) _ i
     nonempty' := (canonicalCell_interior_nonempty sites hA hn z i).mono interior_subset },
   cellSet_subset_parent hA z.1 (sites z.2) _ i⟩

theorem canonicalCell_carrier
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (z : BodySpace K A × X) (i : Fin n) :
    ((canonicalCell sites hA hn z i).body : Set Plane) =
      cellSet hA z.1 (sites z.2)
        (normalizedWeight hA hn z.1 (sites z.2)) i :=
  rfl

theorem canonicalCell_area
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (z : BodySpace K A × X) (i : Fin n) :
    (canonicalCell sites hA hn z i).area =
      cellArea hA z.1 (sites z.2)
        (normalizedWeight hA hn z.1 (sites z.2)) i :=
  rfl

theorem canonicalCell_area_eq_target
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (z : BodySpace K A × X) (i : Fin n) :
    (canonicalCell sites hA hn z i).area =
      z.1.body.area / (n : ℝ) := by
  rw [canonicalCell_area]
  have h := congrFun (areaVec_normalizedWeight_eq_target sites hA hn z) i
  simpa [areaVec_apply, targetArea] using h

end NRR.EMP.VariableBody
