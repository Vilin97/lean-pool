/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.Phase1Interface
public import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.BodyCells
public import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeights
public import LeanPool.NandakumarRamanaRao.NRR.EMP.WeightSpace
public import LeanPool.NandakumarRamanaRao.NRR.EMP.NormalizedWeightSelection

/-!
# `NRR.EMP.VariableBody.Basic` — variable-body power-diagram vocabulary

This module opens the variable-body layer of the Akopyan–Avvakumov–Karasev power-partition
development. A parameter is a positive-area subbody `C : BodySpace K A` of a fixed planar parent
`K`, together with a configuration `s : Config n` and a weight vector `w : Fin n → ℝ`.

Every declaration here is a thin wrapper that specializes the existing fixed-body power-diagram and
normalized-weight APIs to the solid body `C.toGeometryConvexBody hA`. No new power diagram,
configuration space, weight selection, or convex-body topology is introduced.
-/

@[expose] public section

open NRR NRR.Geometry NRR.Geometry.ConvexBody

namespace NRR.EMP.VariableBody

/-- The **solid body** of a positive-area subbody parameter: the fixed-body geometry body obtained
from `C : BodySpace K A` via the positive-area body bridge. -/
noncomputable def solidBody
    {K : Geometry.ConvexBody Plane} {A : ℝ}
    (hA : 0 < A) (C : BodySpace K A) :
    Geometry.ConvexBody Plane :=
  C.toGeometryConvexBody hA

/-- The **restricted power cell** of site `i` inside the variable body `C`, as a set. -/
def cellSet
    {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}
    (hA : 0 < A) (C : BodySpace K A)
    (s : Config n) (w : Fin n → ℝ) (i : Fin n) :
    Set Plane :=
  PowerDiagram.bodyCellSet (solidBody hA C) s.pts w i

/-- The **area** of the restricted power cell of site `i` inside the variable body `C`. -/
noncomputable def cellArea
    {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}
    (hA : 0 < A) (C : BodySpace K A)
    (s : Config n) (w : Fin n → ℝ) (i : Fin n) :
    ℝ :=
  PowerDiagram.bodyCellArea (solidBody hA C) s.pts w i

/-- `w` is an **equal-area weight** for the sites `s` inside the variable body `C`: every restricted
power cell has the average area `C.area / n`. -/
def IsEqualAreaWeight
    {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}
    (hA : 0 < A) (C : BodySpace K A)
    (s : Config n) (w : Fin n → ℝ) : Prop :=
  EMP.IsEqualAreaWeight (solidBody hA C) s.pts w

/-- `w` is a **normalized equal-area weight**: equal-area for `s` in `C` and normalized
(`∑ i, w i = 0`). -/
def IsNormalizedEqualAreaWeight
    {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}
    (hA : 0 < A) (C : BodySpace K A)
    (s : Config n) (w : Fin n → ℝ) : Prop :=
  IsEqualAreaWeight hA C s w ∧ EMP.WeightNormalized w

/-- The **canonical normalized equal-area weight** for the sites `s` inside the variable body `C`,
selected by the fixed-body existence/uniqueness core applied to `solidBody hA C`. -/
noncomputable def normalizedWeight
    {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}
    (hA : 0 < A) (hn : 0 < n)
    (C : BodySpace K A) (s : Config n) :
    Fin n → ℝ :=
  EMP.normalizedWeight (solidBody hA C) s.pts hn s.injective_pts

@[simp] theorem solidBody_carrier
    {K : Geometry.ConvexBody Plane} {A : ℝ}
    (hA : 0 < A) (C : BodySpace K A) :
    (solidBody hA C : Set Plane) = (C.body : Set Plane) :=
  rfl

@[simp] theorem solidBody_area
    {K : Geometry.ConvexBody Plane} {A : ℝ}
    (hA : 0 < A) (C : BodySpace K A) :
    (solidBody hA C).area = C.body.area :=
  rfl

@[simp] theorem cellSet_def
    {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}
    (hA : 0 < A) (C : BodySpace K A)
    (s : Config n) (w : Fin n → ℝ) (i : Fin n) :
    cellSet hA C s w i =
      PowerDiagram.bodyCellSet (solidBody hA C) s.pts w i :=
  rfl

@[simp] theorem cellArea_def
    {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}
    (hA : 0 < A) (C : BodySpace K A)
    (s : Config n) (w : Fin n → ℝ) (i : Fin n) :
    cellArea hA C s w i =
      PowerDiagram.bodyCellArea (solidBody hA C) s.pts w i :=
  rfl

theorem cellSet_subset_body
    {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}
    (hA : 0 < A) (C : BodySpace K A)
    (s : Config n) (w : Fin n → ℝ) (i : Fin n) :
    cellSet hA C s w i ⊆ (C.body : Set Plane) := by
  simp only [cellSet_def]
  exact PowerDiagram.bodyCellSet_subset_body (solidBody hA C) s.pts w i

theorem cellSet_subset_parent
    {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}
    (hA : 0 < A) (C : BodySpace K A)
    (s : Config n) (w : Fin n → ℝ) (i : Fin n) :
    cellSet hA C s w i ⊆ (K : Set Plane) :=
  (cellSet_subset_body hA C s w i).trans C.body.subset_parent

theorem cellSet_convex
    {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}
    (hA : 0 < A) (C : BodySpace K A)
    (s : Config n) (w : Fin n → ℝ) (i : Fin n) :
    Convex ℝ (cellSet hA C s w i) :=
  PowerDiagram.bodyCellSet_convex (solidBody hA C) s.pts w i

theorem cellSet_isCompact
    {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}
    (hA : 0 < A) (C : BodySpace K A)
    (s : Config n) (w : Fin n → ℝ) (i : Fin n) :
    IsCompact (cellSet hA C s w i) :=
  PowerDiagram.bodyCellSet_isCompact (solidBody hA C) s.pts w i

theorem normalizedWeight_isEqualArea
    {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}
    (hA : 0 < A) (hn : 0 < n)
    (C : BodySpace K A) (s : Config n) :
    IsEqualAreaWeight hA C s (normalizedWeight hA hn C s) :=
  EMP.normalizedWeight_isEqualArea (solidBody hA C) s.pts hn s.injective_pts

theorem normalizedWeight_normalized
    {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}
    (hA : 0 < A) (hn : 0 < n)
    (C : BodySpace K A) (s : Config n) :
    EMP.WeightNormalized (normalizedWeight hA hn C s) :=
  EMP.normalizedWeight_normalized (solidBody hA C) s.pts hn s.injective_pts

theorem normalizedWeight_unique
    {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}
    (hA : 0 < A) (hn : 0 < n)
    (C : BodySpace K A) (s : Config n)
    {w : Fin n → ℝ}
    (hw : IsNormalizedEqualAreaWeight hA C s w) :
    w = normalizedWeight hA hn C s :=
  EMP.normalizedWeight_unique (solidBody hA C) s.pts hn s.injective_pts hw.1 hw.2

end NRR.EMP.VariableBody
