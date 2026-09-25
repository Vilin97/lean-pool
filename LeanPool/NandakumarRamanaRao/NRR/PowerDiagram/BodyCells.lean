/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Tactic
public import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
public import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.Defs
public import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellGeometry

/-!
# `NRR.PowerDiagram.BodyCells` — restricted power cells as sets

Restricted power (Laguerre) cells of a convex body `K`, kept **at the set level**:

* `bodyCellSet K s w i = (K : Set Plane) ∩ cell s w i` — the restricted cell as a plain set.
* `bodyCellArea K s w i` — its area (real‑valued Lebesgue measure), defined unconditionally.

Set‑level geometry (`bodyCellSet_subset_body`, `bodyCellSet_convex`, `bodyCellSet_isCompact`)
is available without any nondegeneracy assumption.

Bundling a restricted cell as a `Geometry.ConvexBody` (which requires nonempty interior by
construction) is **only** possible when explicit interior evidence is supplied, via
`bodyCellBody K s w i hInt`. There is deliberately **no** unconditional `bodyCell`: a
restricted cell can be empty or lower‑dimensional, so it need not be a solid convex body.

Partition properties of the family `i ↦ bodyCellSet K s w i` are out of scope here.
-/

@[expose] public section

open NRR NRR.Geometry MeasureTheory

namespace NRR.PowerDiagram

variable {n : ℕ}

/-- **Restricted power cell** as a set: the intersection of the body `K` with the power cell of
site `i`. Kept at the set level (no bundling, no nondegeneracy hypothesis). -/
def bodyCellSet (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ) (i : Fin n) :
    Set Plane :=
  (K : Set Plane) ∩ cell s w i

/-- **Area** of a restricted power cell: the real‑valued Lebesgue measure of `bodyCellSet`.
Defined unconditionally (no nonempty‑interior hypothesis). -/
noncomputable def bodyCellArea (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  (volume (bodyCellSet K s w i)).toReal

/-- Definitional unfolding of `bodyCellSet`. -/
@[simp] theorem bodyCellSet_def (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (i : Fin n) :
    bodyCellSet K s w i = (K : Set Plane) ∩ cell s w i := rfl

/-- A restricted power cell is contained in the body `K`. -/
theorem bodyCellSet_subset_body (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (i : Fin n) :
    bodyCellSet K s w i ⊆ (K : Set Plane) :=
  Set.inter_subset_left

/-- A restricted power cell is convex (intersection of two convex sets). -/
theorem bodyCellSet_convex (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (i : Fin n) :
    Convex ℝ (bodyCellSet K s w i) :=
  K.convex.inter (cell_convex s w i)

/-- A restricted power cell is compact: the body is compact and the power cell is closed. -/
theorem bodyCellSet_isCompact (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (i : Fin n) :
    IsCompact (bodyCellSet K s w i) :=
  K.isCompact.inter_right (cell_isClosed s w i)

/-- **Bundled** restricted power cell, requiring explicit nonempty‑interior evidence `hInt`.
The carrier is `bodyCellSet K s w i`; convexity and compactness are automatic, and solidity is
exactly the supplied hypothesis. -/
noncomputable def bodyCellBody (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (i : Fin n) (hInt : (interior (bodyCellSet K s w i)).Nonempty) :
    Geometry.ConvexBody Plane where
  carrier := bodyCellSet K s w i
  convex' := bodyCellSet_convex K s w i
  isCompact' := bodyCellSet_isCompact K s w i
  interior_nonempty' := hInt

/-- The carrier of `bodyCellBody` is the restricted cell set. -/
@[simp] theorem bodyCellBody_carrier (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w :
  Fin n → ℝ)
    (i : Fin n) (hInt : (interior (bodyCellSet K s w i)).Nonempty) :
    (bodyCellBody K s w i hInt : Set Plane) = bodyCellSet K s w i := rfl

/-- The area of the bundled restricted cell equals the set‑level `bodyCellArea`. -/
theorem bodyCellBody_area (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (i : Fin n) (hInt : (interior (bodyCellSet K s w i)).Nonempty) :
    (bodyCellBody K s w i hInt).area = bodyCellArea K s w i := rfl

end NRR.PowerDiagram
