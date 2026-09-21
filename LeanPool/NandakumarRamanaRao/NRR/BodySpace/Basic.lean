/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.ConvexBody

/-!
# `NRR.ConvexSubbody` — fixed-parent convex subbodies

This module introduces the fixed-parent hyperspace element type

```
NRR.ConvexSubbody (K : Geometry.ConvexBody Plane)
```

whose elements are compact, nonempty, convex Mathlib bodies (`_root_.ConvexBody Plane`) contained
in the solid parent body `K`. Unlike the solid geometry body `Geometry.ConvexBody`, a
`ConvexSubbody` may be lower-dimensional (degenerate), which is exactly what is needed for a
compact hyperspace under the Hausdorff metric.

The area of a subbody is the real-valued Lebesgue measure of its carrier, matching the convention
of `Geometry.ConvexBody.area`.
-/

open MeasureTheory

open NRR.Geometry

namespace NRR

/-- A **convex subbody** of a fixed solid parent body `K`: a compact, nonempty, convex Mathlib
body whose carrier is contained in `K`. Elements may be lower-dimensional. -/
def ConvexSubbody (K : Geometry.ConvexBody Plane) :=
  {C : _root_.ConvexBody Plane // (C : Set Plane) ⊆ (K : Set Plane)}

namespace ConvexSubbody

variable {K : Geometry.ConvexBody Plane}

/-- The underlying Mathlib convex body of a subbody. -/
def body (C : ConvexSubbody K) : _root_.ConvexBody Plane := C.1

/-- Coercion of a subbody to its underlying carrier set. The `ConvexSubbody` wrapper is a `def`
over a subtype, so the subtype/root-body coercion chain does not fire automatically; this instance
restores `(C : Set Plane)` through `C.body`. -/
instance : CoeHead (ConvexSubbody K) (Set Plane) := ⟨fun C => (C.body : Set Plane)⟩

/-- The carrier of a subbody is contained in the parent body. -/
theorem subset_parent (C : ConvexSubbody K) :
    (C.body : Set Plane) ⊆ (K : Set Plane) :=
  C.2

/-- **Area** of a subbody: the real-valued Lebesgue measure of its carrier. -/
noncomputable def area (C : ConvexSubbody K) : ℝ :=
  (volume (C.body : Set Plane)).toReal

@[simp] theorem body_carrier (C : ConvexSubbody K) :
    (C.body : Set Plane) = (C.1 : Set Plane) :=
  rfl


/-- The carrier of a subbody is convex. -/
theorem convex (C : ConvexSubbody K) :
    Convex ℝ (C.body : Set Plane) :=
  C.body.convex'

/-- The carrier of a subbody is compact. -/
theorem isCompact (C : ConvexSubbody K) :
    IsCompact (C.body : Set Plane) :=
  C.body.isCompact'

/-- The carrier of a subbody is nonempty. -/
theorem nonempty (C : ConvexSubbody K) :
    (C.body : Set Plane).Nonempty :=
  C.body.nonempty'

/-- The area of a subbody is nonnegative. -/
theorem area_nonneg (C : ConvexSubbody K) :
    0 ≤ C.area :=
  ENNReal.toReal_nonneg

/-- The Lebesgue measure of a subbody is finite (its carrier is compact). -/
theorem area_lt_top (C : ConvexSubbody K) :
    volume (C.body : Set Plane) < ⊤ :=
  C.isCompact.measure_lt_top

/-- **Extensionality**: two subbodies with equal carriers are equal. -/
@[ext] theorem ext {C D : ConvexSubbody K}
    (h : (C.body : Set Plane) = (D.body : Set Plane)) :
    C = D :=
  Subtype.ext (_root_.ConvexBody.ext h)

end ConvexSubbody

/-- The **lower-area subspace**: subbodies of `K` whose area is at least `A`. -/
def BodySpace (K : Geometry.ConvexBody Plane) (A : ℝ) :=
  {C : ConvexSubbody K // A ≤ C.area}

end NRR
