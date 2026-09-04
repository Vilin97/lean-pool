/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Definitions for Grünbaum's centroid halfspace theorem

Mathlib's `ConvexBody` permits lower-dimensional compact convex sets.  In
finite-dimensional convex geometry, a convex body is normally required to
have nonempty interior.  `FullDimensionalConvexBody` records precisely that
standard convention.
-/

open MeasureTheory Set

namespace Grunbaum

/-- Euclidean space of positive dimension `d + 1`. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

/-- A compact convex set with nonempty interior. -/
structure FullDimensionalConvexBody (d : ℕ) where
  /-- The underlying point set. -/
  carrier : Set (Euc d)
  /-- Convexity of the body. -/
  convex' : Convex ℝ carrier
  /-- Compactness of the body. -/
  isCompact' : IsCompact carrier
  /-- The body is full-dimensional. -/
  interior_nonempty' : (interior carrier).Nonempty

namespace FullDimensionalConvexBody

instance {d : ℕ} : SetLike (FullDimensionalConvexBody d) (Euc d) where
  coe := FullDimensionalConvexBody.carrier
  coe_injective C D h := by
    cases C
    cases D
    congr

protected theorem convex {d : ℕ} (C : FullDimensionalConvexBody d) :
    Convex ℝ (C : Set (Euc d)) :=
  C.convex'

protected theorem isCompact {d : ℕ} (C : FullDimensionalConvexBody d) :
    IsCompact (C : Set (Euc d)) :=
  C.isCompact'

protected theorem isClosed {d : ℕ} (C : FullDimensionalConvexBody d) :
    IsClosed (C : Set (Euc d)) :=
  C.isCompact.isClosed

protected theorem interior_nonempty {d : ℕ} (C : FullDimensionalConvexBody d) :
    (interior (C : Set (Euc d))).Nonempty :=
  C.interior_nonempty'

protected theorem nonempty {d : ℕ} (C : FullDimensionalConvexBody d) :
    (C : Set (Euc d)).Nonempty :=
  C.interior_nonempty.mono interior_subset

theorem volume_pos {d : ℕ} (C : FullDimensionalConvexBody d) :
    0 < volume (C : Set (Euc d)) :=
  Measure.measure_pos_of_nonempty_interior volume C.interior_nonempty

theorem volume_ne_zero {d : ℕ} (C : FullDimensionalConvexBody d) :
    volume (C : Set (Euc d)) ≠ 0 :=
  C.volume_pos.ne'

theorem volume_ne_top {d : ℕ} (C : FullDimensionalConvexBody d) :
    volume (C : Set (Euc d)) ≠ ⊤ :=
  C.isCompact.measure_lt_top.ne

/-- The volume centroid of a full-dimensional convex body. -/
noncomputable def centroid {d : ℕ} (C : FullDimensionalConvexBody d) : Euc d :=
  ⨍ x in (C : Set (Euc d)), x ∂volume

end FullDimensionalConvexBody

/-- The closed halfspace cut out by `ℓ x ≤ a`. -/
def closedHalfspace {d : ℕ} (ℓ : Euc d →L[ℝ] ℝ) (a : ℝ) : Set (Euc d) :=
  ℓ ⁻¹' Iic a

/-- A (proper) closed halfspace, represented by a nonzero continuous linear
functional and a threshold. -/
structure ClosedHalfspace (d : ℕ) where
  /-- The defining normal functional. -/
  normal : Euc d →L[ℝ] ℝ
  /-- The defining threshold. -/
  threshold : ℝ
  /-- A halfspace has a nonzero normal. -/
  normal_ne_zero : normal ≠ 0

namespace ClosedHalfspace

instance {d : ℕ} : Coe (ClosedHalfspace d) (Set (Euc d)) where
  coe H := closedHalfspace H.normal H.threshold

instance {d : ℕ} : Membership (Euc d) (ClosedHalfspace d) where
  mem H x := x ∈ (H : Set (Euc d))

@[simp]
theorem mem_iff {d : ℕ} {x : Euc d} {H : ClosedHalfspace d} :
    x ∈ H ↔ H.normal x ≤ H.threshold :=
  Iff.rfl

theorem isClosed {d : ℕ} (H : ClosedHalfspace d) :
    IsClosed (closedHalfspace H.normal H.threshold) :=
  isClosed_Iic.preimage H.normal.continuous

end ClosedHalfspace

/-- The normalized volume of a body's intersection with a closed halfspace. -/
noncomputable def halfspaceVolumeRatio {d : ℕ} (C : FullDimensionalConvexBody d)
    (ℓ : Euc d →L[ℝ] ℝ) (a : ℝ) : ℝ :=
  (volume ((C : Set (Euc d)) ∩ closedHalfspace ℓ a) /
    volume (C : Set (Euc d))).toReal

/-- The sharp constant `(n / (n + 1)) ^ n` in dimension `n = d + 1`. -/
noncomputable def grunbaumConstant (d : ℕ) : ℝ :=
  (((d + 1 : ℕ) : ℝ) / (d + 2 : ℕ)) ^ (d + 1)

end Grunbaum
