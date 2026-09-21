/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.BodySpace.PositiveArea

/-!
# The full parent body as a hyperspace point
-/

namespace NRR

open Geometry

namespace BodySpace

/-- The parent body itself, regarded as an element of `BodySpace K A` whenever the threshold is at
most the parent's area. -/
noncomputable def parentAt
    (K : Geometry.ConvexBody Plane) {A : ℝ} (hAK : A ≤ K.area) :
    BodySpace K A :=
  ⟨⟨K.toMathlib, subset_rfl⟩, hAK⟩

theorem parentAt_body_carrier
    (K : Geometry.ConvexBody Plane) {A : ℝ} (hAK : A ≤ K.area) :
    ((parentAt K hAK).body : Set Plane) = (K : Set Plane) :=
  rfl

@[simp] theorem parentAt_body_area
    (K : Geometry.ConvexBody Plane) {A : ℝ} (hAK : A ≤ K.area) :
    (parentAt K hAK).body.area = K.area :=
  rfl

/-- The parent body itself, regarded as an element of `BodySpace K K.area`. -/
noncomputable def full (K : Geometry.ConvexBody Plane) : BodySpace K K.area :=
  parentAt K le_rfl

theorem full_body_carrier (K : Geometry.ConvexBody Plane) :
    ((full K).body : Set Plane) = (K : Set Plane) :=
  rfl

@[simp] theorem full_body_area (K : Geometry.ConvexBody Plane) :
    (full K).body.area = K.area :=
  rfl

/-- The positive-area solid bridge of the full hyperspace point is the original body. -/
theorem toGeometryConvexBody_full
    (K : Geometry.ConvexBody Plane) (hK : 0 < K.area) :
    (full K).toGeometryConvexBody hK = K :=
  Geometry.ConvexBody.ext rfl

end BodySpace

end NRR
