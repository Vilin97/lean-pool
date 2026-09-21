/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ExplicitPotentialRankOne
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.MovingPosition

/-!
# Affine-described positions on a subdivided slot

This is the small bridge between a passive affine certificate and the
dependent `PathPosition` type of a concrete subdivision.  A code names a
slot, an affine offset measured from one of its endpoints, and a direction.
The certificate contains no proofs: the two rows asserting that the offset
lies in its slot are required literally in its local cone.  Cone soundness
then supplies the bounds needed to construct a typed path position.
-/

namespace MarkedGraphs.Certificate.AffinePosition
open Utilities.Certificate

open Utilities

open ExplicitPotential
open SubdivisionGraph

/-- Passive name for a point on a slot.  `fromHead = true` reads `offset`
from the head, so its tail-oriented coordinate is `length - offset`. -/
structure Code (m p : ℕ) where
  edge : Fin p
  fromHead : Bool
  offset : ExplicitPotential.AffineForm m

namespace Code

variable {m n p : ℕ}

/-- The lower-bound row for a position code. -/
def lowerRow (code : Code m p) : ExplicitPotential.AffineForm m :=
  code.offset

/-- The upper-bound row for a position code on a particular certificate. -/
def upperRow (certificate : ExplicitPotential.Certificate m n p)
    (code : Code m p) : ExplicitPotential.AffineForm m :=
  ExplicitPotential.AffineForm.sub (certificate.segment code.edge) code.offset

/-- The local cone explicitly contains the two rows which say that the
offset is between zero and the length of its named slot. -/
def BoundsCertified (certificate : ExplicitPotential.Certificate m n p)
    (code : Code m p) : Prop :=
  (code.lowerRow = 0 ∨ code.lowerRow ∈ certificate.cone) ∧
  (code.upperRow certificate = 0 ∨ code.upperRow certificate ∈ certificate.cone)

/-- Proof-free check that one required bound row is either identically zero
or literally present in the local cone. -/
def checkRow (form : ExplicitPotential.AffineForm m)
    (cone : List (ExplicitPotential.AffineForm m)) : Bool :=
  AffineCover.AffineForm.equal form 0 ||
    AffineCover.AffineForm.mem form cone

@[simp] theorem checkRow_eq_true_iff
    (form : ExplicitPotential.AffineForm m)
    (cone : List (ExplicitPotential.AffineForm m)) :
    checkRow form cone = true ↔ form = 0 ∨ form ∈ cone := by
  simp [checkRow]

/-- Executable fail-closed bounds check for an affine position code. -/
def checkBounds (certificate : ExplicitPotential.Certificate m n p)
    (code : Code m p) : Bool :=
  checkRow code.lowerRow certificate.cone &&
    checkRow (code.upperRow certificate) certificate.cone

@[simp] theorem checkBounds_eq_true_iff
    (certificate : ExplicitPotential.Certificate m n p)
    (code : Code m p) :
    code.checkBounds certificate = true ↔ code.BoundsCertified certificate := by
  simp [checkBounds, BoundsCertified]

/-- The raw natural offset recovered from an integral affine evaluation. -/
def rawOffset (code : Code m p) (point : Fin m → ℤ) : ℕ :=
  (code.offset.eval point).toNat

private theorem holds_of_zero_or_mem
    (certificate : ExplicitPotential.Certificate m n p)
    (point : Fin m → ℤ) (form : ExplicitPotential.AffineForm m)
    (hRow : form = 0 ∨ form ∈ certificate.cone)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    form.Holds point := by
  rcases hRow with rfl | hMem
  · simp [AffineCover.AffineForm.Holds]
  · exact hCone form hMem

/-- Cone-certified offsets evaluate nonnegatively. -/
theorem offset_nonneg
    (certificate : ExplicitPotential.Certificate m n p) (code : Code m p)
    (point : Fin m → ℤ) (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    0 ≤ code.offset.eval point := by
  have h := holds_of_zero_or_mem certificate point code.lowerRow hBounds.1 hCone
  simpa [lowerRow, AffineCover.AffineForm.Holds] using h

/-- Cone-certified offsets do not exceed their named segment length. -/
theorem offset_le_segment_eval
    (certificate : ExplicitPotential.Certificate m n p) (code : Code m p)
    (point : Fin m → ℤ) (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    code.offset.eval point ≤ (certificate.segment code.edge).eval point := by
  have h := holds_of_zero_or_mem certificate point
    (code.upperRow certificate) hBounds.2 hCone
  simp only [upperRow, AffineCover.AffineForm.Holds,
    ExplicitPotential.AffineForm.eval_sub] at h
  omega

/-- At a certified point, coercing the raw offset back to `ℤ` recovers its
affine value exactly. -/
theorem rawOffset_cast
    (certificate : ExplicitPotential.Certificate m n p) (code : Code m p)
    (point : Fin m → ℤ) (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    (code.rawOffset point : ℤ) = code.offset.eval point := by
  exact Int.toNat_of_nonneg (code.offset_nonneg certificate point hBounds hCone)

/-- The raw natural offset is bounded by the concrete subdivision length. -/
theorem rawOffset_le_segmentNat
    (certificate : ExplicitPotential.Certificate m n p) (code : Code m p)
    (point : Fin m → ℤ) {degree : ℤ} (hValid : certificate.Valid degree)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    code.rawOffset point ≤ certificate.segmentNat point code.edge := by
  have hOffset := code.offset_le_segment_eval certificate point hBounds hCone
  have hRaw := code.rawOffset_cast certificate point hBounds hCone
  have hLength := certificate.segmentNat_cast_eq hValid point hCone code.edge
  have hCast : (code.rawOffset point : ℤ) ≤
      (certificate.segmentNat point code.edge : ℤ) := by
    rw [hRaw, hLength]
    exact hOffset
  exact_mod_cast hCast

/-- Tail-oriented numerical coordinate of a code in the concrete
subdivision. -/
def coordinate (certificate : ExplicitPotential.Certificate m n p)
    (code : Code m p) (point : Fin m → ℤ) : ℕ :=
  if code.fromHead then
    certificate.segmentNat point code.edge - code.rawOffset point
  else code.rawOffset point

/-- The orientation-normalized coordinate lies on its named slot. -/
theorem coordinate_le_segmentNat
    (certificate : ExplicitPotential.Certificate m n p) (code : Code m p)
    (point : Fin m → ℤ) {degree : ℤ} (hValid : certificate.Valid degree)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    code.coordinate certificate point ≤
      certificate.segmentNat point code.edge := by
  unfold coordinate
  split_ifs
  · omega
  · exact code.rawOffset_le_segmentNat certificate point hValid hBounds hCone

/-- Typed path position decoded from a cone-certified affine position. -/
def decodePosition (certificate : ExplicitPotential.Certificate m n p)
    (code : Code m p) (point : Fin m → ℤ) (core_nonempty : 0 < n)
    {degree : ℤ} (hValid : certificate.Valid degree)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    (certificate.subdivisionSpec point core_nonempty hValid hCone).PathPosition code.edge :=
  (certificate.subdivisionSpec point core_nonempty hValid hCone).pathPosition
    code.edge (code.coordinate certificate point)
    (code.coordinate_le_segmentNat certificate point hValid hBounds hCone)

/-- The actual subdivision vertex named by an affine position code. -/
def decodeVertex (certificate : ExplicitPotential.Certificate m n p)
    (code : Code m p) (point : Fin m → ℤ) (core_nonempty : 0 < n)
    {degree : ℤ} (hValid : certificate.Valid degree)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    (certificate.subdivisionSpec point core_nonempty hValid hCone).Vertex :=
  (certificate.subdivisionSpec point core_nonempty hValid hCone).pathVertex
    code.edge (code.decodePosition certificate point core_nonempty hValid hBounds hCone)

@[simp] theorem decodePosition_val
    (certificate : ExplicitPotential.Certificate m n p) (code : Code m p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n) {degree : ℤ}
    (hValid : certificate.Valid degree) (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    (code.decodePosition certificate point core_nonempty hValid hBounds hCone).val =
      code.coordinate certificate point := rfl

/-- Tail-oriented codes retain their raw coordinate. -/
theorem decodePosition_val_of_fromHead_false
    (certificate : ExplicitPotential.Certificate m n p) (code : Code m p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n) {degree : ℤ}
    (hValid : certificate.Valid degree) (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hDirection : code.fromHead = false) :
    (code.decodePosition certificate point core_nonempty hValid hBounds hCone).val =
      code.rawOffset point := by
  simp [decodePosition_val, coordinate, hDirection]

/-- Head-oriented codes use the complementary tail coordinate. -/
theorem decodePosition_val_of_fromHead_true
    (certificate : ExplicitPotential.Certificate m n p) (code : Code m p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n) {degree : ℤ}
    (hValid : certificate.Valid degree) (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hDirection : code.fromHead = true) :
    (code.decodePosition certificate point core_nonempty hValid hBounds hCone).val =
      certificate.segmentNat point code.edge - code.rawOffset point := by
  simp [decodePosition_val, coordinate, hDirection]
/-- Tail-oriented decoding is definitionally the ordinary bounded path
position constructor. -/
theorem decodePosition_eq_pathPosition_of_fromHead_false
    (certificate : ExplicitPotential.Certificate m n p) (code : Code m p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n) {degree : ℤ}
    (hValid : certificate.Valid degree) (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hDirection : code.fromHead = false) :
    code.decodePosition certificate point core_nonempty hValid hBounds hCone =
      (certificate.subdivisionSpec point core_nonempty hValid hCone).pathPosition
        code.edge (code.rawOffset point)
        (code.rawOffset_le_segmentNat certificate point hValid hBounds hCone) := by
  apply Fin.ext
  simp [decodePosition_val, coordinate, hDirection]

/-- A decoded position is interior whenever its normalized coordinate is
strictly between the two endpoints. -/
theorem decodePosition_isInterior
    (certificate : ExplicitPotential.Certificate m n p) (code : Code m p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n) {degree : ℤ}
    (hValid : certificate.Valid degree) (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hPositive : 0 < code.coordinate certificate point)
    (hStrict : code.coordinate certificate point <
      certificate.segmentNat point code.edge) :
    (certificate.subdivisionSpec point core_nonempty hValid hCone).IsInteriorPosition
      code.edge
      (code.decodePosition certificate point core_nonempty hValid hBounds hCone) := by
  change 0 < code.coordinate certificate point ∧
    code.coordinate certificate point < certificate.segmentNat point code.edge
  exact ⟨hPositive, hStrict⟩

/-- Coordinate zero decodes to the tail core vertex. -/
theorem decodeVertex_eq_tail_of_coordinate_eq_zero
    (certificate : ExplicitPotential.Certificate m n p) (code : Code m p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n) {degree : ℤ}
    (hValid : certificate.Valid degree) (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hZero : code.coordinate certificate point = 0) :
    code.decodeVertex certificate point core_nonempty hValid hBounds hCone =
      (certificate.subdivisionSpec point core_nonempty hValid hCone).coreVertex
        (certificate.core.tail code.edge) := by
  unfold decodeVertex
  have hPosition :
      code.decodePosition certificate point core_nonempty hValid hBounds hCone =
        ⟨0, by
          have := code.coordinate_le_segmentNat certificate point hValid hBounds hCone
          omega⟩ := by
    apply Fin.ext
    simpa [decodePosition_val] using hZero
  rw [hPosition]
  exact (certificate.subdivisionSpec point core_nonempty hValid hCone).pathVertex_zero
    code.edge

/-- Coordinate equal to the slot length decodes to the head core vertex. -/
theorem decodeVertex_eq_head_of_coordinate_eq_length
    (certificate : ExplicitPotential.Certificate m n p) (code : Code m p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n) {degree : ℤ}
    (hValid : certificate.Valid degree) (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hLength : code.coordinate certificate point =
      certificate.segmentNat point code.edge) :
    code.decodeVertex certificate point core_nonempty hValid hBounds hCone =
      (certificate.subdivisionSpec point core_nonempty hValid hCone).coreVertex
        (certificate.core.head code.edge) := by
  unfold decodeVertex
  have hPosition :
      code.decodePosition certificate point core_nonempty hValid hBounds hCone =
        ⟨certificate.segmentNat point code.edge, by
          change certificate.segmentNat point code.edge <
            certificate.segmentNat point code.edge + 1
          omega⟩ := by
    apply Fin.ext
    simpa [decodePosition_val] using hLength
  rw [hPosition]
  exact (certificate.subdivisionSpec point core_nonempty hValid hCone).pathVertex_length
    code.edge

end Code

end MarkedGraphs.Certificate.AffinePosition
