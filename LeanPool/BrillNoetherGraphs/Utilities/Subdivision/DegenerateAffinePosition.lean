/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.AffinePosition
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateRankOne

/-!
# Affine-described positions on the CLOSED length orthant

The `DegSpec` counterpart of `Certificate/AffinePosition.lean`'s
`decodePosition` and `decodeVertex`.  Nothing there is modified: the strictly
positive decoder keeps working, and the passive `Code` type, its two cone rows
(`BoundsCertified`), `rawOffset`, `coordinate` and every purely arithmetic fact
about them are reused verbatim — none of them mention `Spec`.

Two things change, and both are forced.

* **`Valid` becomes `ValidClosed`.**  `rawOffset_le_segmentNat` reads the slot
  length off `segmentNat_cast_eq`, which needs `segment_positive_of_valid`.  The
  closed-orthant replacement is `segmentNat_cast_eq_of_validClosed`, which needs
  only non-negativity.  Nothing else in the bound argument changes.

* **The two-case split becomes a trichotomy.**  On a `Spec` a decoded position
  is `0` or interior whenever it is strictly below the slot length, and
  `length_pos` usually supplies that.  On the closed orthant `coordinate =
  length` is reachable — and at a *collapsed* slot it is the only possibility,
  where it coincides with `coordinate = 0`.  `decodeDegenerateVertex_trichotomy`
  is the exhaustive statement; the positive-world two-case consumers have no
  case for the middle disjunct.

Note that `decodeVertex_eq_head_of_coordinate_eq_length` is already
boundary-safe *as a statement*; what is not boundary-safe is concluding
"interior" from `0 < coordinate`.
-/

@[expose] public section

namespace MarkedGraphs.Certificate.AffinePosition
open Utilities.Certificate

open Utilities

open ExplicitPotential

namespace Code

variable {m n p : ℕ}

/-! ## The bound argument, on the closed orthant -/

/-- Closed-orthant replacement for `rawOffset_le_segmentNat`.  Only the length
decoding changes: `segmentNat_cast_eq_of_validClosed` needs non-negativity, not
positivity. -/
theorem rawOffset_le_segmentNat_of_validClosed
    (certificate : ExplicitPotential.CertificateData m n p) (code : Code m p)
    (point : Fin m → ℤ) {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    code.rawOffset point ≤ certificate.segmentNat point code.edge := by
  have hOffset := code.offset_le_segment_eval certificate point hBounds hCone
  have hRaw := code.rawOffset_cast certificate point hBounds hCone
  have hLength := certificate.segmentNat_cast_eq_of_validClosed hValid point hCone
    code.edge
  have hCast : (code.rawOffset point : ℤ) ≤
      (certificate.segmentNat point code.edge : ℤ) := by
    rw [hRaw, hLength]
    exact hOffset
  exact_mod_cast hCast

/-- Closed-orthant replacement for `coordinate_le_segmentNat`. -/
theorem coordinate_le_segmentNat_of_validClosed
    (certificate : ExplicitPotential.CertificateData m n p) (code : Code m p)
    (point : Fin m → ℤ) {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    code.coordinate certificate point ≤
      certificate.segmentNat point code.edge := by
  unfold coordinate
  split_ifs
  · omega
  · exact code.rawOffset_le_segmentNat_of_validClosed certificate point hValid
      hBounds hCone

/-! ## Decoding into the contracted subdivision -/

section Decode

variable (certificate : ExplicitPotential.CertificateData m n p) (code : Code m p)
  (point : Fin m → ℤ) (core_nonempty : 0 < n) (rep : Fin n → Fin n)
  (rep_idem : ∀ v : Fin n, rep (rep v) = rep v)
  (rep_zero : ∀ edge : Fin p, certificate.segmentNat point edge = 0 →
    rep (certificate.core.tail edge) = rep (certificate.core.head edge))
  (rep_loopless : ∀ edge : Fin p, 0 < certificate.segmentNat point edge →
    rep (certificate.core.tail edge) ≠ rep (certificate.core.head edge))
  (forest : (Finset.univ.image rep).card
    + (Finset.univ.filter
        (fun edge : Fin p => certificate.segmentNat point edge = 0)).card = n)

/-- Typed path position on the contracted subdivision, decoded from a
cone-certified affine position. -/
def decodeDegeneratePosition {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
      rep_loopless forest).PathPosition code.edge :=
  (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
      rep_loopless forest).pathPosition code.edge
    (code.coordinate certificate point)
    (code.coordinate_le_segmentNat_of_validClosed certificate point hValid
      hBounds hCone)

/-- The actual vertex of the contracted subdivision named by an affine position
code. -/
def decodeDegenerateVertex {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
      rep_loopless forest).Vertex :=
  (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
      rep_loopless forest).pathVertex code.edge
    (code.decodeDegeneratePosition certificate point core_nonempty rep rep_idem
      rep_zero rep_loopless forest hValid hBounds hCone)

@[simp] theorem decodeDegeneratePosition_val {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    (code.decodeDegeneratePosition certificate point core_nonempty rep rep_idem
      rep_zero rep_loopless forest hValid hBounds hCone).val =
      code.coordinate certificate point := rfl

theorem decodeDegeneratePosition_val_of_fromHead_false {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hDirection : code.fromHead = false) :
    (code.decodeDegeneratePosition certificate point core_nonempty rep rep_idem
      rep_zero rep_loopless forest hValid hBounds hCone).val =
      code.rawOffset point := by
  simp [decodeDegeneratePosition_val, coordinate, hDirection]

theorem decodeDegeneratePosition_val_of_fromHead_true {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hDirection : code.fromHead = true) :
    (code.decodeDegeneratePosition certificate point core_nonempty rep rep_idem
      rep_zero rep_loopless forest hValid hBounds hCone).val =
      certificate.segmentNat point code.edge - code.rawOffset point := by
  simp [decodeDegeneratePosition_val, coordinate, hDirection]

/-! ## The trichotomy

`decodeVertex_eq_tail_of_coordinate_eq_zero` and
`decodeVertex_eq_head_of_coordinate_eq_length` port unchanged; the third case is
the one the positive world does not have as a separate statement, because there
`0 < coordinate` already implies interiority when `coordinate < length`. -/

/-- Coordinate zero decodes to the tail class. -/
theorem decodeDegenerateVertex_eq_tail_of_coordinate_eq_zero {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hZero : code.coordinate certificate point = 0) :
    code.decodeDegenerateVertex certificate point core_nonempty rep rep_idem
        rep_zero rep_loopless forest hValid hBounds hCone =
      (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).coreVertex (certificate.core.tail code.edge) := by
  unfold decodeDegenerateVertex
  have hPosition :
      code.decodeDegeneratePosition certificate point core_nonempty rep rep_idem
          rep_zero rep_loopless forest hValid hBounds hCone =
        ⟨0, by
          have := code.coordinate_le_segmentNat_of_validClosed certificate point
            hValid hBounds hCone
          omega⟩ := by
    apply Fin.ext
    simpa [decodeDegeneratePosition_val] using hZero
  rw [hPosition]
  exact (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
    rep_loopless forest).pathVertex_zero code.edge

/-- Coordinate equal to the slot length decodes to the head class.  This holds
at a **collapsed** slot too, where it is the same vertex as the tail class:
`DegSpec.pathVertex_length` uses `rep_zero`, not `length_pos`. -/
theorem decodeDegenerateVertex_eq_head_of_coordinate_eq_length {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hLength : code.coordinate certificate point =
      certificate.segmentNat point code.edge) :
    code.decodeDegenerateVertex certificate point core_nonempty rep rep_idem
        rep_zero rep_loopless forest hValid hBounds hCone =
      (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).coreVertex (certificate.core.head code.edge) := by
  unfold decodeDegenerateVertex
  have hPosition :
      code.decodeDegeneratePosition certificate point core_nonempty rep rep_idem
          rep_zero rep_loopless forest hValid hBounds hCone =
        ⟨certificate.segmentNat point code.edge, by
          change certificate.segmentNat point code.edge <
            certificate.segmentNat point code.edge + 1
          omega⟩ := by
    apply Fin.ext
    simpa [decodeDegeneratePosition_val] using hLength
  rw [hPosition]
  exact (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
    rep_loopless forest).pathVertex_length code.edge

/-- A strictly interior coordinate decodes to an interior vertex. -/
theorem decodeDegenerateVertex_eq_interiorVertex {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hZero : code.coordinate certificate point ≠ 0)
    (hLast : code.coordinate certificate point ≠
      certificate.segmentNat point code.edge) :
    code.decodeDegenerateVertex certificate point core_nonempty rep rep_idem
        rep_zero rep_loopless forest hValid hBounds hCone =
      (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
          rep_loopless forest).interiorVertex code.edge
        ⟨code.coordinate certificate point - 1, by
          have := code.coordinate_le_segmentNat_of_validClosed certificate point
            hValid hBounds hCone
          change code.coordinate certificate point - 1 <
            certificate.segmentNat point code.edge - 1
          omega⟩ := by
  unfold decodeDegenerateVertex
  rw [(certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
    rep_loopless forest).pathVertex_interior code.edge _ hZero hLast]
  rfl

/-- **The trichotomy.**  A decoded position lands on the tail class, on the head
class, or on an interior vertex.  At a collapsed slot only the first two are
available and they coincide; the positive-world two-case split
(`coordinate = 0` versus `coordinate > 0 ⟹ interior`) has no case for the head
class. -/
theorem decodeDegenerateVertex_trichotomy {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    code.decodeDegenerateVertex certificate point core_nonempty rep rep_idem
          rep_zero rep_loopless forest hValid hBounds hCone =
        (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
          rep_loopless forest).coreVertex (certificate.core.tail code.edge) ∨
      code.decodeDegenerateVertex certificate point core_nonempty rep rep_idem
          rep_zero rep_loopless forest hValid hBounds hCone =
        (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
          rep_loopless forest).coreVertex (certificate.core.head code.edge) ∨
      ∃ o : Fin (certificate.segmentNat point code.edge - 1),
        code.decodeDegenerateVertex certificate point core_nonempty rep rep_idem
            rep_zero rep_loopless forest hValid hBounds hCone =
          (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
            rep_loopless forest).interiorVertex code.edge o := by
  by_cases hZero : code.coordinate certificate point = 0
  · exact Or.inl (code.decodeDegenerateVertex_eq_tail_of_coordinate_eq_zero
      certificate point core_nonempty rep rep_idem rep_zero rep_loopless forest
      hValid hBounds hCone hZero)
  · by_cases hLast : code.coordinate certificate point =
        certificate.segmentNat point code.edge
    · exact Or.inr (Or.inl
        (code.decodeDegenerateVertex_eq_head_of_coordinate_eq_length certificate
          point core_nonempty rep rep_idem rep_zero rep_loopless forest hValid
          hBounds hCone hLast))
    · refine Or.inr (Or.inr ⟨_, code.decodeDegenerateVertex_eq_interiorVertex
        certificate point core_nonempty rep rep_idem rep_zero rep_loopless forest
        hValid hBounds hCone hZero hLast⟩)

end Decode

end Code

end MarkedGraphs.Certificate.AffinePosition
