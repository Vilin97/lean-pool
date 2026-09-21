/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionSeparator
import Mathlib.Tactic

/-!
# Named positions on subdivided core edges

The Dhar configurations used for low-genus Brill--Noether arguments place
chips at a few elementary expressions in edge lengths: a minimum, or a
(truncated) difference.  This file packages those expressions as actual
vertices of `SubdivisionGraph.Spec`, with the elementary endpoint and
interiority facts kept independent of any particular configuration.
-/

namespace Utilities.Certificate

namespace SubdivisionGraph.Spec

variable {n p : ℕ} (spec : SubdivisionGraph.Spec n p)

/-- The path position at a natural offset known to be no further than the
head endpoint. -/
def pathPosition (edge : Fin p) (offset : ℕ)
    (hOffset : offset ≤ spec.length edge) : spec.PathPosition edge :=
  ⟨offset, by omega⟩

@[simp] theorem pathPosition_val (edge : Fin p) (offset : ℕ)
    (hOffset : offset ≤ spec.length edge) :
    (spec.pathPosition edge offset hOffset).val = offset := rfl

/-- Equality of path positions follows from equality of their numerical
offsets. -/
theorem pathPosition_eq_of_val_eq {edge : Fin p}
    {left right : spec.PathPosition edge} (h : left.val = right.val) :
    left = right :=
  Fin.ext h

/-- On one core slot, equal numerical positions give equal subdivision
vertices. -/
theorem pathVertex_eq_of_val_eq (edge : Fin p)
    {left right : spec.PathPosition edge} (h : left.val = right.val) :
    spec.pathVertex edge left = spec.pathVertex edge right := by
  rw [spec.pathPosition_eq_of_val_eq h]

/-- The numerical coordinate completely detects equality of vertices along a
single subdivided, loopless core slot. -/
theorem pathVertex_eq_iff_val_eq (edge : Fin p)
    (left right : spec.PathPosition edge) :
    spec.pathVertex edge left = spec.pathVertex edge right ↔
      left.val = right.val := by
  constructor
  · intro h
    exact congrArg Fin.val (spec.pathVertex_injective edge h)
  · exact spec.pathVertex_eq_of_val_eq edge

@[simp] theorem pathPosition_eq_zero_iff (edge : Fin p) (offset : ℕ)
    (hOffset : offset ≤ spec.length edge) :
    spec.pathPosition edge offset hOffset = ⟨0, by omega⟩ ↔ offset = 0 := by
  constructor
  · intro h
    simpa using congrArg Fin.val h
  · intro h
    subst offset
    rfl

@[simp] theorem pathPosition_eq_length_iff (edge : Fin p) (offset : ℕ)
    (hOffset : offset ≤ spec.length edge) :
    spec.pathPosition edge offset hOffset =
        ⟨spec.length edge, by omega⟩ ↔ offset = spec.length edge := by
  constructor
  · intro h
    simpa using congrArg Fin.val h
  · intro h
    subst offset
    rfl

/-- A named position is interior exactly when its numerical offset is strictly
between the two endpoints. -/
theorem isInteriorPosition_pathPosition_iff (edge : Fin p) (offset : ℕ)
    (hOffset : offset ≤ spec.length edge) :
    spec.IsInteriorPosition edge (spec.pathPosition edge offset hOffset) ↔
      0 < offset ∧ offset < spec.length edge := by
  change 0 < offset ∧ offset < spec.length edge ↔ _
  rfl

/-- The minimum of two core-edge lengths, viewed as a position on an edge
which is at least that long. -/
def minLengthPosition (edge left right : Fin p)
    (hBound : min (spec.length left) (spec.length right) ≤ spec.length edge) :
    spec.PathPosition edge :=
  spec.pathPosition edge (min (spec.length left) (spec.length right)) hBound

@[simp] theorem minLengthPosition_val (edge left right : Fin p)
    (hBound : min (spec.length left) (spec.length right) ≤ spec.length edge) :
    (spec.minLengthPosition edge left right hBound).val =
      min (spec.length left) (spec.length right) := rfl

theorem minLengthPosition_pos (edge left right : Fin p)
    (hBound : min (spec.length left) (spec.length right) ≤ spec.length edge) :
    0 < (spec.minLengthPosition edge left right hBound).val := by
  simp only [minLengthPosition_val]
  have hLeft := spec.length_pos left
  have hRight := spec.length_pos right
  omega

theorem minLengthPosition_isInterior (edge left right : Fin p)
    (hBound : min (spec.length left) (spec.length right) ≤ spec.length edge)
    (hStrict : min (spec.length left) (spec.length right) < spec.length edge) :
    spec.IsInteriorPosition edge
      (spec.minLengthPosition edge left right hBound) := by
  change 0 < min (spec.length left) (spec.length right) ∧
    min (spec.length left) (spec.length right) < spec.length edge
  exact ⟨spec.minLengthPosition_pos edge left right hBound, hStrict⟩

theorem minLengthPosition_eq_left (edge left right : Fin p)
    (hBound : min (spec.length left) (spec.length right) ≤ spec.length edge)
    (h : spec.length left ≤ spec.length right) :
    spec.minLengthPosition edge left right hBound =
      spec.pathPosition edge (spec.length left)
        (by omega) := by
  apply Fin.ext
  simp [minLengthPosition, Nat.min_eq_left h]

theorem minLengthPosition_eq_right (edge left right : Fin p)
    (hBound : min (spec.length left) (spec.length right) ≤ spec.length edge)
    (h : spec.length right ≤ spec.length left) :
    spec.minLengthPosition edge left right hBound =
      spec.pathPosition edge (spec.length right)
        (by omega) := by
  apply Fin.ext
  simp [minLengthPosition, Nat.min_eq_right h]

/-- The truncated difference of two core-edge lengths, viewed as a position
on an edge which is at least that far from its tail. -/
def differencePosition (edge minuend subtrahend : Fin p)
    (hBound : spec.length minuend - spec.length subtrahend ≤ spec.length edge) :
    spec.PathPosition edge :=
  spec.pathPosition edge (spec.length minuend - spec.length subtrahend) hBound

@[simp] theorem differencePosition_val (edge minuend subtrahend : Fin p)
    (hBound : spec.length minuend - spec.length subtrahend ≤ spec.length edge) :
    (spec.differencePosition edge minuend subtrahend hBound).val =
      spec.length minuend - spec.length subtrahend := rfl

theorem differencePosition_isInterior (edge minuend subtrahend : Fin p)
    (hBound : spec.length minuend - spec.length subtrahend ≤ spec.length edge)
    (hPositive : 0 < spec.length minuend - spec.length subtrahend)
    (hStrict : spec.length minuend - spec.length subtrahend < spec.length edge) :
    spec.IsInteriorPosition edge
      (spec.differencePosition edge minuend subtrahend hBound) := by
  change 0 < spec.length minuend - spec.length subtrahend ∧
    spec.length minuend - spec.length subtrahend < spec.length edge
  exact ⟨hPositive, hStrict⟩

/-- A non-truncated difference is positive precisely when the subtracted
length is strictly smaller. -/
theorem differencePosition_pos_iff (edge minuend subtrahend : Fin p)
    (hBound : spec.length minuend - spec.length subtrahend ≤ spec.length edge) :
    0 < (spec.differencePosition edge minuend subtrahend hBound).val ↔
      spec.length subtrahend < spec.length minuend := by
  rw [differencePosition_val]
  omega

end SubdivisionGraph.Spec

end Utilities.Certificate
