/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Topology.UnitInterval

/-!
# UnitInterval

Supporting results for the classification of compact one-dimensional manifolds.
-/

public section

namespace OneMfld

/-- The closed unit interval in the real line. -/
abbrev UnitInterval : Set Real := unitInterval

/-- `UnitInterval` is definitionally `Set.Icc 0 1`; this bridge unlocks Mathlib's
`Icc` API (e.g. `iccHomeoI`, `isCompact_Icc`) for it. -/
lemma UnitInterval_eq_Icc : UnitInterval = Set.Icc (0 : Real) 1 := rfl

lemma isCompact_UnitInterval : IsCompact UnitInterval := by
  rw [UnitInterval_eq_Icc]
  exact isCompact_Icc

end OneMfld
