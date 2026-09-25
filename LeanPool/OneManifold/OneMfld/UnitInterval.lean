/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Tactic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.Compact


/-!
# UnitInterval

Supporting results for the classification of compact one-dimensional manifolds.
-/

@[expose] public section

/-- The closed unit interval in the real line. -/
def UnitInterval : Set Real := { x : Real | 0 ≤ x ∧ x ≤ 1 }

/-- `UnitInterval` is definitionally `Set.Icc 0 1`; this bridge unlocks Mathlib's
`Icc` API (e.g. `iccHomeoI`, `isCompact_Icc`) for it. -/
lemma UnitInterval_eq_Icc : UnitInterval = Set.Icc (0 : Real) 1 := rfl

lemma isCompact_UnitInterval : IsCompact UnitInterval := by
  rw [UnitInterval_eq_Icc]
  exact isCompact_Icc

instance : CompactSpace UnitInterval :=
  isCompact_iff_compactSpace.mp isCompact_UnitInterval

instance : Nonempty UnitInterval :=
  ⟨⟨0, le_refl 0, zero_le_one⟩⟩
