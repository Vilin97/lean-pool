/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Multivalued.PhaseInterfaces

/-!
# `NRR.Multivalued.SignedInterval` — the signed interval `[-1, 1]`

The signed interval is the closed real interval `[-1, 1]`, carrying the inherited subtype topology
and metric. The sign convention is that a nice multivalued observable is negative at the endpoint
`-1` and positive at the endpoint `1`.

This module provides the endpoint elements (`left`, `center`, `right`), the coordinate projection
`coord`, their coercion lemmas, compactness and connectedness of the whole interval, the ambient
`CompactSpace`/`T2Space`/`MetricSpace`/`ConnectedSpace` structures, and the vertical embedding
`vertical` used to build separator fibers.
-/

namespace NRR

/-- The signed interval `[-1, 1] ⊆ ℝ`, used as a subtype with the inherited topology and metric. -/
abbrev SignedInterval := Set.Icc (-1 : ℝ) 1

namespace SignedInterval

/-- The left endpoint `-1`, at which a nice multivalued observable is negative. -/
def left : SignedInterval :=
  ⟨-1, by constructor <;> norm_num⟩

/-- The right endpoint `1`, at which a nice multivalued observable is positive. -/
def right : SignedInterval :=
  ⟨1, by constructor <;> norm_num⟩

/-- The center point `0`. -/
def center : SignedInterval :=
  ⟨0, by constructor <;> norm_num⟩

/-- The coordinate projection sending a signed-interval point to its underlying real number. -/
def coord : SignedInterval → ℝ := fun y => y.1

instance : Nonempty SignedInterval := ⟨center⟩

/-- The signed interval is connected: it is the preconnected closed interval `[-1, 1]`, and it is
nonempty. -/
instance : ConnectedSpace SignedInterval where
  toPreconnectedSpace := Subtype.preconnectedSpace isPreconnected_Icc
  toNonempty := inferInstance

@[simp] theorem coe_left : ((left : SignedInterval) : ℝ) = -1 := rfl

@[simp] theorem coe_right : ((right : SignedInterval) : ℝ) = 1 := rfl

@[simp] theorem coe_center : ((center : SignedInterval) : ℝ) = 0 := rfl

@[simp] theorem coord_left : coord left = -1 := rfl

@[simp] theorem coord_right : coord right = 1 := rfl

@[simp] theorem coord_center : coord center = 0 := rfl

theorem left_ne_right : (left : SignedInterval) ≠ right := by
  intro h
  have := congrArg (Subtype.val) h
  simp only [coe_left, coe_right] at this
  norm_num at this

theorem right_ne_left : (right : SignedInterval) ≠ left :=
  fun h => left_ne_right h.symm

/-- The coordinate projection is continuous (it is the subtype coercion). -/
theorem continuous_coord : Continuous (coord : SignedInterval → ℝ) :=
  continuous_subtype_val

/-- The whole signed interval is compact. -/
theorem compact_univ : IsCompact (Set.univ : Set SignedInterval) :=
  isCompact_univ

/-- The whole signed interval is preconnected. -/
theorem preconnected_univ : IsPreconnected (Set.univ : Set SignedInterval) :=
  isPreconnected_univ

/-- The signed interval is a connected space. -/
theorem connectedSpace : ConnectedSpace SignedInterval := inferInstance

/-- The vertical embedding `y ↦ (x, y)` used to build separator fibers. -/
def vertical (X : Type*) (x : X) : SignedInterval → X × SignedInterval :=
  fun y => (x, y)

/-- The vertical embedding is continuous. -/
theorem continuous_vertical {X : Type*} [TopologicalSpace X] (x : X) :
    Continuous (vertical X x) :=
  continuous_const.prodMk continuous_id


end SignedInterval

end NRR
