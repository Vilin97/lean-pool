/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic.Abel

/-!
# The order topology on a densely ordered additive group

Addition and negation are continuous for the order topology of a densely ordered abelian group.
The addition proof uses rectangles cut out by an intermediate point, so it does not assume the
continuity that it is constructing.
-/

open Set

universe u

public section

namespace ConwayRefinement.Standalone.Hahn

variable (G : Type u) [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [TopologicalSpace G] [OrderTopology G] [DenselyOrdered G]

/-- Addition is continuous in the order topology of a densely ordered abelian group. -/
theorem continuousAdd_of_orderTopology : ContinuousAdd G := by
  constructor
  apply OrderTopology.continuous_iff.mpr
  intro a
  constructor
  · rw [isOpen_prod_iff]
    intro x y hxy
    have hxy' : a - y < x := sub_lt_iff_lt_add.mpr hxy
    obtain ⟨d, had, hdx⟩ := exists_between hxy'
    refine ⟨Ioi d, Ioi (a - d), isOpen_Ioi, isOpen_Ioi, hdx, ?_, ?_⟩
    · change a - d < y
      rw [sub_lt_iff_lt_add, add_comm]
      exact sub_lt_iff_lt_add.mp had
    · rintro ⟨x', y'⟩ ⟨hx', hy'⟩
      calc
        a = d + (a - d) := by abel
        _ < x' + y' := add_lt_add hx' hy'
  · rw [isOpen_prod_iff]
    intro x y hxy
    have hxy' : x < a - y := lt_sub_iff_add_lt.mpr hxy
    obtain ⟨d, hxd, hda⟩ := exists_between hxy'
    refine ⟨Iio d, Iio (a - d), isOpen_Iio, isOpen_Iio, hxd, ?_, ?_⟩
    · change y < a - d
      rw [lt_sub_iff_add_lt, add_comm]
      exact lt_sub_iff_add_lt.mp hda
    · rintro ⟨x', y'⟩ ⟨hx', hy'⟩
      calc
        x' + y' < d + (a - d) := add_lt_add hx' hy'
        _ = a := by abel

omit [DenselyOrdered G] in
/-- Negation is continuous in the order topology of an ordered abelian group. -/
theorem continuousNeg_of_orderTopology : ContinuousNeg G :=
  ⟨(OrderIso.neg G).continuous⟩

end ConwayRefinement.Standalone.Hahn
