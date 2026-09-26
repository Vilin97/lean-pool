/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCoreAtlas
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CubicCore
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.TwoPoleSubdivision

/-!
# Finite two-pole data for six genus-five rows

Each row is two connected leafless four-vertex, five-slot factors joined by
two connector slots.  The index `focus : Fin 2` chooses which connector is
first.  The factors are exchanged when necessary to orient that connector
from left to right; the second connector may retain either orientation.

All data below concern finite incidence and canonical-weight tables.  They
contain no rank or length hypotheses.  The source slots are exactly those in
`GenusFiveCoreAtlas`, including the reversed connector in rows 02 and 04.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveTwoPoleData

open Utilities.Certificate
open Utilities.Certificate.TwoPoleSubdivision
open GenusFiveCoreAtlas

/-- Bundle mutually inverse finite-index functions as a permutation. -/
def permutation {n : ℕ} (forward inverse : Fin n → Fin n)
    (hLeft : ∀ i, inverse (forward i) = i)
    (hRight : ∀ i, forward (inverse i) = i) : Equiv.Perm (Fin n) where
  toFun := forward
  invFun := inverse
  left_inv := hLeft
  right_inv := hRight

/-- Convert a permutation of eight vertices into the displayed two-core vertex indexing. -/
def vertexIndex (perm : Equiv.Perm (Fin 8)) :
    (Fin 4 ⊕ Fin 4) ≃ Fin 8 :=
  (@finSumFinEquiv 4 4).trans perm

/-- Convert a permutation of twelve slots into the displayed two-core edge indexing. -/
def slotIndex (perm : Equiv.Perm (Fin 12)) :
    ((Fin 5 ⊕ Fin 5) ⊕ Fin 2) ≃ Fin 12 :=
  ((Equiv.sumCongr (@finSumFinEquiv 5 5) (Equiv.refl (Fin 2))).trans
    (@finSumFinEquiv 10 2)).trans perm

/-! ## Factor cores -/

/-- The left four-vertex, five-slot component of the row-01 two-pole decomposition, with
oriented slots `0→1, 0→1, 2→0, 1→3, 2→3` in index order. -/
def row01LeftCore : ExplicitPotential.Core 4 5 where
  tail := ![0, 0, 2, 1, 2]
  head := ![1, 1, 0, 3, 3]

/-- The right four-vertex, five-slot component of the row-01 two-pole decomposition, with
oriented slots `1→3, 0→2, 0→1, 2→3, 2→3` in index order. -/
def row01RightCore : ExplicitPotential.Core 4 5 where
  tail := ![1, 0, 0, 2, 2]
  head := ![3, 2, 1, 3, 3]

/-- The left four-vertex, five-slot component of the row-02 two-pole decomposition, with
oriented slots `0→1, 0→2, 1→3, 2→3, 2→3` in index order. -/
def row02LeftCore : ExplicitPotential.Core 4 5 where
  tail := ![0, 0, 1, 2, 2]
  head := ![1, 2, 3, 3, 3]

/-- The right four-vertex, five-slot component of the row-02 two-pole decomposition, with
oriented slots `1→2, 1→2, 2→3, 3→0, 3→0` in index order. -/
def row02RightCore : ExplicitPotential.Core 4 5 where
  tail := ![1, 1, 2, 3, 3]
  head := ![2, 2, 3, 0, 0]

/-- The left four-vertex, five-slot component of the row-03 two-pole decomposition, with
oriented slots `0→2, 2→1, 0→3, 3→1, 0→1` in index order. -/
def row03LeftCore : ExplicitPotential.Core 4 5 where
  tail := ![0, 2, 0, 3, 0]
  head := ![2, 1, 3, 1, 1]

/-- The right four-vertex, five-slot component of the row-03 two-pole decomposition, with
oriented slots `2→0, 3→1, 0→1, 0→1, 2→3` in index order. -/
def row03RightCore : ExplicitPotential.Core 4 5 where
  tail := ![2, 3, 0, 0, 2]
  head := ![0, 1, 1, 1, 3]

/-- The left four-vertex, five-slot component of the row-04 two-pole decomposition, with
oriented slots `0→1, 0→1, 3→2, 3→2, 2→0` in index order. -/
def row04LeftCore : ExplicitPotential.Core 4 5 where
  tail := ![0, 0, 3, 3, 2]
  head := ![1, 1, 2, 2, 0]

/-- The right four-vertex, five-slot component of the row-04 two-pole decomposition, with
oriented slots `0→1, 0→1, 1→2, 2→3, 2→3` in index order. -/
def row04RightCore : ExplicitPotential.Core 4 5 where
  tail := ![0, 0, 1, 2, 2]
  head := ![1, 1, 2, 3, 3]

/-- The left four-vertex, five-slot component of the row-07 two-pole decomposition, with
oriented slots `0→2, 2→1, 0→3, 3→1, 2→3` in index order. -/
def row07LeftCore : ExplicitPotential.Core 4 5 where
  tail := ![0, 2, 0, 3, 2]
  head := ![2, 1, 3, 1, 3]

/-- The right four-vertex, five-slot component of the row-07 two-pole decomposition, with
oriented slots `2→3, 0→2, 0→2, 1→3, 1→3` in index order. -/
def row07RightCore : ExplicitPotential.Core 4 5 where
  tail := ![2, 0, 0, 1, 1]
  head := ![3, 2, 2, 3, 3]

/-- The left four-vertex, five-slot core in the row-13 two-pole decomposition; its incidence
data are the same as `row07LeftCore`. -/
def row13LeftCore : ExplicitPotential.Core 4 5 := row07LeftCore

/-- The right four-vertex, five-slot core in the row-13 two-pole decomposition, again using
`row07LeftCore` with the row-13 attachment data. -/
def row13RightCore : ExplicitPotential.Core 4 5 := row07LeftCore

/-! ## The two choices of first connector -/

/-- The explicit two-pole decomposition for row 01 with connector slot 0 first. -/
def row01Focus0 : Data row01Core 4 5 4 5 where
  leftCore := row01LeftCore
  rightCore := row01RightCore
  vertices := vertexIndex (Equiv.refl _)
  slots := slotIndex (permutation
    ![0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 5, 7]
    ![0, 1, 2, 3, 4, 10, 5, 11, 6, 7, 8, 9] (by decide) (by decide))
  leftPole := ![3, 2]
  rightPole := ![1, 0]
  left_nonempty := by decide
  right_nonempty := by decide
  tail_left := by decide
  head_left := by decide
  tail_right := by decide
  head_right := by decide
  tail_first := by decide
  head_first := by decide
  second_ends := by decide

/-- The explicit two-pole decomposition for row 01 with connector slot 1 first. -/
def row01Focus1 : Data row01Core 4 5 4 5 where
  leftCore := row01LeftCore
  rightCore := row01RightCore
  vertices := vertexIndex (Equiv.refl _)
  slots := slotIndex (permutation
    ![0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 7, 5]
    ![0, 1, 2, 3, 4, 11, 5, 10, 6, 7, 8, 9] (by decide) (by decide))
  leftPole := ![2, 3]
  rightPole := ![0, 1]
  left_nonempty := by decide
  right_nonempty := by decide
  tail_left := by decide
  head_left := by decide
  tail_right := by decide
  head_right := by decide
  tail_first := by decide
  head_first := by decide
  second_ends := by decide

/-- Row 01, with either of its two connector slots chosen first. -/
def row01 (focus : Fin 2) : Data row01Core 4 5 4 5 :=
  if focus = 0 then row01Focus0 else row01Focus1

/-- The explicit two-pole decomposition for row 02 with connector slot 0 first. -/
def row02Focus0 : Data row02Core 4 5 4 5 where
  leftCore := row02RightCore
  rightCore := row02LeftCore
  vertices := vertexIndex (permutation
    ![0, 5, 6, 7, 1, 2, 3, 4]
    ![0, 4, 5, 6, 7, 1, 2, 3] (by decide) (by decide))
  slots := slotIndex (permutation
    ![3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 0, 2]
    ![10, 5, 11, 0, 1, 2, 3, 4, 6, 7, 8, 9] (by decide) (by decide))
  leftPole := ![0, 1]
  rightPole := ![0, 1]
  left_nonempty := by decide
  right_nonempty := by decide
  tail_left := by decide
  head_left := by decide
  tail_right := by decide
  head_right := by decide
  tail_first := by decide
  head_first := by decide
  second_ends := by decide

/-- The explicit two-pole decomposition for row 02 with connector slot 1 first. -/
def row02Focus1 : Data row02Core 4 5 4 5 where
  leftCore := row02LeftCore
  rightCore := row02RightCore
  vertices := vertexIndex (permutation
    ![1, 2, 3, 4, 0, 5, 6, 7]
    ![4, 0, 1, 2, 3, 5, 6, 7] (by decide) (by decide))
  slots := slotIndex (permutation
    ![1, 8, 9, 10, 11, 3, 4, 5, 6, 7, 2, 0]
    ![11, 0, 10, 5, 6, 7, 8, 9, 1, 2, 3, 4] (by decide) (by decide))
  leftPole := ![1, 0]
  rightPole := ![1, 0]
  left_nonempty := by decide
  right_nonempty := by decide
  tail_left := by decide
  head_left := by decide
  tail_right := by decide
  head_right := by decide
  tail_first := by decide
  head_first := by decide
  second_ends := by decide

/-- Row 02, with either of its two connector slots chosen first. -/
def row02 (focus : Fin 2) : Data row02Core 4 5 4 5 :=
  if focus = 0 then row02Focus0 else row02Focus1

/-- The explicit two-pole decomposition for row 03 with connector slot 0 first. -/
def row03Focus0 : Data row03Core 4 5 4 5 where
  leftCore := row03LeftCore
  rightCore := row03RightCore
  vertices := vertexIndex (Equiv.refl _)
  slots := slotIndex (permutation
    ![0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 5, 7]
    ![0, 1, 2, 3, 4, 10, 5, 11, 6, 7, 8, 9] (by decide) (by decide))
  leftPole := ![2, 3]
  rightPole := ![2, 3]
  left_nonempty := by decide
  right_nonempty := by decide
  tail_left := by decide
  head_left := by decide
  tail_right := by decide
  head_right := by decide
  tail_first := by decide
  head_first := by decide
  second_ends := by decide

/-- The explicit two-pole decomposition for row 03 with connector slot 1 first. -/
def row03Focus1 : Data row03Core 4 5 4 5 where
  leftCore := row03LeftCore
  rightCore := row03RightCore
  vertices := vertexIndex (Equiv.refl _)
  slots := slotIndex (permutation
    ![0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 7, 5]
    ![0, 1, 2, 3, 4, 11, 5, 10, 6, 7, 8, 9] (by decide) (by decide))
  leftPole := ![3, 2]
  rightPole := ![3, 2]
  left_nonempty := by decide
  right_nonempty := by decide
  tail_left := by decide
  head_left := by decide
  tail_right := by decide
  head_right := by decide
  tail_first := by decide
  head_first := by decide
  second_ends := by decide

/-- Row 03, with either of its two connector slots chosen first. -/
def row03 (focus : Fin 2) : Data row03Core 4 5 4 5 :=
  if focus = 0 then row03Focus0 else row03Focus1

/-- The explicit two-pole decomposition for row 04 with connector slot 0 first. -/
def row04Focus0 : Data row04Core 4 5 4 5 where
  leftCore := row04LeftCore
  rightCore := row04RightCore
  vertices := vertexIndex (Equiv.refl _)
  slots := slotIndex (permutation
    ![0, 1, 9, 10, 11, 3, 4, 5, 6, 7, 2, 8]
    ![0, 1, 10, 5, 6, 7, 8, 9, 11, 2, 3, 4] (by decide) (by decide))
  leftPole := ![1, 3]
  rightPole := ![0, 3]
  left_nonempty := by decide
  right_nonempty := by decide
  tail_left := by decide
  head_left := by decide
  tail_right := by decide
  head_right := by decide
  tail_first := by decide
  head_first := by decide
  second_ends := by decide

/-- The explicit two-pole decomposition for row 04 with connector slot 1 first. -/
def row04Focus1 : Data row04Core 4 5 4 5 where
  leftCore := row04RightCore
  rightCore := row04LeftCore
  vertices := vertexIndex (permutation
    ![4, 5, 6, 7, 0, 1, 2, 3]
    ![4, 5, 6, 7, 0, 1, 2, 3] (by decide) (by decide))
  slots := slotIndex (permutation
    ![3, 4, 5, 6, 7, 0, 1, 9, 10, 11, 8, 2]
    ![5, 6, 11, 0, 1, 2, 3, 4, 10, 7, 8, 9] (by decide) (by decide))
  leftPole := ![3, 0]
  rightPole := ![3, 1]
  left_nonempty := by decide
  right_nonempty := by decide
  tail_left := by decide
  head_left := by decide
  tail_right := by decide
  head_right := by decide
  tail_first := by decide
  head_first := by decide
  second_ends := by decide

/-- Row 04, with either of its two connector slots chosen first. -/
def row04 (focus : Fin 2) : Data row04Core 4 5 4 5 :=
  if focus = 0 then row04Focus0 else row04Focus1

/-- The explicit two-pole decomposition for row 07 with connector slot 0 first. -/
def row07Focus0 : Data row07Core 4 5 4 5 where
  leftCore := row07LeftCore
  rightCore := row07RightCore
  vertices := vertexIndex (Equiv.refl _)
  slots := slotIndex (permutation
    ![0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 5, 6]
    ![0, 1, 2, 3, 4, 10, 11, 5, 6, 7, 8, 9] (by decide) (by decide))
  leftPole := ![0, 1]
  rightPole := ![0, 1]
  left_nonempty := by decide
  right_nonempty := by decide
  tail_left := by decide
  head_left := by decide
  tail_right := by decide
  head_right := by decide
  tail_first := by decide
  head_first := by decide
  second_ends := by decide

/-- The explicit two-pole decomposition for row 07 with connector slot 1 first. -/
def row07Focus1 : Data row07Core 4 5 4 5 where
  leftCore := row07LeftCore
  rightCore := row07RightCore
  vertices := vertexIndex (Equiv.refl _)
  slots := slotIndex (permutation
    ![0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 6, 5]
    ![0, 1, 2, 3, 4, 11, 10, 5, 6, 7, 8, 9] (by decide) (by decide))
  leftPole := ![1, 0]
  rightPole := ![1, 0]
  left_nonempty := by decide
  right_nonempty := by decide
  tail_left := by decide
  head_left := by decide
  tail_right := by decide
  head_right := by decide
  tail_first := by decide
  head_first := by decide
  second_ends := by decide

/-- Row 07, with either of its two connector slots chosen first. -/
def row07 (focus : Fin 2) : Data row07Core 4 5 4 5 :=
  if focus = 0 then row07Focus0 else row07Focus1

/-- The explicit two-pole decomposition for row 13 with connector slot 0 first. -/
def row13Focus0 : Data row13Core 4 5 4 5 where
  leftCore := row13LeftCore
  rightCore := row13RightCore
  vertices := vertexIndex (Equiv.refl _)
  slots := slotIndex (Equiv.refl _)
  leftPole := ![0, 1]
  rightPole := ![0, 1]
  left_nonempty := by decide
  right_nonempty := by decide
  tail_left := by decide
  head_left := by decide
  tail_right := by decide
  head_right := by decide
  tail_first := by decide
  head_first := by decide
  second_ends := by decide

/-- The explicit two-pole decomposition for row 13 with connector slot 1 first. -/
def row13Focus1 : Data row13Core 4 5 4 5 where
  leftCore := row13LeftCore
  rightCore := row13RightCore
  vertices := vertexIndex (Equiv.refl _)
  slots := slotIndex (permutation
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10]
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10] (by decide) (by decide))
  leftPole := ![1, 0]
  rightPole := ![1, 0]
  left_nonempty := by decide
  right_nonempty := by decide
  tail_left := by decide
  head_left := by decide
  tail_right := by decide
  head_right := by decide
  tail_first := by decide
  head_first := by decide
  second_ends := by decide

/-- Row 13, with either of its two connector slots chosen first. -/
def row13 (focus : Fin 2) : Data row13Core 4 5 4 5 :=
  if focus = 0 then row13Focus0 else row13Focus1

/-! ## Factor hypotheses for the canonical construction -/

theorem row01_left_connected (focus : Fin 2) :
    (row01 focus).leftCore.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast (by
    fin_cases focus <;> decide)

theorem row01_left_degree_ge_two (focus : Fin 2) :
    ∀ v : Fin 4, 2 ≤ (row01 focus).leftCore.incidenceDegree v := by
  fin_cases focus <;> decide

theorem row01_right_connected (focus : Fin 2) :
    (row01 focus).rightCore.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast (by
    fin_cases focus <;> decide)

theorem row01_right_degree_ge_two (focus : Fin 2) :
    ∀ v : Fin 4, 2 ≤ (row01 focus).rightCore.incidenceDegree v := by
  fin_cases focus <;> decide

theorem row02_left_connected (focus : Fin 2) :
    (row02 focus).leftCore.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast (by
    fin_cases focus <;> decide)

theorem row02_left_degree_ge_two (focus : Fin 2) :
    ∀ v : Fin 4, 2 ≤ (row02 focus).leftCore.incidenceDegree v := by
  fin_cases focus <;> decide

theorem row02_right_connected (focus : Fin 2) :
    (row02 focus).rightCore.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast (by
    fin_cases focus <;> decide)

theorem row02_right_degree_ge_two (focus : Fin 2) :
    ∀ v : Fin 4, 2 ≤ (row02 focus).rightCore.incidenceDegree v := by
  fin_cases focus <;> decide

theorem row03_left_connected (focus : Fin 2) :
    (row03 focus).leftCore.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast (by
    fin_cases focus <;> decide)

theorem row03_left_degree_ge_two (focus : Fin 2) :
    ∀ v : Fin 4, 2 ≤ (row03 focus).leftCore.incidenceDegree v := by
  fin_cases focus <;> decide

theorem row03_right_connected (focus : Fin 2) :
    (row03 focus).rightCore.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast (by
    fin_cases focus <;> decide)

theorem row03_right_degree_ge_two (focus : Fin 2) :
    ∀ v : Fin 4, 2 ≤ (row03 focus).rightCore.incidenceDegree v := by
  fin_cases focus <;> decide

theorem row04_left_connected (focus : Fin 2) :
    (row04 focus).leftCore.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast (by
    fin_cases focus <;> decide)

theorem row04_left_degree_ge_two (focus : Fin 2) :
    ∀ v : Fin 4, 2 ≤ (row04 focus).leftCore.incidenceDegree v := by
  fin_cases focus <;> decide

theorem row04_right_connected (focus : Fin 2) :
    (row04 focus).rightCore.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast (by
    fin_cases focus <;> decide)

theorem row04_right_degree_ge_two (focus : Fin 2) :
    ∀ v : Fin 4, 2 ≤ (row04 focus).rightCore.incidenceDegree v := by
  fin_cases focus <;> decide

theorem row07_left_connected (focus : Fin 2) :
    (row07 focus).leftCore.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast (by
    fin_cases focus <;> decide)

theorem row07_left_degree_ge_two (focus : Fin 2) :
    ∀ v : Fin 4, 2 ≤ (row07 focus).leftCore.incidenceDegree v := by
  fin_cases focus <;> decide

theorem row07_right_connected (focus : Fin 2) :
    (row07 focus).rightCore.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast (by
    fin_cases focus <;> decide)

theorem row07_right_degree_ge_two (focus : Fin 2) :
    ∀ v : Fin 4, 2 ≤ (row07 focus).rightCore.incidenceDegree v := by
  fin_cases focus <;> decide

theorem row13_left_connected (focus : Fin 2) :
    (row13 focus).leftCore.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast (by
    fin_cases focus <;> decide)

theorem row13_left_degree_ge_two (focus : Fin 2) :
    ∀ v : Fin 4, 2 ≤ (row13 focus).leftCore.incidenceDegree v := by
  fin_cases focus <;> decide

theorem row13_right_connected (focus : Fin 2) :
    (row13 focus).rightCore.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast (by
    fin_cases focus <;> decide)

theorem row13_right_degree_ge_two (focus : Fin 2) :
    ∀ v : Fin 4, 2 ≤ (row13 focus).rightCore.incidenceDegree v := by
  fin_cases focus <;> decide


/-! ## Canonical weights and the finite coverage check -/

/-- The sum of the two factor canonical divisors, supported on core vertices. -/
def row13Weight : Fin 8 → ℤ := ![0, 0, 1, 1, 0, 0, 1, 1]

theorem row13_weight_nonneg : ∀ v, 0 ≤ row13Weight v := by decide

theorem row13_weight_sum : (∑ v, row13Weight v) = 4 := by decide

theorem row13_weight_left (focus : Fin 2) :
    ∀ a : Fin 4, row13Weight ((row13 focus).vertices (.inl a)) =
      ((row13 focus).leftCore.incidenceDegree a : ℤ) - 2 := by
  fin_cases focus <;> decide

theorem row13_weight_right (focus : Fin 2) :
    ∀ b : Fin 4, row13Weight ((row13 focus).vertices (.inr b)) =
      ((row13 focus).rightCore.incidenceDegree b : ℤ) - 2 := by
  fin_cases focus <;> decide

theorem row13_coverage :
    ∀ v : Fin 8, 1 ≤ row13Weight v ∨
      ∃ focus : Fin 2,
        v = (row13 focus).vertices (.inl ((row13 focus).leftPole 0)) ∨
        v = (row13 focus).vertices (.inr ((row13 focus).rightPole 0)) := by
  decide

/-- The sum of the two factor canonical divisors, supported on core vertices. -/
def row01Weight : Fin 8 → ℤ := ![1, 1, 0, 0, 0, 0, 1, 1]

theorem row01_weight_nonneg : ∀ v, 0 ≤ row01Weight v := by decide

theorem row01_weight_sum : (∑ v, row01Weight v) = 4 := by decide

theorem row01_weight_left (focus : Fin 2) :
    ∀ a : Fin 4, row01Weight ((row01 focus).vertices (.inl a)) =
      ((row01 focus).leftCore.incidenceDegree a : ℤ) - 2 := by
  fin_cases focus <;> decide

theorem row01_weight_right (focus : Fin 2) :
    ∀ b : Fin 4, row01Weight ((row01 focus).vertices (.inr b)) =
      ((row01 focus).rightCore.incidenceDegree b : ℤ) - 2 := by
  fin_cases focus <;> decide

theorem row01_coverage :
    ∀ v : Fin 8, 1 ≤ row01Weight v ∨
      ∃ focus : Fin 2,
        v = (row01 focus).vertices (.inl ((row01 focus).leftPole 0)) ∨
        v = (row01 focus).vertices (.inr ((row01 focus).rightPole 0)) := by
  decide

/-- The sum of the two factor canonical divisors, supported on core vertices. -/
def row02Weight : Fin 8 → ℤ := ![0, 0, 0, 1, 1, 0, 1, 1]

theorem row02_weight_nonneg : ∀ v, 0 ≤ row02Weight v := by decide

theorem row02_weight_sum : (∑ v, row02Weight v) = 4 := by decide

theorem row02_weight_left (focus : Fin 2) :
    ∀ a : Fin 4, row02Weight ((row02 focus).vertices (.inl a)) =
      ((row02 focus).leftCore.incidenceDegree a : ℤ) - 2 := by
  fin_cases focus <;> decide

theorem row02_weight_right (focus : Fin 2) :
    ∀ b : Fin 4, row02Weight ((row02 focus).vertices (.inr b)) =
      ((row02 focus).rightCore.incidenceDegree b : ℤ) - 2 := by
  fin_cases focus <;> decide

theorem row02_coverage :
    ∀ v : Fin 8, 1 ≤ row02Weight v ∨
      ∃ focus : Fin 2,
        v = (row02 focus).vertices (.inl ((row02 focus).leftPole 0)) ∨
        v = (row02 focus).vertices (.inr ((row02 focus).rightPole 0)) := by
  decide

/-- The sum of the two factor canonical divisors, supported on core vertices. -/
def row03Weight : Fin 8 → ℤ := ![1, 1, 0, 0, 1, 1, 0, 0]

theorem row03_weight_nonneg : ∀ v, 0 ≤ row03Weight v := by decide

theorem row03_weight_sum : (∑ v, row03Weight v) = 4 := by decide

theorem row03_weight_left (focus : Fin 2) :
    ∀ a : Fin 4, row03Weight ((row03 focus).vertices (.inl a)) =
      ((row03 focus).leftCore.incidenceDegree a : ℤ) - 2 := by
  fin_cases focus <;> decide

theorem row03_weight_right (focus : Fin 2) :
    ∀ b : Fin 4, row03Weight ((row03 focus).vertices (.inr b)) =
      ((row03 focus).rightCore.incidenceDegree b : ℤ) - 2 := by
  fin_cases focus <;> decide

theorem row03_coverage :
    ∀ v : Fin 8, 1 ≤ row03Weight v ∨
      ∃ focus : Fin 2,
        v = (row03 focus).vertices (.inl ((row03 focus).leftPole 0)) ∨
        v = (row03 focus).vertices (.inr ((row03 focus).rightPole 0)) := by
  decide

/-- The sum of the two factor canonical divisors, supported on core vertices. -/
def row04Weight : Fin 8 → ℤ := ![1, 0, 1, 0, 0, 1, 1, 0]

theorem row04_weight_nonneg : ∀ v, 0 ≤ row04Weight v := by decide

theorem row04_weight_sum : (∑ v, row04Weight v) = 4 := by decide

theorem row04_weight_left (focus : Fin 2) :
    ∀ a : Fin 4, row04Weight ((row04 focus).vertices (.inl a)) =
      ((row04 focus).leftCore.incidenceDegree a : ℤ) - 2 := by
  fin_cases focus <;> decide

theorem row04_weight_right (focus : Fin 2) :
    ∀ b : Fin 4, row04Weight ((row04 focus).vertices (.inr b)) =
      ((row04 focus).rightCore.incidenceDegree b : ℤ) - 2 := by
  fin_cases focus <;> decide

theorem row04_coverage :
    ∀ v : Fin 8, 1 ≤ row04Weight v ∨
      ∃ focus : Fin 2,
        v = (row04 focus).vertices (.inl ((row04 focus).leftPole 0)) ∨
        v = (row04 focus).vertices (.inr ((row04 focus).rightPole 0)) := by
  decide

/-- The sum of the two factor canonical divisors, supported on core vertices. -/
def row07Weight : Fin 8 → ℤ := ![0, 0, 1, 1, 0, 0, 1, 1]

theorem row07_weight_nonneg : ∀ v, 0 ≤ row07Weight v := by decide

theorem row07_weight_sum : (∑ v, row07Weight v) = 4 := by decide

theorem row07_weight_left (focus : Fin 2) :
    ∀ a : Fin 4, row07Weight ((row07 focus).vertices (.inl a)) =
      ((row07 focus).leftCore.incidenceDegree a : ℤ) - 2 := by
  fin_cases focus <;> decide

theorem row07_weight_right (focus : Fin 2) :
    ∀ b : Fin 4, row07Weight ((row07 focus).vertices (.inr b)) =
      ((row07 focus).rightCore.incidenceDegree b : ℤ) - 2 := by
  fin_cases focus <;> decide

theorem row07_coverage :
    ∀ v : Fin 8, 1 ≤ row07Weight v ∨
      ∃ focus : Fin 2,
        v = (row07 focus).vertices (.inl ((row07 focus).leftPole 0)) ∨
        v = (row07 focus).vertices (.inr ((row07 focus).rightPole 0)) := by
  decide

end AtanasovRanganathan.GenusFiveTwoPoleData
