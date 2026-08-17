/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# ErLV maximal-gap arithmetic for the convex three-distance argument

This file isolates the integer bookkeeping in draft Sections 3--4.  A
`K3Majorant` records cover moves, equivalently polygon sides consumed at its
two ends.  In particular, the first majorant's fields are the draft's `a,b`;
they are not counts of interior points.  This is the convention documented in
REVIEW1 D5 and is the one for which the rank budget is `a + b ≤ 2`.

Signed integers are used for arc differences.  Thus the case `L < 0`, where
`u` precedes `y` in unwrapped order, is represented rather than discarded.
-/

namespace LeanPool.Erdos132ConvexK3

/-- Cover moves at the two ends of a `k = 3` majorant.

For the majorant of `zx`, `leftMoves = a` counts moves at the `x`-end and
`rightMoves = b` counts moves at the `z`-end.  For the majorant of `tu`, the
same fields are the draft's `α,β`.  Every move consumes one polygon side and
strictly raises one of the three distance ranks, hence at most two moves. -/
structure K3Majorant where
  /-- Cover moves made at the first endpoint. -/
  leftMoves : ℕ
  /-- Cover moves made at the second endpoint. -/
  rightMoves : ℕ
  coverBudget : leftMoves + rightMoves ≤ 2

/-- Arithmetic data retained from the two ErLV majorants after choosing a
vertex with maximal first-neighbor gap. -/
structure ErLVK3MaximalGapSetup where
  /-- Majorant issuing from the maximal-gap vertex. -/
  first : K3Majorant
  /-- Facing majorant issuing three cyclic steps later. -/
  second : K3Majorant
  /-- First-neighbor gap at the selected maximal-gap vertex. -/
  gapX : ℕ
  /-- First-neighbor gap at the facing vertex. -/
  gapT : ℕ
  gapT_le_gapX : gapT ≤ gapX
  /-- `M = |us|_sides`; the second majorant consumes at least these moves at
  its `u`-end. -/
  M : ℕ
  M_le_secondRight : M ≤ second.rightMoves

namespace ErLVK3MaximalGapSetup

/-- The maximal-gap slack `δ = gₓ - gₜ`. -/
def delta (D : ErLVK3MaximalGapSetup) : ℕ := D.gapX - D.gapT

/-- The signed side difference `L = |yu|_sides = 3 - δ`. -/
def L (D : ErLVK3MaximalGapSetup) : ℤ := 3 - (D.delta : ℤ)

/-- The signed side difference `|yz| = L + M + b`. -/
def yzSides (D : ErLVK3MaximalGapSetup) : ℤ :=
  D.L + (D.M : ℤ) + (D.first.rightMoves : ℤ)

end ErLVK3MaximalGapSetup

/-- Maximality gives the exact corrected formula `L = 3 - δ`, not merely
ErLV's printed loose upper bound. -/
theorem maximal_gap_L_eq_three_sub_delta (D : ErLVK3MaximalGapSetup) :
    D.L = 3 - (D.delta : ℤ) := rfl

/-- The corrected maximal-gap formula implies the sharp signed bound `L ≤ 3`. -/
theorem maximal_gap_L_le_three (D : ErLVK3MaximalGapSetup) : D.L ≤ 3 := by
  simp [ErLVK3MaximalGapSetup.L]

/-- With unwrapped indices `t=x+3`, `y=x+gₓ`, and `u=t+gₜ`, maximality
turns the signed arc difference `u-y` into `3-δ`. -/
theorem maximal_gap_signed_yu
    (D : ErLVK3MaximalGapSetup) {x t y u : ℤ}
    (ht : t = x + 3)
    (hy : y = x + (D.gapX : ℤ))
    (hu : u = t + (D.gapT : ℤ)) :
    u - y = D.L := by
  unfold ErLVK3MaximalGapSetup.L ErLVK3MaximalGapSetup.delta
  rw [Nat.cast_sub (R := ℤ) D.gapT_le_gapX]
  omega

/-- Signed arc arithmetic remains valid when `L < 0`: if
`u-y=L`, `s-u=M`, and `z-s=b`, then `z-y=L+M+b`. -/
theorem signed_arc_arithmetic
    {y u s z L M b : ℤ}
    (hyu : u - y = L)
    (hus : s - u = M)
    (hsz : z - s = b) :
    z - y = L + M + b := by
  omega

/-- The second majorant gives the draft bound `M ≤ 2`. -/
theorem majorant_M_le_two (D : ErLVK3MaximalGapSetup) : D.M ≤ 2 := by
  calc
    D.M ≤ D.second.rightMoves := D.M_le_secondRight
    _ ≤ D.second.leftMoves + D.second.rightMoves := Nat.le_add_left _ _
    _ ≤ 2 := D.second.coverBudget

/-- The complete signed arc identity for the maximal-gap setup. -/
theorem maximal_gap_signed_yz
    (D : ErLVK3MaximalGapSetup) {x t y u s z : ℤ}
    (ht : t = x + 3)
    (hy : y = x + (D.gapX : ℤ))
    (hu : u = t + (D.gapT : ℤ))
    (hus : s - u = (D.M : ℤ))
    (hsz : z - s = (D.first.rightMoves : ℤ)) :
    z - y = D.yzSides := by
  rw [signed_arc_arithmetic (maximal_gap_signed_yu D ht hy hu) hus hsz]
  rfl

/-- The five and only five integer rows for which the short-arc inequality
`L + M + b ≤ 5` fails under the `k = 3` majorant budgets. -/
def IsExceptionalMajorantRow (a b L M : ℤ) : Prop :=
  (a = 0 ∧ b = 1 ∧ L = 3 ∧ M = 2) ∨
  (a = 1 ∧ b = 1 ∧ L = 3 ∧ M = 2) ∨
  (a = 0 ∧ b = 2 ∧ L = 2 ∧ M = 2) ∨
  (a = 0 ∧ b = 2 ∧ L = 3 ∧ M = 1) ∨
  (a = 0 ∧ b = 2 ∧ L = 3 ∧ M = 2)

/-- Transparent Presburger certification of draft table (3.5)/(Section 4):
the short-arc bound fails exactly on the five displayed `(a,b,L,M)` rows. -/
theorem five_row_enumeration
    {a b L M δ : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hM0 : 0 ≤ M) (hδ : 0 ≤ δ)
    (hcover : a + b ≤ 2) (hM2 : M ≤ 2)
    (hL : L = 3 - δ) :
    5 < L + M + b ↔ IsExceptionalMajorantRow a b L M := by
  simp only [IsExceptionalMajorantRow]
  omega

/-- The structure-level form of `five_row_enumeration`, with `a,b,L,M`
read directly from the two majorants and maximal-gap data. -/
theorem maximal_gap_five_row_enumeration (D : ErLVK3MaximalGapSetup) :
    5 < D.yzSides ↔
      IsExceptionalMajorantRow
        D.first.leftMoves D.first.rightMoves D.L D.M := by
  change
    5 < D.L + (D.M : ℤ) + (D.first.rightMoves : ℤ) ↔
      IsExceptionalMajorantRow
        D.first.leftMoves D.first.rightMoves D.L D.M
  apply five_row_enumeration (δ := (D.delta : ℤ))
  · exact_mod_cast Nat.zero_le D.first.leftMoves
  · exact_mod_cast Nat.zero_le D.first.rightMoves
  · exact_mod_cast Nat.zero_le D.M
  · exact_mod_cast Nat.zero_le D.delta
  · exact_mod_cast D.first.coverBudget
  · exact_mod_cast majorant_M_le_two D
  · rfl

/-- A negative signed `L` can never be exceptional; it forces the desired
short-arc bound directly. -/
theorem negative_L_short_arc (D : ErLVK3MaximalGapSetup) (hL : D.L < 0) :
    D.yzSides ≤ 5 := by
  have hb : D.first.rightMoves ≤ 2 := by
    calc
      D.first.rightMoves ≤ D.first.leftMoves + D.first.rightMoves :=
        Nat.le_add_left _ _
      _ ≤ 2 := D.first.coverBudget
  have hb' : (D.first.rightMoves : ℤ) ≤ 2 := by exact_mod_cast hb
  have hM' : (D.M : ℤ) ≤ 2 := by exact_mod_cast majorant_M_le_two D
  unfold ErLVK3MaximalGapSetup.yzSides
  omega

end LeanPool.Erdos132ConvexK3
