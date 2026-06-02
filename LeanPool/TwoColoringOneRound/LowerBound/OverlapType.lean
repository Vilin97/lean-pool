/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
/-!
Overlap types for ordered pairs of vertices can be encoded as `3×3` partial permutation matrices.
We represent such a matrix as a `Nat` bitmask with 9 bits in row-major order.

This file provides the core combinatorial operations needed to compute the orbital-algebra structure
constants for fixed `n` (eventually instantiated to `n = 10^6`).
-/

namespace Distributed2Coloring.LowerBound


/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Mask := Nat

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def bit (i : Nat) : Nat := (1 : Nat) <<< i

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def transposeMask3x3 (m : Mask) : Mask :=
  let step := fun out (i j : Nat) =>
    if m.testBit (i * 3 + j) then out ||| bit (j * 3 + i) else out
  step (step (step (step (step (step (step (step (step 0 0 0) 0 1) 0 2) 1 0) 1 1) 1 2) 2 0) 2 1) 2 2

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def rowHas (m : Mask) (i j : Nat) : Bool :=
  m.testBit (i * 3 + j)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def decodePartialPerm (m : Mask) : Fin 3 → Option (Fin 3) :=
  fun i =>
    let r := i.1
    if rowHas m r 0 then some ⟨0, by decide⟩
    else if rowHas m r 1 then some ⟨1, by decide⟩
    else if rowHas m r 2 then some ⟨2, by decide⟩
    else none

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def IsPartialPermMask (m : Mask) : Prop :=
  (∀ i : Fin 3, (Finset.filter (fun j : Fin 3 => m.testBit (i.1 * 3 + j.1)) Finset.univ).card ≤ 1) ∧
  (∀ j : Fin 3, (Finset.filter (fun i : Fin 3 => m.testBit (i.1 * 3 + j.1)) Finset.univ).card ≤ 1)

end Distributed2Coloring.LowerBound
