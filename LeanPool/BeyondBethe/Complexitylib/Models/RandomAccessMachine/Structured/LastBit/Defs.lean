/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Scanner.Defs

/-!
# Structured RAM last-bit scanner — definitions

This is a second consumer of the typed finite-state scanner API. Its state is
`Option Bool`: `none` before any input and `some bit` thereafter.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace LastBit

instance optionBoolFinEnum : FinEnum (Option Bool) :=
  FinEnum.ofList [none, some false, some true] (by
    intro state
    rcases state with _ | bit
    · simp
    · cases bit <;> simp)

/-- Typed scanner for whether the final input bit equals `target`. -/
def spec (target : Bool) : Scanner.TypedSpec (Option Bool) where
  initial := none
  step := fun _ bit => some bit
  accept := fun state => decide (state = some target)

/-- Final verdict register inherited from the scanner layout. -/
abbrev verdictReg : ℕ := Scanner.lengthReg

/-- Reserved-prefix input store for the last-bit scanner. -/
abbrev inputStore (target : Bool) : List Bool → Store := (spec target).inputStore

/-- Structured RAM last-bit program. -/
abbrev program (target : Bool) : Cmd := (spec target).program

/-- Concrete compiled RAM last-bit program. -/
abbrev compiled (target : Bool) : Program := (spec target).compiled

/-- Exact compiled transition count. -/
abbrev stepCount (target : Bool) : ℕ → ℕ := (spec target).stepCount

/-- Explicit logarithmic-time budget. -/
abbrev timeBound (target : Bool) : ℕ → ℕ := (spec target).timeBound

/-- Explicit peak-space budget. -/
abbrev spaceBound (target : Bool) : ℕ → ℕ := (spec target).spaceBound

/-- Shifted quasilinear comparison function. -/
abbrev quasilinearBound (target : Bool) : ℕ → ℕ :=
  (spec target).quasilinearBound

end LastBit

end Structured

end RAM

end Complexity
