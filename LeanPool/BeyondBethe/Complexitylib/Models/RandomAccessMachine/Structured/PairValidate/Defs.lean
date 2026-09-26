/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Scanner.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.PairValidate.Defs

/-!
# Structured RAM pair-encoding validator — definitions

The benchmark-specific implementation is just a numeric presentation of the
same five-state automaton used by `TM.pairValidateTM`. The generic scanner
compiler supplies the table-driven structured RAM program.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace PairValidate

instance : FinEnum TM.PairValidateState :=
  FinEnum.ofList [.next, .afterZero, .afterOne, .suffix, .invalid] (by
    intro state
    cases state <;> simp)

/-- Pair validation as a typed finite-state scanner specification. -/
def typedSpec : Scanner.TypedSpec TM.PairValidateState where
  initial := .next
  step := TM.pairValidateStep
  accept := TM.pairValidateAccept

/-- Numeric lowering used by the generic structured RAM compiler. -/
abbrev spec : Scanner.Spec := typedSpec.numeric

/-- Final verdict register inherited from the scanner layout. -/
abbrev lengthReg : ℕ := Scanner.lengthReg
/-- First input register for the five-state instance. -/
abbrev inputBase : ℕ := Scanner.inputBase spec
/-- Reserved-prefix input store for pair validation. -/
abbrev inputStore : List Bool → Store := Scanner.inputStore spec
/-- Structured RAM pair-validator program. -/
abbrev program : Cmd := Scanner.program spec
/-- Concrete compiled RAM pair-validator program. -/
abbrev compiled : Program := Scanner.compiled spec
/-- Exact compiled transition count. -/
abbrev stepCount : ℕ → ℕ := Scanner.stepCount spec
/-- Explicit logarithmic-time budget. -/
abbrev timeBound : ℕ → ℕ := Scanner.timeBound spec
/-- Explicit peak-space budget. -/
abbrev spaceBound : ℕ → ℕ := Scanner.spaceBound spec
/-- Shifted quasilinear comparison function. -/
abbrev quasilinearBound : ℕ → ℕ := Scanner.quasilinearBound spec

end PairValidate

end Structured

end RAM

end Complexity
