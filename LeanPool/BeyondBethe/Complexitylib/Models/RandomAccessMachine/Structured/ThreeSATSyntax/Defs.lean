/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Scanner.Defs
public import LeanPool.BeyondBethe.Complexitylib.SAT.ThreeSAT.Syntax

/-!
# Structured RAM exact-3-CNF syntax scanner — definitions

This is the larger typed-scanner benchmark: the existing 27-state bit-level
3-CNF syntax automaton is compiled without a handwritten numeric transition
table or benchmark-specific execution invariant.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace ThreeSATSyntax

open SAT.ThreeSAT

instance : FinEnum Syntax.TokenState :=
  FinEnum.ofList
    (((List.finRange 4).map Syntax.TokenState.between) ++
      ((List.finRange 4).map Syntax.TokenState.inLit) ++ [.invalid]) (by
      intro state
      cases state <;> simp)

instance : FinEnum Syntax.BitState :=
  FinEnum.ofList
    (((FinEnum.toList Syntax.TokenState).map Syntax.BitState.ready) ++
      (FinEnum.toList Syntax.TokenState).flatMap fun state =>
        [.half state false, .half state true]) (by
      intro state
      cases state with
      | ready state => simp
      | half state bit => cases bit <;> simp)

/-- The existing exact-3-CNF syntax automaton as a typed scanner specification. -/
def spec : Scanner.TypedSpec Syntax.BitState where
  initial := Syntax.bitStart
  step := Syntax.bitStep
  accept := Syntax.accept

/-- Final verdict register inherited from the scanner layout. -/
abbrev verdictReg : ℕ := Scanner.lengthReg

/-- Reserved-prefix input store for the syntax scanner. -/
abbrev inputStore : List Bool → Store := spec.inputStore

/-- Structured RAM exact-3-CNF syntax program. -/
abbrev program : Cmd := spec.program

/-- Concrete compiled RAM exact-3-CNF syntax program. -/
abbrev compiled : Program := spec.compiled

/-- Exact compiled transition count. -/
abbrev stepCount : ℕ → ℕ := spec.stepCount

/-- Explicit logarithmic-time budget. -/
abbrev timeBound : ℕ → ℕ := spec.timeBound

/-- Explicit peak-space budget. -/
abbrev spaceBound : ℕ → ℕ := spec.spaceBound

/-- Shifted quasilinear comparison function. -/
abbrev quasilinearBound : ℕ → ℕ := spec.quasilinearBound

end ThreeSATSyntax

end Structured

end RAM

end Complexity
