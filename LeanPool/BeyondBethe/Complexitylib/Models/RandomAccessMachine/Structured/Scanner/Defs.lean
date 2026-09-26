/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Defs
public import Mathlib.Data.FinEnum

/-!
# Finite-state scanners for the structured RAM frontend

`Scanner.Spec` describes a finite automaton using numeric state codes. The
compiler below realizes it as a table-driven structured RAM program. The state
bound and transition-closure fields are the complete trusted interface needed by
the generic correctness and resource proof.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace Scanner

/-- A total finite-state Boolean scanner with contiguous numeric state codes. -/
structure Spec where
  /-- Number of valid state codes. -/
  stateCount : ℕ
  /-- Initial state code. -/
  initial : ℕ
  /-- The initial code is valid. -/
  initial_lt : initial < stateCount
  /-- One state transition. -/
  step : ℕ → Bool → ℕ
  /-- Transitions preserve valid state codes. -/
  step_lt : ∀ state, state < stateCount → ∀ bit, step state bit < stateCount
  /-- Final Boolean verdict. -/
  accept : ℕ → Bool

/-- A scanner specification over an explicitly enumerable Lean state type.

`FinEnum` retains a concrete equivalence with an initial segment of natural
numbers, so lowering remains executable while consumers reason using their
domain-specific state type. -/
structure TypedSpec (State : Type) [FinEnum State] where
  /-- Initial typed state. -/
  initial : State
  /-- One typed state transition. -/
  step : State → Bool → State
  /-- Final Boolean verdict. -/
  accept : State → Bool

namespace TypedSpec

variable {State : Type} [FinEnum State]

/-- Numeric state code chosen by the explicit enumeration. -/
def code (state : State) : ℕ := (FinEnum.equiv state).val

/-- Lower a typed scanner to the verified numeric scanner interface. -/
def numeric (typed : TypedSpec State) : Spec where
  stateCount := FinEnum.card State
  initial := code typed.initial
  initial_lt := (FinEnum.equiv typed.initial).isLt
  step := fun state bit =>
    if hstate : state < FinEnum.card State then
      code (typed.step (FinEnum.equiv.symm ⟨state, hstate⟩) bit)
    else 0
  step_lt := by
    intro state hstate bit
    simp [hstate, code]
  accept := fun state =>
    if hstate : state < FinEnum.card State then
      typed.accept (FinEnum.equiv.symm ⟨state, hstate⟩)
    else false

end TypedSpec

/-- Remaining input length and final verdict register. -/
def lengthReg : ℕ := 0
/-- Current numeric automaton state. -/
def stateReg : ℕ := 1
/-- Address of the next input bit. -/
def pointerReg : ℕ := 2
/-- Constant-one register. -/
def oneReg : ℕ := 3
/-- Current input bit. -/
def bitReg : ℕ := 4
/-- Scratch address used for table lookups. -/
def addressReg : ℕ := 5
/-- Constant-two register. -/
def twoReg : ℕ := 6
/-- Register containing the transition-table base address. -/
def transitionBaseReg : ℕ := 7
/-- Register containing the verdict-table base address. -/
def acceptBaseReg : ℕ := 8
/-- First transition-table register. -/
def transitionBase : ℕ := 9

/-- First verdict-table register. -/
def acceptBase (spec : Spec) : ℕ :=
  transitionBase + 2 * spec.stateCount

/-- First input register. -/
def inputBase (spec : Spec) : ℕ :=
  transitionBase + 3 * spec.stateCount

/-- Address of one transition-table entry. -/
def transitionAddress (state : ℕ) (bit : Bool) : ℕ :=
  transitionBase + 2 * state + Input.bitValue bit

/-- Address of one verdict-table entry. -/
def acceptAddress (spec : Spec) (state : ℕ) : ℕ :=
  acceptBase spec + state

/-- Reserved-prefix input layout for a scanner. -/
def inputStore (spec : Spec) (bits : List Bool) : Store :=
  Input.bitStore lengthReg (inputBase spec) bits

/-- The six fixed setup destinations below the tables. -/
def fixedSetupIndices : List ℕ :=
  [stateReg, pointerReg, oneReg, twoReg, transitionBaseReg, acceptBaseReg]

/-- Every table destination, in increasing order. -/
def tableIndices (spec : Spec) : List ℕ :=
  List.range' transitionBase (3 * spec.stateCount)

/-- Every setup destination. -/
def setupIndices (spec : Spec) : List ℕ :=
  fixedSetupIndices ++ tableIndices spec

/-- Value written to one setup destination. -/
def setupValue (spec : Spec) (index : ℕ) : ℕ :=
  if index = stateReg then spec.initial
  else if index = pointerReg then inputBase spec
  else if index = oneReg then 1
  else if index = twoReg then 2
  else if index = transitionBaseReg then transitionBase
  else if index = acceptBaseReg then acceptBase spec
  else if index < acceptBase spec then
    let offset := index - transitionBase
    spec.step (offset / 2) (offset % 2 = 1)
  else
    Input.bitValue (spec.accept (index - acceptBase spec))

/-- Constant and table writes performed before scanning. -/
def setupWrites (spec : Spec) : List (ℕ × ℕ) :=
  (setupIndices spec).map fun index => (index, setupValue spec index)

/-- Straight-line setup instruction list. -/
def setupOps (spec : Spec) : List Basic :=
  (setupWrites spec).map fun write => .imm write.1 write.2

/-- Initialize constants and transition/verdict tables. -/
def setup (spec : Spec) : Cmd := Cmd.basics (setupOps spec)

/-- Seven-instruction scanner body, independent of the particular automaton. -/
def bodyOps : List Basic :=
  [.load bitReg pointerReg,
    .mul addressReg stateReg twoReg,
    .add addressReg addressReg bitReg,
    .add addressReg addressReg transitionBaseReg,
    .load stateReg addressReg,
    .add pointerReg pointerReg oneReg,
    .sub lengthReg lengthReg oneReg]

/-- Consume one input bit and update the encoded automaton state. -/
def body : Cmd := Cmd.basics bodyOps

/-- Scan all input bits. -/
def mainLoop : Cmd := Cmd.whileNonzero lengthReg body

/-- Two-instruction final verdict lookup. -/
def finalizeOps : List Basic :=
  [.add addressReg stateReg acceptBaseReg, .load lengthReg addressReg]

/-- Write the final verdict to `R₀`. -/
def finalize : Cmd := Cmd.basics finalizeOps

/-- Complete structured scanner. -/
def program (spec : Spec) : Cmd :=
  Cmd.seq (setup spec) (.seq mainLoop finalize)

/-- Concrete compiled RAM scanner. -/
def compiled (spec : Spec) : Program := (program spec).compile

/-- Exact compiled transition count. -/
def stepCount (spec : Spec) (inputLength : ℕ) : ℕ :=
  9 + 3 * spec.stateCount + 9 * inputLength

/-- Explicit logarithmic-cost time budget. -/
def timeBound (spec : Spec) (inputLength : ℕ) : ℕ :=
  64 * (inputLength + spec.stateCount + 1) *
    (bitlen (inputLength + inputBase spec) + 1)

/-- Explicit peak-space budget. -/
def spaceBound (spec : Spec) (inputLength : ℕ) : ℕ :=
  (inputLength + inputBase spec) *
    (2 * bitlen (inputLength + inputBase spec))

/-- Shifted quasilinear comparison function. -/
def quasilinearBound (spec : Spec) (inputLength : ℕ) : ℕ :=
  (inputLength + inputBase spec) *
    (bitlen (inputLength + inputBase spec) + 1)

namespace TypedSpec

variable {State : Type} [FinEnum State]

/-- Input store for a typed scanner. -/
abbrev inputStore (typed : TypedSpec State) : List Bool → Store :=
  Scanner.inputStore typed.numeric

/-- Structured RAM program generated from a typed scanner. -/
abbrev program (typed : TypedSpec State) : Cmd := Scanner.program typed.numeric

/-- Concrete RAM program generated from a typed scanner. -/
abbrev compiled (typed : TypedSpec State) : Program := Scanner.compiled typed.numeric

/-- Exact transition count for a typed scanner. -/
abbrev stepCount (typed : TypedSpec State) : ℕ → ℕ :=
  Scanner.stepCount typed.numeric

/-- Explicit logarithmic-time budget for a typed scanner. -/
abbrev timeBound (typed : TypedSpec State) : ℕ → ℕ :=
  Scanner.timeBound typed.numeric

/-- Explicit peak-space budget for a typed scanner. -/
abbrev spaceBound (typed : TypedSpec State) : ℕ → ℕ :=
  Scanner.spaceBound typed.numeric

/-- Shifted quasilinear comparison function for a typed scanner. -/
abbrev quasilinearBound (typed : TypedSpec State) : ℕ → ℕ :=
  Scanner.quasilinearBound typed.numeric

end TypedSpec

end Scanner

end Structured

end RAM

end Complexity
