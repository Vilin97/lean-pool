/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Defs
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# Sparse RAM decision-machine resource-bound definitions

The concrete simulator has fixed control once its RAM program is fixed.  The
only program-dependent quantities that matter asymptotically are therefore
collected in `programResourceMagnitude`.  `programDecisionScale` combines
that constant with the public input length and the charged logarithmic RAM
time.  The fourth-power envelope is deliberately coarse: it keeps the public
class-transfer theorem independent of low-level controller constants while
still recording a genuine polynomial simulation.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- A positive magnitude containing every natural literal of one instruction. -/
def instructionResourceMagnitude : Instr → ℕ
  | .imm destination value => destination + value + 1
  | .add destination source₀ source₁
  | .sub destination source₀ source₁
  | .mul destination source₀ source₁ =>
      destination + source₀ + source₁ + 1
  | .load destination addressRegister
  | .store destination addressRegister => destination + addressRegister + 1
  | .jz source target => source + target + 1
  | .jmp target => target + 1
  | .halt => 1

/-- One positive fixed constant containing the program length and every
hardwired register, immediate, and jump literal. -/
def programResourceMagnitude (program : Program) : ℕ :=
  program.length + (program.map instructionResourceMagnitude).sum + 1

/-- Common width/count scale for a run with charged logarithmic time `cost`. -/
def programDecisionScale (program : Program) (inputLength cost : ℕ) : ℕ :=
  inputLength + cost * (programResourceMagnitude program + 2) +
    programResourceMagnitude program + 3

/-- Coarse checked polynomial envelope for the complete concrete simulation. -/
def programDecisionEnvelope (program : Program) (inputLength cost : ℕ) : ℕ :=
  1000000000 * programResourceMagnitude program *
    (programDecisionScale program inputLength cost + 1) ^ 4

end Machine

end RegisterStore

end RAM

end Complexity
