/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Defs

/-!
# Dense public input with a sparse mutable overlay -- definitions

The ordinary sparse snapshot eagerly materializes every nonzero public-input
register. That representation is convenient but occupies `Theta(n log n)`
cells before the RAM executes a step. This module separates the immutable input
bank from the mutable register overlay.

An overlay entry `(address, tag)` represents the actual value `tag - 1`.
Because every stored tag is positive, an absent address is distinguishable from
an explicit write of zero (`tag = 1`). Absent reads fall through to the dense
public-input ABI `RAM.initRegs input`.
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace DenseOverlay

/-- Mutable tagged entries layered over the immutable public-input bank. -/
abbrev Store := RegisterStore.Store

/-- Read through the sparse tagged overlay, falling back to the public input. -/
def read (input : List Bool) (overlay : Store) (address : ℕ) : ℕ :=
  let tag := RegisterStore.read overlay address
  if tag = 0 then RAM.initRegs input address else tag - 1

/-- Record an explicit mutable value. The positive tag preserves written zero. -/
def write (overlay : Store) (address value : ℕ) : Store :=
  RegisterStore.write overlay address (value + 1)

/-- A valid overlay has unique addresses and positive tags. -/
abbrev Canonical (overlay : Store) : Prop := RegisterStore.Canonical overlay

/-- Register zero is materialized in every concrete overlay. This lets the
dense-input lookup specialize its fallback path to positive input addresses. -/
def CoversZero (overlay : Store) : Prop :=
  RegisterStore.read overlay 0 ≠ 0

/-- Full representation invariant for the mutable overlay. -/
def Valid (overlay : Store) : Prop :=
  Canonical overlay ∧ CoversZero overlay

/-- Decode the dense-input/overlay pair to a total RAM register file. -/
def decode (input : List Bool) (overlay : Store) : ℕ → ℕ := read input overlay

/-- A finite mutable overlay plus program counter. The immutable input remains
on the Turing input tape and is not duplicated in this snapshot. -/
structure Snapshot where
  /-- Current RAM program counter. -/
  pc : ℕ
  /-- Sparse positive-tag overlay. -/
  overlay : Store
  deriving DecidableEq

namespace Snapshot

/-- Decode one dense-overlay snapshot against its immutable public input. -/
def decode (input : List Bool) (snapshot : Snapshot) : RAM.Cfg where
  pc := snapshot.pc
  regs := DenseOverlay.decode input snapshot.overlay

/-- Reuse the checked sparse snapshot codec for the tagged mutable overlay. -/
def encode (snapshot : Snapshot) : List Bool :=
  RegisterStore.Snapshot.encode { pc := snapshot.pc, store := snapshot.overlay }

/-- The initial mutable overlay materializes only `R₀ = input.length`; all input
bits remain in the read-only dense bank. The stored positive tag is
`input.length + 1`. -/
def initial (input : List Bool) : Snapshot :=
  { pc := 0, overlay := DenseOverlay.write [] 0 input.length }

/-- Instruction selected by the current program counter. -/
def curInstr (program : Program) (snapshot : Snapshot) : Instr :=
  (program[snapshot.pc]?).getD .halt

/-- Whether the selected instruction is `halt`. -/
def Halted (program : Program) (snapshot : Snapshot) : Prop :=
  snapshot.curInstr program = .halt

instance (program : Program) (snapshot : Snapshot) :
    Decidable (snapshot.Halted program) := by
  unfold Halted
  infer_instance

/-- Execute one RAM instruction against the decoded input/overlay register
file, recording the result as a positive tag. -/
def stepInstr (input : List Bool) : Instr → Snapshot → Snapshot
  | .imm destination value, snapshot =>
      { pc := snapshot.pc + 1
        overlay := DenseOverlay.write snapshot.overlay destination value }
  | .add destination source₀ source₁, snapshot =>
      { pc := snapshot.pc + 1
        overlay := DenseOverlay.write snapshot.overlay destination
          (DenseOverlay.read input snapshot.overlay source₀ +
            DenseOverlay.read input snapshot.overlay source₁) }
  | .sub destination source₀ source₁, snapshot =>
      { pc := snapshot.pc + 1
        overlay := DenseOverlay.write snapshot.overlay destination
          (DenseOverlay.read input snapshot.overlay source₀ -
            DenseOverlay.read input snapshot.overlay source₁) }
  | .mul destination source₀ source₁, snapshot =>
      { pc := snapshot.pc + 1
        overlay := DenseOverlay.write snapshot.overlay destination
          (DenseOverlay.read input snapshot.overlay source₀ *
            DenseOverlay.read input snapshot.overlay source₁) }
  | .load destination addressRegister, snapshot =>
      { pc := snapshot.pc + 1
        overlay := DenseOverlay.write snapshot.overlay destination
          (DenseOverlay.read input snapshot.overlay
            (DenseOverlay.read input snapshot.overlay addressRegister)) }
  | .store addressRegister source, snapshot =>
      { pc := snapshot.pc + 1
        overlay := DenseOverlay.write snapshot.overlay
          (DenseOverlay.read input snapshot.overlay addressRegister)
          (DenseOverlay.read input snapshot.overlay source) }
  | .jz source target, snapshot =>
      if DenseOverlay.read input snapshot.overlay source = 0 then
        { snapshot with pc := target }
      else
        { snapshot with pc := snapshot.pc + 1 }
  | .jmp target, snapshot => { snapshot with pc := target }
  | .halt, snapshot => snapshot

/-- Execute the instruction selected by the current program counter. -/
def step (program : Program) (input : List Bool) (snapshot : Snapshot) : Snapshot :=
  snapshot.stepInstr input (snapshot.curInstr program)

/-- Fuel-bounded dense-overlay execution, stopping once halted. -/
def run (program : Program) (input : List Bool) : ℕ → Snapshot → Snapshot
  | 0, snapshot => snapshot
  | fuel + 1, snapshot =>
      if snapshot.Halted program then snapshot
      else run program input fuel (snapshot.step program input)

end Snapshot
end DenseOverlay
end RegisterStore
end RAM
end Complexity
