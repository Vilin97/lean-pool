/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseDefs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Sim.Defs

/-!
# Dense-overlay instruction simulation -- controller definitions

These definitions connect the dense instruction kernels to the existing
fixed-program selector and representation-independent buffered cleanup pass.
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- Execute one selected instruction against the dense public-input overlay. -/
def denseExecuteInstructionTM {n : ℕ} (tapes : ControlInstructionTapes n) :
    Instr → TM (n + 1)
  | .imm destination value =>
      TM.seqTM
        (denseImmediateInstructionTM tapes.data destination value).retargetOutput
        (TM.binarySuccTM tapes.liftedPC)
  | .add destination source₀ source₁ =>
      TM.seqTM
        (denseDirectBinaryInstructionTM tapes.data .add destination source₀
          source₁).retargetOutput
        (TM.binarySuccTM tapes.liftedPC)
  | .sub destination source₀ source₁ =>
      TM.seqTM
        (denseDirectBinaryInstructionTM tapes.data .sub destination source₀
          source₁).retargetOutput
        (TM.binarySuccTM tapes.liftedPC)
  | .mul destination source₀ source₁ =>
      TM.seqTM
        (denseDirectBinaryInstructionTM tapes.data .mul destination source₀
          source₁).retargetOutput
        (TM.binarySuccTM tapes.liftedPC)
  | .load destination addressRegister =>
      TM.seqTM
        (denseIndirectLoadInstructionTM tapes.data destination
          addressRegister).retargetOutput
        (TM.binarySuccTM tapes.liftedPC)
  | .store addressRegister source =>
      TM.seqTM
        (denseIndirectStoreInstructionTM tapes.data addressRegister
          source).retargetOutput
        (TM.binarySuccTM tapes.liftedPC)
  | .jz source target =>
      finishControlInstructionTM tapes
        (denseZeroJumpInstructionTM tapes.lifted source target)
  | .jmp target =>
      finishControlInstructionTM tapes (jumpInstructionTM tapes.lifted target)
  | .halt =>
      finishControlInstructionTM tapes (haltInstructionTM (n := n + 1))

/-- Dense finite branch tree selected by a decrementing PC copy. -/
def denseDispatchProgramTM {n : ℕ} (tapes : ControlInstructionTapes n)
    (program : Program) : TM (n + 1) :=
  dispatchWithTM tapes (denseExecuteInstructionTM tapes) program

/-- Copy the dense snapshot PC into selector scratch and dispatch once. -/
def denseProgramInstructionTM {n : ℕ} (tapes : ControlInstructionTapes n)
    (program : Program) : TM (n + 1) :=
  TM.seqTM
    (TM.binaryCopyIntoTM tapes.liftedPC tapes.liftedLhs tapes.liftedFound)
    (denseDispatchProgramTM tapes program)

/-- Mutable overlay after one dense instruction. -/
def denseInstructionStore (input : List Bool) (instruction : Instr)
    (pcValue : ℕ) (overlay : Store) : Store :=
  (DenseOverlay.Snapshot.stepInstr input instruction
    { pc := pcValue, overlay := overlay }).overlay

/-- Program counter after one dense instruction. -/
def denseInstructionPC (input : List Bool) (instruction : Instr)
    (pcValue : ℕ) (overlay : Store) : ℕ :=
  (DenseOverlay.Snapshot.stepInstr input instruction
    { pc := pcValue, overlay := overlay }).pc

/-- Exact values left on the five physical cleanup roles by a dense kernel. -/
def denseInstructionCleanupValue (input : List Bool)
    (instruction : Instr) (overlay : Store) : Fin 5 → ℕ
  | 0 =>
      match instruction with
      | .imm destination _ | .add destination _ _ |
          .sub destination _ _ | .mul destination _ _ |
          .load destination _ => destination
      | .store addressRegister _ =>
          DenseOverlay.read input overlay addressRegister
      | .jz _ _ | .jmp _ | .halt => 0
  | 1 =>
      match instruction with
      | .imm _ value => value + 1
      | .add _ source₀ source₁ =>
          DenseOverlay.read input overlay source₀ +
            DenseOverlay.read input overlay source₁ + 1
      | .sub _ source₀ source₁ =>
          (DenseOverlay.read input overlay source₀ -
            DenseOverlay.read input overlay source₁) + 1
      | .mul _ source₀ source₁ =>
          DenseOverlay.read input overlay source₀ *
            DenseOverlay.read input overlay source₁ + 1
      | .load _ addressRegister =>
          DenseOverlay.read input overlay
            (DenseOverlay.read input overlay addressRegister) + 1
      | .store _ source => DenseOverlay.read input overlay source + 1
      | .jz _ _ | .jmp _ | .halt => 0
  | 2 =>
      match instruction with
      | .imm destination _ | .add destination _ _ |
          .sub destination _ _ | .mul destination _ _ |
          .load destination _ =>
          if destination ∈ overlay.map Prod.fst then 1 else 0
      | .store addressRegister _ =>
          if DenseOverlay.read input overlay addressRegister ∈
              overlay.map Prod.fst then 1 else 0
      | .jz _ _ | .jmp _ | .halt => 0
  | 3 =>
      match instruction with
      | .add _ source₀ _ | .sub _ source₀ _ | .mul _ source₀ _ =>
          DenseOverlay.read input overlay source₀
      | .load _ addressRegister | .store addressRegister _ =>
          DenseOverlay.read input overlay addressRegister
      | .imm _ _ | .jz _ _ | .jmp _ | .halt => 0
  | _ =>
      match instruction with
      | .add _ _ source₁ | .sub _ _ source₁ | .mul _ _ source₁ =>
          DenseOverlay.read input overlay source₁
      | .store _ source => DenseOverlay.read input overlay source
      | .imm _ _ | .load _ _ | .jz _ _ | .jmp _ | .halt => 0

/-- Old overlay counter state before generic buffered cleanup. -/
def denseInstructionRemainingValue (instruction : Instr)
    (overlay : Store) : ℕ :=
  match instruction with
  | .imm _ _ | .add _ _ _ | .sub _ _ _ | .mul _ _ _ |
      .load _ _ | .store _ _ => 0
  | .jz _ _ | .jmp _ | .halt => overlay.length

/-- Common dense semantic endpoint before representation cleanup. -/
abbrev DenseInstructionExecutionResult {n : ℕ}
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (instruction : Instr) (pcValue : ℕ) (overlay : Store)
    (work : Fin (n + 1) → Tape) : Prop :=
  BufferedInstructionResult tapes overlay
    (denseInstructionStore input instruction pcValue overlay)
    (denseInstructionPC input instruction pcValue overlay)
    (denseInstructionCleanupValue input instruction overlay)
    (denseInstructionRemainingValue instruction overlay) work

/-- Dense endpoint plus the marker and source-cursor bounds needed by cleanup. -/
abbrev DenseInstructionCleanupReady {n : ℕ}
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (instruction : Instr) (pcValue : ℕ) (overlay : Store)
    (sourceHeadBound : ℕ) (work : Fin (n + 1) → Tape) : Prop :=
  BufferedCleanupReady tapes overlay
    (denseInstructionStore input instruction pcValue overlay)
    (denseInstructionPC input instruction pcValue overlay)
    (denseInstructionCleanupValue input instruction overlay)
    (denseInstructionRemainingValue instruction overlay)
    sourceHeadBound work

/-- Runtime of one statically selected dense instruction before cleanup. -/
def denseExecuteInstructionTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (instruction : Instr) (pcValue : ℕ) (overlay : Store) : ℕ :=
  match instruction with
  | .imm destination value =>
      denseImmediateInstructionTime tapes.data overlay destination value + 1 +
        TM.binarySuccTime pcValue
  | .add destination source₀ source₁ =>
      denseDirectBinaryInstructionTime tapes.data .add input overlay destination
        source₀ source₁ + 1 + TM.binarySuccTime pcValue
  | .sub destination source₀ source₁ =>
      denseDirectBinaryInstructionTime tapes.data .sub input overlay destination
        source₀ source₁ + 1 + TM.binarySuccTime pcValue
  | .mul destination source₀ source₁ =>
      denseDirectBinaryInstructionTime tapes.data .mul input overlay destination
        source₀ source₁ + 1 + TM.binarySuccTime pcValue
  | .load destination addressRegister =>
      denseIndirectLoadInstructionTime tapes.data input overlay destination
        addressRegister + 1 + TM.binarySuccTime pcValue
  | .store addressRegister source =>
      denseIndirectStoreInstructionTime tapes.data input overlay addressRegister
        source + 1 + TM.binarySuccTime pcValue
  | .jz source target =>
      denseZeroJumpInstructionTime tapes.lifted input overlay pcValue source
        target + 1 + (overlay.flatMap Entry.encode).length + 1
  | .jmp target =>
      jumpInstructionTime pcValue target + 1 +
        (overlay.flatMap Entry.encode).length + 1
  | .halt =>
      haltInstructionTime + 1 + (overlay.flatMap Entry.encode).length + 1

/-- Dense branch-tree runtime for a represented selector. -/
def denseDispatchProgramTime {n : ℕ} (tapes : ControlInstructionTapes n)
    (input : List Bool) (overlay : Store) (pcValue : ℕ) :
    Program → ℕ → ℕ :=
  dispatchWithTime tapes
    (fun instruction =>
      denseExecuteInstructionTime tapes input instruction pcValue overlay)

/-- Complete dense selection and selected-instruction runtime. -/
def denseProgramInstructionTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (pcValue : ℕ) (overlay : Store) : ℕ :=
  TM.binaryCopyTime pcValue 0 + 1 +
    denseDispatchProgramTime tapes input overlay pcValue program pcValue

/-- Select, execute, and clean one dense RAM instruction. -/
def denseProgramStepTM {n : ℕ} (tapes : ControlInstructionTapes n)
    (program : Program) : TM (n + 1) :=
  TM.seqTM (denseProgramInstructionTM tapes program)
    (instructionCleanupTM tapes)

/-- Source-head bound after dense selection and execution. -/
def denseProgramStepSourceHeadBound {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (pcValue : ℕ) (overlay : Store) : ℕ :=
  1 + denseProgramInstructionTime tapes program input pcValue overlay

/-- Exact compositional time for one selected and cleaned dense RAM step. -/
noncomputable def denseProgramStepTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (pcValue : ℕ) (overlay : Store) : ℕ :=
  let instruction := selectedInstruction program pcValue
  let nextStore := denseInstructionStore input instruction pcValue overlay
  denseProgramInstructionTime tapes program input pcValue overlay + 1 +
    bufferedCleanupTime tapes overlay nextStore
      (denseInstructionCleanupValue input instruction overlay)
      (denseInstructionRemainingValue instruction overlay)
      (denseProgramStepSourceHeadBound tapes program input pcValue overlay)

end Machine
end RegisterStore
end RAM
end Complexity
