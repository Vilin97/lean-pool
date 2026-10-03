/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseControl
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseSimDefs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Sim.Control

/-!
# Dense-overlay control-instruction simulation
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

variable {n : ℕ}

private theorem denseInput_parked (input : List Bool) :
    TM.Parked ((Tape.init (input.map Γ.ofBool)).move Dir3.right) := by
  refine ⟨by simp [Tape.move], ?_⟩
  simpa using Tape.init_ofBool_move_right_cells_ne_start input

private theorem blankOutput_parked :
    TM.Parked ((Tape.init []).move Dir3.right) := by
  refine ⟨by simp [Tape.move], ?_⟩
  intro j hj
  simp [Tape.init, Tape.move]
  omega

/-- Dense conditional-zero execution preserves the overlay and exposes the
generic buffered endpoint. -/
theorem denseExecuteInstructionTM_jz_hoareTime_frame
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue source target : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseExecuteInstructionTM tapes (.jz source target)).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseInstructionExecutionResult tapes input (.jz source target)
          pcValue overlay work ∧
        out = (Tape.init []).move Dir3.right)
      (denseExecuteInstructionTime tapes input (.jz source target)
        pcValue overlay) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let out₀ := (Tape.init []).move Dir3.right
  let newPC := if DenseOverlay.read input overlay source = 0 then target
    else pcValue + 1
  have hcontrol := denseZeroJumpInstructionTM_hoareTime_frame tapes.lifted
    input overlay pcValue source target initialWork out₀ hvalid
    hready.control blankOutput_parked
  have hfinish :=
    finishBufferedControlInstructionTM_hoareTime_frame_internal tapes overlay
      pcValue newPC initialWork inp₀ out₀
      (denseZeroJumpInstructionTM tapes.lifted source target)
      (denseZeroJumpInstructionTime tapes.lifted input overlay pcValue source
        target)
      hready (denseInput_parked input) blankOutput_parked
      (by simpa [inp₀, newPC] using hcontrol)
  have hcleanup :
      denseInstructionCleanupValue input (.jz source target) overlay =
        fun _ => 0 := by
    funext slot
    fin_cases slot <;> rfl
  by_cases hzero : DenseOverlay.read input overlay source = 0
  · simpa [inp₀, out₀, newPC, denseExecuteInstructionTM,
      denseExecuteInstructionTime, DenseInstructionExecutionResult,
      denseInstructionStore, denseInstructionPC, hcleanup,
      denseInstructionRemainingValue, DenseOverlay.Snapshot.stepInstr,
      hzero] using hfinish
  · simpa [inp₀, out₀, newPC, denseExecuteInstructionTM,
      denseExecuteInstructionTime, DenseInstructionExecutionResult,
      denseInstructionStore, denseInstructionPC, hcleanup,
      denseInstructionRemainingValue, DenseOverlay.Snapshot.stepInstr,
      hzero] using hfinish

/-- Dense unconditional-jump execution preserves the overlay and exposes the
generic buffered endpoint. -/
theorem denseExecuteInstructionTM_jmp_hoareTime_frame
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue target : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseExecuteInstructionTM tapes (.jmp target)).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseInstructionExecutionResult tapes input (.jmp target)
          pcValue overlay work ∧
        out = (Tape.init []).move Dir3.right)
      (denseExecuteInstructionTime tapes input (.jmp target)
        pcValue overlay) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let out₀ := (Tape.init []).move Dir3.right
  have hcontrol := jumpInstructionTM_hoareTime_frame_internal tapes.lifted
    overlay pcValue target initialWork inp₀ out₀ hready.control
    (denseInput_parked input) blankOutput_parked
  have hfinish :=
    finishBufferedControlInstructionTM_hoareTime_frame_internal tapes overlay
      pcValue target initialWork inp₀ out₀
      (jumpInstructionTM tapes.lifted target)
      (jumpInstructionTime pcValue target) hready (denseInput_parked input)
      blankOutput_parked hcontrol
  have hcleanup : denseInstructionCleanupValue input (.jmp target) overlay =
      fun _ => 0 := by
    funext slot
    fin_cases slot <;> rfl
  simpa [inp₀, out₀, denseExecuteInstructionTM,
    denseExecuteInstructionTime, DenseInstructionExecutionResult,
    denseInstructionStore, denseInstructionPC, hcleanup,
    denseInstructionRemainingValue,
    DenseOverlay.Snapshot.stepInstr] using hfinish

/-- Dense halt execution preserves both the overlay and program counter and
exposes the generic buffered endpoint. -/
theorem denseExecuteInstructionTM_halt_hoareTime_frame
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseExecuteInstructionTM tapes .halt).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseInstructionExecutionResult tapes input .halt pcValue overlay
          work ∧
        out = (Tape.init []).move Dir3.right)
      (denseExecuteInstructionTime tapes input .halt pcValue overlay) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let out₀ := (Tape.init []).move Dir3.right
  have hcontrol := haltInstructionTM_hoareTime_frame_internal tapes.lifted
    overlay pcValue initialWork inp₀ out₀ hready.control
    (denseInput_parked input) blankOutput_parked
  have hfinish :=
    finishBufferedControlInstructionTM_hoareTime_frame_internal tapes overlay
      pcValue pcValue initialWork inp₀ out₀
      (haltInstructionTM (n := n + 1)) haltInstructionTime hready
      (denseInput_parked input) blankOutput_parked hcontrol
  have hcleanup : denseInstructionCleanupValue input .halt overlay =
      fun _ => 0 := by
    funext slot
    fin_cases slot <;> rfl
  simpa [inp₀, out₀, denseExecuteInstructionTM,
    denseExecuteInstructionTime, DenseInstructionExecutionResult,
    denseInstructionStore, denseInstructionPC, hcleanup,
    denseInstructionRemainingValue,
    DenseOverlay.Snapshot.stepInstr] using hfinish

end Machine
end RegisterStore
end RAM
end Complexity
