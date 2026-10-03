/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseCtrlSim
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseSimData

/-!
# Dense-overlay instruction simulation
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- Every statically selected RAM instruction realizes the common dense
buffered snapshot-step contract. -/
theorem denseExecuteInstructionTM_hoareTime_frame {n : ℕ}
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (instruction : Instr) (overlay : Store) (pcValue : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseExecuteInstructionTM tapes instruction).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseInstructionExecutionResult tapes input instruction pcValue
          overlay work ∧
        out = (Tape.init []).move Dir3.right)
      (denseExecuteInstructionTime tapes input instruction pcValue
        overlay) := by
  cases instruction with
  | imm destination value =>
      exact denseExecuteInstructionTM_imm_hoareTime_frame tapes input overlay
        pcValue destination value initialWork hvalid hready
  | add destination source₀ source₁ =>
      exact denseExecuteInstructionTM_add_hoareTime_frame tapes input overlay
        pcValue destination source₀ source₁ initialWork hvalid hready
  | sub destination source₀ source₁ =>
      exact denseExecuteInstructionTM_sub_hoareTime_frame tapes input overlay
        pcValue destination source₀ source₁ initialWork hvalid hready
  | mul destination source₀ source₁ =>
      exact denseExecuteInstructionTM_mul_hoareTime_frame tapes input overlay
        pcValue destination source₀ source₁ initialWork hvalid hready
  | load destination addressRegister =>
      exact denseExecuteInstructionTM_load_hoareTime_frame tapes input overlay
        pcValue destination addressRegister initialWork hvalid hready
  | store addressRegister source =>
      exact denseExecuteInstructionTM_store_hoareTime_frame tapes input overlay
        pcValue addressRegister source initialWork hvalid hready
  | jz source target =>
      exact denseExecuteInstructionTM_jz_hoareTime_frame tapes input overlay
        pcValue source target initialWork hvalid hready
  | jmp target =>
      exact denseExecuteInstructionTM_jmp_hoareTime_frame tapes input overlay
        pcValue target initialWork hready
  | halt =>
      exact denseExecuteInstructionTM_halt_hoareTime_frame tapes input overlay
        pcValue initialWork hready

end Machine
end RegisterStore
end RAM
end Complexity
