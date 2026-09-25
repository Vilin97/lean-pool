/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Sim.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Sim.Control
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Sim.Data
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Sim.Internal

/-!
# Fixed-program sparse RAM dispatch

The dispatch machine copies the canonical PC, walks a fixed decrementing
branch tree, and runs the selected instruction with a uniform next-store work
buffer. This surface currently exposes its structural transducer and coarse
all-prefix space certificates; semantic selection is proved in the internal
execution layer.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

private theorem parked_blank :
    TM.Parked ((Tape.init []).move Dir3.right) := by
  refine ⟨by simp [Tape.move], ?_⟩
  intro j hj
  simp [Tape.move, Tape.init, show j ≠ 0 by omega]

private theorem hasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t := by
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem copyWorkToWorkTM_isTransducer {n : ℕ}
    (source destination : Fin n) :
    (TM.copyWorkToWorkTM source destination).IsTransducer := by
  intro state iHead wHeads oHead
  cases state <;> dsimp only [TM.copyWorkToWorkTM, TM.allIdle]
  · split <;> simp only [TM.idleDir] <;> split <;> decide
  · simp only [TM.idleDir]
    split <;> decide

/-- Pure branch-tree selection agrees with list lookup and the RAM model's
out-of-range `halt` convention. -/
theorem selectedInstruction_eq_getElem?_getD (program : Program)
    (selector : ℕ) :
    selectedInstruction program selector =
      (program[selector]?).getD Instr.halt := by
  induction program generalizing selector with
  | nil => simp [selectedInstruction]
  | cons instruction program ih =>
      cases selector with
      | zero => simp [selectedInstruction]
      | succ selector => simp [selectedInstruction, ih]

/-- Public generic correctness rule for the finite decrementing dispatch
tree. -/
theorem dispatchProgramTM_hoareTime_of_execute {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (store : Store) (pcValue selector : ℕ)
    (cleanWork work₀ : Fin (n + 1) → Tape) (inp₀ out₀ : Tape)
    (hready : DispatchReady tapes store pcValue selector cleanWork work₀)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀)
    (hexecute : ∀ instruction,
      (executeInstructionTM tapes instruction).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = cleanWork ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          InstructionExecutionResult tapes instruction pcValue store work ∧
          out = out₀)
        (executeInstructionTime tapes instruction pcValue store)) :
    (dispatchProgramTM tapes program).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes
          (selectedInstruction program selector) pcValue store work ∧
        out = out₀)
      (dispatchProgramTime tapes store pcValue program selector) :=
  dispatchProgramTM_hoareTime_of_execute_internal tapes program store pcValue
    selector cleanWork work₀ inp₀ out₀ hready hinput houtput hexecute

/-- Every statically selected RAM instruction realizes the common buffered
snapshot-step contract. -/
theorem executeInstructionTM_hoareTime_frame {n : ℕ}
    (tapes : ControlInstructionTapes n) (instruction : Instr)
    (store : Store) (pcValue : ℕ) (initialWork : Fin (n + 1) → Tape)
    (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) :
    (executeInstructionTM tapes instruction).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes instruction pcValue store work ∧
        out = (Tape.init []).move Dir3.right)
      (executeInstructionTime tapes instruction pcValue store) := by
  have hblank := parked_blank
  cases instruction with
  | imm destination value =>
      exact executeInstructionTM_imm_hoareTime_frame tapes store pcValue
        destination value initialWork inp₀ hready hinput
  | add destination source₀ source₁ =>
      exact executeInstructionTM_add_hoareTime_frame tapes store pcValue
        destination source₀ source₁ initialWork inp₀ hready hinput
  | sub destination source₀ source₁ =>
      exact executeInstructionTM_sub_hoareTime_frame tapes store pcValue
        destination source₀ source₁ initialWork inp₀ hready hinput
  | mul destination source₀ source₁ =>
      exact executeInstructionTM_mul_hoareTime_frame tapes store pcValue
        destination source₀ source₁ initialWork inp₀ hready hinput
  | load destination addressRegister =>
      exact executeInstructionTM_load_hoareTime_frame tapes store pcValue
        destination addressRegister initialWork inp₀ hready hinput
  | store addressRegister source =>
      exact executeInstructionTM_store_hoareTime_frame tapes store pcValue
        addressRegister source initialWork inp₀ hready hinput
  | jz source target =>
      exact executeInstructionTM_jz_hoareTime_frame tapes store pcValue source
        target initialWork inp₀ ((Tape.init []).move Dir3.right) hready hinput
        hblank
  | jmp target =>
      exact executeInstructionTM_jmp_hoareTime_frame tapes store pcValue target
        initialWork inp₀ ((Tape.init []).move Dir3.right) hready hinput hblank
  | halt =>
      exact executeInstructionTM_halt_hoareTime_frame tapes store pcValue
        initialWork inp₀ ((Tape.init []).move Dir3.right) hready hinput hblank

/-- Copy the canonical PC into dispatch scratch, select the fixed program
instruction, and realize one exact sparse snapshot step. -/
theorem programInstructionTM_hoareTime_frame {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (store : Store) (pcValue : ℕ) (initialWork : Fin (n + 1) → Tape)
    (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) :
    (programInstructionTM tapes program).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes
          (selectedInstruction program pcValue) pcValue store work ∧
        out = (Tape.init []).move Dir3.right)
      (programInstructionTime tapes program pcValue store) := by
  let selectorTape :=
    (Tape.init (pcValue.bits.map Γ.ofBool)).move Dir3.right
  let selectorWork :=
    Function.update initialWork tapes.liftedLhs selectorTape
  have hcopy := TM.binaryCopyIntoTM_hoareTime_frame tapes.liftedPC
    tapes.liftedLhs tapes.liftedFound tapes.lifted.pc_ne_lhs
    (tapes.lifted.pc_ne 11) (tapes.lifted.data.ne (by decide)) pcValue 0
    inp₀ initialWork ((Tape.init []).move Dir3.right) hready.control.pc
    hready.control.lookup.destination hready.control.lookup.copyScratch hinput
    (fun i _ _ _ => hready.control.lookup.scanner.parked i) parked_blank
  have hselectorReady : DispatchReady tapes store pcValue pcValue initialWork
      selectorWork := by
    exact ⟨hready, rfl⟩
  have hdispatch := dispatchProgramTM_hoareTime_of_execute tapes program store
    pcValue pcValue initialWork selectorWork inp₀
    ((Tape.init []).move Dir3.right) hselectorReady hinput parked_blank
    (fun instruction => executeInstructionTM_hoareTime_frame tapes instruction
      store pcValue initialWork inp₀ hready hinput)
  have hselectorParked : ∀ i, TM.Parked (selectorWork i) := by
    intro i
    by_cases hi : i = tapes.liftedLhs
    · subst i
      simp only [selectorWork, Function.update_self]
      exact hasBinaryNat_parked (Tape.init_move_right_hasBinaryNat pcValue)
    · simp only [selectorWork, Function.update_of_ne hi]
      exact hready.control.lookup.scanner.parked i
  have hseq := TM.seqTM_hoareTime
    (TM.binaryCopyIntoTM tapes.liftedPC tapes.liftedLhs tapes.liftedFound)
    (dispatchProgramTM tapes program) hcopy
    (by
      rintro inp work out ⟨hinp, hworkEq, hout⟩
      have hinpParked : TM.Parked inp := by simpa [hinp] using hinput
      have houtParked : TM.Parked out := by simpa [hout] using parked_blank
      have hworkParked : ∀ i, TM.Parked (work i) := by
        simpa [hworkEq, selectorWork, selectorTape] using hselectorParked
      obtain ⟨hi, hw, ho⟩ :=
        TM.phaseTransition_eq_self_of_reads_ne_start
          hinpParked.read_ne_start
          (fun i => (hworkParked i).read_ne_start)
          houtParked.read_ne_start
      rw [hi, hw, ho]
      exact ⟨hinp, by simpa [selectorWork, selectorTape] using hworkEq, hout⟩)
    hdispatch
  simpa only [programInstructionTM, programInstructionTime, selectorWork,
    selectorTape] using hseq

/-- Restore the clean instruction ABI after a buffered instruction result. -/
theorem instructionCleanupTM_hoareTime_frame {n : ℕ}
    (tapes : ControlInstructionTapes n) (instruction : Instr)
    (pcValue : ℕ) (store : Store) (sourceHeadBound : ℕ)
    (initialWork : Fin (n + 1) → Tape) (inp₀ out₀ : Tape)
    (hready : InstructionCleanupReady tapes instruction pcValue store
      sourceHeadBound initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (instructionCleanupTM tapes).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionReady tapes
          (instructionStore instruction pcValue store)
          (instructionPC instruction pcValue store) work ∧
        out = out₀)
      (instructionCleanupTime tapes instruction pcValue store
        sourceHeadBound) :=
  instructionCleanupTM_hoareTime_frame_internal tapes instruction pcValue
    store sourceHeadBound initialWork inp₀ out₀ hready hinput houtput

/-- One fixed-program RAM step returns directly to the reusable clean ABI for
the exact successor sparse snapshot. -/
theorem programStepTM_hoareTime_frame {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (store : Store) (pcValue : ℕ)
    (initialWork : Fin (n + 1) → Tape) (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) :
    (programStepTM tapes program).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        let next :=
          ({ pc := pcValue, store := store } : Snapshot).step program
        inp = inp₀ ∧
        InstructionExecutionReady tapes next.store next.pc work ∧
        out = (Tape.init []).move Dir3.right)
      (programStepTime tapes program pcValue store) := by
  have hstep := programStepTM_hoareTime_frame_internal tapes program store
    pcValue initialWork inp₀ hready hinput
    (programInstructionTM_hoareTime_frame tapes program store pcValue
      initialWork inp₀ hready hinput)
  refine hstep.consequence (fun _ _ _ h => h) ?_ le_rfl
  rintro inp work out ⟨hinp, hnext, hout⟩
  refine ⟨hinp, ?_, hout⟩
  simpa [instructionStore, instructionPC, Snapshot.step, Snapshot.curInstr,
    selectedInstruction_eq_getElem?_getD] using hnext

/-- Control execution followed by unchanged-store copying is append-only on
the real output tape. -/
theorem finishControlInstructionTM_isTransducer {n : ℕ}
    (tapes : ControlInstructionTapes n) (control : TM (n + 1))
    (hcontrol : control.IsTransducer) :
    (finishControlInstructionTM tapes control).IsTransducer :=
  hcontrol.seqTM
    (copyWorkToWorkTM_isTransducer tapes.liftedSource tapes.buffer)

/-- Every statically selected RAM instruction is append-only on real output. -/
theorem executeInstructionTM_isTransducer {n : ℕ}
    (tapes : ControlInstructionTapes n) (instruction : Instr) :
    (executeInstructionTM tapes instruction).IsTransducer := by
  cases instruction with
  | imm destination value =>
      exact (TM.retargetOutput_isTransducer _).seqTM
        (TM.binarySuccTM_isTransducer tapes.liftedPC)
  | add destination source₀ source₁ =>
      exact (TM.retargetOutput_isTransducer _).seqTM
        (TM.binarySuccTM_isTransducer tapes.liftedPC)
  | sub destination source₀ source₁ =>
      exact (TM.retargetOutput_isTransducer _).seqTM
        (TM.binarySuccTM_isTransducer tapes.liftedPC)
  | mul destination source₀ source₁ =>
      exact (TM.retargetOutput_isTransducer _).seqTM
        (TM.binarySuccTM_isTransducer tapes.liftedPC)
  | load destination addressRegister =>
      exact (TM.retargetOutput_isTransducer _).seqTM
        (TM.binarySuccTM_isTransducer tapes.liftedPC)
  | store addressRegister source =>
      exact (TM.retargetOutput_isTransducer _).seqTM
        (TM.binarySuccTM_isTransducer tapes.liftedPC)
  | jz source target =>
      exact finishControlInstructionTM_isTransducer tapes _
        (zeroJumpInstructionTM_isTransducer tapes.lifted source target)
  | jmp target =>
      exact finishControlInstructionTM_isTransducer tapes _
        (jumpInstructionTM_isTransducer tapes.lifted target)
  | halt =>
      exact finishControlInstructionTM_isTransducer tapes _
        haltInstructionTM_isTransducer

/-- Every node of the fixed finite dispatch tree preserves one-way output. -/
theorem dispatchProgramTM_isTransducer {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program) :
    (dispatchProgramTM tapes program).IsTransducer := by
  induction program with
  | nil =>
      simpa only [dispatchProgramTM] using
        ((TM.resetBinaryWorkTM_isTransducer tapes.liftedLhs).seqTM
          (executeInstructionTM_isTransducer tapes .halt))
  | cons instruction program ih =>
      simpa only [dispatchProgramTM] using
        ((executeInstructionTM_isTransducer tapes instruction).branchWorkBlankTM
          ((TM.binaryPredTM_isTransducer tapes.liftedLhs).seqTM ih))

/-- Fixed-program selection followed by selected execution preserves one-way
output. -/
theorem programInstructionTM_isTransducer {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program) :
    (programInstructionTM tapes program).IsTransducer :=
  (TM.binaryCopyIntoTM_isTransducer tapes.liftedPC tapes.liftedLhs
    tapes.liftedFound).seqTM (dispatchProgramTM_isTransducer tapes program)

/-- Every prefix of fixed-program selection and execution stays within the
initial auxiliary space plus its advertised total running-time bound. -/
theorem programInstructionTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (pcValue : ℕ) (store : Store)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg (n + 1)
      (programInstructionTM tapes program).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (programInstructionTM tapes program).reachesIn time start current)
    (htime : time ≤ programInstructionTime tapes program pcValue store) :
    current.WithinAuxSpace inputLength
      (initialSpace + programInstructionTime tapes program pcValue store) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

end Machine

end RegisterStore

end RAM

end Complexity
