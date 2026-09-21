/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Internal

/-!
# Sparse RAM program controller

The fixed-program halt test copies the canonical sparse-snapshot PC, walks a
finite decrementing selector, restores its scratch, and writes `1` exactly when
the selected instruction is `halt`.
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

@[simp] theorem instructionHaltOutput_head (instruction : Instr) :
    (instructionHaltOutput instruction).head = 1 :=
  instructionHaltOutput_head_internal instruction

@[simp] theorem instructionHaltOutput_cells_zero (instruction : Instr) :
    (instructionHaltOutput instruction).cells 0 = Γ.start :=
  instructionHaltOutput_cells_zero_internal instruction

theorem instructionHaltOutput_cells_ne_start (instruction : Instr) :
    ∀ j, j ≥ 1 → (instructionHaltOutput instruction).cells j ≠ Γ.start :=
  instructionHaltOutput_cells_ne_start_internal instruction

@[simp] theorem instructionHaltOutput_cell_one_eq_one_iff
    (instruction : Instr) :
    (instructionHaltOutput instruction).cells 1 = Γ.one ↔
      instruction = .halt :=
  instructionHaltOutput_cell_one_eq_one_iff_internal instruction

@[simp] theorem instructionHaltOutput_eq_blank_of_ne_halt
    {instruction : Instr} (h : instruction ≠ .halt) :
    instructionHaltOutput instruction =
      (Tape.init []).move Dir3.right :=
  instructionHaltOutput_eq_blank_of_ne_halt_internal h

/-- The canonical work-tape image of a sparse snapshot satisfies the complete
reusable instruction ABI. -/
theorem programSnapshotWork_ready {n : ℕ}
    (tapes : ControlInstructionTapes n) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    InstructionExecutionReady tapes snapshot.store snapshot.pc
      (programSnapshotWork tapes snapshot) :=
  programSnapshotWork_ready_internal tapes snapshot hcanonical

@[simp] theorem registerVerdictOutput_cell_one (value : ℕ) :
    (registerVerdictOutput value).cells 1 =
      if value = 0 then Γ.zero else Γ.one :=
  registerVerdictOutput_cell_one_internal value

/-- Final sparse lookup recovers `R₀` and emits zero exactly for value zero,
or one for any nonzero value. -/
theorem programOutputTM_hoareTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (store : Store) (pcValue : ℕ)
    (initialWork : Fin (n + 1) → Tape) (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) :
    (programOutputTM tapes).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp _work out =>
        inp = inp₀ ∧
        out = registerVerdictOutput (RegisterStore.read store 0))
      (programOutputTime tapes store) :=
  programOutputTM_hoareTime_internal tapes store pcValue initialWork inp₀
    hready hinput

/-- Final sparse lookup overwrites the loop's halt-test bit with the RAM
verdict, allowing direct controller/extractor composition. -/
theorem programOutputTM_hoareTime_haltOutput {n : ℕ}
    (tapes : ControlInstructionTapes n) (store : Store) (pcValue : ℕ)
    (initialWork : Fin (n + 1) → Tape) (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) :
    (programOutputTM tapes).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = instructionHaltOutput .halt)
      (fun inp _work out =>
        inp = inp₀ ∧
        out = registerVerdictOutput (RegisterStore.read store 0))
      (programOutputTime tapes store) :=
  programOutputTM_hoareTime_haltOutput_internal tapes store pcValue
    initialWork inp₀ hready hinput

/-- The fixed-program test preserves the complete clean instruction ABI and
emits the exact sparse snapshot's halt status. -/
theorem programHaltTM_hoareTime_frame {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (store : Store) (pcValue : ℕ)
    (initialWork : Fin (n + 1) → Tape) (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) :
    (programHaltTM tapes program).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        let snapshot : Snapshot := { pc := pcValue, store := store }
        inp = inp₀ ∧ work = initialWork ∧
        out = instructionHaltOutput (snapshot.curInstr program))
      (programHaltTime tapes program pcValue) := by
  simpa [Snapshot.curInstr, selectedInstruction_eq_getElem?_getD] using
    programHaltTM_hoareTime_frame_internal tapes program store pcValue
      initialWork inp₀ hready hinput

/-- A halted sparse snapshot is stationary under both one pure step and every
fuel-bounded run. -/
theorem Snapshot.step_eq_self_of_halted (program : Program)
    (snapshot : Snapshot) (hhalted : snapshot.Halted program) :
    snapshot.step program = snapshot :=
  snapshot_step_eq_self_of_halted_internal program snapshot hhalted

/-- Running a halted sparse snapshot for arbitrary additional fuel is a no-op. -/
theorem Snapshot.run_halted (program : Program) (snapshot : Snapshot)
    (hhalted : snapshot.Halted program) (fuel : ℕ) :
    snapshot.run program fuel = snapshot :=
  snapshot_run_halted_internal program snapshot hhalted fuel

/-- If the pure fuel-bounded sparse run is halted, the fixed controller loop
reaches that exact reusable snapshot and exposes its halt verdict. -/
theorem programLoopTM_hoareTime_run {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (fuel : ℕ) (snapshot : Snapshot)
    (initialWork : Fin (n + 1) → Tape) (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes snapshot.store snapshot.pc
      initialWork)
    (hinput : TM.Parked inp₀)
    (hhalted : (snapshot.run program fuel).Halted program) :
    (programLoopTM tapes program).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        let final := snapshot.run program fuel
        inp = inp₀ ∧
        InstructionExecutionReady tapes final.store final.pc work ∧
        out = instructionHaltOutput (final.curInstr program))
      (programLoopTime tapes program (fuel + 1) snapshot) :=
  programLoopTM_hoareTime_run_internal tapes program fuel snapshot
    initialWork inp₀ hready hinput hhalted

end Machine

end RegisterStore

end RAM

end Complexity
