/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseDecisionDefs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseInitProof
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseInternal

/-!
# Complete dense-overlay RAM decision-machine proof internals
-/


public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

variable {n : ℕ}

/-- The complete dense machine realizes one halted overlay run and emits its
decoded `R₀` verdict. -/
theorem denseProgramDecisionTM_hoareTime_run_internal
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (fuel : ℕ)
    (hhalted : ((DenseOverlay.Snapshot.initial input).run program input fuel).Halted
      program) :
    (denseProgramDecisionTM tapes program).HoareTime
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _inp _work out =>
        let final := (DenseOverlay.Snapshot.initial input).run program input fuel
        out = registerVerdictOutput
          (DenseOverlay.read input final.overlay 0))
      (denseProgramDecisionTime tapes program input fuel) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  let initial := DenseOverlay.Snapshot.initial input
  let final := initial.run program input fuel
  have hinit := denseProgramInitTM_hoareTime_internal tapes input
  obtain ⟨initDone, initTime, hinitTime, hinitReach, hinitHalt,
      hinitInput, hinitWork, hinitOutput⟩ :=
    hinit _ _ _ ⟨rfl, rfl, rfl⟩
  have hinitialValid : DenseOverlay.Valid initial.overlay := by
    simpa only [initial] using DenseOverlay.Snapshot.initial_valid input
  let sparseInitial : Snapshot :=
    { pc := initial.pc, store := initial.overlay }
  have hready : InstructionExecutionReady tapes initial.overlay initial.pc
      initDone.work := by
    rw [hinitWork]
    simpa only [denseProgramSnapshotWork, sparseInitial] using
      programSnapshotWork_ready_internal tapes sparseInitial hinitialValid.1
  have hinitInputParked : TM.Parked initDone.input := by
    rw [hinitInput]
    refine ⟨by simp [Tape.move], ?_⟩
    simpa using Tape.init_ofBool_move_right_cells_ne_start input
  have hloop := denseProgramLoopTM_hoareTime_run_internal tapes program input
    fuel initial initDone.work hinitialValid hready hhalted
  obtain ⟨loopDone, loopTime, hloopTime, hloopReach, hloopHalt,
      hloopInput, hloopReady, hloopOutput⟩ :=
    hloop _ _ _ ⟨rfl, rfl, by simpa [TM.resetBinaryBlank] using hinitOutput⟩
  have hloopInputParked : TM.Parked loopDone.input := by
    rw [hloopInput]
    rw [← hinitInput]
    exact hinitInputParked
  have hloopOutputHalt : loopDone.output = instructionHaltOutput .halt := by
    change loopDone.output = instructionHaltOutput (final.curInstr program)
      at hloopOutput
    rw [show final.curInstr program = .halt from hhalted] at hloopOutput
    exact hloopOutput
  have hfinalValid : DenseOverlay.Valid final.overlay := by
    simpa only [final, initial] using DenseOverlay.Snapshot.run_valid
      program input fuel (DenseOverlay.Snapshot.initial input)
        (DenseOverlay.Snapshot.initial_valid input)
  have houtputRun := denseProgramOutputTM_hoareTime_haltOutput_internal tapes
    input final.overlay final.pc loopDone.work hfinalValid hloopReady
  obtain ⟨outputDone, outputTime, houtputTime, houtputReach,
      houtputHalt, houtputInput, houtputVerdict⟩ :=
    houtputRun _ _ _ ⟨hloopInput, rfl, hloopOutputHalt⟩
  have hloopOutputParked : TM.Parked loopDone.output := by
    rw [hloopOutputHalt]
    refine ⟨?_, instructionHaltOutput_cells_ne_start_internal .halt⟩
    rw [instructionHaltOutput_head_internal]
  have houtputReach' : (denseProgramOutputTM tapes).reachesIn outputTime
      { state := (denseProgramOutputTM tapes).qstart
        input := TM.transitionInput loopDone.input
        work := fun i => TM.transitionTape (loopDone.work i)
        output := TM.transitionTape loopDone.output }
      outputDone := by
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      hloopInputParked.read_ne_start
      (fun i => (hloopReady.control.lookup.scanner.parked i).read_ne_start)
      hloopOutputParked.read_ne_start
    simpa only [hi, hw, ho] using houtputReach
  have htailReach := TM.seqTM_reachesIn_of_reachesIn
    (denseProgramLoopTM tapes program) (denseProgramOutputTM tapes)
    hloopReach hloopHalt houtputReach'
  let tailDone := TM.phase2Wrap (denseProgramLoopTM tapes program)
    (denseProgramOutputTM tapes) outputDone
  have htailHalt :
      (TM.seqTM (denseProgramLoopTM tapes program)
        (denseProgramOutputTM tapes)).halted tailDone := by
    rw [TM.phase2Wrap_halted_iff]
    exact houtputHalt
  have hinitWorkParked : ∀ i, TM.Parked (initDone.work i) := by
    exact hready.control.lookup.scanner.parked
  have hinitOutputParked : TM.Parked initDone.output := by
    rw [hinitOutput]
    have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
      simpa [TM.resetBinaryBlank] using Tape.init_move_right_hasBinaryNat 0
    exact ⟨by rw [hblankNat.2.1],
      hblankNat.2.hasBinaryContent.cells_ne_start⟩
  have htailReach' :
      (TM.seqTM (denseProgramLoopTM tapes program)
        (denseProgramOutputTM tapes)).reachesIn
        (loopTime + 1 + outputTime)
        { state := (TM.seqTM (denseProgramLoopTM tapes program)
            (denseProgramOutputTM tapes)).qstart
          input := TM.transitionInput initDone.input
          work := fun i => TM.transitionTape (initDone.work i)
          output := TM.transitionTape initDone.output }
        tailDone := by
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      hinitInputParked.read_ne_start
      (fun i => (hinitWorkParked i).read_ne_start)
      hinitOutputParked.read_ne_start
    rw [hi, hw, ho]
    simpa only [hinitInput] using htailReach
  have hreach := TM.seqTM_reachesIn_of_reachesIn
    (denseProgramInitTM tapes)
    (TM.seqTM (denseProgramLoopTM tapes program)
      (denseProgramOutputTM tapes))
    hinitReach hinitHalt htailReach'
  let done := TM.phase2Wrap (denseProgramInitTM tapes)
    (TM.seqTM (denseProgramLoopTM tapes program)
      (denseProgramOutputTM tapes)) tailDone
  refine ⟨done, initTime + 1 + (loopTime + 1 + outputTime),
    ?_, hreach, ?_, ?_⟩
  · unfold denseProgramDecisionTime
    dsimp only [initial, final] at hloopTime houtputTime ⊢
    omega
  · change (denseProgramDecisionTM tapes program).halted done
    unfold denseProgramDecisionTM
    rw [TM.phase2Wrap_halted_iff]
    exact htailHalt
  · change outputDone.output = registerVerdictOutput
        (DenseOverlay.read input final.overlay 0)
    exact houtputVerdict

/-- The complete dense machine realizes a halted executable RAM run, with its
verdict rewritten through the overlay decoding theorem. -/
theorem denseProgramDecisionTM_hoareTime_ramRun_internal
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (fuel : ℕ)
    (hhalted : RAM.Halted program
      (RAM.run program fuel (RAM.initCfg input))) :
    (denseProgramDecisionTM tapes program).HoareTime
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _inp _work out =>
        out = registerVerdictOutput
          (RAM.run program fuel (RAM.initCfg input)).verdict)
      (denseProgramDecisionTime tapes program input fuel) := by
  let initial := DenseOverlay.Snapshot.initial input
  let final := initial.run program input fuel
  have hdecode : final.decode input =
      RAM.run program fuel (RAM.initCfg input) := by
    rw [show RAM.initCfg input = initial.decode input by
      simpa only [initial] using (DenseOverlay.Snapshot.initial_decode input).symm]
    simpa only [final] using DenseOverlay.Snapshot.decode_run
      program input fuel initial (by
        simpa only [initial] using DenseOverlay.Snapshot.initial_canonical input)
  have hfinalHalted : final.Halted program := by
    change RAM.Halted program (final.decode input)
    rw [hdecode]
    exact hhalted
  have hrun := denseProgramDecisionTM_hoareTime_run_internal tapes program
    input fuel hfinalHalted
  apply hrun.consequence
  · exact fun _ _ _ h => h
  · intro inp work out hpost
    change out = registerVerdictOutput
        (DenseOverlay.read input final.overlay 0) at hpost
    rw [hpost]
    congr 1
    change (final.decode input).regs 0 =
      (RAM.run program fuel (RAM.initCfg input)).regs 0
    rw [hdecode]
  · exact le_rfl

end Machine
end RegisterStore
end RAM
end Complexity
