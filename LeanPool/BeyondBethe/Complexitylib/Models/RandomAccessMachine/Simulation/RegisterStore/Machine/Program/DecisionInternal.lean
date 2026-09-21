/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Decision.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Init.Internal
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Internal

/-!
# Complete sparse RAM decision-machine proof internals
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

/-- The complete concrete machine realizes one halted pure sparse RAM run and
emits its `R₀` verdict. -/
theorem programDecisionTM_hoareTime_run_internal
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (fuel : ℕ)
    (hhalted : ((programInitialSnapshot input).run program fuel).Halted program) :
    (programDecisionTM tapes program).HoareTime
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _inp _work out =>
        let final := (programInitialSnapshot input).run program fuel
        out = registerVerdictOutput (RegisterStore.read final.store 0))
      (programDecisionTime tapes program input fuel) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  let initial := programInitialSnapshot input
  let final := initial.run program fuel
  have hinit := programInitTM_hoareTime_internal tapes input
  obtain ⟨initDone, initTime, hinitTime, hinitReach, hinitHalt,
      hinitInput, hinitWork, hinitOutput⟩ :=
    hinit _ _ _ ⟨rfl, rfl, rfl⟩
  have hinitialCanonical : Canonical initial.store := by
    simpa only [initial, programInitialSnapshot] using
      programInitialStore_canonical_internal input
  have hready : InstructionExecutionReady tapes initial.store initial.pc
      initDone.work := by
    rw [hinitWork]
    exact programSnapshotWork_ready_internal tapes initial hinitialCanonical
  have hinitInputParked : TM.Parked initDone.input :=
    ⟨hinitInput.1, hinitInput.2.2.2⟩
  have hloop := programLoopTM_hoareTime_run_internal tapes program fuel initial
    initDone.work initDone.input hready hinitInputParked hhalted
  obtain ⟨loopDone, loopTime, hloopTime, hloopReach, hloopHalt,
      hloopInput, hloopReady, hloopOutput⟩ :=
    hloop _ _ _ ⟨rfl, rfl, by simpa [TM.resetBinaryBlank] using hinitOutput⟩
  have hloopInputParked : TM.Parked loopDone.input := by
    rw [hloopInput]
    exact hinitInputParked
  have hloopOutputHalt : loopDone.output = instructionHaltOutput .halt := by
    change loopDone.output = instructionHaltOutput (final.curInstr program) at hloopOutput
    rw [show final.curInstr program = .halt from hhalted] at hloopOutput
    exact hloopOutput
  have houtputRun := programOutputTM_hoareTime_haltOutput_internal tapes
    final.store final.pc loopDone.work loopDone.input hloopReady
    hloopInputParked
  obtain ⟨outputDone, outputTime, houtputTime, houtputReach,
      houtputHalt, houtputInput, houtputVerdict⟩ :=
    houtputRun _ _ _ ⟨rfl, rfl, hloopOutputHalt⟩
  have hloopOutputParked : TM.Parked loopDone.output := by
    rw [hloopOutputHalt]
    refine ⟨?_, instructionHaltOutput_cells_ne_start_internal .halt⟩
    rw [instructionHaltOutput_head_internal]
  have houtputReach' : (programOutputTM tapes).reachesIn outputTime
      { state := (programOutputTM tapes).qstart
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
    (programLoopTM tapes program) (programOutputTM tapes)
    hloopReach hloopHalt houtputReach'
  let tailDone := TM.phase2Wrap (programLoopTM tapes program)
    (programOutputTM tapes) outputDone
  have htailHalt :
      (TM.seqTM (programLoopTM tapes program)
        (programOutputTM tapes)).halted tailDone := by
    rw [TM.phase2Wrap_halted_iff]
    exact houtputHalt
  have hinitWorkParked : ∀ i, TM.Parked (initDone.work i) := by
    rw [hinitWork]
    exact (programSnapshotWork_ready_internal tapes initial
      hinitialCanonical).control.lookup.scanner.parked
  have hinitOutputParked : TM.Parked initDone.output := by
    rw [hinitOutput]
    have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
      simpa [TM.resetBinaryBlank] using Tape.init_move_right_hasBinaryNat 0
    exact ⟨by rw [hblankNat.2.1],
      hblankNat.2.hasBinaryContent.cells_ne_start⟩
  have htailReach' :
      (TM.seqTM (programLoopTM tapes program)
        (programOutputTM tapes)).reachesIn
        (loopTime + 1 + outputTime)
        { state := (TM.seqTM (programLoopTM tapes program)
            (programOutputTM tapes)).qstart
          input := TM.transitionInput initDone.input
          work := fun i => TM.transitionTape (initDone.work i)
          output := TM.transitionTape initDone.output }
        tailDone := by
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      hinitInputParked.read_ne_start
      (fun i => (hinitWorkParked i).read_ne_start)
      hinitOutputParked.read_ne_start
    simpa only [hi, hw, ho] using htailReach
  have hreach := TM.seqTM_reachesIn_of_reachesIn
    (programInitTM tapes)
    (TM.seqTM (programLoopTM tapes program) (programOutputTM tapes))
    hinitReach hinitHalt htailReach'
  let done := TM.phase2Wrap (programInitTM tapes)
    (TM.seqTM (programLoopTM tapes program) (programOutputTM tapes)) tailDone
  refine ⟨done, initTime + 1 + (loopTime + 1 + outputTime),
    ?_, hreach, ?_, ?_⟩
  · unfold programDecisionTime
    dsimp only [initial, final] at hloopTime houtputTime ⊢
    omega
  · change (programDecisionTM tapes program).halted done
    unfold programDecisionTM
    rw [TM.phase2Wrap_halted_iff]
    exact htailHalt
  · change outputDone.output = registerVerdictOutput
        (RegisterStore.read final.store 0)
    exact houtputVerdict

/-- The complete machine realizes a halted executable RAM run, with the public
RAM verdict rewritten through the sparse representation theorem. -/
theorem programDecisionTM_hoareTime_ramRun_internal
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (fuel : ℕ)
    (hhalted : RAM.Halted program
      (RAM.run program fuel (RAM.initCfg input))) :
    (programDecisionTM tapes program).HoareTime
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _inp _work out =>
        out = registerVerdictOutput
          (RAM.run program fuel (RAM.initCfg input)).verdict)
      (programDecisionTime tapes program input fuel) := by
  let initial := programInitialSnapshot input
  let final := initial.run program fuel
  have hinitialRep : initial.Represents (RAM.initCfg input) := by
    simpa only [initial] using programInitialSnapshot_represents_internal input
  have hdecode : final.decode = RAM.run program fuel (RAM.initCfg input) := by
    have hrun := Snapshot.decode_run_internal program fuel initial hinitialRep.1
    rw [hinitialRep.2] at hrun
    exact hrun
  have hfinalHalted : final.Halted program := by
    apply (Snapshot.halted_decode_iff_internal program final).mp
    rw [hdecode]
    exact hhalted
  have hrun := programDecisionTM_hoareTime_run_internal tapes program input
    fuel hfinalHalted
  apply hrun.consequence
  · exact fun _ _ _ h => h
  · intro inp work out hpost
    change out = registerVerdictOutput (RegisterStore.read final.store 0)
      at hpost
    rw [hpost]
    congr 1
    change final.decode.regs 0 =
      (RAM.run program fuel (RAM.initCfg input)).regs 0
    rw [hdecode]
  · exact le_rfl

end Machine

end RegisterStore

end RAM

end Complexity
