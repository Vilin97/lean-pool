/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseDefs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program
public import
LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseDispatch

/-!
# Dense-overlay RAM program controller -- proof internals
-/


public section

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

private theorem phaseTransition_of_parked
    {inp out : Tape} {work : Fin n → Tape}
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    TM.transitionInput inp = inp ∧
      (fun i => TM.transitionTape (work i)) = work ∧
      TM.transitionTape out = out :=
  TM.phaseTransition_eq_self_of_reads_ne_start hinput.read_ne_start
    (fun i => (hwork i).read_ne_start) houtput.read_ne_start

/-- Final dense lookup and Boolean emission recover the decoded RAM verdict
register. -/
theorem denseProgramOutputTM_hoareTime_internal
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseProgramOutputTM tapes).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp _work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        out = registerVerdictOutput (DenseOverlay.read input overlay 0))
      (denseProgramOutputTime tapes input overlay) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let blank := (Tape.init []).move Dir3.right
  have hinput : TM.Parked inp₀ := by
    simpa only [inp₀] using denseInput_parked input
  have hlookup := denseOverlayLookupStaticTM_hoareTime_frame
    tapes.lifted.data.lhsLookup input overlay 0 initialWork blank hvalid
    hready.control.lookup blankOutput_parked
  let mid : TM.TapePred (n + 1) := fun inp work out =>
    inp = inp₀ ∧
      DenseOverlayLookupStaticResult tapes.lifted.data.lhsLookup input
        overlay 0 initialWork work ∧
      out = blank
  have hverdict : (registerVerdictTM tapes.liftedLhs).HoareTime mid
      (fun inp _work out =>
        inp = inp₀ ∧
        out = registerVerdictOutput (DenseOverlay.read input overlay 0))
      1 := by
    rintro inp work out ⟨hinp, hresult, hout⟩
    have hleaf := registerVerdictTM_hoareTime_frame_internal
      tapes.liftedLhs (DenseOverlay.read input overlay 0) inp₀ work
      hresult.destination hinput hresult.parked
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        _hfinalWork, hfinalOutput⟩ :=
      hleaf inp work out ⟨hinp, rfl, by simpa only [blank] using hout⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput, hfinalOutput⟩
  have hseq := TM.seqTM_hoareTime
    (denseOverlayLookupStaticTM tapes.lifted.data.lhsLookup 0)
    (registerVerdictTM tapes.liftedLhs) hlookup
    (by
      rintro inp work out ⟨hinp, hresult, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using hinput) hresult.parked
        (by simpa [hout, blank] using blankOutput_parked)
      rw [hi, hw, ho]
      exact ⟨hinp, hresult, by simpa only [blank] using hout⟩)
    hverdict
  simpa only [denseProgramOutputTM, denseProgramOutputTime, mid, inp₀,
    blank] using hseq

/-- Final dense lookup overwrites the loop's halt-test bit with the decoded
RAM verdict. -/
theorem denseProgramOutputTM_hoareTime_haltOutput_internal
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseProgramOutputTM tapes).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = instructionHaltOutput .halt)
      (fun inp _work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        out = registerVerdictOutput (DenseOverlay.read input overlay 0))
      (denseProgramOutputTime tapes input overlay) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let haltOut := instructionHaltOutput .halt
  have hinput : TM.Parked inp₀ := by
    simpa only [inp₀] using denseInput_parked input
  have hhaltOutParked : TM.Parked haltOut := by
    refine ⟨?_, ?_⟩
    · simp [haltOut, instructionHaltOutput, instructionHaltVerdict,
        TM.idleDir, Tape.writeAndMove, Tape.move, Tape.write, Tape.read,
        Tape.init]
    · intro j hj
      exact instructionHaltOutput_cells_ne_start .halt j hj
  have hlookup := denseOverlayLookupStaticTM_hoareTime_frame
    tapes.lifted.data.lhsLookup input overlay 0 initialWork haltOut hvalid
    hready.control.lookup hhaltOutParked
  let mid : TM.TapePred (n + 1) := fun inp work out =>
    inp = inp₀ ∧
      DenseOverlayLookupStaticResult tapes.lifted.data.lhsLookup input
        overlay 0 initialWork work ∧
      out = haltOut
  have hverdict : (registerVerdictTM tapes.liftedLhs).HoareTime mid
      (fun inp _work out =>
        inp = inp₀ ∧
        out = registerVerdictOutput (DenseOverlay.read input overlay 0))
      1 := by
    rintro inp work out ⟨hinp, hresult, hout⟩
    have hleaf := registerVerdictTM_hoareTime_haltOutput_internal
      tapes.liftedLhs (DenseOverlay.read input overlay 0) inp₀ work
      hresult.destination hinput hresult.parked
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        _hfinalWork, hfinalOutput⟩ :=
      hleaf inp work out ⟨hinp, rfl, by simpa only [haltOut] using hout⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput, hfinalOutput⟩
  have hseq := TM.seqTM_hoareTime
    (denseOverlayLookupStaticTM tapes.lifted.data.lhsLookup 0)
    (registerVerdictTM tapes.liftedLhs) hlookup
    (by
      rintro inp work out ⟨hinp, hresult, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using hinput) hresult.parked
        (by simpa [hout, haltOut] using hhaltOutParked)
      rw [hi, hw, ho]
      exact ⟨hinp, hresult, by simpa only [haltOut] using hout⟩)
    hverdict
  simpa only [denseProgramOutputTM, denseProgramOutputTime, mid, inp₀,
    haltOut] using hseq

/-- One dense loop iteration realizes one overlay step and either halts on the
successor's selected instruction or returns to the body start. -/
theorem denseProgramLoopTM_iteration_internal
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hready : InstructionExecutionReady tapes snapshot.overlay snapshot.pc
      initialWork) :
    let next := snapshot.step program input
    ∃ (nextWork : Fin (n + 1) → Tape) (time : ℕ),
      time ≤ denseProgramLoopIterationTime tapes program input snapshot ∧
      InstructionExecutionReady tapes next.overlay next.pc nextWork ∧
      ((next.Halted program ∧
          (denseProgramLoopTM tapes program).reachesIn time
            { state := (denseProgramLoopTM tapes program).qstart
              input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
              work := initialWork
              output := (Tape.init []).move Dir3.right }
            { state := Sum.inr (Sum.inl TM.LoopPhase.done)
              input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
              work := nextWork
              output := instructionHaltOutput (next.curInstr program) }) ∨
        (¬next.Halted program ∧
          (denseProgramLoopTM tapes program).reachesIn time
            { state := (denseProgramLoopTM tapes program).qstart
              input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
              work := initialWork
              output := (Tape.init []).move Dir3.right }
            { state := (denseProgramLoopTM tapes program).qstart
              input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
              work := nextWork
              output := (Tape.init []).move Dir3.right })) := by
  let next := snapshot.step program input
  let body := denseProgramStepTM tapes program
  let test := programHaltTM tapes program
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let blank := (Tape.init []).move Dir3.right
  have hinput : TM.Parked inp₀ := by
    simpa only [inp₀] using denseInput_parked input
  have hbody := denseProgramStepTM_hoareTime_frame tapes program input
    snapshot.overlay snapshot.pc initialWork hvalid hready
  obtain ⟨cbody, bodyTime, hbodyTime, hbodyReach, hbodyHalt,
      hbodyInput, hnextReadyRaw, hbodyOutput⟩ :=
    hbody inp₀ initialWork blank ⟨rfl, rfl, rfl⟩
  have hnextReady : InstructionExecutionReady tapes next.overlay next.pc
      cbody.work := by
    simpa [next, DenseOverlay.Snapshot.step,
      DenseOverlay.Snapshot.curInstr, denseInstructionStore,
      denseInstructionPC, selectedInstruction_eq_getElem?_getD] using
      hnextReadyRaw
  have hbodyInputParked : TM.Parked cbody.input := by
    simpa [hbodyInput] using hinput
  have hbodyWorkParked : ∀ i, TM.Parked (cbody.work i) :=
    hnextReady.control.lookup.scanner.parked
  have hbodyOutputParked : TM.Parked cbody.output := by
    simpa [hbodyOutput, blank] using blankOutput_parked
  have hbodyLoop := TM.loopTM_body_simulation body test hbodyReach
  have hbodyTransition :
      (⟨test.qstart, TM.transitionInput cbody.input,
        fun i => TM.transitionTape (cbody.work i),
        TM.transitionTape cbody.output⟩ : Complexity.Cfg (n + 1) test.Q) =
      ⟨test.qstart, inp₀, cbody.work, blank⟩ := by
    have hi : TM.transitionInput cbody.input = inp₀ := by
      rw [hbodyInput]
      exact hinput.transitionInput_eq_self
    have hw : (fun i => TM.transitionTape (cbody.work i)) = cbody.work :=
      funext fun i => (hbodyWorkParked i).transitionTape_eq_self
    have ho : TM.transitionTape cbody.output = blank := by
      rw [hbodyOutput]
      exact blankOutput_parked.transitionTape_eq_self
    rw [hi, hw, ho]
  have hbodyToTest := TM.loopTM_body_to_test body test hbodyHalt
  rw [hbodyTransition] at hbodyToTest
  have htest := programHaltTM_hoareTime_frame_internal tapes program
    next.overlay next.pc cbody.work inp₀ hnextReady hinput
  obtain ⟨ctest, testTime, htestTime, htestReach, htestHalt,
      htestInput, htestWork, htestOutput⟩ :=
    htest inp₀ cbody.work blank ⟨rfl, rfl, rfl⟩
  have hselected :
      selectedInstruction program next.pc = next.curInstr program :=
    selectedInstruction_eq_getElem?_getD program next.pc
  have htestOutput' :
      ctest.output = instructionHaltOutput (next.curInstr program) := by
    simpa only [hselected] using htestOutput
  have htestInputParked : TM.Parked ctest.input := by
    simpa [htestInput] using hinput
  have htestWorkParked : ∀ i, TM.Parked (ctest.work i) := by
    simpa [htestWork] using hbodyWorkParked
  have htestOutputParked : TM.Parked ctest.output := by
    refine ⟨?_, ?_⟩
    · rw [htestOutput', instructionHaltOutput_head]
    · rw [htestOutput']
      exact instructionHaltOutput_cells_ne_start _
  have htestTransition :
      (⟨(Sum.inr (Sum.inl TM.LoopPhase.rewindOut) :
          TM.LoopQ body.Q test.Q),
        TM.transitionInput ctest.input,
        fun i => TM.transitionTape (ctest.work i),
        TM.transitionTape ctest.output⟩ :
          Complexity.Cfg (n + 1) (TM.LoopQ body.Q test.Q)) =
      ⟨Sum.inr (Sum.inl TM.LoopPhase.rewindOut), inp₀,
        cbody.work, ctest.output⟩ := by
    have hi : TM.transitionInput ctest.input = inp₀ := by
      rw [htestInput]
      exact hinput.transitionInput_eq_self
    have hw : (fun i => TM.transitionTape (ctest.work i)) = cbody.work := by
      funext i
      rw [htestWork]
      exact (hbodyWorkParked i).transitionTape_eq_self
    have ho : TM.transitionTape ctest.output = ctest.output :=
      htestOutputParked.transitionTape_eq_self
    rw [hi, hw, ho]
  have htestToRewind :=
    (TM.loopTM_test_to_rewind body test htestHalt).trans
      (congrArg some htestTransition)
  obtain ⟨ctail, htailReach, htailState, htailInput, htailWork,
      htailOutput⟩ := programLoop_rewind_check_internal body test
      ⟨Sum.inr (Sum.inl TM.LoopPhase.rewindOut), inp₀,
        cbody.work, ctest.output⟩ rfl hinput.read_ne_start
      (fun i => (hbodyWorkParked i).read_ne_start)
      (by rw [htestOutput', instructionHaltOutput_head])
      (by rw [htestOutput', instructionHaltOutput_cells_zero])
      (by rw [htestOutput']; exact instructionHaltOutput_cells_ne_start _)
  have hreach := TM.reachesIn_trans _
    (TM.reachesIn_trans _
      (TM.reachesIn_trans _
        (TM.reachesIn_trans _ hbodyLoop (.step hbodyToTest .zero))
        (TM.loopTM_test_simulation body test htestReach))
      (.step htestToRewind .zero)) htailReach
  have htime : bodyTime + 1 + testTime + 1 + 3 ≤
      denseProgramLoopIterationTime tapes program input snapshot := by
    dsimp only [next] at htestTime
    simp only [denseProgramLoopIterationTime]
    omega
  refine ⟨cbody.work, bodyTime + 1 + testTime + 1 + 3, htime,
    hnextReady, ?_⟩
  by_cases hhalted : next.Halted program
  · left
    refine ⟨hhalted, ?_⟩
    have hone : ctest.output.cells 1 = Γ.one := by
      rw [htestOutput']
      exact instructionHaltOutput_cell_one_eq_one_iff _ |>.2 hhalted
    have htailDone : ctail.state =
        Sum.inr (Sum.inl TM.LoopPhase.done) := by
      simpa [hone] using htailState
    have hcTail : ctail =
        { state := Sum.inr (Sum.inl TM.LoopPhase.done)
          input := inp₀
          work := cbody.work
          output := instructionHaltOutput (next.curInstr program) } := by
      cases ctail
      simp only [Complexity.Cfg.mk.injEq]
      exact ⟨htailDone, htailInput, htailWork,
        htailOutput.trans htestOutput'⟩
    simpa only [denseProgramLoopTM, body, test, inp₀, blank, hcTail] using
      hreach
  · right
    refine ⟨hhalted, ?_⟩
    have hcur : next.curInstr program ≠ .halt := hhalted
    have hblankOutput : ctest.output = blank := by
      rw [htestOutput']
      simpa only [blank] using
        instructionHaltOutput_eq_blank_of_ne_halt hcur
    have hone : ctest.output.cells 1 ≠ Γ.one := by
      rw [htestOutput']
      exact fun h => hhalted
        (instructionHaltOutput_cell_one_eq_one_iff _ |>.1 h)
    have htailStart : ctail.state = Sum.inl body.qstart := by
      simpa [hone] using htailState
    have hcTail : ctail =
        { state := Sum.inl body.qstart
          input := inp₀
          work := cbody.work
          output := blank } := by
      cases ctail
      simp only [Complexity.Cfg.mk.injEq]
      exact ⟨htailStart, htailInput, htailWork,
        htailOutput.trans hblankOutput⟩
    simpa only [denseProgramLoopTM, body, test, inp₀, blank, hcTail] using
      hreach

/-- A halted dense snapshot is stationary under one selected step. -/
theorem denseSnapshot_step_eq_self_of_halted_internal
    (program : Program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot)
    (hhalted : snapshot.Halted program) :
    snapshot.step program input = snapshot := by
  change snapshot.curInstr program = .halt at hhalted
  rw [DenseOverlay.Snapshot.step, hhalted]
  rfl

/-- Running a halted dense snapshot for arbitrary additional fuel is a no-op. -/
theorem denseSnapshot_run_halted_internal
    (program : Program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot)
    (hhalted : snapshot.Halted program) :
    ∀ fuel, snapshot.run program input fuel = snapshot
  | 0 => rfl
  | fuel + 1 => by
      rw [DenseOverlay.Snapshot.run, if_pos hhalted]

/-- A halted fuel-bounded dense run is realized by the fixed controller loop.
The extra iteration handles a snapshot already halted at fuel zero. -/
theorem denseProgramLoopTM_hoareTime_run_internal
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) :
    ∀ (fuel : ℕ) (snapshot : DenseOverlay.Snapshot)
      (initialWork : Fin (n + 1) → Tape),
      DenseOverlay.Valid snapshot.overlay →
      InstructionExecutionReady tapes snapshot.overlay snapshot.pc
        initialWork →
      (snapshot.run program input fuel).Halted program →
      (denseProgramLoopTM tapes program).HoareTime
        (fun inp work out =>
          inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
          work = initialWork ∧ out = (Tape.init []).move Dir3.right)
        (fun inp work out =>
          let final := snapshot.run program input fuel
          inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
          InstructionExecutionReady tapes final.overlay final.pc work ∧
          out = instructionHaltOutput (final.curInstr program))
        (denseProgramLoopTime tapes program input (fuel + 1)
          snapshot) := by
  intro fuel
  induction fuel with
  | zero =>
      intro snapshot initialWork hvalid hready hhalted
      rintro inp work out ⟨hinp, hwork, hout⟩
      subst inp
      subst work
      subst out
      have hsnapshotHalted : snapshot.Halted program := by
        simpa [DenseOverlay.Snapshot.run] using hhalted
      have hstepSelf := denseSnapshot_step_eq_self_of_halted_internal
        program input snapshot hsnapshotHalted
      obtain ⟨nextWork, time, htime, hnextReady, hbranch⟩ :=
        denseProgramLoopTM_iteration_internal tapes program input snapshot
          initialWork hvalid hready
      rcases hbranch with ⟨hnextHalted, hreach⟩ |
          ⟨hnextRunning, _⟩
      · have hready' : InstructionExecutionReady tapes snapshot.overlay
            snapshot.pc nextWork := by
          simpa only [hstepSelf] using hnextReady
        have hreach' : (denseProgramLoopTM tapes program).reachesIn time
            { state := (denseProgramLoopTM tapes program).qstart
              input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
              work := initialWork
              output := (Tape.init []).move Dir3.right }
            { state := Sum.inr (Sum.inl TM.LoopPhase.done)
              input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
              work := nextWork
              output := instructionHaltOutput
                (snapshot.curInstr program) } := by
          simpa only [hstepSelf] using hreach
        refine ⟨_, time, ?_, hreach', rfl, rfl, ?_, ?_⟩
        · simpa [denseProgramLoopTime] using htime
        · simpa [DenseOverlay.Snapshot.run] using hready'
        · simp [DenseOverlay.Snapshot.run]
      · exact (hnextRunning (by simpa only [hstepSelf] using
          hsnapshotHalted)).elim
  | succ fuel ih =>
      intro snapshot initialWork hvalid hready hhalted
      by_cases hsnapshotHalted : snapshot.Halted program
      · rintro inp work out ⟨hinp, hwork, hout⟩
        subst inp
        subst work
        subst out
        have hstepSelf := denseSnapshot_step_eq_self_of_halted_internal
          program input snapshot hsnapshotHalted
        obtain ⟨nextWork, time, htime, hnextReady, hbranch⟩ :=
          denseProgramLoopTM_iteration_internal tapes program input snapshot
            initialWork hvalid hready
        rcases hbranch with ⟨_, hreach⟩ | ⟨hnextRunning, _⟩
        · have hfinal : snapshot.run program input (fuel + 1) = snapshot :=
            denseSnapshot_run_halted_internal program input snapshot
              hsnapshotHalted _
          have hready' : InstructionExecutionReady tapes snapshot.overlay
              snapshot.pc nextWork := by
            simpa only [hstepSelf] using hnextReady
          have hreach' : (denseProgramLoopTM tapes program).reachesIn time
              { state := (denseProgramLoopTM tapes program).qstart
                input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
                work := initialWork
                output := (Tape.init []).move Dir3.right }
              { state := Sum.inr (Sum.inl TM.LoopPhase.done)
                input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
                work := nextWork
                output := instructionHaltOutput
                  (snapshot.curInstr program) } := by
            simpa only [hstepSelf] using hreach
          refine ⟨_, time, ?_, hreach', rfl, rfl, ?_, ?_⟩
          · simp only [denseProgramLoopTime]
            omega
          · simpa only [hfinal] using hready'
          · simp only [hfinal]
        · exact (hnextRunning (by simpa only [hstepSelf] using
            hsnapshotHalted)).elim
      · have hrunHalted :
            ((snapshot.step program input).run program input fuel).Halted
              program := by
          simpa [DenseOverlay.Snapshot.run, hsnapshotHalted] using hhalted
        have hiter := denseProgramLoopTM_iteration_internal tapes program
          input snapshot initialWork hvalid hready
        obtain ⟨nextWork, time₁, htime₁, hnextReady, hbranch⟩ := hiter
        rcases hbranch with ⟨hnextHalted, hreach₁⟩ |
            ⟨hnextRunning, hreach₁⟩
        · rintro inp work out ⟨hinp, hwork, hout⟩
          subst inp
          subst work
          subst out
          have hfinal :
              (snapshot.step program input).run program input fuel =
                snapshot.step program input :=
            denseSnapshot_run_halted_internal program input
              (snapshot.step program input) hnextHalted fuel
          refine ⟨_, time₁, ?_, hreach₁, rfl, rfl, ?_, ?_⟩
          · simp only [denseProgramLoopTime]
            omega
          · simpa [DenseOverlay.Snapshot.run, hsnapshotHalted, hfinal]
              using hnextReady
          · simp [DenseOverlay.Snapshot.run, hsnapshotHalted, hfinal]
        · have hnextValid := DenseOverlay.Snapshot.step_valid program input
            snapshot hvalid
          have hrecursive := ih (snapshot.step program input) nextWork
            hnextValid hnextReady hrunHalted
          rintro inp work out ⟨hinp, hwork, hout⟩
          subst inp
          subst work
          subst out
          obtain ⟨cfinal, time₂, htime₂, hreach₂, hhalt₂,
              hfinalInput, hfinalReady, hfinalOutput⟩ :=
            hrecursive
              ((Tape.init (input.map Γ.ofBool)).move Dir3.right)
              nextWork ((Tape.init []).move Dir3.right) ⟨rfl, rfl, rfl⟩
          refine ⟨cfinal, time₁ + time₂, ?_,
            TM.reachesIn_trans _ hreach₁ hreach₂, hhalt₂,
            hfinalInput, ?_, ?_⟩
          · change time₁ + time₂ ≤
              denseProgramLoopIterationTime tapes program input snapshot +
                denseProgramLoopTime tapes program input (fuel + 1)
                  (snapshot.step program input)
            exact Nat.add_le_add htime₁ htime₂
          · simpa [DenseOverlay.Snapshot.run, hsnapshotHalted] using
              hfinalReady
          · simpa [DenseOverlay.Snapshot.run, hsnapshotHalted] using
              hfinalOutput

end Machine
end RegisterStore
end RAM
end Complexity
