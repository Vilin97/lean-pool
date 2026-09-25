/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseInitDefs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Init.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Internal

/-!
# Dense-overlay public-input initialization -- proofs
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

variable {n : ℕ}

private theorem parked_of_binaryNat {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t :=
  ⟨by rw [h.2.1], h.2.hasBinaryContent.cells_ne_start⟩

private theorem parked_of_binarySuffix {t : Tape} {bits : List Bool}
    (h : t.HasBinarySuffix bits) : TM.Parked t :=
  ⟨h.1, h.2.2.2⟩

private def denseInitialLengthWrap (tapes : ControlInstructionTapes n)
    (c : Complexity.Cfg (n + 1) (initialZeroBitTM tapes).Q) :
    Complexity.Cfg (n + 1) (denseInitialLengthLoopTM tapes).Q :=
  { state := .inr c.state
    input := c.input
    work := c.work
    output := c.output }

private theorem denseInitialLengthLoopTM_body_step
    (tapes : ControlInstructionTapes n)
    {c c' : Complexity.Cfg (n + 1) (initialZeroBitTM tapes).Q}
    (hstep : (initialZeroBitTM tapes).step c = some c') :
    (denseInitialLengthLoopTM tapes).step (denseInitialLengthWrap tapes c) =
      some (denseInitialLengthWrap tapes c') := by
  have hne : c.state ≠ (initialZeroBitTM tapes).qhalt :=
    TM.state_ne_qhalt_of_step hstep
  rw [TM.step,
    ite_eq_right (by simp [denseInitialLengthWrap, denseInitialLengthLoopTM])]
  simp only [denseInitialLengthWrap, denseInitialLengthLoopTM, hne,
    ↓reduceIte]
  rw [TM.step, ite_eq_right hne] at hstep
  revert hstep
  generalize (initialZeroBitTM tapes).δ c.state c.input.read
    (fun i => (c.work i).read) c.output.read = action
  obtain ⟨state, workWrites, outputWrite, inputDir, workDirs, outputDir⟩ :=
    action
  intro hstep
  cases Option.some.inj hstep
  rfl

private theorem denseInitialLengthLoopTM_body_reachesIn
    (tapes : ControlInstructionTapes n)
    {time : ℕ} {c c' : Complexity.Cfg (n + 1) (initialZeroBitTM tapes).Q}
    (hreach : (initialZeroBitTM tapes).reachesIn time c c') :
    (denseInitialLengthLoopTM tapes).reachesIn time
      (denseInitialLengthWrap tapes c) (denseInitialLengthWrap tapes c') :=
  TM.reachesIn_map (denseInitialLengthWrap tapes)
    (fun _ _ => denseInitialLengthLoopTM_body_step tapes) hreach

private theorem denseInitialLengthLoopTM_step_scan_data
    (tapes : ControlInstructionTapes n)
    (c : Complexity.Cfg (n + 1) (denseInitialLengthLoopTM tapes).Q)
    (hstate : c.state = .inl .scan) (hblank : c.input.read ≠ Γ.blank)
    (hstart : c.input.read ≠ Γ.start)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (denseInitialLengthLoopTM tapes).step c = some
      { state := .inr (initialZeroBitTM tapes).qstart
        input := c.input
        work := c.work
        output := c.output } := by
  rw [TM.step,
    ite_eq_right (by rw [hstate]; simp [denseInitialLengthLoopTM])]
  simp only [denseInitialLengthLoopTM, hstate, hblank, TM.allReadBack,
    ↓reduceIte]
  refine congrArg some ((Complexity.Cfg.mk.injEq ..).mpr
    ⟨rfl, ?_, ?_, ?_⟩)
  · simp [TM.idleDir, hstart, Tape.move]
  · funext i
    rw [TM.writeAndMove_readBack _ (hwork i), TM.idleDir,
      ite_eq_right (hwork i)]
    rfl
  · rw [TM.writeAndMove_readBack _ houtput, TM.idleDir, ite_eq_right houtput]
    rfl

private theorem denseInitialLengthLoopTM_step_scan_blank
    (tapes : ControlInstructionTapes n)
    (c : Complexity.Cfg (n + 1) (denseInitialLengthLoopTM tapes).Q)
    (hstate : c.state = .inl .scan) (hblank : c.input.read = Γ.blank)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (denseInitialLengthLoopTM tapes).step c = some
      { state := .inl .done
        input := c.input
        work := c.work
        output := c.output } := by
  rw [TM.step,
    ite_eq_right (by rw [hstate]; simp [denseInitialLengthLoopTM])]
  simp only [denseInitialLengthLoopTM, hstate, hblank, TM.allReadBack,
    ↓reduceIte]
  refine congrArg some ((Complexity.Cfg.mk.injEq ..).mpr
    ⟨rfl, ?_, ?_, ?_⟩)
  · simp [TM.idleDir, Tape.move]
  · funext i
    rw [TM.writeAndMove_readBack _ (hwork i), TM.idleDir,
      ite_eq_right (hwork i)]
    rfl
  · rw [TM.writeAndMove_readBack _ houtput, TM.idleDir, ite_eq_right houtput]
    rfl

private theorem denseInitialLengthLoopTM_step_body_halt
    (tapes : ControlInstructionTapes n)
    (c : Complexity.Cfg (n + 1) (initialZeroBitTM tapes).Q)
    (hhalt : (initialZeroBitTM tapes).halted c)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (denseInitialLengthLoopTM tapes).step
      (denseInitialLengthWrap tapes c) = some
      { state := .inl .scan
        input := c.input.move Dir3.right
        work := c.work
        output := c.output } := by
  rw [TM.step,
    ite_eq_right (by simp [denseInitialLengthWrap, denseInitialLengthLoopTM])]
  simp only [denseInitialLengthWrap, denseInitialLengthLoopTM, hhalt,
    ↓reduceIte]
  refine congrArg some ((Complexity.Cfg.mk.injEq ..).mpr
    ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    rw [TM.writeAndMove_readBack _ (hwork i), TM.idleDir,
      ite_eq_right (hwork i)]
    rfl
  · rw [TM.writeAndMove_readBack _ houtput, TM.idleDir, ite_eq_right houtput]
    rfl

theorem denseInitialLengthLoopTM_hoareTime_internal
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (address count : ℕ) (entries : Store)
    (inp₀ : Tape) (work₀ : Fin (n + 1) → Tape) (out₀ : Tape)
    (hinput : inp₀.HasBinarySuffix input)
    (hready : InitialLoopReady tapes address count entries work₀)
    (houtput : out₀ = TM.resetBinaryBlank) :
    (denseInitialLengthLoopTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp.HasBinarySuffix [] ∧
        inp.head = inp₀.head + input.length ∧
        InitialLoopReady tapes (address + input.length) count entries work ∧
        out = out₀)
      (denseInitialLengthLoopTime address input) := by
  induction input generalizing address inp₀ work₀ out₀ with
  | nil =>
      intro inp work out hpre
      rcases hpre with ⟨hinp, hwork, hout⟩
      subst inp
      subst work
      subst out
      let done : Complexity.Cfg (n + 1) (denseInitialLengthLoopTM tapes).Q :=
        { state := .inl .done
          input := inp₀
          work := work₀
          output := out₀ }
      have hstep := denseInitialLengthLoopTM_step_scan_blank tapes
        ({ state := (denseInitialLengthLoopTM tapes).qstart
           input := inp₀
           work := work₀
           output := out₀ } :
          Complexity.Cfg (n + 1) (denseInitialLengthLoopTM tapes).Q)
        rfl hinput.read_nil
        (fun i => (hready.parked i).read_ne_start)
        (by
          rw [houtput]
          have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
            simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
          exact (parked_of_binaryNat hblankNat).read_ne_start)
      refine ⟨done, 1, by simp [denseInitialLengthLoopTime],
        .step (by simpa [done] using! hstep) .zero, ?_, ?_⟩
      · rfl
      · exact ⟨hinput, rfl, by simpa, rfl⟩
  | cons bit rest ih =>
      intro inp work out hpre
      rcases hpre with ⟨hinp, hwork, hout⟩
      subst inp
      subst work
      subst out
      let scan : Complexity.Cfg (n + 1) (denseInitialLengthLoopTM tapes).Q :=
        { state := (denseInitialLengthLoopTM tapes).qstart
          input := inp₀
          work := work₀
          output := out₀ }
      let bodyStart : Complexity.Cfg (n + 1) (initialZeroBitTM tapes).Q :=
        { state := (initialZeroBitTM tapes).qstart
          input := inp₀
          work := work₀
          output := out₀ }
      have hinputParked : TM.Parked inp₀ := parked_of_binarySuffix hinput
      have houtputParked : TM.Parked out₀ := by
        rw [houtput]
        have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
          simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
        exact parked_of_binaryNat hblankNat
      have hreadNonblank : inp₀.read ≠ Γ.blank := by
        rw [hinput.read_cons]
        exact Γ.ofBool_ne_blank bit
      have hreadNonstart : inp₀.read ≠ Γ.start := by
        rw [hinput.read_cons]
        exact Γ.ofBool_ne_start bit
      have hscanStep := denseInitialLengthLoopTM_step_scan_data tapes scan
        rfl hreadNonblank hreadNonstart
        (fun i => (hready.parked i).read_ne_start)
        houtputParked.read_ne_start
      have hscanReach : (denseInitialLengthLoopTM tapes).reachesIn 1 scan
          (denseInitialLengthWrap tapes bodyStart) :=
        .step (by simpa [scan, bodyStart, denseInitialLengthWrap] using!
          hscanStep) .zero
      have hbody := initialZeroBitTM_hoareTime_internal tapes address count
        entries inp₀ work₀ out₀ hready hinputParked houtputParked
      obtain ⟨bodyDone, bodyTime, hbodyTime, hbodyReach, hbodyHalt,
          hbodyInput, hbodyReady, hbodyOutput⟩ :=
        hbody inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩
      have hbodyLift :=
        denseInitialLengthLoopTM_body_reachesIn tapes hbodyReach
      let nextScan :
          Complexity.Cfg (n + 1) (denseInitialLengthLoopTM tapes).Q :=
        { state := .inl .scan
          input := bodyDone.input.move Dir3.right
          work := bodyDone.work
          output := bodyDone.output }
      have hseamStep := denseInitialLengthLoopTM_step_body_halt tapes bodyDone
        hbodyHalt (fun i => (hbodyReady.parked i).read_ne_start)
        (by rw [hbodyOutput]; exact houtputParked.read_ne_start)
      have hseamReach : (denseInitialLengthLoopTM tapes).reachesIn 1
          (denseInitialLengthWrap tapes bodyDone) nextScan :=
        .step (by simpa [nextScan] using! hseamStep) .zero
      have hnextInput :
          (bodyDone.input.move Dir3.right).HasBinarySuffix rest := by
        rw [hbodyInput]
        exact hinput.move_right_cons
      have hnextOutput : bodyDone.output = TM.resetBinaryBlank :=
        hbodyOutput.trans houtput
      have htail := ih (address + 1) (bodyDone.input.move Dir3.right)
        bodyDone.work bodyDone.output hnextInput hbodyReady hnextOutput
      obtain ⟨tailDone, tailTime, htailTime, htailReach, htailHalt,
          htailInput, htailHead, htailReady, htailOutput⟩ :=
        htail _ _ _ ⟨rfl, rfl, rfl⟩
      have hreach := TM.reachesIn_trans (denseInitialLengthLoopTM tapes)
        hscanReach (TM.reachesIn_trans (denseInitialLengthLoopTM tapes)
          hbodyLift (TM.reachesIn_trans (denseInitialLengthLoopTM tapes)
            hseamReach htailReach))
      refine ⟨tailDone, 1 + bodyTime + 1 + tailTime, ?_, ?_,
        htailHalt, ?_⟩
      · simp only [denseInitialLengthLoopTime]
        omega
      · simpa [Nat.add_assoc] using! hreach
      · refine ⟨htailInput, ?_, ?_, htailOutput.trans hbodyOutput⟩
        · rw [htailHead, hbodyInput]
          simp only [Tape.move, List.length_cons]
          omega
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! htailReady

private theorem denseProgramInitialStore_eq (input : List Bool) :
    denseProgramInitialStore input = [(0, input.length + 1)] := by
  simp [denseProgramInitialStore, DenseOverlay.Snapshot.initial,
    DenseOverlay.write, RegisterStore.write]

/-- Complete dense public-input initialization reaches the exact one-entry
snapshot image and rewinds the immutable input bank to cell one. -/
theorem denseProgramInitTM_hoareTime_internal
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    (denseProgramInitTM tapes).HoareTime
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = denseProgramSnapshotWork tapes
          (DenseOverlay.Snapshot.initial input) ∧
        out = TM.resetBinaryBlank)
      (denseProgramInitTime tapes input) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  have hsetup := initialSetupTM_hoareTime_internal tapes input
  obtain ⟨setupDone, setupTime, hsetupTime, hsetupReach, hsetupHalt,
      hsetupInput, hsetupInputEq, hsetupReady, hsetupOutput⟩ :=
    hsetup _ _ _ ⟨rfl, rfl, rfl⟩
  have hsetupBufferStart :
      (setupDone.work tapes.buffer).cells 0 = Γ.start := by
    apply TM.work_cells_zero_eq_start_of_reachesIn tapes.buffer hsetupReach
    simp [Tape.init]
  have hsetupInputParked : TM.Parked setupDone.input :=
    parked_of_binarySuffix hsetupInput
  have hsetupOutputParked : TM.Parked setupDone.output := by
    rw [hsetupOutput]
    have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
      simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
    exact parked_of_binaryNat hblankNat
  have hloop := denseInitialLengthLoopTM_hoareTime_internal tapes input
    1 0 [] setupDone.input setupDone.work setupDone.output hsetupInput
    hsetupReady hsetupOutput
  obtain ⟨loopDone, loopTime, hloopTime, hloopReach, hloopHalt,
      hloopInput, hloopHead, hloopReadyRaw, hloopOutput⟩ :=
    hloop _ _ _ ⟨rfl, rfl, rfl⟩
  have hloopReady : InitialLoopReady tapes (input.length + 1) 0 []
      loopDone.work := by
    simpa [Nat.add_comm] using! hloopReadyRaw
  have hloopBufferStart :
      (loopDone.work tapes.buffer).cells 0 = Γ.start :=
    TM.work_cells_zero_eq_start_of_reachesIn tapes.buffer hloopReach
      hsetupBufferStart
  have hloopInputParked : TM.Parked loopDone.input :=
    parked_of_binarySuffix hloopInput
  have hloopOutputBlank : loopDone.output = TM.resetBinaryBlank :=
    hloopOutput.trans hsetupOutput
  have hloopOutputParked : TM.Parked loopDone.output := by
    rw [hloopOutputBlank]
    have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
      simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
    exact parked_of_binaryNat hblankNat
  have hemit := initialLengthEmitTM_hoareTime_internal tapes
    (input.length + 1) 0 [] loopDone.input loopDone.work loopDone.output
    hloopReady hloopInputParked hloopOutputBlank
  obtain ⟨emitDone, emitTime, hemitTime, hemitReach, hemitHalt,
      hemitInput, hemitReadyRaw, hemitOutput⟩ :=
    hemit _ _ _ ⟨rfl, rfl, rfl⟩
  have hemitBufferStart :
      (emitDone.work tapes.buffer).cells 0 = Γ.start :=
    TM.work_cells_zero_eq_start_of_reachesIn tapes.buffer hemitReach
      hloopBufferStart
  have hemitReady : InitialLoopReady tapes (input.length + 1)
      (denseProgramInitialStore input).length
      (denseProgramInitialStore input) emitDone.work := by
    rw [denseProgramInitialStore_eq]
    simpa using! hemitReadyRaw
  have hemitInputParked : TM.Parked emitDone.input := by
    rw [hemitInput]
    exact hloopInputParked
  have hemitOutputBlank : emitDone.output = TM.resetBinaryBlank :=
    hemitOutput.trans hloopOutputBlank
  have hemitOutputParked : TM.Parked emitDone.output := by
    rw [hemitOutputBlank]
    have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
      simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
    exact parked_of_binaryNat hblankNat
  have habi := initialAbiInstallTM_hoareTime_internal tapes
    (denseProgramInitialStore input) (input.length + 1) emitDone.input
    emitDone.work emitDone.output hemitReady hemitBufferStart
    hemitInputParked hemitOutputBlank
  obtain ⟨abiDone, abiTime, habiTime, habiReach, habiHalt,
      habiInput, habiWork, habiOutput⟩ :=
    habi _ _ _ ⟨rfl, rfl, rfl⟩
  have habiInputCells : abiDone.input.cells =
      (Tape.init (input.map Γ.ofBool)).cells := by
    rw [habiInput, hemitInput,
      TM.input_cells_eq_of_reachesIn hloopReach, hsetupInputEq]
    rfl
  have habiInputHead : abiDone.input.head = input.length + 1 := by
    rw [habiInput, hemitInput, hloopHead, hsetupInputEq]
    simp [Tape.move]
    omega
  let sparseInitial : Snapshot :=
    { pc := 0, store := denseProgramInitialStore input }
  have hsparseCanonical : Canonical sparseInitial.store := by
    simpa [sparseInitial, denseProgramInitialStore] using!
      DenseOverlay.Snapshot.initial_canonical input
  have habiReady : InstructionExecutionReady tapes sparseInitial.store 0
      (programSnapshotWork tapes sparseInitial) :=
    programSnapshotWork_ready_internal tapes sparseInitial hsparseCanonical
  have hrewind := TM.rewindInputTM_hoareTime_frame
    (n := n + 1) (input.length + 1)
    (P := fun inp work out =>
      inp.cells = (Tape.init (input.map Γ.ofBool)).cells ∧
      work = denseProgramSnapshotWork tapes
        (DenseOverlay.Snapshot.initial input) ∧
      out = TM.resetBinaryBlank)
    (by
      intro inp work out inp' work' out' hP hcells _hhead hwork' hout'
      exact ⟨hcells.trans hP.1,
        hwork'.trans hP.2.1, hout'.trans hP.2.2⟩)
  have hrewindPre :
      abiDone.input.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → abiDone.input.cells j ≠ Γ.start) ∧
      abiDone.input.head ≤ input.length + 1 ∧
      abiDone.output.read ≠ Γ.start ∧ abiDone.output.head ≥ 1 ∧
      (∀ i, (abiDone.work i).read ≠ Γ.start ∧
        (abiDone.work i).head ≥ 1) ∧
      (abiDone.input.cells = (Tape.init (input.map Γ.ofBool)).cells ∧
        abiDone.work = denseProgramSnapshotWork tapes
          (DenseOverlay.Snapshot.initial input) ∧
        abiDone.output = TM.resetBinaryBlank) := by
    refine ⟨?_, ?_, by omega, ?_, ?_, ?_, habiInputCells, ?_, ?_⟩
    · rw [habiInputCells]
      simp [Tape.init]
    · intro j hj
      rw [habiInputCells]
      exact Tape.init_ofBool_cells_ne_start input j hj
    · rw [habiOutput]
      exact hemitOutputParked.read_ne_start
    · rw [habiOutput]
      exact hemitOutputParked.1
    · intro i
      have hiParked := habiReady.control.lookup.scanner.parked i
      have hworkEq : abiDone.work = programSnapshotWork tapes sparseInitial :=
        habiWork
      rw [hworkEq]
      exact ⟨hiParked.read_ne_start, hiParked.1⟩
    · simpa [denseProgramSnapshotWork, sparseInitial] using! habiWork
    · exact habiOutput.trans hemitOutputBlank
  obtain ⟨rewindDone, rewindTime, hrewindTime, hrewindReach,
      hrewindHalt, hrewindHead, hrewindCells, hrewindWork,
      hrewindOutput⟩ := hrewind _ _ _ hrewindPre
  have habiInputParked : TM.Parked abiDone.input :=
    ⟨by omega, hrewindPre.2.1⟩
  have habiOutputParked : TM.Parked abiDone.output := by
    rw [habiOutput]
    exact hemitOutputParked
  have habiWorkParked : ∀ i, TM.Parked (abiDone.work i) := by
    intro i
    rw [habiWork]
    exact habiReady.control.lookup.scanner.parked i
  obtain ⟨habiInputTransition, habiWorkTransition,
      habiOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      habiInputParked.read_ne_start
      (fun i => (habiWorkParked i).read_ne_start)
      habiOutputParked.read_ne_start
  have hrewindReach' : TM.rewindInputTM.reachesIn rewindTime
      { state := TM.rewindInputTM.qstart
        input := TM.transitionInput abiDone.input
        work := fun i => TM.transitionTape (abiDone.work i)
        output := TM.transitionTape abiDone.output }
      rewindDone := by
    simpa only [habiInputTransition, habiWorkTransition,
      habiOutputTransition] using! hrewindReach
  have habiRewindReach := TM.seqTM_reachesIn_of_reachesIn
    (initialAbiInstallTM tapes) TM.rewindInputTM habiReach habiHalt
    hrewindReach'
  let abiRewindDone := TM.phase2Wrap (initialAbiInstallTM tapes)
    TM.rewindInputTM rewindDone
  have habiRewindHalt :
      (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM).halted
        abiRewindDone := by
    rw [TM.phase2Wrap_halted_iff]
    exact hrewindHalt
  obtain ⟨hemitInputTransition, hemitWorkTransition,
      hemitOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hemitInputParked.read_ne_start
      (fun i => (hemitReady.parked i).read_ne_start)
      hemitOutputParked.read_ne_start
  have habiRewindReach' :
      (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM).reachesIn
        (abiTime + 1 + rewindTime)
        { state :=
            (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM).qstart
          input := TM.transitionInput emitDone.input
          work := fun i => TM.transitionTape (emitDone.work i)
          output := TM.transitionTape emitDone.output }
        abiRewindDone := by
    simpa only [hemitInputTransition, hemitWorkTransition,
      hemitOutputTransition] using! habiRewindReach
  have emitTailReach := TM.seqTM_reachesIn_of_reachesIn
    (initialLengthEmitTM tapes)
    (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM)
    hemitReach hemitHalt habiRewindReach'
  let emitTailDone := TM.phase2Wrap (initialLengthEmitTM tapes)
    (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM)
    abiRewindDone
  have emitTailHalt :
      (TM.seqTM (initialLengthEmitTM tapes)
        (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM)).halted
        emitTailDone := by
    exact (TM.phase2Wrap_halted_iff
      (initialLengthEmitTM tapes)
      (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM) abiRewindDone).mpr
      habiRewindHalt
  obtain ⟨hloopInputTransition, hloopWorkTransition,
      hloopOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hloopInputParked.read_ne_start
      (fun i => (hloopReady.parked i).read_ne_start)
      hloopOutputParked.read_ne_start
  have emitTailReach' :
      (TM.seqTM (initialLengthEmitTM tapes)
        (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM)).reachesIn
        (emitTime + 1 + (abiTime + 1 + rewindTime))
        { state :=
            (TM.seqTM (initialLengthEmitTM tapes)
              (TM.seqTM (initialAbiInstallTM tapes)
                TM.rewindInputTM)).qstart
          input := TM.transitionInput loopDone.input
          work := fun i => TM.transitionTape (loopDone.work i)
          output := TM.transitionTape loopDone.output }
        emitTailDone := by
    simpa only [hloopInputTransition, hloopWorkTransition,
      hloopOutputTransition] using! emitTailReach
  have loopTailReach := TM.seqTM_reachesIn_of_reachesIn
    (denseInitialLengthLoopTM tapes)
    (TM.seqTM (initialLengthEmitTM tapes)
      (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM))
    hloopReach hloopHalt emitTailReach'
  let loopTailDone := TM.phase2Wrap (denseInitialLengthLoopTM tapes)
    (TM.seqTM (initialLengthEmitTM tapes)
      (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM))
    emitTailDone
  have loopTailHalt :
      (TM.seqTM (denseInitialLengthLoopTM tapes)
        (TM.seqTM (initialLengthEmitTM tapes)
          (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM))).halted
        loopTailDone := by
    exact (TM.phase2Wrap_halted_iff
      (denseInitialLengthLoopTM tapes)
      (TM.seqTM (initialLengthEmitTM tapes)
        (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM)) emitTailDone).mpr
      emitTailHalt
  obtain ⟨hsetupInputTransition, hsetupWorkTransition,
      hsetupOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hsetupInputParked.read_ne_start
      (fun i => (hsetupReady.parked i).read_ne_start)
      hsetupOutputParked.read_ne_start
  have loopTailReach' :
      (TM.seqTM (denseInitialLengthLoopTM tapes)
        (TM.seqTM (initialLengthEmitTM tapes)
          (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM))).reachesIn
        (loopTime + 1 +
          (emitTime + 1 + (abiTime + 1 + rewindTime)))
        { state :=
            (TM.seqTM (denseInitialLengthLoopTM tapes)
              (TM.seqTM (initialLengthEmitTM tapes)
                (TM.seqTM (initialAbiInstallTM tapes)
                  TM.rewindInputTM))).qstart
          input := TM.transitionInput setupDone.input
          work := fun i => TM.transitionTape (setupDone.work i)
          output := TM.transitionTape setupDone.output }
        loopTailDone := by
    simpa only [hsetupInputTransition, hsetupWorkTransition,
      hsetupOutputTransition] using! loopTailReach
  have hreach := TM.seqTM_reachesIn_of_reachesIn
    (initialSetupTM tapes)
    (TM.seqTM (denseInitialLengthLoopTM tapes)
      (TM.seqTM (initialLengthEmitTM tapes)
        (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM)))
    hsetupReach hsetupHalt loopTailReach'
  let finalCfg := TM.phase2Wrap (initialSetupTM tapes)
    (TM.seqTM (denseInitialLengthLoopTM tapes)
      (TM.seqTM (initialLengthEmitTM tapes)
        (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM)))
    loopTailDone
  refine ⟨finalCfg,
    setupTime + 1 +
      (loopTime + 1 + (emitTime + 1 + (abiTime + 1 + rewindTime))),
    ?_, hreach, ?_, ?_⟩
  · unfold denseProgramInitTime
    omega
  · change (denseProgramInitTM tapes).halted finalCfg
    unfold denseProgramInitTM
    exact (TM.phase2Wrap_halted_iff
      (initialSetupTM tapes)
      (TM.seqTM (denseInitialLengthLoopTM tapes)
        (TM.seqTM (initialLengthEmitTM tapes)
          (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM))) loopTailDone).mpr
      loopTailHalt
  · refine ⟨?_, hrewindWork, hrewindOutput⟩
    change rewindDone.input =
      (Tape.init (input.map Γ.ofBool)).move Dir3.right
    exact Tape.ext (by simpa [Tape.move] using! hrewindHead)
      (by simpa [Tape.move] using! hrewindCells)

end Machine
end RegisterStore
end RAM
end Complexity
