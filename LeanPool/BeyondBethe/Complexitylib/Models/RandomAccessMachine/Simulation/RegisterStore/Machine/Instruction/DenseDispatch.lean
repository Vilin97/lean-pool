/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseSim
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Sim.Internal

/-!
# Fixed-program dense-overlay dispatch
-/


public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

variable {n : ℕ}

private theorem hasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t :=
  ⟨by rw [h.2.1], h.2.hasBinaryContent.cells_ne_start⟩

private theorem denseInput_parked (input : List Bool) :
    TM.Parked ((Tape.init (input.map Γ.ofBool)).move Dir3.right) := by
  refine ⟨by simp [Tape.move], ?_⟩
  simpa using! Tape.init_ofBool_move_right_cells_ne_start input

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

/-- The decrementing branch tree selects the corresponding dense instruction,
including the out-of-range halt convention. -/
theorem denseDispatchProgramTM_hoareTime_frame
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (overlay : Store) (pcValue selector : ℕ)
    (cleanWork work₀ : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : DispatchReady tapes overlay pcValue selector cleanWork work₀) :
    (denseDispatchProgramTM tapes program).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = work₀ ∧ out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseInstructionExecutionResult tapes input
          (selectedInstruction program selector) pcValue overlay work ∧
        out = (Tape.init []).move Dir3.right)
      (denseDispatchProgramTime tapes input overlay pcValue program
        selector) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let out₀ := (Tape.init []).move Dir3.right
  have hinput : TM.Parked inp₀ := by
    simpa only [inp₀] using! denseInput_parked input
  have houtput : TM.Parked out₀ := by
    simpa only [out₀] using! blankOutput_parked
  induction program generalizing selector work₀ with
  | nil =>
      let blankTape := (Tape.init []).move Dir3.right
      have hselector : (work₀ tapes.liftedLhs).HasBinaryNat selector := by
        rw [hready.2]
        simp only [Function.update_self]
        exact Tape.init_move_right_hasBinaryNat selector
      have hcleanLhs : cleanWork tapes.liftedLhs = blankTape := by
        have hzero := hready.1.control.lookup.destination
        change (cleanWork tapes.liftedLhs).HasBinaryNat 0 at hzero
        simpa only [blankTape] using!
          Tape.HasBinaryNat.eq_init_move_right hzero
      have hwork₀Parked : ∀ i, TM.Parked (work₀ i) := by
        intro i
        rw [hready.2]
        by_cases hi : i = tapes.liftedLhs
        · subst i
          simp only [Function.update_self]
          exact hasBinaryNat_parked
            (Tape.init_move_right_hasBinaryNat selector)
        · simp only [Function.update_of_ne hi]
          exact hready.1.control.lookup.scanner.parked i
      have hreset := TM.resetBinaryWorkTM_hoareTime_frame tapes.liftedLhs
        selector.bits 1 inp₀ work₀ out₀
        hselector.2.hasBinaryContent hselector.1
        ⟨by rw [hselector.2.1], by rw [hselector.2.1]⟩
        hinput (fun i _ => hwork₀Parked i) houtput
      have hreset' : (TM.resetBinaryWorkTM tapes.liftedLhs).HoareTime
          (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
          (fun inp work out =>
            inp = inp₀ ∧ work = cleanWork ∧ out = out₀)
          (TM.resetBinaryWorkTime 1 selector.bits.length) := by
        apply hreset.consequence
        · exact fun _ _ _ h => h
        · rintro inp work out ⟨hinp, hworkEq, hout⟩
          refine ⟨hinp, ?_, hout⟩
          rw [hworkEq, hready.2, Function.update_idem]
          change Function.update cleanWork tapes.liftedLhs blankTape =
            cleanWork
          rw [← hcleanLhs, Function.update_eq_self]
        · exact le_rfl
      have hhalt := denseExecuteInstructionTM_hoareTime_frame tapes input
        .halt overlay pcValue cleanWork hvalid hready.1
      have hseq := TM.seqTM_hoareTime
        (TM.resetBinaryWorkTM tapes.liftedLhs)
        (denseExecuteInstructionTM tapes .halt) hreset'
        (by
          rintro inp work out ⟨hinp, hworkEq, hout⟩
          obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
            (inp := inp) (work := work) (out := out)
            (by simpa [hinp] using! hinput)
            (by simpa [hworkEq] using!
              hready.1.control.lookup.scanner.parked)
            (by simpa [hout] using! houtput)
          rw [hi, hw, ho]
          exact ⟨hinp, hworkEq, hout⟩)
        hhalt
      simpa only [denseDispatchProgramTM, dispatchWithTM,
        denseDispatchProgramTime, dispatchWithTime,
        selectedInstruction, inp₀, out₀] using! hseq
  | cons instruction program ih =>
      let pre : TM.TapePred (n + 1) := fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀
      let post : TM.TapePred (n + 1) := fun inp work out =>
        inp = inp₀ ∧
          DenseInstructionExecutionResult tapes input
            (selectedInstruction (instruction :: program) selector)
            pcValue overlay work ∧
          out = out₀
      let blankPre : TM.TapePred (n + 1) := fun inp work out =>
        pre inp work out ∧ selector = 0
      let nonblankPre : TM.TapePred (n + 1) := fun inp work out =>
        pre inp work out ∧ selector ≠ 0
      have hselector : (work₀ tapes.liftedLhs).HasBinaryNat selector := by
        rw [hready.2]
        simp only [Function.update_self]
        exact Tape.init_move_right_hasBinaryNat selector
      have hwork₀Parked : ∀ i, TM.Parked (work₀ i) := by
        intro i
        rw [hready.2]
        by_cases hi : i = tapes.liftedLhs
        · subst i
          simp only [Function.update_self]
          exact hasBinaryNat_parked
            (Tape.init_move_right_hasBinaryNat selector)
        · simp only [Function.update_of_ne hi]
          exact hready.1.control.lookup.scanner.parked i
      have hblank : (denseExecuteInstructionTM tapes instruction).HoareTime
          blankPre post
          (denseExecuteInstructionTime tapes input instruction pcValue
            overlay) := by
        rintro inp work out ⟨⟨hinp, hworkEq, hout⟩, hzero⟩
        subst selector
        have hcleanLhs := Tape.HasBinaryNat.eq_init_move_right
          hready.1.control.lookup.destination
        change cleanWork tapes.liftedLhs =
          (Tape.init []).move Dir3.right at hcleanLhs
        have hworkClean : work = cleanWork := by
          rw [hworkEq, hready.2]
          funext i
          by_cases hi : i = tapes.liftedLhs
          · subst i
            simp only [Function.update_self]
            exact hcleanLhs.symm
          · simp only [Function.update_of_ne hi]
        obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
            hresult, hfinalOutput⟩ :=
          denseExecuteInstructionTM_hoareTime_frame tapes input instruction
            overlay pcValue cleanWork hvalid hready.1 inp cleanWork out
            ⟨hinp, rfl, hout⟩
        refine ⟨final, time, htime, ?_, hhalt, hfinalInput, ?_,
          hfinalOutput⟩
        · simpa [hworkClean] using! hreach
        · simpa only [selectedInstruction] using! hresult
      have hnonblank :
          (TM.seqTM (TM.binaryPredTM tapes.liftedLhs)
            (denseDispatchProgramTM tapes program)).HoareTime
          nonblankPre post
          (TM.binaryPredTime (selector - 1) + 1 +
            denseDispatchProgramTime tapes input overlay pcValue program
              (selector - 1)) := by
        rintro inp work out ⟨⟨hinp, hworkEq, hout⟩, hnonzero⟩
        have hsucc : selector = (selector - 1) + 1 := by omega
        have hvalue : (work tapes.liftedLhs).HasBinaryNat
            ((selector - 1) + 1) := by
          rw [hworkEq]
          rw [hsucc] at hselector
          exact hselector
        have hinpParked : TM.Parked inp := by simpa [hinp] using! hinput
        have houtParked : TM.Parked out := by simpa [hout] using! houtput
        have hworkParked : ∀ i, TM.Parked (work i) := by
          intro i
          simpa [hworkEq] using! hwork₀Parked i
        have hpred := TM.binaryPredTM_hoareTime_frame tapes.liftedLhs
          (selector - 1) inp work out hvalue hinpParked.read_ne_start
          (fun i _ => (hworkParked i).read_ne_start)
          houtParked.read_ne_start
        let nextWork := Function.update cleanWork tapes.liftedLhs
          ((Tape.init ((selector - 1).bits.map Γ.ofBool)).move Dir3.right)
        have hpred' : (TM.binaryPredTM tapes.liftedLhs).HoareTime
            (fun inp' work' out' =>
              inp' = inp ∧ work' = work ∧ out' = out)
            (fun inp' work' out' =>
              inp' = inp ∧ work' = nextWork ∧ out' = out)
            (TM.binaryPredTime (selector - 1)) := by
          apply hpred.consequence
          · exact fun _ _ _ h => h
          · rintro inp' work' out' ⟨hinp', hframe, hvalue', hout'⟩
            refine ⟨hinp', ?_, hout'⟩
            funext i
            by_cases hi : i = tapes.liftedLhs
            · subst i
              simp only [nextWork, Function.update_self]
              exact Tape.HasBinaryNat.eq_init_move_right hvalue'
            · simp only [nextWork, Function.update_of_ne hi]
              rw [hframe i hi, hworkEq, hready.2,
                Function.update_of_ne hi]
          · exact le_rfl
        have hnextReady : DispatchReady tapes overlay pcValue
            (selector - 1) cleanWork nextWork := ⟨hready.1, rfl⟩
        have hrecursive := ih (selector - 1) nextWork hnextReady
        have hrecursive' :
            (denseDispatchProgramTM tapes program).HoareTime
            (fun inp' work' out' =>
              inp' = inp ∧ work' = nextWork ∧ out' = out)
            post
            (denseDispatchProgramTime tapes input overlay pcValue program
              (selector - 1)) := by
          apply hrecursive.consequence
          · rintro inp' work' out' ⟨hinp', hwork', hout'⟩
            exact ⟨hinp'.trans hinp, hwork', hout'.trans hout⟩
          · rintro inp' work' out' ⟨hinp', hresult, hout'⟩
            have hselected :
                selectedInstruction (instruction :: program) selector =
                  selectedInstruction program (selector - 1) := by
              rw [hsucc]
              rfl
            exact ⟨hinp', by simpa only [hselected] using! hresult, hout'⟩
          · exact le_rfl
        have hseq := TM.seqTM_hoareTime
          (TM.binaryPredTM tapes.liftedLhs)
          (denseDispatchProgramTM tapes program) hpred'
          (by
            rintro inp' work' out' ⟨hinp', hwork', hout'⟩
            obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
              (inp := inp') (work := work') (out := out')
              (by simpa [hinp', hinp] using! hinput)
              (by
                intro i
                rw [hwork']
                by_cases hidx : i = tapes.liftedLhs
                · subst i
                  simp only [nextWork, Function.update_self]
                  exact hasBinaryNat_parked
                    (Tape.init_move_right_hasBinaryNat (selector - 1))
                · simp only [nextWork, Function.update_of_ne hidx]
                  exact hready.1.control.lookup.scanner.parked i)
              (by simpa [hout', hout] using! houtput)
            rw [hi, hw, ho]
            exact ⟨hinp', hwork', hout'⟩)
          hrecursive'
        exact hseq inp work out ⟨rfl, rfl, rfl⟩
      by_cases hzero : selector = 0
      · subst selector
        intro inp work out hpre
        obtain ⟨branchDone, time, htime, hreach, hhalt, hpost⟩ :=
          hblank inp work out ⟨hpre, rfl⟩
        have hread : (work tapes.liftedLhs).read = Γ.blank := by
          rw [hpre.2.1]
          exact hselector.read_eq_blank_iff.mpr rfl
        have hinpRead : inp.read ≠ Γ.start := by
          simpa [hpre.1] using! hinput.read_ne_start
        have hworkRead : ∀ i, (work i).read ≠ Γ.start := by
          intro i
          simpa [hpre.2.1] using! (hwork₀Parked i).read_ne_start
        have houtRead : out.read ≠ Γ.start := by
          simp [hpre.2.2]
        obtain ⟨done, hreach', hhalt', hdoneInput, hdoneWork,
            hdoneOutput⟩ :=
          TM.branchWorkBlankTM_reachesIn_blank_frame tapes.liftedLhs
            (denseExecuteInstructionTM tapes instruction)
            (TM.seqTM (TM.binaryPredTM tapes.liftedLhs)
              (denseDispatchProgramTM tapes program))
            inp work out hread hinpRead hworkRead houtRead hreach hhalt
        refine ⟨done, time + 1, ?_, ?_, hhalt', ?_⟩
        · simpa only [denseDispatchProgramTime, dispatchWithTime] using!
            Nat.add_le_add_right htime 1
        · simpa only [denseDispatchProgramTM, dispatchWithTM] using! hreach'
        · rw [hdoneInput, hdoneWork, hdoneOutput]
          exact hpost
      · intro inp work out hpre
        obtain ⟨branchDone, time, htime, hreach, hhalt, hpost⟩ :=
          hnonblank inp work out ⟨hpre, hzero⟩
        have hread : (work tapes.liftedLhs).read ≠ Γ.blank := by
          intro hblankRead
          apply hzero
          exact hselector.read_eq_blank_iff.mp (by
            simpa [hpre.2.1] using! hblankRead)
        have hinpRead : inp.read ≠ Γ.start := by
          simpa [hpre.1] using! hinput.read_ne_start
        have hworkRead : ∀ i, (work i).read ≠ Γ.start := by
          intro i
          simpa [hpre.2.1] using! (hwork₀Parked i).read_ne_start
        have houtRead : out.read ≠ Γ.start := by
          simp [hpre.2.2]
        obtain ⟨done, hreach', hhalt', hdoneInput, hdoneWork,
            hdoneOutput⟩ :=
          TM.branchWorkBlankTM_reachesIn_nonblank_frame tapes.liftedLhs
            (denseExecuteInstructionTM tapes instruction)
            (TM.seqTM (TM.binaryPredTM tapes.liftedLhs)
              (denseDispatchProgramTM tapes program))
            inp work out hread hinpRead hworkRead houtRead hreach hhalt
        refine ⟨done, time + 1, ?_, ?_, hhalt', ?_⟩
        · rw [show selector = selector - 1 + 1 by omega]
          simpa only [denseDispatchProgramTime, dispatchWithTime] using!
            Nat.add_le_add_right htime 1
        · simpa only [denseDispatchProgramTM, dispatchWithTM] using! hreach'
        · rw [hdoneInput, hdoneWork, hdoneOutput]
          exact hpost

/-- Copy the canonical PC into dispatch scratch and execute the selected dense
instruction. -/
theorem denseProgramInstructionTM_hoareTime_frame
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (overlay : Store) (pcValue : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseProgramInstructionTM tapes program).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseInstructionExecutionResult tapes input
          (selectedInstruction program pcValue) pcValue overlay work ∧
        out = (Tape.init []).move Dir3.right)
      (denseProgramInstructionTime tapes program input pcValue overlay) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let out₀ := (Tape.init []).move Dir3.right
  let selectorTape :=
    (Tape.init (pcValue.bits.map Γ.ofBool)).move Dir3.right
  let selectorWork :=
    Function.update initialWork tapes.liftedLhs selectorTape
  have hinput : TM.Parked inp₀ := by
    simpa only [inp₀] using! denseInput_parked input
  have houtput : TM.Parked out₀ := by
    simpa only [out₀] using! blankOutput_parked
  have hcopy := TM.binaryCopyIntoTM_hoareTime_frame tapes.liftedPC
    tapes.liftedLhs tapes.liftedFound tapes.lifted.pc_ne_lhs
    (tapes.lifted.pc_ne 11) (tapes.lifted.data.ne (by decide)) pcValue 0
    inp₀ initialWork out₀ hready.control.pc
    hready.control.lookup.destination hready.control.lookup.copyScratch
    hinput (fun i _ _ _ => hready.control.lookup.scanner.parked i) houtput
  have hselectorReady : DispatchReady tapes overlay pcValue pcValue
      initialWork selectorWork := ⟨hready, rfl⟩
  have hdispatch := denseDispatchProgramTM_hoareTime_frame tapes program
    input overlay pcValue pcValue initialWork selectorWork hvalid
    hselectorReady
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
    (denseDispatchProgramTM tapes program) hcopy
    (by
      rintro inp work out ⟨hinp, hworkEq, hout⟩
      have hinpParked : TM.Parked inp := by simpa [hinp] using! hinput
      have houtParked : TM.Parked out := by simpa [hout] using! houtput
      have hworkParked : ∀ i, TM.Parked (work i) := by
        simpa [hworkEq, selectorWork, selectorTape] using! hselectorParked
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        hinpParked hworkParked houtParked
      rw [hi, hw, ho]
      exact ⟨hinp, by simpa [selectorWork, selectorTape] using! hworkEq,
        hout⟩)
    hdispatch
  simpa only [denseProgramInstructionTM, denseProgramInstructionTime,
    selectorWork, selectorTape, inp₀, out₀] using! hseq

/-- One fixed-program dense RAM step returns to the reusable clean ABI for the
exact successor overlay snapshot. -/
theorem denseProgramStepTM_hoareTime_frame
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (overlay : Store) (pcValue : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseProgramStepTM tapes program).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        InstructionExecutionReady tapes
          (denseInstructionStore input
            (selectedInstruction program pcValue) pcValue overlay)
          (denseInstructionPC input
            (selectedInstruction program pcValue) pcValue overlay)
          work ∧
        out = (Tape.init []).move Dir3.right)
      (denseProgramStepTime tapes program input pcValue overlay) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let blank := (Tape.init []).move Dir3.right
  let instruction := selectedInstruction program pcValue
  let nextStore := denseInstructionStore input instruction pcValue overlay
  let nextPC := denseInstructionPC input instruction pcValue overlay
  let cleanupValues :=
    denseInstructionCleanupValue input instruction overlay
  let remainingValue := denseInstructionRemainingValue instruction overlay
  let sourceBound :=
    denseProgramStepSourceHeadBound tapes program input pcValue overlay
  have hinput : TM.Parked inp₀ := by
    simpa only [inp₀] using! denseInput_parked input
  have hprogram := denseProgramInstructionTM_hoareTime_frame tapes program
    input overlay pcValue initialWork hvalid hready
  have hprogramCleanup :
      (denseProgramInstructionTM tapes program).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = initialWork ∧ out = blank)
        (fun inp work out =>
          inp = inp₀ ∧
          BufferedCleanupReady tapes overlay nextStore nextPC cleanupValues
            remainingValue sourceBound work ∧
          out = blank)
        (denseProgramInstructionTime tapes program input pcValue
          overlay) := by
    intro inp work out hpre
    obtain ⟨c, time, htime, hreach, hhalt, hinp, hresult, hout⟩ :=
      hprogram inp work out (by simpa [inp₀, blank] using! hpre)
    have hsourceStart₀ :
        (work tapes.liftedSource).cells 0 = Γ.start := by
      simpa [hpre.2.1] using! hready.control.lookup.sourceStart
    have hsourceStart := TM.work_cells_zero_eq_start_of_reachesIn
      tapes.liftedSource hreach hsourceStart₀
    have hbufferStart₀ :
        (work tapes.buffer).cells 0 = Γ.start := by
      rw [hpre.2.1, hready.buffer]
      simp [Tape.move, Tape.init]
    have hbufferStart := TM.work_cells_zero_eq_start_of_reachesIn
      tapes.buffer hreach hbufferStart₀
    have hsourceHead :=
      (denseProgramInstructionTM tapes program).work_head_reachesIn_bound
        hreach tapes.liftedSource
    refine ⟨c, time, htime, hreach, hhalt, hinp, ?_, hout⟩
    refine
      { nextCanonical := ?_
        result := ?_
        sourceStart := hsourceStart
        bufferStart := hbufferStart
        sourceHead := ?_ }
    · simpa [nextStore, denseInstructionStore, instruction] using!
        DenseOverlay.Snapshot.stepInstr_canonical input instruction
          { pc := pcValue, overlay := overlay } hvalid.1
    · simpa only [instruction, nextStore, nextPC, cleanupValues,
        remainingValue] using! hresult
    · have hsourceHead₀ : (work tapes.liftedSource).head = 1 := by
        simpa [hpre.2.1] using! hready.control.lookup.sourceHead
      rw [hsourceHead₀] at hsourceHead
      simp only [sourceBound, denseProgramStepSourceHeadBound]
      omega
  have hcleanup :
      (instructionCleanupTM tapes).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧
          BufferedCleanupReady tapes overlay nextStore nextPC cleanupValues
            remainingValue sourceBound work ∧
          out = blank)
        (fun inp work out =>
          inp = inp₀ ∧
          InstructionExecutionReady tapes nextStore nextPC work ∧
          out = blank)
        (bufferedCleanupTime tapes overlay nextStore cleanupValues
          remainingValue sourceBound) := by
    intro inp work out hpre
    have hcleanupWork := bufferedCleanupTM_hoareTime_frame_internal tapes
      overlay nextStore nextPC cleanupValues remainingValue sourceBound work
      inp₀ blank hpre.2.1 hinput blankOutput_parked
    exact hcleanupWork inp work out ⟨hpre.1, rfl, hpre.2.2⟩
  have hseq := TM.seqTM_hoareTime
    (denseProgramInstructionTM tapes program) (instructionCleanupTM tapes)
    hprogramCleanup
    (by
      rintro inp work out ⟨hinp, hcleanupReady, hout⟩
      have hinpParked : TM.Parked inp := by simpa [hinp] using! hinput
      have houtParked : TM.Parked out := by
        simpa [hout, blank] using! blankOutput_parked
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked hinpParked
        hcleanupReady.result.parked houtParked
      rw [hi, hw, ho]
      exact ⟨hinp, hcleanupReady, hout⟩)
    hcleanup
  simpa only [denseProgramStepTM, denseProgramStepTime, instruction,
    nextStore, nextPC, cleanupValues, remainingValue, sourceBound, inp₀,
    blank] using! hseq

end Machine
end RegisterStore
end RAM
end Complexity
