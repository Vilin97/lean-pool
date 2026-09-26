/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Sim.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.CopyWorkOutput

/-!
# Uniform next-store buffering for control instructions
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem hasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t := by
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem hasBinaryPrefix_parked {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : TM.Parked t :=
  TM.hasBinaryPrefix_parked h

/-- Restore the empty entry scanner after copying a control instruction's store buffer. -/
private theorem controlCopy_entryScannerReady
    (tapes : ControlInstructionTapes n) (store : Store) (newPC : ℕ)
    (initialWork work finalWork : Fin (n + 1) → Tape)
    (hcontrolResult :
      ControlInstructionResult tapes.lifted store newPC initialWork work) :
    let bits := store.flatMap Entry.encode
    let source := tapes.liftedSource
    let buffer := tapes.buffer
    (∀ i, i ≠ source → i ≠ buffer → finalWork i = work i) →
    (∀ i, TM.Parked (finalWork i)) →
    (work source).HasBinarySuffix bits →
    (finalWork source).cells = (work source).cells →
    (finalWork source).head = bits.length + 1 →
    (finalWork source).HasOutput bits →
    EntryScanReady tapes.lifted.data.update.entry [] [] finalWork finalWork := by
  dsimp only
  intro hotherFrame hfinalParked hsourceSuffix hsourceCells
    hsourceFinalHead hsourceFinalOutput
  let bits := store.flatMap Entry.encode
  let source := tapes.liftedSource
  let buffer := tapes.buffer
  let entry := tapes.lifted.data.update.entry
  have hrole (slot : Fin 9) (hne : slot ≠ 0) :
      finalWork (entry.idx slot) = work (entry.idx slot) := by
    exact hotherFrame _ (entry.ne hne)
      (tapes.liftedData_ne_buffer ⟨slot, by omega⟩)
  refine
    { source := ?_
      address := by
        change (finalWork (entry.idx 1)).HasBinaryPrefix []
        rw [hrole 1 (by decide)]
        exact hcontrolResult.ready.lookup.scanner.address
      addressStart := by
        change (finalWork (entry.idx 1)).cells 0 = Γ.start
        rw [hrole 1 (by decide)]
        exact hcontrolResult.ready.lookup.scanner.addressStart
      value := by
        change (finalWork (entry.idx 2)).HasBinaryPrefix []
        rw [hrole 2 (by decide)]
        exact hcontrolResult.ready.lookup.scanner.value
      valueStart := by
        change (finalWork (entry.idx 2)).cells 0 = Γ.start
        rw [hrole 2 (by decide)]
        exact hcontrolResult.ready.lookup.scanner.valueStart
      addressCounter := by
        change (finalWork (entry.idx 3)).HasBinaryNat 0
        rw [hrole 3 (by decide)]
        exact hcontrolResult.ready.lookup.scanner.addressCounter
      addressWidth := by
        change (finalWork (entry.idx 4)).HasBinaryNat 0
        rw [hrole 4 (by decide)]
        exact hcontrolResult.ready.lookup.scanner.addressWidth
      valueCounter := by
        change (finalWork (entry.idx 5)).HasBinaryNat 0
        rw [hrole 5 (by decide)]
        exact hcontrolResult.ready.lookup.scanner.valueCounter
      valueWidth := by
        change (finalWork (entry.idx 6)).HasBinaryNat 0
        rw [hrole 6 (by decide)]
        exact hcontrolResult.ready.lookup.scanner.valueWidth
      query := by
        change (finalWork (entry.idx 7)).HasBinaryString []
        rw [hrole 7 (by decide)]
        exact hcontrolResult.ready.lookup.scanner.query
      queryStart := by
        change (finalWork (entry.idx 7)).cells 0 = Γ.start
        rw [hrole 7 (by decide)]
        exact hcontrolResult.ready.lookup.scanner.queryStart
      result := by
        change (finalWork (entry.idx 8)).HasBinaryPrefix []
        rw [hrole 8 (by decide)]
        exact hcontrolResult.ready.lookup.scanner.result
      resultStart := by
        change (finalWork (entry.idx 8)).cells 0 = Γ.start
        rw [hrole 8 (by decide)]
        exact hcontrolResult.ready.lookup.scanner.resultStart
      parked := hfinalParked
      frame := by intro i _ _ _ _ _ _ _ _ _; rfl }
  change (finalWork tapes.liftedSource).HasBinarySuffix []
  refine ⟨by rw [hsourceFinalHead]; omega, ?_, ?_, ?_⟩
  · intro i hi
    simp at hi
  · rw [hsourceFinalHead]
    simpa only [List.length_nil, Nat.add_zero, Nat.add_comm] using hsourceFinalOutput.2
  · intro j hj
    rw [hsourceCells]
    exact hsourceSuffix.2.2.2 j hj

private theorem finishControlInstructionTM_hoareTime_frame_internal
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue newPC : ℕ) (initialWork : Fin (n + 1) → Tape)
    (inp₀ out₀ : Tape) (control : TM (n + 1)) (controlTime : ℕ)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀)
    (hcontrol : control.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        ControlInstructionResult tapes.lifted store newPC initialWork work ∧
        out = out₀)
      controlTime) :
    (finishControlInstructionTM tapes control).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work tapes.buffer).HasBinaryPrefix
          (store.flatMap Entry.encode) ∧
        (work tapes.liftedPC).HasBinaryNat newPC ∧
        (work tapes.lifted.data.update.resultCount).HasBinaryNat
          store.length ∧
        (work tapes.liftedSource).HasBinaryContent
          (store.flatMap Entry.encode) ∧
        (∀ slot, (work (instructionCleanupTape tapes slot)).HasBinaryNat 0) ∧
        (work tapes.lifted.data.update.remaining).HasBinaryNat store.length ∧
        EntryScanReady tapes.lifted.data.update.entry [] [] work work ∧
        (work tapes.lifted.data.shift).HasBinaryNat 0 ∧
        (work tapes.lifted.data.tmp).HasBinaryNat 0 ∧
        (work tapes.lifted.data.dbl).HasBinaryNat 0 ∧
        (∀ i, TM.Parked (work i)) ∧
        out = out₀)
      (controlTime + 1 + (store.flatMap Entry.encode).length + 1) := by
  let bits := store.flatMap Entry.encode
  let source := tapes.liftedSource
  let buffer := tapes.buffer
  have hsourceBuffer : source ≠ buffer := tapes.liftedSource_ne_buffer
  have hcopy : (TM.copyWorkToWorkTM source buffer).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        ControlInstructionResult tapes.lifted store newPC initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work buffer).HasBinaryPrefix bits ∧
        (work tapes.liftedPC).HasBinaryNat newPC ∧
        (work tapes.lifted.data.update.resultCount).HasBinaryNat store.length ∧
        (work tapes.liftedSource).HasBinaryContent bits ∧
        (∀ slot, (work (instructionCleanupTape tapes slot)).HasBinaryNat 0) ∧
        (work tapes.lifted.data.update.remaining).HasBinaryNat store.length ∧
        EntryScanReady tapes.lifted.data.update.entry [] [] work work ∧
        (work tapes.lifted.data.shift).HasBinaryNat 0 ∧
        (work tapes.lifted.data.tmp).HasBinaryNat 0 ∧
        (work tapes.lifted.data.dbl).HasBinaryNat 0 ∧
        (∀ i, TM.Parked (work i)) ∧
        out = out₀)
      (bits.length + 1) := by
    rintro inp work out ⟨hinp, hcontrolResult, hout⟩
    have hsourceHead : (work source).head = 1 := by
      exact hcontrolResult.ready.lookup.sourceHead
    have hsourceSuffix : (work source).HasBinarySuffix bits := by
      exact hcontrolResult.ready.lookup.scanner.source
    have hsourceOutput : (work source).HasOutput bits := by
      refine ⟨?_, ?_⟩
      · intro i hi
        simpa [hsourceHead, Nat.add_comm] using! hsourceSuffix.2.1 i hi
      · simpa [hsourceHead, Nat.add_comm] using! hsourceSuffix.2.2.1
    have hbufferEq : work buffer = (Tape.init []).move Dir3.right := by
      rw [hcontrolResult.frame buffer
        tapes.liftedPC_ne_buffer.symm
        (fun slot => (tapes.liftedData_ne_buffer
          (BinaryInstructionTapes.lhsLookupSlot slot)).symm)]
      exact hready.buffer
    have hcleanup : ∀ slot,
        (work (instructionCleanupTape tapes slot)).HasBinaryNat 0 := by
      intro slot
      fin_cases slot
      · exact ⟨hcontrolResult.ready.lookup.scanner.queryStart,
          by simpa [instructionCleanupTape, instructionCleanupParentSlot] using!
            hcontrolResult.ready.lookup.scanner.query⟩
      · change (work tapes.lifted.data.update.replacement).HasBinaryNat 0
        rw [show work tapes.lifted.data.update.replacement =
            initialWork tapes.lifted.data.update.replacement from
          hcontrolResult.frame _ (tapes.lifted.data_ne_pc 10)
            (fun role =>
              (tapes.lifted.data.lhsLookup_ne_replacement role).symm)]
        exact hready.replacement
      · simpa [instructionCleanupTape, instructionCleanupParentSlot] using!
          hcontrolResult.ready.lookup.copyScratch
      · simpa [instructionCleanupTape, instructionCleanupParentSlot] using!
          hcontrolResult.ready.lookup.destination
      · change (work tapes.lifted.data.rhs).HasBinaryNat 0
        rw [show work tapes.lifted.data.rhs = initialWork tapes.lifted.data.rhs
            from hcontrolResult.frame _ (tapes.lifted.data_ne_pc 14)
              (fun role => (tapes.lifted.data.lhsLookup_ne_rhs role).symm)]
        exact hready.rhs
    let P : TM.TapePred (n + 1) := fun inp' work' out' =>
      inp' = inp₀ ∧ out' = out₀ ∧
      (work' tapes.liftedPC).HasBinaryNat newPC ∧
      (work' tapes.lifted.data.update.resultCount).HasBinaryNat store.length ∧
      (∀ slot, (work' (instructionCleanupTape tapes slot)).HasBinaryNat 0) ∧
      (work' tapes.lifted.data.update.remaining).HasBinaryNat store.length ∧
      (∀ i, i ≠ source → i ≠ buffer → TM.Parked (work' i)) ∧
      ∀ i, i ≠ source → i ≠ buffer → work' i = work i
    have hP : P inp work out := by
      refine ⟨hinp, hout, hcontrolResult.ready.pc, ?_, hcleanup,
        hcontrolResult.ready.lookup.count, ?_, ?_⟩
      · exact hcontrolResult.ready.lookup.countSource
      · intro i _ _
        exact hcontrolResult.ready.lookup.scanner.parked i
      · intro i _ _
        rfl
    have hframe := TM.copyWorkToWorkTM_hoareTime_frame_of_hasOutput
      source buffer hsourceBuffer bits (work source)
      (P := P)
      (by
        intro inp' work' out' inp'' work'' out'' hPred _ _ _ _ _
          hinpEq houtEq hworkFrame
        obtain ⟨hPredInput, hPredOutput, hPredPC, hPredCount,
          hPredCleanup, hPredRemaining, hPredParked, hPredFrame⟩ := hPred
        refine ⟨hinpEq.trans hPredInput, houtEq.trans hPredOutput, ?_, ?_,
          ?_, ?_, ?_, ?_⟩
        · rw [hworkFrame tapes.liftedPC tapes.liftedPC_ne_source
            tapes.liftedPC_ne_buffer]
          exact hPredPC
        · have hpcResultCount :
              tapes.lifted.data.update.resultCount ≠ source := by
            exact tapes.lifted.data.ne (by decide)
          have hresultBuffer :
              tapes.lifted.data.update.resultCount ≠ buffer := by
            exact tapes.liftedData_ne_buffer 12
          rw [hworkFrame _ hpcResultCount hresultBuffer]
          exact hPredCount
        · intro slot
          rw [hworkFrame _ (instructionCleanupTape_ne_source tapes slot)
            (instructionCleanupTape_ne_buffer tapes slot)]
          exact hPredCleanup slot
        · rw [hworkFrame tapes.lifted.data.update.remaining
            (tapes.lifted.data.ne (by decide))
            (tapes.liftedData_ne_buffer 9)]
          exact hPredRemaining
        · intro i hiSource hiBuffer
          rw [hworkFrame i hiSource hiBuffer]
          exact hPredParked i hiSource hiBuffer
        · intro i hiSource hiBuffer
          rw [hworkFrame i hiSource hiBuffer]
          exact hPredFrame i hiSource hiBuffer)
    have hinpParked : TM.Parked inp := by simpa [hinp] using! hinput
    have houtParked : TM.Parked out := by simpa [hout] using! houtput
    obtain ⟨final, time, htime, hreach, hhalt, hsourceCells,
        hsourceFinalHead, hsourceFinalOutput, hbufferPrefix, _hbufferStart,
        hfinalInput, hfinalOutput, hfinalPC, hfinalCount, hfinalCleanup,
        hfinalRemaining, hotherParked, hotherFrame⟩ :=
      hframe inp work out
        ⟨rfl, hsourceHead, hsourceOutput, hbufferEq,
          hinpParked.read_ne_start,
          houtParked.read_ne_start,
          houtParked.1,
          (fun i hiSource hiBuffer =>
            ⟨(hcontrolResult.ready.lookup.scanner.parked i).read_ne_start,
              (hcontrolResult.ready.lookup.scanner.parked i).1⟩),
          hP⟩
    have hfinalSourceContent :
        (final.work source).HasBinaryContent bits := by
      have hsourceInitial : (work source).cells =
          (initialWork source).cells := hcontrolResult.sourceCells
      unfold Tape.HasBinaryContent
      rw [hsourceCells, hsourceInitial]
      exact hready.sourceContent
    have hfinalParked : ∀ i, TM.Parked (final.work i) := by
      intro i
      by_cases hiSource : i = source
      · subst i
        refine ⟨by omega, ?_⟩
        intro j hj
        rw [hsourceCells]
        exact hsourceSuffix.2.2.2 j hj
      by_cases hiBuffer : i = buffer
      · subst i
        exact hasBinaryPrefix_parked hbufferPrefix
      · exact hotherParked i hiSource hiBuffer
    have hfinalScanner : EntryScanReady
        tapes.lifted.data.update.entry [] [] final.work final.work := by
      exact controlCopy_entryScannerReady tapes store newPC initialWork work
        final.work hcontrolResult hotherFrame hfinalParked hsourceSuffix
        hsourceCells hsourceFinalHead hsourceFinalOutput
    have hfinalShift :
        (final.work tapes.lifted.data.shift).HasBinaryNat 0 := by
      change (final.work (tapes.lifted.data.idx 15)).HasBinaryNat 0
      rw [hotherFrame _ (tapes.lifted.data.ne (by decide))
        (tapes.liftedData_ne_buffer 15)]
      exact hcontrolResult.ready.lookup.querySource
    have hfinalTmp :
        (final.work tapes.lifted.data.tmp).HasBinaryNat 0 := by
      change (final.work (tapes.lifted.data.idx 16)).HasBinaryNat 0
      rw [hotherFrame _ (tapes.lifted.data.ne (by decide))
        (tapes.liftedData_ne_buffer 16)]
      rw [hcontrolResult.frame _ (tapes.lifted.data_ne_pc 16)
        (fun slot => (tapes.lifted.data.lhsLookup_ne_tmp slot).symm)]
      exact hready.tmp
    have hfinalDbl :
        (final.work tapes.lifted.data.dbl).HasBinaryNat 0 := by
      change (final.work (tapes.lifted.data.idx 17)).HasBinaryNat 0
      rw [hotherFrame _ (tapes.lifted.data.ne (by decide))
        (tapes.liftedData_ne_buffer 17)]
      rw [hcontrolResult.frame _ (tapes.lifted.data_ne_pc 17)
        (fun slot => (tapes.lifted.data.lhsLookup_ne_dbl slot).symm)]
      exact hready.dbl
    refine ⟨final, time, htime, hreach, hhalt, hfinalInput,
      hbufferPrefix, hfinalPC, hfinalCount, hfinalSourceContent,
      hfinalCleanup, hfinalRemaining, hfinalScanner, hfinalShift, hfinalTmp,
      hfinalDbl, hfinalParked, hfinalOutput⟩
  have hseq := TM.seqTM_hoareTime control
    (TM.copyWorkToWorkTM source buffer) hcontrol
    (by
      rintro inp work out ⟨hinp, hcontrolResult, hout⟩
      have hworkParked := hcontrolResult.ready.lookup.scanner.parked
      have hinpParked : TM.Parked inp := by simpa [hinp] using! hinput
      have houtParked : TM.Parked out := by simpa [hout] using! houtput
      obtain ⟨hi, hw, ho⟩ :=
        TM.phaseTransition_eq_self_of_reads_ne_start
          hinpParked.read_ne_start
          (fun i => (hworkParked i).read_ne_start)
          houtParked.read_ne_start
      rw [hi, hw, ho]
      exact ⟨hinp, hcontrolResult, hout⟩)
    hcopy
  simpa only [finishControlInstructionTM, bits, source, buffer] using! hseq

/-- Representation-independent form of the control-instruction finisher.
Control instructions preserve the encoded store, leave zero on every cleanup
role, and retain the old entry count for the generic cleanup pass. -/
theorem finishBufferedControlInstructionTM_hoareTime_frame_internal
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue newPC : ℕ) (initialWork : Fin (n + 1) → Tape)
    (inp₀ out₀ : Tape) (control : TM (n + 1)) (controlTime : ℕ)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀)
    (hcontrol : control.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        ControlInstructionResult tapes.lifted store newPC initialWork work ∧
        out = out₀)
      controlTime) :
    (finishControlInstructionTM tapes control).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        BufferedInstructionResult tapes store store newPC (fun _ => 0)
          store.length work ∧
        out = out₀)
      (controlTime + 1 + (store.flatMap Entry.encode).length + 1) := by
  have hfinish := finishControlInstructionTM_hoareTime_frame_internal tapes
    store pcValue newPC initialWork inp₀ out₀ control controlTime hready
    hinput houtput hcontrol
  apply hfinish.consequence
  · exact fun _ _ _ h => h
  · rintro inp work out
      ⟨hinp, hbuffer, hpc, hcount, hsourceContent, hcleanup, hremaining,
        hscanner, hshift, htmp, hdbl, hparked, hout⟩
    exact ⟨hinp,
      { buffer := hbuffer
        pc := hpc
        resultCount := hcount
        sourceContent := hsourceContent
        cleanup := hcleanup
        remaining := hremaining
        scanner := hscanner
        shift := hshift
        tmp := htmp
        dbl := hdbl
        parked := hparked },
      hout⟩
  · exact le_rfl

/-- Conditional-zero execution has the common one-buffer instruction
contract. -/
theorem executeInstructionTM_jz_hoareTime_frame
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue source target : ℕ) (initialWork : Fin (n + 1) → Tape)
    (inp₀ out₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (executeInstructionTM tapes (.jz source target)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes (.jz source target) pcValue store
          work ∧
        out = out₀)
      (executeInstructionTime tapes (.jz source target) pcValue store) := by
  have hcontrol := zeroJumpInstructionTM_hoareTime_frame tapes.lifted store
    pcValue source target initialWork inp₀ out₀ hready.control hinput houtput
  have hfinish := finishControlInstructionTM_hoareTime_frame_internal tapes
    store pcValue
      (if RegisterStore.read store source = 0 then target else pcValue + 1)
    initialWork inp₀ out₀ _ _ hready hinput houtput hcontrol
  apply hfinish.consequence
  · exact fun _ _ _ h => h
  · rintro inp work out
      ⟨hinp, hbuffer, hpc, hcount, hsourceContent, hcleanup, hremaining,
        hscanner, hshift, htmp, hdbl, hparked, hout⟩
    by_cases hzero : RegisterStore.read store source = 0
    · exact ⟨hinp,
        { buffer := by
            simpa [instructionStore, Snapshot.stepInstr, hzero] using! hbuffer
          pc := by
            simpa [instructionPC, Snapshot.stepInstr, hzero] using! hpc
          resultCount := by
            simpa [instructionStore, Snapshot.stepInstr, hzero] using! hcount
          sourceContent := hsourceContent
          cleanup := by
            intro slot
            have hvalue : instructionCleanupValue (.jz source target) store
                slot = 0 := by
              fin_cases slot <;> rfl
            rw [hvalue]
            exact hcleanup slot
          remaining := by
            simpa [instructionRemainingValue] using! hremaining
          scanner := by
            simpa [instructionCleanupValue] using! hscanner
          shift := hshift
          tmp := htmp
          dbl := hdbl
          parked := hparked },
        hout⟩
    · exact ⟨hinp,
        { buffer := by
            simpa [instructionStore, Snapshot.stepInstr, hzero] using! hbuffer
          pc := by
            simpa [instructionPC, Snapshot.stepInstr, hzero] using! hpc
          resultCount := by
            simpa [instructionStore, Snapshot.stepInstr, hzero] using! hcount
          sourceContent := hsourceContent
          cleanup := by
            intro slot
            have hvalue : instructionCleanupValue (.jz source target) store
                slot = 0 := by
              fin_cases slot <;> rfl
            rw [hvalue]
            exact hcleanup slot
          remaining := by
            simpa [instructionRemainingValue] using! hremaining
          scanner := by
            simpa [instructionCleanupValue] using! hscanner
          shift := hshift
          tmp := htmp
          dbl := hdbl
          parked := hparked },
        hout⟩
  · exact le_rfl

/-- Unconditional-jump execution has the common one-buffer instruction
contract. -/
theorem executeInstructionTM_jmp_hoareTime_frame
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue target : ℕ) (initialWork : Fin (n + 1) → Tape)
    (inp₀ out₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (executeInstructionTM tapes (.jmp target)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes (.jmp target) pcValue store work ∧
        out = out₀)
      (executeInstructionTime tapes (.jmp target) pcValue store) := by
  have hcontrol := jumpInstructionTM_hoareTime_frame tapes.lifted store
    pcValue target initialWork inp₀ out₀ hready.control hinput houtput
  have hfinish := finishControlInstructionTM_hoareTime_frame_internal tapes
    store pcValue target initialWork inp₀ out₀ _ _ hready hinput houtput
    hcontrol
  apply hfinish.consequence
  · exact fun _ _ _ h => h
  · rintro inp work out
      ⟨hinp, hbuffer, hpc, hcount, hsourceContent, hcleanup, hremaining,
        hscanner, hshift, htmp, hdbl, hparked, hout⟩
    exact ⟨hinp,
      { buffer := by
          simpa [instructionStore, Snapshot.stepInstr] using! hbuffer
        pc := by simpa [instructionPC, Snapshot.stepInstr] using! hpc
        resultCount := by
          simpa [instructionStore, Snapshot.stepInstr] using! hcount
        sourceContent := hsourceContent
        cleanup := by
          intro slot
          have hvalue : instructionCleanupValue (.jmp target) store slot = 0 := by
            fin_cases slot <;> rfl
          rw [hvalue]
          exact hcleanup slot
        remaining := by
          simpa [instructionRemainingValue] using! hremaining
        scanner := by
          simpa [instructionCleanupValue] using! hscanner
        shift := hshift
        tmp := htmp
        dbl := hdbl
        parked := hparked },
      hout⟩
  · exact le_rfl

/-- Halt execution has the common one-buffer instruction contract. -/
theorem executeInstructionTM_halt_hoareTime_frame
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue : ℕ) (initialWork : Fin (n + 1) → Tape)
    (inp₀ out₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (executeInstructionTM tapes .halt).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes .halt pcValue store work ∧
        out = out₀)
      (executeInstructionTime tapes .halt pcValue store) := by
  have hcontrol := haltInstructionTM_hoareTime_frame tapes.lifted store
    pcValue initialWork inp₀ out₀ hready.control hinput houtput
  have hfinish := finishControlInstructionTM_hoareTime_frame_internal tapes
    store pcValue pcValue initialWork inp₀ out₀ _ _ hready hinput houtput
    hcontrol
  apply hfinish.consequence
  · exact fun _ _ _ h => h
  · rintro inp work out
      ⟨hinp, hbuffer, hpc, hcount, hsourceContent, hcleanup, hremaining,
        hscanner, hshift, htmp, hdbl, hparked, hout⟩
    exact ⟨hinp,
      { buffer := by
          simpa [instructionStore, Snapshot.stepInstr] using! hbuffer
        pc := by simpa [instructionPC, Snapshot.stepInstr] using! hpc
        resultCount := by
          simpa [instructionStore, Snapshot.stepInstr] using! hcount
        sourceContent := hsourceContent
        cleanup := by
          intro slot
          have hvalue : instructionCleanupValue .halt store slot = 0 := by
            fin_cases slot <;> rfl
          rw [hvalue]
          exact hcleanup slot
        remaining := by
          simpa [instructionRemainingValue] using! hremaining
        scanner := by
          simpa [instructionCleanupValue] using! hscanner
        shift := hshift
        tmp := htmp
        dbl := hdbl
        parked := hparked },
      hout⟩
  · exact le_rfl

end Machine

end RegisterStore

end RAM

end Complexity
