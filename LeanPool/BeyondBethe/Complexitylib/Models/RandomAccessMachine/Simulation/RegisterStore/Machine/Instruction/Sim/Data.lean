/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Sim.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction

/-!
# Uniform next-store buffering for data instructions
-/


public section

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
    (h : t.HasBinaryPrefix bits) : TM.Parked t := by
  refine ⟨by rw [h.1]; omega, ?_⟩
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  by_cases hi : i < bits.length
  · rw [h.2.1 i hi]
    exact Γ.ofBool_ne_start _
  · rw [h.2.2 i (Nat.le_of_not_gt hi)]
    decide

/-- Restrict the lifted clean lookup ABI to the original data-tape family. -/
theorem instructionExecutionReady_baseLookup_internal
    (tapes : ControlInstructionTapes n) (store : Store) (pcValue : ℕ)
    (work : Fin (n + 1) → Tape)
    (hready : InstructionExecutionReady tapes store pcValue work) :
    EntryLookupStaticReady tapes.data.lhsLookup store
      (fun i => work (Fin.castSucc i)) := by
  let baseWork : Fin n → Tape := fun i => work (Fin.castSucc i)
  have hcastNe {i j : Fin n} (h : i ≠ j) :
      Fin.castSucc i ≠ Fin.castSucc j := by
    intro hij
    exact h (Fin.castSucc_injective _ hij)
  have hscanner : EntryScanReady tapes.data.lhsLookup.scan.entry
      (store.flatMap Entry.encode) [] baseWork baseWork := by
    let hs := hready.control.lookup.scanner
    refine
      { source := hs.source
        address := hs.address
        addressStart := hs.addressStart
        value := hs.value
        valueStart := hs.valueStart
        addressCounter := hs.addressCounter
        addressWidth := hs.addressWidth
        valueCounter := hs.valueCounter
        valueWidth := hs.valueWidth
        query := hs.query
        queryStart := hs.queryStart
        result := hs.result
        resultStart := hs.resultStart
        parked := fun i => hs.parked (Fin.castSucc i)
        frame := ?_ }
    intro i hsource haddress hvalue haddressCounter haddressWidth
      hvalueCounter hvalueWidth hquery hresult
    exact hs.frame (Fin.castSucc i) (hcastNe hsource) (hcastNe haddress)
      (hcastNe hvalue) (hcastNe haddressCounter) (hcastNe haddressWidth)
      (hcastNe hvalueCounter) (hcastNe hvalueWidth) (hcastNe hquery)
      (hcastNe hresult)
  exact
    { scanner := hscanner
      sourceStart := hready.control.lookup.sourceStart
      sourceHead := hready.control.lookup.sourceHead
      count := hready.control.lookup.count
      countSource := hready.control.lookup.countSource
      querySource := hready.control.lookup.querySource
      destination := hready.control.lookup.destination
      copyScratch := hready.control.lookup.copyScratch }

private theorem entryScanReady_of_role_frame {m : ℕ}
    (tapes : EntryMatchTapes m) (sourceBits queryBits : List Bool)
    (initialWork finalWork : Fin m → Tape)
    (hready : EntryScanReady tapes sourceBits queryBits initialWork initialWork)
    (hframe : ∀ slot, finalWork (tapes.idx slot) =
      initialWork (tapes.idx slot))
    (hparked : ∀ i, TM.Parked (finalWork i)) :
    EntryScanReady tapes sourceBits queryBits finalWork finalWork := by
  refine
    { source := by rw [show finalWork tapes.source = initialWork tapes.source
          from hframe 0]; exact hready.source
      address := by rw [show finalWork tapes.address = initialWork tapes.address
          from hframe 1]; exact hready.address
      addressStart := by
        rw [show finalWork tapes.address = initialWork tapes.address
          from hframe 1]; exact hready.addressStart
      value := by rw [show finalWork tapes.value = initialWork tapes.value
          from hframe 2]; exact hready.value
      valueStart := by rw [show finalWork tapes.value = initialWork tapes.value
          from hframe 2]; exact hready.valueStart
      addressCounter := by
        rw [show finalWork tapes.addressCounter =
          initialWork tapes.addressCounter from hframe 3]
        exact hready.addressCounter
      addressWidth := by
        rw [show finalWork tapes.addressWidth = initialWork tapes.addressWidth
          from hframe 4]
        exact hready.addressWidth
      valueCounter := by
        rw [show finalWork tapes.valueCounter = initialWork tapes.valueCounter
          from hframe 5]
        exact hready.valueCounter
      valueWidth := by
        rw [show finalWork tapes.valueWidth = initialWork tapes.valueWidth
          from hframe 6]
        exact hready.valueWidth
      query := by rw [show finalWork tapes.query = initialWork tapes.query
          from hframe 7]; exact hready.query
      queryStart := by rw [show finalWork tapes.query = initialWork tapes.query
          from hframe 7]; exact hready.queryStart
      result := by rw [show finalWork tapes.result = initialWork tapes.result
          from hframe 8]; exact hready.result
      resultStart := by
        rw [show finalWork tapes.result = initialWork tapes.result
          from hframe 8]; exact hready.resultStart
      parked := hparked
      frame := by intro i _ _ _ _ _ _ _ _ _; rfl }

/-- Lift a scanner-ready state on the initial tape family to the one-buffer
layout.  The scanner roles all live below the fresh final tape. -/
private theorem entryScanReady_lifted {m : ℕ}
    (tapes : EntryMatchTapes m) (sourceBits queryBits : List Bool)
    (work : Fin (m + 1) → Tape)
    (hready : EntryScanReady tapes sourceBits queryBits
      (fun i => work (Fin.castSucc i)) (fun i => work (Fin.castSucc i)))
    (hparked : ∀ i, TM.Parked (work i)) :
    EntryScanReady
      { idx := fun slot => Fin.castSucc (tapes.idx slot)
        injective := by
          intro i j h
          apply tapes.injective
          exact Fin.castSucc_injective _ h }
      sourceBits queryBits work work := by
  refine
    { source := hready.source
      address := hready.address
      addressStart := hready.addressStart
      value := hready.value
      valueStart := hready.valueStart
      addressCounter := hready.addressCounter
      addressWidth := hready.addressWidth
      valueCounter := hready.valueCounter
      valueWidth := hready.valueWidth
      query := hready.query
      queryStart := hready.queryStart
      result := hready.result
      resultStart := hready.resultStart
      parked := hparked
      frame := by intro i _ _ _ _ _ _ _ _ _; rfl }

/-- Increment the PC after a redirected data kernel satisfying the common
pre-successor boundary. -/
theorem finishBufferedDataTM_hoareTime_frame_internal
    (tapes : ControlInstructionTapes n) (oldStore nextStore : Store)
    (nextPC pcValue : ℕ) (cleanupValues : Fin 5 → ℕ)
    (remainingValue : ℕ) (initialWork : Fin (n + 1) → Tape)
    (inp₀ : Tape) (dataTM : TM n) (dataTime : ℕ)
    (hpcNext : nextPC = pcValue + 1)
    (hinput : TM.Parked inp₀)
    (hdata : dataTM.retargetOutput.HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        (work tapes.buffer).HasBinaryPrefix
          (nextStore.flatMap Entry.encode) ∧
        (work tapes.liftedPC).HasBinaryNat pcValue ∧
        (work tapes.lifted.data.update.resultCount).HasBinaryNat
          nextStore.length ∧
        (work tapes.liftedSource).HasBinaryContent
          (oldStore.flatMap Entry.encode) ∧
        (∀ slot,
          (work (instructionCleanupTape tapes slot)).HasBinaryNat
            (cleanupValues slot)) ∧
        (work tapes.lifted.data.update.remaining).HasBinaryNat
          remainingValue ∧
        EntryScanReady tapes.lifted.data.update.entry []
          (cleanupValues 0).bits work work ∧
        (work tapes.lifted.data.shift).HasBinaryNat 0 ∧
        (work tapes.lifted.data.tmp).HasBinaryNat 0 ∧
        (work tapes.lifted.data.dbl).HasBinaryNat 0 ∧
        (∀ i, TM.Parked (work i)) ∧
        out = (Tape.init []).move Dir3.right)
      dataTime) :
    (TM.seqTM dataTM.retargetOutput
      (TM.binarySuccTM tapes.liftedPC)).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        BufferedInstructionResult tapes oldStore nextStore nextPC
          cleanupValues remainingValue work ∧
        out = (Tape.init []).move Dir3.right)
      (dataTime + 1 + TM.binarySuccTime pcValue) := by
  let out₀ := (Tape.init []).move Dir3.right
  have hout : TM.Parked out₀ :=
    hasBinaryPrefix_parked Tape.init_nil_move_right_hasBinaryPrefix_nil
  have hsucc : (TM.binarySuccTM tapes.liftedPC).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        (work tapes.buffer).HasBinaryPrefix
          (nextStore.flatMap Entry.encode) ∧
        (work tapes.liftedPC).HasBinaryNat pcValue ∧
        (work tapes.lifted.data.update.resultCount).HasBinaryNat
          nextStore.length ∧
        (work tapes.liftedSource).HasBinaryContent
          (oldStore.flatMap Entry.encode) ∧
        (∀ slot,
          (work (instructionCleanupTape tapes slot)).HasBinaryNat
            (cleanupValues slot)) ∧
        (work tapes.lifted.data.update.remaining).HasBinaryNat
          remainingValue ∧
        EntryScanReady tapes.lifted.data.update.entry []
          (cleanupValues 0).bits work work ∧
        (work tapes.lifted.data.shift).HasBinaryNat 0 ∧
        (work tapes.lifted.data.tmp).HasBinaryNat 0 ∧
        (work tapes.lifted.data.dbl).HasBinaryNat 0 ∧
        (∀ i, TM.Parked (work i)) ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        BufferedInstructionResult tapes oldStore nextStore nextPC
          cleanupValues remainingValue work ∧
        out = out₀)
      (TM.binarySuccTime pcValue) := by
    rintro inp work out
      ⟨hinp, hbuffer, hpc, hcount, hsourceContent, hcleanup, hremaining,
        hscanner, hshift, htmp, hdbl, hparked, houtEq⟩
    have hinpParked : TM.Parked inp := by simpa [hinp] using! hinput
    have houtParked : TM.Parked out := by simpa [houtEq] using! hout
    have hrun := TM.binarySuccTM_hoareTime_frame tapes.liftedPC pcValue
      inp work out hpc hinpParked.read_ne_start
      (fun i _ => (hparked i).read_ne_start) houtParked.read_ne_start
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput, hframe,
        hfinalPC, hfinalOutput⟩ := hrun inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨final, time, htime, hreach, hhalt, hfinalInput.trans hinp,
      ?_, hfinalOutput.trans houtEq⟩
    refine
      { buffer := ?_
        pc := ?_
        resultCount := ?_
        sourceContent := ?_
        cleanup := ?_
        remaining := ?_
        scanner := ?_
        shift := ?_
        tmp := ?_
        dbl := ?_
        parked := ?_ }
    · rw [hframe tapes.buffer tapes.liftedPC_ne_buffer.symm]
      exact hbuffer
    · rw [hpcNext]
      exact hfinalPC
    · rw [hframe tapes.lifted.data.update.resultCount
          (tapes.lifted.data_ne_pc 12)]
      exact hcount
    · rw [hframe tapes.liftedSource tapes.liftedPC_ne_source.symm]
      exact hsourceContent
    · intro slot
      rw [show final.work (instructionCleanupTape tapes slot) =
          work (instructionCleanupTape tapes slot) from
        hframe _ (tapes.lifted.data_ne_pc
          (instructionCleanupParentSlot slot))]
      exact hcleanup slot
    · rw [hframe tapes.lifted.data.update.remaining
          (tapes.lifted.data_ne_pc 9)]
      exact hremaining
    · exact entryScanReady_of_role_frame _ _ _ _ _ hscanner
        (fun slot => hframe _ (tapes.lifted.pc_ne ⟨slot, by omega⟩).symm)
        (by
          intro i
          by_cases hi : i = tapes.liftedPC
          · subst i
            exact hasBinaryNat_parked hfinalPC
          · rw [hframe i hi]
            exact hparked i)
    · rw [hframe tapes.lifted.data.shift (tapes.lifted.data_ne_pc 15)]
      exact hshift
    · rw [hframe tapes.lifted.data.tmp (tapes.lifted.data_ne_pc 16)]
      exact htmp
    · rw [hframe tapes.lifted.data.dbl (tapes.lifted.data_ne_pc 17)]
      exact hdbl
    · intro i
      by_cases hi : i = tapes.liftedPC
      · subst i
        exact hasBinaryNat_parked hfinalPC
      · rw [hframe i hi]
        exact hparked i
  have hseq := TM.seqTM_hoareTime dataTM.retargetOutput
    (TM.binarySuccTM tapes.liftedPC) hdata
    (by
      rintro inp work out
        ⟨hinp, hbuffer, hpc, hcount, hsourceContent, hcleanup, hremaining,
          hscanner, hshift, htmp, hdbl, hparked, houtEq⟩
      have hinpParked : TM.Parked inp := by simpa [hinp] using! hinput
      have houtParked : TM.Parked out := by simpa [houtEq] using! hout
      obtain ⟨hi, hw, ho⟩ :=
        TM.phaseTransition_eq_self_of_reads_ne_start
          hinpParked.read_ne_start
          (fun i => (hparked i).read_ne_start)
          houtParked.read_ne_start
      rw [hi, hw, ho]
      exact ⟨hinp, hbuffer, hpc, hcount, hsourceContent, hcleanup,
        hremaining, hscanner, hshift, htmp, hdbl, hparked, houtEq⟩)
    hsucc
  simpa only [out₀] using! hseq

/-- Sparse-instruction specialization of buffered data finalization. -/
private theorem finishDataInstructionTM_hoareTime_frame_internal
    (tapes : ControlInstructionTapes n) (instruction : Instr)
    (store : Store) (pcValue : ℕ) (initialWork : Fin (n + 1) → Tape)
    (inp₀ : Tape) (dataTM : TM n) (dataTime : ℕ)
    (hpcNext : instructionPC instruction pcValue store = pcValue + 1)
    (hinput : TM.Parked inp₀)
    (hdata : dataTM.retargetOutput.HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        (work tapes.buffer).HasBinaryPrefix
          ((instructionStore instruction pcValue store).flatMap Entry.encode) ∧
        (work tapes.liftedPC).HasBinaryNat pcValue ∧
        (work tapes.lifted.data.update.resultCount).HasBinaryNat
          (instructionStore instruction pcValue store).length ∧
        (work tapes.liftedSource).HasBinaryContent
          (store.flatMap Entry.encode) ∧
        (∀ slot,
          (work (instructionCleanupTape tapes slot)).HasBinaryNat
            (instructionCleanupValue instruction store slot)) ∧
        (work tapes.lifted.data.update.remaining).HasBinaryNat
          (instructionRemainingValue instruction store) ∧
        EntryScanReady tapes.lifted.data.update.entry []
          (instructionCleanupValue instruction store 0).bits work work ∧
        (work tapes.lifted.data.shift).HasBinaryNat 0 ∧
        (work tapes.lifted.data.tmp).HasBinaryNat 0 ∧
        (work tapes.lifted.data.dbl).HasBinaryNat 0 ∧
        (∀ i, TM.Parked (work i)) ∧
        out = (Tape.init []).move Dir3.right)
      dataTime) :
    (TM.seqTM dataTM.retargetOutput
      (TM.binarySuccTM tapes.liftedPC)).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes instruction pcValue store work ∧
        out = (Tape.init []).move Dir3.right)
      (dataTime + 1 + TM.binarySuccTime pcValue) := by
  have hrun := finishBufferedDataTM_hoareTime_frame_internal tapes store
    (instructionStore instruction pcValue store)
    (instructionPC instruction pcValue store) pcValue
    (instructionCleanupValue instruction store)
    (instructionRemainingValue instruction store) initialWork inp₀ dataTM
    dataTime hpcNext hinput hdata
  exact hrun.strengthen_post (by
    rintro inp work out ⟨hinp, hresult, hout⟩
    exact ⟨hinp,
      { buffer := hresult.buffer
        pc := hresult.pc
        resultCount := hresult.resultCount
        sourceContent := hresult.sourceContent
        cleanup := hresult.cleanup
        remaining := hresult.remaining
        scanner := hresult.scanner
        shift := hresult.shift
        tmp := hresult.tmp
        dbl := hresult.dbl
        parked := hresult.parked },
      hout⟩)

/-- Lift a base data-kernel contract through output redirection once its
semantic result exposes PC framing, the next-store count, and parked heads. -/
theorem retargetBufferedDataKernel_hoareTime_frame_internal
    (tapes : ControlInstructionTapes n) (oldStore nextStore : Store)
    (cleanupValues : Fin 5 → ℕ) (remainingValue pcValue : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (inp₀ : Tape) (dataTM : TM n) (dataTime : ℕ)
    (Result : (Fin n → Tape) → Prop)
    (hready : InstructionExecutionReady tapes oldStore pcValue initialWork)
    (hbase : dataTM.HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        work = (fun i => initialWork (Fin.castSucc i)) ∧
        out = initialWork tapes.buffer)
      (fun inp work out =>
        inp = inp₀ ∧ Result work ∧
        out.HasBinaryPrefix
          (nextStore.flatMap Entry.encode))
      dataTime)
    (hresult : ∀ work, Result work →
      work tapes.pc = initialWork (Fin.castSucc tapes.pc) ∧
      (work tapes.data.update.resultCount).HasBinaryNat
        nextStore.length ∧
      (work tapes.data.update.entry.source).HasBinaryContent
        (oldStore.flatMap Entry.encode) ∧
      (∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (cleanupValues slot)) ∧
      (work tapes.data.update.remaining).HasBinaryNat
        remainingValue ∧
      EntryScanReady tapes.data.update.entry []
        (cleanupValues 0).bits work work ∧
      (work tapes.data.shift).HasBinaryNat 0 ∧
      (work tapes.data.tmp).HasBinaryNat 0 ∧
      (work tapes.data.dbl).HasBinaryNat 0 ∧
      ∀ i, TM.Parked (work i)) :
    dataTM.retargetOutput.HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        (work tapes.buffer).HasBinaryPrefix
          (nextStore.flatMap Entry.encode) ∧
        (work tapes.liftedPC).HasBinaryNat pcValue ∧
        (work tapes.lifted.data.update.resultCount).HasBinaryNat
          nextStore.length ∧
        (work tapes.liftedSource).HasBinaryContent
          (oldStore.flatMap Entry.encode) ∧
        (∀ slot,
          (work (instructionCleanupTape tapes slot)).HasBinaryNat
            (cleanupValues slot)) ∧
        (work tapes.lifted.data.update.remaining).HasBinaryNat
          remainingValue ∧
        EntryScanReady tapes.lifted.data.update.entry []
          (cleanupValues 0).bits work work ∧
        (work tapes.lifted.data.shift).HasBinaryNat 0 ∧
        (work tapes.lifted.data.tmp).HasBinaryNat 0 ∧
        (work tapes.lifted.data.dbl).HasBinaryNat 0 ∧
        (∀ i, TM.Parked (work i)) ∧
        out = (Tape.init []).move Dir3.right)
      dataTime := by
  have hlift := TM.retargetOutput_hoareTime dataTM hbase
  apply hlift.consequence
  · rintro inp work out ⟨hinp, hwork, hout⟩
    subst work
    exact ⟨⟨hinp, rfl, rfl⟩, hout⟩
  · rintro inp work out ⟨⟨hinp, hsemantic, hbuffer⟩, hout⟩
    obtain ⟨hpcEq, hcount, hsourceContent, hcleanup, hremaining, hscanner,
      hshift, htmp, hdbl, hparkedBase⟩ :=
      hresult _ hsemantic
    have hpc : (work tapes.liftedPC).HasBinaryNat pcValue := by
      change (work (Fin.castSucc tapes.pc)).HasBinaryNat pcValue
      rw [hpcEq]
      exact hready.control.pc
    have hparked : ∀ i, TM.Parked (work i) := by
      intro i
      exact Fin.lastCases (hasBinaryPrefix_parked hbuffer)
        (fun j => hparkedBase j) i
    exact ⟨hinp, hbuffer, hpc, hcount, hsourceContent, hcleanup,
      hremaining, by
        simpa [ControlInstructionTapes.lifted] using!
          entryScanReady_lifted tapes.data.update.entry _ _ work hscanner
            hparked,
      hshift, htmp, hdbl, hparked, hout⟩
  · exact le_rfl

/-- Sparse specialization of representation-independent output retargeting. -/
private theorem retargetDataKernel_hoareTime_frame_internal
    (tapes : ControlInstructionTapes n) (instruction : Instr)
    (store : Store) (pcValue : ℕ) (initialWork : Fin (n + 1) → Tape)
    (inp₀ : Tape) (dataTM : TM n) (dataTime : ℕ)
    (Result : (Fin n → Tape) → Prop)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hbase : dataTM.HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        work = (fun i => initialWork (Fin.castSucc i)) ∧
        out = initialWork tapes.buffer)
      (fun inp work out =>
        inp = inp₀ ∧ Result work ∧
        out.HasBinaryPrefix
          ((instructionStore instruction pcValue store).flatMap Entry.encode))
      dataTime)
    (hresult : ∀ work, Result work →
      work tapes.pc = initialWork (Fin.castSucc tapes.pc) ∧
      (work tapes.data.update.resultCount).HasBinaryNat
        (instructionStore instruction pcValue store).length ∧
      (work tapes.data.update.entry.source).HasBinaryContent
        (store.flatMap Entry.encode) ∧
      (∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (instructionCleanupValue instruction store slot)) ∧
      (work tapes.data.update.remaining).HasBinaryNat
        (instructionRemainingValue instruction store) ∧
      EntryScanReady tapes.data.update.entry []
        (instructionCleanupValue instruction store 0).bits work work ∧
      (work tapes.data.shift).HasBinaryNat 0 ∧
      (work tapes.data.tmp).HasBinaryNat 0 ∧
      (work tapes.data.dbl).HasBinaryNat 0 ∧
      ∀ i, TM.Parked (work i)) :
    dataTM.retargetOutput.HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        (work tapes.buffer).HasBinaryPrefix
          ((instructionStore instruction pcValue store).flatMap Entry.encode) ∧
        (work tapes.liftedPC).HasBinaryNat pcValue ∧
        (work tapes.lifted.data.update.resultCount).HasBinaryNat
          (instructionStore instruction pcValue store).length ∧
        (work tapes.liftedSource).HasBinaryContent
          (store.flatMap Entry.encode) ∧
        (∀ slot,
          (work (instructionCleanupTape tapes slot)).HasBinaryNat
            (instructionCleanupValue instruction store slot)) ∧
        (work tapes.lifted.data.update.remaining).HasBinaryNat
          (instructionRemainingValue instruction store) ∧
        EntryScanReady tapes.lifted.data.update.entry []
          (instructionCleanupValue instruction store 0).bits work work ∧
        (work tapes.lifted.data.shift).HasBinaryNat 0 ∧
        (work tapes.lifted.data.tmp).HasBinaryNat 0 ∧
        (work tapes.lifted.data.dbl).HasBinaryNat 0 ∧
        (∀ i, TM.Parked (work i)) ∧
        out = (Tape.init []).move Dir3.right)
      dataTime :=
  retargetBufferedDataKernel_hoareTime_frame_internal tapes store
    (instructionStore instruction pcValue store)
    (instructionCleanupValue instruction store)
    (instructionRemainingValue instruction store) pcValue initialWork inp₀
    dataTM dataTime Result hready hbase hresult

/-- Instruction constructor corresponding to a direct arithmetic kernel. -/
def directInstruction (op : BinaryInstrOp) (destination source₀
    source₁ : ℕ) : Instr :=
  match op with
  | .add => .add destination source₀ source₁
  | .sub => .sub destination source₀ source₁
  | .mul => .mul destination source₀ source₁

/-- Immediate execution redirects the new sparse store and increments the
program counter. -/
theorem executeInstructionTM_imm_hoareTime_frame
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue destination value : ℕ)
    (initialWork : Fin (n + 1) → Tape) (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) :
    (executeInstructionTM tapes (.imm destination value)).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes (.imm destination value) pcValue
          store work ∧
        out = (Tape.init []).move Dir3.right)
      (executeInstructionTime tapes (.imm destination value) pcValue store) := by
  let baseWork : Fin n → Tape := fun i => initialWork (Fin.castSucc i)
  have hlookup : EntryLookupStaticReady tapes.data.lhsLookup store baseWork := by
    exact instructionExecutionReady_baseLookup_internal tapes store pcValue
      initialWork
      hready
  have hreplacement :
      (baseWork tapes.data.update.replacement).HasBinaryNat 0 := by
    exact hready.replacement
  have hbuffer :
      (initialWork tapes.buffer).HasBinaryPrefix [] := by
    rw [hready.buffer]
    exact Tape.init_nil_move_right_hasBinaryPrefix_nil
  have hbase := immediateInstructionTM_hoareTime_frame tapes.data store
    destination value [] baseWork inp₀ (initialWork tapes.buffer)
    hready.canonical hlookup hreplacement hinput hbuffer
  have hlift := TM.retargetOutput_hoareTime
    (immediateInstructionTM tapes.data destination value) hbase
  have hdata :
      (immediateInstructionTM tapes.data destination value).retargetOutput.HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = initialWork ∧
          out = (Tape.init []).move Dir3.right)
        (fun inp work out =>
          inp = inp₀ ∧
          (work tapes.buffer).HasBinaryPrefix
            ((instructionStore (.imm destination value) pcValue store).flatMap
              Entry.encode) ∧
          (work tapes.liftedPC).HasBinaryNat pcValue ∧
          (work tapes.lifted.data.update.resultCount).HasBinaryNat
            (instructionStore (.imm destination value) pcValue store).length ∧
          (work tapes.liftedSource).HasBinaryContent
            (store.flatMap Entry.encode) ∧
          (∀ slot,
            (work (instructionCleanupTape tapes slot)).HasBinaryNat
              (instructionCleanupValue (.imm destination value) store slot)) ∧
          (work tapes.lifted.data.update.remaining).HasBinaryNat
            (instructionRemainingValue (.imm destination value) store) ∧
          EntryScanReady tapes.lifted.data.update.entry [] destination.bits
            work work ∧
          (work tapes.lifted.data.shift).HasBinaryNat 0 ∧
          (work tapes.lifted.data.tmp).HasBinaryNat 0 ∧
          (work tapes.lifted.data.dbl).HasBinaryNat 0 ∧
          (∀ i, TM.Parked (work i)) ∧
          out = (Tape.init []).move Dir3.right)
        (immediateInstructionTime tapes.data store destination value) := by
    apply hlift.consequence
    · rintro inp work out ⟨hinp, hwork, hout⟩
      subst work
      exact ⟨⟨hinp, rfl, rfl⟩, hout⟩
    · rintro inp work out ⟨⟨hinp, hresult, hbuffer'⟩, hout⟩
      obtain ⟨valueWork, updateWork, hvalueWork, hupdateWork, houtcome,
        hsourceCells⟩ := hresult
      have hpcBase :
          (fun i => work (Fin.castSucc i)) tapes.pc = baseWork tapes.pc := by
        have hpcQuery :
            tapes.pc ≠ tapes.data.update.entry.query := tapes.pc_ne 7
        have hpcReplacement :
            tapes.pc ≠ tapes.data.update.replacement := tapes.pc_ne 10
        calc
          work (Fin.castSucc tapes.pc) = updateWork tapes.pc :=
            houtcome.frame tapes.pc (fun slot => by
              exact tapes.pc_ne ⟨slot, by omega⟩)
          _ = valueWork tapes.pc := by
            rw [hupdateWork, Function.update_of_ne hpcQuery]
          _ = baseWork tapes.pc := by
            rw [hvalueWork, Function.update_of_ne hpcReplacement]
      have hpc : (work tapes.liftedPC).HasBinaryNat pcValue := by
        change ((fun i => work (Fin.castSucc i)) tapes.pc).HasBinaryNat pcValue
        rw [hpcBase]
        exact hready.control.pc
      have hcount :
          (work tapes.lifted.data.update.resultCount).HasBinaryNat
            (RegisterStore.write store destination value).length := by
        exact houtcome.resultCount
      have hparked : ∀ i, TM.Parked (work i) := by
        intro i
        exact Fin.lastCases (hasBinaryPrefix_parked hbuffer')
          (fun j => houtcome.ready.parked j) i
      have hsourceContent :
          (work tapes.liftedSource).HasBinaryContent
            (store.flatMap Entry.encode) := by
        change ((fun i => work (Fin.castSucc i))
          tapes.data.update.entry.source).HasBinaryContent _
        unfold Tape.HasBinaryContent
        rw [hsourceCells]
        exact hready.sourceContent
      have hcleanup : ∀ slot,
          (work (instructionCleanupTape tapes slot)).HasBinaryNat
            (instructionCleanupValue (.imm destination value) store slot) := by
        intro slot
        fin_cases slot
        · exact ⟨houtcome.ready.queryStart, by
            simpa [instructionCleanupValue, instructionCleanupTape,
              instructionCleanupParentSlot] using! houtcome.ready.query⟩
        · change ((fun i => work (Fin.castSucc i))
              tapes.data.update.replacement).HasBinaryNat value
          rw [show (fun i => work (Fin.castSucc i))
                tapes.data.update.replacement =
              updateWork tapes.data.update.replacement from
            houtcome.replacement]
          rw [show updateWork tapes.data.update.replacement =
              valueWork tapes.data.update.replacement by
            rw [hupdateWork]
            exact Function.update_of_ne
              (tapes.data.update.ne (by decide)) _ _]
          rw [show valueWork tapes.data.update.replacement =
              (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right by
            rw [hvalueWork]
            exact Function.update_self _ _ _]
          exact Tape.init_move_right_hasBinaryNat value
        · simpa [instructionCleanupValue, instructionCleanupTape,
            instructionCleanupParentSlot] using! houtcome.found
        · change ((fun i => work (Fin.castSucc i)) tapes.data.lhs).HasBinaryNat 0
          rw [show (fun i => work (Fin.castSucc i)) tapes.data.lhs =
              updateWork tapes.data.lhs from
            houtcome.frame tapes.data.lhs (fun role =>
              (tapes.data.update_ne_lhs role).symm),
            show updateWork tapes.data.lhs = valueWork tapes.data.lhs by
              rw [hupdateWork]
              exact Function.update_of_ne
                (tapes.data.update_ne_lhs 7).symm _ _,
            show valueWork tapes.data.lhs = baseWork tapes.data.lhs by
              rw [hvalueWork]
              exact Function.update_of_ne
                (tapes.data.update_ne_lhs 10).symm _ _]
          exact hready.control.lookup.destination
        · change ((fun i => work (Fin.castSucc i)) tapes.data.rhs).HasBinaryNat 0
          rw [show (fun i => work (Fin.castSucc i)) tapes.data.rhs =
              updateWork tapes.data.rhs from
            houtcome.frame tapes.data.rhs (fun role =>
              (tapes.data.update_ne_rhs role).symm),
            show updateWork tapes.data.rhs = valueWork tapes.data.rhs by
              rw [hupdateWork]
              exact Function.update_of_ne
                (tapes.data.update_ne_rhs 7).symm _ _,
            show valueWork tapes.data.rhs = baseWork tapes.data.rhs by
              rw [hvalueWork]
              exact Function.update_of_ne
                (tapes.data.update_ne_rhs 10).symm _ _]
          exact hready.rhs
      have hshift : (work tapes.lifted.data.shift).HasBinaryNat 0 := by
        change ((fun i => work (Fin.castSucc i))
          tapes.data.shift).HasBinaryNat 0
        have hqueryNe : tapes.data.shift ≠
            tapes.data.update.entry.query :=
          (tapes.data.update_ne_shift 7).symm
        have hreplacementNe : tapes.data.shift ≠
            tapes.data.update.replacement :=
          (tapes.data.update_ne_shift 10).symm
        rw [houtcome.frame tapes.data.shift (fun slot =>
              (tapes.data.update_ne_shift slot).symm),
          hupdateWork, Function.update_of_ne hqueryNe,
          hvalueWork, Function.update_of_ne hreplacementNe]
        exact hready.control.lookup.querySource
      have htmp' : (work tapes.lifted.data.tmp).HasBinaryNat 0 := by
        change ((fun i => work (Fin.castSucc i))
          tapes.data.tmp).HasBinaryNat 0
        have hqueryNe : tapes.data.tmp ≠
            tapes.data.update.entry.query :=
          (tapes.data.update_ne_tmp 7).symm
        have hreplacementNe : tapes.data.tmp ≠
            tapes.data.update.replacement :=
          (tapes.data.update_ne_tmp 10).symm
        rw [houtcome.frame tapes.data.tmp (fun slot =>
              (tapes.data.update_ne_tmp slot).symm),
          hupdateWork, Function.update_of_ne hqueryNe,
          hvalueWork, Function.update_of_ne hreplacementNe]
        exact hready.tmp
      have hdbl' : (work tapes.lifted.data.dbl).HasBinaryNat 0 := by
        change ((fun i => work (Fin.castSucc i))
          tapes.data.dbl).HasBinaryNat 0
        have hqueryNe : tapes.data.dbl ≠
            tapes.data.update.entry.query :=
          (tapes.data.update_ne_dbl 7).symm
        have hreplacementNe : tapes.data.dbl ≠
            tapes.data.update.replacement :=
          (tapes.data.update_ne_dbl 10).symm
        rw [houtcome.frame tapes.data.dbl (fun slot =>
              (tapes.data.update_ne_dbl slot).symm),
          hupdateWork, Function.update_of_ne hqueryNe,
          hvalueWork, Function.update_of_ne hreplacementNe]
        exact hready.dbl
      refine ⟨hinp, ?_, hpc, ?_, hsourceContent, hcleanup, ?_, ?_, hshift,
        htmp', hdbl', hparked, hout⟩
      · simpa [instructionStore, Snapshot.stepInstr] using! hbuffer'
      · simpa [instructionStore, Snapshot.stepInstr] using! hcount
      · simpa [instructionRemainingValue] using! houtcome.remaining
      · simpa [ControlInstructionTapes.lifted] using!
          entryScanReady_lifted tapes.data.update.entry _ _ work
            houtcome.ready hparked
    · exact le_rfl
  simpa only [executeInstructionTM, executeInstructionTime] using!
    finishDataInstructionTM_hoareTime_frame_internal tapes
      (.imm destination value) store pcValue initialWork inp₀
      (immediateInstructionTM tapes.data destination value)
      (immediateInstructionTime tapes.data store destination value) rfl hinput
      hdata

/-- A direct arithmetic kernel redirects its next sparse store and increments
the program counter. -/
theorem executeInstructionTM_direct_hoareTime_frame
    (tapes : ControlInstructionTapes n) (op : BinaryInstrOp) (store : Store)
    (pcValue destination source₀ source₁ : ℕ)
    (initialWork : Fin (n + 1) → Tape) (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) :
    (executeInstructionTM tapes
      (directInstruction op destination source₀ source₁)).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes
          (directInstruction op destination source₀ source₁) pcValue store
          work ∧
        out = (Tape.init []).move Dir3.right)
      (executeInstructionTime tapes
        (directInstruction op destination source₀ source₁) pcValue store) := by
  let baseWork : Fin n → Tape := fun i => initialWork (Fin.castSucc i)
  have hlookup : EntryLookupStaticReady tapes.data.lhsLookup store baseWork :=
    instructionExecutionReady_baseLookup_internal tapes store pcValue
      initialWork hready
  have hrhs : (baseWork tapes.data.rhs).HasBinaryNat 0 := hready.rhs
  have hreplacement :
      (baseWork tapes.data.update.replacement).HasBinaryNat 0 :=
    hready.replacement
  have htmp : (baseWork tapes.data.tmp).HasBinaryNat 0 := hready.tmp
  have hdbl : (baseWork tapes.data.dbl).HasBinaryNat 0 := hready.dbl
  have hbuffer : (initialWork tapes.buffer).HasBinaryPrefix [] := by
    rw [hready.buffer]
    exact Tape.init_nil_move_right_hasBinaryPrefix_nil
  have hbaseRaw := directBinaryInstructionTM_hoareTime_frame tapes.data op store
    destination source₀ source₁ [] baseWork inp₀
    (initialWork tapes.buffer) hready.canonical hlookup hrhs hreplacement htmp
    hdbl hinput hbuffer
  let Result : (Fin n → Tape) → Prop := fun work =>
    DirectBinaryInstructionResult tapes.data op store destination source₀
      source₁ baseWork work
  have hbase : (directBinaryInstructionTM tapes.data op destination source₀
      source₁).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = baseWork ∧
        out = initialWork tapes.buffer)
      (fun inp work out =>
        inp = inp₀ ∧ Result work ∧
        out.HasBinaryPrefix
          ((instructionStore
            (directInstruction op destination source₀ source₁) pcValue store).flatMap
              Entry.encode))
      (directBinaryInstructionTime tapes.data op store destination source₀
        source₁) := by
    cases op <;>
      simpa [Result, directInstruction, instructionStore, Snapshot.stepInstr,
        BinaryInstrOp.eval] using! hbaseRaw
  have hresult : ∀ work, Result work →
      work tapes.pc = initialWork (Fin.castSucc tapes.pc) ∧
      (work tapes.data.update.resultCount).HasBinaryNat
        (instructionStore (directInstruction op destination source₀ source₁)
          pcValue store).length ∧
      (work tapes.data.update.entry.source).HasBinaryContent
        (store.flatMap Entry.encode) ∧
      (∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (instructionCleanupValue
            (directInstruction op destination source₀ source₁) store slot)) ∧
      (work tapes.data.update.remaining).HasBinaryNat
        (instructionRemainingValue
          (directInstruction op destination source₀ source₁) store) ∧
      EntryScanReady tapes.data.update.entry []
        (instructionCleanupValue
          (directInstruction op destination source₀ source₁) store 0).bits
        work work ∧
      (work tapes.data.shift).HasBinaryNat 0 ∧
      (work tapes.data.tmp).HasBinaryNat 0 ∧
      (work tapes.data.dbl).HasBinaryNat 0 ∧
      ∀ i, TM.Parked (work i) := by
    intro work hsemantic
    obtain ⟨updateWork, haddress, hbinary⟩ := hsemantic
    obtain ⟨operandsWork, hoperands, hupdateWork⟩ := haddress
    obtain ⟨lhsWork, hlhs, hrhsResult⟩ := hoperands
    obtain ⟨arithmeticWork, harithmetic, houtcome, hsourceCells⟩ := hbinary
    have hpcUpdate : work tapes.pc = arithmeticWork tapes.pc := by
      exact houtcome.frame tapes.pc (fun slot => by
        exact tapes.pc_ne ⟨slot, by omega⟩)
    have hpcArithmetic : arithmeticWork tapes.pc = updateWork tapes.pc := by
      exact harithmetic.frame tapes.pc (tapes.pc_ne 13) (tapes.pc_ne 14)
        (tapes.pc_ne 10) (tapes.pc_ne 15) (tapes.pc_ne 16)
        (tapes.pc_ne 17)
    have hpcQuery : tapes.pc ≠ tapes.data.update.entry.query := tapes.pc_ne 7
    have hpcAddress : updateWork tapes.pc = operandsWork tapes.pc := by
      rw [hupdateWork, Function.update_of_ne hpcQuery]
    have hpcRhs : operandsWork tapes.pc = lhsWork tapes.pc := by
      exact hrhsResult.frame tapes.pc (fun slot => by
        exact tapes.pc_ne (BinaryInstructionTapes.rhsLookupSlot slot))
    have hpcLhs : lhsWork tapes.pc = baseWork tapes.pc := by
      exact hlhs.frame tapes.pc (fun slot => by
        exact tapes.pc_ne (BinaryInstructionTapes.lhsLookupSlot slot))
    have hsourceContent :
        (work tapes.data.update.entry.source).HasBinaryContent
          (store.flatMap Entry.encode) := by
      have hcells : (work tapes.data.update.entry.source).cells =
          (baseWork tapes.data.update.entry.source).cells := by
        calc
          (work tapes.data.update.entry.source).cells =
              (updateWork tapes.data.update.entry.source).cells := hsourceCells
          _ = (operandsWork tapes.data.update.entry.source).cells := by
            rw [show updateWork tapes.data.update.entry.source =
                operandsWork tapes.data.update.entry.source by
              rw [hupdateWork]
              exact Function.update_of_ne
                (tapes.data.update.ne (by decide)) _ _]
          _ = (lhsWork tapes.data.update.entry.source).cells :=
            hrhsResult.sourceCells
          _ = (baseWork tapes.data.update.entry.source).cells :=
            hlhs.sourceCells
      unfold Tape.HasBinaryContent
      rw [hcells]
      exact hready.sourceContent
    have hcleanup : ∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (instructionCleanupValue
            (directInstruction op destination source₀ source₁) store slot) := by
      intro slot
      fin_cases slot
      · exact ⟨houtcome.ready.queryStart, by
          cases op <;>
            simpa [directInstruction, instructionCleanupValue,
              instructionCleanupParentSlot] using! houtcome.ready.query⟩
      · change (work tapes.data.update.replacement).HasBinaryNat _
        rw [show work tapes.data.update.replacement =
            arithmeticWork tapes.data.update.replacement from
          houtcome.replacement]
        cases op <;>
          simpa [directInstruction, instructionCleanupValue,
            BinaryInstrOp.eval] using! harithmetic.result
      · cases op <;>
          simpa [directInstruction, instructionCleanupValue,
            instructionCleanupParentSlot] using! houtcome.found
      · change (work tapes.data.lhs).HasBinaryNat _
        rw [houtcome.frame tapes.data.lhs (fun role =>
            (tapes.data.update_ne_lhs role).symm)]
        cases op <;>
          simpa [directInstruction, instructionCleanupValue,
            instructionCleanupParentSlot] using! harithmetic.lhsValue
      · change (work tapes.data.rhs).HasBinaryNat _
        rw [houtcome.frame tapes.data.rhs (fun role =>
            (tapes.data.update_ne_rhs role).symm)]
        cases op <;>
          simpa [directInstruction, instructionCleanupValue,
            instructionCleanupParentSlot] using! harithmetic.rhsValue
    have hshift : (work tapes.data.shift).HasBinaryNat 0 := by
      rw [houtcome.frame tapes.data.shift (fun slot =>
        (tapes.data.update_ne_shift slot).symm)]
      exact harithmetic.shift
    have htmp' : (work tapes.data.tmp).HasBinaryNat 0 := by
      rw [houtcome.frame tapes.data.tmp (fun slot =>
        (tapes.data.update_ne_tmp slot).symm)]
      exact harithmetic.tmp
    have hdbl' : (work tapes.data.dbl).HasBinaryNat 0 := by
      rw [houtcome.frame tapes.data.dbl (fun slot =>
        (tapes.data.update_ne_dbl slot).symm)]
      exact harithmetic.dbl
    refine ⟨hpcUpdate.trans (hpcArithmetic.trans
      (hpcAddress.trans (hpcRhs.trans hpcLhs))), ?_, hsourceContent,
      hcleanup, ?_, ?_, hshift, htmp', hdbl', houtcome.ready.parked⟩
    · cases op <;>
        simpa [directInstruction, instructionStore, Snapshot.stepInstr,
          BinaryInstrOp.eval] using! houtcome.resultCount
    · cases op <;>
        simpa [directInstruction, instructionRemainingValue] using!
          houtcome.remaining
    · cases op <;>
        simpa [directInstruction, instructionCleanupValue] using!
          houtcome.ready
  have hdata := retargetDataKernel_hoareTime_frame_internal tapes
    (directInstruction op destination source₀ source₁) store pcValue
    initialWork inp₀
    (directBinaryInstructionTM tapes.data op destination source₀ source₁)
    (directBinaryInstructionTime tapes.data op store destination source₀
      source₁) Result hready hbase hresult
  have hall := finishDataInstructionTM_hoareTime_frame_internal tapes
    (directInstruction op destination source₀ source₁) store pcValue
    initialWork inp₀
    (directBinaryInstructionTM tapes.data op destination source₀ source₁)
    (directBinaryInstructionTime tapes.data op store destination source₀
      source₁) (by cases op <;> rfl) hinput hdata
  cases op <;>
    simpa [directInstruction, executeInstructionTM, executeInstructionTime]
      using! hall

/-- Direct addition has the common one-buffer instruction contract. -/
theorem executeInstructionTM_add_hoareTime_frame
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue destination source₀ source₁ : ℕ)
    (initialWork : Fin (n + 1) → Tape) (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) :
    (executeInstructionTM tapes (.add destination source₀ source₁)).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes (.add destination source₀ source₁)
          pcValue store work ∧
        out = (Tape.init []).move Dir3.right)
      (executeInstructionTime tapes (.add destination source₀ source₁)
        pcValue store) := by
  simpa [directInstruction] using!
    executeInstructionTM_direct_hoareTime_frame tapes .add store pcValue
      destination source₀ source₁ initialWork inp₀ hready hinput

/-- Direct subtraction has the common one-buffer instruction contract. -/
theorem executeInstructionTM_sub_hoareTime_frame
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue destination source₀ source₁ : ℕ)
    (initialWork : Fin (n + 1) → Tape) (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) :
    (executeInstructionTM tapes (.sub destination source₀ source₁)).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes (.sub destination source₀ source₁)
          pcValue store work ∧
        out = (Tape.init []).move Dir3.right)
      (executeInstructionTime tapes (.sub destination source₀ source₁)
        pcValue store) := by
  simpa [directInstruction] using!
    executeInstructionTM_direct_hoareTime_frame tapes .sub store pcValue
      destination source₀ source₁ initialWork inp₀ hready hinput

/-- Direct multiplication has the common one-buffer instruction contract. -/
theorem executeInstructionTM_mul_hoareTime_frame
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue destination source₀ source₁ : ℕ)
    (initialWork : Fin (n + 1) → Tape) (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) :
    (executeInstructionTM tapes (.mul destination source₀ source₁)).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes (.mul destination source₀ source₁)
          pcValue store work ∧
        out = (Tape.init []).move Dir3.right)
      (executeInstructionTime tapes (.mul destination source₀ source₁)
        pcValue store) := by
  simpa [directInstruction] using!
    executeInstructionTM_direct_hoareTime_frame tapes .mul store pcValue
      destination source₀ source₁ initialWork inp₀ hready hinput

/-- Indirect-load execution redirects its next sparse store and increments
the program counter. -/
theorem executeInstructionTM_load_hoareTime_frame
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue destination addressRegister : ℕ)
    (initialWork : Fin (n + 1) → Tape) (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) :
    (executeInstructionTM tapes (.load destination addressRegister)).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes (.load destination addressRegister)
          pcValue store work ∧
        out = (Tape.init []).move Dir3.right)
      (executeInstructionTime tapes (.load destination addressRegister)
        pcValue store) := by
  let baseWork : Fin n → Tape := fun i => initialWork (Fin.castSucc i)
  have hlookup : EntryLookupStaticReady tapes.data.lhsLookup store baseWork :=
    instructionExecutionReady_baseLookup_internal tapes store pcValue
      initialWork hready
  have hreplacement :
      (baseWork tapes.data.update.replacement).HasBinaryNat 0 :=
    hready.replacement
  have hbuffer : (initialWork tapes.buffer).HasBinaryPrefix [] := by
    rw [hready.buffer]
    exact Tape.init_nil_move_right_hasBinaryPrefix_nil
  have hbaseRaw := indirectLoadInstructionTM_hoareTime_frame tapes.data store
    destination addressRegister [] baseWork inp₀ (initialWork tapes.buffer)
    hready.canonical hlookup hreplacement hinput hbuffer
  let instruction : Instr := .load destination addressRegister
  let Result : (Fin n → Tape) → Prop := fun work =>
    IndirectLoadInstructionResult tapes.data store destination addressRegister
      baseWork work
  have hbase : (indirectLoadInstructionTM tapes.data destination
      addressRegister).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = baseWork ∧
        out = initialWork tapes.buffer)
      (fun inp work out =>
        inp = inp₀ ∧ Result work ∧
        out.HasBinaryPrefix
          ((instructionStore instruction pcValue store).flatMap Entry.encode))
      (indirectLoadInstructionTime tapes.data store destination
        addressRegister) := by
    simpa [Result, instruction, instructionStore, Snapshot.stepInstr] using!
      hbaseRaw
  have hresult : ∀ work, Result work →
      work tapes.pc = initialWork (Fin.castSucc tapes.pc) ∧
      (work tapes.data.update.resultCount).HasBinaryNat
        (instructionStore instruction pcValue store).length ∧
      (work tapes.data.update.entry.source).HasBinaryContent
        (store.flatMap Entry.encode) ∧
      (∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (instructionCleanupValue instruction store slot)) ∧
      (work tapes.data.update.remaining).HasBinaryNat
        (instructionRemainingValue instruction store) ∧
      EntryScanReady tapes.data.update.entry []
        (instructionCleanupValue instruction store 0).bits work work ∧
      (work tapes.data.shift).HasBinaryNat 0 ∧
      (work tapes.data.tmp).HasBinaryNat 0 ∧
      (work tapes.data.dbl).HasBinaryNat 0 ∧
      ∀ i, TM.Parked (work i) := by
    intro work hsemantic
    obtain ⟨addressWork, loadedWork, updateWork, haddress, hloaded,
      hupdateWork, houtcome, hsourceCells⟩ := hsemantic
    have hpcOutcome : work tapes.pc = updateWork tapes.pc := by
      exact houtcome.frame tapes.pc (fun slot => by
        exact tapes.pc_ne ⟨slot, by omega⟩)
    have hpcQuery : tapes.pc ≠ tapes.data.update.entry.query := tapes.pc_ne 7
    have hpcUpdate : updateWork tapes.pc = loadedWork tapes.pc := by
      rw [hupdateWork, Function.update_of_ne hpcQuery]
    have hpcLoaded : loadedWork tapes.pc = addressWork tapes.pc := by
      exact hloaded.frame tapes.pc (fun slot => by
        exact tapes.pc_ne
          (BinaryInstructionTapes.indirectLoadLookupSlot slot))
    have hpcAddress : addressWork tapes.pc = baseWork tapes.pc := by
      exact haddress.frame tapes.pc (fun slot => by
        exact tapes.pc_ne (BinaryInstructionTapes.lhsLookupSlot slot))
    have hsourceContent :
        (work tapes.data.update.entry.source).HasBinaryContent
          (store.flatMap Entry.encode) := by
      unfold Tape.HasBinaryContent
      rw [hsourceCells]
      exact hready.sourceContent
    have hcleanup : ∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (instructionCleanupValue instruction store slot) := by
      intro slot
      fin_cases slot
      · exact ⟨houtcome.ready.queryStart, by
          simpa [instruction, instructionCleanupValue,
            instructionCleanupParentSlot] using! houtcome.ready.query⟩
      · change (work tapes.data.update.replacement).HasBinaryNat _
        rw [show work tapes.data.update.replacement =
            updateWork tapes.data.update.replacement from houtcome.replacement,
          show updateWork tapes.data.update.replacement =
              loadedWork tapes.data.update.replacement by
            rw [hupdateWork]
            exact Function.update_of_ne
              (tapes.data.update.ne (by decide)) _ _]
        exact hloaded.value
      · simpa [instruction, instructionCleanupValue,
          instructionCleanupParentSlot] using! houtcome.found
      · change (work tapes.data.lhs).HasBinaryNat _
        rw [show work tapes.data.lhs = updateWork tapes.data.lhs from
            houtcome.frame tapes.data.lhs (fun role =>
              (tapes.data.update_ne_lhs role).symm),
          show updateWork tapes.data.lhs = loadedWork tapes.data.lhs by
            rw [hupdateWork]
            exact Function.update_of_ne
              (tapes.data.update_ne_lhs 7).symm _ _]
        rw [show loadedWork tapes.data.lhs = addressWork tapes.data.lhs from
          hloaded.querySource]
        simpa [instruction, instructionCleanupValue] using! haddress.destination
      · change (work tapes.data.rhs).HasBinaryNat _
        rw [show work tapes.data.rhs = updateWork tapes.data.rhs from
            houtcome.frame tapes.data.rhs (fun role =>
              (tapes.data.update_ne_rhs role).symm),
          show updateWork tapes.data.rhs = loadedWork tapes.data.rhs by
            rw [hupdateWork]
            exact Function.update_of_ne
              (tapes.data.update_ne_rhs 7).symm _ _,
          hloaded.frame tapes.data.rhs (fun role => by
              apply tapes.data.ne
              fin_cases role <;> decide),
          haddress.frame tapes.data.rhs (fun role =>
              (tapes.data.lhsLookup_ne_rhs role).symm)]
        exact hready.rhs
    have hshift : (work tapes.data.shift).HasBinaryNat 0 := by
      have hqueryNe : tapes.data.shift ≠
          tapes.data.update.entry.query :=
        (tapes.data.update_ne_shift 7).symm
      rw [houtcome.frame tapes.data.shift (fun slot =>
            (tapes.data.update_ne_shift slot).symm),
        hupdateWork, Function.update_of_ne hqueryNe,
        hloaded.frame tapes.data.shift (fun slot => by
          apply tapes.data.ne
          fin_cases slot <;> decide)]
      simpa using! haddress.querySource
    have htmp' : (work tapes.data.tmp).HasBinaryNat 0 := by
      have hqueryNe : tapes.data.tmp ≠
          tapes.data.update.entry.query :=
        (tapes.data.update_ne_tmp 7).symm
      rw [houtcome.frame tapes.data.tmp (fun slot =>
            (tapes.data.update_ne_tmp slot).symm),
        hupdateWork, Function.update_of_ne hqueryNe,
        hloaded.frame tapes.data.tmp (fun slot => by
          apply tapes.data.ne
          fin_cases slot <;> decide),
        haddress.frame tapes.data.tmp (fun slot =>
          (tapes.data.lhsLookup_ne_tmp slot).symm)]
      exact hready.tmp
    have hdbl' : (work tapes.data.dbl).HasBinaryNat 0 := by
      have hqueryNe : tapes.data.dbl ≠
          tapes.data.update.entry.query :=
        (tapes.data.update_ne_dbl 7).symm
      rw [houtcome.frame tapes.data.dbl (fun slot =>
            (tapes.data.update_ne_dbl slot).symm),
        hupdateWork, Function.update_of_ne hqueryNe,
        hloaded.frame tapes.data.dbl (fun slot => by
          apply tapes.data.ne
          fin_cases slot <;> decide),
        haddress.frame tapes.data.dbl (fun slot =>
          (tapes.data.lhsLookup_ne_dbl slot).symm)]
      exact hready.dbl
    refine ⟨hpcOutcome.trans (hpcUpdate.trans
      (hpcLoaded.trans hpcAddress)), ?_, hsourceContent, hcleanup,
      ?_, ?_, hshift, htmp', hdbl', houtcome.ready.parked⟩
    · simpa [instruction, instructionStore, Snapshot.stepInstr] using!
        houtcome.resultCount
    · simpa [instruction, instructionRemainingValue] using!
        houtcome.remaining
    · simpa [instruction, instructionCleanupValue] using! houtcome.ready
  have hdata := retargetDataKernel_hoareTime_frame_internal tapes instruction
    store pcValue initialWork inp₀
    (indirectLoadInstructionTM tapes.data destination addressRegister)
    (indirectLoadInstructionTime tapes.data store destination addressRegister)
    Result hready hbase hresult
  simpa only [instruction, executeInstructionTM, executeInstructionTime] using!
    finishDataInstructionTM_hoareTime_frame_internal tapes instruction store
      pcValue initialWork inp₀
      (indirectLoadInstructionTM tapes.data destination addressRegister)
      (indirectLoadInstructionTime tapes.data store destination addressRegister)
      rfl hinput hdata

/-- Indirect-store execution redirects its next sparse store and increments
the program counter. -/
theorem executeInstructionTM_store_hoareTime_frame
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue addressRegister source : ℕ)
    (initialWork : Fin (n + 1) → Tape) (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) :
    (executeInstructionTM tapes (.store addressRegister source)).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes (.store addressRegister source)
          pcValue store work ∧
        out = (Tape.init []).move Dir3.right)
      (executeInstructionTime tapes (.store addressRegister source)
        pcValue store) := by
  let baseWork : Fin n → Tape := fun i => initialWork (Fin.castSucc i)
  have hlookup : EntryLookupStaticReady tapes.data.lhsLookup store baseWork :=
    instructionExecutionReady_baseLookup_internal tapes store pcValue
      initialWork hready
  have hrhs : (baseWork tapes.data.rhs).HasBinaryNat 0 := hready.rhs
  have hreplacement :
      (baseWork tapes.data.update.replacement).HasBinaryNat 0 :=
    hready.replacement
  have hbuffer : (initialWork tapes.buffer).HasBinaryPrefix [] := by
    rw [hready.buffer]
    exact Tape.init_nil_move_right_hasBinaryPrefix_nil
  have hbaseRaw := indirectStoreInstructionTM_hoareTime_frame tapes.data store
    addressRegister source [] baseWork inp₀ (initialWork tapes.buffer)
    hready.canonical hlookup hrhs hreplacement hinput hbuffer
  let instruction : Instr := .store addressRegister source
  let Result : (Fin n → Tape) → Prop := fun work =>
    IndirectStoreInstructionResult tapes.data store addressRegister source
      baseWork work
  have hbase : (indirectStoreInstructionTM tapes.data addressRegister
      source).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = baseWork ∧
        out = initialWork tapes.buffer)
      (fun inp work out =>
        inp = inp₀ ∧ Result work ∧
        out.HasBinaryPrefix
          ((instructionStore instruction pcValue store).flatMap Entry.encode))
      (indirectStoreInstructionTime tapes.data store addressRegister source) := by
    simpa [Result, instruction, instructionStore, Snapshot.stepInstr] using!
      hbaseRaw
  have hresult : ∀ work, Result work →
      work tapes.pc = initialWork (Fin.castSucc tapes.pc) ∧
      (work tapes.data.update.resultCount).HasBinaryNat
        (instructionStore instruction pcValue store).length ∧
      (work tapes.data.update.entry.source).HasBinaryContent
        (store.flatMap Entry.encode) ∧
      (∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (instructionCleanupValue instruction store slot)) ∧
      (work tapes.data.update.remaining).HasBinaryNat
        (instructionRemainingValue instruction store) ∧
      EntryScanReady tapes.data.update.entry []
        (instructionCleanupValue instruction store 0).bits work work ∧
      (work tapes.data.shift).HasBinaryNat 0 ∧
      (work tapes.data.tmp).HasBinaryNat 0 ∧
      (work tapes.data.dbl).HasBinaryNat 0 ∧
      ∀ i, TM.Parked (work i) := by
    intro work hsemantic
    obtain ⟨operandsWork, queryWork, updateWork, hoperands, hqueryWork,
      hupdateWork, houtcome, hsourceCells⟩ := hsemantic
    obtain ⟨lhsWork, hlhs, hrhsResult⟩ := hoperands
    have hpcOutcome : work tapes.pc = updateWork tapes.pc := by
      exact houtcome.frame tapes.pc (fun slot => by
        exact tapes.pc_ne ⟨slot, by omega⟩)
    have hpcReplacement :
        tapes.pc ≠ tapes.data.update.replacement := tapes.pc_ne 10
    have hpcUpdate : updateWork tapes.pc = queryWork tapes.pc := by
      rw [hupdateWork, Function.update_of_ne hpcReplacement]
    have hpcQuery : tapes.pc ≠ tapes.data.update.entry.query := tapes.pc_ne 7
    have hpcQueryWork : queryWork tapes.pc = operandsWork tapes.pc := by
      rw [hqueryWork, Function.update_of_ne hpcQuery]
    have hpcRhs : operandsWork tapes.pc = lhsWork tapes.pc := by
      exact hrhsResult.frame tapes.pc (fun slot => by
        exact tapes.pc_ne (BinaryInstructionTapes.rhsLookupSlot slot))
    have hpcLhs : lhsWork tapes.pc = baseWork tapes.pc := by
      exact hlhs.frame tapes.pc (fun slot => by
        exact tapes.pc_ne (BinaryInstructionTapes.lhsLookupSlot slot))
    have hsourceContent :
        (work tapes.data.update.entry.source).HasBinaryContent
          (store.flatMap Entry.encode) := by
      unfold Tape.HasBinaryContent
      rw [hsourceCells]
      exact hready.sourceContent
    have hcleanup : ∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (instructionCleanupValue instruction store slot) := by
      intro slot
      fin_cases slot
      · exact ⟨houtcome.ready.queryStart, by
          simpa [instruction, instructionCleanupValue,
            instructionCleanupParentSlot] using! houtcome.ready.query⟩
      · change (work tapes.data.update.replacement).HasBinaryNat _
        rw [show work tapes.data.update.replacement =
            updateWork tapes.data.update.replacement from houtcome.replacement,
          hupdateWork, Function.update_self]
        exact Tape.init_move_right_hasBinaryNat
          (RegisterStore.read store source)
      · simpa [instruction, instructionCleanupValue,
          instructionCleanupParentSlot] using! houtcome.found
      · change (work tapes.data.lhs).HasBinaryNat _
        rw [show work tapes.data.lhs = updateWork tapes.data.lhs from
            houtcome.frame tapes.data.lhs (fun role =>
              (tapes.data.update_ne_lhs role).symm),
          show updateWork tapes.data.lhs = queryWork tapes.data.lhs by
            rw [hupdateWork]
            exact Function.update_of_ne
              (tapes.data.update_ne_lhs 10).symm _ _,
          show queryWork tapes.data.lhs = operandsWork tapes.data.lhs by
            rw [hqueryWork]
            exact Function.update_of_ne
              (tapes.data.update_ne_lhs 7).symm _ _,
          hrhsResult.frame tapes.data.lhs (fun role =>
              (tapes.data.rhsLookup_ne_lhs role).symm)]
        exact hlhs.destination
      · change (work tapes.data.rhs).HasBinaryNat _
        rw [show work tapes.data.rhs = updateWork tapes.data.rhs from
            houtcome.frame tapes.data.rhs (fun role =>
              (tapes.data.update_ne_rhs role).symm),
          show updateWork tapes.data.rhs = queryWork tapes.data.rhs by
            rw [hupdateWork]
            exact Function.update_of_ne
              (tapes.data.update_ne_rhs 10).symm _ _,
          show queryWork tapes.data.rhs = operandsWork tapes.data.rhs by
            rw [hqueryWork]
            exact Function.update_of_ne
              (tapes.data.update_ne_rhs 7).symm _ _]
        exact hrhsResult.destination
    have hshift : (work tapes.data.shift).HasBinaryNat 0 := by
      have hreplacementNe : tapes.data.shift ≠
          tapes.data.update.replacement :=
        (tapes.data.update_ne_shift 10).symm
      have hqueryNe : tapes.data.shift ≠
          tapes.data.update.entry.query :=
        (tapes.data.update_ne_shift 7).symm
      rw [houtcome.frame tapes.data.shift (fun slot =>
            (tapes.data.update_ne_shift slot).symm),
        hupdateWork, Function.update_of_ne hreplacementNe,
        hqueryWork, Function.update_of_ne hqueryNe]
      simpa using! hrhsResult.querySource
    have htmp' : (work tapes.data.tmp).HasBinaryNat 0 := by
      have hreplacementNe : tapes.data.tmp ≠
          tapes.data.update.replacement :=
        (tapes.data.update_ne_tmp 10).symm
      have hqueryNe : tapes.data.tmp ≠
          tapes.data.update.entry.query :=
        (tapes.data.update_ne_tmp 7).symm
      rw [houtcome.frame tapes.data.tmp (fun slot =>
            (tapes.data.update_ne_tmp slot).symm),
        hupdateWork, Function.update_of_ne hreplacementNe,
        hqueryWork, Function.update_of_ne hqueryNe,
        hrhsResult.frame tapes.data.tmp (fun slot =>
          (tapes.data.rhsLookup_ne_tmp slot).symm),
        hlhs.frame tapes.data.tmp (fun slot =>
          (tapes.data.lhsLookup_ne_tmp slot).symm)]
      exact hready.tmp
    have hdbl' : (work tapes.data.dbl).HasBinaryNat 0 := by
      have hreplacementNe : tapes.data.dbl ≠
          tapes.data.update.replacement :=
        (tapes.data.update_ne_dbl 10).symm
      have hqueryNe : tapes.data.dbl ≠
          tapes.data.update.entry.query :=
        (tapes.data.update_ne_dbl 7).symm
      rw [houtcome.frame tapes.data.dbl (fun slot =>
            (tapes.data.update_ne_dbl slot).symm),
        hupdateWork, Function.update_of_ne hreplacementNe,
        hqueryWork, Function.update_of_ne hqueryNe,
        hrhsResult.frame tapes.data.dbl (fun slot =>
          (tapes.data.rhsLookup_ne_dbl slot).symm),
        hlhs.frame tapes.data.dbl (fun slot =>
          (tapes.data.lhsLookup_ne_dbl slot).symm)]
      exact hready.dbl
    refine ⟨hpcOutcome.trans (hpcUpdate.trans
      (hpcQueryWork.trans (hpcRhs.trans hpcLhs))), ?_, hsourceContent,
      hcleanup, ?_, ?_, hshift, htmp', hdbl', houtcome.ready.parked⟩
    · simpa [instruction, instructionStore, Snapshot.stepInstr] using!
        houtcome.resultCount
    · simpa [instruction, instructionRemainingValue] using!
        houtcome.remaining
    · simpa [instruction, instructionCleanupValue] using! houtcome.ready
  have hdata := retargetDataKernel_hoareTime_frame_internal tapes instruction
    store pcValue initialWork inp₀
    (indirectStoreInstructionTM tapes.data addressRegister source)
    (indirectStoreInstructionTime tapes.data store addressRegister source)
    Result hready hbase hresult
  simpa only [instruction, executeInstructionTM, executeInstructionTime] using!
    finishDataInstructionTM_hoareTime_frame_internal tapes instruction store
      pcValue initialWork inp₀
      (indirectStoreInstructionTM tapes.data addressRegister source)
      (indirectStoreInstructionTime tapes.data store addressRegister source)
      rfl hinput hdata

end Machine

end RegisterStore

end RAM

end Complexity
