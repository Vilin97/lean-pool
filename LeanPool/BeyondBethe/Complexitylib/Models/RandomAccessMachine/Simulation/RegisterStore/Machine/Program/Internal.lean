/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Dispatch
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Loop

/-!
# Sparse RAM program controller -- proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem blank_parked :
    TM.Parked ((Tape.init []).move Dir3.right) := by
  refine ⟨by simp [Tape.move], ?_⟩
  intro j hj
  simp [Tape.move, Tape.init, show j ≠ 0 by omega]

private theorem hasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t := by
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem programBinaryTape_hasBinaryString (bits : List Bool) :
    (programBinaryTape bits).HasBinaryString bits := by
  simpa only [programBinaryTape] using!
    Tape.init_move_right_hasBinaryString bits

private theorem programBinaryTape_hasBinaryNat (value : ℕ) :
    (programBinaryTape value.bits).HasBinaryNat value := by
  simpa only [programBinaryTape] using!
    Tape.init_move_right_hasBinaryNat value

private theorem programBinaryTape_parked (bits : List Bool) :
    TM.Parked (programBinaryTape bits) := by
  refine ⟨by rw [(programBinaryTape_hasBinaryString bits).1], ?_⟩
  exact (programBinaryTape_hasBinaryString bits).hasBinaryContent.cells_ne_start

private theorem programSnapshotWork_source
    (tapes : ControlInstructionTapes n) (snapshot : Snapshot) :
    programSnapshotWork tapes snapshot tapes.liftedSource =
      programBinaryTape (snapshot.store.flatMap Entry.encode) := by
  have hsourceRemaining : tapes.liftedSource ≠
      tapes.lifted.data.update.remaining :=
    tapes.lifted.data.ne (by decide)
  have hsourceResult : tapes.liftedSource ≠
      tapes.lifted.data.update.resultCount :=
    tapes.lifted.data.ne (by decide)
  unfold programSnapshotWork
  rw [Function.update_of_ne tapes.liftedPC_ne_source.symm,
    Function.update_of_ne hsourceResult,
    Function.update_of_ne hsourceRemaining,
    Function.update_self]

private theorem programSnapshotWork_remaining
    (tapes : ControlInstructionTapes n) (snapshot : Snapshot) :
    programSnapshotWork tapes snapshot
        tapes.lifted.data.update.remaining =
      programBinaryTape snapshot.store.length.bits := by
  have hremainingSource : tapes.lifted.data.update.remaining ≠
      tapes.liftedSource := tapes.lifted.data.ne (by decide)
  have hremainingResult : tapes.lifted.data.update.remaining ≠
      tapes.lifted.data.update.resultCount :=
    tapes.lifted.data.ne (by decide)
  have hremainingPC : tapes.lifted.data.update.remaining ≠
      tapes.liftedPC := tapes.lifted.data_ne_pc 9
  unfold programSnapshotWork
  rw [Function.update_of_ne hremainingPC,
    Function.update_of_ne hremainingResult,
    Function.update_self]

private theorem programSnapshotWork_resultCount
    (tapes : ControlInstructionTapes n) (snapshot : Snapshot) :
    programSnapshotWork tapes snapshot
        tapes.lifted.data.update.resultCount =
      programBinaryTape snapshot.store.length.bits := by
  have hresultPC : tapes.lifted.data.update.resultCount ≠
      tapes.liftedPC := tapes.lifted.data_ne_pc 12
  unfold programSnapshotWork
  rw [Function.update_of_ne hresultPC, Function.update_self]

private theorem programSnapshotWork_pc
    (tapes : ControlInstructionTapes n) (snapshot : Snapshot) :
    programSnapshotWork tapes snapshot tapes.liftedPC =
      programBinaryTape snapshot.pc.bits := by
  simp [programSnapshotWork]

private theorem programSnapshotWork_other
    (tapes : ControlInstructionTapes n) (snapshot : Snapshot)
    (i : Fin (n + 1))
    (hsource : i ≠ tapes.liftedSource)
    (hremaining : i ≠ tapes.lifted.data.update.remaining)
    (hresult : i ≠ tapes.lifted.data.update.resultCount)
    (hpc : i ≠ tapes.liftedPC) :
    programSnapshotWork tapes snapshot i = TM.resetBinaryBlank := by
  unfold programSnapshotWork
  rw [Function.update_of_ne hpc,
    Function.update_of_ne hresult,
    Function.update_of_ne hremaining,
    Function.update_of_ne hsource]
  rfl

/-- The snapshot's source and blank scratch slots initialize the entry scanner. -/
private theorem programSnapshotWork_scanner
    (tapes : ControlInstructionTapes n) (snapshot : Snapshot)
    (work : Fin (n + 1) → Tape)
    (hsource : work tapes.liftedSource =
      programBinaryTape (snapshot.store.flatMap Entry.encode))
    (hdataBlank : ∀ (slot : Fin 18), slot ≠ 0 → slot ≠ 9 → slot ≠ 12 →
      work (tapes.lifted.data.idx slot) = TM.resetBinaryBlank)
    (hparked : ∀ i, TM.Parked (work i)) :
    EntryScanReady tapes.lifted.data.lhsLookup.scan.entry
      (snapshot.store.flatMap Entry.encode) [] work work := by
  let entry := tapes.lifted.data.lhsLookup.scan.entry
  have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
    simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
  have hblankString : TM.resetBinaryBlank.HasBinaryString [] := hblankNat.2
  have hblankPrefix : TM.resetBinaryBlank.HasBinaryPrefix [] :=
    ⟨by simpa using! hblankString.1, hblankString.2⟩
  have hblankStart : TM.resetBinaryBlank.cells 0 = Γ.start := hblankNat.1
  have hslotOther (slot : Fin 9) (hslot : slot ≠ 0) :
      work (entry.idx slot) = TM.resetBinaryBlank := by
    fin_cases slot
    · exact (hslot rfl).elim
    · simpa [entry, BinaryInstructionTapes.lhsLookup,
        BinaryInstructionTapes.lhsLookupSlot] using!
        hdataBlank 1 (by decide) (by decide) (by decide)
    · simpa [entry, BinaryInstructionTapes.lhsLookup,
        BinaryInstructionTapes.lhsLookupSlot] using!
        hdataBlank 2 (by decide) (by decide) (by decide)
    · simpa [entry, BinaryInstructionTapes.lhsLookup,
        BinaryInstructionTapes.lhsLookupSlot] using!
        hdataBlank 3 (by decide) (by decide) (by decide)
    · simpa [entry, BinaryInstructionTapes.lhsLookup,
        BinaryInstructionTapes.lhsLookupSlot] using!
        hdataBlank 4 (by decide) (by decide) (by decide)
    · simpa [entry, BinaryInstructionTapes.lhsLookup,
        BinaryInstructionTapes.lhsLookupSlot] using!
        hdataBlank 5 (by decide) (by decide) (by decide)
    · simpa [entry, BinaryInstructionTapes.lhsLookup,
        BinaryInstructionTapes.lhsLookupSlot] using!
        hdataBlank 6 (by decide) (by decide) (by decide)
    · simpa [entry, BinaryInstructionTapes.lhsLookup,
        BinaryInstructionTapes.lhsLookupSlot] using!
        hdataBlank 7 (by decide) (by decide) (by decide)
    · simpa [entry, BinaryInstructionTapes.lhsLookup,
        BinaryInstructionTapes.lhsLookupSlot] using!
        hdataBlank 8 (by decide) (by decide) (by decide)
  refine
    { source := by
        change (work tapes.liftedSource).HasBinarySuffix _
        rw [hsource]
        exact Tape.init_move_right_hasBinarySuffix _
      address := by
        rw [show work entry.address = TM.resetBinaryBlank by
          simpa only [EntryMatchTapes.address] using!
            hslotOther 1 (by decide)]
        exact hblankPrefix
      addressStart := by
        rw [show work entry.address = TM.resetBinaryBlank by
          simpa only [EntryMatchTapes.address] using!
            hslotOther 1 (by decide)]
        exact hblankStart
      value := by
        rw [show work entry.value = TM.resetBinaryBlank by
          simpa only [EntryMatchTapes.value] using!
            hslotOther 2 (by decide)]
        exact hblankPrefix
      valueStart := by
        rw [show work entry.value = TM.resetBinaryBlank by
          simpa only [EntryMatchTapes.value] using!
            hslotOther 2 (by decide)]
        exact hblankStart
      addressCounter := by
        rw [show work entry.addressCounter = TM.resetBinaryBlank by
          simpa only [EntryMatchTapes.addressCounter] using!
            hslotOther 3 (by decide)]
        exact hblankNat
      addressWidth := by
        rw [show work entry.addressWidth = TM.resetBinaryBlank by
          simpa only [EntryMatchTapes.addressWidth] using!
            hslotOther 4 (by decide)]
        exact hblankNat
      valueCounter := by
        rw [show work entry.valueCounter = TM.resetBinaryBlank by
          simpa only [EntryMatchTapes.valueCounter] using!
            hslotOther 5 (by decide)]
        exact hblankNat
      valueWidth := by
        rw [show work entry.valueWidth = TM.resetBinaryBlank by
          simpa only [EntryMatchTapes.valueWidth] using!
            hslotOther 6 (by decide)]
        exact hblankNat
      query := by
        rw [show work entry.query = TM.resetBinaryBlank by
          simpa only [EntryMatchTapes.query] using!
            hslotOther 7 (by decide)]
        exact hblankString
      queryStart := by
        rw [show work entry.query = TM.resetBinaryBlank by
          simpa only [EntryMatchTapes.query] using!
            hslotOther 7 (by decide)]
        exact hblankStart
      result := by
        rw [show work entry.result = TM.resetBinaryBlank by
          simpa only [EntryMatchTapes.result] using!
            hslotOther 8 (by decide)]
        exact hblankPrefix
      resultStart := by
        rw [show work entry.result = TM.resetBinaryBlank by
          simpa only [EntryMatchTapes.result] using!
            hslotOther 8 (by decide)]
        exact hblankStart
      parked := hparked
      frame := by intros; rfl }

/-- The exact snapshot work image satisfies the complete reusable instruction
ABI whenever its sparse store is canonical. -/
theorem programSnapshotWork_ready_internal
    (tapes : ControlInstructionTapes n) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    InstructionExecutionReady tapes snapshot.store snapshot.pc
      (programSnapshotWork tapes snapshot) := by
  let work := programSnapshotWork tapes snapshot
  let entry := tapes.lifted.data.lhsLookup.scan.entry
  change InstructionExecutionReady tapes snapshot.store snapshot.pc work
  have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
    simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
  have hsource : work tapes.liftedSource =
      programBinaryTape (snapshot.store.flatMap Entry.encode) := by
    exact programSnapshotWork_source tapes snapshot
  have hremaining : work tapes.lifted.data.update.remaining =
      programBinaryTape snapshot.store.length.bits := by
    exact programSnapshotWork_remaining tapes snapshot
  have hresultCount : work tapes.lifted.data.update.resultCount =
      programBinaryTape snapshot.store.length.bits := by
    exact programSnapshotWork_resultCount tapes snapshot
  have hpc : work tapes.liftedPC = programBinaryTape snapshot.pc.bits := by
    exact programSnapshotWork_pc tapes snapshot
  have hother (i : Fin (n + 1))
      (hsourceIdx : i ≠ tapes.liftedSource)
      (hremainingIdx : i ≠ tapes.lifted.data.update.remaining)
      (hresultIdx : i ≠ tapes.lifted.data.update.resultCount)
      (hpcIdx : i ≠ tapes.liftedPC) :
      work i = TM.resetBinaryBlank := by
    exact programSnapshotWork_other tapes snapshot i hsourceIdx
      hremainingIdx hresultIdx hpcIdx
  have hdataBlank (slot : Fin 18) (hsourceSlot : slot ≠ 0)
      (hremainingSlot : slot ≠ 9) (hresultSlot : slot ≠ 12) :
      work (tapes.lifted.data.idx slot) = TM.resetBinaryBlank := by
    exact hother _ (tapes.lifted.data.ne hsourceSlot)
      (tapes.lifted.data.ne hremainingSlot)
      (tapes.lifted.data.ne hresultSlot)
      (tapes.lifted.data_ne_pc slot)
  have hparked : ∀ i, TM.Parked (work i) := by
    intro i
    by_cases hsi : i = tapes.liftedSource
    · subst i
      rw [hsource]
      exact programBinaryTape_parked _
    by_cases hri : i = tapes.lifted.data.update.remaining
    · subst i
      rw [hremaining]
      exact programBinaryTape_parked _
    by_cases hci : i = tapes.lifted.data.update.resultCount
    · subst i
      rw [hresultCount]
      exact programBinaryTape_parked _
    by_cases hpi : i = tapes.liftedPC
    · subst i
      rw [hpc]
      exact programBinaryTape_parked _
    · rw [hother i hsi hri hci hpi]
      exact blank_parked
  have hscanner : EntryScanReady entry
      (snapshot.store.flatMap Entry.encode) [] work work :=
    programSnapshotWork_scanner tapes snapshot work hsource hdataBlank hparked
  have hlookup : EntryLookupStaticReady tapes.lifted.data.lhsLookup
      snapshot.store work := by
    refine
      { scanner := by
          change EntryScanReady entry
            (snapshot.store.flatMap Entry.encode) [] work work
          exact hscanner
        sourceStart := by
          change (work tapes.liftedSource).cells 0 = Γ.start
          rw [hsource]
          simp [programBinaryTape, Tape.move, Tape.init]
        sourceHead := by
          change (work tapes.liftedSource).head = 1
          rw [hsource]
          exact (programBinaryTape_hasBinaryString _).1
        count := by
          change (work tapes.lifted.data.update.remaining).HasBinaryNat _
          rw [hremaining]
          exact programBinaryTape_hasBinaryNat _
        countSource := by
          change (work tapes.lifted.data.update.resultCount).HasBinaryNat _
          rw [hresultCount]
          exact programBinaryTape_hasBinaryNat _
        querySource := by
          change (work (tapes.lifted.data.idx 15)).HasBinaryNat 0
          rw [hdataBlank 15 (by decide) (by decide) (by decide)]
          exact hblankNat
        destination := by
          change (work (tapes.lifted.data.idx 13)).HasBinaryNat 0
          rw [hdataBlank 13 (by decide) (by decide) (by decide)]
          exact hblankNat
        copyScratch := by
          change (work (tapes.lifted.data.idx 11)).HasBinaryNat 0
          rw [hdataBlank 11 (by decide) (by decide) (by decide)]
          exact hblankNat }
  refine
    { canonical := hcanonical
      control :=
        { lookup := hlookup
          pc := by
            change (work tapes.liftedPC).HasBinaryNat snapshot.pc
            rw [hpc]
            exact programBinaryTape_hasBinaryNat _ }
      sourceContent := by
        rw [hsource]
        exact (programBinaryTape_hasBinaryString _).hasBinaryContent
      rhs := by
        change (work (tapes.lifted.data.idx 14)).HasBinaryNat 0
        rw [hdataBlank 14 (by decide) (by decide) (by decide)]
        exact hblankNat
      replacement := by
        change (work (tapes.lifted.data.idx 10)).HasBinaryNat 0
        rw [hdataBlank 10 (by decide) (by decide) (by decide)]
        exact hblankNat
      tmp := by
        change (work (tapes.lifted.data.idx 16)).HasBinaryNat 0
        rw [hdataBlank 16 (by decide) (by decide) (by decide)]
        exact hblankNat
      dbl := by
        change (work (tapes.lifted.data.idx 17)).HasBinaryNat 0
        rw [hdataBlank 17 (by decide) (by decide) (by decide)]
        exact hblankNat
      buffer := by
        rw [hother tapes.buffer tapes.liftedSource_ne_buffer.symm
          (tapes.liftedData_ne_buffer 9).symm
          (tapes.liftedData_ne_buffer 12).symm
          tapes.liftedPC_ne_buffer.symm]
        rfl }

theorem registerVerdictOutput_cell_one_internal (value : ℕ) :
    (registerVerdictOutput value).cells 1 =
      if value = 0 then Γ.zero else Γ.one := by
  by_cases hzero : value = 0 <;>
    simp [registerVerdictOutput, registerVerdictSymbol, hzero, TM.idleDir,
      Tape.writeAndMove, Tape.move, Tape.write, Tape.read, Tape.init]

theorem registerVerdictTM_hoareTime_frame_internal
    (idx : Fin n) (value : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (hvalue : (work₀ idx).HasBinaryNat value)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (work₀ i)) :
    (registerVerdictTM idx).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧
        out = registerVerdictOutput value)
      1 := by
  intro inp work out hpre
  obtain ⟨rfl, rfl, rfl⟩ := hpre
  have hinp := hinput.move_idle
  have hworkEq :
      (fun i => (work i).writeAndMove
        (TM.readBackWrite (work i).read)
        (TM.idleDir (work i).read)) = work := by
    funext i
    exact (hwork i).writeAndMove_readBack_idle
  have hsymbol :
      (if (work idx).read = Γ.blank then Γw.zero else Γw.one) =
        registerVerdictSymbol value := by
    rw [registerVerdictSymbol]
    exact if_congr hvalue.read_eq_blank_iff rfl rfl
  have hout :
      ((Tape.init []).move Dir3.right).writeAndMove
          (if (work idx).read = Γ.blank then Γw.zero else Γw.one).toΓ
          (TM.idleDir ((Tape.init []).move Dir3.right).read) =
        registerVerdictOutput value := by
    rw [hsymbol]
    rfl
  let final : Complexity.Cfg n (registerVerdictTM idx).Q :=
    { state := .done
      input := inp
      work := work
      output := registerVerdictOutput value }
  have hstep :
      (registerVerdictTM idx).step
        { state := (registerVerdictTM idx).qstart
          input := inp
          work := work
          output := (Tape.init []).move Dir3.right } = some final := by
    simp only [TM.step, registerVerdictTM, reduceCtorEq, ↓reduceIte, final]
    rw [hinp, hworkEq, hout]
  exact ⟨final, 1, le_rfl, .step hstep .zero, rfl, rfl, rfl, rfl⟩

/-- Final sparse lookup and Boolean emission recover the RAM verdict register. -/
theorem programOutputTM_hoareTime_internal
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
      (programOutputTime tapes store) := by
  let blank := (Tape.init []).move Dir3.right
  have hlookup := entryLookupStaticTM_hoareTime_frame
    tapes.lifted.data.lhsLookup store 0 initialWork inp₀ blank
    hready.control.lookup hinput blank_parked
  let mid : TM.TapePred (n + 1) := fun inp work out =>
    inp = inp₀ ∧
      EntryLookupStaticResult tapes.lifted.data.lhsLookup store 0
        initialWork work ∧
      out = blank
  have hverdict : (registerVerdictTM tapes.liftedLhs).HoareTime mid
      (fun inp _work out =>
        inp = inp₀ ∧
        out = registerVerdictOutput (RegisterStore.read store 0))
      1 := by
    rintro inp work out ⟨hinp, hresult, hout⟩
    have hleaf := registerVerdictTM_hoareTime_frame_internal
      tapes.liftedLhs (RegisterStore.read store 0) inp₀ work
      hresult.destination hinput hresult.parked
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        _hfinalWork, hfinalOutput⟩ :=
      hleaf inp work out ⟨hinp, rfl, by simpa only [blank] using! hout⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput, hfinalOutput⟩
  have hseq := TM.seqTM_hoareTime
    (entryLookupStaticTM tapes.lifted.data.lhsLookup 0)
    (registerVerdictTM tapes.liftedLhs) hlookup
    (by
      rintro inp work out ⟨hinp, hresult, hout⟩
      have hi : TM.transitionInput inp = inp :=
        TM.transitionInput_eq_self
          (by simpa [hinp] using! hinput.read_ne_start)
      have hw : (fun i => TM.transitionTape (work i)) = work := by
        funext i
        exact TM.transitionTape_eq_self (hresult.parked i).read_ne_start
      have ho : TM.transitionTape out = out :=
        TM.transitionTape_eq_self
          (by rw [hout]; exact blank_parked.read_ne_start)
      rw [hi, hw, ho]
      exact ⟨hinp, hresult, by simpa only [blank] using! hout⟩)
    hverdict
  simpa only [programOutputTM, programOutputTime, mid, blank] using! hseq

theorem registerVerdictTM_hoareTime_haltOutput_internal
    (idx : Fin n) (value : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (hvalue : (work₀ idx).HasBinaryNat value)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (work₀ i)) :
    (registerVerdictTM idx).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = instructionHaltOutput .halt)
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧
        out = registerVerdictOutput value)
      1 := by
  intro inp work out hpre
  obtain ⟨rfl, rfl, rfl⟩ := hpre
  have hinp := hinput.move_idle
  have hworkEq :
      (fun i => (work i).writeAndMove
        (TM.readBackWrite (work i).read)
        (TM.idleDir (work i).read)) = work := by
    funext i
    exact (hwork i).writeAndMove_readBack_idle
  have hsymbol :
      (if (work idx).read = Γ.blank then Γw.zero else Γw.one) =
        registerVerdictSymbol value := by
    rw [registerVerdictSymbol]
    exact if_congr hvalue.read_eq_blank_iff rfl rfl
  have hout :
      (instructionHaltOutput .halt).writeAndMove
          (if (work idx).read = Γ.blank then Γw.zero else Γw.one).toΓ
          (TM.idleDir (instructionHaltOutput .halt).read) =
        registerVerdictOutput value := by
    rw [hsymbol]
    simp [instructionHaltOutput, instructionHaltVerdict,
      registerVerdictOutput, TM.idleDir, Tape.writeAndMove, Tape.move,
      Tape.write, Tape.read, Tape.init]
  let final : Complexity.Cfg n (registerVerdictTM idx).Q :=
    { state := .done
      input := inp
      work := work
      output := registerVerdictOutput value }
  have hstep :
      (registerVerdictTM idx).step
        { state := (registerVerdictTM idx).qstart
          input := inp
          work := work
          output := instructionHaltOutput .halt } = some final := by
    simp only [TM.step, registerVerdictTM, reduceCtorEq, ↓reduceIte, final]
    rw [hinp, hworkEq, hout]
  exact ⟨final, 1, le_rfl, .step hstep .zero, rfl, rfl, rfl, rfl⟩

/-- Final sparse lookup overwrites the loop's halt-test bit with the RAM
verdict, so the controller and extractor compose without an output reset. -/
theorem programOutputTM_hoareTime_haltOutput_internal
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
      (programOutputTime tapes store) := by
  let haltOut := instructionHaltOutput .halt
  have hhaltOutParked : TM.Parked haltOut := by
    refine ⟨?_, ?_⟩
    · simp [haltOut, instructionHaltOutput, instructionHaltVerdict,
        TM.idleDir, Tape.writeAndMove, Tape.move, Tape.write, Tape.read,
        Tape.init]
    · intro j hj
      by_cases hjone : j = 1
      · subst j
        simp [haltOut, instructionHaltOutput, instructionHaltVerdict,
          TM.idleDir, Tape.writeAndMove, Tape.move, Tape.write, Tape.read,
          Tape.init]
      · have hjzero : j ≠ 0 := by omega
        simp [haltOut, instructionHaltOutput, instructionHaltVerdict,
          TM.idleDir, Tape.writeAndMove, Tape.move, Tape.write, Tape.read,
          Tape.init, Function.update, hjone, hjzero]
  have hlookup := entryLookupStaticTM_hoareTime_frame
    tapes.lifted.data.lhsLookup store 0 initialWork inp₀ haltOut
    hready.control.lookup hinput hhaltOutParked
  let mid : TM.TapePred (n + 1) := fun inp work out =>
    inp = inp₀ ∧
      EntryLookupStaticResult tapes.lifted.data.lhsLookup store 0
        initialWork work ∧
      out = haltOut
  have hverdict : (registerVerdictTM tapes.liftedLhs).HoareTime mid
      (fun inp _work out =>
        inp = inp₀ ∧
        out = registerVerdictOutput (RegisterStore.read store 0))
      1 := by
    rintro inp work out ⟨hinp, hresult, hout⟩
    have hleaf := registerVerdictTM_hoareTime_haltOutput_internal
      tapes.liftedLhs (RegisterStore.read store 0) inp₀ work
      hresult.destination hinput hresult.parked
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        _hfinalWork, hfinalOutput⟩ :=
      hleaf inp work out ⟨hinp, rfl, by simpa only [haltOut] using! hout⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput, hfinalOutput⟩
  have hseq := TM.seqTM_hoareTime
    (entryLookupStaticTM tapes.lifted.data.lhsLookup 0)
    (registerVerdictTM tapes.liftedLhs) hlookup
    (by
      rintro inp work out ⟨hinp, hresult, hout⟩
      have hi : TM.transitionInput inp = inp :=
        TM.transitionInput_eq_self
          (by simpa [hinp] using! hinput.read_ne_start)
      have hw : (fun i => TM.transitionTape (work i)) = work := by
        funext i
        exact TM.transitionTape_eq_self (hresult.parked i).read_ne_start
      have ho : TM.transitionTape out = out :=
        TM.transitionTape_eq_self
          (by rw [hout]; exact hhaltOutParked.read_ne_start)
      rw [hi, hw, ho]
      exact ⟨hinp, hresult, by simpa only [haltOut] using! hout⟩)
    hverdict
  simpa only [programOutputTM, programOutputTime, mid, haltOut] using! hseq

theorem instructionHaltOutput_head_internal (instruction : Instr) :
    (instructionHaltOutput instruction).head = 1 := by
  cases instruction <;>
    simp [instructionHaltOutput, instructionHaltVerdict, TM.idleDir,
      Tape.writeAndMove, Tape.move, Tape.write, Tape.read, Tape.init]

theorem instructionHaltOutput_cells_zero_internal (instruction : Instr) :
    (instructionHaltOutput instruction).cells 0 = Γ.start := by
  cases instruction <;>
    simp [instructionHaltOutput, instructionHaltVerdict, TM.idleDir,
      Tape.writeAndMove, Tape.move, Tape.write, Tape.read, Tape.init]

theorem instructionHaltOutput_cells_ne_start_internal
    (instruction : Instr) :
    ∀ j, j ≥ 1 → (instructionHaltOutput instruction).cells j ≠ Γ.start := by
  intro j hj
  by_cases h1 : j = 1
  · subst j
    cases instruction <;>
      simp [instructionHaltOutput, instructionHaltVerdict, TM.idleDir,
        Tape.writeAndMove, Tape.move, Tape.write, Tape.read, Tape.init]
  · cases instruction <;>
      simp [instructionHaltOutput, instructionHaltVerdict, TM.idleDir,
        Tape.writeAndMove, Tape.move, Tape.write, Tape.read, Tape.init, h1,
        show j ≠ 0 by omega]

theorem instructionHaltOutput_cell_one_eq_one_iff_internal
    (instruction : Instr) :
    (instructionHaltOutput instruction).cells 1 = Γ.one ↔
      instruction = .halt := by
  cases instruction <;>
    simp [instructionHaltOutput, instructionHaltVerdict, TM.idleDir,
      Tape.writeAndMove, Tape.move, Tape.write, Tape.read, Tape.init]

theorem instructionHaltOutput_eq_blank_of_ne_halt_internal
    {instruction : Instr} (h : instruction ≠ .halt) :
    instructionHaltOutput instruction =
      (Tape.init []).move Dir3.right := by
  cases instruction <;>
    simp_all [instructionHaltOutput, instructionHaltVerdict, TM.idleDir,
      Tape.writeAndMove, Tape.move, Tape.write, Tape.read, Tape.init]

private theorem phaseTransition_of_parked
    {inp out : Tape} {work : Fin n → Tape}
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    TM.transitionInput inp = inp ∧
      (fun i => TM.transitionTape (work i)) = work ∧
      TM.transitionTape out = out :=
  TM.phaseTransition_of_parked hinput hwork houtput

/-- The loop's fixed three-step rewind/check tail preserves every tape exactly. -/
theorem programLoop_rewind_check_internal (tmBody tmTest : TM n)
    (c : Complexity.Cfg n (TM.LoopQ tmBody.Q tmTest.Q))
    (hstate : c.state = Sum.inr (Sum.inl TM.LoopPhase.rewindOut))
    (hin : c.input.read ≠ Γ.start)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (hhead : c.output.head = 1)
    (hstart : c.output.cells 0 = Γ.start)
    (hnoStart : ∀ j, 1 ≤ j → c.output.cells j ≠ Γ.start) :
    ∃ c', (TM.loopTM tmBody tmTest).reachesIn 3 c c' ∧
      c'.state = (if c.output.cells 1 = Γ.one then
          (Sum.inr (Sum.inl TM.LoopPhase.done) :
            TM.LoopQ tmBody.Q tmTest.Q)
        else Sum.inl tmBody.qstart) ∧
      c'.input = c.input ∧ c'.work = c.work ∧ c'.output = c.output := by
  have hread₁ : c.output.read ≠ Γ.start := by
    rw [Tape.read, hhead]
    exact hnoStart 1 le_rfl
  obtain ⟨c₁, hstep₁, hstate₁, hinput₁, hwork₁, hhead₁, hcells₁⟩ :
      ∃ c₁, (TM.loopTM tmBody tmTest).step c = some c₁ ∧
        c₁.state = Sum.inr (Sum.inl TM.LoopPhase.rewindOut) ∧
        c₁.input = c.input ∧ c₁.work = c.work ∧
        c₁.output.head = 0 ∧ c₁.output.cells = c.output.cells := by
    simp only [TM.step, ↓reduceIte, hstate, TM.loopTM, hread₁]
    refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · exact TM.transitionInput_eq_self hin
    · exact funext fun i => TM.transitionTape_eq_self (hwork i)
    · simp [Tape.writeAndMove, Tape.move, Tape.write_head, hhead]
    · exact TM.tape_readBackWrite_preserves _ _ (Or.inr hread₁)
  have hread₂ : c₁.output.read = Γ.start := by
    rw [Tape.read, hhead₁, hcells₁]
    exact hstart
  obtain ⟨c₂, hstep₂, hstate₂, hinput₂, hwork₂, hhead₂, hcells₂⟩ :
      ∃ c₂, (TM.loopTM tmBody tmTest).step c₁ = some c₂ ∧
        c₂.state = Sum.inr (Sum.inl TM.LoopPhase.check) ∧
        c₂.input = c₁.input ∧ c₂.work = c₁.work ∧
        c₂.output.head = 1 ∧ c₂.output.cells = c₁.output.cells := by
    simp only [TM.step, ↓reduceIte, hstate₁, TM.loopTM, hread₂]
    refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · exact TM.transitionInput_eq_self (by rw [hinput₁]; exact hin)
    · refine funext fun i => TM.transitionTape_eq_self ?_
      rw [hwork₁]
      exact hwork i
    · simp [Tape.writeAndMove, Tape.move, Tape.write_head, hhead₁]
    · show ((c₁.output.write (Γw.blank).toΓ).move Dir3.right).cells =
        c₁.output.cells
      rw [Tape.move_cells]
      simp only [Tape.write, hhead₁, ↓reduceIte]
  have houtput₂ : c₂.output = c.output :=
    Tape.ext (by rw [hhead₂, hhead])
      (by rw [hcells₂, hcells₁])
  by_cases hone : c.output.cells 1 = Γ.one
  · have hread₃ : c₂.output.read = Γ.one := by
      rw [Tape.read, hhead₂, hcells₂, hcells₁]
      exact hone
    obtain ⟨c₃, hstep₃, hstate₃, hinput₃, hwork₃, houtput₃⟩ :
        ∃ c₃, (TM.loopTM tmBody tmTest).step c₂ = some c₃ ∧
          c₃.state = Sum.inr (Sum.inl TM.LoopPhase.done) ∧
          c₃.input = c₂.input ∧ c₃.work = c₂.work ∧
          c₃.output = c₂.output := by
      simp only [TM.step, ↓reduceIte, hstate₂, TM.loopTM, hread₃]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
      · exact TM.transitionInput_eq_self
          (by rw [hinput₂, hinput₁]; exact hin)
      · refine funext fun i => TM.transitionTape_eq_self ?_
        rw [hwork₂, hwork₁]
        exact hwork i
      · rw [← hread₃]
        exact TM.transitionTape_eq_self (by rw [hread₃]; simp)
    refine ⟨c₃, .step hstep₁ (.step hstep₂ (.step hstep₃ .zero)),
      ?_, ?_, ?_, ?_⟩
    · rw [hstate₃, ite_eq_left hone]
    · rw [hinput₃, hinput₂, hinput₁]
    · rw [hwork₃, hwork₂, hwork₁]
    · rw [houtput₃, houtput₂]
  · have hread₃ : c₂.output.read ≠ Γ.one := by
      rw [Tape.read, hhead₂, hcells₂, hcells₁]
      exact hone
    have hread₃Start : c₂.output.read ≠ Γ.start := by
      rw [Tape.read, hhead₂, hcells₂, hcells₁]
      exact hnoStart 1 le_rfl
    obtain ⟨c₃, hstep₃, hstate₃, hinput₃, hwork₃, houtput₃⟩ :
        ∃ c₃, (TM.loopTM tmBody tmTest).step c₂ = some c₃ ∧
          c₃.state = Sum.inl tmBody.qstart ∧
          c₃.input = c₂.input ∧ c₃.work = c₂.work ∧
          c₃.output = c₂.output := by
      simp only [TM.step, ↓reduceIte, hstate₂, TM.loopTM, hread₃]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
      · exact TM.transitionInput_eq_self
          (by rw [hinput₂, hinput₁]; exact hin)
      · refine funext fun i => TM.transitionTape_eq_self ?_
        rw [hwork₂, hwork₁]
        exact hwork i
      · exact TM.transitionTape_eq_self hread₃Start
    refine ⟨c₃, .step hstep₁ (.step hstep₂ (.step hstep₃ .zero)),
      ?_, ?_, ?_, ?_⟩
    · rw [hstate₃, ite_eq_right hone]
    · rw [hinput₃, hinput₂, hinput₁]
    · rw [hwork₃, hwork₂, hwork₁]
    · rw [houtput₃, houtput₂]

/-- The verdict leaf has a literal one-step frame. -/
theorem instructionHaltVerdictTM_hoareTime_frame_internal
    (instruction : Instr) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (work₀ i)) :
    (instructionHaltVerdictTM instruction).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧
        out = instructionHaltOutput instruction)
      1 := by
  intro inp work out hpre
  obtain ⟨rfl, rfl, rfl⟩ := hpre
  have hinp := hinput.move_idle
  have hworkEq :
      (fun i => (work i).writeAndMove
        (TM.readBackWrite (work i).read)
        (TM.idleDir (work i).read)) = work := by
    funext i
    exact (hwork i).writeAndMove_readBack_idle
  have hout :
      ((Tape.init []).move Dir3.right).writeAndMove
          (instructionHaltVerdict instruction).toΓ
          (TM.idleDir ((Tape.init []).move Dir3.right).read) =
        instructionHaltOutput instruction := rfl
  let final : Complexity.Cfg n
      (instructionHaltVerdictTM (n := n) instruction).Q :=
    { state := .done
      input := inp
      work := work
      output := instructionHaltOutput instruction }
  have hstep :
      (instructionHaltVerdictTM instruction).step
        { state := (instructionHaltVerdictTM instruction).qstart
          input := inp
          work := work
          output := (Tape.init []).move Dir3.right } = some final := by
    simp only [TM.step, instructionHaltVerdictTM, reduceCtorEq,
      ↓reduceIte, final]
    rw [hinp, hworkEq, hout]
  exact ⟨final, 1, le_rfl, .step hstep .zero, rfl, rfl, rfl, rfl⟩

/-- An empty dispatch program resets its selector and emits the halt verdict. -/
private theorem dispatchHaltEmpty_hoareTime_frame
    (tapes : ControlInstructionTapes n)
    (store : Store) (pcValue selector : ℕ)
    (cleanWork work₀ : Fin (n + 1) → Tape) (inp₀ : Tape)
    (hready : DispatchReady tapes store pcValue selector cleanWork work₀)
    (hinput : TM.Parked inp₀) :
    (dispatchHaltTM tapes ([] : Program)).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧ work = cleanWork ∧
        out = instructionHaltOutput
          (selectedInstruction ([] : Program) selector))
      (dispatchHaltTime tapes ([] : Program) selector) := by
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
    selector.bits 1 inp₀ work₀ ((Tape.init []).move Dir3.right)
    hselector.2.hasBinaryContent hselector.1
    ⟨by rw [hselector.2.1], by rw [hselector.2.1]⟩
    hinput (fun i _ => hwork₀Parked i) blank_parked
  have hreset' : (TM.resetBinaryWorkTM tapes.liftedLhs).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧ work = cleanWork ∧
        out = (Tape.init []).move Dir3.right)
      (TM.resetBinaryWorkTime 1 selector.bits.length) := by
    apply hreset.consequence
    · exact fun _ _ _ h => h
    · rintro inp work out ⟨hinp, hworkEq, hout⟩
      refine ⟨hinp, ?_, hout⟩
      rw [hworkEq, hready.2, Function.update_idem]
      change Function.update cleanWork tapes.liftedLhs blankTape = cleanWork
      rw [← hcleanLhs, Function.update_eq_self]
    · exact le_rfl
  have hverdict := instructionHaltVerdictTM_hoareTime_frame_internal
    (.halt : Instr) inp₀ cleanWork hinput
    hready.1.control.lookup.scanner.parked
  have hseq := TM.seqTM_hoareTime
    (TM.resetBinaryWorkTM tapes.liftedLhs)
    (instructionHaltVerdictTM (.halt : Instr)) hreset'
    (by
      rintro inp work out ⟨hinp, hworkEq, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using! hinput)
        (by simpa [hworkEq] using!
          hready.1.control.lookup.scanner.parked)
        (by simpa [hout] using! blank_parked)
      rw [hi, hw, ho]
      exact ⟨hinp, hworkEq, hout⟩)
    hverdict
  simpa only [dispatchHaltTM, dispatchHaltTime,
    selectedInstruction] using! hseq

/-- The decrementing selector emits the verdict of the selected instruction
and restores its scratch tape to the clean ABI. -/
theorem dispatchHaltTM_hoareTime_frame_internal
    (tapes : ControlInstructionTapes n) (program : Program)
    (store : Store) (pcValue selector : ℕ)
    (cleanWork work₀ : Fin (n + 1) → Tape) (inp₀ : Tape)
    (hready : DispatchReady tapes store pcValue selector cleanWork work₀)
    (hinput : TM.Parked inp₀) :
    (dispatchHaltTM tapes program).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧ work = cleanWork ∧
        out = instructionHaltOutput
          (selectedInstruction program selector))
      (dispatchHaltTime tapes program selector) := by
  induction program generalizing selector work₀ with
  | nil =>
      exact dispatchHaltEmpty_hoareTime_frame tapes store pcValue selector
        cleanWork work₀ inp₀ hready hinput
  | cons instruction program ih =>
      let pre : TM.TapePred (n + 1) := fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧
        out = (Tape.init []).move Dir3.right
      let post : TM.TapePred (n + 1) := fun inp work out =>
        inp = inp₀ ∧ work = cleanWork ∧
        out = instructionHaltOutput
          (selectedInstruction (instruction :: program) selector)
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
      have hblank : (instructionHaltVerdictTM instruction).HoareTime
          blankPre post 1 := by
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
        have hverdict := instructionHaltVerdictTM_hoareTime_frame_internal
          instruction inp₀ cleanWork hinput
          hready.1.control.lookup.scanner.parked
        obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
            hfinalWork, hfinalOutput⟩ :=
          hverdict inp cleanWork out ⟨hinp, rfl, hout⟩
        refine ⟨final, time, htime, ?_, hhalt, hfinalInput, hfinalWork, ?_⟩
        · simpa [hworkClean] using! hreach
        · simpa only [selectedInstruction] using! hfinalOutput
      have hnonblank :
          (TM.seqTM (TM.binaryPredTM tapes.liftedLhs)
            (dispatchHaltTM tapes program)).HoareTime
          nonblankPre post
          (TM.binaryPredTime (selector - 1) + 1 +
            dispatchHaltTime tapes program (selector - 1)) := by
        rintro inp work out ⟨⟨hinp, hworkEq, hout⟩, hnonzero⟩
        have hsucc : selector = (selector - 1) + 1 := by omega
        have hvalue : (work tapes.liftedLhs).HasBinaryNat
            ((selector - 1) + 1) := by
          rw [hworkEq]
          rw [hsucc] at hselector
          exact hselector
        have hinpParked : TM.Parked inp := by simpa [hinp] using! hinput
        have houtParked : TM.Parked out := by simpa [hout] using! blank_parked
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
        have hnextReady : DispatchReady tapes store pcValue (selector - 1)
            cleanWork nextWork := ⟨hready.1, rfl⟩
        have hrecursive := ih (selector - 1) nextWork hnextReady
        have hrecursive' : (dispatchHaltTM tapes program).HoareTime
            (fun inp' work' out' =>
              inp' = inp ∧ work' = nextWork ∧ out' = out)
            post
            (dispatchHaltTime tapes program (selector - 1)) := by
          apply hrecursive.consequence
          · rintro inp' work' out' ⟨hinp', hwork', hout'⟩
            exact ⟨hinp'.trans hinp, hwork', hout'.trans hout⟩
          · rintro inp' work' out' ⟨hinp', hwork', hout'⟩
            have hselected :
                selectedInstruction (instruction :: program) selector =
                  selectedInstruction program (selector - 1) := by
              rw [hsucc]
              rfl
            exact ⟨hinp', hwork', by simpa only [hselected] using! hout'⟩
          · exact le_rfl
        have hseq := TM.seqTM_hoareTime (TM.binaryPredTM tapes.liftedLhs)
          (dispatchHaltTM tapes program) hpred'
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
              (by simpa [hout', hout] using! blank_parked)
            rw [hi, hw, ho]
            exact ⟨hinp', hwork', hout'⟩)
          hrecursive'
        exact hseq inp work out ⟨rfl, rfl, rfl⟩
      have hdispatch := TM.branchWorkBlankTM_hoareTime tapes.liftedLhs
        (instructionHaltVerdictTM instruction)
        (TM.seqTM (TM.binaryPredTM tapes.liftedLhs)
          (dispatchHaltTM tapes program))
        (pre := pre) (blankPre := blankPre) (nonblankPre := nonblankPre)
        (blankPost := post) (nonblankPost := post)
        (fun inp work out hpre => by
          have hinpParked : TM.Parked inp := by
            simpa [hpre.1] using! hinput
          have houtParked : TM.Parked out := by
            simpa [hpre.2.2] using! blank_parked
          have hworkParked : ∀ i, TM.Parked (work i) := by
            intro i
            simpa [hpre.2.1] using! hwork₀Parked i
          exact ⟨hinpParked.read_ne_start,
            fun i => (hworkParked i).read_ne_start,
            houtParked.read_ne_start⟩)
        (fun _ work _ hpre hread =>
          ⟨hpre, hselector.read_eq_blank_iff.mp
            (by simpa [hpre.2.1] using! hread)⟩)
        (fun _ work _ hpre hread =>
          ⟨hpre, fun hzero => hread (by
            rw [hpre.2.1]
            exact hselector.read_eq_blank_iff.mpr hzero)⟩)
        hblank hnonblank
      simpa only [dispatchHaltTM, dispatchHaltTime, pre, post] using!
        hdispatch.consequence (fun _ _ _ h => h)
          (fun _ _ _ h => h.elim id id) le_rfl

/-- Copy the canonical PC, select its fixed-program instruction, and emit its
halt verdict while restoring the complete instruction ABI. -/
theorem programHaltTM_hoareTime_frame_internal
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
        inp = inp₀ ∧ work = initialWork ∧
        out = instructionHaltOutput
          (selectedInstruction program pcValue))
      (programHaltTime tapes program pcValue) := by
  let selectorTape :=
    (Tape.init (pcValue.bits.map Γ.ofBool)).move Dir3.right
  let selectorWork :=
    Function.update initialWork tapes.liftedLhs selectorTape
  have hcopy := TM.binaryCopyIntoTM_hoareTime_frame tapes.liftedPC
    tapes.liftedLhs tapes.liftedFound tapes.lifted.pc_ne_lhs
    (tapes.lifted.pc_ne 11) (tapes.lifted.data.ne (by decide)) pcValue 0
    inp₀ initialWork ((Tape.init []).move Dir3.right) hready.control.pc
    hready.control.lookup.destination hready.control.lookup.copyScratch hinput
    (fun i _ _ _ => hready.control.lookup.scanner.parked i) blank_parked
  have hselectorReady : DispatchReady tapes store pcValue pcValue initialWork
      selectorWork := by
    exact ⟨hready, rfl⟩
  have hdispatch := dispatchHaltTM_hoareTime_frame_internal tapes program store
    pcValue pcValue initialWork selectorWork inp₀ hselectorReady hinput
  have hselectorParked : ∀ i, TM.Parked (selectorWork i) := by
    intro i
    by_cases hi : i = tapes.liftedLhs
    · subst i
      simp only [selectorWork, Function.update_self]
      exact hasBinaryNat_parked
        (Tape.init_move_right_hasBinaryNat pcValue)
    · simp only [selectorWork, Function.update_of_ne hi]
      exact hready.control.lookup.scanner.parked i
  have hseq := TM.seqTM_hoareTime
    (TM.binaryCopyIntoTM tapes.liftedPC tapes.liftedLhs tapes.liftedFound)
    (dispatchHaltTM tapes program) hcopy
    (by
      rintro inp work out ⟨hinp, hworkEq, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using! hinput)
        (by simpa [hworkEq, selectorWork, selectorTape] using! hselectorParked)
        (by simpa [hout] using! blank_parked)
      rw [hi, hw, ho]
      exact ⟨hinp, by simpa [selectorWork, selectorTape] using! hworkEq, hout⟩)
    hdispatch
  simpa only [programHaltTM, programHaltTime, selectorWork,
    selectorTape] using! hseq

/-- One loop iteration realizes one pure sparse step and either halts on the
successor's `halt` instruction or returns to the body start with blank output. -/
theorem programLoopTM_iteration_internal
    (tapes : ControlInstructionTapes n) (program : Program)
    (snapshot : Snapshot) (initialWork : Fin (n + 1) → Tape)
    (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes snapshot.store snapshot.pc
      initialWork)
    (hinput : TM.Parked inp₀) :
    let next := snapshot.step program
    ∃ (nextWork : Fin (n + 1) → Tape) (time : ℕ),
      time ≤ programLoopIterationTime tapes program snapshot ∧
      InstructionExecutionReady tapes next.store next.pc nextWork ∧
      ((next.Halted program ∧
          (programLoopTM tapes program).reachesIn time
            { state := (programLoopTM tapes program).qstart
              input := inp₀
              work := initialWork
              output := (Tape.init []).move Dir3.right }
            { state := Sum.inr (Sum.inl TM.LoopPhase.done)
              input := inp₀
              work := nextWork
              output := instructionHaltOutput (next.curInstr program) }) ∨
        (¬next.Halted program ∧
          (programLoopTM tapes program).reachesIn time
            { state := (programLoopTM tapes program).qstart
              input := inp₀
              work := initialWork
              output := (Tape.init []).move Dir3.right }
            { state := (programLoopTM tapes program).qstart
              input := inp₀
              work := nextWork
              output := (Tape.init []).move Dir3.right })) := by
  let next := snapshot.step program
  let body := programStepTM tapes program
  let test := programHaltTM tapes program
  let blank := (Tape.init []).move Dir3.right
  have hbody := programStepTM_hoareTime_frame tapes program snapshot.store
    snapshot.pc initialWork inp₀ hready hinput
  obtain ⟨cbody, bodyTime, hbodyTime, hbodyReach, hbodyHalt,
      hbodyInput, hnextReady, hbodyOutput⟩ :=
    hbody inp₀ initialWork blank ⟨rfl, rfl, rfl⟩
  have hbodyInputParked : TM.Parked cbody.input := by
    simpa [hbodyInput] using! hinput
  have hbodyWorkParked : ∀ i, TM.Parked (cbody.work i) := by
    exact hnextReady.control.lookup.scanner.parked
  have hbodyOutputParked : TM.Parked cbody.output := by
    simpa [hbodyOutput, blank] using! blank_parked
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
      exact blank_parked.transitionTape_eq_self
    rw [hi, hw, ho]
  have hbodyToTest := TM.loopTM_body_to_test body test hbodyHalt
  rw [hbodyTransition] at hbodyToTest
  have htest := programHaltTM_hoareTime_frame_internal tapes program
    next.store next.pc cbody.work inp₀ hnextReady hinput
  obtain ⟨ctest, testTime, htestTime, htestReach, htestHalt,
      htestInput, htestWork, htestOutput⟩ :=
    htest inp₀ cbody.work blank ⟨rfl, rfl, rfl⟩
  have hselected :
      selectedInstruction program next.pc = next.curInstr program :=
    selectedInstruction_eq_getElem?_getD program next.pc
  have htestOutput' :
      ctest.output = instructionHaltOutput (next.curInstr program) := by
    simpa only [hselected] using! htestOutput
  have htestInputParked : TM.Parked ctest.input := by
    simpa [htestInput] using! hinput
  have htestWorkParked : ∀ i, TM.Parked (ctest.work i) := by
    simpa [htestWork] using! hbodyWorkParked
  have htestOutputParked : TM.Parked ctest.output := by
    refine ⟨?_, ?_⟩
    · rw [htestOutput', instructionHaltOutput_head_internal]
    · rw [htestOutput']
      exact instructionHaltOutput_cells_ne_start_internal _
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
      (by rw [htestOutput', instructionHaltOutput_head_internal])
      (by rw [htestOutput', instructionHaltOutput_cells_zero_internal])
      (by rw [htestOutput']; exact
        instructionHaltOutput_cells_ne_start_internal _)
  have hreach := TM.reachesIn_trans _
    (TM.reachesIn_trans _
      (TM.reachesIn_trans _
        (TM.reachesIn_trans _ hbodyLoop (.step hbodyToTest .zero))
        (TM.loopTM_test_simulation body test htestReach))
      (.step htestToRewind .zero)) htailReach
  have htime : bodyTime + 1 + testTime + 1 + 3 ≤
      programLoopIterationTime tapes program snapshot := by
    dsimp only [next] at htestTime
    simp only [programLoopIterationTime]
    omega
  refine ⟨cbody.work, bodyTime + 1 + testTime + 1 + 3, htime,
    hnextReady, ?_⟩
  by_cases hhalted : next.Halted program
  · left
    refine ⟨hhalted, ?_⟩
    have hone : ctest.output.cells 1 = Γ.one := by
      rw [htestOutput']
      exact instructionHaltOutput_cell_one_eq_one_iff_internal _ |>.2 hhalted
    have htailDone : ctail.state = Sum.inr (Sum.inl TM.LoopPhase.done) := by
      simpa [hone] using! htailState
    have hcTail : ctail =
        { state := Sum.inr (Sum.inl TM.LoopPhase.done)
          input := inp₀
          work := cbody.work
          output := instructionHaltOutput (next.curInstr program) } := by
      cases ctail
      apply Complexity.Cfg.ext
      · exact htailDone
      · exact htailInput
      · exact htailWork
      · exact htailOutput.trans htestOutput'
    simpa only [programLoopTM, body, test, blank, hcTail] using! hreach
  · right
    refine ⟨hhalted, ?_⟩
    have hcur : next.curInstr program ≠ .halt := hhalted
    have hblankOutput : ctest.output = blank := by
      rw [htestOutput']
      simpa only [blank] using!
        instructionHaltOutput_eq_blank_of_ne_halt_internal hcur
    have hone : ctest.output.cells 1 ≠ Γ.one := by
      rw [htestOutput']
      exact fun h => hhalted
        (instructionHaltOutput_cell_one_eq_one_iff_internal _ |>.1 h)
    have htailStart : ctail.state = Sum.inl body.qstart := by
      simpa [hone] using! htailState
    have hcTail : ctail =
        { state := Sum.inl body.qstart
          input := inp₀
          work := cbody.work
          output := blank } := by
      cases ctail
      apply Complexity.Cfg.ext
      · exact htailStart
      · exact htailInput
      · exact htailWork
      · exact htailOutput.trans hblankOutput
    simpa only [programLoopTM, body, test, blank, hcTail] using! hreach

theorem snapshot_step_eq_self_of_halted_internal
    (program : Program) (snapshot : Snapshot)
    (hhalted : snapshot.Halted program) :
    snapshot.step program = snapshot := by
  change snapshot.curInstr program = .halt at hhalted
  rw [Snapshot.step, hhalted]
  rfl

theorem snapshot_run_halted_internal
    (program : Program) (snapshot : Snapshot)
    (hhalted : snapshot.Halted program) :
    ∀ fuel, snapshot.run program fuel = snapshot
  | 0 => rfl
  | fuel + 1 => by
      rw [Snapshot.run, ite_eq_left hhalted]

/-- A halted fuel-bounded sparse run is realized by the fixed controller loop.
The extra iteration handles a snapshot that is already halted at fuel zero. -/
theorem programLoopTM_hoareTime_run_internal
    (tapes : ControlInstructionTapes n) (program : Program) :
    ∀ (fuel : ℕ) (snapshot : Snapshot)
      (initialWork : Fin (n + 1) → Tape) (inp₀ : Tape),
      InstructionExecutionReady tapes snapshot.store snapshot.pc initialWork →
      TM.Parked inp₀ →
      (snapshot.run program fuel).Halted program →
      (programLoopTM tapes program).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = initialWork ∧
          out = (Tape.init []).move Dir3.right)
        (fun inp work out =>
          let final := snapshot.run program fuel
          inp = inp₀ ∧
          InstructionExecutionReady tapes final.store final.pc work ∧
          out = instructionHaltOutput (final.curInstr program))
        (programLoopTime tapes program (fuel + 1) snapshot) := by
  intro fuel
  induction fuel with
  | zero =>
      intro snapshot initialWork inp₀ hready hinput hhalted
      rintro inp work out ⟨hinp, hwork, hout⟩
      subst inp
      subst work
      subst out
      have hsnapshotHalted : snapshot.Halted program := by
        simpa [Snapshot.run] using! hhalted
      have hstepSelf := snapshot_step_eq_self_of_halted_internal program
        snapshot hsnapshotHalted
      obtain ⟨nextWork, time, htime, hnextReady, hbranch⟩ :=
        programLoopTM_iteration_internal tapes program snapshot initialWork
          inp₀ hready hinput
      rcases hbranch with ⟨hnextHalted, hreach⟩ |
          ⟨hnextRunning, _⟩
      · have hready' : InstructionExecutionReady tapes snapshot.store
            snapshot.pc nextWork := by
          simpa only [hstepSelf] using! hnextReady
        have hreach' : (programLoopTM tapes program).reachesIn time
            { state := (programLoopTM tapes program).qstart
              input := inp₀
              work := initialWork
              output := (Tape.init []).move Dir3.right }
            { state := Sum.inr (Sum.inl TM.LoopPhase.done)
              input := inp₀
              work := nextWork
              output := instructionHaltOutput
                (snapshot.curInstr program) } := by
          simpa only [hstepSelf] using! hreach
        refine ⟨_, time, ?_, hreach', rfl, rfl, ?_, ?_⟩
        · simpa [programLoopTime] using! htime
        · simpa [Snapshot.run] using! hready'
        · simp [Snapshot.run]
      · exact (hnextRunning (by simpa only [hstepSelf] using!
          hsnapshotHalted)).elim
  | succ fuel ih =>
      intro snapshot initialWork inp₀ hready hinput hhalted
      by_cases hsnapshotHalted : snapshot.Halted program
      · rintro inp work out ⟨hinp, hwork, hout⟩
        subst inp
        subst work
        subst out
        have hstepSelf := snapshot_step_eq_self_of_halted_internal program
          snapshot hsnapshotHalted
        obtain ⟨nextWork, time, htime, hnextReady, hbranch⟩ :=
          programLoopTM_iteration_internal tapes program snapshot initialWork
            inp₀ hready hinput
        rcases hbranch with ⟨_, hreach⟩ | ⟨hnextRunning, _⟩
        · have hfinal : snapshot.run program (fuel + 1) = snapshot :=
            snapshot_run_halted_internal program snapshot hsnapshotHalted _
          have hready' : InstructionExecutionReady tapes snapshot.store
              snapshot.pc nextWork := by
            simpa only [hstepSelf] using! hnextReady
          have hreach' : (programLoopTM tapes program).reachesIn time
              { state := (programLoopTM tapes program).qstart
                input := inp₀
                work := initialWork
                output := (Tape.init []).move Dir3.right }
              { state := Sum.inr (Sum.inl TM.LoopPhase.done)
                input := inp₀
                work := nextWork
                output := instructionHaltOutput
                  (snapshot.curInstr program) } := by
            simpa only [hstepSelf] using! hreach
          refine ⟨_, time, ?_, hreach', rfl, rfl, ?_, ?_⟩
          · simp only [programLoopTime]
            omega
          · simpa only [hfinal] using! hready'
          · simp only [hfinal]
        · exact (hnextRunning (by simpa only [hstepSelf] using!
            hsnapshotHalted)).elim
      · have hrunHalted :
            ((snapshot.step program).run program fuel).Halted program := by
          simpa [Snapshot.run, hsnapshotHalted] using! hhalted
        have hiter := programLoopTM_iteration_internal tapes program snapshot
          initialWork inp₀ hready hinput
        obtain ⟨nextWork, time₁, htime₁, hnextReady, hbranch⟩ := hiter
        rcases hbranch with ⟨hnextHalted, hreach₁⟩ |
            ⟨hnextRunning, hreach₁⟩
        · rintro inp work out ⟨hinp, hwork, hout⟩
          subst inp
          subst work
          subst out
          have hfinal :
              (snapshot.step program).run program fuel =
                snapshot.step program :=
            snapshot_run_halted_internal program (snapshot.step program)
              hnextHalted fuel
          refine ⟨_, time₁, ?_, hreach₁, rfl, rfl, ?_, ?_⟩
          · simp only [programLoopTime]
            omega
          · simpa [Snapshot.run, hsnapshotHalted, hfinal] using! hnextReady
          · simp [Snapshot.run, hsnapshotHalted, hfinal]
        · have hrecursive := ih (snapshot.step program) nextWork inp₀
            hnextReady hinput hrunHalted
          rintro inp work out ⟨hinp, hwork, hout⟩
          subst inp
          subst work
          subst out
          obtain ⟨cfinal, time₂, htime₂, hreach₂, hhalt₂,
              hfinalInput, hfinalReady, hfinalOutput⟩ :=
            hrecursive inp₀ nextWork ((Tape.init []).move Dir3.right)
              ⟨rfl, rfl, rfl⟩
          refine ⟨cfinal, time₁ + time₂, ?_,
            TM.reachesIn_trans _ hreach₁ hreach₂, hhalt₂,
            hfinalInput, ?_, ?_⟩
          · change time₁ + time₂ ≤
              programLoopIterationTime tapes program snapshot +
                programLoopTime tapes program (fuel + 1)
                  (snapshot.step program)
            exact Nat.add_le_add htime₁ htime₂
          · simpa [Snapshot.run, hsnapshotHalted] using! hfinalReady
          · simpa [Snapshot.run, hsnapshotHalted] using! hfinalOutput

end Machine

end RegisterStore

end RAM

end Complexity
