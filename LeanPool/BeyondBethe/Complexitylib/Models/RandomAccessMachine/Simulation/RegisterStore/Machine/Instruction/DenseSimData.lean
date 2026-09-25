/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseSimDefs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Sim.Data
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseImm
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseLoad
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseStore

/-!
# Dense-overlay data-instruction simulation
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

variable {n : ℕ}

/-- A dense immediate write produces the generic buffered endpoint and advances
the program counter. -/
theorem denseExecuteInstructionTM_imm_hoareTime_frame
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue destination value : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseExecuteInstructionTM tapes (.imm destination value)).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseInstructionExecutionResult tapes input (.imm destination value)
          pcValue overlay work ∧
        out = (Tape.init []).move Dir3.right)
      (denseExecuteInstructionTime tapes input (.imm destination value)
        pcValue overlay) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let baseWork : Fin n → Tape := fun i => initialWork (Fin.castSucc i)
  let nextStore := DenseOverlay.write overlay destination value
  let cleanupValues :=
    denseInstructionCleanupValue input (.imm destination value) overlay
  have hinput : TM.Parked inp₀ := by
    refine ⟨by simp [inp₀, Tape.move], ?_⟩
    simpa [inp₀] using! Tape.init_ofBool_move_right_cells_ne_start input
  have hlookup : EntryLookupStaticReady tapes.data.lhsLookup overlay
      baseWork :=
    instructionExecutionReady_baseLookup_internal tapes overlay pcValue
      initialWork hready
  have hreplacement :
      (baseWork tapes.data.update.replacement).HasBinaryNat 0 :=
    hready.replacement
  have hbuffer : (initialWork tapes.buffer).HasBinaryPrefix [] := by
    rw [hready.buffer]
    exact Tape.init_nil_move_right_hasBinaryPrefix_nil
  have hbaseRaw := denseImmediateInstructionTM_hoareTime_frame tapes.data
    overlay destination value [] baseWork inp₀ (initialWork tapes.buffer)
    hvalid.1 hlookup hreplacement hinput hbuffer
  let Result : (Fin n → Tape) → Prop := fun work =>
    DenseImmediateInstructionResult tapes.data overlay destination value
      baseWork work
  have hbase : (denseImmediateInstructionTM tapes.data destination value).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = baseWork ∧ out = initialWork tapes.buffer)
      (fun inp work out =>
        inp = inp₀ ∧ Result work ∧
        out.HasBinaryPrefix (nextStore.flatMap Entry.encode))
      (denseImmediateInstructionTime tapes.data overlay destination value) := by
    simpa [Result, nextStore] using! hbaseRaw
  have hresult : ∀ work, Result work →
      work tapes.pc = initialWork (Fin.castSucc tapes.pc) ∧
      (work tapes.data.update.resultCount).HasBinaryNat nextStore.length ∧
      (work tapes.data.update.entry.source).HasBinaryContent
        (overlay.flatMap Entry.encode) ∧
      (∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (cleanupValues slot)) ∧
      (work tapes.data.update.remaining).HasBinaryNat 0 ∧
      EntryScanReady tapes.data.update.entry [] (cleanupValues 0).bits
        work work ∧
      (work tapes.data.shift).HasBinaryNat 0 ∧
      (work tapes.data.tmp).HasBinaryNat 0 ∧
      (work tapes.data.dbl).HasBinaryNat 0 ∧
      ∀ i, TM.Parked (work i) := by
    intro work hsemantic
    obtain ⟨valueWork, updateWork, hvalueWork, hupdateWork,
      taggedWork, htagValue, htagFrame, houtcome, hsourceCells⟩ := hsemantic
    have hpc : work tapes.pc = baseWork tapes.pc := by
      have hpcQuery :
          tapes.pc ≠ tapes.data.update.entry.query := tapes.pc_ne 7
      have hpcReplacement :
          tapes.pc ≠ tapes.data.update.replacement := tapes.pc_ne 10
      calc
        work tapes.pc = taggedWork tapes.pc :=
          houtcome.frame tapes.pc (fun slot => by
            exact tapes.pc_ne ⟨slot, by omega⟩)
        _ = updateWork tapes.pc :=
          htagFrame tapes.pc (tapes.pc_ne 10)
        _ = valueWork tapes.pc := by
          rw [hupdateWork, Function.update_of_ne hpcQuery]
        _ = baseWork tapes.pc := by
          rw [hvalueWork, Function.update_of_ne hpcReplacement]
    have hsourceContent :
        (work tapes.data.update.entry.source).HasBinaryContent
          (overlay.flatMap Entry.encode) := by
      have hcells : (work tapes.data.update.entry.source).cells =
          (baseWork tapes.data.update.entry.source).cells := by
        calc
          (work tapes.data.update.entry.source).cells =
              (updateWork tapes.data.update.entry.source).cells := hsourceCells
          _ = (valueWork tapes.data.update.entry.source).cells := by
            congr 1
            rw [hupdateWork]
            exact Function.update_of_ne
              (tapes.data.update.ne (by decide)) _ _
          _ = (baseWork tapes.data.update.entry.source).cells := by
            congr 1
            rw [hvalueWork]
            exact Function.update_of_ne
              (tapes.data.update.ne (by decide)) _ _
      unfold Tape.HasBinaryContent
      rw [hcells]
      exact hready.sourceContent
    have hcleanup : ∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (cleanupValues slot) := by
      intro slot
      fin_cases slot
      · exact ⟨houtcome.ready.queryStart, by
          simpa [cleanupValues, denseInstructionCleanupValue,
            instructionCleanupParentSlot] using! houtcome.ready.query⟩
      · change (work tapes.data.update.replacement).HasBinaryNat (value + 1)
        rw [houtcome.replacement]
        exact htagValue
      · simpa [cleanupValues, denseInstructionCleanupValue,
          instructionCleanupParentSlot] using! houtcome.found
      · change (work tapes.data.lhs).HasBinaryNat 0
        rw [houtcome.frame tapes.data.lhs (fun role =>
            (tapes.data.update_ne_lhs role).symm),
          htagFrame tapes.data.lhs
            (tapes.data.update_ne_lhs 10).symm,
          show updateWork tapes.data.lhs = valueWork tapes.data.lhs by
            rw [hupdateWork]
            exact Function.update_of_ne
              (tapes.data.update_ne_lhs 7).symm _ _,
          show valueWork tapes.data.lhs = baseWork tapes.data.lhs by
            rw [hvalueWork]
            exact Function.update_of_ne
              (tapes.data.update_ne_lhs 10).symm _ _]
        exact hready.control.lookup.destination
      · change (work tapes.data.rhs).HasBinaryNat 0
        rw [houtcome.frame tapes.data.rhs (fun role =>
            (tapes.data.update_ne_rhs role).symm),
          htagFrame tapes.data.rhs
            (tapes.data.update_ne_rhs 10).symm,
          show updateWork tapes.data.rhs = valueWork tapes.data.rhs by
            rw [hupdateWork]
            exact Function.update_of_ne
              (tapes.data.update_ne_rhs 7).symm _ _,
          show valueWork tapes.data.rhs = baseWork tapes.data.rhs by
            rw [hvalueWork]
            exact Function.update_of_ne
              (tapes.data.update_ne_rhs 10).symm _ _]
        exact hready.rhs
    have hshift : (work tapes.data.shift).HasBinaryNat 0 := by
      rw [houtcome.frame tapes.data.shift (fun slot =>
          (tapes.data.update_ne_shift slot).symm),
        htagFrame tapes.data.shift (tapes.data.update_ne_shift 10).symm,
        show updateWork tapes.data.shift = valueWork tapes.data.shift by
          rw [hupdateWork]
          exact Function.update_of_ne
            (tapes.data.update_ne_shift 7).symm _ _,
        show valueWork tapes.data.shift = baseWork tapes.data.shift by
          rw [hvalueWork]
          exact Function.update_of_ne
            (tapes.data.update_ne_shift 10).symm _ _]
      exact hready.control.lookup.querySource
    have htmp : (work tapes.data.tmp).HasBinaryNat 0 := by
      rw [houtcome.frame tapes.data.tmp (fun slot =>
          (tapes.data.update_ne_tmp slot).symm),
        htagFrame tapes.data.tmp (tapes.data.update_ne_tmp 10).symm,
        show updateWork tapes.data.tmp = valueWork tapes.data.tmp by
          rw [hupdateWork]
          exact Function.update_of_ne
            (tapes.data.update_ne_tmp 7).symm _ _,
        show valueWork tapes.data.tmp = baseWork tapes.data.tmp by
          rw [hvalueWork]
          exact Function.update_of_ne
            (tapes.data.update_ne_tmp 10).symm _ _]
      exact hready.tmp
    have hdbl : (work tapes.data.dbl).HasBinaryNat 0 := by
      rw [houtcome.frame tapes.data.dbl (fun slot =>
          (tapes.data.update_ne_dbl slot).symm),
        htagFrame tapes.data.dbl (tapes.data.update_ne_dbl 10).symm,
        show updateWork tapes.data.dbl = valueWork tapes.data.dbl by
          rw [hupdateWork]
          exact Function.update_of_ne
            (tapes.data.update_ne_dbl 7).symm _ _,
        show valueWork tapes.data.dbl = baseWork tapes.data.dbl by
          rw [hvalueWork]
          exact Function.update_of_ne
            (tapes.data.update_ne_dbl 10).symm _ _]
      exact hready.dbl
    refine ⟨hpc, ?_, hsourceContent, hcleanup, ?_, ?_, hshift, htmp,
      hdbl, houtcome.ready.parked⟩
    · simpa [nextStore] using! houtcome.resultCount
    · simpa using! houtcome.remaining
    · simpa [cleanupValues, denseInstructionCleanupValue] using!
        houtcome.ready
  have hdata := retargetBufferedDataKernel_hoareTime_frame_internal tapes
    overlay nextStore cleanupValues 0 pcValue initialWork inp₀
    (denseImmediateInstructionTM tapes.data destination value)
    (denseImmediateInstructionTime tapes.data overlay destination value)
    Result hready hbase hresult
  have hall := finishBufferedDataTM_hoareTime_frame_internal tapes overlay
    nextStore (pcValue + 1) pcValue cleanupValues 0 initialWork inp₀
    (denseImmediateInstructionTM tapes.data destination value)
    (denseImmediateInstructionTime tapes.data overlay destination value)
    rfl hinput hdata
  simpa [denseExecuteInstructionTM, denseExecuteInstructionTime,
    DenseInstructionExecutionResult, denseInstructionStore,
    denseInstructionPC, DenseOverlay.Snapshot.stepInstr, nextStore,
    cleanupValues] using! hall

/-- Instruction constructor corresponding to a dense direct arithmetic
kernel. -/
def denseDirectInstruction (op : BinaryInstrOp)
    (destination source₀ source₁ : ℕ) : Instr :=
  match op with
  | .add => .add destination source₀ source₁
  | .sub => .sub destination source₀ source₁
  | .mul => .mul destination source₀ source₁

/-- A dense direct arithmetic instruction produces the generic buffered
endpoint and advances the program counter. -/
theorem denseExecuteInstructionTM_direct_hoareTime_frame
    (tapes : ControlInstructionTapes n) (op : BinaryInstrOp)
    (input : List Bool) (overlay : Store)
    (pcValue destination source₀ source₁ : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseExecuteInstructionTM tapes
      (denseDirectInstruction op destination source₀ source₁)).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseInstructionExecutionResult tapes input
          (denseDirectInstruction op destination source₀ source₁)
          pcValue overlay work ∧
        out = (Tape.init []).move Dir3.right)
      (denseExecuteInstructionTime tapes input
        (denseDirectInstruction op destination source₀ source₁)
        pcValue overlay) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let baseWork : Fin n → Tape := fun i => initialWork (Fin.castSucc i)
  let instruction := denseDirectInstruction op destination source₀ source₁
  let lhs := DenseOverlay.read input overlay source₀
  let rhs := DenseOverlay.read input overlay source₁
  let nextStore := DenseOverlay.write overlay destination (op.eval lhs rhs)
  let cleanupValues := denseInstructionCleanupValue input instruction overlay
  have hinput : TM.Parked inp₀ := by
    refine ⟨by simp [inp₀, Tape.move], ?_⟩
    simpa [inp₀] using! Tape.init_ofBool_move_right_cells_ne_start input
  have hlookup : EntryLookupStaticReady tapes.data.lhsLookup overlay
      baseWork :=
    instructionExecutionReady_baseLookup_internal tapes overlay pcValue
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
  have hbaseRaw := denseDirectBinaryInstructionTM_hoareTime_frame tapes.data
    op input overlay destination source₀ source₁ [] baseWork
    (initialWork tapes.buffer) hvalid hlookup hrhs hreplacement htmp hdbl
    hbuffer
  let Result : (Fin n → Tape) → Prop := fun work =>
    DenseDirectBinaryInstructionResult tapes.data op input overlay destination
      source₀ source₁ baseWork work
  have hbase : (denseDirectBinaryInstructionTM tapes.data op destination
      source₀ source₁).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = baseWork ∧ out = initialWork tapes.buffer)
      (fun inp work out =>
        inp = inp₀ ∧ Result work ∧
        out.HasBinaryPrefix (nextStore.flatMap Entry.encode))
      (denseDirectBinaryInstructionTime tapes.data op input overlay destination
        source₀ source₁) := by
    simpa [Result, lhs, rhs, nextStore] using! hbaseRaw
  have hresult : ∀ work, Result work →
      work tapes.pc = initialWork (Fin.castSucc tapes.pc) ∧
      (work tapes.data.update.resultCount).HasBinaryNat nextStore.length ∧
      (work tapes.data.update.entry.source).HasBinaryContent
        (overlay.flatMap Entry.encode) ∧
      (∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (cleanupValues slot)) ∧
      (work tapes.data.update.remaining).HasBinaryNat 0 ∧
      EntryScanReady tapes.data.update.entry [] (cleanupValues 0).bits
        work work ∧
      (work tapes.data.shift).HasBinaryNat 0 ∧
      (work tapes.data.tmp).HasBinaryNat 0 ∧
      (work tapes.data.dbl).HasBinaryNat 0 ∧
      ∀ i, TM.Parked (work i) := by
    intro work hsemantic
    obtain ⟨updateWork, haddress, hbinary⟩ := hsemantic
    obtain ⟨operandsWork, hoperands, hupdateWork⟩ := haddress
    obtain ⟨lhsWork, hlhs, hrhsResult⟩ := hoperands
    obtain ⟨arithmeticWork, harithmetic, htagged⟩ := hbinary
    obtain ⟨taggedWork, htagValue, htagFrame, houtcome,
      hsourceCells⟩ := htagged
    have hpcUpdate : work tapes.pc = taggedWork tapes.pc :=
      houtcome.frame tapes.pc (fun slot => by
        exact tapes.pc_ne ⟨slot, by omega⟩)
    have hpcTag : taggedWork tapes.pc = arithmeticWork tapes.pc :=
      htagFrame tapes.pc (tapes.pc_ne 10)
    have hpcArithmetic : arithmeticWork tapes.pc = updateWork tapes.pc :=
      harithmetic.frame tapes.pc (tapes.pc_ne 13) (tapes.pc_ne 14)
        (tapes.pc_ne 10) (tapes.pc_ne 15) (tapes.pc_ne 16)
        (tapes.pc_ne 17)
    have hpcQuery :
        tapes.pc ≠ tapes.data.update.entry.query := tapes.pc_ne 7
    have hpcAddress : updateWork tapes.pc = operandsWork tapes.pc := by
      rw [hupdateWork, Function.update_of_ne hpcQuery]
    have hpcRhs : operandsWork tapes.pc = lhsWork tapes.pc :=
      hrhsResult.frame tapes.pc (fun slot => by
        exact tapes.pc_ne (BinaryInstructionTapes.rhsLookupSlot slot))
    have hpcLhs : lhsWork tapes.pc = baseWork tapes.pc :=
      hlhs.frame tapes.pc (fun slot => by
        exact tapes.pc_ne (BinaryInstructionTapes.lhsLookupSlot slot))
    have hsourceContent :
        (work tapes.data.update.entry.source).HasBinaryContent
          (overlay.flatMap Entry.encode) := by
      have harithmeticSource :
          arithmeticWork tapes.data.update.entry.source =
            updateWork tapes.data.update.entry.source :=
        harithmetic.frame tapes.data.update.entry.source
          (tapes.data.update_ne_lhs 0)
          (tapes.data.update_ne_rhs 0)
          (tapes.data.update.ne (by decide))
          (tapes.data.update_ne_shift 0)
          (tapes.data.update_ne_tmp 0)
          (tapes.data.update_ne_dbl 0)
      have hcells : (work tapes.data.update.entry.source).cells =
          (baseWork tapes.data.update.entry.source).cells := by
        calc
          (work tapes.data.update.entry.source).cells =
              (arithmeticWork tapes.data.update.entry.source).cells :=
            hsourceCells
          _ = (updateWork tapes.data.update.entry.source).cells := by
            rw [harithmeticSource]
          _ = (operandsWork tapes.data.update.entry.source).cells := by
            congr 1
            rw [hupdateWork]
            exact Function.update_of_ne
              (tapes.data.update.ne (by decide)) _ _
          _ = (lhsWork tapes.data.update.entry.source).cells :=
            hrhsResult.sourceCells
          _ = (baseWork tapes.data.update.entry.source).cells :=
            hlhs.sourceCells
      unfold Tape.HasBinaryContent
      rw [hcells]
      exact hready.sourceContent
    have hcleanup : ∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (cleanupValues slot) := by
      intro slot
      fin_cases slot
      · exact ⟨houtcome.ready.queryStart, by
          cases op <;>
            simpa [instruction, denseDirectInstruction, cleanupValues,
              denseInstructionCleanupValue, instructionCleanupParentSlot]
              using! houtcome.ready.query⟩
      · change (work tapes.data.update.replacement).HasBinaryNat _
        rw [houtcome.replacement]
        cases op <;>
          simpa [instruction, denseDirectInstruction, cleanupValues,
            denseInstructionCleanupValue, lhs, rhs, BinaryInstrOp.eval]
            using! htagValue
      · cases op <;>
          simpa [instruction, denseDirectInstruction, cleanupValues,
            denseInstructionCleanupValue, instructionCleanupParentSlot]
            using! houtcome.found
      · change (work tapes.data.lhs).HasBinaryNat _
        rw [houtcome.frame tapes.data.lhs (fun role =>
            (tapes.data.update_ne_lhs role).symm),
          htagFrame tapes.data.lhs
            (tapes.data.update_ne_lhs 10).symm]
        cases op <;>
          simpa [instruction, denseDirectInstruction, cleanupValues,
            denseInstructionCleanupValue, lhs] using! harithmetic.lhsValue
      · change (work tapes.data.rhs).HasBinaryNat _
        rw [houtcome.frame tapes.data.rhs (fun role =>
            (tapes.data.update_ne_rhs role).symm),
          htagFrame tapes.data.rhs
            (tapes.data.update_ne_rhs 10).symm]
        cases op <;>
          simpa [instruction, denseDirectInstruction, cleanupValues,
            denseInstructionCleanupValue, rhs] using! harithmetic.rhsValue
    have hshift : (work tapes.data.shift).HasBinaryNat 0 := by
      rw [houtcome.frame tapes.data.shift (fun slot =>
          (tapes.data.update_ne_shift slot).symm),
        htagFrame tapes.data.shift (tapes.data.update_ne_shift 10).symm]
      exact harithmetic.shift
    have htmp' : (work tapes.data.tmp).HasBinaryNat 0 := by
      rw [houtcome.frame tapes.data.tmp (fun slot =>
          (tapes.data.update_ne_tmp slot).symm),
        htagFrame tapes.data.tmp (tapes.data.update_ne_tmp 10).symm]
      exact harithmetic.tmp
    have hdbl' : (work tapes.data.dbl).HasBinaryNat 0 := by
      rw [houtcome.frame tapes.data.dbl (fun slot =>
          (tapes.data.update_ne_dbl slot).symm),
        htagFrame tapes.data.dbl (tapes.data.update_ne_dbl 10).symm]
      exact harithmetic.dbl
    refine ⟨hpcUpdate.trans (hpcTag.trans (hpcArithmetic.trans
      (hpcAddress.trans (hpcRhs.trans hpcLhs)))), ?_, hsourceContent,
      hcleanup, ?_, ?_, hshift, htmp', hdbl', houtcome.ready.parked⟩
    · simpa [nextStore, DenseOverlay.write] using! houtcome.resultCount
    · simpa using! houtcome.remaining
    · cases op <;>
        simpa [instruction, denseDirectInstruction, cleanupValues,
          denseInstructionCleanupValue] using! houtcome.ready
  have hdata := retargetBufferedDataKernel_hoareTime_frame_internal tapes
    overlay nextStore cleanupValues 0 pcValue initialWork inp₀
    (denseDirectBinaryInstructionTM tapes.data op destination source₀ source₁)
    (denseDirectBinaryInstructionTime tapes.data op input overlay destination
      source₀ source₁) Result hready hbase hresult
  have hall := finishBufferedDataTM_hoareTime_frame_internal tapes overlay
    nextStore (pcValue + 1) pcValue cleanupValues 0 initialWork inp₀
    (denseDirectBinaryInstructionTM tapes.data op destination source₀ source₁)
    (denseDirectBinaryInstructionTime tapes.data op input overlay destination
      source₀ source₁) rfl hinput hdata
  cases op <;>
    simpa [instruction, denseDirectInstruction, denseExecuteInstructionTM,
      denseExecuteInstructionTime, DenseInstructionExecutionResult,
      denseInstructionStore, denseInstructionPC,
      DenseOverlay.Snapshot.stepInstr, nextStore, cleanupValues, lhs, rhs,
      BinaryInstrOp.eval] using! hall

/-- Dense direct addition has the common buffered instruction contract. -/
theorem denseExecuteInstructionTM_add_hoareTime_frame
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue destination source₀ source₁ : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseExecuteInstructionTM tapes
      (.add destination source₀ source₁)).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseInstructionExecutionResult tapes input
          (.add destination source₀ source₁) pcValue overlay work ∧
        out = (Tape.init []).move Dir3.right)
      (denseExecuteInstructionTime tapes input
        (.add destination source₀ source₁) pcValue overlay) := by
  simpa [denseDirectInstruction] using!
    denseExecuteInstructionTM_direct_hoareTime_frame tapes .add input overlay
      pcValue destination source₀ source₁ initialWork hvalid hready

/-- Dense direct subtraction has the common buffered instruction contract. -/
theorem denseExecuteInstructionTM_sub_hoareTime_frame
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue destination source₀ source₁ : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseExecuteInstructionTM tapes
      (.sub destination source₀ source₁)).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseInstructionExecutionResult tapes input
          (.sub destination source₀ source₁) pcValue overlay work ∧
        out = (Tape.init []).move Dir3.right)
      (denseExecuteInstructionTime tapes input
        (.sub destination source₀ source₁) pcValue overlay) := by
  simpa [denseDirectInstruction] using!
    denseExecuteInstructionTM_direct_hoareTime_frame tapes .sub input overlay
      pcValue destination source₀ source₁ initialWork hvalid hready

/-- Dense direct multiplication has the common buffered instruction contract. -/
theorem denseExecuteInstructionTM_mul_hoareTime_frame
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue destination source₀ source₁ : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseExecuteInstructionTM tapes
      (.mul destination source₀ source₁)).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseInstructionExecutionResult tapes input
          (.mul destination source₀ source₁) pcValue overlay work ∧
        out = (Tape.init []).move Dir3.right)
      (denseExecuteInstructionTime tapes input
        (.mul destination source₀ source₁) pcValue overlay) := by
  simpa [denseDirectInstruction] using!
    denseExecuteInstructionTM_direct_hoareTime_frame tapes .mul input overlay
      pcValue destination source₀ source₁ initialWork hvalid hready

/-- A dense indirect load produces the generic buffered endpoint and advances
the program counter. -/
theorem denseExecuteInstructionTM_load_hoareTime_frame
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue destination addressRegister : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseExecuteInstructionTM tapes
      (.load destination addressRegister)).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseInstructionExecutionResult tapes input
          (.load destination addressRegister) pcValue overlay work ∧
        out = (Tape.init []).move Dir3.right)
      (denseExecuteInstructionTime tapes input
        (.load destination addressRegister) pcValue overlay) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let baseWork : Fin n → Tape := fun i => initialWork (Fin.castSucc i)
  let instruction : Instr := .load destination addressRegister
  let address := DenseOverlay.read input overlay addressRegister
  let value := DenseOverlay.read input overlay address
  let nextStore := DenseOverlay.write overlay destination value
  let cleanupValues := denseInstructionCleanupValue input instruction overlay
  have hinput : TM.Parked inp₀ := by
    refine ⟨by simp [inp₀, Tape.move], ?_⟩
    simpa [inp₀] using! Tape.init_ofBool_move_right_cells_ne_start input
  have hlookup : EntryLookupStaticReady tapes.data.lhsLookup overlay
      baseWork :=
    instructionExecutionReady_baseLookup_internal tapes overlay pcValue
      initialWork hready
  have hreplacement :
      (baseWork tapes.data.update.replacement).HasBinaryNat 0 :=
    hready.replacement
  have hbuffer : (initialWork tapes.buffer).HasBinaryPrefix [] := by
    rw [hready.buffer]
    exact Tape.init_nil_move_right_hasBinaryPrefix_nil
  have hbaseRaw := denseIndirectLoadInstructionTM_hoareTime_frame tapes.data
    input overlay destination addressRegister [] baseWork
    (initialWork tapes.buffer) hvalid hlookup hreplacement hbuffer
  let Result : (Fin n → Tape) → Prop := fun work =>
    DenseIndirectLoadInstructionResult tapes.data input overlay destination
      addressRegister baseWork work
  have hbase : (denseIndirectLoadInstructionTM tapes.data destination
      addressRegister).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = baseWork ∧ out = initialWork tapes.buffer)
      (fun inp work out =>
        inp = inp₀ ∧ Result work ∧
        out.HasBinaryPrefix (nextStore.flatMap Entry.encode))
      (denseIndirectLoadInstructionTime tapes.data input overlay destination
        addressRegister) := by
    simpa [Result, address, value, nextStore] using! hbaseRaw
  have hresult : ∀ work, Result work →
      work tapes.pc = initialWork (Fin.castSucc tapes.pc) ∧
      (work tapes.data.update.resultCount).HasBinaryNat nextStore.length ∧
      (work tapes.data.update.entry.source).HasBinaryContent
        (overlay.flatMap Entry.encode) ∧
      (∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (cleanupValues slot)) ∧
      (work tapes.data.update.remaining).HasBinaryNat 0 ∧
      EntryScanReady tapes.data.update.entry [] (cleanupValues 0).bits
        work work ∧
      (work tapes.data.shift).HasBinaryNat 0 ∧
      (work tapes.data.tmp).HasBinaryNat 0 ∧
      (work tapes.data.dbl).HasBinaryNat 0 ∧
      ∀ i, TM.Parked (work i) := by
    intro work hsemantic
    obtain ⟨addressWork, loadedWork, updateWork, haddress, hloaded,
      hupdateWork, htagged⟩ := hsemantic
    obtain ⟨taggedWork, htagValue, htagFrame, houtcome,
      hsourceCells⟩ := htagged
    have hpcOutcome : work tapes.pc = taggedWork tapes.pc :=
      houtcome.frame tapes.pc (fun slot => by
        exact tapes.pc_ne ⟨slot, by omega⟩)
    have hpcTag : taggedWork tapes.pc = updateWork tapes.pc :=
      htagFrame tapes.pc (tapes.pc_ne 10)
    have hpcQuery :
        tapes.pc ≠ tapes.data.update.entry.query := tapes.pc_ne 7
    have hpcUpdate : updateWork tapes.pc = loadedWork tapes.pc := by
      rw [hupdateWork, Function.update_of_ne hpcQuery]
    have hpcLoaded : loadedWork tapes.pc = addressWork tapes.pc :=
      hloaded.frame tapes.pc (fun slot => by
        exact tapes.pc_ne
          (BinaryInstructionTapes.indirectLoadLookupSlot slot))
    have hpcAddress : addressWork tapes.pc = baseWork tapes.pc :=
      haddress.frame tapes.pc (fun slot => by
        exact tapes.pc_ne (BinaryInstructionTapes.lhsLookupSlot slot))
    have hsourceContent :
        (work tapes.data.update.entry.source).HasBinaryContent
          (overlay.flatMap Entry.encode) := by
      have hcells : (work tapes.data.update.entry.source).cells =
          (baseWork tapes.data.update.entry.source).cells := by
        calc
          (work tapes.data.update.entry.source).cells =
              (updateWork tapes.data.update.entry.source).cells :=
            hsourceCells
          _ = (loadedWork tapes.data.update.entry.source).cells := by
            congr 1
            rw [hupdateWork]
            exact Function.update_of_ne
              (tapes.data.update.ne (by decide)) _ _
          _ = (addressWork tapes.data.update.entry.source).cells :=
            hloaded.sourceCells
          _ = (baseWork tapes.data.update.entry.source).cells :=
            haddress.sourceCells
      unfold Tape.HasBinaryContent
      rw [hcells]
      exact hready.sourceContent
    have hcleanup : ∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (cleanupValues slot) := by
      intro slot
      fin_cases slot
      · exact ⟨houtcome.ready.queryStart, by
          simpa [instruction, cleanupValues, denseInstructionCleanupValue,
            instructionCleanupParentSlot] using! houtcome.ready.query⟩
      · change (work tapes.data.update.replacement).HasBinaryNat _
        rw [houtcome.replacement]
        simpa [instruction, cleanupValues, denseInstructionCleanupValue,
          address, value] using! htagValue
      · simpa [instruction, cleanupValues, denseInstructionCleanupValue,
          instructionCleanupParentSlot] using! houtcome.found
      · change (work tapes.data.lhs).HasBinaryNat _
        rw [houtcome.frame tapes.data.lhs (fun role =>
            (tapes.data.update_ne_lhs role).symm),
          htagFrame tapes.data.lhs
            (tapes.data.update_ne_lhs 10).symm,
          show updateWork tapes.data.lhs = loadedWork tapes.data.lhs by
            rw [hupdateWork]
            exact Function.update_of_ne
              (tapes.data.update_ne_lhs 7).symm _ _,
          show loadedWork tapes.data.lhs = addressWork tapes.data.lhs from
            hloaded.querySource]
        simpa [instruction, cleanupValues, denseInstructionCleanupValue,
          address] using! haddress.destination
      · change (work tapes.data.rhs).HasBinaryNat _
        rw [houtcome.frame tapes.data.rhs (fun role =>
            (tapes.data.update_ne_rhs role).symm),
          htagFrame tapes.data.rhs
            (tapes.data.update_ne_rhs 10).symm,
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
      have hqueryNe :
          tapes.data.shift ≠ tapes.data.update.entry.query :=
        (tapes.data.update_ne_shift 7).symm
      rw [houtcome.frame tapes.data.shift (fun slot =>
            (tapes.data.update_ne_shift slot).symm),
        htagFrame tapes.data.shift (tapes.data.update_ne_shift 10).symm,
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
        htagFrame tapes.data.tmp (tapes.data.update_ne_tmp 10).symm,
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
        htagFrame tapes.data.dbl (tapes.data.update_ne_dbl 10).symm,
        hupdateWork, Function.update_of_ne hqueryNe,
        hloaded.frame tapes.data.dbl (fun slot => by
          apply tapes.data.ne
          fin_cases slot <;> decide),
        haddress.frame tapes.data.dbl (fun slot =>
          (tapes.data.lhsLookup_ne_dbl slot).symm)]
      exact hready.dbl
    refine ⟨hpcOutcome.trans (hpcTag.trans (hpcUpdate.trans
      (hpcLoaded.trans hpcAddress))), ?_, hsourceContent, hcleanup,
      ?_, ?_, hshift, htmp', hdbl', houtcome.ready.parked⟩
    · simpa [nextStore, DenseOverlay.write] using! houtcome.resultCount
    · simpa using! houtcome.remaining
    · simpa [instruction, cleanupValues, denseInstructionCleanupValue]
        using! houtcome.ready
  have hdata := retargetBufferedDataKernel_hoareTime_frame_internal tapes
    overlay nextStore cleanupValues 0 pcValue initialWork inp₀
    (denseIndirectLoadInstructionTM tapes.data destination addressRegister)
    (denseIndirectLoadInstructionTime tapes.data input overlay destination
      addressRegister) Result hready hbase hresult
  have hall := finishBufferedDataTM_hoareTime_frame_internal tapes overlay
    nextStore (pcValue + 1) pcValue cleanupValues 0 initialWork inp₀
    (denseIndirectLoadInstructionTM tapes.data destination addressRegister)
    (denseIndirectLoadInstructionTime tapes.data input overlay destination
      addressRegister) rfl hinput hdata
  simpa [instruction, denseExecuteInstructionTM,
    denseExecuteInstructionTime, DenseInstructionExecutionResult,
    denseInstructionStore, denseInstructionPC,
    DenseOverlay.Snapshot.stepInstr, nextStore, cleanupValues, address,
    value] using! hall

/-- The dense-store endpoint supplies every frame and cleanup invariant for buffering. -/
private theorem denseStore_buffered_result
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue addressRegister source : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    ∀ work, DenseIndirectStoreInstructionResult tapes.data input overlay
        addressRegister source (fun i => initialWork (Fin.castSucc i)) work →
      work tapes.pc = initialWork (Fin.castSucc tapes.pc) ∧
      (work tapes.data.update.resultCount).HasBinaryNat
        (DenseOverlay.write overlay (DenseOverlay.read input overlay addressRegister)
          (DenseOverlay.read input overlay source)).length ∧
      (work tapes.data.update.entry.source).HasBinaryContent
        (overlay.flatMap Entry.encode) ∧
      (∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (denseInstructionCleanupValue input (.store addressRegister source) overlay slot)) ∧
      (work tapes.data.update.remaining).HasBinaryNat 0 ∧
      EntryScanReady tapes.data.update.entry []
        (denseInstructionCleanupValue input (.store addressRegister source) overlay 0).bits
        work work ∧
      (work tapes.data.shift).HasBinaryNat 0 ∧
      (work tapes.data.tmp).HasBinaryNat 0 ∧
      (work tapes.data.dbl).HasBinaryNat 0 ∧
      ∀ i, TM.Parked (work i) := by
  let baseWork : Fin n → Tape := fun i => initialWork (Fin.castSucc i)
  let instruction : Instr := .store addressRegister source
  let address := DenseOverlay.read input overlay addressRegister
  let value := DenseOverlay.read input overlay source
  let nextStore := DenseOverlay.write overlay address value
  let cleanupValues := denseInstructionCleanupValue input instruction overlay
  intro work hsemantic
  obtain ⟨operandsWork, queryWork, updateWork, hoperands, hqueryWork,
    hupdateWork, htagged⟩ := hsemantic
  obtain ⟨lhsWork, hlhs, hrhsResult⟩ := hoperands
  obtain ⟨taggedWork, htagValue, htagFrame, houtcome,
    hsourceCells⟩ := htagged
  have hpcOutcome : work tapes.pc = taggedWork tapes.pc :=
    houtcome.frame tapes.pc (fun slot => by
      exact tapes.pc_ne ⟨slot, by omega⟩)
  have hpcTag : taggedWork tapes.pc = updateWork tapes.pc :=
    htagFrame tapes.pc (tapes.pc_ne 10)
  have hpcReplacement :
      tapes.pc ≠ tapes.data.update.replacement := tapes.pc_ne 10
  have hpcUpdate : updateWork tapes.pc = queryWork tapes.pc := by
    rw [hupdateWork, Function.update_of_ne hpcReplacement]
  have hpcQuery :
      tapes.pc ≠ tapes.data.update.entry.query := tapes.pc_ne 7
  have hpcQueryWork : queryWork tapes.pc = operandsWork tapes.pc := by
    rw [hqueryWork, Function.update_of_ne hpcQuery]
  have hpcRhs : operandsWork tapes.pc = lhsWork tapes.pc :=
    hrhsResult.frame tapes.pc (fun slot => by
      exact tapes.pc_ne (BinaryInstructionTapes.rhsLookupSlot slot))
  have hpcLhs : lhsWork tapes.pc = baseWork tapes.pc :=
    hlhs.frame tapes.pc (fun slot => by
      exact tapes.pc_ne (BinaryInstructionTapes.lhsLookupSlot slot))
  have hsourceContent :
      (work tapes.data.update.entry.source).HasBinaryContent
        (overlay.flatMap Entry.encode) := by
    have hcells : (work tapes.data.update.entry.source).cells =
        (baseWork tapes.data.update.entry.source).cells := by
      calc
        (work tapes.data.update.entry.source).cells =
            (updateWork tapes.data.update.entry.source).cells :=
          hsourceCells
        _ = (queryWork tapes.data.update.entry.source).cells := by
          congr 1
          rw [hupdateWork]
          exact Function.update_of_ne
            (tapes.data.update.ne (by decide)) _ _
        _ = (operandsWork tapes.data.update.entry.source).cells := by
          congr 1
          rw [hqueryWork]
          exact Function.update_of_ne
            (tapes.data.update.ne (by decide)) _ _
        _ = (lhsWork tapes.data.update.entry.source).cells :=
          hrhsResult.sourceCells
        _ = (baseWork tapes.data.update.entry.source).cells :=
          hlhs.sourceCells
    unfold Tape.HasBinaryContent
    rw [hcells]
    exact hready.sourceContent
  have hcleanup : ∀ slot,
      (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
        (cleanupValues slot) := by
    intro slot
    fin_cases slot
    · exact ⟨houtcome.ready.queryStart, by
        simpa [instruction, cleanupValues, denseInstructionCleanupValue,
          instructionCleanupParentSlot, address] using!
          houtcome.ready.query⟩
    · change (work tapes.data.update.replacement).HasBinaryNat _
      rw [houtcome.replacement]
      simpa [instruction, cleanupValues, denseInstructionCleanupValue,
        value] using! htagValue
    · simpa [instruction, cleanupValues, denseInstructionCleanupValue,
        instructionCleanupParentSlot, address] using! houtcome.found
    · change (work tapes.data.lhs).HasBinaryNat _
      rw [houtcome.frame tapes.data.lhs (fun role =>
          (tapes.data.update_ne_lhs role).symm),
        htagFrame tapes.data.lhs
          (tapes.data.update_ne_lhs 10).symm,
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
      simpa [instruction, cleanupValues, denseInstructionCleanupValue,
        address] using! hlhs.destination
    · change (work tapes.data.rhs).HasBinaryNat _
      rw [houtcome.frame tapes.data.rhs (fun role =>
          (tapes.data.update_ne_rhs role).symm),
        htagFrame tapes.data.rhs
          (tapes.data.update_ne_rhs 10).symm,
        show updateWork tapes.data.rhs = queryWork tapes.data.rhs by
          rw [hupdateWork]
          exact Function.update_of_ne
            (tapes.data.update_ne_rhs 10).symm _ _,
        show queryWork tapes.data.rhs = operandsWork tapes.data.rhs by
          rw [hqueryWork]
          exact Function.update_of_ne
            (tapes.data.update_ne_rhs 7).symm _ _]
      simpa [instruction, cleanupValues, denseInstructionCleanupValue,
        value] using! hrhsResult.destination
  have hshift : (work tapes.data.shift).HasBinaryNat 0 := by
    have hreplacementNe :
        tapes.data.shift ≠ tapes.data.update.replacement :=
      (tapes.data.update_ne_shift 10).symm
    have hqueryNe :
        tapes.data.shift ≠ tapes.data.update.entry.query :=
      (tapes.data.update_ne_shift 7).symm
    rw [houtcome.frame tapes.data.shift (fun slot =>
          (tapes.data.update_ne_shift slot).symm),
      htagFrame tapes.data.shift hreplacementNe,
      hupdateWork, Function.update_of_ne hreplacementNe,
      hqueryWork, Function.update_of_ne hqueryNe]
    simpa using! hrhsResult.querySource
  have htmp' : (work tapes.data.tmp).HasBinaryNat 0 := by
    have hreplacementNe :
        tapes.data.tmp ≠ tapes.data.update.replacement :=
      (tapes.data.update_ne_tmp 10).symm
    have hqueryNe : tapes.data.tmp ≠
        tapes.data.update.entry.query :=
      (tapes.data.update_ne_tmp 7).symm
    rw [houtcome.frame tapes.data.tmp (fun slot =>
          (tapes.data.update_ne_tmp slot).symm),
      htagFrame tapes.data.tmp hreplacementNe,
      hupdateWork, Function.update_of_ne hreplacementNe,
      hqueryWork, Function.update_of_ne hqueryNe,
      hrhsResult.frame tapes.data.tmp (fun slot =>
        (tapes.data.rhsLookup_ne_tmp slot).symm),
      hlhs.frame tapes.data.tmp (fun slot =>
        (tapes.data.lhsLookup_ne_tmp slot).symm)]
    exact hready.tmp
  have hdbl' : (work tapes.data.dbl).HasBinaryNat 0 := by
    have hreplacementNe :
        tapes.data.dbl ≠ tapes.data.update.replacement :=
      (tapes.data.update_ne_dbl 10).symm
    have hqueryNe : tapes.data.dbl ≠
        tapes.data.update.entry.query :=
      (tapes.data.update_ne_dbl 7).symm
    rw [houtcome.frame tapes.data.dbl (fun slot =>
          (tapes.data.update_ne_dbl slot).symm),
      htagFrame tapes.data.dbl hreplacementNe,
      hupdateWork, Function.update_of_ne hreplacementNe,
      hqueryWork, Function.update_of_ne hqueryNe,
      hrhsResult.frame tapes.data.dbl (fun slot =>
        (tapes.data.rhsLookup_ne_dbl slot).symm),
      hlhs.frame tapes.data.dbl (fun slot =>
        (tapes.data.lhsLookup_ne_dbl slot).symm)]
    exact hready.dbl
  refine ⟨hpcOutcome.trans (hpcTag.trans (hpcUpdate.trans
    (hpcQueryWork.trans (hpcRhs.trans hpcLhs)))), ?_, hsourceContent,
    hcleanup, ?_, ?_, hshift, htmp', hdbl', houtcome.ready.parked⟩
  · simpa [nextStore, DenseOverlay.write] using! houtcome.resultCount
  · simpa using! houtcome.remaining
  · simpa [instruction, cleanupValues, denseInstructionCleanupValue,
      address] using! houtcome.ready

/-- A dense indirect store produces the generic buffered endpoint and advances
the program counter. -/
theorem denseExecuteInstructionTM_store_hoareTime_frame
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue addressRegister source : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseExecuteInstructionTM tapes
      (.store addressRegister source)).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseInstructionExecutionResult tapes input
          (.store addressRegister source) pcValue overlay work ∧
        out = (Tape.init []).move Dir3.right)
      (denseExecuteInstructionTime tapes input
        (.store addressRegister source) pcValue overlay) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let baseWork : Fin n → Tape := fun i => initialWork (Fin.castSucc i)
  let instruction : Instr := .store addressRegister source
  let address := DenseOverlay.read input overlay addressRegister
  let value := DenseOverlay.read input overlay source
  let nextStore := DenseOverlay.write overlay address value
  let cleanupValues := denseInstructionCleanupValue input instruction overlay
  have hinput : TM.Parked inp₀ := by
    refine ⟨by simp [inp₀, Tape.move], ?_⟩
    simpa [inp₀] using! Tape.init_ofBool_move_right_cells_ne_start input
  have hlookup : EntryLookupStaticReady tapes.data.lhsLookup overlay
      baseWork :=
    instructionExecutionReady_baseLookup_internal tapes overlay pcValue
      initialWork hready
  have hrhs : (baseWork tapes.data.rhs).HasBinaryNat 0 := hready.rhs
  have hreplacement :
      (baseWork tapes.data.update.replacement).HasBinaryNat 0 :=
    hready.replacement
  have hbuffer : (initialWork tapes.buffer).HasBinaryPrefix [] := by
    rw [hready.buffer]
    exact Tape.init_nil_move_right_hasBinaryPrefix_nil
  have hbaseRaw := denseIndirectStoreInstructionTM_hoareTime_frame tapes.data
    input overlay addressRegister source [] baseWork
    (initialWork tapes.buffer) hvalid hlookup hrhs hreplacement hbuffer
  let Result : (Fin n → Tape) → Prop := fun work =>
    DenseIndirectStoreInstructionResult tapes.data input overlay
      addressRegister source baseWork work
  have hbase : (denseIndirectStoreInstructionTM tapes.data addressRegister
      source).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = baseWork ∧ out = initialWork tapes.buffer)
      (fun inp work out =>
        inp = inp₀ ∧ Result work ∧
        out.HasBinaryPrefix (nextStore.flatMap Entry.encode))
      (denseIndirectStoreInstructionTime tapes.data input overlay
        addressRegister source) := by
    simpa [Result, address, value, nextStore] using! hbaseRaw
  have hresult : ∀ work, Result work →
      work tapes.pc = initialWork (Fin.castSucc tapes.pc) ∧
      (work tapes.data.update.resultCount).HasBinaryNat nextStore.length ∧
      (work tapes.data.update.entry.source).HasBinaryContent
        (overlay.flatMap Entry.encode) ∧
      (∀ slot,
        (work (tapes.data.idx (instructionCleanupParentSlot slot))).HasBinaryNat
          (cleanupValues slot)) ∧
      (work tapes.data.update.remaining).HasBinaryNat 0 ∧
      EntryScanReady tapes.data.update.entry [] (cleanupValues 0).bits
        work work ∧
      (work tapes.data.shift).HasBinaryNat 0 ∧
      (work tapes.data.tmp).HasBinaryNat 0 ∧
      (work tapes.data.dbl).HasBinaryNat 0 ∧
      ∀ i, TM.Parked (work i) :=
    denseStore_buffered_result tapes input overlay pcValue addressRegister source
      initialWork hready
  have hdata := retargetBufferedDataKernel_hoareTime_frame_internal tapes
    overlay nextStore cleanupValues 0 pcValue initialWork inp₀
    (denseIndirectStoreInstructionTM tapes.data addressRegister source)
    (denseIndirectStoreInstructionTime tapes.data input overlay
      addressRegister source) Result hready hbase hresult
  have hall := finishBufferedDataTM_hoareTime_frame_internal tapes overlay
    nextStore (pcValue + 1) pcValue cleanupValues 0 initialWork inp₀
    (denseIndirectStoreInstructionTM tapes.data addressRegister source)
    (denseIndirectStoreInstructionTime tapes.data input overlay
      addressRegister source) rfl hinput hdata
  simpa [instruction, denseExecuteInstructionTM,
    denseExecuteInstructionTime, DenseInstructionExecutionResult,
    denseInstructionStore, denseInstructionPC,
    DenseOverlay.Snapshot.stepInstr, nextStore, cleanupValues, address,
    value] using! hall

end Machine
end RegisterStore
end RAM
end Complexity
