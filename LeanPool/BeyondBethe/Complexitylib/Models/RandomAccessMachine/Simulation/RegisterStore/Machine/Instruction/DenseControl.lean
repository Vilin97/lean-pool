/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseDefs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Control

/-!
# Dense-overlay control instructions
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

private theorem phaseTransition_of_parked
    {inp out : Tape} {work : Fin n → Tape}
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    TM.transitionInput inp = inp ∧
      (fun i => TM.transitionTape (work i)) = work ∧
      TM.transitionTape out = out :=
  TM.phaseTransition_eq_self_of_reads_ne_start hinput.read_ne_start
    (fun i => (hwork i).read_ne_start) houtput.read_ne_start

private def DenseZeroJumpBranchResult
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (source newPC : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  ∃ lookupWork : Fin n → Tape,
    DenseOverlayLookupStaticResult tapes.data.lhsLookup input overlay source
      initialWork lookupWork ∧
    (finalWork tapes.data.lhs).HasBinaryNat
      (DenseOverlay.read input overlay source) ∧
    (finalWork tapes.pc).HasBinaryNat newPC ∧
    (∀ i, TM.Parked (finalWork i)) ∧
    ∀ i, i ≠ tapes.pc → finalWork i = lookupWork i

private theorem denseControlResult_of_zeroJumpReset
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (oldPC source newPC : ℕ)
    (initialWork branchWork : Fin n → Tape)
    (hinitial : ControlInstructionReady tapes overlay oldPC initialWork)
    (hbranch : DenseZeroJumpBranchResult tapes input overlay source newPC
      initialWork branchWork) :
    ControlInstructionResult tapes overlay newPC initialWork
      (Function.update branchWork tapes.data.lhs
        ((Tape.init []).move Dir3.right)) := by
  obtain ⟨lookupWork, hlookup, hoperand, hpc, hparked, hframe⟩ := hbranch
  let finalWork := Function.update branchWork tapes.data.lhs
    ((Tape.init []).move Dir3.right)
  have hrole (slot : Fin 14) (hslot : slot ≠ 12) :
      finalWork (tapes.data.lhsLookup.idx slot) =
        lookupWork (tapes.data.lhsLookup.idx slot) := by
    have hneLhs : tapes.data.lhsLookup.idx slot ≠ tapes.data.lhs := by
      intro heq
      apply hslot
      apply tapes.data.lhsLookup.injective
      exact heq
    simp only [finalWork, Function.update_of_ne hneLhs]
    exact hframe _ (tapes.lookup_ne_pc slot)
  have hfinalParked : ∀ i, TM.Parked (finalWork i) := by
    intro i
    by_cases hi : i = tapes.data.lhs
    · subst i
      simp only [finalWork, Function.update_self]
      exact hasBinaryNat_parked (Tape.init_move_right_hasBinaryNat 0)
    · simpa only [finalWork, Function.update_of_ne hi] using hparked i
  have hscanner : EntryScanReady tapes.data.lhsLookup.scan.entry
      (overlay.flatMap Entry.encode) [] finalWork finalWork := by
    refine
      { source := ?_
        address := ?_
        addressStart := ?_
        value := ?_
        valueStart := ?_
        addressCounter := ?_
        addressWidth := ?_
        valueCounter := ?_
        valueWidth := ?_
        query := ?_
        queryStart := ?_
        result := ?_
        resultStart := ?_
        parked := hfinalParked
        frame := by intro i _ _ _ _ _ _ _ _ _; rfl }
    · change (finalWork (tapes.data.lhsLookup.idx 0)).HasBinarySuffix _
      rw [hrole 0 (by decide)]
      exact hlookup.scanner.source
    · change (finalWork (tapes.data.lhsLookup.idx 1)).HasBinaryPrefix []
      rw [hrole 1 (by decide)]
      exact hlookup.scanner.address
    · change (finalWork (tapes.data.lhsLookup.idx 1)).cells 0 = Γ.start
      rw [hrole 1 (by decide)]
      exact hlookup.scanner.addressStart
    · change (finalWork (tapes.data.lhsLookup.idx 2)).HasBinaryPrefix []
      rw [hrole 2 (by decide)]
      exact hlookup.scanner.value
    · change (finalWork (tapes.data.lhsLookup.idx 2)).cells 0 = Γ.start
      rw [hrole 2 (by decide)]
      exact hlookup.scanner.valueStart
    · change (finalWork (tapes.data.lhsLookup.idx 3)).HasBinaryNat 0
      rw [hrole 3 (by decide)]
      exact hlookup.scanner.addressCounter
    · change (finalWork (tapes.data.lhsLookup.idx 4)).HasBinaryNat 0
      rw [hrole 4 (by decide)]
      exact hlookup.scanner.addressWidth
    · change (finalWork (tapes.data.lhsLookup.idx 5)).HasBinaryNat 0
      rw [hrole 5 (by decide)]
      exact hlookup.scanner.valueCounter
    · change (finalWork (tapes.data.lhsLookup.idx 6)).HasBinaryNat 0
      rw [hrole 6 (by decide)]
      exact hlookup.scanner.valueWidth
    · change (finalWork (tapes.data.lhsLookup.idx 7)).HasBinaryString []
      rw [hrole 7 (by decide)]
      exact hlookup.scanner.query
    · change (finalWork (tapes.data.lhsLookup.idx 7)).cells 0 = Γ.start
      rw [hrole 7 (by decide)]
      exact hlookup.scanner.queryStart
    · change (finalWork (tapes.data.lhsLookup.idx 8)).HasBinaryPrefix []
      rw [hrole 8 (by decide)]
      exact hlookup.scanner.result
    · change (finalWork (tapes.data.lhsLookup.idx 8)).cells 0 = Γ.start
      rw [hrole 8 (by decide)]
      exact hlookup.scanner.resultStart
  have hfinalReady : ControlInstructionReady tapes overlay newPC finalWork := by
    refine
      { lookup :=
          { scanner := hscanner
            sourceStart := ?_
            sourceHead := ?_
            count := ?_
            countSource := ?_
            querySource := ?_
            destination := ?_
            copyScratch := ?_ }
        pc := ?_ }
    · change (finalWork (tapes.data.lhsLookup.idx 0)).cells 0 = Γ.start
      rw [hrole 0 (by decide)]
      exact hlookup.sourceStart
    · change (finalWork (tapes.data.lhsLookup.idx 0)).head = 1
      rw [hrole 0 (by decide)]
      exact hlookup.sourceHead
    · change (finalWork (tapes.data.lhsLookup.idx 9)).HasBinaryNat _
      rw [hrole 9 (by decide)]
      exact hlookup.count
    · change (finalWork (tapes.data.lhsLookup.idx 10)).HasBinaryNat _
      rw [hrole 10 (by decide)]
      rw [show lookupWork (tapes.data.lhsLookup.idx 10) =
          initialWork (tapes.data.lhsLookup.idx 10) by
        simpa using hlookup.countSource]
      exact hinitial.lookup.countSource
    · change (finalWork (tapes.data.lhsLookup.idx 11)).HasBinaryNat 0
      rw [hrole 11 (by decide)]
      exact hlookup.querySource
    · change (finalWork tapes.data.lhs).HasBinaryNat 0
      simp only [finalWork, Function.update_self]
      exact Tape.init_move_right_hasBinaryNat 0
    · change (finalWork (tapes.data.lhsLookup.idx 13)).HasBinaryNat 0
      rw [hrole 13 (by decide)]
      exact hlookup.copyScratch
    · simpa only [finalWork, Function.update_of_ne tapes.pc_ne_lhs] using hpc
  refine
    { ready := hfinalReady
      sourceCells := ?_
      frame := ?_ }
  · change (finalWork (tapes.data.lhsLookup.idx 0)).cells =
      (initialWork (tapes.data.lhsLookup.idx 0)).cells
    rw [hrole 0 (by decide)]
    exact hlookup.sourceCells
  · intro i hipc hdata
    have hiLhs : i ≠ tapes.data.lhs := hdata 12
    simp only [Function.update_of_ne hiLhs]
    rw [hframe i hipc]
    exact hlookup.frame i hdata

/-- A dense-overlay conditional read implements `jz` and restores the shared
lookup ABI after the program-counter branch. -/
theorem denseZeroJumpInstructionTM_hoareTime_frame
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue source target : ℕ)
    (initialWork : Fin n → Tape) (out₀ : Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : ControlInstructionReady tapes overlay pcValue initialWork)
    (houtput : TM.Parked out₀) :
    (denseZeroJumpInstructionTM tapes source target).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        ControlInstructionResult tapes overlay
          (if DenseOverlay.read input overlay source = 0 then target
            else pcValue + 1)
          initialWork work ∧ out = out₀)
      (denseZeroJumpInstructionTime tapes input overlay pcValue source
        target) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let value := DenseOverlay.read input overlay source
  let newPC := if value = 0 then target else pcValue + 1
  let lookupPost : TM.TapePred n := fun inp work out =>
    inp = inp₀ ∧
      DenseOverlayLookupStaticResult tapes.data.lhsLookup input overlay source
        initialWork work ∧ out = out₀
  let branchPost : TM.TapePred n := fun inp work out =>
    inp = inp₀ ∧
      DenseZeroJumpBranchResult tapes input overlay source newPC initialWork
        work ∧ out = out₀
  have hinput : TM.Parked inp₀ := by
    refine ⟨by simp [inp₀, Tape.move], ?_⟩
    simpa [inp₀] using Tape.init_ofBool_move_right_cells_ne_start input
  have hlookup := denseOverlayLookupStaticTM_hoareTime_frame
    tapes.data.lhsLookup input overlay source initialWork out₀ hvalid
    hready.lookup houtput
  have hbranch :
      (TM.branchWorkBlankTM tapes.data.lhs
        (setProgramCounterTM tapes.pc target)
        (TM.binarySuccTM tapes.pc)).HoareTime lookupPost branchPost
      (TM.branchWorkBlankTime (setProgramCounterTime pcValue target)
        (TM.binarySuccTime pcValue)) := by
    let blankPre : TM.TapePred n := fun inp work out =>
      lookupPost inp work out ∧ value = 0
    let nonblankPre : TM.TapePred n := fun inp work out =>
      lookupPost inp work out ∧ value ≠ 0
    have hblank : (setProgramCounterTM tapes.pc target).HoareTime
        blankPre branchPost (setProgramCounterTime pcValue target) := by
      rintro inp work out ⟨⟨hinp, hlookupResult, hout⟩, hzero⟩
      have hpcWork : (work tapes.pc).HasBinaryNat pcValue := by
        rw [hlookupResult.frame tapes.pc
          (fun slot => (tapes.lookup_ne_pc slot).symm)]
        exact hready.pc
      have hset := setProgramCounterTM_hoareTime_frame_internal tapes.pc
        pcValue target inp work out hpcWork
        (by simpa [hinp] using hinput)
        hlookupResult.parked (by simpa [hout] using houtput)
      obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
          hfinalWork, hfinalOutput⟩ := hset inp work out ⟨rfl, rfl, rfl⟩
      refine ⟨final, time, htime, hreach, hhalt,
        hfinalInput.trans hinp, ?_, hfinalOutput.trans hout⟩
      rw [hfinalWork]
      let targetTape :=
        (Tape.init (target.bits.map Γ.ofBool)).move Dir3.right
      have htarget : targetTape.HasBinaryNat target :=
        Tape.init_move_right_hasBinaryNat target
      refine ⟨work, hlookupResult, ?_, ?_, ?_, ?_⟩
      · simpa only [Function.update_of_ne tapes.lhs_ne_pc, value] using
          hlookupResult.destination
      · simpa only [targetTape, Function.update_self, newPC, hzero, ite_eq_left]
          using htarget
      · intro i
        by_cases hi : i = tapes.pc
        · subst i
          simpa only [targetTape, Function.update_self] using
            hasBinaryNat_parked htarget
        · simpa only [targetTape, Function.update_of_ne hi] using
            hlookupResult.parked i
      · intro i hi
        exact Function.update_of_ne hi _ work
    have hnonblank : (TM.binarySuccTM tapes.pc).HoareTime
        nonblankPre branchPost (TM.binarySuccTime pcValue) := by
      rintro inp work out ⟨⟨hinp, hlookupResult, hout⟩, hnonzero⟩
      have hpcWork : (work tapes.pc).HasBinaryNat pcValue := by
        rw [hlookupResult.frame tapes.pc
          (fun slot => (tapes.lookup_ne_pc slot).symm)]
        exact hready.pc
      have hsucc := TM.binarySuccTM_hoareTime_frame tapes.pc pcValue inp
        work out hpcWork (by simpa [hinp] using hinput.read_ne_start)
        (fun i _ => (hlookupResult.parked i).read_ne_start)
        (by simpa [hout] using houtput.read_ne_start)
      obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
          hframe, hfinalPC, hfinalOutput⟩ :=
        hsucc inp work out ⟨rfl, rfl, rfl⟩
      refine ⟨final, time, htime, hreach, hhalt,
        hfinalInput.trans hinp, ?_, hfinalOutput.trans hout⟩
      refine ⟨work, hlookupResult, ?_, ?_, ?_, hframe⟩
      · rw [hframe tapes.data.lhs tapes.lhs_ne_pc]
        simpa only [value] using hlookupResult.destination
      · simpa only [newPC, ite_eq_right hnonzero] using hfinalPC
      · intro i
        by_cases hi : i = tapes.pc
        · subst i
          exact hasBinaryNat_parked hfinalPC
        · rw [hframe i hi]
          exact hlookupResult.parked i
    have hdispatch := TM.branchWorkBlankTM_hoareTime tapes.data.lhs
      (setProgramCounterTM tapes.pc target) (TM.binarySuccTM tapes.pc)
      (pre := lookupPost) (blankPre := blankPre)
      (nonblankPre := nonblankPre) (blankPost := branchPost)
      (nonblankPost := branchPost)
      (fun inp work out hpre =>
        ⟨(by simpa [hpre.1] using hinput.read_ne_start),
          fun i => (hpre.2.1.parked i).read_ne_start,
          by simpa [hpre.2.2] using houtput.read_ne_start⟩)
      (fun _ _ _ hpre hread =>
        ⟨hpre, hpre.2.1.destination.read_eq_blank_iff.mp hread⟩)
      (fun _ _ _ hpre hread =>
        ⟨hpre, fun hzero =>
          hread (hpre.2.1.destination.read_eq_blank_iff.mpr hzero)⟩)
      hblank hnonblank
    exact hdispatch.consequence (fun _ _ _ h => h)
      (fun _ _ _ h => h.elim id id) le_rfl
  have hreset : (TM.resetBinaryWorkTM tapes.data.lhs).HoareTime branchPost
      (fun inp work out =>
        inp = inp₀ ∧
        ControlInstructionResult tapes overlay newPC initialWork work ∧
        out = out₀)
      (TM.resetBinaryWorkTime 1 value.bits.length) := by
    rintro inp work out ⟨hinp, hbranchResult, hout⟩
    obtain ⟨lookupWork, hlookupResult, hoperand, hpcResult,
      hparked, hframe⟩ := hbranchResult
    have hrun := TM.resetBinaryWorkTM_hoareTime_frame tapes.data.lhs
      value.bits 1 inp work out hoperand.2.hasBinaryContent hoperand.1
      ⟨by rw [hoperand.2.1], by rw [hoperand.2.1]⟩
      (by simpa [hinp] using hinput)
      (fun i _ => hparked i) (by simpa [hout] using houtput)
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hfinalWork, hfinalOutput⟩ := hrun inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨final, time, htime, hreach, hhalt,
      hfinalInput.trans hinp, ?_, hfinalOutput.trans hout⟩
    rw [hfinalWork]
    exact denseControlResult_of_zeroJumpReset tapes input overlay pcValue
      source newPC initialWork work hready
      ⟨lookupWork, hlookupResult, hoperand, hpcResult, hparked, hframe⟩
  have hbranchReset := TM.seqTM_hoareTime
    (TM.branchWorkBlankTM tapes.data.lhs
      (setProgramCounterTM tapes.pc target) (TM.binarySuccTM tapes.pc))
    (TM.resetBinaryWorkTM tapes.data.lhs) hbranch
    (by
      rintro inp work out ⟨hinp, hbranchResult, hout⟩
      obtain ⟨lookupWork, hlookupResult, hoperand, hpcResult,
        hparked, hframe⟩ := hbranchResult
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using hinput) hparked
        (by simpa [hout] using houtput)
      rw [hi, hw, ho]
      exact ⟨hinp,
        ⟨lookupWork, hlookupResult, hoperand, hpcResult, hparked, hframe⟩,
        hout⟩)
    hreset
  have hall := TM.seqTM_hoareTime
    (denseOverlayLookupStaticTM tapes.data.lhsLookup source)
    (TM.seqTM
      (TM.branchWorkBlankTM tapes.data.lhs
        (setProgramCounterTM tapes.pc target) (TM.binarySuccTM tapes.pc))
      (TM.resetBinaryWorkTM tapes.data.lhs)) hlookup
    (by
      rintro inp work out ⟨hinp, hlookupResult, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [inp₀, hinp] using hinput) hlookupResult.parked
        (by simpa [hout] using houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, hlookupResult, hout⟩)
    hbranchReset
  simpa [denseZeroJumpInstructionTM, denseZeroJumpInstructionTime, inp₀,
    value, newPC] using hall

end Machine
end RegisterStore
end RAM
end Complexity
