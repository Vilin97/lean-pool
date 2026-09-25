/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryLookupRestore

/-!
# Sparse-store control instructions

This proof layer realizes conditional-zero jump, unconditional jump, and halt
over the reusable sparse-lookup ABI and a disjoint canonical binary program-
counter tape.
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

private theorem phaseTransition_of_parked
    {inp out : Tape} {work : Fin n → Tape}
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    TM.transitionInput inp = inp ∧
      (fun i => TM.transitionTape (work i)) = work ∧
      TM.transitionTape out = out :=
  TM.phaseTransition_of_parked hinput hwork houtput

private theorem controlReady_update_pc
    (tapes : ControlInstructionTapes n) (store : Store)
    (oldPC newPC : ℕ) (work : Fin n → Tape) (newTape : Tape)
    (hready : ControlInstructionReady tapes store oldPC work)
    (hnewTape : newTape.HasBinaryNat newPC) :
    ControlInstructionReady tapes store newPC
      (Function.update work tapes.pc newTape) := by
  let finalWork := Function.update work tapes.pc newTape
  have hsourceNe : tapes.data.lhsLookup.scan.entry.source ≠ tapes.pc := by
    exact tapes.lookup_ne_pc 0
  have haddressNe : tapes.data.lhsLookup.scan.entry.address ≠ tapes.pc := by
    exact tapes.lookup_ne_pc 1
  have hvalueNe : tapes.data.lhsLookup.scan.entry.value ≠ tapes.pc := by
    exact tapes.lookup_ne_pc 2
  have haddressCounterNe :
      tapes.data.lhsLookup.scan.entry.addressCounter ≠ tapes.pc := by
    exact tapes.lookup_ne_pc 3
  have haddressWidthNe :
      tapes.data.lhsLookup.scan.entry.addressWidth ≠ tapes.pc := by
    exact tapes.lookup_ne_pc 4
  have hvalueCounterNe :
      tapes.data.lhsLookup.scan.entry.valueCounter ≠ tapes.pc := by
    exact tapes.lookup_ne_pc 5
  have hvalueWidthNe :
      tapes.data.lhsLookup.scan.entry.valueWidth ≠ tapes.pc := by
    exact tapes.lookup_ne_pc 6
  have hqueryNe : tapes.data.lhsLookup.scan.entry.query ≠ tapes.pc := by
    exact tapes.lookup_ne_pc 7
  have hresultNe : tapes.data.lhsLookup.scan.entry.result ≠ tapes.pc := by
    exact tapes.lookup_ne_pc 8
  have hcountNe : tapes.data.lhsLookup.scan.count ≠ tapes.pc := by
    exact tapes.lookup_ne_pc 9
  have hcountSourceNe : tapes.data.lhsLookup.countSource ≠ tapes.pc := by
    exact tapes.lookup_ne_pc 10
  have hquerySourceNe : tapes.data.lhsLookup.querySource ≠ tapes.pc := by
    exact tapes.lookup_ne_pc 11
  have hdestinationNe : tapes.data.lhsLookup.destination ≠ tapes.pc := by
    exact tapes.lookup_ne_pc 12
  have hcopyScratchNe : tapes.data.lhsLookup.copyScratch ≠ tapes.pc := by
    exact tapes.lookup_ne_pc 13
  have hscanner : EntryScanReady tapes.data.lhsLookup.scan.entry
      (store.flatMap Entry.encode) [] finalWork finalWork := by
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
        parked := ?_
        frame := by intro i _ _ _ _ _ _ _ _ _; rfl }
    · simpa only [finalWork, Function.update_of_ne hsourceNe] using
        hready.lookup.scanner.source
    · simpa only [finalWork, Function.update_of_ne haddressNe] using
        hready.lookup.scanner.address
    · simpa only [finalWork, Function.update_of_ne haddressNe] using
        hready.lookup.scanner.addressStart
    · simpa only [finalWork, Function.update_of_ne hvalueNe] using
        hready.lookup.scanner.value
    · simpa only [finalWork, Function.update_of_ne hvalueNe] using
        hready.lookup.scanner.valueStart
    · simpa only [finalWork, Function.update_of_ne haddressCounterNe] using
        hready.lookup.scanner.addressCounter
    · simpa only [finalWork, Function.update_of_ne haddressWidthNe] using
        hready.lookup.scanner.addressWidth
    · simpa only [finalWork, Function.update_of_ne hvalueCounterNe] using
        hready.lookup.scanner.valueCounter
    · simpa only [finalWork, Function.update_of_ne hvalueWidthNe] using
        hready.lookup.scanner.valueWidth
    · simpa only [finalWork, Function.update_of_ne hqueryNe] using
        hready.lookup.scanner.query
    · simpa only [finalWork, Function.update_of_ne hqueryNe] using
        hready.lookup.scanner.queryStart
    · simpa only [finalWork, Function.update_of_ne hresultNe] using
        hready.lookup.scanner.result
    · simpa only [finalWork, Function.update_of_ne hresultNe] using
        hready.lookup.scanner.resultStart
    · intro i
      by_cases hi : i = tapes.pc
      · subst i
        simpa only [finalWork, Function.update_self] using
          hasBinaryNat_parked hnewTape
      · simpa only [finalWork, Function.update_of_ne hi] using
          hready.lookup.scanner.parked i
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
  · simpa only [finalWork, Function.update_of_ne hsourceNe] using
      hready.lookup.sourceStart
  · simpa only [finalWork, Function.update_of_ne hsourceNe] using
      hready.lookup.sourceHead
  · simpa only [finalWork, Function.update_of_ne hcountNe] using
      hready.lookup.count
  · simpa only [finalWork, Function.update_of_ne hcountSourceNe] using
      hready.lookup.countSource
  · simpa only [finalWork, Function.update_of_ne hquerySourceNe] using
      hready.lookup.querySource
  · simpa only [finalWork, Function.update_of_ne hdestinationNe] using
      hready.lookup.destination
  · simpa only [finalWork, Function.update_of_ne hcopyScratchNe] using
      hready.lookup.copyScratch
  · simpa only [finalWork, Function.update_self] using hnewTape

private def ZeroJumpBranchResult
    (tapes : ControlInstructionTapes n) (store : Store)
    (source newPC : ℕ) (initialWork finalWork : Fin n → Tape) :
    Prop :=
  ∃ lookupWork : Fin n → Tape,
    EntryLookupStaticResult tapes.data.lhsLookup store source
      initialWork lookupWork ∧
    (finalWork tapes.data.lhs).HasBinaryNat
      (RegisterStore.read store source) ∧
    (finalWork tapes.pc).HasBinaryNat newPC ∧
    (∀ i, TM.Parked (finalWork i)) ∧
    ∀ i, i ≠ tapes.pc → finalWork i = lookupWork i

private theorem controlResult_of_zeroJumpReset
    (tapes : ControlInstructionTapes n) (store : Store)
    (oldPC source newPC : ℕ) (initialWork branchWork : Fin n → Tape)
    (hinitial : ControlInstructionReady tapes store oldPC initialWork)
    (hbranch : ZeroJumpBranchResult tapes store source newPC
      initialWork branchWork) :
    ControlInstructionResult tapes store newPC initialWork
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
      (store.flatMap Entry.encode) [] finalWork finalWork := by
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
  have hfinalReady : ControlInstructionReady tapes store newPC finalWork := by
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
      have hcountSource := hlookup.countSource
      change lookupWork (tapes.data.lhsLookup.idx 10) =
        initialWork (tapes.data.lhsLookup.idx 10) at hcountSource
      rw [hcountSource]
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
    · simpa only [finalWork,
        Function.update_of_ne tapes.pc_ne_lhs] using hpc
  refine
    { ready := hfinalReady
      sourceCells := ?_
      frame := ?_ }
  · change (finalWork (tapes.data.lhsLookup.idx 0)).cells =
      (initialWork (tapes.data.lhsLookup.idx 0)).cells
    rw [hrole 0 (by decide)]
    exact hlookup.sourceCells
  intro i hipc hdata
  have hiLhs : i ≠ tapes.data.lhs := hdata 12
  simp only [Function.update_of_ne hiLhs]
  rw [hframe i hipc]
  exact hlookup.frame i hdata

/-- Reset a canonical PC and load a fixed target, preserving the literal
external frame. -/
theorem setProgramCounterTM_hoareTime_frame_internal
    (pc : Fin n) (pcValue target : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hpc : (work₀ pc).HasBinaryNat pcValue)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    (setProgramCounterTM pc target).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ pc
          ((Tape.init (target.bits.map Γ.ofBool)).move Dir3.right) ∧
        out = out₀)
      (setProgramCounterTime pcValue target) := by
  let midWork := Function.update work₀ pc
    ((Tape.init []).move Dir3.right)
  have hreset := TM.resetBinaryWorkTM_hoareTime_frame pc pcValue.bits 1
    inp₀ work₀ out₀ hpc.2.hasBinaryContent hpc.1
    ⟨by rw [hpc.2.1], by rw [hpc.2.1]⟩ hinput
    (fun i _ => hwork i) houtput
  have hreset' : (TM.resetBinaryWorkTM pc).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = midWork ∧ out = out₀)
      (TM.resetBinaryWorkTime 1 pcValue.bits.length) := by
    simpa only [midWork] using hreset
  have hzero : (midWork pc).HasBinaryNat 0 := by
    simp only [midWork, Function.update_self]
    exact Tape.init_move_right_hasBinaryNat 0
  have hmidWork : ∀ i, TM.Parked (midWork i) := by
    intro i
    by_cases hi : i = pc
    · subst i
      exact hasBinaryNat_parked hzero
    · simpa only [midWork, Function.update_of_ne hi] using hwork i
  have hadd := TM.binaryAddConstTM_hoareTime_frame pc target 0 inp₀
    midWork out₀ hzero hinput (fun i _ => hmidWork i) houtput
  have hseq := TM.seqTM_hoareTime (TM.resetBinaryWorkTM pc)
    (TM.binaryAddConstTM pc target) hreset'
    (by
      rintro inp work out ⟨hinp, hworkEq, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using hinput)
        (by simpa [hworkEq] using hmidWork)
        (by simpa [hout] using houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, hworkEq, hout⟩)
    hadd
  simpa only [setProgramCounterTM, setProgramCounterTime, midWork,
    Function.update_idem, Nat.zero_add] using hseq

/-- Unconditional jump replaces the PC and preserves the clean sparse-lookup
boundary. -/
theorem jumpInstructionTM_hoareTime_frame_internal
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue target : ℕ) (initialWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hready : ControlInstructionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (jumpInstructionTM tapes target).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        ControlInstructionResult tapes store target initialWork work ∧
        out = out₀)
      (jumpInstructionTime pcValue target) := by
  have hset := setProgramCounterTM_hoareTime_frame_internal tapes.pc
    pcValue target inp₀ initialWork out₀ hready.pc hinput
    hready.lookup.scanner.parked houtput
  apply hset.consequence
  · exact fun _ _ _ h => h
  · rintro inp work out ⟨hinp, hworkEq, hout⟩
    let targetTape :=
      (Tape.init (target.bits.map Γ.ofBool)).move Dir3.right
    have htarget : targetTape.HasBinaryNat target := by
      exact Tape.init_move_right_hasBinaryNat target
    have hfinalReady := controlReady_update_pc tapes store pcValue target
      initialWork targetTape hready htarget
    refine ⟨hinp, ?_, hout⟩
    rw [hworkEq]
    refine
      { ready := hfinalReady
        sourceCells := ?_
        frame := ?_ }
    · exact congrArg Tape.cells
        (Function.update_of_ne (tapes.lookup_ne_pc 0) targetTape initialWork)
    · intro i hipc _
      simp only [Function.update_of_ne hipc]
  · exact le_rfl

/-- Conditional-zero lookup and PC update realize the sparse interpreter's
`jz` semantics and restore the lookup operand to zero. -/
theorem zeroJumpInstructionTM_hoareTime_frame_internal
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue source target : ℕ) (initialWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hready : ControlInstructionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (zeroJumpInstructionTM tapes source target).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        ControlInstructionResult tapes store
          (if RegisterStore.read store source = 0 then target
            else pcValue + 1)
          initialWork work ∧
        out = out₀)
      (zeroJumpInstructionTime tapes store pcValue source target) := by
  let value := RegisterStore.read store source
  let newPC := if value = 0 then target else pcValue + 1
  let lookupPost : TM.TapePred n := fun inp work out =>
    inp = inp₀ ∧
      EntryLookupStaticResult tapes.data.lhsLookup store source
        initialWork work ∧
      out = out₀
  let branchPost : TM.TapePred n := fun inp work out =>
    inp = inp₀ ∧
      ZeroJumpBranchResult tapes store source newPC
        initialWork work ∧
      out = out₀
  have hlookup := entryLookupStaticTM_hoareTime_frame
    tapes.data.lhsLookup store source initialWork inp₀ out₀ hready.lookup
    hinput houtput
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
        have hpcEq := hlookupResult.frame tapes.pc
          (fun slot => (tapes.lookup_ne_pc slot).symm)
        rw [hpcEq]
        exact hready.pc
      have hset := setProgramCounterTM_hoareTime_frame_internal tapes.pc
        pcValue target inp work out hpcWork
        (by simpa [hinp] using hinput)
        hlookupResult.parked (by simpa [hout] using houtput)
      obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
          hfinalWork, hfinalOutput⟩ :=
        hset inp work out ⟨rfl, rfl, rfl⟩
      refine ⟨final, time, htime, hreach, hhalt, ?_, ?_, ?_⟩
      · exact hfinalInput.trans hinp
      · rw [hfinalWork]
        let targetTape :=
          (Tape.init (target.bits.map Γ.ofBool)).move Dir3.right
        have htarget : targetTape.HasBinaryNat target :=
          Tape.init_move_right_hasBinaryNat target
        refine ⟨work, hlookupResult, ?_, ?_, ?_, ?_⟩
        · have hoperand := hlookupResult.destination
          change (work tapes.data.lhs).HasBinaryNat value at hoperand
          simpa only [Function.update_of_ne tapes.lhs_ne_pc] using hoperand
        · simpa only [targetTape, Function.update_self, newPC, value,
            hzero, ite_eq_left] using htarget
        · intro i
          by_cases hi : i = tapes.pc
          · subst i
            simpa only [targetTape, Function.update_self] using
              hasBinaryNat_parked htarget
          · simpa only [targetTape, Function.update_of_ne hi] using
              hlookupResult.parked i
        · intro i hi
          simp only [Function.update_of_ne hi]
      · exact hfinalOutput.trans hout
    have hnonblank : (TM.binarySuccTM tapes.pc).HoareTime
        nonblankPre branchPost (TM.binarySuccTime pcValue) := by
      rintro inp work out ⟨⟨hinp, hlookupResult, hout⟩, hnonzero⟩
      have hpcWork : (work tapes.pc).HasBinaryNat pcValue := by
        have hpcEq := hlookupResult.frame tapes.pc
          (fun slot => (tapes.lookup_ne_pc slot).symm)
        rw [hpcEq]
        exact hready.pc
      have hinpParked : TM.Parked inp := by simpa [hinp] using hinput
      have houtParked : TM.Parked out := by simpa [hout] using houtput
      have hsucc := TM.binarySuccTM_hoareTime_frame tapes.pc pcValue inp
        work out hpcWork hinpParked.read_ne_start
        (fun i _ => (hlookupResult.parked i).read_ne_start)
        houtParked.read_ne_start
      obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
          hframe, hfinalPC, hfinalOutput⟩ :=
        hsucc inp work out ⟨rfl, rfl, rfl⟩
      refine ⟨final, time, htime, hreach, hhalt, ?_, ?_, ?_⟩
      · exact hfinalInput.trans hinp
      · refine ⟨work, hlookupResult, ?_, ?_, ?_, hframe⟩
        · rw [hframe tapes.data.lhs tapes.lhs_ne_pc]
          change (work tapes.data.lhs).HasBinaryNat value
          exact hlookupResult.destination
        · simpa only [newPC, value, ite_eq_right hnonzero] using hfinalPC
        · intro i
          by_cases hi : i = tapes.pc
          · subst i
            exact hasBinaryNat_parked hfinalPC
          · rw [hframe i hi]
            exact hlookupResult.parked i
      · exact hfinalOutput.trans hout
    have hdispatch := TM.branchWorkBlankTM_hoareTime tapes.data.lhs
      (setProgramCounterTM tapes.pc target) (TM.binarySuccTM tapes.pc)
      (pre := lookupPost) (blankPre := blankPre)
      (nonblankPre := nonblankPre) (blankPost := branchPost)
      (nonblankPost := branchPost)
      (fun inp work out hpre => by
        have hinpParked : TM.Parked inp := by simpa [hpre.1] using hinput
        have houtParked : TM.Parked out := by simpa [hpre.2.2] using houtput
        exact ⟨hinpParked.read_ne_start,
          fun i => (hpre.2.1.parked i).read_ne_start,
          houtParked.read_ne_start⟩)
      (fun _ work _ hpre hread =>
        ⟨hpre,
          hpre.2.1.destination.read_eq_blank_iff.mp hread⟩)
      (fun _ work _ hpre hread =>
        ⟨hpre, fun hzero =>
          hread (hpre.2.1.destination.read_eq_blank_iff.mpr hzero)⟩)
      hblank hnonblank
    exact hdispatch.consequence (fun _ _ _ h => h)
      (fun _ _ _ h => h.elim id id) le_rfl
  have hreset : (TM.resetBinaryWorkTM tapes.data.lhs).HoareTime
      branchPost
      (fun inp work out =>
        inp = inp₀ ∧
          ControlInstructionResult tapes store newPC initialWork work ∧
          out = out₀)
      (TM.resetBinaryWorkTime 1 value.bits.length) := by
    rintro inp work out ⟨hinp, hbranchResult, hout⟩
    obtain ⟨lookupWork, hlookupResult, hoperand, hpcResult,
      hparked, hframe⟩ := hbranchResult
    have hinpParked : TM.Parked inp := by simpa [hinp] using hinput
    have hrun := TM.resetBinaryWorkTM_hoareTime_frame tapes.data.lhs
      value.bits 1 inp work out hoperand.2.hasBinaryContent
      hoperand.1
      ⟨by rw [hoperand.2.1], by rw [hoperand.2.1]⟩
      hinpParked (fun i _ => hparked i)
      (by simpa [hout] using houtput)
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hfinalWork, hfinalOutput⟩ := hrun inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨final, time, htime, hreach, hhalt, ?_, ?_, ?_⟩
    · exact hfinalInput.trans hinp
    · rw [hfinalWork]
      exact controlResult_of_zeroJumpReset tapes store pcValue source newPC
        initialWork work hready
          ⟨lookupWork, hlookupResult, hoperand, hpcResult, hparked, hframe⟩
    · exact hfinalOutput.trans hout
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
    (entryLookupStaticTM tapes.data.lhsLookup source)
    (TM.seqTM
      (TM.branchWorkBlankTM tapes.data.lhs
        (setProgramCounterTM tapes.pc target) (TM.binarySuccTM tapes.pc))
      (TM.resetBinaryWorkTM tapes.data.lhs)) hlookup
    (by
      rintro inp work out ⟨hinp, hlookupResult, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using hinput) hlookupResult.parked
        (by simpa [hout] using houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, hlookupResult, hout⟩)
    hbranchReset
  simpa only [zeroJumpInstructionTM, zeroJumpInstructionTime, value, newPC]
    using hall

/-- Halt is an exact one-step no-op at the clean control boundary. -/
theorem haltInstructionTM_hoareTime_frame_internal
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue : ℕ) (initialWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hready : ControlInstructionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (haltInstructionTM (n := n)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        ControlInstructionResult tapes store pcValue initialWork work ∧
        out = out₀)
      haltInstructionTime := by
  have hskip := TM.skipTM_hoareTime_frame inp₀ initialWork out₀ hinput
    hready.lookup.scanner.parked houtput
  apply hskip.consequence
  · exact fun _ _ _ h => h
  · rintro inp work out ⟨hinp, hworkEq, hout⟩
    subst work
    exact ⟨hinp, ⟨hready, rfl, by intros; rfl⟩, hout⟩
  · exact le_rfl

end Machine

end RegisterStore

end RAM

end Complexity
