/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul

/-!
# Concrete sparse-store arithmetic instruction kernel -- proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem hasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t :=
  ⟨by rw [h.2.1], h.2.hasBinaryContent.cells_ne_start⟩

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

private theorem arithmeticResult_of_threeTape
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp) (lhs rhs : ℕ)
    (initialWork finalWork : Fin n → Tape)
    (hlhs : (finalWork tapes.lhs).HasBinaryNat lhs)
    (hrhs : (finalWork tapes.rhs).HasBinaryNat rhs)
    (hresult :
      (finalWork tapes.update.replacement).HasBinaryNat (op.eval lhs rhs))
    (hframe : ∀ i, i ≠ tapes.lhs → i ≠ tapes.rhs →
      i ≠ tapes.update.replacement → finalWork i = initialWork i)
    (hwork : ∀ i, TM.Parked (initialWork i))
    (hshift : (initialWork tapes.shift).HasBinaryNat 0)
    (htmp : (initialWork tapes.tmp).HasBinaryNat 0)
    (hdbl : (initialWork tapes.dbl).HasBinaryNat 0) :
    BinaryInstructionArithmeticResult tapes op lhs rhs initialWork
      finalWork := by
  have hshift' : (finalWork tapes.shift).HasBinaryNat 0 := by
    rw [hframe tapes.shift (tapes.ne (by decide)) (tapes.ne (by decide))
      (tapes.ne (by decide))]
    exact hshift
  have htmp' : (finalWork tapes.tmp).HasBinaryNat 0 := by
    rw [hframe tapes.tmp (tapes.ne (by decide)) (tapes.ne (by decide))
      (tapes.ne (by decide))]
    exact htmp
  have hdbl' : (finalWork tapes.dbl).HasBinaryNat 0 := by
    rw [hframe tapes.dbl (tapes.ne (by decide)) (tapes.ne (by decide))
      (tapes.ne (by decide))]
    exact hdbl
  refine ⟨hlhs, hrhs, hresult, hshift', htmp', hdbl', ?_, ?_⟩
  · intro i
    by_cases hilhs : i = tapes.lhs
    · subst i
      exact hasBinaryNat_parked hlhs
    · by_cases hirhs : i = tapes.rhs
      · subst i
        exact hasBinaryNat_parked hrhs
      · by_cases hires : i = tapes.update.replacement
        · subst i
          exact hasBinaryNat_parked hresult
        · rw [hframe i hilhs hirhs hires]
          exact hwork i
  · intro i hilhs hirhs hires _ _ _
    exact hframe i hilhs hirhs hires

private theorem arithmeticResult_of_sub
    (tapes : BinaryInstructionTapes n) (lhs rhs : ℕ)
    (initialWork finalWork : Fin n → Tape)
    (hlhs : (finalWork tapes.lhs).HasBinaryNat lhs)
    (hrhs : (finalWork tapes.rhs).HasBinaryNat rhs)
    (hresult :
      (finalWork tapes.update.replacement).HasBinaryNat (lhs - rhs))
    (hframe : ∀ i, i ≠ tapes.lhs → i ≠ tapes.rhs →
      i ≠ tapes.update.replacement → finalWork i = initialWork i)
    (hwork : ∀ i, TM.Parked (initialWork i))
    (hshift : (initialWork tapes.shift).HasBinaryNat 0)
    (htmp : (initialWork tapes.tmp).HasBinaryNat 0)
    (hdbl : (initialWork tapes.dbl).HasBinaryNat 0) :
    BinaryInstructionArithmeticResult tapes .sub lhs rhs initialWork
      finalWork := by
  exact arithmeticResult_of_threeTape tapes .sub lhs rhs initialWork finalWork hlhs hrhs
    hresult hframe hwork hshift htmp hdbl

/-- The selected width-efficient arithmetic phase has one uniform framed
contract. -/
theorem binaryInstructionArithmeticTM_hoareTime_frame_internal
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ tapes.lhs).HasBinaryNat lhs)
    (hrhs : (work₀ tapes.rhs).HasBinaryNat rhs)
    (hresult : (work₀ tapes.update.replacement).HasBinaryNat 0)
    (hshift : (work₀ tapes.shift).HasBinaryNat 0)
    (htmp : (work₀ tapes.tmp).HasBinaryNat 0)
    (hdbl : (work₀ tapes.dbl).HasBinaryNat 0)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    (binaryInstructionArithmeticTM tapes op).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        BinaryInstructionArithmeticResult tapes op lhs rhs work₀ work ∧
        out = out₀)
      (binaryInstructionArithmeticTime op lhs rhs) := by
  cases op with
  | add =>
      exact (TM.binaryRippleAddTM_hoareTime_frame tapes.lhs tapes.rhs
        tapes.update.replacement tapes.arithmeticDistinct lhs rhs inp₀ work₀
        out₀ hlhs hrhs hresult hinput
        (fun i _ _ _ => hwork i) houtput).strengthen_post (by
          rintro inp work out ⟨hinp, hlhs', hrhs', hresult', hframe, hout⟩
          exact ⟨hinp, arithmeticResult_of_threeTape tapes .add lhs rhs work₀ work
            hlhs' hrhs' hresult' hframe hwork hshift htmp hdbl, hout⟩)
  | sub =>
      exact (TM.binaryRippleSubTM_hoareTime_frame tapes.lhs tapes.rhs
        tapes.update.replacement tapes.subtractionDistinct lhs rhs inp₀ work₀
        out₀ hlhs hrhs hresult hinput
        (fun i _ _ _ => hwork i) houtput).strengthen_post (by
          rintro inp work out ⟨hinp, hlhs', hrhs', hresult', hframe, hout⟩
          exact ⟨hinp, arithmeticResult_of_sub tapes lhs rhs work₀ work
            hlhs' hrhs' hresult' hframe hwork hshift htmp hdbl, hout⟩)
  | mul =>
      exact (TM.binaryShiftMulTM_hoareTime_frame tapes.mul lhs rhs inp₀ work₀
        out₀ (by simpa using! hlhs) (by simpa using! hrhs)
        (by simpa using! hresult) (by simpa using! hshift)
        (by simpa using! htmp) (by simpa using! hdbl) hinput hwork
        houtput).strengthen_post (by
          rintro inp work out
            ⟨hinp, hlhs', hrhs', hresult', hshift', htmp', hdbl', hframe,
              hout⟩
          refine ⟨hinp, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hout⟩
          · simpa using! hlhs'
          · simpa using! hrhs'
          · simpa using! hresult'
          · simpa using! hshift'
          · simpa using! htmp'
          · simpa using! hdbl'
          · intro i
            by_cases hilhs : i = tapes.lhs
            · subst i
              exact hasBinaryNat_parked (by simpa using! hlhs')
            · by_cases hirhs : i = tapes.rhs
              · subst i
                exact hasBinaryNat_parked (by simpa using! hrhs')
              · by_cases hires : i = tapes.update.replacement
                · subst i
                  exact hasBinaryNat_parked (by simpa using! hresult')
                · by_cases hishift : i = tapes.shift
                  · subst i
                    exact hasBinaryNat_parked (by simpa using! hshift')
                  · by_cases hitmp : i = tapes.tmp
                    · subst i
                      exact hasBinaryNat_parked (by simpa using! htmp')
                    · by_cases hidbl : i = tapes.dbl
                      · subst i
                        exact hasBinaryNat_parked (by simpa using! hdbl')
                      · rw [hframe i (by simpa using! hilhs)
                          (by simpa using! hirhs) (by simpa using! hires)
                          (by simpa using! hishift) (by simpa using! hitmp)
                          (by simpa using! hidbl)]
                        exact hwork i
          · intro i hilhs hirhs hires hishift hitmp hidbl
            exact hframe i (by simpa using! hilhs) (by simpa using! hirhs)
              (by simpa using! hires) (by simpa using! hishift)
              (by simpa using! hitmp) (by simpa using! hidbl))

/-- Arithmetic feeds its canonical result directly into sparse update. -/
theorem binaryInstructionUpdateTM_hoareTime_frame_internal
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (store : Store) (address lhs rhs : ℕ)
    (emittedBits : List Bool) (initialWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hcanonical : Canonical store)
    (hready : EntryScanReady tapes.update.entry
      (store.flatMap Entry.encode) address.bits initialWork initialWork)
    (hlhs : (initialWork tapes.lhs).HasBinaryNat lhs)
    (hrhs : (initialWork tapes.rhs).HasBinaryNat rhs)
    (hresult : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (hshift : (initialWork tapes.shift).HasBinaryNat 0)
    (htmp : (initialWork tapes.tmp).HasBinaryNat 0)
    (hdbl : (initialWork tapes.dbl).HasBinaryNat 0)
    (hremaining :
      (initialWork tapes.update.remaining).HasBinaryNat store.length)
    (hfound : (initialWork tapes.update.found).HasBinaryNat 0)
    (hresultCount :
      (initialWork tapes.update.resultCount).HasBinaryNat store.length)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (initialWork i))
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (binaryInstructionUpdateTM tapes op).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        BinaryInstructionUpdateResult tapes op store address lhs rhs
          initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store address (op.eval lhs rhs)).flatMap
              Entry.encode))
      (binaryInstructionUpdateTime tapes op store address lhs rhs) := by
  have harithmetic :=
    binaryInstructionArithmeticTM_hoareTime_frame_internal tapes op lhs rhs
      inp₀ initialWork out₀ hlhs hrhs hresult hshift htmp hdbl hinput
      hwork (hasBinaryPrefix_parked houtput)
  have hupdate : (entryUpdateTM tapes.update).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        BinaryInstructionArithmeticResult tapes op lhs rhs initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        BinaryInstructionUpdateResult tapes op store address lhs rhs
          initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store address (op.eval lhs rhs)).flatMap
              Entry.encode))
      (entryUpdateTime tapes.update store address (op.eval lhs rhs)) := by
    rintro inp work out ⟨hinp, harith, hout⟩
    subst inp
    subst out
    have hslotEq (slot : Fin 13) (hne : slot ≠ 10) :
        work (tapes.update.idx slot) = initialWork (tapes.update.idx slot) :=
      harith.frame (tapes.update.idx slot)
        (tapes.update_ne_lhs slot) (tapes.update_ne_rhs slot)
        (tapes.update.ne hne) (tapes.update_ne_shift slot)
        (tapes.update_ne_tmp slot) (tapes.update_ne_dbl slot)
    have hready' : EntryScanReady tapes.update.entry
        (store.flatMap Entry.encode) address.bits work work := by
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
          parked := harith.parked
          frame := by intro i _ _ _ _ _ _ _ _ _; rfl }
      · change (work (tapes.update.idx 0)).HasBinarySuffix _
        rw [hslotEq 0 (by decide)]
        exact hready.source
      · change (work (tapes.update.idx 1)).HasBinaryPrefix []
        rw [hslotEq 1 (by decide)]
        exact hready.address
      · change (work (tapes.update.idx 1)).cells 0 = _
        rw [hslotEq 1 (by decide)]
        exact hready.addressStart
      · change (work (tapes.update.idx 2)).HasBinaryPrefix []
        rw [hslotEq 2 (by decide)]
        exact hready.value
      · change (work (tapes.update.idx 2)).cells 0 = _
        rw [hslotEq 2 (by decide)]
        exact hready.valueStart
      · change (work (tapes.update.idx 3)).HasBinaryNat 0
        rw [hslotEq 3 (by decide)]
        exact hready.addressCounter
      · change (work (tapes.update.idx 4)).HasBinaryNat 0
        rw [hslotEq 4 (by decide)]
        exact hready.addressWidth
      · change (work (tapes.update.idx 5)).HasBinaryNat 0
        rw [hslotEq 5 (by decide)]
        exact hready.valueCounter
      · change (work (tapes.update.idx 6)).HasBinaryNat 0
        rw [hslotEq 6 (by decide)]
        exact hready.valueWidth
      · change (work (tapes.update.idx 7)).HasBinaryString address.bits
        rw [hslotEq 7 (by decide)]
        exact hready.query
      · change (work (tapes.update.idx 7)).cells 0 = _
        rw [hslotEq 7 (by decide)]
        exact hready.queryStart
      · change (work (tapes.update.idx 8)).HasBinaryPrefix []
        rw [hslotEq 8 (by decide)]
        exact hready.result
      · change (work (tapes.update.idx 8)).cells 0 = _
        rw [hslotEq 8 (by decide)]
        exact hready.resultStart
    have hremaining' :
        (work tapes.update.remaining).HasBinaryNat store.length := by
      change (work (tapes.update.idx 9)).HasBinaryNat _
      rw [hslotEq 9 (by decide)]
      exact hremaining
    have hfound' : (work tapes.update.found).HasBinaryNat 0 := by
      change (work (tapes.update.idx 11)).HasBinaryNat 0
      rw [hslotEq 11 (by decide)]
      exact hfound
    have hresultCount' :
        (work tapes.update.resultCount).HasBinaryNat store.length := by
      change (work (tapes.update.idx 12)).HasBinaryNat _
      rw [hslotEq 12 (by decide)]
      exact hresultCount
    have hrun := entryUpdateTM_hoareTime_frame tapes.update store address
      (op.eval lhs rhs) emittedBits work inp₀ out₀ hcanonical hready'
      harith.result hremaining' hfound' hresultCount' hinput houtput
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput, houtcome,
        hfinalOutput, hsource⟩ :=
      hrun inp₀ work out₀ ⟨rfl, rfl, rfl⟩
    have hsourceInitial :
        work tapes.update.entry.source =
          initialWork tapes.update.entry.source :=
      hslotEq 0 (by decide)
    refine ⟨final, time, htime, hreach, hhalt, hfinalInput, ?_,
      hfinalOutput⟩
    exact ⟨work, harith, houtcome, hsource.trans
      (congrArg Tape.cells hsourceInitial)⟩
  refine TM.seqTM_hoareTime (binaryInstructionArithmeticTM tapes op)
    (entryUpdateTM tapes.update)
    (mid := fun inp work out =>
      inp = inp₀ ∧
      BinaryInstructionArithmeticResult tapes op lhs rhs initialWork work ∧
      out = out₀)
    (mid' := fun inp work out =>
      inp = inp₀ ∧
      BinaryInstructionArithmeticResult tapes op lhs rhs initialWork work ∧
      out = out₀)
    harithmetic ?_ hupdate
  rintro inp work out ⟨hinp, harith, hout⟩
  have hinread : inp.read ≠ Γ.start := by
    rw [hinp]
    exact hinput.read_ne_start
  have hworkread : ∀ i, (work i).read ≠ Γ.start :=
    fun i => (harith.parked i).read_ne_start
  have houtread : out.read ≠ Γ.start := by
    rw [hout]
    exact (hasBinaryPrefix_parked houtput).read_ne_start
  have htransition := TM.phaseTransition_eq_self_of_reads_ne_start
    hinread hworkread houtread
  rw [htransition.1, htransition.2.1, htransition.2.2]
  exact ⟨hinp, harith, hout⟩

end Machine

end RegisterStore

end RAM

end Complexity
