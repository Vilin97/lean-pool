/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScan.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.WorkReadOnly
public import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Sparse-store update source preservation

The update controller advances its encoded source cursor but never changes the
source cells. This file packages that local transition fact as a reusable
read-only certificate.
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem binarySuccTM_readOnly_of_ne (target other : Fin n)
    (hne : other ≠ target) :
    (TM.binarySuccTM target).WorkReadOnly other := by
  intro state inputHead workHeads outputHead hstate
  cases state with
  | carry =>
      cases hread : workHeads target <;>
        simp [TM.binarySuccTM, hread, hne]
  | rewind =>
      by_cases hread : workHeads target = Γ.start <;>
        simp [TM.binarySuccTM, hread]
  | done => exact (hstate rfl).elim

private theorem binaryPredTM_readOnly_of_ne (target other : Fin n)
    (hne : other ≠ target) :
    (TM.binaryPredTM target).WorkReadOnly other := by
  intro state inputHead workHeads outputHead hstate
  cases state with
  | borrow | check =>
      cases hread : workHeads target <;>
        simp [TM.binaryPredTM, hread, hne]
  | erase | rewind =>
      by_cases hread : workHeads target = Γ.start <;>
        simp [TM.binaryPredTM, hread, hne]
  | done => exact (hstate rfl).elim

private theorem rewindWorkTM_readOnly (target other : Fin n) :
    (TM.rewindWorkTM target).WorkReadOnly other := by
  intro state inputHead workHeads outputHead hstate
  cases state with
  | moveLeft =>
      by_cases hread : workHeads target = Γ.start <;>
        simp [TM.rewindWorkTM, hread]
  | moveRight => rfl
  | done => exact (hstate rfl).elim

private theorem blankWorkTM_readOnly_of_ne (target other : Fin n)
    (hne : other ≠ target) :
    (TM.blankWorkTM target).WorkReadOnly other := by
  intro state inputHead workHeads outputHead hstate
  cases state with
  | scanning =>
      by_cases hread : workHeads target = Γ.blank <;>
        simp [TM.blankWorkTM, hread, hne]
  | done => exact (hstate rfl).elim

private theorem clearWorkTM_readOnly_of_ne (target other : Fin n)
    (hne : other ≠ target) :
    (TM.clearWorkTM target).WorkReadOnly other := by
  exact (blankWorkTM_readOnly_of_ne target other hne).seqTM
    (rewindWorkTM_readOnly target other)

private theorem resetBinaryWorkTM_readOnly_of_ne (target other : Fin n)
    (hne : other ≠ target) :
    (TM.resetBinaryWorkTM target).WorkReadOnly other := by
  unfold TM.resetBinaryWorkTM
  exact (rewindWorkTM_readOnly target other).seqTM
    (clearWorkTM_readOnly_of_ne target other hne)

private theorem skipTM_readOnly (other : Fin n) :
    (TM.skipTM (n := n)).WorkReadOnly other := by
  intro state inputHead workHeads outputHead hstate
  rfl

private theorem resetBinaryWorkManyTM_readOnly_of_not_mem
    (targets : List (Fin n)) (other : Fin n) (hnotmem : other ∉ targets) :
    (TM.resetBinaryWorkManyTM targets).WorkReadOnly other := by
  induction targets with
  | nil => exact skipTM_readOnly other
  | cons target targets ih =>
      simp only [List.mem_cons, not_or] at hnotmem
      exact (resetBinaryWorkTM_readOnly_of_ne target other hnotmem.1).seqTM
        (ih hnotmem.2)

private theorem forWorkOnesTM_readOnly (driver other : Fin n) (body : TM n)
    (hbody : body.WorkReadOnly other) :
    (TM.forWorkOnesTM driver body).WorkReadOnly other := by
  intro state inputHead workHeads outputHead hstate
  cases state with
  | inl phase =>
      cases phase with
      | scan =>
          by_cases hstart : workHeads driver = Γ.start
          · simp [TM.forWorkOnesTM, hstart]
          · by_cases hone : workHeads driver = Γ.one
            · simp [TM.forWorkOnesTM, hone]
            · simp only [TM.forWorkOnesTM, hstart, hone, ↓reduceIte]
              rfl
      | done => exact (hstate rfl).elim
  | inr state =>
      by_cases hhalt : state = body.qhalt
      · simp only [TM.forWorkOnesTM, hhalt, ↓reduceIte]
        rfl
      · simpa [TM.forWorkOnesTM, hhalt] using
          hbody state inputHead workHeads outputHead hhalt

private theorem binaryForTM_readOnly (body : TM n)
    (counter limit other : Fin n) (hbody : body.WorkReadOnly other)
    (hne : other ≠ counter) :
    (TM.binaryForTM body counter limit).WorkReadOnly other := by
  have hiteration :
      (TM.binaryForIterationTM body counter).WorkReadOnly other := by
    exact hbody.seqTM (binarySuccTM_readOnly_of_ne counter other hne)
  intro state inputHead workHeads outputHead hstate
  cases state with
  | inl phase =>
      cases phase with
      | scan equalSoFar =>
          by_cases hblank :
              workHeads counter = Γ.blank ∧ workHeads limit = Γ.blank <;>
            simp [TM.binaryForTM, hblank]
      | rewind equalSoFar =>
          by_cases hstart :
              workHeads counter = Γ.start ∧ workHeads limit = Γ.start <;>
            simp [TM.binaryForTM, hstart]
      | done => exact (hstate rfl).elim
  | inr state =>
      by_cases hhalt : state = (TM.binaryForIterationTM body counter).qhalt
      · simp only [TM.binaryForTM, hhalt, ↓reduceIte]
        rfl
      · simpa [TM.binaryForTM, hhalt] using
          hiteration state inputHead workHeads outputHead hhalt

private theorem workEmitTM_readOnly (target other : Fin n)
    (mode : WorkEmitMode) :
    (workEmitTM target mode).WorkReadOnly other := by
  intro state inputHead workHeads outputHead hstate
  cases state with
  | scan =>
      cases hread : workHeads target with
      | zero | one => simp [workEmitTM, hread]
      | start =>
          simp only [workEmitTM, hread]
          rfl
      | blank =>
          by_cases hmode : mode = .width
          · simp [workEmitTM, hread, hmode]
          · simp only [workEmitTM, hread, hmode, ↓reduceIte]
            rfl
  | done => exact (hstate rfl).elim

private theorem wordEncodeTM_readOnly (target other : Fin n) :
    (wordEncodeTM target).WorkReadOnly other := by
  unfold wordEncodeTM
  exact (workEmitTM_readOnly target other .width).seqTM
    ((rewindWorkTM_readOnly target other).seqTM
      (workEmitTM_readOnly target other .payload))

private theorem rewindWordEncodeTM_readOnly (target other : Fin n) :
    (rewindWordEncodeTM target).WorkReadOnly other := by
  unfold rewindWordEncodeTM
  exact (rewindWorkTM_readOnly target other).seqTM
    (wordEncodeTM_readOnly target other)

private theorem rewindEntryEncodeTM_readOnly
    (tapes : EntryEncodeTapes n) (other : Fin n) :
    (rewindEntryEncodeTM tapes).WorkReadOnly other := by
  unfold rewindEntryEncodeTM
  exact (rewindWordEncodeTM_readOnly tapes.address other).seqTM
    (rewindWordEncodeTM_readOnly tapes.value other)

private theorem payloadBitTM_source_readOnly (source target : Fin n)
    (hne : source ≠ target) :
    (payloadBitTM source target).WorkReadOnly source := by
  intro state inputHead workHeads outputHead hstate
  cases state with
  | copy =>
      cases hread : workHeads source with
      | zero | one => simp [payloadBitTM, hread, hne]
      | blank =>
          simp [payloadBitTM, hread, TM.allReadBack]
      | start => simp [payloadBitTM, hread, TM.allIdle, TM.readBackWrite]
  | done => exact (hstate rfl).elim

private theorem wordSeparatorTM_source_readOnly (source : Fin n) :
    (wordSeparatorTM source).WorkReadOnly source := by
  intro state inputHead workHeads outputHead hstate
  cases state with
  | skip =>
      by_cases hzero : workHeads source = Γ.zero
      · simp [wordSeparatorTM, hzero]
      · by_cases hstart : workHeads source = Γ.start
        · simp [wordSeparatorTM, hstart, TM.allIdle, TM.readBackWrite]
        · simp only [wordSeparatorTM, hzero, hstart, ↓reduceIte]
          simp [TM.allReadBack]
  | done => exact (hstate rfl).elim

private theorem binaryEqTM_readOnly_of_ne_result
    (lhs rhs result other : Fin n) (hne : other ≠ result) :
    (TM.binaryEqTM lhs rhs result).WorkReadOnly other := by
  intro state inputHead workHeads outputHead hstate
  cases state with
  | scan =>
      by_cases hblank :
          workHeads lhs = Γ.blank ∧ workHeads rhs = Γ.blank
      · simp [TM.binaryEqTM, hblank, hne]
      · by_cases heq : workHeads lhs = workHeads rhs
        · have hrhs : workHeads rhs ≠ Γ.blank := by
            intro hrhs
            apply hblank
            exact ⟨heq.trans hrhs, hrhs⟩
          simp [TM.binaryEqTM, heq, hrhs]
        · simp [TM.binaryEqTM, hblank, heq, hne]
  | done => exact (hstate rfl).elim

private theorem wordDecodeTM_source_readOnly
    (source target counter width : Fin n)
    (hsourceTarget : source ≠ target)
    (hsourceCounter : source ≠ counter)
    (hsourceWidth : source ≠ width) :
    (wordDecodeTM source target counter width).WorkReadOnly source := by
  have hwidth : (wordWidthTM source width).WorkReadOnly source := by
    unfold wordWidthTM
    exact forWorkOnesTM_readOnly source source (TM.binarySuccTM width)
      (binarySuccTM_readOnly_of_ne width source hsourceWidth)
  have hpayload :
      (wordPayloadTM source target counter width).WorkReadOnly source := by
    unfold wordPayloadTM
    exact binaryForTM_readOnly (payloadBitTM source target) counter width source
      (payloadBitTM_source_readOnly source target hsourceTarget) hsourceCounter
  unfold wordDecodeTM
  exact hwidth.seqTM
    ((wordSeparatorTM_source_readOnly source).seqTM hpayload)

private theorem entryDecodeTM_source_readOnly (tapes : EntryDecodeTapes n) :
    (entryDecodeTM tapes).WorkReadOnly tapes.source := by
  unfold entryDecodeTM
  exact
    (wordDecodeTM_source_readOnly tapes.source tapes.address
      tapes.addressCounter tapes.addressWidth
      (tapes.ne (by decide)) (tapes.ne (by decide))
      (tapes.ne (by decide))).seqTM
    (wordDecodeTM_source_readOnly tapes.source tapes.value
      tapes.valueCounter tapes.valueWidth
      (tapes.ne (by decide)) (tapes.ne (by decide))
      (tapes.ne (by decide)))

private theorem wordDecodeLinearTM_source_readOnly
    (source target marker : Fin n) (hsourceTarget : source ≠ target)
    (hsourceMarker : source ≠ marker) :
    (wordDecodeLinearTM source target marker).WorkReadOnly source := by
  intro phase inputHead workHeads outputHead hphase
  cases phase with
  | mark =>
      cases hsource : workHeads source <;>
        simp [wordDecodeLinearTM, hsource, hsourceMarker, TM.allReadBack,
          TM.allIdle, TM.readBackWrite]
  | rewind =>
      by_cases hmarker : workHeads marker = Γ.start <;>
        simp [wordDecodeLinearTM, hmarker]
  | copy =>
      cases hmarker : workHeads marker with
      | one =>
          cases hsource : workHeads source <;>
            simp [wordDecodeLinearTM, hmarker, hsource, hsourceTarget,
              TM.allReadBack]
      | zero | blank =>
          simp [wordDecodeLinearTM, hmarker, TM.allReadBack]
      | start =>
          simp [wordDecodeLinearTM, hmarker]
  | done => exact (hphase rfl).elim

private theorem entryDecodeLinearTM_source_readOnly
    (tapes : EntryDecodeTapes n) :
    (entryDecodeLinearTM tapes).WorkReadOnly tapes.source := by
  unfold entryDecodeLinearTM
  exact
    (wordDecodeLinearTM_source_readOnly tapes.source tapes.address
      tapes.addressCounter (tapes.ne (by decide))
      (tapes.ne (by decide))).seqTM
    (wordDecodeLinearTM_source_readOnly tapes.source tapes.value
      tapes.valueCounter (tapes.ne (by decide)) (tapes.ne (by decide)))

private theorem decodedAddressEqTM_readOnly_of_ne_result
    (address query result other : Fin n) (hne : other ≠ result) :
    (decodedAddressEqTM address query result).WorkReadOnly other := by
  unfold decodedAddressEqTM
  exact (rewindWorkTM_readOnly address other).seqTM
    (binaryEqTM_readOnly_of_ne_result address query result other hne)

private theorem entryMatchReadTM_source_readOnly (tapes : EntryMatchTapes n) :
    (entryMatchReadTM tapes).WorkReadOnly tapes.source := by
  have hdecode :
      (entryDecodeLinearTM tapes.decode).WorkReadOnly tapes.source :=
    entryDecodeLinearTM_source_readOnly tapes.decode
  have heq :
      (decodedAddressEqTM tapes.address tapes.query tapes.result).WorkReadOnly
        tapes.source :=
    decodedAddressEqTM_readOnly_of_ne_result tapes.address tapes.query
      tapes.result tapes.source (tapes.ne (by decide))
  unfold entryMatchReadTM entryMatchTM
  exact (hdecode.seqTM heq).seqTM
    (rewindWorkTM_readOnly tapes.result tapes.source)

private theorem source_not_mem_entryMissTargets (tapes : EntryMatchTapes n) :
    tapes.source ∉ entryMissTargets tapes := by
  intro hmem
  obtain ⟨slot, hslot⟩ := List.mem_ofFn.mp hmem
  have hidx := tapes.injective hslot
  have hval := congrArg Fin.val hidx
  change (if slot.val = 6 then 8 else slot.val + 1) = 0 at hval
  split at hval <;> omega

private theorem entryMissCleanupTM_source_readOnly
    (tapes : EntryMatchTapes n) :
    (entryMissCleanupTM tapes).WorkReadOnly tapes.source := by
  unfold entryMissCleanupTM
  exact (rewindWorkTM_readOnly tapes.query tapes.source).seqTM
    (resetBinaryWorkManyTM_readOnly_of_not_mem
      (entryMissTargets tapes) tapes.source
      (source_not_mem_entryMissTargets tapes))

private theorem entryMissCopyTM_source_readOnly (tapes : EntryMatchTapes n) :
    (entryMissCopyTM tapes).WorkReadOnly tapes.source := by
  unfold entryMissCopyTM
  exact (rewindEntryEncodeTM_readOnly tapes.encodeTapes tapes.source).seqTM
    (entryMissCleanupTM_source_readOnly tapes)

private theorem entryReplaceCleanupTM_source_readOnly
    (tapes : EntryReplaceTapes n) :
    (entryReplaceCleanupTM tapes).WorkReadOnly tapes.entry.source := by
  unfold entryReplaceCleanupTM
  exact
    (rewindEntryEncodeTM_readOnly tapes.encodeTapes tapes.entry.source).seqTM
    ((rewindWorkTM_readOnly tapes.replacement tapes.entry.source).seqTM
      (entryMissCleanupTM_source_readOnly tapes.entry))

private theorem entryAppendRestoreTM_source_readOnly
    (tapes : EntryReplaceTapes n) :
    (entryAppendRestoreTM tapes).WorkReadOnly tapes.entry.source := by
  unfold entryAppendRestoreTM
  exact
    (rewindEntryEncodeTM_readOnly tapes.appendEncodeTapes
      tapes.entry.source).seqTM
    ((rewindWorkTM_readOnly tapes.entry.query tapes.entry.source).seqTM
      (rewindWorkTM_readOnly tapes.replacement tapes.entry.source))

private theorem branchWorkSymbolTM_readOnly
    (idx : Fin n) (symbol : Γ) (onEqual onDifferent : TM n)
    (other : Fin n) (hequal : onEqual.WorkReadOnly other)
    (hdifferent : onDifferent.WorkReadOnly other) :
    (TM.branchWorkSymbolTM idx symbol onEqual onDifferent).WorkReadOnly
      other := by
  intro state inputHead workHeads outputHead hstate
  cases state with
  | inl phase =>
      cases phase with
      | dispatch =>
          by_cases hread : workHeads idx = symbol <;>
            simp [TM.branchWorkSymbolTM, hread, TM.allReadBack]
      | done => exact (hstate rfl).elim
  | inr branch =>
      cases branch with
      | inl state =>
          by_cases hhalt : state = onEqual.qhalt
          · simp [TM.branchWorkSymbolTM, hhalt, TM.allReadBack]
          · simpa [TM.branchWorkSymbolTM, hhalt] using
              hequal state inputHead workHeads outputHead hhalt
      | inr state =>
          by_cases hhalt : state = onDifferent.qhalt
          · simp [TM.branchWorkSymbolTM, hhalt, TM.allReadBack]
          · simpa [TM.branchWorkSymbolTM, hhalt] using
              hdifferent state inputHead workHeads outputHead hhalt

private theorem entryScanStepTM_source_readOnly (tapes : EntryMatchTapes n) :
    (entryScanStepTM tapes).WorkReadOnly tapes.source := by
  have hbranch :
      (entryScanBranchTM tapes).WorkReadOnly tapes.source := by
    unfold entryScanBranchTM
    exact branchWorkSymbolTM_readOnly tapes.result Γ.one TM.skipTM
      (entryMissCleanupTM tapes) tapes.source
      (skipTM_readOnly tapes.source)
      (entryMissCleanupTM_source_readOnly tapes)
  unfold entryScanStepTM
  exact (entryMatchReadTM_source_readOnly tapes).seqTM hbranch

/-- The bounded lookup scanner advances but never changes its encoded source
cells. -/
theorem entryScanTM_source_readOnly_internal (tapes : EntryScanTapes n) :
    (entryScanTM tapes).WorkReadOnly tapes.entry.source := by
  have hstep := entryScanStepTM_source_readOnly tapes.entry
  have hcount := binaryPredTM_readOnly_of_ne tapes.count tapes.entry.source
    tapes.count_ne_source.symm
  intro state inputHead workHeads outputHead hstate
  cases state with
  | inl phase =>
      cases phase with
      | test =>
          by_cases hblank : workHeads tapes.count = Γ.blank <;>
            simp [entryScanTM, hblank, TM.allReadBack]
      | done => exact (hstate rfl).elim
  | inr nested =>
      cases nested with
      | inl state =>
          by_cases hhalt : state = (entryScanStepTM tapes.entry).qhalt
          · by_cases hresult : workHeads tapes.entry.result = Γ.one <;>
              simp [entryScanTM, hhalt, hresult, TM.allReadBack]
          · simpa [entryScanTM, hhalt] using
              hstep state inputHead workHeads outputHead hhalt
      | inr state =>
          by_cases hhalt : state = (TM.binaryPredTM tapes.count).qhalt
          · simp [entryScanTM, hhalt, TM.allReadBack]
          · simpa [entryScanTM, hhalt] using
              hcount state inputHead workHeads outputHead hhalt

theorem entryUpdateTM_source_readOnly_internal
    (tapes : EntryUpdateTapes n) :
    (entryUpdateTM tapes).WorkReadOnly tapes.entry.source := by
  have hmatching := entryMatchReadTM_source_readOnly tapes.entry
  have hmiss := entryMissCopyTM_source_readOnly tapes.entry
  have hdelete := entryMissCleanupTM_source_readOnly tapes.entry
  have hreplace := entryReplaceCleanupTM_source_readOnly tapes.replace
  have happend := entryAppendRestoreTM_source_readOnly tapes.replace
  have hsourceRemaining : tapes.entry.source ≠ tapes.remaining :=
    tapes.ne (by decide)
  have hsourceFound : tapes.entry.source ≠ tapes.found :=
    tapes.ne (by decide)
  have hsourceResultCount : tapes.entry.source ≠ tapes.resultCount :=
    tapes.ne (by decide)
  have hremaining := binaryPredTM_readOnly_of_ne tapes.remaining
    tapes.entry.source hsourceRemaining
  have hdeleteCount := binaryPredTM_readOnly_of_ne tapes.resultCount
    tapes.entry.source hsourceResultCount
  have happendCount := binarySuccTM_readOnly_of_ne tapes.resultCount
    tapes.entry.source hsourceResultCount
  intro state inputHead workHeads outputHead hstate
  cases state with
  | test =>
      by_cases hremainingBlank : workHeads tapes.remaining = Γ.blank
      · by_cases hfoundOne : workHeads tapes.found = Γ.one
        · simp [entryUpdateTM, hremainingBlank, hfoundOne, TM.allReadBack]
        · by_cases hreplBlank : workHeads tapes.replacement = Γ.blank <;>
            simp [entryUpdateTM, hremainingBlank, hfoundOne, hreplBlank,
              TM.allReadBack]
      · simp [entryUpdateTM, hremainingBlank, TM.allReadBack]
  | matching state =>
      by_cases hhalt : state = (entryMatchReadTM tapes.entry).qhalt
      · by_cases hresult : workHeads tapes.entry.result = Γ.one
        · simp [entryUpdateTM, hhalt, hresult, hsourceFound]
        · simp [entryUpdateTM, hhalt, hresult, TM.allReadBack]
      · simpa [entryUpdateTM, hhalt] using
          hmatching state inputHead workHeads outputHead hhalt
  | miss state =>
      by_cases hhalt : state = (entryMissCopyTM tapes.entry).qhalt
      · simp [entryUpdateTM, hhalt, TM.allReadBack]
      · simpa [entryUpdateTM, hhalt] using
          hmiss state inputHead workHeads outputHead hhalt
  | delete state =>
      by_cases hhalt : state = (entryMissCleanupTM tapes.entry).qhalt
      · simp [entryUpdateTM, hhalt, TM.allReadBack]
      · simpa [entryUpdateTM, hhalt] using
          hdelete state inputHead workHeads outputHead hhalt
  | replace state =>
      by_cases hhalt : state = (entryReplaceCleanupTM tapes.replace).qhalt
      · simp [entryUpdateTM, hhalt, TM.allReadBack]
      · simpa [entryUpdateTM, hhalt] using
          hreplace state inputHead workHeads outputHead hhalt
  | append state =>
      by_cases hhalt : state = (entryAppendRestoreTM tapes.replace).qhalt
      · simp [entryUpdateTM, hhalt, TM.allReadBack]
      · simpa [entryUpdateTM, hhalt] using
          happend state inputHead workHeads outputHead hhalt
  | remaining state =>
      by_cases hhalt : state = (TM.binaryPredTM tapes.remaining).qhalt
      · simp [entryUpdateTM, hhalt, TM.allReadBack]
      · simpa [entryUpdateTM, hhalt] using
          hremaining state inputHead workHeads outputHead hhalt
  | deleteCount state =>
      by_cases hhalt : state = (TM.binaryPredTM tapes.resultCount).qhalt
      · simp [entryUpdateTM, hhalt, TM.allReadBack]
      · simpa [entryUpdateTM, hhalt] using
          hdeleteCount state inputHead workHeads outputHead hhalt
  | appendCount state =>
      by_cases hhalt : state = (TM.binarySuccTM tapes.resultCount).qhalt
      · simp [entryUpdateTM, hhalt, TM.allReadBack]
      · simpa [entryUpdateTM, hhalt] using
          happendCount state inputHead workHeads outputHead hhalt
  | done => exact (hstate rfl).elim

end Machine

end RegisterStore

end RAM

end Complexity
