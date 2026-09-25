/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Internal.Loop
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Internal.Out
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Internal.Time
public import Mathlib.Data.Nat.Bitwise
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkBranch

/-!
# Bounded encoded sparse-store update -- unmatched entry iteration
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem nat_eq_of_bits_eq {a b : ℕ} (h : a.bits = b.bits) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth, h]

/-- One unmatched old entry is copied to the output, its remaining-count unit
is consumed, and the update controller returns to its loop-test state. -/
theorem entryUpdateIteration_miss_internal
    (tapes : EntryUpdateTapes n) (store : Store) (address newValue : ℕ)
    (processed emitted : Store) (entry : Entry) (rest : Store)
    (found : Bool) (resultCount : ℕ)
    (initialWork work : Fin n → Tape) (outPrefix : List Bool)
    (inp out : Tape)
    (hinv : EntryUpdateLoopInv tapes store address newValue processed
      (entry :: rest) emitted found resultCount initialWork work)
    (hne : entry.1 ≠ address)
    (hinput : TM.Parked inp)
    (houtput : out.HasBinaryPrefix
      (outPrefix ++ emitted.flatMap Entry.encode)) :
    ∃ nextWork nextOut time,
      time ≤ entryUpdateIterationTime tapes entry rest address newValue
        store.length ∧
      (entryUpdateTM tapes).reachesIn time
        (entryUpdateTestCfg tapes inp work out)
        (entryUpdateTestCfg tapes inp nextWork nextOut) ∧
      EntryUpdateLoopInv tapes store address newValue
        (processed ++ [entry]) rest (emitted ++ [entry]) found resultCount
        initialWork nextWork ∧
      nextOut.HasBinaryPrefix
        (outPrefix ++ (emitted ++ [entry]).flatMap Entry.encode) := by
  have hready : EntryScanReady tapes.entry
      (Entry.encode entry ++ rest.flatMap Entry.encode) address.bits work work := by
    simpa using hinv.ready
  have hremainingPositive :
      (work tapes.remaining).HasBinaryNat (rest.length + 1) := by
    simpa using hinv.remainingCount
  have hremainingRead : (work tapes.remaining).read ≠ Γ.blank := by
    intro hblank
    have hzero := hremainingPositive.read_eq_blank_iff.mp hblank
    omega
  have houtputParked : TM.Parked out :=
    parked_of_binaryPrefix_internal houtput
  have htest := entryUpdateTM_step_test_continue_internal tapes inp work out
    hremainingRead hinput hready.parked houtputParked
  have hmatchContract := entryMatchReadTM_reachesIn_frame tapes.entry entry
    (rest.flatMap Entry.encode) address.bits inp work out hready.source
    hready.address hready.value hready.addressStart hready.valueStart
    hready.addressCounter hready.addressWidth hready.valueCounter
    hready.valueWidth hready.query hready.queryStart hready.result
    hready.resultStart hinput hready.parked houtputParked
  obtain ⟨matchDone, matchTime, hmatchTime, hmatchReach, hmatchHalt,
      hmatchInput, hmatchInv, hmatchOutput⟩ := hmatchContract
  have hmatchReach' :=
    entryUpdateTM_match_reachesIn_internal tapes hmatchReach
  have hmatchInputParked : TM.Parked matchDone.input := by
    rw [hmatchInput]
    exact hinput
  have hmatchOutputPrefix : matchDone.output.HasBinaryPrefix
      (outPrefix ++ emitted.flatMap Entry.encode) := by
    rw [hmatchOutput]
    exact houtput
  have hmatchOutputParked : TM.Parked matchDone.output :=
    parked_of_binaryPrefix_internal hmatchOutputPrefix
  have hresultNotOne :
      (matchDone.work tapes.entry.result).read ≠ Γ.one := by
    intro hone
    apply hne
    exact nat_eq_of_bits_eq (hmatchInv.result_read_eq_one_iff.mp hone)
  have hdispatch := entryUpdateTM_step_match_miss_internal tapes matchDone
    hmatchHalt hresultNotOne hmatchInputParked hmatchInv.parked
    hmatchOutputParked
  have hmissContract := entryMissCopyTM_hoareTime_frame tapes.entry entry
    (rest.flatMap Entry.encode) address.bits
    (outPrefix ++ emitted.flatMap Entry.encode) work matchDone.work
    matchDone.input matchDone.output hmatchInv hmatchInputParked
    hmatchOutputPrefix
  obtain ⟨missDone, missTime, hmissTime, hmissReach, hmissHalt,
      hmissInput, hmissReady, hmissOutput⟩ :=
    hmissContract matchDone.input matchDone.work matchDone.output
      ⟨rfl, rfl, rfl⟩
  have hmissReach' := entryUpdateTM_miss_reachesIn_internal tapes hmissReach
  have hmissInputParked : TM.Parked missDone.input := by
    rw [hmissInput, hmatchInput]
    exact hinput
  have hmissOutputParked : TM.Parked missDone.output :=
    parked_of_binaryPrefix_internal hmissOutput
  have hmissExit := entryUpdateTM_step_miss_halt_internal tapes missDone
    hmissHalt hmissInputParked hmissReady.parked hmissOutputParked
  have hremainingMiss :
      (missDone.work tapes.remaining).HasBinaryNat (rest.length + 1) := by
    rw [hmissReady.frame_outside_entry_internal tapes.remaining
      tapes.remaining_ne_entry]
    exact hremainingPositive
  obtain ⟨predDone, hpredReach, hpredHalt, hpredInput, hpredOther,
      hpredCount, hpredOutput⟩ :=
    TM.binaryPredTM_reachesIn_frame tapes.remaining rest.length
      missDone.input missDone.work missDone.output hremainingMiss
      hmissInputParked.read_ne_start
      (fun i _ => (hmissReady.parked i).read_ne_start)
      hmissOutputParked.read_ne_start
  have hpredReach' :=
    entryUpdateTM_remaining_reachesIn_internal tapes hpredReach
  have hreadyPred := hmissReady.change_remaining_internal hpredOther hpredCount
  have hpredInputParked : TM.Parked predDone.input := by
    rw [hpredInput]
    exact hmissInputParked
  have hpredOutputParked : TM.Parked predDone.output := by
    rw [hpredOutput]
    exact hmissOutputParked
  have hloop := entryUpdateTM_step_remaining_halt_internal tapes predDone
    hpredHalt hpredInputParked hreadyPred.parked hpredOutputParked
  have hinputFinal : predDone.input = inp :=
    hpredInput.trans (hmissInput.trans hmatchInput)
  have hloop' : (entryUpdateTM tapes).step
      (entryUpdateRemainingWrap tapes predDone) =
      some (entryUpdateTestCfg tapes inp predDone.work predDone.output) := by
    simpa [hinputFinal] using hloop
  have hmatchPrefix : (entryUpdateTM tapes).reachesIn (matchTime + 1)
      (entryUpdateTestCfg tapes inp work out)
      (entryUpdateMatchWrap tapes matchDone) :=
    .step htest hmatchReach'
  have htoMiss : (entryUpdateTM tapes).reachesIn (matchTime + 1 + 1)
      (entryUpdateTestCfg tapes inp work out)
      (entryUpdateMissWrap tapes
        { state := (entryMissCopyTM tapes.entry).qstart
          input := matchDone.input
          work := matchDone.work
          output := matchDone.output }) :=
    TM.reachesIn_trans _ hmatchPrefix (.step hdispatch .zero)
  have hthroughMiss :=
    TM.reachesIn_trans (entryUpdateTM tapes) htoMiss hmissReach'
  have htoPred := TM.reachesIn_trans (entryUpdateTM tapes) hthroughMiss
    (.step hmissExit .zero)
  have hthroughPred :=
    TM.reachesIn_trans (entryUpdateTM tapes) htoPred hpredReach'
  have hreach := TM.reachesIn_trans (entryUpdateTM tapes) hthroughPred
    (.step hloop' .zero)
  have hmissStatic :
      missTime ≤ entryUpdateMissTime tapes entry address :=
    le_trans hmissTime
      (entryMissCopyTime_le_entryUpdateMissTime_internal tapes entry address
        (rest.flatMap Entry.encode) work work matchDone.work hready hmatchInv)
  have htime :
      1 + matchTime + 1 + missTime + 1 +
          TM.binaryPredTime rest.length + 1 ≤
        entryUpdateIterationTime tapes entry rest address newValue
          store.length := by
    have hbranch : entryUpdateMissTime tapes entry address + 1 ≤
        entryUpdateBranchTime tapes entry address newValue store.length :=
      le_max_left _ _
    unfold entryUpdateIterationTime
    omega
  have hreplacementMiss :
      missDone.work tapes.replacement = work tapes.replacement :=
    hmissReady.frame_outside_entry_internal tapes.replacement
      tapes.replacement_ne_entry
  have hfoundMiss : missDone.work tapes.found = work tapes.found :=
    hmissReady.frame_outside_entry_internal tapes.found tapes.found_ne_entry
  have hresultCountMiss :
      missDone.work tapes.resultCount = work tapes.resultCount :=
    hmissReady.frame_outside_entry_internal tapes.resultCount
      tapes.resultCount_ne_entry
  have hreplacementPred :
      predDone.work tapes.replacement = missDone.work tapes.replacement :=
    hpredOther tapes.replacement
      (Ne.symm tapes.remaining_ne_replacement)
  have hfoundPred : predDone.work tapes.found = missDone.work tapes.found :=
    hpredOther tapes.found (Ne.symm tapes.remaining_ne_found)
  have hresultCountPred :
      predDone.work tapes.resultCount = missDone.work tapes.resultCount :=
    hpredOther tapes.resultCount (Ne.symm tapes.remaining_ne_resultCount)
  have hframeMiss : EntryUpdateFrame tapes initialWork missDone.work :=
    hinv.frame.trans_ready_internal hmissReady
  have hframePred : EntryUpdateFrame tapes initialWork predDone.work :=
    EntryUpdateFrame.trans_single_internal hframeMiss (9 : Fin 13) (by
      intro i hi
      apply hpredOther i
      simpa [EntryUpdateTapes.remaining] using hi)
  have hnextInv : EntryUpdateLoopInv tapes store address newValue
      (processed ++ [entry]) rest (emitted ++ [entry]) found resultCount
      initialWork predDone.work := by
    refine ⟨hinv.progress.miss_internal hne, hreadyPred, ?_, ?_, hpredCount,
      ?_, ?_, hinv.resultCount_le, hframePred⟩
    · rw [hreplacementPred, hreplacementMiss]
      exact hinv.replacement
    · exact hreplacementPred.trans
        (hreplacementMiss.trans hinv.replacement_eq)
    · rw [hfoundPred, hfoundMiss]
      exact hinv.foundCount
    · rw [hresultCountPred, hresultCountMiss]
      exact hinv.resultCountTape
  have hnextOutput : predDone.output.HasBinaryPrefix
      (outPrefix ++ (emitted ++ [entry]).flatMap Entry.encode) := by
    rw [hpredOutput]
    simpa [List.flatMap_append, List.append_assoc] using hmissOutput
  refine ⟨predDone.work, predDone.output,
    1 + matchTime + 1 + missTime + 1 +
      TM.binaryPredTime rest.length + 1, htime, ?_, hnextInv, hnextOutput⟩
  convert hreach using 1
  omega

end Machine

end RegisterStore

end RAM

end Complexity
