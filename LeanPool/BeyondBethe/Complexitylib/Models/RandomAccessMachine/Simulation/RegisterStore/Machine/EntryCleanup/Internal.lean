/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryCleanup.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany
public import Mathlib.Tactic.FinCases
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

/-!
# Sparse-entry miss cleanup — proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem entryMissTargets_nodup (tapes : EntryMatchTapes n) :
    (entryMissTargets tapes).Nodup := by
  exact List.nodup_ofFn_ofInjective tapes.cleanupIdx_injective

private theorem cleanupIdx_mem (tapes : EntryMatchTapes n) (slot : Fin 7) :
    tapes.cleanupIdx slot ∈ entryMissTargets tapes := by
  exact List.mem_ofFn.mpr ⟨slot, rfl⟩

private theorem source_not_mem_entryMissTargets (tapes : EntryMatchTapes n) :
    tapes.source ∉ entryMissTargets tapes := by
  intro hmem
  obtain ⟨slot, hslot⟩ := List.mem_ofFn.mp hmem
  have hidx := tapes.injective hslot
  have hval := congrArg Fin.val hidx
  change (if slot.val = 6 then 8 else slot.val + 1) = 0 at hval
  split at hval <;> omega

private theorem query_not_mem_entryMissTargets (tapes : EntryMatchTapes n) :
    tapes.query ∉ entryMissTargets tapes := by
  intro hmem
  obtain ⟨slot, hslot⟩ := List.mem_ofFn.mp hmem
  have hidx := tapes.injective hslot
  have hval := congrArg Fin.val hidx
  change (if slot.val = 6 then 8 else slot.val + 1) = 7 at hval
  split at hval <;> omega

private theorem cleanupIdx_ne_query (tapes : EntryMatchTapes n)
    (slot : Fin 7) : tapes.cleanupIdx slot ≠ tapes.query := by
  intro heq
  exact query_not_mem_entryMissTargets tapes
    (heq ▸ cleanupIdx_mem tapes slot)

private theorem readable_target_content
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits : List Bool)
    (initialWork matchedWork : Fin n → Tape)
    (hmatch : ReadableEntryMatch tapes entry rest queryBits initialWork matchedWork) :
    ∀ i, i ∈ entryMissTargets tapes →
      (matchedWork i).HasBinaryContent (entryMissBits tapes entry queryBits i) := by
  intro i hi
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
  fin_cases slot
  · simpa [entryMissBits, EntryMatchTapes.address, EntryMatchTapes.value,
      EntryMatchTapes.addressCounter, EntryMatchTapes.addressWidth,
      EntryMatchTapes.valueCounter, EntryMatchTapes.valueWidth,
      EntryMatchTapes.result, tapes.injective.eq_iff] using hmatch.address
  · simpa [entryMissBits, EntryMatchTapes.address, EntryMatchTapes.value,
      EntryMatchTapes.addressCounter, EntryMatchTapes.addressWidth,
      EntryMatchTapes.valueCounter, EntryMatchTapes.valueWidth,
      EntryMatchTapes.result, tapes.injective.eq_iff] using! hmatch.value.2
  · dsimp only [EntryMatchTapes.cleanupIdx]
    change (matchedWork tapes.addressCounter).HasBinaryContent
      (entryMissBits tapes entry queryBits tapes.addressCounter)
    unfold entryMissBits
    have haddress : tapes.addressCounter ≠ tapes.address :=
      tapes.ne (show (3 : Fin 9) ≠ 1 by decide)
    have hvalue : tapes.addressCounter ≠ tapes.value :=
      tapes.ne (show (3 : Fin 9) ≠ 2 by decide)
    rw [ite_eq_right haddress, ite_eq_right hvalue, ite_eq_left rfl]
    exact hmatch.addressCounter.2
  · simpa [entryMissBits, EntryMatchTapes.address, EntryMatchTapes.value,
      EntryMatchTapes.addressCounter, EntryMatchTapes.addressWidth,
      EntryMatchTapes.valueCounter, EntryMatchTapes.valueWidth,
      EntryMatchTapes.result, tapes.injective.eq_iff] using
      hmatch.addressWidth.2.hasBinaryContent
  · dsimp only [EntryMatchTapes.cleanupIdx]
    change (matchedWork tapes.valueCounter).HasBinaryContent
      (entryMissBits tapes entry queryBits tapes.valueCounter)
    unfold entryMissBits
    have haddress : tapes.valueCounter ≠ tapes.address :=
      tapes.ne (show (5 : Fin 9) ≠ 1 by decide)
    have hvalue : tapes.valueCounter ≠ tapes.value :=
      tapes.ne (show (5 : Fin 9) ≠ 2 by decide)
    have haddressCounter : tapes.valueCounter ≠ tapes.addressCounter :=
      tapes.ne (show (5 : Fin 9) ≠ 3 by decide)
    have haddressWidth : tapes.valueCounter ≠ tapes.addressWidth :=
      tapes.ne (show (5 : Fin 9) ≠ 4 by decide)
    rw [ite_eq_right haddress, ite_eq_right hvalue, ite_eq_right haddressCounter,
      ite_eq_right haddressWidth, ite_eq_left rfl]
    exact hmatch.valueCounter.2
  · simpa [entryMissBits, EntryMatchTapes.address, EntryMatchTapes.value,
      EntryMatchTapes.addressCounter, EntryMatchTapes.addressWidth,
      EntryMatchTapes.valueCounter, EntryMatchTapes.valueWidth,
      EntryMatchTapes.result, tapes.injective.eq_iff] using
      hmatch.valueWidth.2.hasBinaryContent
  · simpa [entryMissBits, EntryMatchTapes.address, EntryMatchTapes.value,
      EntryMatchTapes.addressCounter, EntryMatchTapes.addressWidth,
      EntryMatchTapes.valueCounter, EntryMatchTapes.valueWidth,
      EntryMatchTapes.result, tapes.injective.eq_iff] using
      hmatch.result.hasBinaryContent

private theorem readable_target_start
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits : List Bool)
    (initialWork matchedWork : Fin n → Tape)
    (hmatch : ReadableEntryMatch tapes entry rest queryBits initialWork matchedWork) :
    ∀ i, i ∈ entryMissTargets tapes → (matchedWork i).cells 0 = Γ.start := by
  intro i hi
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
  fin_cases slot
  · exact hmatch.addressStart
  · exact hmatch.valueStart
  · exact hmatch.addressCounterStart
  · exact hmatch.addressWidth.1
  · exact hmatch.valueCounterStart
  · exact hmatch.valueWidth.1
  · exact hmatch.resultStart

private theorem readable_target_head
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits : List Bool)
    (initialWork matchedWork : Fin n → Tape)
    (hmatch : ReadableEntryMatch tapes entry rest queryBits initialWork matchedWork) :
    ∀ i, i ∈ entryMissTargets tapes →
      (matchedWork i).head ≤ entryMissHeadBound entry queryBits initialWork i := by
  intro i _
  exact hmatch.headBound i

private theorem resetBinaryBlank_hasBinaryNat_zero :
    TM.resetBinaryBlank.HasBinaryNat 0 := by
  simpa [TM.resetBinaryBlank] using Tape.init_move_right_hasBinaryNat 0

private theorem resetBinaryBlank_start :
    TM.resetBinaryBlank.cells 0 = Γ.start := by
  simp [TM.resetBinaryBlank, Tape.init, Tape.move]

private theorem hasBinaryString_parked {t : Tape} {bits : List Bool}
    (h : t.HasBinaryString bits) : TM.Parked t :=
  ⟨by rw [h.1], Tape.cells_ne_start_of_hasBinaryString h⟩

private theorem entryMissCleanup_post
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits : List Bool)
    (initialWork matchedWork rewoundWork : Fin n → Tape)
    (hmatch : ReadableEntryMatch tapes entry rest queryBits initialWork matchedWork)
    (hrewoundQuery : rewoundWork tapes.query =
      (Tape.init (queryBits.map Γ.ofBool)).move Dir3.right)
    (hrewoundOther : ∀ i, i ≠ tapes.query → rewoundWork i = matchedWork i)
    (hrewoundParked : ∀ i, TM.Parked (rewoundWork i)) :
    EntryScanReady tapes rest queryBits initialWork
      (TM.resetBinaryWorkManyResult rewoundWork (entryMissTargets tapes)) := by
  let finalWork := TM.resetBinaryWorkManyResult rewoundWork (entryMissTargets tapes)
  have hsource : finalWork tapes.source = rewoundWork tapes.source :=
    TM.resetBinaryWorkManyResult_eq_of_not_mem rewoundWork _ tapes.source
      (source_not_mem_entryMissTargets tapes)
  have hquery : finalWork tapes.query = rewoundWork tapes.query :=
    TM.resetBinaryWorkManyResult_eq_of_not_mem rewoundWork _ tapes.query
      (query_not_mem_entryMissTargets tapes)
  have hblank : ∀ slot : Fin 7,
      finalWork (tapes.cleanupIdx slot) = TM.resetBinaryBlank := by
    intro slot
    exact TM.resetBinaryWorkManyResult_eq_blank_of_mem rewoundWork _ _
      (cleanupIdx_mem tapes slot)
  have hblankPrefix : ∀ slot : Fin 7,
      (finalWork (tapes.cleanupIdx slot)).HasBinaryPrefix [] := by
    intro slot
    rw [hblank]
    exact Tape.init_nil_move_right_hasBinaryPrefix_nil
  have hblankStart : ∀ slot : Fin 7,
      (finalWork (tapes.cleanupIdx slot)).cells 0 = Γ.start := by
    intro slot
    rw [hblank]
    exact resetBinaryBlank_start
  have hblankNat : ∀ slot : Fin 7,
      (finalWork (tapes.cleanupIdx slot)).HasBinaryNat 0 := by
    intro slot
    rw [hblank]
    exact resetBinaryBlank_hasBinaryNat_zero
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hsourceOther : rewoundWork tapes.source = matchedWork tapes.source :=
      hrewoundOther tapes.source (tapes.ne (by decide))
    have h := hmatch.source
    rw [← hsourceOther, ← hsource] at h
    simpa [finalWork] using h
  · simpa [finalWork] using hblankPrefix 0
  · simpa [finalWork] using hblankStart 0
  · simpa [finalWork] using hblankPrefix 1
  · simpa [finalWork] using hblankStart 1
  · simpa [finalWork] using hblankNat 2
  · simpa [finalWork] using hblankNat 3
  · simpa [finalWork] using hblankNat 4
  · simpa [finalWork] using hblankNat 5
  · have h := Tape.init_move_right_hasBinaryString queryBits
    rw [← hrewoundQuery, ← hquery] at h
    simpa [finalWork] using h
  · have hfinalQuery :
        TM.resetBinaryWorkManyResult rewoundWork (entryMissTargets tapes)
            tapes.query =
          (Tape.init (queryBits.map Γ.ofBool)).move Dir3.right := by
      simpa [finalWork] using hquery.trans hrewoundQuery
    rw [hfinalQuery]
    simp [Tape.init, Tape.move]
  · simpa [finalWork] using hblankPrefix 6
  · simpa [finalWork] using hblankStart 6
  · exact TM.resetBinaryWorkManyResult_parked rewoundWork _ hrewoundParked
  · intro i hsourceNe haddressNe hvalueNe haddressCounterNe
      haddressWidthNe hvalueCounterNe hvalueWidthNe hqueryNe hresultNe
    have hnotmem : i ∉ entryMissTargets tapes := by
      intro hmem
      obtain ⟨slot, hslot⟩ := List.mem_ofFn.mp hmem
      fin_cases slot <;> simp_all
    have hframe := hmatch.frame i hsourceNe haddressNe hvalueNe
      haddressCounterNe haddressWidthNe hvalueCounterNe hvalueWidthNe
      hqueryNe hresultNe
    have hrewound := hrewoundOther i hqueryNe
    simpa [finalWork,
      TM.resetBinaryWorkManyResult_eq_of_not_mem rewoundWork _ i hnotmem]
      using hrewound.trans hframe

theorem entryMissCleanupTM_hoareTime_frame_internal
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits : List Bool)
    (initialWork matchedWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hmatch : ReadableEntryMatch tapes entry rest queryBits initialWork matchedWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryMissCleanupTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = matchedWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryScanReady tapes rest queryBits initialWork work ∧
        out = out₀)
      (entryMissCleanupTime tapes entry queryBits initialWork) := by
  let queryTape := (Tape.init (queryBits.map Γ.ofBool)).move Dir3.right
  let rewoundWork := Function.update matchedWork tapes.query queryTape
  have hrewindBase := TM.rewindBinaryWorkTM_hoareTime_frame tapes.query
    queryBits (entryMissHeadBound entry queryBits initialWork tapes.query)
    inp₀ matchedWork out₀ hmatch.query hmatch.queryStart
    ⟨(hmatch.parked tapes.query).1, hmatch.headBound tapes.query⟩ hinput
    (fun i _ => hmatch.parked i) houtput
  have hrewind : (TM.rewindWorkTM tapes.query).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = matchedWork ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = rewoundWork ∧ out = out₀)
      (entryMissHeadBound entry queryBits initialWork tapes.query + 2) := by
    exact hrewindBase.strengthen_post (by
      intro inp work out hpost
      rcases hpost with ⟨hinp, hquery, hother, hout⟩
      refine ⟨hinp, ?_, hout⟩
      funext i
      by_cases hi : i = tapes.query
      · subst i
        simpa [rewoundWork, queryTape] using hquery
      · simpa [rewoundWork, Function.update_of_ne hi] using hother i hi)
  have hrewoundOther : ∀ i, i ≠ tapes.query →
      rewoundWork i = matchedWork i := by
    intro i hi
    simp [rewoundWork, Function.update_of_ne hi]
  have hrewoundParked : ∀ i, TM.Parked (rewoundWork i) := by
    intro i
    by_cases hi : i = tapes.query
    · subst i
      rw [show rewoundWork tapes.query = queryTape by
        simp [rewoundWork, Function.update_self]]
      exact hasBinaryString_parked (by
        simpa [queryTape] using Tape.init_move_right_hasBinaryString queryBits)
    · rw [hrewoundOther i hi]
      exact hmatch.parked i
  have htargetContent : ∀ i, i ∈ entryMissTargets tapes →
      (rewoundWork i).HasBinaryContent (entryMissBits tapes entry queryBits i) := by
    intro i hi
    have hne : i ≠ tapes.query := by
      intro heq
      exact query_not_mem_entryMissTargets tapes (heq ▸ hi)
    rw [hrewoundOther i hne]
    exact readable_target_content tapes entry rest queryBits initialWork
      matchedWork hmatch i hi
  have htargetStart : ∀ i, i ∈ entryMissTargets tapes →
      (rewoundWork i).cells 0 = Γ.start := by
    intro i hi
    have hne : i ≠ tapes.query := by
      intro heq
      exact query_not_mem_entryMissTargets tapes (heq ▸ hi)
    rw [hrewoundOther i hne]
    exact readable_target_start tapes entry rest queryBits initialWork
      matchedWork hmatch i hi
  have htargetHead : ∀ i, i ∈ entryMissTargets tapes →
      (rewoundWork i).head ≤ entryMissHeadBound entry queryBits initialWork i := by
    intro i hi
    have hne : i ≠ tapes.query := by
      intro heq
      exact query_not_mem_entryMissTargets tapes (heq ▸ hi)
    rw [hrewoundOther i hne]
    exact hmatch.headBound i
  have hreset := TM.resetBinaryWorkManyTM_hoareTime_frame
    (entryMissTargets tapes) (entryMissBits tapes entry queryBits)
    (entryMissHeadBound entry queryBits initialWork) inp₀ rewoundWork out₀
    (entryMissTargets_nodup tapes) htargetContent htargetStart htargetHead
    hinput hrewoundParked houtput
  have hseq := TM.seqTM_hoareTime (TM.rewindWorkTM tapes.query)
    (TM.resetBinaryWorkManyTM (entryMissTargets tapes)) hrewind
    (by
      intro inp work out hmid
      rcases hmid with ⟨hinp, hwork, hout⟩
      subst work
      obtain ⟨hinpTransition, hworkTransition, houtTransition⟩ :=
        TM.phaseTransition_eq_self_of_reads_ne_start
          (hinp ▸ hinput.read_ne_start)
          (fun i => (hrewoundParked i).read_ne_start)
          (hout ▸ houtput.read_ne_start)
      rw [hinpTransition, hworkTransition, houtTransition]
      exact ⟨hinp, rfl, hout⟩)
    hreset
  have hfinal := hseq.strengthen_post
    (post' := fun inp work out =>
      inp = inp₀ ∧
      EntryScanReady tapes rest queryBits initialWork work ∧
      out = out₀) (by
    intro inp work out hpost
    rcases hpost with ⟨hinp, hwork, hout⟩
    subst work
    exact ⟨hinp,
      entryMissCleanup_post tapes entry rest queryBits initialWork matchedWork
        rewoundWork hmatch (by simp [rewoundWork, queryTape]) hrewoundOther
        hrewoundParked,
      hout⟩)
  simpa [entryMissCleanupTM, entryMissCleanupTime] using hfinal

end Machine

end RegisterStore

end RAM

end Complexity
