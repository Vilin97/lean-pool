/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMissCopy.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryCleanup
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryEncode

/-!
# Sparse-entry miss copy — proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem parked_of_binarySuffix {t : Tape} {bits : List Bool}
    (h : t.HasBinarySuffix bits) : TM.Parked t :=
  ⟨h.1, h.2.2.2⟩

private theorem parked_of_binaryPrefix {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : TM.Parked t :=
  ⟨by rw [h.1]; omega,
    (show t.HasBinaryContent bits from h.2).cells_ne_start⟩

private theorem entryMissCopiedWork_eq
    (tapes : EntryMatchTapes n) (entry : Entry)
    (matchedWork copiedWork : Fin n → Tape)
    (haddressCells : (copiedWork tapes.address).cells =
      (matchedWork tapes.address).cells)
    (haddressHead : (copiedWork tapes.address).head =
      entry.1.bits.length + 1)
    (hvalueCells : (copiedWork tapes.value).cells =
      (matchedWork tapes.value).cells)
    (hvalueHead : (copiedWork tapes.value).head =
      entry.2.bits.length + 1)
    (hframe : ∀ i, i ≠ tapes.address → i ≠ tapes.value →
      copiedWork i = matchedWork i) :
    copiedWork = entryMissCopiedWork tapes entry matchedWork := by
  funext i
  by_cases hia : i = tapes.address
  · subst i
    simp only [entryMissCopiedWork, ite_eq_left]
    exact Tape.ext haddressHead haddressCells
  · by_cases hiv : i = tapes.value
    · subst i
      simp only [entryMissCopiedWork, hia, ite_false, ite_eq_left]
      exact Tape.ext hvalueHead hvalueCells
    · simp only [entryMissCopiedWork, hia, hiv, ite_false]
      exact hframe i hia hiv

private theorem readableEntryMatch_rebase_after_copy
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits : List Bool)
    (baseWork initialWork copiedWork : Fin n → Tape)
    (hmatch : ReadableEntryMatch tapes entry rest queryBits baseWork initialWork)
    (haddressSuffix : (copiedWork tapes.address).HasBinarySuffix [])
    (haddressCells : (copiedWork tapes.address).cells =
      (initialWork tapes.address).cells)
    (hvalueSuffix : (copiedWork tapes.value).HasBinarySuffix [])
    (hvalueCells : (copiedWork tapes.value).cells =
      (initialWork tapes.value).cells)
    (hvalueHead : (copiedWork tapes.value).head =
      entry.2.bits.length + 1)
    (hframe : ∀ i, i ≠ tapes.address → i ≠ tapes.value →
      copiedWork i = initialWork i) :
    ReadableEntryMatch tapes entry rest queryBits copiedWork copiedWork := by
  have hsourceNeAddress : tapes.source ≠ tapes.address := tapes.ne (by decide)
  have hsourceNeValue : tapes.source ≠ tapes.value := tapes.ne (by decide)
  have haddressContent :
      (copiedWork tapes.address).HasBinaryContent entry.1.bits := by
    simpa only [Tape.HasBinaryContent, haddressCells] using! hmatch.address
  have hvalueContent :
      (copiedWork tapes.value).HasBinaryContent entry.2.bits := by
    simpa only [Tape.HasBinaryContent, hvalueCells] using! hmatch.value.2
  constructor
  · rw [hframe tapes.source hsourceNeAddress hsourceNeValue]
    exact hmatch.source
  · exact haddressContent
  · rw [haddressCells]
    exact hmatch.addressStart
  · exact ⟨hvalueHead, hvalueContent⟩
  · rw [hvalueCells]
    exact hmatch.valueStart
  · rw [hframe tapes.addressCounter (tapes.ne (by decide))
      (tapes.ne (by decide))]
    exact hmatch.addressCounter
  · rw [hframe tapes.addressCounter (tapes.ne (by decide))
      (tapes.ne (by decide))]
    exact hmatch.addressCounterStart
  · rw [hframe tapes.addressWidth (tapes.ne (by decide))
      (tapes.ne (by decide))]
    exact hmatch.addressWidth
  · rw [hframe tapes.valueCounter (tapes.ne (by decide))
      (tapes.ne (by decide))]
    exact hmatch.valueCounter
  · rw [hframe tapes.valueCounter (tapes.ne (by decide))
      (tapes.ne (by decide))]
    exact hmatch.valueCounterStart
  · rw [hframe tapes.valueWidth (tapes.ne (by decide))
      (tapes.ne (by decide))]
    exact hmatch.valueWidth
  · rw [hframe tapes.query (tapes.ne (by decide))
      (tapes.ne (by decide))]
    exact hmatch.query
  · rw [hframe tapes.query (tapes.ne (by decide))
      (tapes.ne (by decide))]
    exact hmatch.queryStart
  · rw [hframe tapes.result (tapes.ne (by decide))
      (tapes.ne (by decide))]
    exact hmatch.result
  · rw [hframe tapes.result (tapes.ne (by decide))
      (tapes.ne (by decide))]
    exact hmatch.resultStart
  · intro i
    by_cases hia : i = tapes.address
    · subst i
      exact parked_of_binarySuffix haddressSuffix
    · by_cases hiv : i = tapes.value
      · subst i
        exact parked_of_binarySuffix hvalueSuffix
      · rw [hframe i hia hiv]
        exact hmatch.parked i
  · intro i
    exact Nat.le_add_right _ _
  · intro i _ _ _ _ _ _ _ _ _
    rfl

theorem entryMissCopyTM_hoareTime_frame_internal
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits emitted : List Bool)
    (initialWork matchedWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hmatch : ReadableEntryMatch tapes entry rest queryBits initialWork matchedWork)
    (hinput : TM.Parked inp₀) (houtput : out₀.HasBinaryPrefix emitted) :
    (entryMissCopyTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = matchedWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryScanReady tapes rest queryBits initialWork work ∧
        out.HasBinaryPrefix (emitted ++ Entry.encode entry))
      (entryMissCopyTime tapes entry queryBits initialWork matchedWork) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  let copiedWork := entryMissCopiedWork tapes entry matchedWork
  have hencode := rewindEntryEncodeTM_hoareTime_frame tapes.encodeTapes entry
    (entryMissHeadBound entry queryBits initialWork tapes.address)
    (entryMissHeadBound entry queryBits initialWork tapes.value)
    emitted inp₀ matchedWork out₀ hmatch.address hmatch.addressStart
    ⟨(hmatch.parked tapes.address).1, hmatch.headBound tapes.address⟩
    hmatch.value.2 hmatch.valueStart
    ⟨(hmatch.parked tapes.value).1, hmatch.headBound tapes.value⟩
    hinput (fun i _ _ => hmatch.parked i) houtput
  obtain ⟨encoded, encodeTime, hencodeTime, hencodeReach, hencodeHalt,
      hencodedInput, haddressSuffix, haddressCells, haddressHead,
      hvalueSuffix, hvalueCells, hvalueHead, hencodedFrame,
      hencodedOutput⟩ :=
    hencode inp₀ matchedWork out₀ ⟨rfl, rfl, rfl⟩
  have hencodedWork : encoded.work = copiedWork := by
    apply entryMissCopiedWork_eq tapes entry matchedWork encoded.work
    · simpa using! haddressCells
    · simpa using! haddressHead
    · simpa using! hvalueCells
    · simpa using! hvalueHead
    · intro i hia hiv
      exact hencodedFrame i hia hiv
  have hmatchSelf :
      ReadableEntryMatch tapes entry rest queryBits copiedWork copiedWork := by
    have hmatchCopied :
        ReadableEntryMatch tapes entry rest queryBits encoded.work encoded.work :=
      readableEntryMatch_rebase_after_copy tapes entry rest queryBits
        initialWork matchedWork encoded.work hmatch
        (by simpa using! haddressSuffix) (by simpa using! haddressCells)
        (by simpa using! hvalueSuffix)
        (by simpa using! hvalueCells) (by simpa using! hvalueHead)
        (by
          intro i hia hiv
          exact hencodedFrame i hia hiv)
    simpa [hencodedWork] using! hmatchCopied
  have hencodedInputParked : TM.Parked encoded.input := by
    rw [hencodedInput]
    exact hinput
  have hencodedWorkParked : ∀ i, TM.Parked (encoded.work i) := by
    intro i
    rw [hencodedWork]
    exact hmatchSelf.parked i
  have hencodedOutputParked : TM.Parked encoded.output :=
    parked_of_binaryPrefix hencodedOutput
  have hcleanup := entryMissCleanupTM_hoareTime_frame tapes entry rest queryBits
    copiedWork copiedWork encoded.input encoded.output hmatchSelf
    (by simpa [hencodedInput] using! hinput) hencodedOutputParked
  obtain ⟨cleaned, cleanupTime, hcleanupTime, hcleanupReach, hcleanupHalt,
      hcleanedInput, hready, hcleanedOutput⟩ :=
    hcleanup encoded.input copiedWork encoded.output ⟨rfl, rfl, rfl⟩
  obtain ⟨hinputTransition, hworkTransition, houtputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hencodedInputParked.read_ne_start
      (fun i => (hencodedWorkParked i).read_ne_start)
      hencodedOutputParked.read_ne_start
  have hworkTransition' :
      (fun i => TM.transitionTape (encoded.work i)) = copiedWork :=
    hworkTransition.trans hencodedWork
  have hcleanupReach' : (entryMissCleanupTM tapes).reachesIn cleanupTime
      { state := (entryMissCleanupTM tapes).qstart
        input := TM.transitionInput encoded.input
        work := fun i => TM.transitionTape (encoded.work i)
        output := TM.transitionTape encoded.output }
      cleaned := by
    simpa only [hinputTransition, hworkTransition', houtputTransition]
      using! hcleanupReach
  have hreach := TM.seqTM_reachesIn_of_reachesIn
    (rewindEntryEncodeTM tapes.encodeTapes) (entryMissCleanupTM tapes)
    hencodeReach hencodeHalt hcleanupReach'
  let finalCfg := TM.phase2Wrap (rewindEntryEncodeTM tapes.encodeTapes)
    (entryMissCleanupTM tapes) cleaned
  refine ⟨finalCfg, encodeTime + 1 + cleanupTime, ?_, hreach, ?_, ?_⟩
  · unfold entryMissCopyTime
    change encodeTime + 1 + cleanupTime ≤
      rewindEntryEncodeTime entry
          (entryMissHeadBound entry queryBits initialWork tapes.address)
          (entryMissHeadBound entry queryBits initialWork tapes.value) +
        1 + entryMissCleanupTime tapes entry queryBits copiedWork
    omega
  · change (entryMissCopyTM tapes).halted finalCfg
    unfold entryMissCopyTM
    exact (TM.phase2Wrap_halted_iff (rewindEntryEncodeTM tapes.encodeTapes)
    (entryMissCleanupTM tapes) cleaned).mpr hcleanupHalt
  · have hreadyGlobal :
        EntryScanReady tapes rest queryBits initialWork cleaned.work := by
      refine ⟨hready.source, hready.address, hready.addressStart,
        hready.value, hready.valueStart, hready.addressCounter,
        hready.addressWidth, hready.valueCounter, hready.valueWidth,
        hready.query, hready.queryStart, hready.result, hready.resultStart,
        hready.parked, ?_⟩
      intro i hsource haddress hvalue haddressCounter haddressWidth
        hvalueCounter hvalueWidth hquery hresult
      have hcopied : copiedWork i = matchedWork i := by
        simp [copiedWork, entryMissCopiedWork, haddress, hvalue]
      exact (hready.frame i hsource haddress hvalue haddressCounter
        haddressWidth hvalueCounter hvalueWidth hquery hresult).trans
        (hcopied.trans (hmatch.frame i hsource haddress hvalue
          haddressCounter haddressWidth hvalueCounter hvalueWidth hquery
          hresult))
    refine ⟨?_, hreadyGlobal, ?_⟩
    · simpa [finalCfg] using! hcleanedInput.trans hencodedInput
    · change cleaned.output.HasBinaryPrefix (emitted ++ Entry.encode entry)
      rw [hcleanedOutput]
      exact hencodedOutput

end Machine

end RegisterStore

end RAM

end Complexity
