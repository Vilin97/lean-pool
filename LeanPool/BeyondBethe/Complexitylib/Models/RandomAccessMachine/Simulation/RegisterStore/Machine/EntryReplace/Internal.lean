/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryReplace.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryCleanup
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryEncode

/-!
# Sparse-entry replacement — proof internals
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

private theorem readableEntryMatch_rebase_after_address_emit
    (tapes : EntryReplaceTapes n) (entry : Entry)
    (rest queryBits : List Bool) (baseWork matchedWork readyWork : Fin n → Tape)
    (hmatch : ReadableEntryMatch tapes.entry entry rest queryBits
      baseWork matchedWork)
    (haddressSuffix : (readyWork tapes.entry.address).HasBinarySuffix [])
    (haddressCells : (readyWork tapes.entry.address).cells =
      (matchedWork tapes.entry.address).cells)
    (hframe : ∀ i, i ≠ tapes.entry.address → readyWork i = matchedWork i) :
    ReadableEntryMatch tapes.entry entry rest queryBits readyWork readyWork := by
  have haddressContent :
      (readyWork tapes.entry.address).HasBinaryContent entry.1.bits := by
    simpa only [Tape.HasBinaryContent, haddressCells] using! hmatch.address
  constructor
  · rw [hframe tapes.entry.source (tapes.entry.ne (by decide))]
    exact hmatch.source
  · exact haddressContent
  · rw [haddressCells]
    exact hmatch.addressStart
  · rw [hframe tapes.entry.value (tapes.entry.ne (by decide))]
    exact hmatch.value
  · rw [hframe tapes.entry.value (tapes.entry.ne (by decide))]
    exact hmatch.valueStart
  · rw [hframe tapes.entry.addressCounter (tapes.entry.ne (by decide))]
    exact hmatch.addressCounter
  · rw [hframe tapes.entry.addressCounter (tapes.entry.ne (by decide))]
    exact hmatch.addressCounterStart
  · rw [hframe tapes.entry.addressWidth (tapes.entry.ne (by decide))]
    exact hmatch.addressWidth
  · rw [hframe tapes.entry.valueCounter (tapes.entry.ne (by decide))]
    exact hmatch.valueCounter
  · rw [hframe tapes.entry.valueCounter (tapes.entry.ne (by decide))]
    exact hmatch.valueCounterStart
  · rw [hframe tapes.entry.valueWidth (tapes.entry.ne (by decide))]
    exact hmatch.valueWidth
  · rw [hframe tapes.entry.query (tapes.entry.ne (by decide))]
    exact hmatch.query
  · rw [hframe tapes.entry.query (tapes.entry.ne (by decide))]
    exact hmatch.queryStart
  · rw [hframe tapes.entry.result (tapes.entry.ne (by decide))]
    exact hmatch.result
  · rw [hframe tapes.entry.result (tapes.entry.ne (by decide))]
    exact hmatch.resultStart
  · intro i
    by_cases hia : i = tapes.entry.address
    · subst i
      exact parked_of_binarySuffix haddressSuffix
    · rw [hframe i hia]
      exact hmatch.parked i
  · intro i
    exact Nat.le_add_right _ _
  · intro i _ _ _ _ _ _ _ _ _
    rfl

private theorem entryReplaceReadyWork_eq
    (tapes : EntryReplaceTapes n) (entry : Entry)
    (matchedWork readyWork : Fin n → Tape)
    (haddressCells : (readyWork tapes.entry.address).cells =
      (matchedWork tapes.entry.address).cells)
    (haddressHead : (readyWork tapes.entry.address).head =
      entry.1.bits.length + 1)
    (hframe : ∀ i, i ≠ tapes.entry.address → readyWork i = matchedWork i) :
    readyWork = entryReplaceReadyWork tapes entry matchedWork := by
  funext i
  by_cases hia : i = tapes.entry.address
  · subst i
    simp only [entryReplaceReadyWork, ite_eq_left]
    exact Tape.ext haddressHead haddressCells
  · simp only [entryReplaceReadyWork, hia, ite_false]
    exact hframe i hia

theorem entryReplaceCleanupTM_hoareTime_frame_internal
    (tapes : EntryReplaceTapes n) (entry : Entry) (newValue : ℕ)
    (rest queryBits emitted : List Bool)
    (initialWork matchedWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hmatch : ReadableEntryMatch tapes.entry entry rest queryBits
      initialWork matchedWork)
    (hreplacement : (matchedWork tapes.replacement).HasBinaryNat newValue)
    (hinput : TM.Parked inp₀) (houtput : out₀.HasBinaryPrefix emitted) :
    (entryReplaceCleanupTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = matchedWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryScanReady tapes.entry rest queryBits initialWork work ∧
        work tapes.replacement = matchedWork tapes.replacement ∧
        out.HasBinaryPrefix
          (emitted ++ Entry.encode (entry.1, newValue)))
      (entryReplaceCleanupTime tapes entry newValue queryBits
        initialWork matchedWork) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  let readyWork := entryReplaceReadyWork tapes entry matchedWork
  have hencode := rewindEntryEncodeTM_hoareTime_frame tapes.encodeTapes
    (entry.1, newValue)
    (entryMissHeadBound entry queryBits initialWork tapes.entry.address) 1
    emitted inp₀ matchedWork out₀ hmatch.address hmatch.addressStart
    ⟨(hmatch.parked tapes.entry.address).1,
      hmatch.headBound tapes.entry.address⟩
    hreplacement.2.hasBinaryContent hreplacement.1
    (by
      have hhead : 1 ≤ (matchedWork tapes.replacement).head ∧
          (matchedWork tapes.replacement).head ≤ 1 := by
        rw [hreplacement.2.1]
        exact ⟨le_rfl, le_rfl⟩
      simpa using! hhead)
    hinput (fun i _ _ => hmatch.parked i) houtput
  obtain ⟨encoded, encodeTime, hencodeTime, hencodeReach, hencodeHalt,
      hencodedInput, haddressSuffix, haddressCells, haddressHead,
      hreplacementSuffix, hreplacementCells, hreplacementHead,
      hencodedFrame, hencodedOutput⟩ :=
    hencode inp₀ matchedWork out₀ ⟨rfl, rfl, rfl⟩
  have hencodedInputParked : TM.Parked encoded.input := by
    rw [hencodedInput]
    exact hinput
  have hencodedOutputParked : TM.Parked encoded.output :=
    parked_of_binaryPrefix hencodedOutput
  have hencodedWorkParked : ∀ i, TM.Parked (encoded.work i) := by
    intro i
    by_cases hia : i = tapes.entry.address
    · subst i
      exact parked_of_binarySuffix haddressSuffix
    · by_cases hir : i = tapes.replacement
      · subst i
        exact parked_of_binarySuffix hreplacementSuffix
      · rw [hencodedFrame i hia hir]
        exact hmatch.parked i
  have hreplacementContent :
      (encoded.work tapes.replacement).HasBinaryContent newValue.bits := by
    have hcells : (encoded.work tapes.replacement).cells =
        (matchedWork tapes.replacement).cells := by
      simpa using! hreplacementCells
    simpa only [Tape.HasBinaryContent, hcells] using!
      hreplacement.2.hasBinaryContent
  have hreplacementStart :
      (encoded.work tapes.replacement).cells 0 = Γ.start := by
    have hcells : (encoded.work tapes.replacement).cells =
        (matchedWork tapes.replacement).cells := by
      simpa using! hreplacementCells
    rw [hcells]
    exact hreplacement.1
  have hreplacementHead' : (encoded.work tapes.replacement).head =
      newValue.bits.length + 1 := by
    simpa using! hreplacementHead
  have hrewind := TM.rewindBinaryWorkTM_hoareTime_frame tapes.replacement
    newValue.bits (newValue.bits.length + 1) encoded.input encoded.work
    encoded.output hreplacementContent hreplacementStart
    ⟨by rw [hreplacementHead']; omega, by rw [hreplacementHead']⟩
    hencodedInputParked
    (fun i _ => hencodedWorkParked i) hencodedOutputParked
  obtain ⟨rewound, rewindTime, hrewindTime, hrewindReach, hrewindHalt,
      hrewoundInput, hrewoundReplacement, hrewoundFrame,
      hrewoundOutput⟩ :=
    hrewind encoded.input encoded.work encoded.output ⟨rfl, rfl, rfl⟩
  have hmatchedReplacement : matchedWork tapes.replacement =
      (Tape.init (newValue.bits.map Γ.ofBool)).move Dir3.right :=
    Tape.eq_init_move_right_of_hasBinaryString hreplacement.2 hreplacement.1
  have hreplacementRestored :
      rewound.work tapes.replacement = matchedWork tapes.replacement :=
    hrewoundReplacement.trans hmatchedReplacement.symm
  have hreadyWorkEq : rewound.work = readyWork := by
    apply entryReplaceReadyWork_eq tapes entry matchedWork rewound.work
    · rw [hrewoundFrame tapes.entry.address
        (Ne.symm (tapes.replacement_ne 1))]
      simpa using! haddressCells
    · rw [hrewoundFrame tapes.entry.address
        (Ne.symm (tapes.replacement_ne 1))]
      simpa using! haddressHead
    · intro i hia
      by_cases hir : i = tapes.replacement
      · subst i
        exact hreplacementRestored
      · exact (hrewoundFrame i hir).trans (hencodedFrame i hia hir)
  have hmatchSelf : ReadableEntryMatch tapes.entry entry rest queryBits
      readyWork readyWork := by
    have hmatchReady := readableEntryMatch_rebase_after_address_emit tapes
      entry rest queryBits initialWork matchedWork rewound.work hmatch
      (by
        rw [hrewoundFrame tapes.entry.address
          (Ne.symm (tapes.replacement_ne 1))]
        simpa using! haddressSuffix)
      (by
        rw [hrewoundFrame tapes.entry.address
          (Ne.symm (tapes.replacement_ne 1))]
        simpa using! haddressCells)
      (by
        intro i hia
        by_cases hir : i = tapes.replacement
        · subst i
          exact hreplacementRestored
        · exact (hrewoundFrame i hir).trans (hencodedFrame i hia hir))
    simpa [hreadyWorkEq] using! hmatchReady
  have hrewoundInputParked : TM.Parked rewound.input := by
    rw [hrewoundInput, hencodedInput]
    exact hinput
  have hrewoundOutputParked : TM.Parked rewound.output := by
    rw [hrewoundOutput]
    exact hencodedOutputParked
  have hrewoundWorkParked : ∀ i, TM.Parked (rewound.work i) := by
    intro i
    rw [hreadyWorkEq]
    exact hmatchSelf.parked i
  have hcleanup := entryMissCleanupTM_hoareTime_frame tapes.entry entry rest
    queryBits readyWork readyWork rewound.input rewound.output hmatchSelf
    hrewoundInputParked hrewoundOutputParked
  obtain ⟨cleaned, cleanupTime, hcleanupTime, hcleanupReach, hcleanupHalt,
      hcleanedInput, hready, hcleanedOutput⟩ :=
    hcleanup rewound.input readyWork rewound.output ⟨rfl, rfl, rfl⟩
  obtain ⟨hrewindInputTransition, hrewindWorkTransition,
      hrewindOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hrewoundInputParked.read_ne_start
      (fun i => (hrewoundWorkParked i).read_ne_start)
      hrewoundOutputParked.read_ne_start
  have hrewindWorkTransition' :
      (fun i => TM.transitionTape (rewound.work i)) = readyWork :=
    hrewindWorkTransition.trans hreadyWorkEq
  have hcleanupReach' : (entryMissCleanupTM tapes.entry).reachesIn cleanupTime
      { state := (entryMissCleanupTM tapes.entry).qstart
        input := TM.transitionInput rewound.input
        work := fun i => TM.transitionTape (rewound.work i)
        output := TM.transitionTape rewound.output }
      cleaned := by
    simpa only [hrewindInputTransition, hrewindWorkTransition',
      hrewindOutputTransition] using! hcleanupReach
  have htailReach := TM.seqTM_reachesIn_of_reachesIn
    (TM.rewindWorkTM tapes.replacement) (entryMissCleanupTM tapes.entry)
    hrewindReach hrewindHalt hcleanupReach'
  let tailFinal := TM.phase2Wrap (TM.rewindWorkTM tapes.replacement)
    (entryMissCleanupTM tapes.entry) cleaned
  have htailHalt :
      (TM.seqTM (TM.rewindWorkTM tapes.replacement)
        (entryMissCleanupTM tapes.entry)).halted tailFinal := by
    rw [TM.phase2Wrap_halted_iff]
    exact hcleanupHalt
  obtain ⟨hencodedInputTransition, hencodedWorkTransition,
      hencodedOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hencodedInputParked.read_ne_start
      (fun i => (hencodedWorkParked i).read_ne_start)
      hencodedOutputParked.read_ne_start
  have htailReach' :
      (TM.seqTM (TM.rewindWorkTM tapes.replacement)
        (entryMissCleanupTM tapes.entry)).reachesIn
        (rewindTime + 1 + cleanupTime)
        { state := (TM.seqTM (TM.rewindWorkTM tapes.replacement)
            (entryMissCleanupTM tapes.entry)).qstart
          input := TM.transitionInput encoded.input
          work := fun i => TM.transitionTape (encoded.work i)
          output := TM.transitionTape encoded.output }
        tailFinal := by
    simpa only [hencodedInputTransition, hencodedWorkTransition,
      hencodedOutputTransition] using! htailReach
  have hreach := TM.seqTM_reachesIn_of_reachesIn
    (rewindEntryEncodeTM tapes.encodeTapes)
    (TM.seqTM (TM.rewindWorkTM tapes.replacement)
      (entryMissCleanupTM tapes.entry))
    hencodeReach hencodeHalt htailReach'
  let finalCfg := TM.phase2Wrap (rewindEntryEncodeTM tapes.encodeTapes)
    (TM.seqTM (TM.rewindWorkTM tapes.replacement)
      (entryMissCleanupTM tapes.entry)) tailFinal
  refine ⟨finalCfg, encodeTime + 1 + (rewindTime + 1 + cleanupTime),
    ?_, hreach, ?_, ?_⟩
  · unfold entryReplaceCleanupTime
    change encodeTime + 1 + (rewindTime + 1 + cleanupTime) ≤
      rewindEntryEncodeTime (entry.1, newValue)
          (entryMissHeadBound entry queryBits initialWork tapes.entry.address) 1 +
        1 + (newValue.bits.length + 1 + 2 + 1 +
          entryMissCleanupTime tapes.entry entry queryBits readyWork)
    omega
  · change (entryReplaceCleanupTM tapes).halted finalCfg
    unfold entryReplaceCleanupTM
    exact (TM.phase2Wrap_halted_iff (rewindEntryEncodeTM tapes.encodeTapes)
    (TM.seqTM (TM.rewindWorkTM tapes.replacement)
      (entryMissCleanupTM tapes.entry)) tailFinal).mpr htailHalt
  · have hreadyGlobal :
        EntryScanReady tapes.entry rest queryBits initialWork cleaned.work := by
      refine ⟨hready.source, hready.address, hready.addressStart,
        hready.value, hready.valueStart, hready.addressCounter,
        hready.addressWidth, hready.valueCounter, hready.valueWidth,
        hready.query, hready.queryStart, hready.result, hready.resultStart,
        hready.parked, ?_⟩
      intro i hsource haddress hvalue haddressCounter haddressWidth
        hvalueCounter hvalueWidth hquery hresult
      have hbase : readyWork i = matchedWork i := by
        simp [readyWork, entryReplaceReadyWork, haddress]
      exact (hready.frame i hsource haddress hvalue haddressCounter
        haddressWidth hvalueCounter hvalueWidth hquery hresult).trans
        (hbase.trans (hmatch.frame i hsource haddress hvalue haddressCounter
          haddressWidth hvalueCounter hvalueWidth hquery hresult))
    refine ⟨?_, hreadyGlobal, ?_, ?_⟩
    · change cleaned.input = inp₀
      exact hcleanedInput.trans (hrewoundInput.trans hencodedInput)
    · have hreplacementReady : readyWork tapes.replacement =
          matchedWork tapes.replacement := by
        have hne : tapes.replacement ≠ tapes.entry.address :=
          tapes.replacement_ne 1
        change (if tapes.replacement = tapes.entry.address then
            { head := entry.1.bits.length + 1,
              cells := (matchedWork tapes.replacement).cells }
          else matchedWork tapes.replacement) = matchedWork tapes.replacement
        rw [ite_eq_right hne]
      exact (hready.frame tapes.replacement
        (tapes.replacement_ne 0) (tapes.replacement_ne 1)
        (tapes.replacement_ne 2) (tapes.replacement_ne 3)
        (tapes.replacement_ne 4) (tapes.replacement_ne 5)
        (tapes.replacement_ne 6) (tapes.replacement_ne 7)
        (tapes.replacement_ne 8)).trans hreplacementReady
    · change cleaned.output.HasBinaryPrefix
        (emitted ++ Entry.encode (entry.1, newValue))
      rw [hcleanedOutput, hrewoundOutput]
      exact hencodedOutput

end Machine

end RegisterStore

end RAM

end Complexity
