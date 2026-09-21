/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryAppend.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryEncode
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

/-!
# Sparse-entry final append — proof internals
-/


public section

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

theorem entryAppendRestoreTM_hoareTime_frame_internal
    (tapes : EntryReplaceTapes n) (address newValue : ℕ)
    (emitted : List Bool) (initialWork readyWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hready : EntryScanReady tapes.entry [] address.bits initialWork readyWork)
    (hreplacement : (readyWork tapes.replacement).HasBinaryNat newValue)
    (hinput : TM.Parked inp₀) (houtput : out₀.HasBinaryPrefix emitted) :
    (entryAppendRestoreTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = readyWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = readyWork ∧
        out.HasBinaryPrefix
          (emitted ++ Entry.encode (address, newValue)))
      (entryAppendRestoreTime address newValue) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  have hqueryHead : 1 ≤ (readyWork tapes.entry.query).head ∧
      (readyWork tapes.entry.query).head ≤ 1 := by
    rw [hready.query.1]
    exact ⟨le_rfl, le_rfl⟩
  have hreplacementHead : 1 ≤ (readyWork tapes.replacement).head ∧
      (readyWork tapes.replacement).head ≤ 1 := by
    rw [hreplacement.2.1]
    exact ⟨le_rfl, le_rfl⟩
  have hencode := rewindEntryEncodeTM_hoareTime_frame
    tapes.appendEncodeTapes (address, newValue) 1 1 emitted
    inp₀ readyWork out₀ hready.query.2 hready.queryStart hqueryHead
    hreplacement.2.hasBinaryContent hreplacement.1 hreplacementHead
    hinput (fun i _ _ => hready.parked i) houtput
  obtain ⟨encoded, encodeTime, hencodeTime, hencodeReach, hencodeHalt,
      hencodedInput, hquerySuffix, hqueryCells, hqueryEncodedHead,
      hreplacementSuffix, hreplacementCells, hreplacementEncodedHead,
      hencodedFrame, hencodedOutput⟩ :=
    hencode inp₀ readyWork out₀ ⟨rfl, rfl, rfl⟩
  have hqueryCells' : (encoded.work tapes.entry.query).cells =
      (readyWork tapes.entry.query).cells := by
    simpa using hqueryCells
  have hqueryEncodedHead' : (encoded.work tapes.entry.query).head =
      address.bits.length + 1 := by
    simpa using hqueryEncodedHead
  have hreplacementCells' : (encoded.work tapes.replacement).cells =
      (readyWork tapes.replacement).cells := by
    simpa using hreplacementCells
  have hreplacementEncodedHead' :
      (encoded.work tapes.replacement).head = newValue.bits.length + 1 := by
    simpa using hreplacementEncodedHead
  have hencodedInputParked : TM.Parked encoded.input := by
    rw [hencodedInput]
    exact hinput
  have hencodedOutputParked : TM.Parked encoded.output :=
    parked_of_binaryPrefix hencodedOutput
  have hencodedWorkParked : ∀ i, TM.Parked (encoded.work i) := by
    intro i
    by_cases hiq : i = tapes.entry.query
    · subst i
      exact parked_of_binarySuffix (by simpa using hquerySuffix)
    · by_cases hir : i = tapes.replacement
      · subst i
        exact parked_of_binarySuffix (by simpa using hreplacementSuffix)
      · rw [hencodedFrame i hiq hir]
        exact hready.parked i
  have hqueryContent :
      (encoded.work tapes.entry.query).HasBinaryContent address.bits := by
    simpa only [Tape.HasBinaryContent, hqueryCells'] using hready.query.2
  have hqueryStart :
      (encoded.work tapes.entry.query).cells 0 = Γ.start := by
    rw [hqueryCells']
    exact hready.queryStart
  have hqueryRewind := TM.rewindBinaryWorkTM_hoareTime_frame
    tapes.entry.query address.bits (address.bits.length + 1)
    encoded.input encoded.work encoded.output hqueryContent hqueryStart
    ⟨by rw [hqueryEncodedHead']; omega, by rw [hqueryEncodedHead']⟩
    hencodedInputParked (fun i _ => hencodedWorkParked i)
    hencodedOutputParked
  obtain ⟨queryRewound, queryTime, hqueryTime, hqueryReach, hqueryHalt,
      hqueryInput, hqueryRestoredCanonical, hqueryFrame,
      hqueryOutput⟩ :=
    hqueryRewind encoded.input encoded.work encoded.output ⟨rfl, rfl, rfl⟩
  have hqueryCanonical : readyWork tapes.entry.query =
      (Tape.init (address.bits.map Γ.ofBool)).move Dir3.right :=
    Tape.eq_init_move_right_of_hasBinaryString hready.query hready.queryStart
  have hqueryRestored : queryRewound.work tapes.entry.query =
      readyWork tapes.entry.query :=
    hqueryRestoredCanonical.trans hqueryCanonical.symm
  have hreplacementContent :
      (queryRewound.work tapes.replacement).HasBinaryContent newValue.bits := by
    rw [hqueryFrame tapes.replacement
      (tapes.replacement_ne 7)]
    simpa only [Tape.HasBinaryContent, hreplacementCells'] using
      hreplacement.2.hasBinaryContent
  have hreplacementStart :
      (queryRewound.work tapes.replacement).cells 0 = Γ.start := by
    rw [hqueryFrame tapes.replacement
      (tapes.replacement_ne 7), hreplacementCells']
    exact hreplacement.1
  have hreplacementHead' :
      (queryRewound.work tapes.replacement).head =
        newValue.bits.length + 1 := by
    rw [hqueryFrame tapes.replacement
      (tapes.replacement_ne 7)]
    exact hreplacementEncodedHead'
  have hqueryInputParked : TM.Parked queryRewound.input := by
    rw [hqueryInput]
    exact hencodedInputParked
  have hqueryOutputParked : TM.Parked queryRewound.output := by
    rw [hqueryOutput]
    exact hencodedOutputParked
  have hqueryWorkParked : ∀ i, TM.Parked (queryRewound.work i) := by
    intro i
    by_cases hiq : i = tapes.entry.query
    · subst i
      rw [hqueryRestored]
      exact hready.parked tapes.entry.query
    · rw [hqueryFrame i hiq]
      exact hencodedWorkParked i
  have hreplacementRewind := TM.rewindBinaryWorkTM_hoareTime_frame
    tapes.replacement newValue.bits (newValue.bits.length + 1)
    queryRewound.input queryRewound.work queryRewound.output
    hreplacementContent hreplacementStart
    ⟨by rw [hreplacementHead']; omega, by rw [hreplacementHead']⟩
    hqueryInputParked (fun i _ => hqueryWorkParked i) hqueryOutputParked
  obtain ⟨restored, replacementTime, hreplacementTime,
      hreplacementReach, hreplacementHalt, hreplacementInput,
      hreplacementRestoredCanonical, hreplacementFrame,
      hreplacementOutput⟩ :=
    hreplacementRewind queryRewound.input queryRewound.work
      queryRewound.output ⟨rfl, rfl, rfl⟩
  have hreplacementCanonical : readyWork tapes.replacement =
      (Tape.init (newValue.bits.map Γ.ofBool)).move Dir3.right :=
    Tape.eq_init_move_right_of_hasBinaryString hreplacement.2 hreplacement.1
  have hreplacementRestored : restored.work tapes.replacement =
      readyWork tapes.replacement :=
    hreplacementRestoredCanonical.trans hreplacementCanonical.symm
  have hrestoredWork : restored.work = readyWork := by
    funext i
    by_cases hir : i = tapes.replacement
    · subst i
      exact hreplacementRestored
    · rw [hreplacementFrame i hir]
      by_cases hiq : i = tapes.entry.query
      · subst i
        exact hqueryRestored
      · exact (hqueryFrame i hiq).trans (hencodedFrame i hiq hir)
  obtain ⟨hqueryInputTransition, hqueryWorkTransition,
      hqueryOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hqueryInputParked.read_ne_start
      (fun i => (hqueryWorkParked i).read_ne_start)
      hqueryOutputParked.read_ne_start
  have hreplacementReach' :
      (TM.rewindWorkTM tapes.replacement).reachesIn replacementTime
        { state := (TM.rewindWorkTM tapes.replacement).qstart
          input := TM.transitionInput queryRewound.input
          work := fun i => TM.transitionTape (queryRewound.work i)
          output := TM.transitionTape queryRewound.output }
        restored := by
    simpa only [hqueryInputTransition, hqueryWorkTransition,
      hqueryOutputTransition] using hreplacementReach
  have htailReach := TM.seqTM_reachesIn_of_reachesIn
    (TM.rewindWorkTM tapes.entry.query) (TM.rewindWorkTM tapes.replacement)
    hqueryReach hqueryHalt hreplacementReach'
  let tailFinal := TM.phase2Wrap (TM.rewindWorkTM tapes.entry.query)
    (TM.rewindWorkTM tapes.replacement) restored
  have htailHalt :
      (TM.seqTM (TM.rewindWorkTM tapes.entry.query)
        (TM.rewindWorkTM tapes.replacement)).halted tailFinal := by
    rw [TM.phase2Wrap_halted_iff]
    exact hreplacementHalt
  obtain ⟨hencodedInputTransition, hencodedWorkTransition,
      hencodedOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hencodedInputParked.read_ne_start
      (fun i => (hencodedWorkParked i).read_ne_start)
      hencodedOutputParked.read_ne_start
  have htailReach' :
      (TM.seqTM (TM.rewindWorkTM tapes.entry.query)
        (TM.rewindWorkTM tapes.replacement)).reachesIn
        (queryTime + 1 + replacementTime)
        { state := (TM.seqTM (TM.rewindWorkTM tapes.entry.query)
            (TM.rewindWorkTM tapes.replacement)).qstart
          input := TM.transitionInput encoded.input
          work := fun i => TM.transitionTape (encoded.work i)
          output := TM.transitionTape encoded.output }
        tailFinal := by
    simpa only [hencodedInputTransition, hencodedWorkTransition,
      hencodedOutputTransition] using htailReach
  have hreach := TM.seqTM_reachesIn_of_reachesIn
    (rewindEntryEncodeTM tapes.appendEncodeTapes)
    (TM.seqTM (TM.rewindWorkTM tapes.entry.query)
      (TM.rewindWorkTM tapes.replacement))
    hencodeReach hencodeHalt htailReach'
  let finalCfg := TM.phase2Wrap
    (rewindEntryEncodeTM tapes.appendEncodeTapes)
    (TM.seqTM (TM.rewindWorkTM tapes.entry.query)
      (TM.rewindWorkTM tapes.replacement)) tailFinal
  refine ⟨finalCfg, encodeTime + 1 + (queryTime + 1 + replacementTime),
    ?_, hreach, ?_, ?_⟩
  · unfold entryAppendRestoreTime
    omega
  · change (entryAppendRestoreTM tapes).halted finalCfg
    unfold entryAppendRestoreTM
    rw [TM.phase2Wrap_halted_iff]
    exact htailHalt
  · refine ⟨?_, ?_, ?_⟩
    · change restored.input = inp₀
      exact hreplacementInput.trans (hqueryInput.trans hencodedInput)
    · change restored.work = readyWork
      exact hrestoredWork
    · change restored.output.HasBinaryPrefix
        (emitted ++ Entry.encode (address, newValue))
      rw [hreplacementOutput, hqueryOutput]
      exact hencodedOutput

end Machine

end RegisterStore

end RAM

end Complexity
