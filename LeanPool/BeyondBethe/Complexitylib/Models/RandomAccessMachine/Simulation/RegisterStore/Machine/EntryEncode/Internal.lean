/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryEncode.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordEncode

/-!
# Sparse entry emission — proof internals
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem parked_of_binaryNat {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t :=
  ⟨by rw [h.2.1], h.2.hasBinaryContent.cells_ne_start⟩

private theorem parked_of_binarySuffix {t : Tape} {bits : List Bool}
    (h : t.HasBinarySuffix bits) : TM.Parked t :=
  ⟨h.1, h.2.2.2⟩

private theorem parked_of_binaryPrefix {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : TM.Parked t :=
  ⟨by rw [h.1]; omega,
    (show t.HasBinaryContent bits from h.2).cells_ne_start⟩

theorem entryEncodeTM_hoareTime_frame_internal
    (tapes : EntryEncodeTapes n) (entry : Entry) (emitted : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (haddress : (work₀ tapes.address).HasBinaryNat entry.1)
    (hvalue : (work₀ tapes.value).HasBinaryNat entry.2)
    (hinput : TM.Parked inp₀)
    (hother : ∀ i, i ≠ tapes.address → i ≠ tapes.value →
      TM.Parked (work₀ i))
    (houtput : out₀.HasBinaryPrefix emitted) :
    (entryEncodeTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work tapes.address).HasBinarySuffix [] ∧
        (work tapes.address).cells = (work₀ tapes.address).cells ∧
        (work tapes.address).head = entry.1.bits.length + 1 ∧
        (work tapes.value).HasBinarySuffix [] ∧
        (work tapes.value).cells = (work₀ tapes.value).cells ∧
        (work tapes.value).head = entry.2.bits.length + 1 ∧
        (∀ i, i ≠ tapes.address → i ≠ tapes.value → work i = work₀ i) ∧
        out.HasBinaryPrefix (emitted ++ Entry.encode entry))
      (entryEncodeTime entry) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  have hinitialParked : ∀ i, TM.Parked (work₀ i) := by
    intro i
    by_cases hia : i = tapes.address
    · subst i
      exact parked_of_binaryNat haddress
    · by_cases hiv : i = tapes.value
      · subst i
        exact parked_of_binaryNat hvalue
      · exact hother i hia hiv
  have haddressContract := wordEncodeTM_hoareTime_frame tapes.address
    entry.1 emitted inp₀ work₀ out₀ haddress hinput
    (fun i _ => hinitialParked i) houtput
  obtain ⟨addressDone, addressTime, haddressTime, haddressReach,
      haddressHalt, haddressInput, haddressSuffix, haddressCells,
      haddressHeadDone, haddressFrame, haddressOutput⟩ :=
    haddressContract inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩
  have haddressParked : TM.Parked (addressDone.work tapes.address) :=
    parked_of_binarySuffix haddressSuffix
  have haddressWorkParked : ∀ i, TM.Parked (addressDone.work i) := by
    intro i
    by_cases hi : i = tapes.address
    · subst i
      exact haddressParked
    · rw [haddressFrame i hi]
      exact hinitialParked i
  have haddressOutputParked : TM.Parked addressDone.output :=
    parked_of_binaryPrefix haddressOutput
  obtain ⟨hinputTransition, hworkTransition, houtputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      (haddressInput ▸ hinput.read_ne_start)
      (fun i => (haddressWorkParked i).read_ne_start)
      haddressOutputParked.read_ne_start
  have hvalueDone : (addressDone.work tapes.value).HasBinaryNat entry.2 := by
    rw [haddressFrame tapes.value (Ne.symm tapes.ne)]
    exact hvalue
  have hvalueContract := wordEncodeTM_hoareTime_frame tapes.value entry.2
    (emitted ++ WordCode.encode entry.1) addressDone.input addressDone.work
    addressDone.output hvalueDone (haddressInput ▸ hinput)
    (fun i _ => haddressWorkParked i) haddressOutput
  obtain ⟨valueDone, valueTime, hvalueTime, hvalueReach, hvalueHalt,
      hvalueInput, hvalueSuffix, hvalueCells, hvalueHeadFinal,
      hvalueFrame, hvalueOutput⟩ :=
    hvalueContract addressDone.input addressDone.work addressDone.output
      ⟨rfl, rfl, rfl⟩
  have hvalueReach' : (wordEncodeTM tapes.value).reachesIn valueTime
      { state := (wordEncodeTM tapes.value).qstart
        input := TM.transitionInput addressDone.input
        work := fun i => TM.transitionTape (addressDone.work i)
        output := TM.transitionTape addressDone.output }
      valueDone := by
    simpa [hinputTransition, hworkTransition, houtputTransition] using
      hvalueReach
  have hreach := TM.seqTM_reachesIn_of_reachesIn
    (wordEncodeTM tapes.address) (wordEncodeTM tapes.value)
    haddressReach haddressHalt hvalueReach'
  let finalCfg := TM.phase2Wrap (wordEncodeTM tapes.address)
    (wordEncodeTM tapes.value) valueDone
  refine ⟨finalCfg, addressTime + 1 + valueTime, ?_, hreach, ?_, ?_⟩
  · unfold entryEncodeTime
    omega
  · change (entryEncodeTM tapes).halted finalCfg
    unfold entryEncodeTM
    rw [TM.phase2Wrap_halted_iff]
    exact hvalueHalt
  · refine ⟨?_, ?_, ?_, ?_, hvalueSuffix, ?_, hvalueHeadFinal, ?_, ?_⟩
    · simpa [finalCfg] using hvalueInput.trans haddressInput
    · change (valueDone.work tapes.address).HasBinarySuffix []
      rw [hvalueFrame tapes.address tapes.ne]
      exact haddressSuffix
    · change (valueDone.work tapes.address).cells =
        (work₀ tapes.address).cells
      rw [hvalueFrame tapes.address tapes.ne]
      exact haddressCells
    · change (valueDone.work tapes.address).head = entry.1.bits.length + 1
      rw [hvalueFrame tapes.address tapes.ne]
      exact haddressHeadDone
    · change (valueDone.work tapes.value).cells = (work₀ tapes.value).cells
      rw [hvalueCells, haddressFrame tapes.value (Ne.symm tapes.ne)]
    · intro i hia hiv
      change valueDone.work i = work₀ i
      exact (hvalueFrame i hiv).trans (haddressFrame i hia)
    · simpa [finalCfg, Entry.encode, List.append_assoc] using hvalueOutput

theorem rewindEntryEncodeTM_hoareTime_frame_internal
    (tapes : EntryEncodeTapes n) (entry : Entry)
    (addressHeadBound valueHeadBound : ℕ) (emitted : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (haddress : (work₀ tapes.address).HasBinaryContent entry.1.bits)
    (haddressStart : (work₀ tapes.address).cells 0 = Γ.start)
    (haddressHead : 1 ≤ (work₀ tapes.address).head ∧
      (work₀ tapes.address).head ≤ addressHeadBound)
    (hvalue : (work₀ tapes.value).HasBinaryContent entry.2.bits)
    (hvalueStart : (work₀ tapes.value).cells 0 = Γ.start)
    (hvalueHead : 1 ≤ (work₀ tapes.value).head ∧
      (work₀ tapes.value).head ≤ valueHeadBound)
    (hinput : TM.Parked inp₀)
    (hother : ∀ i, i ≠ tapes.address → i ≠ tapes.value →
      TM.Parked (work₀ i))
    (houtput : out₀.HasBinaryPrefix emitted) :
    (rewindEntryEncodeTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work tapes.address).HasBinarySuffix [] ∧
        (work tapes.address).cells = (work₀ tapes.address).cells ∧
        (work tapes.address).head = entry.1.bits.length + 1 ∧
        (work tapes.value).HasBinarySuffix [] ∧
        (work tapes.value).cells = (work₀ tapes.value).cells ∧
        (work tapes.value).head = entry.2.bits.length + 1 ∧
        (∀ i, i ≠ tapes.address → i ≠ tapes.value → work i = work₀ i) ∧
        out.HasBinaryPrefix (emitted ++ Entry.encode entry))
      (rewindEntryEncodeTime entry addressHeadBound valueHeadBound) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  have hinitialParked : ∀ i, TM.Parked (work₀ i) := by
    intro i
    by_cases hia : i = tapes.address
    · subst i
      exact ⟨haddressHead.1, haddress.cells_ne_start⟩
    · by_cases hiv : i = tapes.value
      · subst i
        exact ⟨hvalueHead.1, hvalue.cells_ne_start⟩
      · exact hother i hia hiv
  have haddressContract := rewindWordEncodeTM_hoareTime_frame tapes.address
    entry.1 addressHeadBound emitted inp₀ work₀ out₀ haddress haddressStart
    haddressHead hinput (fun i _ => hinitialParked i) houtput
  obtain ⟨addressDone, addressTime, haddressTime, haddressReach,
      haddressHalt, haddressInput, haddressSuffix, haddressCells,
      haddressHeadDone, haddressFrame, haddressOutput⟩ :=
    haddressContract inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩
  have haddressWorkParked : ∀ i, TM.Parked (addressDone.work i) := by
    intro i
    by_cases hi : i = tapes.address
    · subst i
      exact parked_of_binarySuffix haddressSuffix
    · rw [haddressFrame i hi]
      exact hinitialParked i
  have haddressOutputParked : TM.Parked addressDone.output :=
    parked_of_binaryPrefix haddressOutput
  obtain ⟨hinputTransition, hworkTransition, houtputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      (haddressInput ▸ hinput.read_ne_start)
      (fun i => (haddressWorkParked i).read_ne_start)
      haddressOutputParked.read_ne_start
  have hvalueDone :
      (addressDone.work tapes.value).HasBinaryContent entry.2.bits := by
    rw [haddressFrame tapes.value (Ne.symm tapes.ne)]
    exact hvalue
  have hvalueStartDone :
      (addressDone.work tapes.value).cells 0 = Γ.start := by
    rw [haddressFrame tapes.value (Ne.symm tapes.ne)]
    exact hvalueStart
  have hvalueHeadDone :
      1 ≤ (addressDone.work tapes.value).head ∧
        (addressDone.work tapes.value).head ≤ valueHeadBound := by
    rw [haddressFrame tapes.value (Ne.symm tapes.ne)]
    exact hvalueHead
  have hvalueContract := rewindWordEncodeTM_hoareTime_frame tapes.value
    entry.2 valueHeadBound (emitted ++ WordCode.encode entry.1)
    addressDone.input addressDone.work addressDone.output hvalueDone
    hvalueStartDone hvalueHeadDone (haddressInput ▸ hinput)
    (fun i _ => haddressWorkParked i) haddressOutput
  obtain ⟨valueDone, valueTime, hvalueTime, hvalueReach, hvalueHalt,
      hvalueInput, hvalueSuffix, hvalueCells, hvalueHeadFinal,
      hvalueFrame, hvalueOutput⟩ :=
    hvalueContract addressDone.input addressDone.work addressDone.output
      ⟨rfl, rfl, rfl⟩
  have hvalueReach' : (rewindWordEncodeTM tapes.value).reachesIn valueTime
      { state := (rewindWordEncodeTM tapes.value).qstart
        input := TM.transitionInput addressDone.input
        work := fun i => TM.transitionTape (addressDone.work i)
        output := TM.transitionTape addressDone.output }
      valueDone := by
    simpa [hinputTransition, hworkTransition, houtputTransition] using
      hvalueReach
  have hreach := TM.seqTM_reachesIn_of_reachesIn
    (rewindWordEncodeTM tapes.address) (rewindWordEncodeTM tapes.value)
    haddressReach haddressHalt hvalueReach'
  let finalCfg := TM.phase2Wrap (rewindWordEncodeTM tapes.address)
    (rewindWordEncodeTM tapes.value) valueDone
  refine ⟨finalCfg, addressTime + 1 + valueTime, ?_, hreach, ?_, ?_⟩
  · unfold rewindEntryEncodeTime
    omega
  · change (rewindEntryEncodeTM tapes).halted finalCfg
    unfold rewindEntryEncodeTM
    rw [TM.phase2Wrap_halted_iff]
    exact hvalueHalt
  · refine ⟨?_, ?_, ?_, ?_, hvalueSuffix, ?_, hvalueHeadFinal, ?_, ?_⟩
    · simpa [finalCfg] using hvalueInput.trans haddressInput
    · change (valueDone.work tapes.address).HasBinarySuffix []
      rw [hvalueFrame tapes.address tapes.ne]
      exact haddressSuffix
    · change (valueDone.work tapes.address).cells =
        (work₀ tapes.address).cells
      rw [hvalueFrame tapes.address tapes.ne]
      exact haddressCells
    · change (valueDone.work tapes.address).head = entry.1.bits.length + 1
      rw [hvalueFrame tapes.address tapes.ne]
      exact haddressHeadDone
    · change (valueDone.work tapes.value).cells = (work₀ tapes.value).cells
      rw [hvalueCells, haddressFrame tapes.value (Ne.symm tapes.ne)]
    · intro i hia hiv
      change valueDone.work i = work₀ i
      exact (hvalueFrame i hiv).trans (haddressFrame i hia)
    · simpa [finalCfg, Entry.encode, List.append_assoc] using hvalueOutput

theorem rewindEntryEncodeRestoreTM_hoareTime_frame_internal
    (tapes : EntryEncodeTapes n) (entry : Entry) (emitted : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (haddress : (work₀ tapes.address).HasBinaryNat entry.1)
    (hvalue : (work₀ tapes.value).HasBinaryNat entry.2)
    (hinput : TM.Parked inp₀)
    (hother : ∀ i, i ≠ tapes.address → i ≠ tapes.value →
      TM.Parked (work₀ i))
    (houtput : out₀.HasBinaryPrefix emitted) :
    (rewindEntryEncodeRestoreTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧
        out.HasBinaryPrefix (emitted ++ Entry.encode entry))
      (rewindEntryEncodeRestoreTime entry) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  have haddressHead : 1 ≤ (work₀ tapes.address).head ∧
      (work₀ tapes.address).head ≤ 1 := by
    rw [haddress.2.1]
    exact ⟨le_rfl, le_rfl⟩
  have hvalueHead : 1 ≤ (work₀ tapes.value).head ∧
      (work₀ tapes.value).head ≤ 1 := by
    rw [hvalue.2.1]
    exact ⟨le_rfl, le_rfl⟩
  have hencode := rewindEntryEncodeTM_hoareTime_frame_internal tapes entry
    1 1 emitted inp₀ work₀ out₀ haddress.2.hasBinaryContent haddress.1
    haddressHead hvalue.2.hasBinaryContent hvalue.1 hvalueHead hinput
    hother houtput
  obtain ⟨encoded, encodeTime, hencodeTime, hencodeReach, hencodeHalt,
      hencodedInput, haddressSuffix, haddressCells, haddressEncodedHead,
      hvalueSuffix, hvalueCells, hvalueEncodedHead, hencodedFrame,
      hencodedOutput⟩ := hencode inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩
  have haddressCells' : (encoded.work tapes.address).cells =
      (work₀ tapes.address).cells := by
    simpa using haddressCells
  have haddressEncodedHead' : (encoded.work tapes.address).head =
      entry.1.bits.length + 1 := by
    simpa using haddressEncodedHead
  have hvalueCells' : (encoded.work tapes.value).cells =
      (work₀ tapes.value).cells := by
    simpa using hvalueCells
  have hvalueEncodedHead' : (encoded.work tapes.value).head =
      entry.2.bits.length + 1 := by
    simpa using hvalueEncodedHead
  have hencodedInputParked : TM.Parked encoded.input := by
    rw [hencodedInput]
    exact hinput
  have hencodedOutputParked : TM.Parked encoded.output :=
    parked_of_binaryPrefix hencodedOutput
  have hencodedWorkParked : ∀ i, TM.Parked (encoded.work i) := by
    intro i
    by_cases hia : i = tapes.address
    · subst i
      exact parked_of_binarySuffix haddressSuffix
    · by_cases hiv : i = tapes.value
      · subst i
        exact parked_of_binarySuffix hvalueSuffix
      · rw [hencodedFrame i hia hiv]
        exact hother i hia hiv
  have haddressContent :
      (encoded.work tapes.address).HasBinaryContent entry.1.bits := by
    simpa only [Tape.HasBinaryContent, haddressCells'] using
      haddress.2.hasBinaryContent
  have haddressStart :
      (encoded.work tapes.address).cells 0 = Γ.start := by
    rw [haddressCells']
    exact haddress.1
  have haddressRewind := TM.rewindBinaryWorkTM_hoareTime_frame
    tapes.address entry.1.bits (entry.1.bits.length + 1)
    encoded.input encoded.work encoded.output haddressContent haddressStart
    ⟨by rw [haddressEncodedHead']; omega,
      by rw [haddressEncodedHead']⟩
    hencodedInputParked (fun i _ => hencodedWorkParked i)
    hencodedOutputParked
  obtain ⟨addressRewound, addressTime, haddressTime, haddressReach,
      haddressHalt, haddressInput, haddressRestoredCanonical,
      haddressFrame, haddressOutput⟩ :=
    haddressRewind encoded.input encoded.work encoded.output ⟨rfl, rfl, rfl⟩
  have haddressCanonical : work₀ tapes.address =
      (Tape.init (entry.1.bits.map Γ.ofBool)).move Dir3.right :=
    Tape.eq_init_move_right_of_hasBinaryString haddress.2 haddress.1
  have haddressRestored : addressRewound.work tapes.address =
      work₀ tapes.address :=
    haddressRestoredCanonical.trans haddressCanonical.symm
  have hvalueContent :
      (addressRewound.work tapes.value).HasBinaryContent entry.2.bits := by
    rw [haddressFrame tapes.value (Ne.symm tapes.ne)]
    simpa only [Tape.HasBinaryContent, hvalueCells'] using
      hvalue.2.hasBinaryContent
  have hvalueStart :
      (addressRewound.work tapes.value).cells 0 = Γ.start := by
    rw [haddressFrame tapes.value (Ne.symm tapes.ne), hvalueCells']
    exact hvalue.1
  have hvalueHead' : (addressRewound.work tapes.value).head =
      entry.2.bits.length + 1 := by
    rw [haddressFrame tapes.value (Ne.symm tapes.ne)]
    exact hvalueEncodedHead'
  have haddressInputParked : TM.Parked addressRewound.input := by
    rw [haddressInput]
    exact hencodedInputParked
  have haddressOutputParked : TM.Parked addressRewound.output := by
    rw [haddressOutput]
    exact hencodedOutputParked
  have haddressWorkParked : ∀ i, TM.Parked (addressRewound.work i) := by
    intro i
    by_cases hia : i = tapes.address
    · subst i
      rw [haddressRestored]
      exact parked_of_binaryNat haddress
    · rw [haddressFrame i hia]
      exact hencodedWorkParked i
  have hvalueRewind := TM.rewindBinaryWorkTM_hoareTime_frame
    tapes.value entry.2.bits (entry.2.bits.length + 1)
    addressRewound.input addressRewound.work addressRewound.output
    hvalueContent hvalueStart
    ⟨by rw [hvalueHead']; omega, by rw [hvalueHead']⟩
    haddressInputParked (fun i _ => haddressWorkParked i)
    haddressOutputParked
  obtain ⟨restored, valueTime, hvalueTime, hvalueReach, hvalueHalt,
      hvalueInput, hvalueRestoredCanonical, hvalueFrame,
      hvalueOutput⟩ :=
    hvalueRewind addressRewound.input addressRewound.work
      addressRewound.output ⟨rfl, rfl, rfl⟩
  have hvalueCanonical : work₀ tapes.value =
      (Tape.init (entry.2.bits.map Γ.ofBool)).move Dir3.right :=
    Tape.eq_init_move_right_of_hasBinaryString hvalue.2 hvalue.1
  have hvalueRestored : restored.work tapes.value = work₀ tapes.value :=
    hvalueRestoredCanonical.trans hvalueCanonical.symm
  have hrestoredWork : restored.work = work₀ := by
    funext i
    by_cases hiv : i = tapes.value
    · subst i
      exact hvalueRestored
    · rw [hvalueFrame i hiv]
      by_cases hia : i = tapes.address
      · subst i
        exact haddressRestored
      · exact (haddressFrame i hia).trans (hencodedFrame i hia hiv)
  obtain ⟨haddressInputTransition, haddressWorkTransition,
      haddressOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      haddressInputParked.read_ne_start
      (fun i => (haddressWorkParked i).read_ne_start)
      haddressOutputParked.read_ne_start
  have hvalueReach' : (TM.rewindWorkTM tapes.value).reachesIn valueTime
      { state := (TM.rewindWorkTM tapes.value).qstart
        input := TM.transitionInput addressRewound.input
        work := fun i => TM.transitionTape (addressRewound.work i)
        output := TM.transitionTape addressRewound.output }
      restored := by
    simpa only [haddressInputTransition, haddressWorkTransition,
      haddressOutputTransition] using hvalueReach
  have htailReach := TM.seqTM_reachesIn_of_reachesIn
    (TM.rewindWorkTM tapes.address) (TM.rewindWorkTM tapes.value)
    haddressReach haddressHalt hvalueReach'
  let tailFinal := TM.phase2Wrap (TM.rewindWorkTM tapes.address)
    (TM.rewindWorkTM tapes.value) restored
  have htailHalt :
      (TM.seqTM (TM.rewindWorkTM tapes.address)
        (TM.rewindWorkTM tapes.value)).halted tailFinal := by
    rw [TM.phase2Wrap_halted_iff]
    exact hvalueHalt
  obtain ⟨hencodedInputTransition, hencodedWorkTransition,
      hencodedOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hencodedInputParked.read_ne_start
      (fun i => (hencodedWorkParked i).read_ne_start)
      hencodedOutputParked.read_ne_start
  have htailReach' :
      (TM.seqTM (TM.rewindWorkTM tapes.address)
        (TM.rewindWorkTM tapes.value)).reachesIn
        (addressTime + 1 + valueTime)
        { state := (TM.seqTM (TM.rewindWorkTM tapes.address)
            (TM.rewindWorkTM tapes.value)).qstart
          input := TM.transitionInput encoded.input
          work := fun i => TM.transitionTape (encoded.work i)
          output := TM.transitionTape encoded.output }
        tailFinal := by
    simpa only [hencodedInputTransition, hencodedWorkTransition,
      hencodedOutputTransition] using htailReach
  have hreach := TM.seqTM_reachesIn_of_reachesIn
    (rewindEntryEncodeTM tapes)
    (TM.seqTM (TM.rewindWorkTM tapes.address)
      (TM.rewindWorkTM tapes.value))
    hencodeReach hencodeHalt htailReach'
  let finalCfg := TM.phase2Wrap (rewindEntryEncodeTM tapes)
    (TM.seqTM (TM.rewindWorkTM tapes.address)
      (TM.rewindWorkTM tapes.value)) tailFinal
  refine ⟨finalCfg, encodeTime + 1 + (addressTime + 1 + valueTime),
    ?_, hreach, ?_, ?_⟩
  · unfold rewindEntryEncodeRestoreTime
    omega
  · change (rewindEntryEncodeRestoreTM tapes).halted finalCfg
    unfold rewindEntryEncodeRestoreTM
    rw [TM.phase2Wrap_halted_iff]
    exact htailHalt
  · refine ⟨?_, hrestoredWork, ?_⟩
    · change restored.input = inp₀
      exact hvalueInput.trans (haddressInput.trans hencodedInput)
    · change restored.output.HasBinaryPrefix
        (emitted ++ Entry.encode entry)
      rw [hvalueOutput, haddressOutput]
      exact hencodedOutput

end Machine

end RegisterStore

end RAM

end Complexity
