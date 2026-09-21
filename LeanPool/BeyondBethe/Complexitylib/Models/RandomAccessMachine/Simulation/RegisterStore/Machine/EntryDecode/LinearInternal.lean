/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryDecode.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordDecode

/-!
# Linear RAM sparse-entry decoder -- proof internals

The address and value words are decoded by the linear unary-marker decoder.
The established counter tapes become markers, while the width tapes remain
framed for compatibility with the existing sparse-store work-tape layout.
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

theorem entryDecodeLinearTM_reachesIn_frame_internal {n : ℕ}
    (tapes : EntryDecodeTapes n) (entry : Entry) (rest : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ tapes.source).HasBinarySuffix (Entry.encode entry ++ rest))
    (haddress : (work₀ tapes.address).HasBinaryPrefix [])
    (hvalue : (work₀ tapes.value).HasBinaryPrefix [])
    (haddressStart : (work₀ tapes.address).cells 0 = Γ.start)
    (hvalueStart : (work₀ tapes.value).cells 0 = Γ.start)
    (haddressMarker : (work₀ tapes.addressCounter).HasBinaryPrefix [])
    (haddressMarkerStart : (work₀ tapes.addressCounter).cells 0 = Γ.start)
    (hvalueMarker : (work₀ tapes.valueCounter).HasBinaryPrefix [])
    (hvalueMarkerStart : (work₀ tapes.valueCounter).cells 0 = Γ.start)
    (hinput : inp₀.read ≠ Γ.start)
    (hreads : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (entryDecodeLinearTM tapes).reachesIn
        (entryDecodeLinearTime entry.1 entry.2)
        { state := (entryDecodeLinearTM tapes).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (entryDecodeLinearTM tapes).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work tapes.source).HasBinarySuffix rest ∧
      (c'.work tapes.address).HasBinaryPrefix entry.1.bits ∧
      (c'.work tapes.address).cells 0 = Γ.start ∧
      (c'.work tapes.value).HasBinaryPrefix entry.2.bits ∧
      (c'.work tapes.value).cells 0 = Γ.start ∧
      (c'.work tapes.addressCounter).HasBinaryPrefix
        (List.replicate (bitlen entry.1) true) ∧
      (c'.work tapes.valueCounter).HasBinaryPrefix
        (List.replicate (bitlen entry.2) true) ∧
      (∀ i, i ≠ tapes.source → i ≠ tapes.address → i ≠ tapes.value →
        i ≠ tapes.addressCounter → i ≠ tapes.valueCounter →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  let addressTM := wordDecodeLinearTM tapes.source tapes.address
    tapes.addressCounter
  let valueTM := wordDecodeLinearTM tapes.source tapes.value
    tapes.valueCounter
  have hsourceAddress : (work₀ tapes.source).HasBinarySuffix
      (WordCode.encode entry.1 ++ (WordCode.encode entry.2 ++ rest)) := by
    simpa [Entry.encode, List.append_assoc] using hsource
  obtain ⟨addressDone, haddressReach, haddressHalt, haddressInput,
      haddressSource, haddressTarget, haddressMarkerFinal, haddressFrame,
      haddressOutput⟩ :=
    wordDecodeLinearTM_reachesIn_frame_encode tapes.source tapes.address
      tapes.addressCounter tapes.addressLinearDistinct entry.1
      (WordCode.encode entry.2 ++ rest) inp₀ work₀ out₀ hsourceAddress
      haddress haddressMarker haddressMarkerStart hinput hreads houtput
  have haddressStartFinal :
      (addressDone.work tapes.address).cells 0 = Γ.start :=
    TM.work_cells_zero_eq_start_of_reachesIn tapes.address haddressReach
      haddressStart
  have haddressReads : ∀ i, (addressDone.work i).read ≠ Γ.start := by
    intro i
    by_cases his : i = tapes.source
    · subst i
      exact haddressSource.read_ne_start
    · by_cases hia : i = tapes.address
      · subst i
        rw [haddressTarget.read_blank]
        decide
      · by_cases him : i = tapes.addressCounter
        · subst i
          rw [haddressMarkerFinal.read_blank]
          decide
        · rw [haddressFrame i his hia him]
          exact hreads i
  have hvalueInitial :
      (addressDone.work tapes.value).HasBinaryPrefix [] := by
    rw [haddressFrame tapes.value (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.ne (by decide))]
    exact hvalue
  have hvalueStartInitial :
      (addressDone.work tapes.value).cells 0 = Γ.start := by
    rw [haddressFrame tapes.value (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.ne (by decide))]
    exact hvalueStart
  have hvalueMarkerInitial :
      (addressDone.work tapes.valueCounter).HasBinaryPrefix [] := by
    rw [haddressFrame tapes.valueCounter (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.ne (by decide))]
    exact hvalueMarker
  have hvalueMarkerStartInitial :
      (addressDone.work tapes.valueCounter).cells 0 = Γ.start := by
    rw [haddressFrame tapes.valueCounter (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.ne (by decide))]
    exact hvalueMarkerStart
  obtain ⟨valueDone, hvalueReach, hvalueHalt, hvalueInput, hvalueSource,
      hvalueTarget, hvalueMarkerFinal, hvalueFrame, hvalueOutput⟩ :=
    wordDecodeLinearTM_reachesIn_frame_encode tapes.source tapes.value
      tapes.valueCounter tapes.valueLinearDistinct entry.2 rest
      addressDone.input addressDone.work addressDone.output haddressSource
      hvalueInitial hvalueMarkerInitial hvalueMarkerStartInitial
      (by rw [haddressInput]; exact hinput) haddressReads
      (by rw [haddressOutput]; exact houtput)
  have hvalueStartFinal :
      (valueDone.work tapes.value).cells 0 = Γ.start :=
    TM.work_cells_zero_eq_start_of_reachesIn tapes.value hvalueReach
      hvalueStartInitial
  have htransitionInput : TM.transitionInput addressDone.input =
      addressDone.input :=
    TM.transitionInput_eq_self (by rw [haddressInput]; exact hinput)
  have htransitionWork :
      (fun i => TM.transitionTape (addressDone.work i)) = addressDone.work := by
    funext i
    exact TM.transitionTape_eq_self (haddressReads i)
  have htransitionOutput : TM.transitionTape addressDone.output =
      addressDone.output :=
    TM.transitionTape_eq_self (by rw [haddressOutput]; exact houtput)
  have hvalueReach' : valueTM.reachesIn
      (wordDecodeLinearTime (bitlen entry.2))
      { state := valueTM.qstart
        input := TM.transitionInput addressDone.input
        work := fun i => TM.transitionTape (addressDone.work i)
        output := TM.transitionTape addressDone.output } valueDone := by
    rw [htransitionInput, htransitionWork, htransitionOutput]
    simpa [valueTM] using hvalueReach
  have hfullReach := TM.seqTM_reachesIn_of_reachesIn addressTM valueTM
    (by simpa [addressTM] using haddressReach) haddressHalt hvalueReach'
  let finalCfg := TM.phase2Wrap addressTM valueTM valueDone
  refine ⟨finalCfg, ?_, ?_, hvalueInput.trans haddressInput, hvalueSource,
    ?_, ?_, hvalueTarget, hvalueStartFinal, ?_, hvalueMarkerFinal, ?_,
    hvalueOutput.trans haddressOutput⟩
  · simpa [entryDecodeLinearTM, entryDecodeLinearTime, addressTM, valueTM,
      finalCfg] using hfullReach
  · exact (TM.phase2Wrap_halted_iff addressTM valueTM valueDone).2 hvalueHalt
  · change (valueDone.work tapes.address).HasBinaryPrefix entry.1.bits
    rw [hvalueFrame tapes.address (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.ne (by decide))]
    exact haddressTarget
  · change (valueDone.work tapes.address).cells 0 = Γ.start
    rw [hvalueFrame tapes.address (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.ne (by decide))]
    exact haddressStartFinal
  · change (valueDone.work tapes.addressCounter).HasBinaryPrefix
      (List.replicate (bitlen entry.1) true)
    rw [hvalueFrame tapes.addressCounter (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.ne (by decide))]
    exact haddressMarkerFinal
  · intro i his hia hiv hiac hivc
    change valueDone.work i = work₀ i
    rw [hvalueFrame i his hiv hivc, haddressFrame i his hia hiac]

end Machine

end RegisterStore

end RAM

end Complexity
