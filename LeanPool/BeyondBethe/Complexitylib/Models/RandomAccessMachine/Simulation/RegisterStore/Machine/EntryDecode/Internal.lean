/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryDecode.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordDecode

/-!
# RAM sparse-entry decoder — proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

theorem entryDecodeTM_reachesIn_frame_internal {n : ℕ}
    (tapes : EntryDecodeTapes n) (entry : Entry) (rest : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ tapes.source).HasBinarySuffix (Entry.encode entry ++ rest))
    (haddress : (work₀ tapes.address).HasBinaryPrefix [])
    (hvalue : (work₀ tapes.value).HasBinaryPrefix [])
    (haddressStart : (work₀ tapes.address).cells 0 = Γ.start)
    (hvalueStart : (work₀ tapes.value).cells 0 = Γ.start)
    (haddressCounter : (work₀ tapes.addressCounter).HasBinaryNat 0)
    (haddressWidth : (work₀ tapes.addressWidth).HasBinaryNat 0)
    (hvalueCounter : (work₀ tapes.valueCounter).HasBinaryNat 0)
    (hvalueWidth : (work₀ tapes.valueWidth).HasBinaryNat 0)
    (hinput : inp₀.read ≠ Γ.start)
    (hreads : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (entryDecodeTM tapes).reachesIn (entryDecodeTime entry.1 entry.2)
        { state := (entryDecodeTM tapes).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (entryDecodeTM tapes).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work tapes.source).HasBinarySuffix rest ∧
      (c'.work tapes.address).HasBinaryPrefix entry.1.bits ∧
      (c'.work tapes.address).cells 0 = Γ.start ∧
      (c'.work tapes.value).HasBinaryPrefix entry.2.bits ∧
      (c'.work tapes.value).cells 0 = Γ.start ∧
      (c'.work tapes.addressCounter).HasBinaryNat (bitlen entry.1) ∧
      (c'.work tapes.addressWidth).HasBinaryNat (bitlen entry.1) ∧
      (c'.work tapes.valueCounter).HasBinaryNat (bitlen entry.2) ∧
      (c'.work tapes.valueWidth).HasBinaryNat (bitlen entry.2) ∧
      (∀ i, i ≠ tapes.source → i ≠ tapes.address → i ≠ tapes.value →
        i ≠ tapes.addressCounter → i ≠ tapes.addressWidth →
        i ≠ tapes.valueCounter → i ≠ tapes.valueWidth →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  let addressTM := wordDecodeTM tapes.source tapes.address
    tapes.addressCounter tapes.addressWidth
  let valueTM := wordDecodeTM tapes.source tapes.value
    tapes.valueCounter tapes.valueWidth
  have hsourceAddress : (work₀ tapes.source).HasBinarySuffix
      (WordCode.encode entry.1 ++ (WordCode.encode entry.2 ++ rest)) := by
    simpa [Entry.encode, List.append_assoc] using hsource
  obtain ⟨addressDone, haddressReach, haddressHalt, haddressInput,
      haddressSource, haddressTarget, haddressCounterFinal,
      haddressWidthFinal, haddressFrame, haddressOutput⟩ :=
    wordDecodeTM_reachesIn_frame_encode tapes.source tapes.address
      tapes.addressCounter tapes.addressWidth tapes.addressDistinct entry.1
      (WordCode.encode entry.2 ++ rest) inp₀ work₀ out₀ hsourceAddress haddress
      haddressCounter haddressWidth hinput (fun i _ _ _ _ => hreads i) houtput
  have haddressStartFinal :
      (addressDone.work tapes.address).cells 0 = Γ.start :=
    TM.work_cells_zero_eq_start_of_reachesIn tapes.address haddressReach
      haddressStart
  have haddressReads : ∀ i, (addressDone.work i).read ≠ Γ.start := by
    intro i
    by_cases his : i = tapes.source
    · subst i
      exact haddressSource.read_ne_start
    · by_cases hit : i = tapes.address
      · subst i
        rw [haddressTarget.read_blank]
        decide
      · by_cases hic : i = tapes.addressCounter
        · subst i
          rw [haddressCounterFinal.eq_init_move_right]
          exact Tape.init_ofBool_move_right_read_ne_start (bitlen entry.1).bits
        · by_cases hiw : i = tapes.addressWidth
          · subst i
            rw [haddressWidthFinal.eq_init_move_right]
            exact Tape.init_ofBool_move_right_read_ne_start (bitlen entry.1).bits
          · rw [haddressFrame i his hit hic hiw]
            exact hreads i
  have hvalueInitial : (addressDone.work tapes.value).HasBinaryPrefix [] := by
    rw [haddressFrame tapes.value (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.ne (by decide)) (tapes.ne (by decide))]
    exact hvalue
  have hvalueStartInitial :
      (addressDone.work tapes.value).cells 0 = Γ.start := by
    rw [haddressFrame tapes.value (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.ne (by decide)) (tapes.ne (by decide))]
    exact hvalueStart
  have hvalueCounterInitial :
      (addressDone.work tapes.valueCounter).HasBinaryNat 0 := by
    rw [haddressFrame tapes.valueCounter (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.ne (by decide)) (tapes.ne (by decide))]
    exact hvalueCounter
  have hvalueWidthInitial :
      (addressDone.work tapes.valueWidth).HasBinaryNat 0 := by
    rw [haddressFrame tapes.valueWidth (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.ne (by decide)) (tapes.ne (by decide))]
    exact hvalueWidth
  obtain ⟨valueDone, hvalueReach, hvalueHalt, hvalueInput, hvalueSource,
      hvalueTarget, hvalueCounterFinal, hvalueWidthFinal, hvalueFrame,
      hvalueOutput⟩ :=
    wordDecodeTM_reachesIn_frame_encode tapes.source tapes.value
      tapes.valueCounter tapes.valueWidth tapes.valueDistinct entry.2 rest
      addressDone.input addressDone.work addressDone.output haddressSource
      hvalueInitial hvalueCounterInitial hvalueWidthInitial
      (by rw [haddressInput]; exact hinput)
      (fun i _ _ _ _ => haddressReads i)
      (by rw [haddressOutput]; exact houtput)
  have hvalueStartFinal : (valueDone.work tapes.value).cells 0 = Γ.start :=
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
  have hvalueReach' : valueTM.reachesIn (wordDecodeTime (bitlen entry.2))
      { state := valueTM.qstart
        input := TM.transitionInput addressDone.input
        work := fun i => TM.transitionTape (addressDone.work i)
        output := TM.transitionTape addressDone.output } valueDone := by
    rw [htransitionInput, htransitionWork, htransitionOutput]
    simpa [valueTM] using hvalueReach
  have hfullReach := TM.seqTM_reachesIn_of_reachesIn addressTM valueTM
    (by simpa [addressTM] using haddressReach) haddressHalt hvalueReach'
  let finalCfg := TM.phase2Wrap addressTM valueTM valueDone
  refine ⟨finalCfg, ?_, ?_, hvalueInput.trans haddressInput, hvalueSource, ?_,
    ?_, hvalueTarget, hvalueStartFinal, ?_, ?_, hvalueCounterFinal,
    hvalueWidthFinal, ?_, hvalueOutput.trans haddressOutput⟩
  · simpa [entryDecodeTM, entryDecodeTime, addressTM, valueTM, finalCfg] using!
      hfullReach
  · exact (TM.phase2Wrap_halted_iff addressTM valueTM valueDone).2 hvalueHalt
  · change (valueDone.work tapes.address).HasBinaryPrefix entry.1.bits
    rw [hvalueFrame tapes.address (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.ne (by decide)) (tapes.ne (by decide))]
    exact haddressTarget
  · change (valueDone.work tapes.address).cells 0 = Γ.start
    rw [hvalueFrame tapes.address (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.ne (by decide)) (tapes.ne (by decide))]
    exact haddressStartFinal
  · change (valueDone.work tapes.addressCounter).HasBinaryNat (bitlen entry.1)
    rw [hvalueFrame tapes.addressCounter (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.ne (by decide)) (tapes.ne (by decide))]
    exact haddressCounterFinal
  · change (valueDone.work tapes.addressWidth).HasBinaryNat (bitlen entry.1)
    rw [hvalueFrame tapes.addressWidth (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.ne (by decide)) (tapes.ne (by decide))]
    exact haddressWidthFinal
  · intro i his hia hiv hiac hiaw hivc hivw
    change valueDone.work i = work₀ i
    rw [hvalueFrame i his hiv hivc hivw,
      haddressFrame i his hia hiac hiaw]

end Machine

end RegisterStore

end RAM

end Complexity
