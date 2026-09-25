/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseDefs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Immediate
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Tagged

/-!
# Dense-overlay immediate instruction
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

variable {n : ℕ}

private theorem hasBinaryPrefix_parked {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : TM.Parked t :=
  TM.hasBinaryPrefix_parked h

private theorem phaseTransition_of_parked
    {inp out : Tape} {work : Fin n → Tape}
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    TM.transitionInput inp = inp ∧
      (fun i => TM.transitionTape (work i)) = work ∧
      TM.transitionTape out = out :=
  TM.phaseTransition_of_parked hinput hwork houtput

/-- Exact semantic and time contract for one immediate dense-overlay write. -/
theorem denseImmediateInstructionTM_hoareTime_frame
    (tapes : BinaryInstructionTapes n) (overlay : Store)
    (destination value : ℕ) (emittedBits : List Bool)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hcanonical : Canonical overlay)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup overlay initialWork)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (hinput : TM.Parked inp₀)
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (denseImmediateInstructionTM tapes destination value).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DenseImmediateInstructionResult tapes overlay destination value
          initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (DenseOverlay.write overlay destination value).flatMap Entry.encode))
      (denseImmediateInstructionTime tapes overlay destination value) := by
  let valueWork := Function.update initialWork tapes.update.replacement
    ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)
  let updateWork := Function.update valueWork tapes.update.entry.query
    ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right)
  have houtputParked := hasBinaryPrefix_parked houtput
  have hvalue := TM.binaryAddConstTM_hoareTime_frame
    tapes.update.replacement value 0 inp₀ initialWork out₀ hreplacement
    hinput (fun i _ => hinitial.scanner.parked i) houtputParked
  have hvalue' : (TM.binaryAddConstTM tapes.update.replacement value).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = valueWork ∧ out = out₀)
      (TM.binaryAddConstTime value 0) := by
    simpa only [valueWork, zero_add] using! hvalue
  have hquery : (TM.binaryAddConstTM tapes.update.entry.query
      destination).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = valueWork ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = updateWork ∧ out = out₀)
      (TM.binaryAddConstTime destination 0) := by
    have hqueryZero : (valueWork tapes.update.entry.query).HasBinaryNat 0 := by
      have hqueryReplacement :
          tapes.update.entry.query ≠ tapes.update.replacement :=
        tapes.update.ne (by decide)
      rw [show valueWork tapes.update.entry.query =
          initialWork tapes.update.entry.query by
        exact Function.update_of_ne hqueryReplacement _ initialWork]
      exact ⟨hinitial.scanner.queryStart, by simpa using! hinitial.scanner.query⟩
    have hrun := TM.binaryAddConstTM_hoareTime_frame
      tapes.update.entry.query destination 0 inp₀ valueWork out₀ hqueryZero
      hinput
      (fun i _ => by
        by_cases hi : i = tapes.update.replacement
        · subst i
          have hnat := Tape.init_move_right_hasBinaryNat value
          simpa only [valueWork, Function.update_self] using!
            (show TM.Parked
                ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right) from
              ⟨by rw [hnat.2.1],
                hnat.2.hasBinaryContent.cells_ne_start⟩)
        · simpa only [valueWork, Function.update_of_ne hi] using!
            hinitial.scanner.parked i)
      houtputParked
    simpa only [updateWork, zero_add] using! hrun
  have hready := immediateUpdate_ready_internal tapes overlay destination value
    initialWork hinitial
  have hupdate := taggedEntryUpdateTM_hoareTime_frame tapes.update overlay
    destination value emittedBits updateWork inp₀ out₀ hcanonical hready.1
    hready.2.1 hready.2.2.1 hready.2.2.2.1 hready.2.2.2.2.1 hinput houtput
  have hupdate' : (taggedEntryUpdateTM tapes.update).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = updateWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DenseImmediateInstructionResult tapes overlay destination value
          initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (DenseOverlay.write overlay destination value).flatMap Entry.encode))
      (taggedEntryUpdateTime tapes.update overlay destination value) :=
    hupdate.strengthen_post (by
      rintro inp work out ⟨hinp, houtcome, hout⟩
      exact ⟨hinp, ⟨valueWork, updateWork, rfl, rfl, houtcome⟩, hout⟩)
  have hqueryUpdate := TM.seqTM_hoareTime
    (TM.binaryAddConstTM tapes.update.entry.query destination)
    (taggedEntryUpdateTM tapes.update) hquery
    (by
      rintro inp work out ⟨hinp, hwork, hout⟩
      subst work
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := updateWork) (out := out)
        (by simpa [hinp] using! hinput) hready.2.2.2.2.2
        (by simpa [hout] using! houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, rfl, hout⟩)
    hupdate'
  have hall := TM.seqTM_hoareTime
    (TM.binaryAddConstTM tapes.update.replacement value)
    (TM.seqTM (TM.binaryAddConstTM tapes.update.entry.query destination)
      (taggedEntryUpdateTM tapes.update)) hvalue'
    (by
      rintro inp work out ⟨hinp, hwork, hout⟩
      subst work
      have hparked : ∀ i, TM.Parked (valueWork i) := by
        intro i
        by_cases hi : i = tapes.update.replacement
        · subst i
          have hnat := Tape.init_move_right_hasBinaryNat value
          simpa only [valueWork, Function.update_self] using!
            (show TM.Parked
                ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right) from
              ⟨by rw [hnat.2.1], hnat.2.hasBinaryContent.cells_ne_start⟩)
        · simpa only [valueWork, Function.update_of_ne hi] using!
            hinitial.scanner.parked i
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := valueWork) (out := out)
        (by simpa [hinp] using! hinput) hparked
        (by simpa [hout] using! houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, rfl, hout⟩)
    hqueryUpdate
  simpa [denseImmediateInstructionTM, denseImmediateInstructionTime] using! hall

end Machine
end RegisterStore
end RAM
end Complexity
