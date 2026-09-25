/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Internal.Step
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Internal.End

/-!
# Bounded encoded sparse-store update -- semantic composition

This file composes the checked one-entry and terminal contracts into the
complete update loop.  The induction is over the runtime-counted remaining
store, while the loop invariant carries the processed prefix and emitted
output needed to connect the concrete controller to `RegisterStore.write`.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

/-- Starting from any valid loop boundary, the update controller finishes the
remaining suffix within its recursive static budget. -/
theorem entryUpdateLoop_internal
    (tapes : EntryUpdateTapes n) (store : Store) (address newValue : ℕ)
    (processed remaining emitted : Store) (found : Bool)
    (resultCount : ℕ) (initialWork work : Fin n → Tape)
    (outPrefix : List Bool) (inp out : Tape)
    (hinv : EntryUpdateLoopInv tapes store address newValue processed
      remaining emitted found resultCount initialWork work)
    (hnodup : AddressesNodup store)
    (hinput : TM.Parked inp)
    (houtput : out.HasBinaryPrefix
      (outPrefix ++ emitted.flatMap Entry.encode)) :
    ∃ final time,
      time ≤ entryUpdateLoopTime tapes address newValue store.length
        remaining ∧
      (entryUpdateTM tapes).reachesIn time
        (entryUpdateTestCfg tapes inp work out) final ∧
      (entryUpdateTM tapes).halted final ∧
      final.input = inp ∧
      EntryUpdateOutcome tapes store address newValue initialWork final.work ∧
      final.output.HasBinaryPrefix
        (outPrefix ++ (RegisterStore.write store address newValue).flatMap
          Entry.encode) := by
  induction remaining generalizing processed emitted found resultCount work out with
  | nil =>
      exact entryUpdateTerminal_internal tapes store address newValue
        processed emitted found resultCount initialWork work outPrefix inp out
        hinv hinput houtput
  | cons entry rest ih =>
      obtain ⟨processed', emitted', found', resultCount', nextWork,
          nextOut, iterationTime, hiterationTime, hiterationReach,
          hnextInv, hnextOutput⟩ :=
        entryUpdateIteration_internal tapes store address newValue processed
          emitted entry rest found resultCount initialWork work outPrefix inp
          out hinv hnodup hinput houtput
      obtain ⟨final, recursiveTime, hrecursiveTime, hrecursiveReach,
          hhalt, hfinalInput, houtcome, hfinalOutput⟩ :=
        ih processed' emitted' found' resultCount' nextWork nextOut hnextInv
          hnextOutput
      refine ⟨final, iterationTime + recursiveTime, ?_, ?_, hhalt,
        hfinalInput, houtcome, hfinalOutput⟩
      · simp only [entryUpdateLoopTime]
        omega
      · exact TM.reachesIn_trans (entryUpdateTM tapes) hiterationReach
          hrecursiveReach

/-- A complete encoded sparse-store update realizes `RegisterStore.write`,
preserves input and the external work frame exactly, and appends precisely the
new store encoding to the caller's existing output prefix. -/
theorem entryUpdateTM_hoareTime_frame_internal
    (tapes : EntryUpdateTapes n) (store : Store) (address newValue : ℕ)
    (emittedBits : List Bool) (initialWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hcanonical : Canonical store)
    (hready : EntryScanReady tapes.entry (store.flatMap Entry.encode)
      address.bits initialWork initialWork)
    (hreplacement :
      (initialWork tapes.replacement).HasBinaryNat newValue)
    (hremaining :
      (initialWork tapes.remaining).HasBinaryNat store.length)
    (hfound : (initialWork tapes.found).HasBinaryNat 0)
    (hresultCount :
      (initialWork tapes.resultCount).HasBinaryNat store.length)
    (hinput : TM.Parked inp₀)
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (entryUpdateTM tapes).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryUpdateOutcome tapes store address newValue initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store address newValue).flatMap
              Entry.encode))
      (entryUpdateTime tapes store address newValue) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  have hinv := entryUpdateLoopInv_initial_internal tapes store address
    newValue initialWork hready hreplacement hremaining hfound hresultCount
  have houtput' : out₀.HasBinaryPrefix
      (emittedBits ++ ([] : Store).flatMap Entry.encode) := by
    simpa using houtput
  obtain ⟨final, time, htime, hreach, hhalt, hfinalInput, houtcome,
      hfinalOutput⟩ :=
    entryUpdateLoop_internal tapes store address newValue [] store [] false
      store.length initialWork initialWork emittedBits inp₀ out₀ hinv
      hcanonical.1 hinput houtput'
  refine ⟨final, time, ?_, ?_, hhalt, hfinalInput, houtcome,
    hfinalOutput⟩
  · simpa [entryUpdateTime] using htime
  · simpa [entryUpdateTestCfg, entryUpdateTM] using hreach

end Machine

end RegisterStore

end RAM

end Complexity
