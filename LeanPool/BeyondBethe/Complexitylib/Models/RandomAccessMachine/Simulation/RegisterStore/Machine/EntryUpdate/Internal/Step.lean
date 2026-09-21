/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Internal.Hit
public import
LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Internal.Miss

/-!
# Bounded encoded sparse-store update -- one positive iteration
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem found_eq_false_of_current_eq
    {tapes : EntryUpdateTapes n} {store : Store} {address newValue : ℕ}
    {processed emitted : Store} {entry : Entry} {rest : Store}
    {found : Bool} {resultCount : ℕ}
    {initialWork work : Fin n → Tape}
    (hinv : EntryUpdateLoopInv tapes store address newValue processed
      (entry :: rest) emitted found resultCount initialWork work)
    (hnodup : AddressesNodup store) (haddress : entry.1 = address) :
    found = false := by
  cases found with
  | false => rfl
  | true =>
      exfalso
      have hnot := hinv.progress.not_mem_remaining_of_found_internal
        hnodup rfl
      apply hnot
      simp [haddress]

/-- One positive old-entry iteration advances the semantic and tape loop
invariant, returning to the controller's test state. -/
theorem entryUpdateIteration_internal
    (tapes : EntryUpdateTapes n) (store : Store) (address newValue : ℕ)
    (processed emitted : Store) (entry : Entry) (rest : Store)
    (found : Bool) (resultCount : ℕ)
    (initialWork work : Fin n → Tape) (outPrefix : List Bool)
    (inp out : Tape)
    (hinv : EntryUpdateLoopInv tapes store address newValue processed
      (entry :: rest) emitted found resultCount initialWork work)
    (hnodup : AddressesNodup store)
    (hinput : TM.Parked inp)
    (houtput : out.HasBinaryPrefix
      (outPrefix ++ emitted.flatMap Entry.encode)) :
    ∃ processed' emitted' found' resultCount' nextWork nextOut time,
      time ≤ entryUpdateIterationTime tapes entry rest address newValue
        store.length ∧
      (entryUpdateTM tapes).reachesIn time
        (entryUpdateTestCfg tapes inp work out)
        (entryUpdateTestCfg tapes inp nextWork nextOut) ∧
      EntryUpdateLoopInv tapes store address newValue processed' rest emitted'
        found' resultCount' initialWork nextWork ∧
      nextOut.HasBinaryPrefix
        (outPrefix ++ emitted'.flatMap Entry.encode) := by
  by_cases haddress : entry.1 = address
  · have hfoundFalse :=
      found_eq_false_of_current_eq hinv hnodup haddress
    have hinvFalse : EntryUpdateLoopInv tapes store address newValue
        processed (entry :: rest) emitted false resultCount initialWork work := by
      simpa [hfoundFalse] using hinv
    by_cases hvalue : newValue = 0
    · subst newValue
      obtain ⟨nextWork, nextOut, time, htime, hreach, hnextInv,
          hnextOutput⟩ :=
        entryUpdateDeleteIteration_internal tapes store address processed
          emitted entry rest resultCount initialWork work outPrefix inp out
          hinvFalse haddress.symm hinput houtput
      exact ⟨processed ++ [entry], emitted, true, resultCount - 1,
        nextWork, nextOut, time, htime, hreach, hnextInv, hnextOutput⟩
    · obtain ⟨nextWork, nextOut, time, htime, hreach, hnextInv,
          hnextOutput⟩ :=
        entryUpdateReplaceIteration_internal tapes store address newValue
          processed emitted entry rest resultCount initialWork work outPrefix
          inp out hinvFalse haddress.symm hvalue hinput houtput
      exact ⟨processed ++ [entry], emitted ++ [(address, newValue)], true,
        resultCount, nextWork, nextOut, time, htime, hreach, hnextInv,
        hnextOutput⟩
  ·
    obtain ⟨nextWork, nextOut, time, htime, hreach, hnextInv,
        hnextOutput⟩ :=
      entryUpdateIteration_miss_internal tapes store address newValue
        processed emitted entry rest found resultCount initialWork work
        outPrefix inp out hinv haddress hinput houtput
    exact ⟨processed ++ [entry], emitted ++ [entry], found, resultCount,
      nextWork, nextOut, time, htime, hreach, hnextInv, hnextOutput⟩

end Machine

end RegisterStore

end RAM

end Complexity
