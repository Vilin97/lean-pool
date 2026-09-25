/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryAppend
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMissCopy
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryReplace
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryPred
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMatch

/-!
# Bounded encoded sparse-store update — output safety internals

The update controller delegates every nested phase to an independently checked
one-way-output machine. Its own dispatch transitions either read back or leave
the output head idle, so the complete controller remains a transducer.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- A canonical binary prefix parks its tape head away from the left endmarker
and contains no spurious left endmarkers. -/
theorem parked_of_binaryPrefix_internal {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : TM.Parked t :=
  ⟨by rw [h.1]; omega,
    (show t.HasBinaryContent bits from h.2).cells_ne_start⟩

/-- The fixed sparse-store update controller never moves its output head left. -/
theorem entryUpdateTM_isTransducer_internal {n : ℕ}
    (tapes : EntryUpdateTapes n) :
    (entryUpdateTM tapes).IsTransducer := by
  intro state iHead wHeads oHead
  cases state with
  | test =>
      simp only [entryUpdateTM]
      split
      · split
        · cases oHead <;> simp [TM.allReadBack, TM.idleDir]
        · split <;> cases oHead <;>
            simp [TM.allReadBack, TM.idleDir]
      · cases oHead <;> simp [TM.allReadBack, TM.idleDir]
  | matching q =>
      simp only [entryUpdateTM]
      split
      · split
        · cases oHead <;> simp [TM.idleDir]
        · cases oHead <;> simp [TM.allReadBack, TM.idleDir]
      · exact entryMatchReadTM_isTransducer tapes.entry q iHead wHeads oHead
  | miss q =>
      simp only [entryUpdateTM]
      split
      · cases oHead <;> simp [TM.allReadBack, TM.idleDir]
      · exact entryMissCopyTM_isTransducer tapes.entry q iHead wHeads oHead
  | delete q =>
      simp only [entryUpdateTM]
      split
      · cases oHead <;> simp [TM.allReadBack, TM.idleDir]
      · exact entryMissCleanupTM_isTransducer tapes.entry q iHead wHeads oHead
  | replace q =>
      simp only [entryUpdateTM]
      split
      · cases oHead <;> simp [TM.allReadBack, TM.idleDir]
      · exact entryReplaceCleanupTM_isTransducer tapes.replace q iHead wHeads oHead
  | append q =>
      simp only [entryUpdateTM]
      split
      · cases oHead <;> simp [TM.allReadBack, TM.idleDir]
      · exact entryAppendRestoreTM_isTransducer tapes.replace q iHead wHeads oHead
  | remaining q =>
      simp only [entryUpdateTM]
      split
      · cases oHead <;> simp [TM.allReadBack, TM.idleDir]
      · exact TM.binaryPredTM_isTransducer tapes.remaining q iHead wHeads oHead
  | deleteCount q =>
      simp only [entryUpdateTM]
      split
      · cases oHead <;> simp [TM.allReadBack, TM.idleDir]
      · exact TM.binaryPredTM_isTransducer tapes.resultCount q iHead wHeads oHead
  | appendCount q =>
      simp only [entryUpdateTM]
      split
      · cases oHead <;> simp [TM.allReadBack, TM.idleDir]
      · exact TM.binarySuccTM_isTransducer tapes.resultCount q iHead wHeads oHead
  | done => cases oHead <;> simp [entryUpdateTM, TM.allIdle, TM.idleDir]

end Machine

end RegisterStore

end RAM

end Complexity
