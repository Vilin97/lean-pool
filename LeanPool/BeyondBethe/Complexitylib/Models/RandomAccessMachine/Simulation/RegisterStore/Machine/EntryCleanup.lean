/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryCleanup.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryCleanup.Internal

/-!
# Sparse-entry miss cleanup

This module exposes the exact invariant-restoring miss branch used by the
bounded sparse register-store scan.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- After a failed readable entry match, rewind the preserved query and reset
all seven decoder/result scratch tapes, restoring the next-iteration frame. -/
theorem entryMissCleanupTM_hoareTime_frame {n : ℕ}
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits : List Bool)
    (initialWork matchedWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hmatch : ReadableEntryMatch tapes entry rest queryBits initialWork matchedWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryMissCleanupTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = matchedWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryScanReady tapes rest queryBits initialWork work ∧
        out = out₀)
      (entryMissCleanupTime tapes entry queryBits initialWork) :=
  entryMissCleanupTM_hoareTime_frame_internal tapes entry rest queryBits
    initialWork matchedWork inp₀ out₀ hmatch hinput houtput

/-- Miss cleanup preserves one-way output safety. -/
theorem entryMissCleanupTM_isTransducer {n : ℕ} (tapes : EntryMatchTapes n) :
    (entryMissCleanupTM tapes).IsTransducer := by
  unfold entryMissCleanupTM
  exact (TM.rewindWorkTM_isTransducer tapes.query).seqTM
    (TM.resetBinaryWorkManyTM_isTransducer (entryMissTargets tapes))

/-- Coarse all-prefix auxiliary-space envelope for miss cleanup. -/
theorem entryMissCleanupTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryMatchTapes n) (entry : Entry) (queryBits : List Bool)
    (initialWork : Fin n → Tape) (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryMissCleanupTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryMissCleanupTM tapes).reachesIn time start current)
    (htime : time ≤ entryMissCleanupTime tapes entry queryBits initialWork) :
    current.WithinAuxSpace inputLength
      (initialSpace + entryMissCleanupTime tapes entry queryBits initialWork) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

end Machine

end RegisterStore

end RAM

end Complexity
