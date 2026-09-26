/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMissCopy.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMissCopy.Internal

/-!
# Sparse-entry miss copy

This module exposes the update-scan branch that appends one unmatched entry to
the new store and restores the exact invariant needed to inspect the next one.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Copy one decoded unmatched entry to the output stream and restore the
ordinary next-entry scan invariant, with an explicit intermediate work frame. -/
theorem entryMissCopyTM_hoareTime_frame {n : ℕ}
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits emitted : List Bool)
    (initialWork matchedWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hmatch : ReadableEntryMatch tapes entry rest queryBits initialWork matchedWork)
    (hinput : TM.Parked inp₀) (houtput : out₀.HasBinaryPrefix emitted) :
    (entryMissCopyTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = matchedWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryScanReady tapes rest queryBits initialWork work ∧
        out.HasBinaryPrefix (emitted ++ Entry.encode entry))
      (entryMissCopyTime tapes entry queryBits initialWork matchedWork) :=
  entryMissCopyTM_hoareTime_frame_internal tapes entry rest queryBits emitted
    initialWork matchedWork inp₀ out₀ hmatch hinput houtput

/-- Miss-copy is append-only on the output tape. -/
theorem entryMissCopyTM_isTransducer {n : ℕ} (tapes : EntryMatchTapes n) :
    (entryMissCopyTM tapes).IsTransducer :=
  (rewindEntryEncodeTM_isTransducer tapes.encodeTapes).seqTM
    (entryMissCleanupTM_isTransducer tapes)

/-- Coarse all-prefix auxiliary-space envelope for one miss-copy branch. -/
theorem entryMissCopyTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryMatchTapes n) (entry : Entry) (queryBits : List Bool)
    (initialWork matchedWork : Fin n → Tape)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryMissCopyTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryMissCopyTM tapes).reachesIn time start current)
    (htime : time ≤
      entryMissCopyTime tapes entry queryBits initialWork matchedWork) :
    current.WithinAuxSpace inputLength
      (initialSpace +
        entryMissCopyTime tapes entry queryBits initialWork matchedWork) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

end Machine

end RegisterStore

end RAM

end Complexity
