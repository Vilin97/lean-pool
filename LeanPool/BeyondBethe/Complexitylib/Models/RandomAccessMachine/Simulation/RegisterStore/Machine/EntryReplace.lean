/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryReplace.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryReplace.Internal

/-!
# Sparse-entry replacement
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Emit a matched address with a canonical replacement value, restore that
external value source, and clear all entry scratch for the next iteration. -/
theorem entryReplaceCleanupTM_hoareTime_frame {n : ℕ}
    (tapes : EntryReplaceTapes n) (entry : Entry) (newValue : ℕ)
    (rest queryBits emitted : List Bool)
    (initialWork matchedWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hmatch : ReadableEntryMatch tapes.entry entry rest queryBits
      initialWork matchedWork)
    (hreplacement : (matchedWork tapes.replacement).HasBinaryNat newValue)
    (hinput : TM.Parked inp₀) (houtput : out₀.HasBinaryPrefix emitted) :
    (entryReplaceCleanupTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = matchedWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryScanReady tapes.entry rest queryBits initialWork work ∧
        work tapes.replacement = matchedWork tapes.replacement ∧
        out.HasBinaryPrefix
          (emitted ++ Entry.encode (entry.1, newValue)))
      (entryReplaceCleanupTime tapes entry newValue queryBits
        initialWork matchedWork) :=
  entryReplaceCleanupTM_hoareTime_frame_internal tapes entry newValue rest
    queryBits emitted initialWork matchedWork inp₀ out₀ hmatch hreplacement
    hinput houtput

/-- Replacement emission and cleanup are append-only on the output tape. -/
theorem entryReplaceCleanupTM_isTransducer {n : ℕ}
    (tapes : EntryReplaceTapes n) :
    (entryReplaceCleanupTM tapes).IsTransducer :=
  (rewindEntryEncodeTM_isTransducer tapes.encodeTapes).seqTM
    ((TM.rewindWorkTM_isTransducer tapes.replacement).seqTM
      (entryMissCleanupTM_isTransducer tapes.entry))

/-- Coarse all-prefix auxiliary-space envelope for replacement and cleanup. -/
theorem entryReplaceCleanupTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryReplaceTapes n) (entry : Entry) (newValue : ℕ)
    (queryBits : List Bool) (initialWork matchedWork : Fin n → Tape)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryReplaceCleanupTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryReplaceCleanupTM tapes).reachesIn time start current)
    (htime : time ≤ entryReplaceCleanupTime tapes entry newValue queryBits
      initialWork matchedWork) :
    current.WithinAuxSpace inputLength
      (initialSpace + entryReplaceCleanupTime tapes entry newValue queryBits
        initialWork matchedWork) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

end Machine

end RegisterStore

end RAM

end Complexity
