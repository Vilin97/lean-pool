/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryAppend.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryAppend.Internal

/-!
# Sparse-entry final append
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Append one absent query/nonzero-value entry and restore both canonical
source tapes exactly, retaining the caller's complete work family. -/
theorem entryAppendRestoreTM_hoareTime_frame {n : ℕ}
    (tapes : EntryReplaceTapes n) (address newValue : ℕ)
    (emitted : List Bool) (initialWork readyWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hready : EntryScanReady tapes.entry [] address.bits initialWork readyWork)
    (hreplacement : (readyWork tapes.replacement).HasBinaryNat newValue)
    (hinput : TM.Parked inp₀) (houtput : out₀.HasBinaryPrefix emitted) :
    (entryAppendRestoreTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = readyWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = readyWork ∧
        out.HasBinaryPrefix
          (emitted ++ Entry.encode (address, newValue)))
      (entryAppendRestoreTime address newValue) :=
  entryAppendRestoreTM_hoareTime_frame_internal tapes address newValue
    emitted initialWork readyWork inp₀ out₀ hready hreplacement hinput houtput

/-- Final append and restoration are append-only on the output tape. -/
theorem entryAppendRestoreTM_isTransducer {n : ℕ}
    (tapes : EntryReplaceTapes n) :
    (entryAppendRestoreTM tapes).IsTransducer :=
  (rewindEntryEncodeTM_isTransducer tapes.appendEncodeTapes).seqTM
    ((TM.rewindWorkTM_isTransducer tapes.entry.query).seqTM
      (TM.rewindWorkTM_isTransducer tapes.replacement))

/-- Coarse all-prefix auxiliary-space envelope for final append/restoration. -/
theorem entryAppendRestoreTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryReplaceTapes n) (address newValue : ℕ)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryAppendRestoreTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryAppendRestoreTM tapes).reachesIn time start current)
    (htime : time ≤ entryAppendRestoreTime address newValue) :
    current.WithinAuxSpace inputLength
      (initialSpace + entryAppendRestoreTime address newValue) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

end Machine

end RegisterStore

end RAM

end Complexity
