/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.DenseInternal

/-!
# Reusable sparse-register operand lookup

This module exposes one complete sparse-register read as a reusable TM
subroutine. It loads a canonical query, scans the encoded store, copies the
semantic value out, resets every scanner-owned tape, rewinds the read-only
source, restores the runtime entry count, and returns to the same scanner ABI.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- One loaded lookup returns the scanner to its blank-query boundary, places
exactly `RegisterStore.read store address` on the destination tape, and
preserves the complete external frame. -/
theorem entryLookupLoadedTM_hoareTime_frame {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hready : EntryLookupRestoreReady tapes store address initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryLookupLoadedTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupRestoreResult tapes store address initialWork work ∧
        out = out₀)
      (entryLookupLoadedTime tapes store address) :=
  entryLookupLoaded_hoareTime_internal tapes store address initialWork
    inp₀ out₀ hready hinput houtput

/-- A reusable lookup through a positive-tag mutable overlay returns either
the decoded tag or the corresponding immutable public-input register. -/
theorem denseOverlayLookupTM_hoareTime_frame {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (input : List Bool)
    (overlay : Store) (address : ℕ) (initialWork : Fin n → Tape)
    (out₀ : Tape) (hvalid : DenseOverlay.Valid overlay)
    (hready : EntryLookupRestoreReady tapes overlay address initialWork)
    (houtput : TM.Parked out₀) :
    (denseOverlayLookupTM tapes).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseOverlayLookupResult tapes input overlay address initialWork work ∧
        out = out₀)
      (denseOverlayLookupTime tapes input.length overlay address) :=
  denseOverlayLookupTM_hoareTime_internal tapes input overlay address
    initialWork out₀ hvalid hready houtput

/-- A fixed-address dense-overlay lookup synthesizes and clears its query,
while returning the decoded register value at the reusable scanner boundary. -/
theorem denseOverlayLookupStaticTM_hoareTime_frame {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (input : List Bool)
    (overlay : Store) (address : ℕ) (initialWork : Fin n → Tape)
    (out₀ : Tape) (hvalid : DenseOverlay.Valid overlay)
    (hready : EntryLookupStaticReady tapes overlay initialWork)
    (houtput : TM.Parked out₀) :
    (denseOverlayLookupStaticTM tapes address).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseOverlayLookupStaticResult tapes input overlay address initialWork
          work ∧ out = out₀)
      (denseOverlayLookupStaticTime tapes input.length overlay address) :=
  denseOverlayLookupStaticTM_hoareTime_internal tapes input overlay address
    initialWork out₀ hvalid hready houtput

/-- Reusable sparse-register lookup never moves the output head left. -/
theorem entryLookupLoadedTM_isTransducer {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) :
    (entryLookupLoadedTM tapes).IsTransducer := by
  exact
    (TM.binaryCopyIntoTM_isTransducer tapes.querySource
      tapes.scan.entry.query tapes.copyScratch).seqTM
    ((entryLookupTM_isTransducer tapes.scan).seqTM
      ((TM.rewindWorkTM_isTransducer tapes.scan.entry.value).seqTM
        ((TM.binaryCopyIntoTM_isTransducer tapes.scan.entry.value
          tapes.destination tapes.copyScratch).seqTM
          ((TM.resetBinaryWorkManyTM_isTransducer
            (entryLookupResetTargets tapes)).seqTM
            ((TM.rewindWorkTM_isTransducer tapes.scan.entry.source).seqTM
              (TM.binaryCopyIntoTM_isTransducer tapes.countSource
                tapes.scan.count tapes.copyScratch))))))

/-- Every prefix of a loaded lookup stays within its initial auxiliary space
plus the advertised total running-time bound. -/
theorem entryLookupLoadedTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryLookupLoadedTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryLookupLoadedTM tapes).reachesIn time start current)
    (htime : time ≤ entryLookupLoadedTime tapes store address) :
    current.WithinAuxSpace inputLength
      (initialSpace + entryLookupLoadedTime tapes store address) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- A fixed-address lookup synthesizes its query from zero, returns the
scanner to its reusable boundary, places the semantic register value in the
destination, and clears the temporary query source. -/
theorem entryLookupStaticTM_hoareTime_frame {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hready : EntryLookupStaticReady tapes store initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryLookupStaticTM tapes address).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupStaticResult tapes store address initialWork work ∧
        out = out₀)
      (entryLookupStaticTime tapes store address) :=
  entryLookupStatic_hoareTime_internal tapes store address initialWork
    inp₀ out₀ hready hinput houtput

/-- Fixed-address lookup never moves the output head left. -/
theorem entryLookupStaticTM_isTransducer {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (address : ℕ) :
    (entryLookupStaticTM tapes address).IsTransducer := by
  exact
    (TM.binaryAddConstTM_isTransducer tapes.querySource address).seqTM
      ((entryLookupLoadedTM_isTransducer tapes).seqTM
        (TM.resetBinaryWorkTM_isTransducer tapes.querySource))

/-- Every fixed-address lookup prefix stays within its initial auxiliary space
plus the advertised total running-time bound. -/
theorem entryLookupStaticTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryLookupStaticTM tapes address).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryLookupStaticTM tapes address).reachesIn time start current)
    (htime : time ≤ entryLookupStaticTime tapes store address) :
    current.WithinAuxSpace inputLength
      (initialSpace + entryLookupStaticTime tapes store address) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

end Machine

end RegisterStore

end RAM

end Complexity
