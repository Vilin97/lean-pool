/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Internal.Out
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Internal.Sem
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.BoundsInternal
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Source

/-!
# Bounded encoded sparse-store update

This module exposes the complete fixed-controller implementation of one
canonical sparse-store write. The machine scans a runtime-counted old store,
copies misses, replaces or deletes the unique hit, and appends a fresh nonzero
entry exactly when the address was absent.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- The encoded source cursor may move during an update, but its complete cell
contents are read-only. -/
theorem entryUpdateTM_source_readOnly {n : ℕ} (tapes : EntryUpdateTapes n) :
    (entryUpdateTM tapes).WorkReadOnly tapes.entry.source :=
  entryUpdateTM_source_readOnly_internal tapes

/-- Update one runtime-sized canonical sparse store. The output appends exactly
the encoding of `RegisterStore.write`; input, the replacement source, and every
work tape outside the thirteen-tape assignment retain their checked frames. -/
theorem entryUpdateTM_hoareTime_frame {n : ℕ}
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
              Entry.encode) ∧
        (work tapes.entry.source).cells =
          (initialWork tapes.entry.source).cells)
      (entryUpdateTime tapes store address newValue) := by
  have hupdate := entryUpdateTM_hoareTime_frame_internal tapes store address newValue
    emittedBits initialWork inp₀ out₀ hcanonical hready hreplacement
    hremaining hfound hresultCount hinput houtput
  intro inp work out hpre
  obtain ⟨final, time, htime, hreach, hhalt, hinp, houtcome, hout⟩ :=
    hupdate inp work out hpre
  have hsourceCells :
      (final.work tapes.entry.source).cells =
        (initialWork tapes.entry.source).cells := by
    have hstartWork : work = initialWork := hpre.2.1
    have hnostart : ∀ j, 1 ≤ j →
        (work tapes.entry.source).cells j ≠ Γ.start := by
      rw [hstartWork]
      exact hready.source.2.2.2
    exact ((entryUpdateTM_source_readOnly tapes).cells_eq_of_reachesIn
      hreach hnostart).trans (congrArg (fun w => (w tapes.entry.source).cells)
        hstartWork)
  exact ⟨final, time, htime, hreach, hhalt, hinp, houtcome, hout,
    hsourceCells⟩

/-- Redirect an encoded sparse-store update into a fresh last work tape. This
is the stable seam used by the multi-step RAM interpreter: the real output is
left blank while the updated store becomes an ordinary work-tape buffer. -/
theorem entryUpdateTM_retargetOutput_hoareTime_frame {n : ℕ}
    (tapes : EntryUpdateTapes n) (store : Store) (address newValue : ℕ)
    (emittedBits : List Bool) (initialWork : Fin (n + 1) → Tape)
    (inp₀ : Tape)
    (hcanonical : Canonical store)
    (hready : EntryScanReady tapes.entry (store.flatMap Entry.encode)
      address.bits (fun i => initialWork (Fin.castSucc i))
        (fun i => initialWork (Fin.castSucc i)))
    (hreplacement :
      (initialWork (Fin.castSucc tapes.replacement)).HasBinaryNat newValue)
    (hremaining :
      (initialWork (Fin.castSucc tapes.remaining)).HasBinaryNat store.length)
    (hfound :
      (initialWork (Fin.castSucc tapes.found)).HasBinaryNat 0)
    (hresultCount :
      (initialWork (Fin.castSucc tapes.resultCount)).HasBinaryNat store.length)
    (hinput : TM.Parked inp₀)
    (hbuffer : (initialWork (Fin.last n)).HasBinaryPrefix emittedBits) :
    (entryUpdateTM tapes).retargetOutput.HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
          out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryUpdateOutcome tapes store address newValue
          (fun i => initialWork (Fin.castSucc i))
          (fun i => work (Fin.castSucc i)) ∧
        (work (Fin.last n)).HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store address newValue).flatMap Entry.encode) ∧
        (work (Fin.castSucc tapes.entry.source)).cells =
          (initialWork (Fin.castSucc tapes.entry.source)).cells ∧
        out = (Tape.init []).move Dir3.right)
      (entryUpdateTime tapes store address newValue) := by
  let baseWork : Fin n → Tape := fun i => initialWork (Fin.castSucc i)
  let buffer := initialWork (Fin.last n)
  have hupdate := entryUpdateTM_hoareTime_frame tapes store address newValue
    emittedBits baseWork inp₀ buffer hcanonical hready hreplacement hremaining
    hfound hresultCount hinput hbuffer
  have hlift := TM.retargetOutput_hoareTime (entryUpdateTM tapes) hupdate
  apply hlift.consequence
  · rintro inp work out ⟨hinp, hwork, hout⟩
    subst inp
    subst work
    exact ⟨⟨rfl, rfl, rfl⟩, hout⟩
  · intro inp work out hpost
    rcases hpost with ⟨⟨hinp, houtcome, hstore, hsource⟩, hout⟩
    exact ⟨hinp, houtcome, hstore, hsource, hout⟩
  · exact le_rfl

/-- The sparse-store update controller is append-only on its output tape. -/
theorem entryUpdateTM_isTransducer {n : ℕ} (tapes : EntryUpdateTapes n) :
    (entryUpdateTM tapes).IsTransducer :=
  entryUpdateTM_isTransducer_internal tapes

/-- Coarse all-prefix auxiliary-space envelope for one complete update. -/
theorem entryUpdateTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryUpdateTapes n) (store : Store) (address newValue : ℕ)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryUpdateTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryUpdateTM tapes).reachesIn time start current)
    (htime : time ≤ entryUpdateTime tapes store address newValue) :
    current.WithinAuxSpace inputLength
      (initialSpace + entryUpdateTime tapes store address newValue) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- A complete sparse update is charged by the entries actually traversed and
the query, replacement, and remaining-count widths reserved at each iteration.
This avoids the former product of entry count with a squared run-wide width. -/
theorem entryUpdateTime_le_encoded {n : ℕ}
    (tapes : EntryUpdateTapes n) (store : Store)
    (address newValue : ℕ) :
    entryUpdateTime tapes store address newValue ≤
      1000 * (encodedStoreLength store +
        (store.length + 1) *
          (bitlen address + bitlen newValue + bitlen store.length + 1) + 1) :=
  entryUpdateTime_le_encoded_internal tapes store address newValue

end Machine

end RegisterStore

end RAM

end Complexity
