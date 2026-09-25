/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryLookup.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryLookup.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Source

/-!
# Sparse register lookup
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- A bounded lookup advances the encoded source cursor without modifying its
cells. -/
theorem entryLookupTM_source_readOnly {n : ℕ} (tapes : EntryScanTapes n) :
    (entryLookupTM tapes).WorkReadOnly tapes.entry.source :=
  entryScanTM_source_readOnly_internal tapes

/-- Scan a runtime-sized encoded sparse store and leave exactly
`RegisterStore.read store address` on the decoded-value tape. -/
theorem entryLookupTM_hoareTime_frame {n : ℕ}
    (tapes : EntryScanTapes n) (store : Store) (address : ℕ)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hready : EntryScanReady tapes.entry (store.flatMap Entry.encode)
      address.bits initialWork initialWork)
    (hcount : (initialWork tapes.count).HasBinaryNat store.length)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryLookupTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupResult tapes store address initialWork work ∧
        out = out₀)
      (entryLookupTime tapes address store) :=
  entryLookupTM_hoareTime_frame_internal tapes store address initialWork
    inp₀ out₀ hready hcount hinput houtput

/-- Framed lookup with explicit preservation of the complete encoded source
cell function. -/
theorem entryLookupTM_hoareTime_frame_source {n : ℕ}
    (tapes : EntryScanTapes n) (store : Store) (address : ℕ)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hready : EntryScanReady tapes.entry (store.flatMap Entry.encode)
      address.bits initialWork initialWork)
    (hcount : (initialWork tapes.count).HasBinaryNat store.length)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryLookupTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupResult tapes store address initialWork work ∧
        (work tapes.entry.source).cells =
          (initialWork tapes.entry.source).cells ∧
        (∀ i, (work i).head ≤ (initialWork i).head +
          entryLookupTime tapes address store) ∧
        out = out₀)
      (entryLookupTime tapes address store) := by
  have hlookup := entryLookupTM_hoareTime_frame tapes store address
    initialWork inp₀ out₀ hready hcount hinput houtput
  intro inp work out hpre
  obtain ⟨final, time, htime, hreach, hhalt, hinp, hresult, hout⟩ :=
    hlookup inp work out hpre
  have hstartWork : work = initialWork := hpre.2.1
  have hnostart : ∀ j, 1 ≤ j →
      (work tapes.entry.source).cells j ≠ Γ.start := by
    rw [hstartWork]
    exact hready.source.2.2.2
  have hcells := (entryLookupTM_source_readOnly tapes).cells_eq_of_reachesIn
    hreach hnostart
  have hheads := TM.head_le_start_add_of_reachesIn
    (entryLookupTM tapes) hreach
  have hworkHeads : ∀ i, (final.work i).head ≤
      (initialWork i).head + entryLookupTime tapes address store := by
    intro i
    have hi := hheads.2.2 i
    rw [hstartWork] at hi
    dsimp only at hi
    omega
  exact ⟨final, time, htime, hreach, hhalt, hinp, hresult,
    hcells.trans (congrArg (fun w => (w tapes.entry.source).cells)
      hstartWork), hworkHeads, hout⟩

/-- Sparse lookup preserves one-way output safety. -/
theorem entryLookupTM_isTransducer {n : ℕ} (tapes : EntryScanTapes n) :
    (entryLookupTM tapes).IsTransducer :=
  entryScanTM_isTransducer tapes

/-- Sparse lookup inherits the scanner's all-prefix auxiliary-space envelope. -/
theorem entryLookupTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryScanTapes n) (store : Store) (address : ℕ)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryLookupTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryLookupTM tapes).reachesIn time start current)
    (htime : time ≤ entryLookupTime tapes address store) :
    current.WithinAuxSpace inputLength
      (initialSpace + entryLookupTime tapes address store) :=
  entryScanTM_prefix_withinAuxSpace tapes store address.bits inputLength
    initialSpace time start current hinitial hreach htime

end Machine

end RegisterStore

end RAM

end Complexity
