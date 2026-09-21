/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryLookup.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScan
public import Mathlib.Data.Nat.Bitwise

/-!
# Sparse register lookup — proof internals
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem nat_eq_of_bits_eq {a b : ℕ} (h : a.bits = b.bits) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth, h]

private theorem read_eq_matched
    (scanned : Store) (matched : Entry) (rest : Store) (address : ℕ)
    (hmiss : ∀ prior ∈ scanned, prior.1.bits ≠ address.bits)
    (hmatch : matched.1.bits = address.bits) :
    RegisterStore.read (scanned ++ matched :: rest) address = matched.2 := by
  induction scanned with
  | nil =>
      simp [RegisterStore.read, nat_eq_of_bits_eq hmatch]
  | cons prior scanned ih =>
      have hprior : prior.1 ≠ address := by
        intro heq
        exact hmiss prior (by simp) (congrArg Nat.bits heq)
      simp only [List.cons_append, RegisterStore.read]
      rw [ite_eq_right (Ne.symm hprior)]
      apply ih
      intro candidate hcandidate
      exact hmiss candidate (by simp [hcandidate])

private theorem read_eq_zero
    (store : Store) (address : ℕ)
    (hmiss : ∀ entry ∈ store, entry.1.bits ≠ address.bits) :
    RegisterStore.read store address = 0 := by
  induction store with
  | nil => rfl
  | cons entry rest ih =>
      have hentry : entry.1 ≠ address := by
        intro heq
        exact hmiss entry (by simp) (congrArg Nat.bits heq)
      simp only [RegisterStore.read]
      rw [ite_eq_right (Ne.symm hentry)]
      exact ih (fun candidate hcandidate =>
        hmiss candidate (by simp [hcandidate]))

private theorem outcome_to_lookup
    (tapes : EntryScanTapes n) (store : Store) (address : ℕ)
    (initialWork finalWork : Fin n → Tape)
    (houtcome :
      EntryScanOutcome tapes store address.bits initialWork finalWork) :
    EntryLookupResult tapes store address initialWork finalWork := by
  have houtcome' := houtcome
  rcases houtcome with hfound | hmiss
  · rcases hfound with ⟨scanned, matched, rest, _, hfound⟩
    have hread : RegisterStore.read store address = matched.2 := by
      rw [hfound.store_eq]
      exact read_eq_matched scanned matched rest address hfound.prefixMiss
        hfound.hit.addressEq
    exact ⟨by simpa [hread] using hfound.hit.value,
      hfound.hit.valueStart, ⟨rest.length + 1, by
        rw [hfound.store_eq]
        simp, hfound.count⟩, hfound.hit.parked, hfound.frame, houtcome'⟩
  · rcases hmiss with ⟨_, hmiss⟩
    have hread : RegisterStore.read store address = 0 :=
      read_eq_zero store address hmiss.notFound
    exact ⟨by simpa [hread] using hmiss.ready.value,
      hmiss.ready.valueStart, ⟨0, Nat.zero_le _, hmiss.count⟩,
      hmiss.ready.parked, hmiss.frame, houtcome'⟩

theorem entryLookupTM_hoareTime_frame_internal
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
      (entryLookupTime tapes address store) := by
  exact (entryScanTM_hoareTime_frame tapes store address.bits initialWork
    inp₀ out₀ hready hcount hinput houtput).consequence
      (fun _ _ _ h => h)
      (fun _ _ _ h => ⟨h.1, outcome_to_lookup tapes store address
        initialWork _ h.2.1, h.2.2⟩)
      le_rfl

end Machine

end RegisterStore

end RAM

end Complexity
