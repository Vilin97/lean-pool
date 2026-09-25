/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryAppend.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMissCopy.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryPred.Defs

/-!
# Tape assignment and endpoint contracts for sparse-store updates

The thirteen distinct tape roles, their replacement view, and the complete final
frame and scanner contract used by the update controller.
-/

@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Thirteen pairwise-distinct tapes used by encoded sparse-store update. -/
structure EntryUpdateTapes (n : ℕ) where
  /-- Assignment order: nine entry-match tapes, remaining count, replacement
  value, found flag, and output count. -/
  idx : Fin 13 → Fin n
  /-- The complete assignment is injective. -/
  injective : Function.Injective idx

namespace EntryUpdateTapes

/-- The nine-tape decode-and-match assignment. -/
def entry {n : ℕ} (tapes : EntryUpdateTapes n) : EntryMatchTapes n where
  idx := fun i => tapes.idx ⟨i, by omega⟩
  injective := by
    intro i j hij
    have h : (⟨i, by omega⟩ : Fin 13) = ⟨j, by omega⟩ :=
      tapes.injective hij
    apply Fin.ext
    exact congrArg (fun k : Fin 13 => k.val) h

/-- Runtime number of old entries still unread. -/
def remaining {n : ℕ} (tapes : EntryUpdateTapes n) : Fin n := tapes.idx 9

/-- Canonical source containing the requested new value. -/
def replacement {n : ℕ} (tapes : EntryUpdateTapes n) : Fin n := tapes.idx 10

/-- One-bit flag recording whether a matching old address has been seen. -/
def found {n : ℕ} (tapes : EntryUpdateTapes n) : Fin n := tapes.idx 11

/-- Canonical count of entries emitted by the completed update. -/
def resultCount {n : ℕ} (tapes : EntryUpdateTapes n) : Fin n := tapes.idx 12

/-- Distinct indices in the thirteen-tape assignment remain distinct. -/
theorem ne {n : ℕ} (tapes : EntryUpdateTapes n) {i j : Fin 13} (h : i ≠ j) :
    tapes.idx i ≠ tapes.idx j :=
  fun hij => h (tapes.injective hij)

/-- Replacement-emission view of the update assignment. -/
def replace {n : ℕ} (tapes : EntryUpdateTapes n) : EntryReplaceTapes n where
  entry := tapes.entry
  replacement := tapes.replacement
  replacement_ne := by
    intro i h
    change tapes.idx 10 = tapes.idx ⟨i.val, by omega⟩ at h
    have h' : (10 : Fin 13) = ⟨i.val, by omega⟩ := tapes.injective h
    have hv : (10 : ℕ) = i.val :=
      congrArg (fun k : Fin 13 => k.val) h'
    omega

@[simp] theorem replace_entry {n : ℕ} (tapes : EntryUpdateTapes n) :
    tapes.replace.entry = tapes.entry := rfl

@[simp] theorem replace_replacement {n : ℕ} (tapes : EntryUpdateTapes n) :
    tapes.replace.replacement = tapes.replacement := rfl

end EntryUpdateTapes

/-- Exact preservation predicate outside the thirteen tapes owned by update. -/
def EntryUpdateFrame {n : ℕ} (tapes : EntryUpdateTapes n)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  ∀ i, (∀ slot, i ≠ tapes.idx slot) → finalWork i = initialWork i

/-- Auditable final work-tape contract for one encoded sparse-store update. -/
structure EntryUpdateOutcome {n : ℕ} (tapes : EntryUpdateTapes n)
    (store : Store) (address newValue : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop where
  /-- The encoded old store has been consumed and all entry scratch is reset. -/
  ready : EntryScanReady tapes.entry [] address.bits finalWork finalWork
  /-- The external replacement source is restored literally. -/
  replacement : finalWork tapes.replacement = initialWork tapes.replacement
  /-- The runtime old-entry counter is exhausted. -/
  remaining : (finalWork tapes.remaining).HasBinaryNat 0
  /-- The flag records whether the old store contained the updated address. -/
  found : (finalWork tapes.found).HasBinaryNat
    (if address ∈ store.map Prod.fst then 1 else 0)
  /-- The result counter is the exact cardinality of the pure sparse write. -/
  resultCount : (finalWork tapes.resultCount).HasBinaryNat
    (RegisterStore.write store address newValue).length
  /-- Every work tape outside the fixed assignment is unchanged. -/
  frame : EntryUpdateFrame tapes initialWork finalWork


end Machine

end RegisterStore

end RAM

end Complexity
