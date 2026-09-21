/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryAppend.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMissCopy.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryPred.Defs

/-!
# Bounded encoded sparse-store update — controller definitions

The fixed controller owns thirteen pairwise-distinct work tapes. It scans a
runtime-counted entry stream, copying misses, replacing or deleting a hit, and
appending a fresh nonzero entry only when the old count is exhausted without a
match. A second count tape tracks the output-store cardinality.
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

/-- Canonical head profile after an old decoded entry has been emitted. -/
def entryUpdatePostEmitHead {n : ℕ} (tapes : EntryUpdateTapes n)
    (entry : Entry) (i : Fin n) : ℕ :=
  if i = tapes.entry.address then entry.1.bits.length + 1
  else if i = tapes.entry.value then entry.2.bits.length + 1
  else if i = tapes.entry.addressCounter then bitlen entry.1 + 1
  else if i = tapes.entry.valueCounter then bitlen entry.2 + 1
  else 1

/-- Work-independent cleanup bound when deletion emits no entry. -/
def entryUpdateReadyCleanupTime {n : ℕ} (tapes : EntryUpdateTapes n)
    (entry : Entry) (address : ℕ) : ℕ :=
  let matchTime := entryMatchReadTime entry address.bits
  1 + matchTime + 2 + 1 +
    TM.resetBinaryWorkManyTime
      (entryMissBits tapes.entry entry address.bits)
      (fun _ => 1 + matchTime) (entryMissTargets tapes.entry)

/-- Work-independent cleanup bound after miss-copy or replacement emission. -/
def entryUpdatePostEmitCleanupTime {n : ℕ}
    (tapes : EntryUpdateTapes n) (entry : Entry) (address : ℕ) : ℕ :=
  let matchTime := entryMatchReadTime entry address.bits
  1 + 2 * matchTime + 2 + 1 +
    TM.resetBinaryWorkManyTime
      (entryMissBits tapes.entry entry address.bits)
      (fun i => entryUpdatePostEmitHead tapes entry i + matchTime)
      (entryMissTargets tapes.entry)

/-- Fixed bound for copying one unmatched entry and restoring scratch. -/
def entryUpdateMissTime {n : ℕ} (tapes : EntryUpdateTapes n)
    (entry : Entry) (address : ℕ) : ℕ :=
  let matchTime := entryMatchReadTime entry address.bits
  rewindEntryEncodeTime entry (1 + matchTime) (1 + matchTime) + 1 +
    entryUpdatePostEmitCleanupTime tapes entry address

/-- Fixed bound for emitting a replacement and restoring scratch. -/
def entryUpdateReplaceTime {n : ℕ} (tapes : EntryUpdateTapes n)
    (entry : Entry) (address newValue : ℕ) : ℕ :=
  let matchTime := entryMatchReadTime entry address.bits
  rewindEntryEncodeTime (entry.1, newValue) (1 + matchTime) 1 + 1 +
    (newValue.bits.length + 1 + 2 + 1 +
      entryUpdatePostEmitCleanupTime tapes entry address)

/-- Uniform binary counter-update budget below the initial store size. -/
def entryUpdateCountTime (total : ℕ) : ℕ :=
  2 * total.size + 2

/-- Maximum controller branch cost after one readable comparison. -/
def entryUpdateBranchTime {n : ℕ} (tapes : EntryUpdateTapes n)
    (entry : Entry) (address newValue total : ℕ) : ℕ :=
  max (entryUpdateMissTime tapes entry address + 1)
    (max (entryUpdateReplaceTime tapes entry address newValue + 1)
      (entryUpdateReadyCleanupTime tapes entry address + 1 +
        entryUpdateCountTime total + 1))

/-- Fixed cost of one positive-count iteration, excluding the recursive tail. -/
def entryUpdateIterationTime {n : ℕ} (tapes : EntryUpdateTapes n)
    (entry : Entry) (rest : Store) (address newValue total : ℕ) : ℕ :=
  1 + entryMatchReadTime entry address.bits + 1 +
    entryUpdateBranchTime tapes entry address newValue total +
    TM.binaryPredTime rest.length + 1

/-- Recursive fixed bound for updating a remaining sparse-store suffix. -/
def entryUpdateLoopTime {n : ℕ} (tapes : EntryUpdateTapes n)
    (address newValue total : ℕ) : Store → ℕ
  | [] =>
      1 + entryAppendRestoreTime address newValue + 1 +
        entryUpdateCountTime total + 1
  | entry :: rest =>
      entryUpdateIterationTime tapes entry rest address newValue total +
        entryUpdateLoopTime tapes address newValue total rest

/-- Public runtime bound for one complete encoded sparse-store update. -/
def entryUpdateTime {n : ℕ} (tapes : EntryUpdateTapes n)
    (store : Store) (address newValue : ℕ) : ℕ :=
  entryUpdateLoopTime tapes address newValue store.length store

/-- Controller states, including each checked nested machine. -/
inductive EntryUpdateQ {n : ℕ} (tapes : EntryUpdateTapes n) where
  | test
  | matching : (entryMatchReadTM tapes.entry).Q → EntryUpdateQ tapes
  | miss : (entryMissCopyTM tapes.entry).Q → EntryUpdateQ tapes
  | delete : (entryMissCleanupTM tapes.entry).Q → EntryUpdateQ tapes
  | replace : (entryReplaceCleanupTM tapes.replace).Q → EntryUpdateQ tapes
  | append : (entryAppendRestoreTM tapes.replace).Q → EntryUpdateQ tapes
  | remaining : (TM.binaryPredTM tapes.remaining).Q → EntryUpdateQ tapes
  | deleteCount : (TM.binaryPredTM tapes.resultCount).Q → EntryUpdateQ tapes
  | appendCount : (TM.binarySuccTM tapes.resultCount).Q → EntryUpdateQ tapes
  | done
  deriving DecidableEq

/-- The update controller has finitely many states because every nested
machine state type is finite. -/
instance instFintypeEntryUpdateQ {n : ℕ}
    (tapes : EntryUpdateTapes n) : Fintype (EntryUpdateQ tapes) where
  elems :=
    {.test, .done} ∪
    (Finset.univ.image EntryUpdateQ.matching) ∪
    (Finset.univ.image EntryUpdateQ.miss) ∪
    (Finset.univ.image EntryUpdateQ.delete) ∪
    (Finset.univ.image EntryUpdateQ.replace) ∪
    (Finset.univ.image EntryUpdateQ.append) ∪
    (Finset.univ.image EntryUpdateQ.remaining) ∪
    (Finset.univ.image EntryUpdateQ.deleteCount) ∪
    (Finset.univ.image EntryUpdateQ.appendCount)
  complete := by
    intro q
    cases q <;> simp

/-- Fixed runtime-counted update controller. The old remaining count reaches
zero on every complete scan; the result count is decremented only for deletion
and incremented only for absent-address append. -/
def entryUpdateTM {n : ℕ} (tapes : EntryUpdateTapes n) : TM n where
  Q := EntryUpdateQ tapes
  qstart := .test
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .test =>
        if wHeads tapes.remaining = Γ.blank then
          if wHeads tapes.found = Γ.one then
            TM.allReadBack .done iHead wHeads oHead
          else if wHeads tapes.replacement = Γ.blank then
            TM.allReadBack .done iHead wHeads oHead
          else
            TM.allReadBack
              (.append (entryAppendRestoreTM tapes.replace).qstart)
              iHead wHeads oHead
        else
          TM.allReadBack (.matching (entryMatchReadTM tapes.entry).qstart)
            iHead wHeads oHead
    | .matching q =>
        if q = (entryMatchReadTM tapes.entry).qhalt then
          if wHeads tapes.entry.result = Γ.one then
            let next :=
              if wHeads tapes.replacement = Γ.blank then
                .delete (entryMissCleanupTM tapes.entry).qstart
              else
                .replace (entryReplaceCleanupTM tapes.replace).qstart
            (next,
              fun i => if i = tapes.found then Γw.one
                else TM.readBackWrite (wHeads i),
              TM.readBackWrite oHead, TM.idleDir iHead,
              fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
          else
            TM.allReadBack (.miss (entryMissCopyTM tapes.entry).qstart)
              iHead wHeads oHead
        else
          let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
            (entryMatchReadTM tapes.entry).δ q iHead wHeads oHead
          (.matching q', workWrites, outputWrite, inputDir, workDirs, outputDir)
    | .miss q =>
        if q = (entryMissCopyTM tapes.entry).qhalt then
          TM.allReadBack (.remaining (TM.binaryPredTM tapes.remaining).qstart)
            iHead wHeads oHead
        else
          let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
            (entryMissCopyTM tapes.entry).δ q iHead wHeads oHead
          (.miss q', workWrites, outputWrite, inputDir, workDirs, outputDir)
    | .delete q =>
        if q = (entryMissCleanupTM tapes.entry).qhalt then
          TM.allReadBack
            (.deleteCount (TM.binaryPredTM tapes.resultCount).qstart)
            iHead wHeads oHead
        else
          let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
            (entryMissCleanupTM tapes.entry).δ q iHead wHeads oHead
          (.delete q', workWrites, outputWrite, inputDir, workDirs, outputDir)
    | .replace q =>
        if q = (entryReplaceCleanupTM tapes.replace).qhalt then
          TM.allReadBack (.remaining (TM.binaryPredTM tapes.remaining).qstart)
            iHead wHeads oHead
        else
          let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
            (entryReplaceCleanupTM tapes.replace).δ q iHead wHeads oHead
          (.replace q', workWrites, outputWrite, inputDir, workDirs, outputDir)
    | .append q =>
        if q = (entryAppendRestoreTM tapes.replace).qhalt then
          TM.allReadBack
            (.appendCount (TM.binarySuccTM tapes.resultCount).qstart)
            iHead wHeads oHead
        else
          let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
            (entryAppendRestoreTM tapes.replace).δ q iHead wHeads oHead
          (.append q', workWrites, outputWrite, inputDir, workDirs, outputDir)
    | .remaining q =>
        if q = (TM.binaryPredTM tapes.remaining).qhalt then
          TM.allReadBack .test iHead wHeads oHead
        else
          let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
            (TM.binaryPredTM tapes.remaining).δ q iHead wHeads oHead
          (.remaining q', workWrites, outputWrite, inputDir, workDirs, outputDir)
    | .deleteCount q =>
        if q = (TM.binaryPredTM tapes.resultCount).qhalt then
          TM.allReadBack (.remaining (TM.binaryPredTM tapes.remaining).qstart)
            iHead wHeads oHead
        else
          let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
            (TM.binaryPredTM tapes.resultCount).δ q iHead wHeads oHead
          (.deleteCount q', workWrites, outputWrite, inputDir, workDirs, outputDir)
    | .appendCount q =>
        if q = (TM.binarySuccTM tapes.resultCount).qhalt then
          TM.allReadBack .done iHead wHeads oHead
        else
          let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
            (TM.binarySuccTM tapes.resultCount).δ q iHead wHeads oHead
          (.appendCount q', workWrites, outputWrite, inputDir, workDirs, outputDir)
    | .done => TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    cases state with
    | test =>
        dsimp only
        split
        · split
          · exact TM.rightOfStart_allReadBack iHead wHeads oHead
          · split <;> exact TM.rightOfStart_allReadBack iHead wHeads oHead
        · exact TM.rightOfStart_allReadBack iHead wHeads oHead
    | matching q =>
        dsimp only
        split
        · split
          · exact TM.rightOfStart_allReadBack iHead wHeads oHead
          · exact TM.rightOfStart_allReadBack iHead wHeads oHead
        · exact (entryMatchReadTM tapes.entry).δ_right_of_start
            q iHead wHeads oHead
    | miss q =>
        dsimp only
        split
        · exact TM.rightOfStart_allReadBack iHead wHeads oHead
        · exact (entryMissCopyTM tapes.entry).δ_right_of_start
            q iHead wHeads oHead
    | delete q =>
        dsimp only
        split
        · exact TM.rightOfStart_allReadBack iHead wHeads oHead
        · exact (entryMissCleanupTM tapes.entry).δ_right_of_start
            q iHead wHeads oHead
    | replace q =>
        dsimp only
        split
        · exact TM.rightOfStart_allReadBack iHead wHeads oHead
        · exact (entryReplaceCleanupTM tapes.replace).δ_right_of_start
            q iHead wHeads oHead
    | append q =>
        dsimp only
        split
        · exact TM.rightOfStart_allReadBack iHead wHeads oHead
        · exact (entryAppendRestoreTM tapes.replace).δ_right_of_start
            q iHead wHeads oHead
    | remaining q =>
        dsimp only
        split
        · exact TM.rightOfStart_allReadBack iHead wHeads oHead
        · exact (TM.binaryPredTM tapes.remaining).δ_right_of_start
            q iHead wHeads oHead
    | deleteCount q =>
        dsimp only
        split
        · exact TM.rightOfStart_allReadBack iHead wHeads oHead
        · exact (TM.binaryPredTM tapes.resultCount).δ_right_of_start
            q iHead wHeads oHead
    | appendCount q =>
        dsimp only
        split
        · exact TM.rightOfStart_allReadBack iHead wHeads oHead
        · exact (TM.binarySuccTM tapes.resultCount).δ_right_of_start
            q iHead wHeads oHead
    | done => exact TM.rightOfStart_allIdle iHead wHeads oHead

end Machine

end RegisterStore

end RAM

end Complexity
