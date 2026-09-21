/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScanStep.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryPred.Defs

/-!
# Bounded sparse-entry scan — definitions

`entryScanTM` is a fixed machine, independent of the runtime store size. A
canonical binary remaining-count tape bounds the scan. Each iteration runs the
checked entry step; a hit leaves its readable result at `1` and halts, while a
miss restores scratch, decrements the count, and loops. Count zero halts with
the blank miss result.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Entry-match tapes plus a distinct canonical binary remaining-count tape. -/
structure EntryScanTapes (n : ℕ) where
  /-- The nine tapes used by one decode/compare iteration. -/
  entry : EntryMatchTapes n
  /-- Runtime remaining-entry count. -/
  count : Fin n
  /-- The count tape is distinct from every entry-step tape. -/
  count_ne : ∀ i, count ≠ entry.idx i

namespace EntryScanTapes

/-- The count tape is distinct from the encoded entry source. -/
theorem count_ne_source {n : ℕ} (tapes : EntryScanTapes n) :
    tapes.count ≠ tapes.entry.source := tapes.count_ne 0

/-- The count tape is distinct from the readable match-result tape. -/
theorem count_ne_result {n : ℕ} (tapes : EntryScanTapes n) :
    tapes.count ≠ tapes.entry.result := tapes.count_ne 8

end EntryScanTapes

/-- Finite controller phases outside the nested entry-step and predecessor
machines. -/
inductive EntryScanPhase where
  | test
  | done
  deriving DecidableEq

/-- `EntryScanPhase` has exactly two states. -/
instance instFintypeEntryScanPhase : Fintype EntryScanPhase where
  elems := {.test, .done}
  complete := fun phase => by cases phase <;> simp

/-- State type of the bounded sparse-entry controller. -/
abbrev EntryScanQ {n : ℕ} (tapes : EntryScanTapes n) :=
  EntryScanPhase ⊕ ((entryScanStepTM tapes.entry).Q ⊕ (TM.binaryPredTM tapes.count).Q)

/-- Fixed bounded scan controlled by a runtime canonical binary count.

The test phase halts on the empty encoding of zero. At positive count it runs
one entry step. A readable `1` result exits immediately with the decoded value;
the blank miss result enters binary predecessor and then loops. -/
def entryScanTM {n : ℕ} (tapes : EntryScanTapes n) : TM n where
  Q := EntryScanQ tapes
  qstart := .inl .test
  qhalt := .inl .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .inl .test =>
        if wHeads tapes.count = Γ.blank then
          TM.allReadBack (.inl .done) iHead wHeads oHead
        else
          TM.allReadBack (.inr (.inl (entryScanStepTM tapes.entry).qstart))
            iHead wHeads oHead
    | .inl .done => TM.allIdle (.inl .done) iHead wHeads oHead
    | .inr (.inl q) =>
        if q = (entryScanStepTM tapes.entry).qhalt then
          if wHeads tapes.entry.result = Γ.one then
            TM.allReadBack (.inl .done) iHead wHeads oHead
          else
            TM.allReadBack (.inr (.inr (TM.binaryPredTM tapes.count).qstart))
              iHead wHeads oHead
        else
          let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
            (entryScanStepTM tapes.entry).δ q iHead wHeads oHead
          (.inr (.inl q'), workWrites, outputWrite, inputDir, workDirs, outputDir)
    | .inr (.inr q) =>
        if q = (TM.binaryPredTM tapes.count).qhalt then
          TM.allReadBack (.inl .test) iHead wHeads oHead
        else
          let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
            (TM.binaryPredTM tapes.count).δ q iHead wHeads oHead
          (.inr (.inr q'), workWrites, outputWrite, inputDir, workDirs, outputDir)
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .inl .test =>
        dsimp only
        split <;> exact TM.rightOfStart_allReadBack iHead wHeads oHead
    | .inl .done => exact TM.rightOfStart_allIdle iHead wHeads oHead
    | .inr (.inl q) =>
        dsimp only
        split
        · split <;> exact TM.rightOfStart_allReadBack iHead wHeads oHead
        · exact (entryScanStepTM tapes.entry).δ_right_of_start q iHead wHeads oHead
    | .inr (.inr q) =>
        dsimp only
        split
        · exact TM.rightOfStart_allReadBack iHead wHeads oHead
        · exact (TM.binaryPredTM tapes.count).δ_right_of_start q iHead wHeads oHead

/-- Canonical all-blank work family used only to state the iteration bound;
every tape head is at cell one. -/
def entryScanCanonicalWork {n : ℕ} : Fin n → Tape :=
  Function.const (Fin n) TM.resetBinaryBlank

/-- Work-value-independent bound for one invariant-preserving entry step. -/
def entryScanOneTime {n : ℕ} (tapes : EntryScanTapes n)
    (entry : Entry) (queryBits : List Bool) : ℕ :=
  entryScanStepTime tapes.entry entry queryBits entryScanCanonicalWork

/-- Recursive bound for scanning a whole finite store. It reserves the miss
path at every entry, so it also bounds an earlier successful exit. -/
def entryScanTime {n : ℕ} (tapes : EntryScanTapes n)
    (queryBits : List Bool) : Store → ℕ
  | [] => 1
  | entry :: rest =>
      1 + entryScanOneTime tapes entry queryBits + 1 +
        TM.binaryPredTime rest.length + 1 + entryScanTime tapes queryBits rest

/-- Exact preservation predicate outside the ten tapes owned by the bounded
entry scanner. -/
def EntryScanFrame {n : ℕ} (tapes : EntryScanTapes n)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  ∀ i, i ≠ tapes.count → i ≠ tapes.entry.source →
    i ≠ tapes.entry.address → i ≠ tapes.entry.value →
    i ≠ tapes.entry.addressCounter → i ≠ tapes.entry.addressWidth →
    i ≠ tapes.entry.valueCounter → i ≠ tapes.entry.valueWidth →
    i ≠ tapes.entry.query → i ≠ tapes.entry.result →
    finalWork i = initialWork i

/-- Successful bounded scan result. The decomposition records the first
matching entry, the decoded value remains readable, and the runtime count is
the number of entries beginning at that hit. -/
structure EntryScanFound {n : ℕ} (tapes : EntryScanTapes n)
    (store scanned : Store) (matched : Entry) (rest : Store)
    (queryBits : List Bool) (initialWork hitBase finalWork : Fin n → Tape) :
    Prop where
  store_eq : store = scanned ++ matched :: rest
  prefixMiss : ∀ prior ∈ scanned, prior.1.bits ≠ queryBits
  hit : EntryScanHit tapes.entry matched (rest.flatMap Entry.encode) queryBits
    hitBase finalWork
  count : (finalWork tapes.count).HasBinaryNat (rest.length + 1)
  frame : EntryScanFrame tapes initialWork finalWork

/-- Unsuccessful bounded scan result. Every address is certified different,
the source and scratch invariant is exhausted, and the runtime count is zero. -/
structure EntryScanMiss {n : ℕ} (tapes : EntryScanTapes n)
    (store : Store) (queryBits : List Bool)
    (initialWork readyBase finalWork : Fin n → Tape) : Prop where
  notFound : ∀ entry ∈ store, entry.1.bits ≠ queryBits
  ready : EntryScanReady tapes.entry [] queryBits readyBase finalWork
  count : (finalWork tapes.count).HasBinaryNat 0
  frame : EntryScanFrame tapes initialWork finalWork

/-- Complete semantic outcome of a bounded sparse-entry scan. -/
def EntryScanOutcome {n : ℕ} (tapes : EntryScanTapes n)
    (store : Store) (queryBits : List Bool)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  (∃ scanned matched rest hitBase,
    EntryScanFound tapes store scanned matched rest queryBits initialWork
      hitBase finalWork) ∨
    ∃ readyBase,
      EntryScanMiss tapes store queryBits initialWork readyBase finalWork

end Machine

end RegisterStore

end RAM

end Complexity
