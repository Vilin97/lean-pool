/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMatch.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany.Defs

/-!
# Sparse-entry miss cleanup — definitions

The miss branch after `entryMatchReadTM` resets the seven decoder/result
scratch tapes while preserving the consumed source cursor and query address.
This restores the exact invariant needed to inspect the next encoded entry.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

namespace EntryMatchTapes

/-- Embed the seven cleanup slots into the nine entry-match tapes. Slots zero
through five select decoder scratch `1..6`; slot six selects result tape `8`,
skipping the preserved query tape `7`. -/
def cleanupIdx {n : ℕ} (tapes : EntryMatchTapes n) (i : Fin 7) : Fin n :=
  tapes.idx ⟨if i.val = 6 then 8 else i.val + 1, by split <;> omega⟩

/-- The cleanup-slot embedding is injective. -/
theorem cleanupIdx_injective {n : ℕ} (tapes : EntryMatchTapes n) :
    Function.Injective tapes.cleanupIdx := by
  intro i j hij
  have hslot := tapes.injective hij
  apply Fin.ext
  have hval := congrArg Fin.val hslot
  change (if i.val = 6 then 8 else i.val + 1) =
    (if j.val = 6 then 8 else j.val + 1) at hval
  split at hval <;> split at hval <;> omega

@[simp] theorem cleanupIdx_zero {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.cleanupIdx 0 = tapes.address := rfl

@[simp] theorem cleanupIdx_one {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.cleanupIdx 1 = tapes.value := rfl

@[simp] theorem cleanupIdx_two {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.cleanupIdx 2 = tapes.addressCounter := rfl

@[simp] theorem cleanupIdx_three {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.cleanupIdx 3 = tapes.addressWidth := rfl

@[simp] theorem cleanupIdx_four {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.cleanupIdx 4 = tapes.valueCounter := rfl

@[simp] theorem cleanupIdx_five {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.cleanupIdx 5 = tapes.valueWidth := rfl

@[simp] theorem cleanupIdx_six {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.cleanupIdx 6 = tapes.result := rfl

end EntryMatchTapes

/-- Fixed, machine-level list of the seven scratch tapes reset on a miss. -/
def entryMissTargets {n : ℕ} (tapes : EntryMatchTapes n) : List (Fin n) :=
  List.ofFn tapes.cleanupIdx

/-- Canonical represented contents occupying each scratch tape at the readable
match endpoint. Values away from the seven scratch tapes are irrelevant. -/
def entryMissBits {n : ℕ} (tapes : EntryMatchTapes n)
    (entry : Entry) (queryBits : List Bool) (i : Fin n) : List Bool :=
  if i = tapes.address then entry.1.bits
  else if i = tapes.value then entry.2.bits
  else if i = tapes.addressCounter then List.replicate (bitlen entry.1) true
  else if i = tapes.addressWidth then []
  else if i = tapes.valueCounter then List.replicate (bitlen entry.2) true
  else if i = tapes.valueWidth then []
  else if i = tapes.result then [decide (entry.1.bits = queryBits)]
  else []

/-- Per-tape cursor bound inherited from the readable match contract. -/
def entryMissHeadBound {n : ℕ} (entry : Entry) (queryBits : List Bool)
    (initialWork : Fin n → Tape) (i : Fin n) : ℕ :=
  (initialWork i).head + entryMatchReadTime entry queryBits

/-- Rewind the preserved query, then reset all decoder/result scratch after a
failed entry comparison. -/
def entryMissCleanupTM {n : ℕ} (tapes : EntryMatchTapes n) : TM n :=
  TM.seqTM (TM.rewindWorkTM tapes.query)
    (TM.resetBinaryWorkManyTM (entryMissTargets tapes))

/-- Compositional miss-cleanup bound specialized to the readable endpoint. -/
def entryMissCleanupTime {n : ℕ} (tapes : EntryMatchTapes n)
    (entry : Entry) (queryBits : List Bool) (initialWork : Fin n → Tape) : ℕ :=
  entryMissHeadBound entry queryBits initialWork tapes.query + 2 + 1 +
    TM.resetBinaryWorkManyTime (entryMissBits tapes entry queryBits)
      (entryMissHeadBound entry queryBits initialWork) (entryMissTargets tapes)

/-- Loop invariant restored after a failed match: the source points at the
next entry, query is preserved, and all seven scratch tapes are canonical
blank/zero tapes ready for another decode. -/
structure EntryScanReady {n : ℕ} (tapes : EntryMatchTapes n)
    (remaining queryBits : List Bool) (initialWork finalWork : Fin n → Tape) :
    Prop where
  source : (finalWork tapes.source).HasBinarySuffix remaining
  address : (finalWork tapes.address).HasBinaryPrefix []
  addressStart : (finalWork tapes.address).cells 0 = Γ.start
  value : (finalWork tapes.value).HasBinaryPrefix []
  valueStart : (finalWork tapes.value).cells 0 = Γ.start
  addressCounter : (finalWork tapes.addressCounter).HasBinaryNat 0
  addressWidth : (finalWork tapes.addressWidth).HasBinaryNat 0
  valueCounter : (finalWork tapes.valueCounter).HasBinaryNat 0
  valueWidth : (finalWork tapes.valueWidth).HasBinaryNat 0
  query : (finalWork tapes.query).HasBinaryString queryBits
  queryStart : (finalWork tapes.query).cells 0 = Γ.start
  result : (finalWork tapes.result).HasBinaryPrefix []
  resultStart : (finalWork tapes.result).cells 0 = Γ.start
  parked : ∀ i, TM.Parked (finalWork i)
  frame : ∀ i, i ≠ tapes.source → i ≠ tapes.address →
    i ≠ tapes.value → i ≠ tapes.addressCounter →
    i ≠ tapes.addressWidth → i ≠ tapes.valueCounter →
    i ≠ tapes.valueWidth → i ≠ tapes.query → i ≠ tapes.result →
    finalWork i = initialWork i

end Machine

end RegisterStore

end RAM

end Complexity
