/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.AddressEq.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryDecode.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Defs

/-!
# RAM sparse-entry matching — definitions

`entryMatchTM` is the concrete unit consumed by a bounded sparse-store scan.
It decodes one address/value entry and compares the decoded address with a
preserved canonical query. The result is appended to a dedicated work tape.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Nine pairwise-distinct work tapes used to decode and match one sparse
register-store entry. -/
structure EntryMatchTapes (n : ℕ) where
  /-- Tape assignment in the order source, address, value, address counter,
  address width, value counter, value width, query, and result. -/
  idx : Fin 9 → Fin n
  injective : Function.Injective idx

namespace EntryMatchTapes

/-- The seven decoder tapes contained in an entry-matching assignment. -/
def decode {n : ℕ} (tapes : EntryMatchTapes n) : EntryDecodeTapes n where
  idx := fun i => tapes.idx ⟨i, by omega⟩
  injective := by
    intro i j h
    have h' : (⟨i, by omega⟩ : Fin 9) = ⟨j, by omega⟩ :=
      tapes.injective h
    apply Fin.ext
    exact congrArg (fun k : Fin 9 => k.val) h'

/-- Encoded entry-stream source tape. -/
def source {n : ℕ} (tapes : EntryMatchTapes n) : Fin n := tapes.idx 0
/-- Decoded address scratch tape. -/
def address {n : ℕ} (tapes : EntryMatchTapes n) : Fin n := tapes.idx 1
/-- Decoded value scratch tape. -/
def value {n : ℕ} (tapes : EntryMatchTapes n) : Fin n := tapes.idx 2
/-- Binary loop counter used while decoding the address. -/
def addressCounter {n : ℕ} (tapes : EntryMatchTapes n) : Fin n := tapes.idx 3
/-- Preserved address payload-width tape. -/
def addressWidth {n : ℕ} (tapes : EntryMatchTapes n) : Fin n := tapes.idx 4
/-- Binary loop counter used while decoding the value. -/
def valueCounter {n : ℕ} (tapes : EntryMatchTapes n) : Fin n := tapes.idx 5
/-- Preserved value payload-width tape. -/
def valueWidth {n : ℕ} (tapes : EntryMatchTapes n) : Fin n := tapes.idx 6
/-- Canonical query-address tape. -/
def query {n : ℕ} (tapes : EntryMatchTapes n) : Fin n := tapes.idx 7
/-- Boolean match-result tape. -/
def result {n : ℕ} (tapes : EntryMatchTapes n) : Fin n := tapes.idx 8

theorem ne {n : ℕ} (tapes : EntryMatchTapes n) {i j : Fin 9} (h : i ≠ j) :
    tapes.idx i ≠ tapes.idx j :=
  fun hij => h (tapes.injective hij)

theorem binaryEqDistinct {n : ℕ} (tapes : EntryMatchTapes n) :
    TM.BinaryEqDistinct tapes.address tapes.query tapes.result := by
  exact ⟨tapes.ne (by decide), tapes.ne (by decide), tapes.ne (by decide)⟩

@[simp] theorem decode_source {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.decode.source = tapes.source := rfl

@[simp] theorem decode_address {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.decode.address = tapes.address := rfl

@[simp] theorem decode_value {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.decode.value = tapes.value := rfl

@[simp] theorem decode_addressCounter {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.decode.addressCounter = tapes.addressCounter := rfl

@[simp] theorem decode_addressWidth {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.decode.addressWidth = tapes.addressWidth := rfl

@[simp] theorem decode_valueCounter {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.decode.valueCounter = tapes.valueCounter := rfl

@[simp] theorem decode_valueWidth {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.decode.valueWidth = tapes.valueWidth := rfl

end EntryMatchTapes

/-- Decode one sparse entry with unary markers and compare its address with the
preserved query. -/
def entryMatchTM {n : ℕ} (tapes : EntryMatchTapes n) : TM n :=
  TM.seqTM (entryDecodeLinearTM tapes.decode)
    (decodedAddressEqTM tapes.address tapes.query tapes.result)

/-- Runtime bound for decoding and matching one sparse entry, including the
composition seam. -/
def entryMatchTime (entry : Entry) (queryBits : List Bool) : ℕ :=
  entryDecodeLinearTime entry.1 entry.2 + 1 +
    decodedAddressEqTime entry.1.bits queryBits

/-- Decode and compare one sparse entry, then rewind the one-bit result to its
canonical cell-one read position. -/
def entryMatchReadTM {n : ℕ} (tapes : EntryMatchTapes n) : TM n :=
  TM.seqTM (entryMatchTM tapes) (TM.rewindWorkTM tapes.result)

/-- Runtime bound for a readable one-entry match, including both composition
seams and the at-most-four-step rewind of the one-bit result. -/
def entryMatchReadTime (entry : Entry) (queryBits : List Bool) : ℕ :=
  entryMatchTime entry queryBits + 1 + 4

/-- Auditable endpoint contract for one readable sparse-entry match. The
decoded scratch remains available to a hit branch or can be cleared by a miss
branch; the result is parked at cell one for direct controller inspection. -/
structure ReadableEntryMatch {n : ℕ} (tapes : EntryMatchTapes n)
    (entry : Entry) (rest queryBits : List Bool)
    (initialWork finalWork : Fin n → Tape) : Prop where
  source : (finalWork tapes.source).HasBinarySuffix rest
  address : (finalWork tapes.address).HasBinaryContent entry.1.bits
  addressStart : (finalWork tapes.address).cells 0 = Γ.start
  value : (finalWork tapes.value).HasBinaryPrefix entry.2.bits
  valueStart : (finalWork tapes.value).cells 0 = Γ.start
  addressCounter : (finalWork tapes.addressCounter).HasBinaryPrefix
    (List.replicate (bitlen entry.1) true)
  addressCounterStart :
    (finalWork tapes.addressCounter).cells 0 = Γ.start
  addressWidth : (finalWork tapes.addressWidth).HasBinaryNat 0
  valueCounter : (finalWork tapes.valueCounter).HasBinaryPrefix
    (List.replicate (bitlen entry.2) true)
  valueCounterStart : (finalWork tapes.valueCounter).cells 0 = Γ.start
  valueWidth : (finalWork tapes.valueWidth).HasBinaryNat 0
  query : (finalWork tapes.query).HasBinaryContent queryBits
  queryStart : (finalWork tapes.query).cells 0 = Γ.start
  result : (finalWork tapes.result).HasBinaryString
    [decide (entry.1.bits = queryBits)]
  resultStart : (finalWork tapes.result).cells 0 = Γ.start
  parked : ∀ i, TM.Parked (finalWork i)
  headBound : ∀ i, (finalWork i).head ≤
    (initialWork i).head + entryMatchReadTime entry queryBits
  frame : ∀ i, i ≠ tapes.source → i ≠ tapes.address →
    i ≠ tapes.value → i ≠ tapes.addressCounter →
    i ≠ tapes.addressWidth → i ≠ tapes.valueCounter →
    i ≠ tapes.valueWidth → i ≠ tapes.query → i ≠ tapes.result →
    finalWork i = initialWork i

end Machine

end RegisterStore

end RAM

end Complexity
