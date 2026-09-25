/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordDecode.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Defs
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# RAM sparse-entry decoder — definitions

One sparse register entry contains two consecutive self-delimiting words: its
address and value. `entryDecodeTM` gives each word its own target, counter, and
width tapes so the two checked word decoders compose without a clearing phase.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Seven pairwise-distinct work tapes used by one sparse-entry decoder. -/
structure EntryDecodeTapes (n : ℕ) where
  /-- Tape assignment in the order source, address, value, address counter,
  address width, value counter, value width. -/
  idx : Fin 7 → Fin n
  injective : Function.Injective idx

namespace EntryDecodeTapes

/-- Encoded entry-stream source tape. -/
def source {n : ℕ} (tapes : EntryDecodeTapes n) : Fin n := tapes.idx 0
/-- Decoded address target tape. -/
def address {n : ℕ} (tapes : EntryDecodeTapes n) : Fin n := tapes.idx 1
/-- Decoded value target tape. -/
def value {n : ℕ} (tapes : EntryDecodeTapes n) : Fin n := tapes.idx 2
/-- Binary loop counter used while decoding the address. -/
def addressCounter {n : ℕ} (tapes : EntryDecodeTapes n) : Fin n := tapes.idx 3
/-- Preserved address payload-width tape. -/
def addressWidth {n : ℕ} (tapes : EntryDecodeTapes n) : Fin n := tapes.idx 4
/-- Binary loop counter used while decoding the value. -/
def valueCounter {n : ℕ} (tapes : EntryDecodeTapes n) : Fin n := tapes.idx 5
/-- Preserved value payload-width tape. -/
def valueWidth {n : ℕ} (tapes : EntryDecodeTapes n) : Fin n := tapes.idx 6

theorem ne {n : ℕ} (tapes : EntryDecodeTapes n) {i j : Fin 7} (h : i ≠ j) :
    tapes.idx i ≠ tapes.idx j :=
  fun hij => h (tapes.injective hij)

theorem addressDistinct {n : ℕ} (tapes : EntryDecodeTapes n) :
    PayloadLoopDistinct tapes.source tapes.address tapes.addressCounter
      tapes.addressWidth := by
  exact ⟨tapes.ne (by decide), tapes.ne (by decide), tapes.ne (by decide),
    tapes.ne (by decide), tapes.ne (by decide), tapes.ne (by decide)⟩

theorem valueDistinct {n : ℕ} (tapes : EntryDecodeTapes n) :
    PayloadLoopDistinct tapes.source tapes.value tapes.valueCounter
      tapes.valueWidth := by
  exact ⟨tapes.ne (by decide), tapes.ne (by decide), tapes.ne (by decide),
    tapes.ne (by decide), tapes.ne (by decide), tapes.ne (by decide)⟩

/-- Source, address target, and address marker are pairwise distinct. -/
theorem addressLinearDistinct {n : ℕ} (tapes : EntryDecodeTapes n) :
    LinearWordDistinct tapes.source tapes.address tapes.addressCounter := by
  exact ⟨tapes.ne (by decide), tapes.ne (by decide), tapes.ne (by decide)⟩

/-- Source, value target, and value marker are pairwise distinct. -/
theorem valueLinearDistinct {n : ℕ} (tapes : EntryDecodeTapes n) :
    LinearWordDistinct tapes.source tapes.value tapes.valueCounter := by
  exact ⟨tapes.ne (by decide), tapes.ne (by decide), tapes.ne (by decide)⟩

end EntryDecodeTapes

/-- Decode the address word and then the value word of one sparse entry. -/
def entryDecodeTM {n : ℕ} (tapes : EntryDecodeTapes n) : TM n :=
  TM.seqTM
    (wordDecodeTM tapes.source tapes.address tapes.addressCounter
      tapes.addressWidth)
    (wordDecodeTM tapes.source tapes.value tapes.valueCounter tapes.valueWidth)

/-- Exact runtime for decoding both words, including the composition seam. -/
def entryDecodeTime (address value : ℕ) : ℕ :=
  wordDecodeTime (bitlen address) + 1 + wordDecodeTime (bitlen value)

/-- Decode both entry words with unary markers. The former counter tapes serve
as address and value markers; the two width tapes are left untouched so this
machine can replace `entryDecodeTM` inside the established seven-tape ABI. -/
def entryDecodeLinearTM {n : ℕ} (tapes : EntryDecodeTapes n) : TM n :=
  TM.seqTM
    (wordDecodeLinearTM tapes.source tapes.address tapes.addressCounter)
    (wordDecodeLinearTM tapes.source tapes.value tapes.valueCounter)

/-- Exact runtime of the optimized two-word decoder, including its composition
seam. -/
def entryDecodeLinearTime (address value : ℕ) : ℕ :=
  wordDecodeLinearTime (bitlen address) + 1 +
    wordDecodeLinearTime (bitlen value)

end Machine

end RegisterStore

end RAM

end Complexity
