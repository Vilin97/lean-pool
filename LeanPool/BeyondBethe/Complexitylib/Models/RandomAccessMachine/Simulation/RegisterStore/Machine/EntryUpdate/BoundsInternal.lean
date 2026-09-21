/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMatch.Internal
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryPred
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany

/-!
# Encoded-length sparse-update bounds -- proof internals

The update controller reserves the slower of copy, replacement, and deletion
at each iteration. With unary-marker decoding, each such reservation is still
linear in the current entry and the instruction's query/replacement widths.
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

private theorem entryMatchReadTime_le_bitlen (entry : Entry)
    (queryBits : List Bool) :
    entryMatchReadTime entry queryBits ≤
      5 * bitlen entry.1 + 3 * bitlen entry.2 + queryBits.length + 18 := by
  have h := entryMatchReadTime_le_linear_internal entry queryBits
  simpa only [bitlen, Nat.size_eq_bits_len] using h

private theorem entryMissBits_length_le_bitlen {n : ℕ}
    (tapes : EntryMatchTapes n) (entry : Entry)
    (queryBits : List Bool) (i : Fin n) :
    (entryMissBits tapes entry queryBits i).length ≤
      bitlen entry.1 + bitlen entry.2 + 1 := by
  unfold entryMissBits
  split_ifs <;>
    (try simp only [List.length_nil, List.length_replicate,
      List.length_singleton, bitlen, Nat.size_eq_bits_len]) <;> omega

private theorem entryUpdatePostEmitHead_le_bitlen {n : ℕ}
    (tapes : EntryUpdateTapes n) (entry : Entry) (i : Fin n) :
    entryUpdatePostEmitHead tapes entry i ≤
      bitlen entry.1 + bitlen entry.2 + 1 := by
  unfold entryUpdatePostEmitHead
  split_ifs <;>
    simp only [bitlen, Nat.size_eq_bits_len] <;> omega

private theorem entryUpdateReadyCleanupTime_le_linear {n : ℕ}
    (tapes : EntryUpdateTapes n) (entry : Entry) (address : ℕ) :
    entryUpdateReadyCleanupTime tapes entry address ≤
      300 * (bitlen entry.1 + bitlen entry.2 + bitlen address + 1) := by
  let matchTime := entryMatchReadTime entry address.bits
  have hmatch : matchTime ≤
      5 * bitlen entry.1 + 3 * bitlen entry.2 + bitlen address + 18 := by
    dsimp only [matchTime]
    simpa only [bitlen, Nat.size_eq_bits_len] using
      entryMatchReadTime_le_bitlen entry address.bits
  have hreset := TM.resetBinaryWorkManyTime_le
    (entryMissTargets tapes.entry)
    (entryMissBits tapes.entry entry address.bits)
    (fun _ => 1 + matchTime) (1 + matchTime)
    (bitlen entry.1 + bitlen entry.2 + 1)
    (fun _ _ => le_rfl)
    (fun i _ => entryMissBits_length_le_bitlen tapes.entry entry address.bits i)
  have htargets : (entryMissTargets tapes.entry).length = 7 := by
    simp [entryMissTargets]
  rw [htargets] at hreset
  unfold entryUpdateReadyCleanupTime
  dsimp only [matchTime] at hmatch hreset ⊢
  omega

private theorem entryUpdatePostEmitCleanupTime_le_linear {n : ℕ}
    (tapes : EntryUpdateTapes n) (entry : Entry) (address : ℕ) :
    entryUpdatePostEmitCleanupTime tapes entry address ≤
      300 * (bitlen entry.1 + bitlen entry.2 + bitlen address + 1) := by
  let matchTime := entryMatchReadTime entry address.bits
  have hmatch : matchTime ≤
      5 * bitlen entry.1 + 3 * bitlen entry.2 + bitlen address + 18 := by
    dsimp only [matchTime]
    simpa only [bitlen, Nat.size_eq_bits_len] using
      entryMatchReadTime_le_bitlen entry address.bits
  have hreset := TM.resetBinaryWorkManyTime_le
    (entryMissTargets tapes.entry)
    (entryMissBits tapes.entry entry address.bits)
    (fun i => entryUpdatePostEmitHead tapes entry i + matchTime)
    (bitlen entry.1 + bitlen entry.2 + 1 + matchTime)
    (bitlen entry.1 + bitlen entry.2 + 1)
    (fun i _ => Nat.add_le_add_right
      (entryUpdatePostEmitHead_le_bitlen tapes entry i) matchTime)
    (fun i _ => entryMissBits_length_le_bitlen tapes.entry entry address.bits i)
  have htargets : (entryMissTargets tapes.entry).length = 7 := by
    simp [entryMissTargets]
  rw [htargets] at hreset
  unfold entryUpdatePostEmitCleanupTime
  dsimp only [matchTime] at hmatch hreset ⊢
  omega

private theorem rewindEntryEncodeTime_le_linear (entry : Entry)
    (addressHead valueHead : ℕ) :
    rewindEntryEncodeTime entry addressHead valueHead ≤
      addressHead + valueHead + 3 * bitlen entry.1 +
        3 * bitlen entry.2 + 21 := by
  unfold rewindEntryEncodeTime rewindWordEncodeTime wordEncodeTime
  simp only [bitlen, Nat.size_eq_bits_len]
  omega
private theorem entryUpdateBranchTime_le_linear {n : ℕ}
    (tapes : EntryUpdateTapes n) (entry : Entry)
    (address newValue total : ℕ) :
    entryUpdateBranchTime tapes entry address newValue total ≤
      500 * (bitlen entry.1 + bitlen entry.2 + bitlen address +
        bitlen newValue + bitlen total + 1) := by
  let matchTime := entryMatchReadTime entry address.bits
  have hmatch : matchTime ≤
      5 * bitlen entry.1 + 3 * bitlen entry.2 + bitlen address + 18 := by
    dsimp only [matchTime]
    simpa only [bitlen, Nat.size_eq_bits_len] using
      entryMatchReadTime_le_bitlen entry address.bits
  have hready := entryUpdateReadyCleanupTime_le_linear tapes entry address
  have hpost := entryUpdatePostEmitCleanupTime_le_linear tapes entry address
  have hmiss := rewindEntryEncodeTime_le_linear entry
    (1 + matchTime) (1 + matchTime)
  have hreplace := rewindEntryEncodeTime_le_linear (entry.1, newValue)
    (1 + matchTime) 1
  have hcount : entryUpdateCountTime total ≤ 2 * bitlen total + 2 := by
    unfold entryUpdateCountTime bitlen
    omega
  have hnewValue : newValue.bits.length = bitlen newValue := by
    exact Nat.size_eq_bits_len newValue
  unfold entryUpdateBranchTime entryUpdateMissTime entryUpdateReplaceTime
  dsimp only [matchTime] at hmatch hmiss hreplace ⊢
  rw [hnewValue]
  apply max_le
  · omega
  · apply max_le <;> omega

private theorem entryUpdateIterationTime_le_linear {n : ℕ}
    (tapes : EntryUpdateTapes n) (entry : Entry) (rest : Store)
    (address newValue total : ℕ) (hrest : rest.length + 1 ≤ total) :
    entryUpdateIterationTime tapes entry rest address newValue total ≤
      600 * (bitlen entry.1 + bitlen entry.2 + bitlen address +
        bitlen newValue + bitlen total + 1) := by
  have hmatch := entryMatchReadTime_le_bitlen entry address.bits
  have hbranch := entryUpdateBranchTime_le_linear tapes entry address
    newValue total
  have hpred := TM.binaryPredTime_le rest.length
  have hrestWidth : (rest.length + 1).size ≤ bitlen total := by
    unfold bitlen
    exact Nat.size_le_size hrest
  unfold entryUpdateIterationTime
  have haddressBits : address.bits.length = bitlen address :=
    Nat.size_eq_bits_len address
  rw [haddressBits] at hmatch
  omega

private theorem entryUpdateNilTime_le_linear {n : ℕ}
    (tapes : EntryUpdateTapes n) (address newValue total : ℕ) :
    entryUpdateLoopTime tapes address newValue total [] ≤
      100 * (bitlen address + bitlen newValue + bitlen total + 1) := by
  have hrewind := rewindEntryEncodeTime_le_linear (address, newValue) 1 1
  change rewindEntryEncodeTime (address, newValue) 1 1 ≤
    1 + 1 + 3 * bitlen address + 3 * bitlen newValue + 21 at hrewind
  have hcount : entryUpdateCountTime total ≤ 2 * bitlen total + 2 := by
    unfold entryUpdateCountTime bitlen
    omega
  unfold entryUpdateLoopTime entryAppendRestoreTime
  have haddress : address.bits.length = bitlen address :=
    Nat.size_eq_bits_len address
  have hnewValue : newValue.bits.length = bitlen newValue :=
    Nat.size_eq_bits_len newValue
  rw [haddress, hnewValue]
  omega

theorem entryUpdateTime_le_encoded_internal {n : ℕ}
    (tapes : EntryUpdateTapes n) (store : Store)
    (address newValue : ℕ) :
    entryUpdateTime tapes store address newValue ≤
      1000 * (encodedStoreLength store +
        (store.length + 1) *
          (bitlen address + bitlen newValue + bitlen store.length + 1) + 1) := by
  have hloop : ∀ remaining : Store, remaining.length ≤ store.length →
      entryUpdateLoopTime tapes address newValue store.length remaining ≤
        1000 * (encodedStoreLength remaining +
          (remaining.length + 1) *
            (bitlen address + bitlen newValue + bitlen store.length + 1) + 1) := by
    intro remaining hremaining
    induction remaining with
    | nil =>
        have hnil := entryUpdateNilTime_le_linear tapes address newValue
          store.length
        simp only [encodedStoreLength, List.flatMap_nil, List.length_nil,
          Nat.zero_add, Nat.one_mul]
        omega
    | cons entry rest ih =>
        have hrestLength : rest.length + 1 ≤ store.length := by
          simpa only [List.length_cons] using hremaining
        have hiteration := entryUpdateIterationTime_le_linear tapes entry rest
          address newValue store.length hrestLength
        have htail := ih (by omega)
        have hentryLength : (Entry.encode entry).length =
            2 * bitlen entry.1 + 2 * bitlen entry.2 + 2 :=
          Entry.encode_length entry
        unfold entryUpdateLoopTime
        have hencoded : encodedStoreLength (entry :: rest) =
            (Entry.encode entry).length + encodedStoreLength rest := by
          simp [encodedStoreLength]
        rw [hencoded, hentryLength]
        simp only [List.length_cons]
        have hmul : (rest.length + 1 + 1) *
              (bitlen address + bitlen newValue + bitlen store.length + 1) =
            (rest.length + 1) *
                (bitlen address + bitlen newValue + bitlen store.length + 1) +
              (bitlen address + bitlen newValue + bitlen store.length + 1) := by
          ring
        rw [hmul]
        omega
  unfold entryUpdateTime
  exact hloop store le_rfl

end Machine

end RegisterStore

end RAM

end Complexity
