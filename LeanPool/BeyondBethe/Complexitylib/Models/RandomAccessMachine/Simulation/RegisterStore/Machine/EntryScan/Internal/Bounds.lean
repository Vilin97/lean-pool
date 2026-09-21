/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore
import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMatch.Internal
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScan.Defs
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryPred
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany

/-!
# Encoded-length bounds for sparse-entry scans -- proof internals

The optimized word decoder leaves unary width markers. This makes decoding,
matching, and cleanup linear in the two words actually traversed. The final
scan theorem retains only the separate binary remaining-count charge.
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

private theorem entryMissBits_length_le_sum {n : ℕ}
    (tapes : EntryMatchTapes n) (entry : Entry)
    (queryBits : List Bool) (i : Fin n) :
    (entryMissBits tapes entry queryBits i).length ≤
      bitlen entry.1 + bitlen entry.2 + 1 := by
  unfold entryMissBits
  split_ifs <;>
    (try simp only [List.length_nil, List.length_replicate,
      List.length_singleton, bitlen, Nat.size_eq_bits_len]) <;> omega

private theorem entryMissCleanupTime_canonical_le_linear {n : ℕ}
    (tapes : EntryMatchTapes n) (entry : Entry)
    (queryBits : List Bool) :
    entryMissCleanupTime tapes entry queryBits
        (entryScanCanonicalWork (n := n)) ≤
      300 * (entry.1.bits.length + entry.2.bits.length +
        queryBits.length + 1) := by
  let matchTime := entryMatchReadTime entry queryBits
  have hmatch : matchTime ≤
      5 * entry.1.bits.length + 3 * entry.2.bits.length +
        queryBits.length + 18 :=
    entryMatchReadTime_le_linear_internal entry queryBits
  have hreset := TM.resetBinaryWorkManyTime_le
    (entryMissTargets tapes) (entryMissBits tapes entry queryBits)
    (entryMissHeadBound entry queryBits (entryScanCanonicalWork (n := n)))
    (1 + matchTime) (bitlen entry.1 + bitlen entry.2 + 1)
    (fun i _ => by
      unfold entryMissHeadBound entryScanCanonicalWork
      simp [TM.resetBinaryBlank, Tape.move, Tape.init]
      dsimp only [matchTime]
      exact le_rfl)
    (fun i _ => entryMissBits_length_le_sum tapes entry queryBits i)
  have htargets : (entryMissTargets tapes).length = 7 := by
    simp [entryMissTargets]
  rw [htargets] at hreset
  have hreset' :
      TM.resetBinaryWorkManyTime (entryMissBits tapes entry queryBits)
          (fun _ => 1 + matchTime) (entryMissTargets tapes) ≤
        7 * (1 + matchTime +
          2 * (bitlen entry.1 + bitlen entry.2 + 1) + 9) + 1 := by
    simpa [entryMissHeadBound, entryScanCanonicalWork,
      TM.resetBinaryBlank, Tape.move, Tape.init] using hreset
  unfold entryMissCleanupTime entryMissHeadBound entryScanCanonicalWork
  simp only [Function.const_apply, TM.resetBinaryBlank, Tape.move, Tape.init,
    Nat.zero_add]
  dsimp only [matchTime] at hmatch hreset'
  have haddressWidth : bitlen entry.1 = entry.1.bits.length := by
    exact (Nat.size_eq_bits_len entry.1).symm
  have hvalueWidth : bitlen entry.2 = entry.2.bits.length := by
    exact (Nat.size_eq_bits_len entry.2).symm
  rw [haddressWidth, hvalueWidth] at hreset'
  omega

theorem entryScanOneTime_le_linear_internal {n : ℕ}
    (tapes : EntryScanTapes n) (entry : Entry)
    (queryBits : List Bool) :
    entryScanOneTime tapes entry queryBits ≤
      400 * (entry.1.bits.length + entry.2.bits.length +
        queryBits.length + 1) := by
  have hmatch := entryMatchReadTime_le_linear_internal entry queryBits
  have hcleanup := entryMissCleanupTime_canonical_le_linear tapes.entry entry
    queryBits
  unfold entryScanOneTime entryScanStepTime entryScanBranchTime
    TM.branchWorkSymbolTime
  have hmax : max 1
      (entryMissCleanupTime tapes.entry entry queryBits
        (entryScanCanonicalWork (n := n))) ≤
      300 * (entry.1.bits.length + entry.2.bits.length +
        queryBits.length + 1) := by
    apply max_le
    · nlinarith
    · exact hcleanup
  omega

theorem entryScanTime_le_encoded_internal {n : ℕ}
    (tapes : EntryScanTapes n) (queryBits : List Bool) (store : Store) :
    entryScanTime tapes queryBits store ≤
      1000 * (encodedStoreLength store +
        store.length * (queryBits.length + bitlen store.length + 2) + 1) := by
  induction store with
  | nil => simp [entryScanTime, encodedStoreLength]
  | cons entry rest ih =>
      have hone := entryScanOneTime_le_linear_internal tapes entry queryBits
      have hpred := TM.binaryPredTime_le rest.length
      have hsize : bitlen rest.length ≤ bitlen (rest.length + 1) := by
        unfold bitlen
        exact Nat.size_le_size (by omega)
      have hfactor : queryBits.length + bitlen rest.length + 2 ≤
          queryBits.length + bitlen (rest.length + 1) + 2 := by omega
      have hinside : encodedStoreLength rest +
            rest.length * (queryBits.length + bitlen rest.length + 2) + 1 ≤
          encodedStoreLength rest +
            rest.length *
              (queryBits.length + bitlen (rest.length + 1) + 2) + 1 := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_left (Nat.mul_le_mul_left rest.length hfactor) _)
          1
      have htail : entryScanTime tapes queryBits rest ≤
          1000 * (encodedStoreLength rest +
            rest.length *
              (queryBits.length + bitlen (rest.length + 1) + 2) + 1) :=
        le_trans ih (Nat.mul_le_mul_left 1000 hinside)
      have hentryLength : (Entry.encode entry).length =
          2 * entry.1.bits.length + 2 * entry.2.bits.length + 2 := by
        rw [Entry.encode_length]
        simp only [bitlen, Nat.size_eq_bits_len]
      simp only [entryScanTime, List.length_cons]
      have hencoded : encodedStoreLength (entry :: rest) =
          (Entry.encode entry).length + encodedStoreLength rest := by
        simp [encodedStoreLength]
      rw [hencoded, hentryLength]
      simp only [bitlen] at hsize ⊢
      have hmul : (rest.length + 1) *
            (queryBits.length + (rest.length + 1).size + 2) =
          rest.length *
              (queryBits.length + (rest.length + 1).size + 2) +
            (queryBits.length + (rest.length + 1).size + 2) := by ring
      rw [hmul]
      simp only [bitlen] at htail
      omega

end Machine

end RegisterStore

end RAM

end Complexity
