/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryPred
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

/-!
# Bounded encoded sparse-store update — static runtime bounds

The entry subroutines expose exact compositional times parameterized by the
current work family.  This file discharges that dependency at the update-loop
boundary: a ready loop invariant fixes every owned starting head, while a
readable match bounds the one cursor whose endpoint is intentionally in-place.
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

/-- The preserved query is rewound at every update-loop boundary. -/
theorem EntryScanReady.query_head_eq_one_internal
    {tapes : EntryMatchTapes n} {remaining queryBits : List Bool}
    {initialWork work : Fin n → Tape}
    (h : EntryScanReady tapes remaining queryBits initialWork work) :
    (work tapes.query).head = 1 :=
  h.query.1

/-- Every scratch target cleared by an update branch starts at cell one at a
ready loop boundary. -/
theorem EntryScanReady.cleanup_target_head_eq_one_internal
    {tapes : EntryMatchTapes n} {remaining queryBits : List Bool}
    {initialWork work : Fin n → Tape}
    (h : EntryScanReady tapes remaining queryBits initialWork work) :
    ∀ i, i ∈ entryMissTargets tapes → (work i).head = 1 := by
  intro i hi
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
  fin_cases slot
  · simpa using h.address.1
  · simpa using h.value.1
  · exact h.addressCounter.2.1
  · exact h.addressWidth.2.1
  · exact h.valueCounter.2.1
  · exact h.valueWidth.2.1
  · simpa using h.result.1

/-- On a ready loop boundary, the exact deletion-cleanup time is the static
controller bound. -/
theorem entryMissCleanupTime_eq_entryUpdateReadyCleanupTime_internal
    (tapes : EntryUpdateTapes n) (entry : Entry) (address : ℕ)
    {remaining : List Bool} {initialWork work : Fin n → Tape}
    (hready : EntryScanReady tapes.entry remaining address.bits
      initialWork work) :
    entryMissCleanupTime tapes.entry entry address.bits work =
      entryUpdateReadyCleanupTime tapes entry address := by
  let matchTime := entryMatchReadTime entry address.bits
  have hquery :
      entryMissHeadBound entry address.bits work tapes.entry.query =
        1 + matchTime := by
    simp [entryMissHeadBound, matchTime, hready.query_head_eq_one_internal]
  have htargets : ∀ i, i ∈ entryMissTargets tapes.entry →
      entryMissHeadBound entry address.bits work i = 1 + matchTime := by
    intro i hi
    simp [entryMissHeadBound, matchTime,
      hready.cleanup_target_head_eq_one_internal i hi]
  have hreset := TM.resetBinaryWorkManyTime_congr_headBound
    (entryMissTargets tapes.entry)
    (entryMissBits tapes.entry entry address.bits)
    (entryMissHeadBound entry address.bits work)
    (fun _ => 1 + matchTime) htargets
  unfold entryMissCleanupTime entryUpdateReadyCleanupTime
  rw [hquery, hreset]

private theorem readable_other_cleanup_target_head
    (tapes : EntryUpdateTapes n) (entry : Entry) (rest queryBits : List Bool)
    (initialWork matchedWork : Fin n → Tape)
    (hmatch : ReadableEntryMatch tapes.entry entry rest queryBits initialWork
      matchedWork) (i : Fin n) (hi : i ∈ entryMissTargets tapes.entry)
    (haddress : i ≠ tapes.entry.address)
    (hvalue : i ≠ tapes.entry.value) :
    (matchedWork i).head = entryUpdatePostEmitHead tapes entry i := by
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
  fin_cases slot
  · simp at haddress
  · simp at hvalue
  · simpa [entryUpdatePostEmitHead, EntryMatchTapes.address,
      EntryMatchTapes.value, EntryMatchTapes.addressCounter,
      EntryMatchTapes.addressWidth, EntryMatchTapes.valueCounter,
      EntryMatchTapes.valueWidth, EntryMatchTapes.result,
      tapes.entry.injective.eq_iff] using
      hmatch.addressCounter.1
  · simpa [entryUpdatePostEmitHead, EntryMatchTapes.address,
      EntryMatchTapes.value, EntryMatchTapes.addressCounter,
      EntryMatchTapes.addressWidth, EntryMatchTapes.valueCounter,
      EntryMatchTapes.valueWidth, EntryMatchTapes.result,
      tapes.entry.injective.eq_iff] using
      hmatch.addressWidth.2.1
  · simpa [entryUpdatePostEmitHead, EntryMatchTapes.address,
      EntryMatchTapes.value, EntryMatchTapes.addressCounter,
      EntryMatchTapes.addressWidth, EntryMatchTapes.valueCounter,
      EntryMatchTapes.valueWidth, EntryMatchTapes.result,
      tapes.entry.injective.eq_iff] using
      hmatch.valueCounter.1
  · simpa [entryUpdatePostEmitHead, EntryMatchTapes.address,
      EntryMatchTapes.value, EntryMatchTapes.addressCounter,
      EntryMatchTapes.addressWidth, EntryMatchTapes.valueCounter,
      EntryMatchTapes.valueWidth, EntryMatchTapes.result,
      tapes.entry.injective.eq_iff] using
      hmatch.valueWidth.2.1
  · simpa [entryUpdatePostEmitHead, EntryMatchTapes.address,
      EntryMatchTapes.value, EntryMatchTapes.addressCounter,
      EntryMatchTapes.addressWidth, EntryMatchTapes.valueCounter,
      EntryMatchTapes.valueWidth, EntryMatchTapes.result,
      tapes.entry.injective.eq_iff] using
      hmatch.result.1

private theorem entryMissCopiedWork_target_head
    (tapes : EntryUpdateTapes n) (entry : Entry) (rest queryBits : List Bool)
    (initialWork matchedWork : Fin n → Tape)
    (hmatch : ReadableEntryMatch tapes.entry entry rest queryBits initialWork
      matchedWork) :
    ∀ i, i ∈ entryMissTargets tapes.entry →
      (entryMissCopiedWork tapes.entry entry matchedWork i).head =
        entryUpdatePostEmitHead tapes entry i := by
  intro i hi
  by_cases haddress : i = tapes.entry.address
  · subst i
    simp [entryMissCopiedWork, entryUpdatePostEmitHead]
  · by_cases hvalue : i = tapes.entry.value
    · subst i
      simp [entryMissCopiedWork, entryUpdatePostEmitHead, haddress]
    · simp only [entryMissCopiedWork, haddress, hvalue, ite_false]
      exact readable_other_cleanup_target_head tapes entry rest queryBits
        initialWork matchedWork hmatch i hi haddress hvalue

private theorem entryReplaceReadyWork_target_head
    (tapes : EntryUpdateTapes n) (entry : Entry) (rest queryBits : List Bool)
    (initialWork matchedWork : Fin n → Tape)
    (hmatch : ReadableEntryMatch tapes.entry entry rest queryBits initialWork
      matchedWork) :
    ∀ i, i ∈ entryMissTargets tapes.entry →
      (entryReplaceReadyWork tapes.replace entry matchedWork i).head =
        entryUpdatePostEmitHead tapes entry i := by
  intro i hi
  by_cases haddress : i = tapes.entry.address
  · subst i
    simp [entryReplaceReadyWork, entryUpdatePostEmitHead]
  · by_cases hvalue : i = tapes.entry.value
    · subst i
      simpa [entryReplaceReadyWork, entryUpdatePostEmitHead, haddress] using
        hmatch.value.1
    · have haddress' : i ≠ tapes.replace.entry.address := by
        simpa using haddress
      rw [entryReplaceReadyWork, ite_eq_right haddress']
      exact readable_other_cleanup_target_head tapes entry rest queryBits
        initialWork matchedWork hmatch i hi haddress hvalue

private theorem entryMissCleanupTime_postEmit_le
    (tapes : EntryUpdateTapes n) (entry : Entry) (address : ℕ)
    (rest : List Bool)
    (initialWork readyWork matchedWork postEmitWork : Fin n → Tape)
    (hready : EntryScanReady tapes.entry (Entry.encode entry ++ rest)
      address.bits initialWork readyWork)
    (hmatch : ReadableEntryMatch tapes.entry entry rest address.bits readyWork
      matchedWork)
    (hqueryEq : postEmitWork tapes.entry.query =
      matchedWork tapes.entry.query)
    (htargets : ∀ i, i ∈ entryMissTargets tapes.entry →
      (postEmitWork i).head = entryUpdatePostEmitHead tapes entry i) :
    entryMissCleanupTime tapes.entry entry address.bits postEmitWork ≤
      entryUpdatePostEmitCleanupTime tapes entry address := by
  let matchTime := entryMatchReadTime entry address.bits
  have hqueryMatched : (matchedWork tapes.entry.query).head ≤
      1 + matchTime := by
    simpa [matchTime, hready.query_head_eq_one_internal] using
      hmatch.headBound tapes.entry.query
  have hqueryPost : (postEmitWork tapes.entry.query).head ≤
      1 + matchTime := by
    rw [hqueryEq]
    exact hqueryMatched
  have hquery :
      entryMissHeadBound entry address.bits postEmitWork tapes.entry.query ≤
        1 + 2 * matchTime := by
    simp only [entryMissHeadBound]
    omega
  have htargets' : ∀ i, i ∈ entryMissTargets tapes.entry →
      entryMissHeadBound entry address.bits postEmitWork i =
        entryUpdatePostEmitHead tapes entry i + matchTime := by
    intro i hi
    simp [entryMissHeadBound, matchTime, htargets i hi]
  have hreset := TM.resetBinaryWorkManyTime_congr_headBound
    (entryMissTargets tapes.entry)
    (entryMissBits tapes.entry entry address.bits)
    (entryMissHeadBound entry address.bits postEmitWork)
    (fun i => entryUpdatePostEmitHead tapes entry i + matchTime) htargets'
  simp only [matchTime] at hreset
  dsimp only [entryMissCleanupTime, entryUpdatePostEmitCleanupTime]
  rw [hreset]
  omega

/-- A ready comparison followed by miss emission has a work-independent
runtime bounded by the controller's static miss budget. -/
theorem entryMissCopyTime_le_entryUpdateMissTime_internal
    (tapes : EntryUpdateTapes n) (entry : Entry) (address : ℕ)
    (rest : List Bool) (initialWork readyWork matchedWork : Fin n → Tape)
    (hready : EntryScanReady tapes.entry (Entry.encode entry ++ rest)
      address.bits initialWork readyWork)
    (hmatch : ReadableEntryMatch tapes.entry entry rest address.bits readyWork
      matchedWork) :
    entryMissCopyTime tapes.entry entry address.bits readyWork matchedWork ≤
      entryUpdateMissTime tapes entry address := by
  let matchTime := entryMatchReadTime entry address.bits
  have haddress :
      entryMissHeadBound entry address.bits readyWork tapes.entry.address =
        1 + matchTime := by
    simp [entryMissHeadBound, matchTime, hready.address.1]
  have hvalue :
      entryMissHeadBound entry address.bits readyWork tapes.entry.value =
        1 + matchTime := by
    simp [entryMissHeadBound, matchTime, hready.value.1]
  have hqueryNeAddress : tapes.entry.query ≠ tapes.entry.address :=
    tapes.entry.ne (by decide)
  have hqueryNeValue : tapes.entry.query ≠ tapes.entry.value :=
    tapes.entry.ne (by decide)
  have hquery :
      entryMissCopiedWork tapes.entry entry matchedWork tapes.entry.query =
        matchedWork tapes.entry.query := by
    simp [entryMissCopiedWork, hqueryNeAddress, hqueryNeValue]
  have hcleanup := entryMissCleanupTime_postEmit_le tapes entry address rest
    initialWork readyWork matchedWork
    (entryMissCopiedWork tapes.entry entry matchedWork) hready hmatch hquery
    (entryMissCopiedWork_target_head tapes entry rest address.bits readyWork
      matchedWork hmatch)
  dsimp only [entryMissCopyTime, entryUpdateMissTime]
  rw [haddress, hvalue]
  exact Nat.add_le_add_left hcleanup _

/-- A ready comparison followed by replacement emission has a work-independent
runtime bounded by the controller's static replacement budget. -/
theorem entryReplaceCleanupTime_le_entryUpdateReplaceTime_internal
    (tapes : EntryUpdateTapes n) (entry : Entry) (address newValue : ℕ)
    (rest : List Bool) (initialWork readyWork matchedWork : Fin n → Tape)
    (hready : EntryScanReady tapes.entry (Entry.encode entry ++ rest)
      address.bits initialWork readyWork)
    (hmatch : ReadableEntryMatch tapes.entry entry rest address.bits readyWork
      matchedWork) :
    entryReplaceCleanupTime tapes.replace entry newValue address.bits readyWork
        matchedWork ≤
      entryUpdateReplaceTime tapes entry address newValue := by
  let matchTime := entryMatchReadTime entry address.bits
  have haddress :
      entryMissHeadBound entry address.bits readyWork tapes.entry.address =
        1 + matchTime := by
    simp [entryMissHeadBound, matchTime, hready.address.1]
  have hqueryNeAddress : tapes.entry.query ≠ tapes.entry.address :=
    tapes.entry.ne (by decide)
  have hquery :
      entryReplaceReadyWork tapes.replace entry matchedWork tapes.entry.query =
        matchedWork tapes.entry.query := by
    simp [entryReplaceReadyWork, hqueryNeAddress]
  have hcleanup := entryMissCleanupTime_postEmit_le tapes entry address rest
    initialWork readyWork matchedWork
    (entryReplaceReadyWork tapes.replace entry matchedWork) hready hmatch hquery
    (entryReplaceReadyWork_target_head tapes entry rest address.bits readyWork
      matchedWork hmatch)
  have haddress' :
      entryMissHeadBound entry address.bits readyWork
          tapes.replace.entry.address =
        1 + matchTime := by
    simpa only [EntryUpdateTapes.replace_entry] using haddress
  have hcleanup' :
      entryMissCleanupTime tapes.replace.entry entry address.bits
          (entryReplaceReadyWork tapes.replace entry matchedWork) ≤
        entryUpdatePostEmitCleanupTime tapes entry address := by
    simpa only [EntryUpdateTapes.replace_entry] using hcleanup
  dsimp only [entryReplaceCleanupTime, entryUpdateReplaceTime]
  rw [haddress']
  simp only [matchTime]
  exact Nat.add_le_add_left
    (Nat.add_le_add_left hcleanup' (newValue.bits.length + 1 + 2 + 1))
    (rewindEntryEncodeTime (entry.1, newValue)
      (1 + entryMatchReadTime entry address.bits) 1 + 1)

/-- A positive counter no larger than the initial store size can be
decremented within the update controller's uniform counter budget. -/
theorem binaryPredTime_le_entryUpdateCountTime_internal
    {value total : ℕ} (hvalue : value + 1 ≤ total) :
    TM.binaryPredTime value ≤ entryUpdateCountTime total := by
  have htime := TM.binaryPredTime_le value
  have hsize := Nat.size_le_size hvalue
  unfold entryUpdateCountTime
  omega

/-- A counter no larger than the initial store size can be incremented within
the update controller's uniform counter budget. -/
theorem binarySuccTime_le_entryUpdateCountTime_internal
    {value total : ℕ} (hvalue : value ≤ total) :
    TM.binarySuccTime value ≤ entryUpdateCountTime total := by
  have htime := TM.binarySuccTime_le value
  have hsize := Nat.size_le_size hvalue
  unfold entryUpdateCountTime
  omega

end Machine

end RegisterStore

end RAM

end Complexity
