/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Internal.Ctrl
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScan.Internal.Inv
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc

/-!
# Bounded encoded sparse-store update — invariant internals

Tape-layout views and frame lemmas used by the semantic update loop.  In
particular, this file isolates the only controller-local mutation: changing
the canonical zero-valued `found` tape to canonical one after a hit.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

namespace EntryUpdateTapes

/-- View the update layout as an entry scanner whose count is `remaining`. -/
def remainingScan (tapes : EntryUpdateTapes n) : EntryScanTapes n where
  entry := tapes.entry
  count := tapes.remaining
  count_ne := by
    intro i h
    change tapes.idx 9 = tapes.idx ⟨i.val, by omega⟩ at h
    have h' : (9 : Fin 13) = ⟨i.val, by omega⟩ := tapes.injective h
    have hv := congrArg (fun k : Fin 13 => k.val) h'
    change 9 = i.val at hv
    omega

/-- View the update layout as an entry scanner whose count is `resultCount`. -/
def resultScan (tapes : EntryUpdateTapes n) : EntryScanTapes n where
  entry := tapes.entry
  count := tapes.resultCount
  count_ne := by
    intro i h
    change tapes.idx 12 = tapes.idx ⟨i.val, by omega⟩ at h
    have h' : (12 : Fin 13) = ⟨i.val, by omega⟩ := tapes.injective h
    have hv := congrArg (fun k : Fin 13 => k.val) h'
    change 12 = i.val at hv
    omega

@[simp] theorem remainingScan_entry (tapes : EntryUpdateTapes n) :
    tapes.remainingScan.entry = tapes.entry := rfl

@[simp] theorem remainingScan_count (tapes : EntryUpdateTapes n) :
    tapes.remainingScan.count = tapes.remaining := rfl

@[simp] theorem resultScan_entry (tapes : EntryUpdateTapes n) :
    tapes.resultScan.entry = tapes.entry := rfl

@[simp] theorem resultScan_count (tapes : EntryUpdateTapes n) :
    tapes.resultScan.count = tapes.resultCount := rfl

/-- The remaining count is outside every entry-machine tape. -/
theorem remaining_ne_entry (tapes : EntryUpdateTapes n) (i : Fin 9) :
    tapes.remaining ≠ tapes.entry.idx i :=
  tapes.remainingScan.count_ne i

/-- The replacement source is outside every entry-machine tape. -/
theorem replacement_ne_entry (tapes : EntryUpdateTapes n) (i : Fin 9) :
    tapes.replacement ≠ tapes.entry.idx i := by
  change tapes.idx 10 ≠ tapes.idx ⟨i.val, by omega⟩
  apply tapes.ne
  intro h
  have hv := congrArg (fun k : Fin 13 => k.val) h
  change 10 = i.val at hv
  omega

/-- The found flag is outside every entry-machine tape. -/
theorem found_ne_entry (tapes : EntryUpdateTapes n) (i : Fin 9) :
    tapes.found ≠ tapes.entry.idx i := by
  change tapes.idx 11 ≠ tapes.idx ⟨i.val, by omega⟩
  apply tapes.ne
  intro h
  have hv := congrArg (fun k : Fin 13 => k.val) h
  change 11 = i.val at hv
  omega

/-- The result count is outside every entry-machine tape. -/
theorem resultCount_ne_entry (tapes : EntryUpdateTapes n) (i : Fin 9) :
    tapes.resultCount ≠ tapes.entry.idx i :=
  tapes.resultScan.count_ne i

/-- The remaining count and replacement source are distinct. -/
theorem remaining_ne_replacement (tapes : EntryUpdateTapes n) :
    tapes.remaining ≠ tapes.replacement :=
  tapes.ne (by decide)

/-- The remaining count and found flag are distinct. -/
theorem remaining_ne_found (tapes : EntryUpdateTapes n) :
    tapes.remaining ≠ tapes.found :=
  tapes.ne (by decide)

/-- The remaining and result counts are distinct. -/
theorem remaining_ne_resultCount (tapes : EntryUpdateTapes n) :
    tapes.remaining ≠ tapes.resultCount :=
  tapes.ne (by decide)

/-- The replacement source and found flag are distinct. -/
theorem replacement_ne_found (tapes : EntryUpdateTapes n) :
    tapes.replacement ≠ tapes.found :=
  tapes.ne (by decide)

/-- The replacement source and result count are distinct. -/
theorem replacement_ne_resultCount (tapes : EntryUpdateTapes n) :
    tapes.replacement ≠ tapes.resultCount :=
  tapes.ne (by decide)

/-- The found flag and result count are distinct. -/
theorem found_ne_resultCount (tapes : EntryUpdateTapes n) :
    tapes.found ≠ tapes.resultCount :=
  tapes.ne (by decide)

end EntryUpdateTapes

/-- The hit-marking update changes exactly the found tape. -/
theorem entryUpdateMarkFoundWork_apply_eq_internal
    (tapes : EntryUpdateTapes n) (work : Fin n → Tape) :
    entryUpdateMarkFoundWork tapes work tapes.found =
      (work tapes.found).writeAndMove Γ.one
        (TM.idleDir (work tapes.found).read) := by
  simp [entryUpdateMarkFoundWork]

/-- The hit-marking update preserves every tape other than the found tape. -/
theorem entryUpdateMarkFoundWork_apply_ne_internal
    (tapes : EntryUpdateTapes n) (work : Fin n → Tape)
    (i : Fin n) (hi : i ≠ tapes.found) :
    entryUpdateMarkFoundWork tapes work i = work i := by
  simp [entryUpdateMarkFoundWork, Function.update_of_ne hi]

/-- Writing `1` over the parked canonical zero flag produces canonical one. -/
theorem entryUpdateMarkFoundWork_found_one_internal
    (tapes : EntryUpdateTapes n) (work : Fin n → Tape)
    (hfound : (work tapes.found).HasBinaryNat 0) :
    (entryUpdateMarkFoundWork tapes work tapes.found).HasBinaryNat 1 := by
  rw [entryUpdateMarkFoundWork_apply_eq_internal]
  rw [hfound.eq_init_move_right]
  have heq :
      (((Tape.init ((0 : ℕ).bits.map Γ.ofBool)).move Dir3.right).writeAndMove
          Γ.one
          (TM.idleDir
            ((Tape.init ((0 : ℕ).bits.map Γ.ofBool)).move Dir3.right).read)) =
        (Tape.init ((1 : ℕ).bits.map Γ.ofBool)).move Dir3.right := by
    apply Tape.ext
    · simp [TM.idleDir, Tape.read, Tape.write, Tape.move, Tape.init,
        Nat.bits]
    · funext i
      cases i with
      | zero =>
          simp [TM.idleDir, Tape.read, Tape.write, Tape.move, Tape.init,
            Nat.bits]
      | succ i =>
          cases i with
          | zero =>
              simp [TM.idleDir, Tape.read, Tape.write, Tape.move, Tape.init,
                Nat.bits, Γ.ofBool]
          | succ i =>
              simp [TM.idleDir, Tape.read, Tape.write, Tape.move, Tape.init,
                Nat.bits]
  rw [heq]
  exact Tape.init_move_right_hasBinaryNat 1

/-- Canonical natural-number tapes are parked away from the left marker. -/
theorem entryUpdateParked_of_hasBinaryNat_internal {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t := by
  exact ⟨by simp [Tape.HasBinaryNat, Tape.HasBinaryString] at h; omega,
    h.2.hasBinaryContent.cells_ne_start⟩

/-- Marking a canonical zero found flag preserves parkedness of the complete
work family. -/
theorem entryUpdateMarkFoundWork_parked_internal
    (tapes : EntryUpdateTapes n) (work : Fin n → Tape)
    (hfound : (work tapes.found).HasBinaryNat 0)
    (hparked : ∀ i, TM.Parked (work i)) :
    ∀ i, TM.Parked (entryUpdateMarkFoundWork tapes work i) := by
  intro i
  by_cases hi : i = tapes.found
  · subst i
    exact entryUpdateParked_of_hasBinaryNat_internal
      (entryUpdateMarkFoundWork_found_one_internal tapes work hfound)
  · rw [entryUpdateMarkFoundWork_apply_ne_internal tapes work i hi]
    exact hparked i

/-- The marked found flag exposes `1` directly under its parked head. -/
theorem entryUpdateMarkFoundWork_found_read_one_internal
    (tapes : EntryUpdateTapes n) (work : Fin n → Tape)
    (hfound : (work tapes.found).HasBinaryNat 0) :
    (entryUpdateMarkFoundWork tapes work tapes.found).read = Γ.one := by
  have h := entryUpdateMarkFoundWork_found_one_internal tapes work hfound
  simpa [Nat.bits, Γ.ofBool] using h.2.hasBinarySuffix.read_cons

/-- The frame component of an entry-ready endpoint can be queried with one
uniform proof that an index lies outside the nine entry-machine tapes. -/
theorem EntryScanReady.frame_outside_entry_internal
    {tapes : EntryUpdateTapes n} {remaining queryBits : List Bool}
    {initialWork finalWork : Fin n → Tape}
    (h : EntryScanReady tapes.entry remaining queryBits initialWork finalWork)
    (i : Fin n) (houtside : ∀ j : Fin 9, i ≠ tapes.entry.idx j) :
    finalWork i = initialWork i :=
  h.frame i (houtside 0) (houtside 1) (houtside 2) (houtside 3)
    (houtside 4) (houtside 5) (houtside 6) (houtside 7) (houtside 8)

/-- The frame component of a readable match can be queried uniformly outside
the nine entry-machine tapes. -/
theorem ReadableEntryMatch.frame_outside_entry_internal
    {tapes : EntryUpdateTapes n} {entry : Entry} {rest queryBits : List Bool}
    {initialWork finalWork : Fin n → Tape}
    (h : ReadableEntryMatch tapes.entry entry rest queryBits
      initialWork finalWork)
    (i : Fin n) (houtside : ∀ j : Fin 9, i ≠ tapes.entry.idx j) :
    finalWork i = initialWork i :=
  h.frame i (houtside 0) (houtside 1) (houtside 2) (houtside 3)
    (houtside 4) (houtside 5) (houtside 6) (houtside 7) (houtside 8)

/-- Marking the external found flag preserves an entry-ready invariant while
updating both sides of its exact frame. -/
theorem EntryScanReady.markFound_internal
    {tapes : EntryUpdateTapes n} {remaining queryBits : List Bool}
    {initialWork finalWork : Fin n → Tape}
    (h : EntryScanReady tapes.entry remaining queryBits initialWork finalWork)
    (hfound : (finalWork tapes.found).HasBinaryNat 0) :
    EntryScanReady tapes.entry remaining queryBits
      (entryUpdateMarkFoundWork tapes initialWork)
      (entryUpdateMarkFoundWork tapes finalWork) := by
  have hfoundFrame : finalWork tapes.found = initialWork tapes.found :=
    h.frame_outside_entry_internal tapes.found tapes.found_ne_entry
  have hsource : tapes.entry.source ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 0)
  have haddress : tapes.entry.address ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 1)
  have hvalue : tapes.entry.value ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 2)
  have haddressCounter : tapes.entry.addressCounter ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 3)
  have haddressWidth : tapes.entry.addressWidth ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 4)
  have hvalueCounter : tapes.entry.valueCounter ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 5)
  have hvalueWidth : tapes.entry.valueWidth ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 6)
  have hquery : tapes.entry.query ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 7)
  have hresult : tapes.entry.result ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 8)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hsource]
    exact h.source
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ haddress]
    exact h.address
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ haddress]
    exact h.addressStart
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hvalue]
    exact h.value
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hvalue]
    exact h.valueStart
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ haddressCounter]
    exact h.addressCounter
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ haddressWidth]
    exact h.addressWidth
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hvalueCounter]
    exact h.valueCounter
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hvalueWidth]
    exact h.valueWidth
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hquery]
    exact h.query
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hquery]
    exact h.queryStart
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hresult]
    exact h.result
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hresult]
    exact h.resultStart
  · exact entryUpdateMarkFoundWork_parked_internal tapes finalWork hfound h.parked
  · intro i hsource haddress hvalue haddressCounter haddressWidth
      hvalueCounter hvalueWidth hquery hresult
    by_cases hi : i = tapes.found
    · subst i
      rw [entryUpdateMarkFoundWork_apply_eq_internal,
        entryUpdateMarkFoundWork_apply_eq_internal, hfoundFrame]
    · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hi,
        entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hi]
      exact h.frame i hsource haddress hvalue haddressCounter haddressWidth
        hvalueCounter hvalueWidth hquery hresult

/-- Marking the external found flag preserves a readable matched-entry
endpoint while updating both sides of its exact frame. -/
theorem ReadableEntryMatch.markFound_internal
    {tapes : EntryUpdateTapes n} {entry : Entry} {rest queryBits : List Bool}
    {initialWork finalWork : Fin n → Tape}
    (h : ReadableEntryMatch tapes.entry entry rest queryBits
      initialWork finalWork)
    (hfound : (finalWork tapes.found).HasBinaryNat 0) :
    ReadableEntryMatch tapes.entry entry rest queryBits
      (entryUpdateMarkFoundWork tapes initialWork)
      (entryUpdateMarkFoundWork tapes finalWork) := by
  have hfoundFrame : finalWork tapes.found = initialWork tapes.found :=
    h.frame_outside_entry_internal tapes.found tapes.found_ne_entry
  have hsource : tapes.entry.source ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 0)
  have haddress : tapes.entry.address ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 1)
  have hvalue : tapes.entry.value ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 2)
  have haddressCounter : tapes.entry.addressCounter ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 3)
  have haddressWidth : tapes.entry.addressWidth ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 4)
  have hvalueCounter : tapes.entry.valueCounter ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 5)
  have hvalueWidth : tapes.entry.valueWidth ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 6)
  have hquery : tapes.entry.query ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 7)
  have hresult : tapes.entry.result ≠ tapes.found :=
    Ne.symm (tapes.found_ne_entry 8)
  constructor
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hsource]
    exact h.source
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ haddress]
    exact h.address
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ haddress]
    exact h.addressStart
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hvalue]
    exact h.value
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hvalue]
    exact h.valueStart
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ haddressCounter]
    exact h.addressCounter
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ haddressCounter]
    exact h.addressCounterStart
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ haddressWidth]
    exact h.addressWidth
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hvalueCounter]
    exact h.valueCounter
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hvalueCounter]
    exact h.valueCounterStart
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hvalueWidth]
    exact h.valueWidth
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hquery]
    exact h.query
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hquery]
    exact h.queryStart
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hresult]
    exact h.result
  · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hresult]
    exact h.resultStart
  · exact entryUpdateMarkFoundWork_parked_internal tapes finalWork hfound h.parked
  · intro i
    by_cases hi : i = tapes.found
    · subst i
      rw [entryUpdateMarkFoundWork_apply_eq_internal,
        entryUpdateMarkFoundWork_apply_eq_internal, hfoundFrame]
      exact Nat.le_add_right _ _
    · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hi,
        entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hi]
      exact h.headBound i
  · intro i hsource haddress hvalue haddressCounter haddressWidth
      hvalueCounter hvalueWidth hquery hresult
    by_cases hi : i = tapes.found
    · subst i
      rw [entryUpdateMarkFoundWork_apply_eq_internal,
        entryUpdateMarkFoundWork_apply_eq_internal, hfoundFrame]
    · rw [entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hi,
        entryUpdateMarkFoundWork_apply_ne_internal _ _ _ hi]
      exact h.frame i hsource haddress hvalue haddressCounter haddressWidth
        hvalueCounter hvalueWidth hquery hresult

/-- A frame-rich binary operation on the remaining-count tape preserves and
rebases the entry-ready invariant. -/
theorem EntryScanReady.change_remaining_internal
    {tapes : EntryUpdateTapes n} {remaining queryBits : List Bool}
    {initialWork work finalWork : Fin n → Tape} {count : ℕ}
    (h : EntryScanReady tapes.entry remaining queryBits initialWork work)
    (hother : ∀ i, i ≠ tapes.remaining → finalWork i = work i)
    (hcount : (finalWork tapes.remaining).HasBinaryNat count) :
    EntryScanReady tapes.entry remaining queryBits finalWork finalWork := by
  exact h.change_count_internal (tapes := tapes.remainingScan) hother hcount

/-- A frame-rich binary operation on the result-count tape preserves and
rebases the entry-ready invariant. -/
theorem EntryScanReady.change_resultCount_internal
    {tapes : EntryUpdateTapes n} {remaining queryBits : List Bool}
    {initialWork work finalWork : Fin n → Tape} {count : ℕ}
    (h : EntryScanReady tapes.entry remaining queryBits initialWork work)
    (hother : ∀ i, i ≠ tapes.resultCount → finalWork i = work i)
    (hcount : (finalWork tapes.resultCount).HasBinaryNat count) :
    EntryScanReady tapes.entry remaining queryBits finalWork finalWork := by
  exact h.change_count_internal (tapes := tapes.resultScan) hother hcount

end Machine

end RegisterStore

end RAM

end Complexity
