/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScan.Defs
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany
import Mathlib.Tactic.FinCases
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

/-!
# Bounded sparse-entry scan — invariant internals
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem resetBinaryBlank_head : TM.resetBinaryBlank.head = 1 := by
  simp [TM.resetBinaryBlank, Tape.init, Tape.move]

private theorem parked_of_hasBinaryNat {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t := by
  exact ⟨by simp [Tape.HasBinaryNat, Tape.HasBinaryString] at h; omega,
    h.2.hasBinaryContent.cells_ne_start⟩

private theorem EntryScanReady.target_head
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

theorem EntryScanReady.stepTime_eq_oneTime_internal
    {tapes : EntryScanTapes n} {entry : Entry} {rest queryBits : List Bool}
    {initialWork work : Fin n → Tape}
    (h : EntryScanReady tapes.entry (Entry.encode entry ++ rest) queryBits
      initialWork work) :
    entryScanStepTime tapes.entry entry queryBits work =
      entryScanOneTime tapes entry queryBits := by
  have hquery :
      entryMissHeadBound entry queryBits work tapes.entry.query =
        entryMissHeadBound entry queryBits entryScanCanonicalWork
          tapes.entry.query := by
    simp [entryMissHeadBound, entryScanCanonicalWork, h.query.1,
      resetBinaryBlank_head]
  have htargets : ∀ i, i ∈ entryMissTargets tapes.entry →
      entryMissHeadBound entry queryBits work i =
        entryMissHeadBound entry queryBits entryScanCanonicalWork i := by
    intro i hi
    simp [entryMissHeadBound, entryScanCanonicalWork, h.target_head i hi,
      resetBinaryBlank_head]
  have hreset := TM.resetBinaryWorkManyTime_congr_headBound
    (entryMissTargets tapes.entry) (entryMissBits tapes.entry entry queryBits)
    (entryMissHeadBound entry queryBits work)
    (entryMissHeadBound entry queryBits entryScanCanonicalWork) htargets
  unfold entryScanOneTime entryScanStepTime entryScanBranchTime
    entryMissCleanupTime TM.branchWorkSymbolTime
  rw [hquery, hreset]

/-- Forget an older frame base and use the current work family as the exact
base for the next loop iteration. -/
theorem EntryScanReady.rebase_self_internal
    {tapes : EntryMatchTapes n} {remaining queryBits : List Bool}
    {initialWork work : Fin n → Tape}
    (h : EntryScanReady tapes remaining queryBits initialWork work) :
    EntryScanReady tapes remaining queryBits work work := by
  refine ⟨h.source, h.address, h.addressStart, h.value, h.valueStart,
    h.addressCounter, h.addressWidth, h.valueCounter, h.valueWidth,
    h.query, h.queryStart, h.result, h.resultStart, h.parked, ?_⟩
  intro i _ _ _ _ _ _ _ _ _
  rfl

/-- Changing only the distinct count tape preserves the entry-loop invariant;
the new count representation supplies parkedness for that tape. -/
theorem EntryScanReady.change_count_internal
    {tapes : EntryScanTapes n} {remaining queryBits : List Bool}
    {initialWork work finalWork : Fin n → Tape} {count : ℕ}
    (h : EntryScanReady tapes.entry remaining queryBits initialWork work)
    (hother : ∀ i, i ≠ tapes.count → finalWork i = work i)
    (hcount : (finalWork tapes.count).HasBinaryNat count) :
    EntryScanReady tapes.entry remaining queryBits finalWork finalWork := by
  have hsource := hother tapes.entry.source (Ne.symm (tapes.count_ne 0))
  have haddress := hother tapes.entry.address (Ne.symm (tapes.count_ne 1))
  have hvalue := hother tapes.entry.value (Ne.symm (tapes.count_ne 2))
  have haddressCounter :=
    hother tapes.entry.addressCounter (Ne.symm (tapes.count_ne 3))
  have haddressWidth :=
    hother tapes.entry.addressWidth (Ne.symm (tapes.count_ne 4))
  have hvalueCounter :=
    hother tapes.entry.valueCounter (Ne.symm (tapes.count_ne 5))
  have hvalueWidth :=
    hother tapes.entry.valueWidth (Ne.symm (tapes.count_ne 6))
  have hquery := hother tapes.entry.query (Ne.symm (tapes.count_ne 7))
  have hresult := hother tapes.entry.result (Ne.symm (tapes.count_ne 8))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsource]
    exact h.source
  · rw [haddress]
    exact h.address
  · rw [haddress]
    exact h.addressStart
  · rw [hvalue]
    exact h.value
  · rw [hvalue]
    exact h.valueStart
  · rw [haddressCounter]
    exact h.addressCounter
  · rw [haddressWidth]
    exact h.addressWidth
  · rw [hvalueCounter]
    exact h.valueCounter
  · rw [hvalueWidth]
    exact h.valueWidth
  · rw [hquery]
    exact h.query
  · rw [hquery]
    exact h.queryStart
  · rw [hresult]
    exact h.result
  · rw [hresult]
    exact h.resultStart
  · intro i
    by_cases hi : i = tapes.count
    · subst i
      exact parked_of_hasBinaryNat hcount
    · rw [hother i hi]
      exact h.parked i
  · intro i _ _ _ _ _ _ _ _ _
    rfl

/-- An entry-ready frame implies the scanner's weaker ten-tape frame. -/
theorem EntryScanReady.scanFrame_internal
    {tapes : EntryScanTapes n} {remaining queryBits : List Bool}
    {initialWork finalWork : Fin n → Tape}
    (h : EntryScanReady tapes.entry remaining queryBits initialWork finalWork) :
    EntryScanFrame tapes initialWork finalWork := by
  intro i _ hsource haddress hvalue haddressCounter haddressWidth
    hvalueCounter hvalueWidth hquery hresult
  exact h.frame i hsource haddress hvalue haddressCounter haddressWidth
    hvalueCounter hvalueWidth hquery hresult

/-- A successful entry endpoint implies the scanner's ten-tape frame. -/
theorem EntryScanHit.scanFrame_internal
    {tapes : EntryScanTapes n} {entry : Entry} {rest queryBits : List Bool}
    {initialWork finalWork : Fin n → Tape}
    (h : EntryScanHit tapes.entry entry rest queryBits initialWork finalWork) :
    EntryScanFrame tapes initialWork finalWork := by
  intro i _ hsource haddress hvalue haddressCounter haddressWidth
    hvalueCounter hvalueWidth hquery hresult
  exact h.frame i hsource haddress hvalue haddressCounter haddressWidth
    hvalueCounter hvalueWidth hquery hresult

/-- Scanner frames compose across loop iterations. -/
theorem EntryScanFrame.trans_internal
    {tapes : EntryScanTapes n} {work₀ work₁ work₂ : Fin n → Tape}
    (h₁ : EntryScanFrame tapes work₀ work₁)
    (h₂ : EntryScanFrame tapes work₁ work₂) :
    EntryScanFrame tapes work₀ work₂ := by
  intro i hcount hsource haddress hvalue haddressCounter haddressWidth
    hvalueCounter hvalueWidth hquery hresult
  exact (h₂ i hcount hsource haddress hvalue haddressCounter haddressWidth
    hvalueCounter hvalueWidth hquery hresult).trans
    (h₁ i hcount hsource haddress hvalue haddressCounter haddressWidth
      hvalueCounter hvalueWidth hquery hresult)

/-- The count tape is in the frame of every entry-ready endpoint. -/
theorem EntryScanReady.count_eq_internal
    {tapes : EntryScanTapes n} {remaining queryBits : List Bool}
    {initialWork finalWork : Fin n → Tape}
    (h : EntryScanReady tapes.entry remaining queryBits initialWork finalWork) :
    finalWork tapes.count = initialWork tapes.count :=
  h.frame tapes.count (tapes.count_ne 0) (tapes.count_ne 1)
    (tapes.count_ne 2) (tapes.count_ne 3) (tapes.count_ne 4)
    (tapes.count_ne 5) (tapes.count_ne 6) (tapes.count_ne 7)
    (tapes.count_ne 8)

/-- The count tape is in the frame of every successful entry endpoint. -/
theorem EntryScanHit.count_eq_internal
    {tapes : EntryScanTapes n} {entry : Entry} {rest queryBits : List Bool}
    {initialWork finalWork : Fin n → Tape}
    (h : EntryScanHit tapes.entry entry rest queryBits initialWork finalWork) :
    finalWork tapes.count = initialWork tapes.count :=
  h.frame tapes.count (tapes.count_ne 0) (tapes.count_ne 1)
    (tapes.count_ne 2) (tapes.count_ne 3) (tapes.count_ne 4)
    (tapes.count_ne 5) (tapes.count_ne 6) (tapes.count_ne 7)
    (tapes.count_ne 8)

/-- A restored miss invariant exposes a blank readable result. -/
theorem EntryScanReady.result_read_blank_internal
    {tapes : EntryMatchTapes n} {remaining queryBits : List Bool}
    {initialWork finalWork : Fin n → Tape}
    (h : EntryScanReady tapes remaining queryBits initialWork finalWork) :
    (finalWork tapes.result).read = Γ.blank :=
  h.result.read_blank

/-- A successful hit exposes the readable one flag. -/
theorem EntryScanHit.result_read_one_internal
    {tapes : EntryMatchTapes n} {entry : Entry} {rest queryBits : List Bool}
    {initialWork finalWork : Fin n → Tape}
    (h : EntryScanHit tapes entry rest queryBits initialWork finalWork) :
    (finalWork tapes.result).read = Γ.one := by
  rw [Tape.read, h.result.1]
  simpa [Γ.ofBool] using h.result.2.1 0 (by simp)

end Machine

end RegisterStore

end RAM

end Complexity
