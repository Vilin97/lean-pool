/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMatch.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMatch.Internal

/-!
# RAM sparse-entry matching

This module exposes the exact framed semantics of the concrete decode-and-match
unit used by a bounded sparse register-store scan.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Decode one canonical sparse entry and compare its address with a preserved
canonical query, leaving the next entry under the source head. -/
theorem entryMatchTM_reachesIn_frame {n : ℕ}
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ tapes.source).HasBinarySuffix (Entry.encode entry ++ rest))
    (haddress : (work₀ tapes.address).HasBinaryPrefix [])
    (hvalue : (work₀ tapes.value).HasBinaryPrefix [])
    (haddressStart : (work₀ tapes.address).cells 0 = Γ.start)
    (hvalueStart : (work₀ tapes.value).cells 0 = Γ.start)
    (haddressCounter : (work₀ tapes.addressCounter).HasBinaryNat 0)
    (haddressWidth : (work₀ tapes.addressWidth).HasBinaryNat 0)
    (hvalueCounter : (work₀ tapes.valueCounter).HasBinaryNat 0)
    (hvalueWidth : (work₀ tapes.valueWidth).HasBinaryNat 0)
    (hquery : (work₀ tapes.query).HasBinaryString queryBits)
    (hqueryStart : (work₀ tapes.query).cells 0 = Γ.start)
    (hresult : (work₀ tapes.result).HasBinaryPrefix [])
    (hresultStart : (work₀ tapes.result).cells 0 = Γ.start)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    ∃ c' t,
      t ≤ entryMatchTime entry queryBits ∧
      (entryMatchTM tapes).reachesIn t
        { state := (entryMatchTM tapes).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (entryMatchTM tapes).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work tapes.source).HasBinarySuffix rest ∧
      (c'.work tapes.address).HasBinaryContent entry.1.bits ∧
      1 ≤ (c'.work tapes.address).head ∧
      (c'.work tapes.address).cells 0 = Γ.start ∧
      (c'.work tapes.value).HasBinaryPrefix entry.2.bits ∧
      (c'.work tapes.value).cells 0 = Γ.start ∧
      (c'.work tapes.addressCounter).HasBinaryPrefix
        (List.replicate (bitlen entry.1) true) ∧
      (c'.work tapes.addressCounter).cells 0 = Γ.start ∧
      (c'.work tapes.addressWidth).HasBinaryNat 0 ∧
      (c'.work tapes.valueCounter).HasBinaryPrefix
        (List.replicate (bitlen entry.2) true) ∧
      (c'.work tapes.valueCounter).cells 0 = Γ.start ∧
      (c'.work tapes.valueWidth).HasBinaryNat 0 ∧
      (c'.work tapes.query).HasBinaryContent queryBits ∧
      1 ≤ (c'.work tapes.query).head ∧
      (c'.work tapes.query).cells 0 = Γ.start ∧
      (c'.work tapes.result).HasBinaryPrefix
        [decide (entry.1.bits = queryBits)] ∧
      (c'.work tapes.result).cells 0 = Γ.start ∧
      (∀ i, TM.Parked (c'.work i)) ∧
      (∀ i, i ≠ tapes.source → i ≠ tapes.address → i ≠ tapes.value →
        i ≠ tapes.addressCounter → i ≠ tapes.addressWidth →
        i ≠ tapes.valueCounter → i ≠ tapes.valueWidth →
        i ≠ tapes.query → i ≠ tapes.result → c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  entryMatchTM_reachesIn_frame_internal tapes entry rest queryBits inp₀
    work₀ out₀ hsource haddress hvalue haddressStart hvalueStart
      haddressCounter haddressWidth hvalueCounter hvalueWidth hquery
      hqueryStart hresult hresultStart hinput hwork houtput

/-- Decode and compare one canonical sparse entry, then rewind the one-bit
result to cell one so that the enclosing bounded scan can branch on it. -/
theorem entryMatchReadTM_reachesIn_frame {n : ℕ}
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ tapes.source).HasBinarySuffix (Entry.encode entry ++ rest))
    (haddress : (work₀ tapes.address).HasBinaryPrefix [])
    (hvalue : (work₀ tapes.value).HasBinaryPrefix [])
    (haddressStart : (work₀ tapes.address).cells 0 = Γ.start)
    (hvalueStart : (work₀ tapes.value).cells 0 = Γ.start)
    (haddressCounter : (work₀ tapes.addressCounter).HasBinaryNat 0)
    (haddressWidth : (work₀ tapes.addressWidth).HasBinaryNat 0)
    (hvalueCounter : (work₀ tapes.valueCounter).HasBinaryNat 0)
    (hvalueWidth : (work₀ tapes.valueWidth).HasBinaryNat 0)
    (hquery : (work₀ tapes.query).HasBinaryString queryBits)
    (hqueryStart : (work₀ tapes.query).cells 0 = Γ.start)
    (hresult : (work₀ tapes.result).HasBinaryPrefix [])
    (hresultStart : (work₀ tapes.result).cells 0 = Γ.start)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    ∃ c' t,
      t ≤ entryMatchReadTime entry queryBits ∧
      (entryMatchReadTM tapes).reachesIn t
        { state := (entryMatchReadTM tapes).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (entryMatchReadTM tapes).halted c' ∧
      c'.input = inp₀ ∧
      ReadableEntryMatch tapes entry rest queryBits work₀ c'.work ∧
      c'.output = out₀ :=
  entryMatchReadTM_reachesIn_frame_internal tapes entry rest queryBits inp₀
    work₀ out₀ hsource haddress hvalue haddressStart hvalueStart
      haddressCounter haddressWidth hvalueCounter hvalueWidth hquery
      hqueryStart hresult hresultStart hinput hwork houtput

/-- A readable entry-match endpoint exposes its Boolean answer directly under
the result-tape head. -/
theorem ReadableEntryMatch.result_read {n : ℕ} {tapes : EntryMatchTapes n}
    {entry : Entry} {rest queryBits : List Bool}
    {initialWork finalWork : Fin n → Tape}
    (h : ReadableEntryMatch tapes entry rest queryBits initialWork finalWork) :
    (finalWork tapes.result).read =
      Γ.ofBool (decide (entry.1.bits = queryBits)) :=
  h.result.hasBinarySuffix.read_cons

/-- The result head reads one exactly when the decoded address equals the
query. -/
theorem ReadableEntryMatch.result_read_eq_one_iff {n : ℕ}
    {tapes : EntryMatchTapes n} {entry : Entry} {rest queryBits : List Bool}
    {initialWork finalWork : Fin n → Tape}
    (h : ReadableEntryMatch tapes entry rest queryBits initialWork finalWork) :
    (finalWork tapes.result).read = Γ.one ↔ entry.1.bits = queryBits := by
  by_cases heq : entry.1.bits = queryBits <;>
    simp [h.result_read, heq, Γ.ofBool]

/-- Exact closed form for the readable unary-marker entry-match runtime. -/
theorem entryMatchReadTime_eq (entry : Entry) (queryBits : List Bool) :
    entryMatchReadTime entry queryBits =
      4 * entry.1.bits.length + 3 * entry.2.bits.length +
        max entry.1.bits.length queryBits.length + 18 :=
  entryMatchReadTime_eq_internal entry queryBits

/-- One readable entry match is linear in the serialized entry and query
widths. -/
theorem entryMatchReadTime_le_linear (entry : Entry)
    (queryBits : List Bool) :
    entryMatchReadTime entry queryBits ≤
      5 * entry.1.bits.length + 3 * entry.2.bits.length +
        queryBits.length + 18 :=
  entryMatchReadTime_le_linear_internal entry queryBits

/-- Coarse all-prefix auxiliary-space envelope for one entry match. -/
theorem entryMatchTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryMatchTapes n) (entry : Entry) (queryBits : List Bool)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryMatchTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryMatchTM tapes).reachesIn time start current)
    (htime : time ≤ entryMatchTime entry queryBits) :
    current.WithinAuxSpace inputLength
      (initialSpace + entryMatchTime entry queryBits) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- Entry matching preserves one-way output safety. -/
theorem entryMatchTM_isTransducer {n : ℕ} (tapes : EntryMatchTapes n) :
    (entryMatchTM tapes).IsTransducer := by
  unfold entryMatchTM
  exact (entryDecodeLinearTM_isTransducer tapes.decode).seqTM
    (decodedAddressEqTM_isTransducer tapes.address tapes.query tapes.result)

/-- Readable entry matching preserves one-way output safety. -/
theorem entryMatchReadTM_isTransducer {n : ℕ} (tapes : EntryMatchTapes n) :
    (entryMatchReadTM tapes).IsTransducer := by
  unfold entryMatchReadTM
  exact (entryMatchTM_isTransducer tapes).seqTM
    (TM.rewindWorkTM_isTransducer tapes.result)

/-- Coarse all-prefix auxiliary-space envelope for readable entry matching. -/
theorem entryMatchReadTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryMatchTapes n) (entry : Entry) (queryBits : List Bool)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryMatchReadTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryMatchReadTM tapes).reachesIn time start current)
    (htime : time ≤ entryMatchReadTime entry queryBits) :
    current.WithinAuxSpace inputLength
      (initialSpace + entryMatchReadTime entry queryBits) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

end Machine

end RegisterStore

end RAM

end Complexity
