/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryDecode.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryDecode.Internal
public import
LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryDecode.LinearInternal

/-!
# RAM sparse-entry decoder

This module exposes the exact framed semantics of the concrete two-word sparse
address/value decoder.
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Decode one canonical sparse address/value entry exactly, leaving the next
encoded entry under the source head and preserving every unrelated tape. -/
theorem entryDecodeTM_reachesIn_frame {n : ℕ}
    (tapes : EntryDecodeTapes n) (entry : Entry) (rest : List Bool)
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
    (hinput : inp₀.read ≠ Γ.start)
    (hreads : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (entryDecodeTM tapes).reachesIn (entryDecodeTime entry.1 entry.2)
        { state := (entryDecodeTM tapes).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (entryDecodeTM tapes).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work tapes.source).HasBinarySuffix rest ∧
      (c'.work tapes.address).HasBinaryPrefix entry.1.bits ∧
      (c'.work tapes.address).cells 0 = Γ.start ∧
      (c'.work tapes.value).HasBinaryPrefix entry.2.bits ∧
      (c'.work tapes.value).cells 0 = Γ.start ∧
      (c'.work tapes.addressCounter).HasBinaryNat (bitlen entry.1) ∧
      (c'.work tapes.addressWidth).HasBinaryNat (bitlen entry.1) ∧
      (c'.work tapes.valueCounter).HasBinaryNat (bitlen entry.2) ∧
      (c'.work tapes.valueWidth).HasBinaryNat (bitlen entry.2) ∧
      (∀ i, i ≠ tapes.source → i ≠ tapes.address → i ≠ tapes.value →
        i ≠ tapes.addressCounter → i ≠ tapes.addressWidth →
        i ≠ tapes.valueCounter → i ≠ tapes.valueWidth →
        c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  entryDecodeTM_reachesIn_frame_internal tapes entry rest inp₀ work₀ out₀
    hsource haddress hvalue haddressStart hvalueStart haddressCounter
      haddressWidth hvalueCounter hvalueWidth hinput hreads houtput

/-- Coarse all-prefix auxiliary-space envelope for entry decoding. -/
theorem entryDecodeTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryDecodeTapes n) (address value : ℕ)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryDecodeTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryDecodeTM tapes).reachesIn time start current)
    (htime : time ≤ entryDecodeTime address value) :
    current.WithinAuxSpace inputLength
      (initialSpace + entryDecodeTime address value) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- Entry decoding preserves one-way output safety. -/
theorem entryDecodeTM_isTransducer {n : ℕ} (tapes : EntryDecodeTapes n) :
    (entryDecodeTM tapes).IsTransducer := by
  unfold entryDecodeTM
  exact (wordDecodeTM_isTransducer tapes.source tapes.address
    tapes.addressCounter tapes.addressWidth).seqTM
      (wordDecodeTM_isTransducer tapes.source tapes.value tapes.valueCounter
        tapes.valueWidth)

/-! ## Linear unary-marker decoder -/

/-- Decode one canonical sparse entry using unary markers, leaving the next
entry under the source head and preserving the two unused width tapes. -/
theorem entryDecodeLinearTM_reachesIn_frame {n : ℕ}
    (tapes : EntryDecodeTapes n) (entry : Entry) (rest : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ tapes.source).HasBinarySuffix (Entry.encode entry ++ rest))
    (haddress : (work₀ tapes.address).HasBinaryPrefix [])
    (hvalue : (work₀ tapes.value).HasBinaryPrefix [])
    (haddressStart : (work₀ tapes.address).cells 0 = Γ.start)
    (hvalueStart : (work₀ tapes.value).cells 0 = Γ.start)
    (haddressMarker : (work₀ tapes.addressCounter).HasBinaryPrefix [])
    (haddressMarkerStart : (work₀ tapes.addressCounter).cells 0 = Γ.start)
    (hvalueMarker : (work₀ tapes.valueCounter).HasBinaryPrefix [])
    (hvalueMarkerStart : (work₀ tapes.valueCounter).cells 0 = Γ.start)
    (hinput : inp₀.read ≠ Γ.start)
    (hreads : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (entryDecodeLinearTM tapes).reachesIn
        (entryDecodeLinearTime entry.1 entry.2)
        { state := (entryDecodeLinearTM tapes).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (entryDecodeLinearTM tapes).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work tapes.source).HasBinarySuffix rest ∧
      (c'.work tapes.address).HasBinaryPrefix entry.1.bits ∧
      (c'.work tapes.address).cells 0 = Γ.start ∧
      (c'.work tapes.value).HasBinaryPrefix entry.2.bits ∧
      (c'.work tapes.value).cells 0 = Γ.start ∧
      (c'.work tapes.addressCounter).HasBinaryPrefix
        (List.replicate (bitlen entry.1) true) ∧
      (c'.work tapes.valueCounter).HasBinaryPrefix
        (List.replicate (bitlen entry.2) true) ∧
      (∀ i, i ≠ tapes.source → i ≠ tapes.address → i ≠ tapes.value →
        i ≠ tapes.addressCounter → i ≠ tapes.valueCounter →
        c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  entryDecodeLinearTM_reachesIn_frame_internal tapes entry rest inp₀ work₀ out₀
    hsource haddress hvalue haddressStart hvalueStart haddressMarker
      haddressMarkerStart hvalueMarker hvalueMarkerStart hinput hreads houtput

/-- The exact optimized entry-decoding time is linear in the two word widths. -/
theorem entryDecodeLinearTime_eq (address value : ℕ) :
    entryDecodeLinearTime address value =
      3 * (bitlen address + bitlen value) + 7 := by
  unfold entryDecodeLinearTime wordDecodeLinearTime
  omega

/-- Coarse all-prefix auxiliary-space envelope for optimized entry decoding. -/
theorem entryDecodeLinearTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryDecodeTapes n) (address value : ℕ)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryDecodeLinearTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryDecodeLinearTM tapes).reachesIn time start current)
    (htime : time ≤ entryDecodeLinearTime address value) :
    current.WithinAuxSpace inputLength
      (initialSpace + entryDecodeLinearTime address value) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- Optimized entry decoding preserves one-way output safety. -/
theorem entryDecodeLinearTM_isTransducer {n : ℕ}
    (tapes : EntryDecodeTapes n) :
    (entryDecodeLinearTM tapes).IsTransducer := by
  unfold entryDecodeLinearTM
  exact (wordDecodeLinearTM_isTransducer tapes.source tapes.address
    tapes.addressCounter).seqTM
      (wordDecodeLinearTM_isTransducer tapes.source tapes.value
        tapes.valueCounter)

end Machine

end RegisterStore

end RAM

end Complexity
