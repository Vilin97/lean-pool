/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.AddressEq.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ClearWork

/-!
# Decoded sparse-address equality

This module exposes the framed linear-time semantics of address rewind and
comparison used by the concrete sparse register-store scan.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Rewind one decoded address and compare it to a canonical query, preserving
both contents, both left markers, and every unrelated tape. -/
theorem decodedAddressEqTM_reachesIn_frame {n : ℕ}
    (addressIdx queryIdx resultIdx : Fin n)
    (hdistinct : TM.BinaryEqDistinct addressIdx queryIdx resultIdx)
    (addressBits queryBits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (haddress : (work₀ addressIdx).HasBinaryPrefix addressBits)
    (haddressStart : (work₀ addressIdx).cells 0 = Γ.start)
    (hquery : (work₀ queryIdx).HasBinaryString queryBits)
    (hqueryStart : (work₀ queryIdx).cells 0 = Γ.start)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ addressIdx → i ≠ queryIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start ∧ 1 ≤ (work₀ i).head)
    (houtput : out₀.read ≠ Γ.start) (houtputHead : 1 ≤ out₀.head) :
    ∃ c' t,
      t ≤ decodedAddressEqTime addressBits queryBits ∧
      (decodedAddressEqTM addressIdx queryIdx resultIdx).reachesIn t
        { state := (decodedAddressEqTM addressIdx queryIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (decodedAddressEqTM addressIdx queryIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work resultIdx).HasBinaryPrefix
        [decide (addressBits = queryBits)] ∧
      (c'.work addressIdx).HasBinaryContent addressBits ∧
      1 ≤ (c'.work addressIdx).head ∧
      (c'.work addressIdx).cells 0 = Γ.start ∧
      (c'.work queryIdx).HasBinaryContent queryBits ∧
      1 ≤ (c'.work queryIdx).head ∧
      (c'.work queryIdx).cells 0 = Γ.start ∧
      (∀ i, i ≠ addressIdx → i ≠ queryIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  decodedAddressEqTM_reachesIn_frame_internal addressIdx queryIdx resultIdx
    hdistinct addressBits queryBits inp₀ work₀ out₀ haddress haddressStart
      hquery hqueryStart hresult hinput hother houtput houtputHead

/-- Coarse all-prefix auxiliary-space envelope for decoded-address equality. -/
theorem decodedAddressEqTM_prefix_withinAuxSpace {n : ℕ}
    (addressIdx queryIdx resultIdx : Fin n) (addressBits queryBits : List Bool)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n
      (decodedAddressEqTM addressIdx queryIdx resultIdx).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (decodedAddressEqTM addressIdx queryIdx resultIdx).reachesIn
      time start current)
    (htime : time ≤ decodedAddressEqTime addressBits queryBits) :
    current.WithinAuxSpace inputLength
      (initialSpace + decodedAddressEqTime addressBits queryBits) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- Decoded-address equality preserves one-way output safety. -/
theorem decodedAddressEqTM_isTransducer {n : ℕ}
    (addressIdx queryIdx resultIdx : Fin n) :
    (decodedAddressEqTM addressIdx queryIdx resultIdx).IsTransducer := by
  unfold decodedAddressEqTM
  exact (TM.rewindWorkTM_isTransducer addressIdx).seqTM
    (TM.binaryEqTM_isTransducer addressIdx queryIdx resultIdx)

end Machine

end RegisterStore

end RAM

end Complexity
