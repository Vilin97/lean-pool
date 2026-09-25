/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.UnaryDecode.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.UnaryDecode.Internal
public import LeanPool.BeyondBethe.Complexitylib.Asymptotics
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured

/-!
# Verified structured RAM terminated-unary decoder

This module exposes a reusable cursor decoder for the unary fields used by the
serialized-circuit format. The source proof covers both successful termination
and input exhaustion, and compilation preserves its exact transition count,
logarithmic cost, peak space, decoded value, and suffix cursor.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace UnaryDecode

/-- Invoke the decoder loop as a resource-bounded cursor routine.

Unlike `program_performance`, this theorem does not require the standalone
input initializer. It can therefore be sequenced after another parser step.
The loop preserves every data register at or above `inputBase`. -/
theorem mainLoop_performance {remaining : List Bool}
    {inputLength offset value : ℕ} {store : Store}
    (hready : CursorReady inputLength remaining offset value store)
    (hbound : Internal.StoreEnvelope (inputLength + inputBase)
      (inputLength + inputBase) store) :
    ∃ final cost space,
      Exec mainLoop store final (loopStepCount remaining) cost space ∧
      cost ≤ timeBound inputLength ∧ space ≤ spaceBound inputLength ∧
      (match CircuitCode.NatCode.decodePrefix? remaining with
      | none =>
          final verdictReg = 0 ∧ final valueReg = value + remaining.length ∧
          final pointerReg = inputBase + inputLength ∧ final remainingReg = 0
      | some (decoded, rest) =>
          final verdictReg = 1 ∧ final valueReg = value + decoded ∧
          final pointerReg = inputBase + offset + decoded + 1 ∧
          final remainingReg = rest.length) ∧
      final activeReg = 0 ∧
      final oneReg = 1 ∧
      (∀ index, inputBase ≤ index → final index = store index) ∧
      Internal.StoreEnvelope (inputLength + inputBase)
        (inputLength + inputBase) final :=
  mainLoop_measured_internal hready hbound

/-- Source-level correctness with exact transitions and explicit resources. -/
theorem program_performance (bits : List Bool) :
    ∃ final cost space,
      Exec program (inputStore bits) final (stepCount bits) cost space ∧
      cost ≤ timeBound bits.length ∧ space ≤ spaceBound bits.length ∧
      match CircuitCode.NatCode.decodePrefix? bits with
      | none =>
          final verdictReg = 0 ∧ final valueReg = bits.length ∧
          final pointerReg = inputBase + bits.length ∧ final remainingReg = 0
      | some (value, rest) =>
          final verdictReg = 1 ∧ final valueReg = value ∧
          final pointerReg = inputBase + value + 1 ∧
          final remainingReg = rest.length :=
  program_measured_internal bits

/-- End-to-end concrete RAM performance and terminated-unary correctness. -/
theorem compiled_performance (bits : List Bool) :
    ∃ final cost space,
      Exec program (inputStore bits) final (stepCount bits) cost space ∧
      run compiled (stepCount bits) { pc := 0, regs := inputStore bits } =
        { pc := program.codeSize, regs := final } ∧
      Halted compiled
        (run compiled (stepCount bits) { pc := 0, regs := inputStore bits }) ∧
      logTimeUpto compiled (stepCount bits)
          { pc := 0, regs := inputStore bits } ≤ timeBound bits.length ∧
      spaceUpto compiled (stepCount bits)
          { pc := 0, regs := inputStore bits } ≤ spaceBound bits.length ∧
      match CircuitCode.NatCode.decodePrefix? bits with
      | none =>
          final verdictReg = 0 ∧ final valueReg = bits.length ∧
          final pointerReg = inputBase + bits.length ∧ final remainingReg = 0
      | some (value, rest) =>
          final verdictReg = 1 ∧ final valueReg = value ∧
          final pointerReg = inputBase + value + 1 ∧
          final remainingReg = rest.length := by
  obtain ⟨final, cost, space, hexec, hcost, hspace, hresult⟩ :=
    program_performance bits
  have hcompiled := Exec.compile_correct hexec
  refine ⟨final, cost, space, hexec, hcompiled.1, Exec.compile_halted hexec,
    ?_, ?_, hresult⟩
  · change logTimeUpto program.compile (stepCount bits)
        { pc := 0, regs := inputStore bits } ≤ timeBound bits.length
    rw [hcompiled.2.1]
    exact hcost
  · change spaceUpto program.compile (stepCount bits)
        { pc := 0, regs := inputStore bits } ≤ spaceBound bits.length
    rw [hcompiled.2.2]
    exact hspace

/-- The explicit logarithmic-cost time budget is quasilinear. -/
theorem timeBound_bigO_quasilinear : timeBound =O quasilinearBound := by
  have hpoint : ∀ n, timeBound n ≤ 96 * quasilinearBound n := by
    intro n
    simp only [timeBound, quasilinearBound]
    have hshift : n + 1 ≤ n + inputBase := by simp [inputBase]
    calc
      96 * (n + 1) * (bitlen (n + inputBase) + 1)
          = 96 * ((n + 1) * (bitlen (n + inputBase) + 1)) := by ring
      _ ≤ 96 * ((n + inputBase) * (bitlen (n + inputBase) + 1)) :=
        Nat.mul_le_mul_left 96
          (Nat.mul_le_mul_right (bitlen (n + inputBase) + 1) hshift)
  exact (BigO.of_le hpoint).trans
    (BigO.const_mul_left 96 (BigO.refl quasilinearBound))

/-- The explicit peak-space budget is quasilinear. -/
theorem spaceBound_bigO_quasilinear : spaceBound =O quasilinearBound := by
  have hpoint : ∀ n, spaceBound n ≤ 2 * quasilinearBound n := by
    intro n
    simp only [spaceBound, quasilinearBound]
    calc
      (n + inputBase) * (2 * bitlen (n + inputBase))
          = 2 * ((n + inputBase) * bitlen (n + inputBase)) := by ring
      _ ≤ 2 * ((n + inputBase) * (bitlen (n + inputBase) + 1)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (n + inputBase) (by omega))
  exact (BigO.of_le hpoint).trans
    (BigO.const_mul_left 2 (BigO.refl quasilinearBound))

end UnaryDecode

end Structured

end RAM

end Complexity
