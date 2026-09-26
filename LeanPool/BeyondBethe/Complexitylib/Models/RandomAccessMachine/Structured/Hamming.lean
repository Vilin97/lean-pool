/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Hamming.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Hamming.Internal
public import LeanPool.BeyondBethe.Complexitylib.Asymptotics
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured

/-!
# Verified structured RAM Hamming weight

`Hamming.program` is a structured imperative program over the reserved-register
layout `Hamming.inputStore`. Its correctness and resource bounds are proved in
the independent source semantics. `Hamming.compiled_performance` then applies
the generic compiler theorem, carrying the result to the concrete logarithmic-cost
RAM with an exact transition count, explicit length-indexed budgets, and
quasilinear asymptotic corollaries.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace Hamming

/-- Source-level correctness with an exact transition count and explicit
logarithmic-cost time and peak-space bounds. -/
theorem program_performance (bits : List Bool) :
    ∃ final cost space,
      Exec program (inputStore bits) final (stepCount bits) cost space ∧
      cost ≤ timeBound bits.length ∧ space ≤ spaceBound bits.length ∧
      final lengthReg = weight bits :=
  program_measured_internal bits

/-- End-to-end compiled performance theorem. The concrete RAM reaches its halt
instruction after exactly `stepCount bits` transitions, within the explicit
logarithmic-cost time and peak-space budgets, and returns the Hamming weight. -/
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
      (run compiled (stepCount bits) { pc := 0, regs := inputStore bits }).regs
          lengthReg = weight bits := by
  obtain ⟨final, cost, space, hexec, hcost, hspace, hresult⟩ :=
    program_performance bits
  have hcompiled := Exec.compile_correct hexec
  refine ⟨final, cost, space, hexec, hcompiled.1, Exec.compile_halted hexec,
    ?_, ?_, ?_⟩
  · change logTimeUpto program.compile (stepCount bits)
        { pc := 0, regs := inputStore bits } ≤ timeBound bits.length
    rw [hcompiled.2.1]
    exact hcost
  · change spaceUpto program.compile (stepCount bits)
        { pc := 0, regs := inputStore bits } ≤ spaceBound bits.length
    rw [hcompiled.2.2]
    exact hspace
  · change (run program.compile (stepCount bits)
        { pc := 0, regs := inputStore bits }).regs lengthReg = weight bits
    rw [hcompiled.1]
    exact hresult

/-- The explicit logarithmic-cost time budget is quasilinear. -/
theorem timeBound_bigO_quasilinear : timeBound =O quasilinearBound := by
  have hpoint : ∀ n, timeBound n ≤ 64 * quasilinearBound n := by
    intro n
    simp only [timeBound, quasilinearBound]
    have hshift : n + 1 ≤ n + 5 := by omega
    calc
      64 * (n + 1) * (bitlen (n + 5) + 1)
          = 64 * ((n + 1) * (bitlen (n + 5) + 1)) := by ring
      _ ≤ 64 * ((n + 5) * (bitlen (n + 5) + 1)) :=
        Nat.mul_le_mul_left 64
          (Nat.mul_le_mul_right (bitlen (n + 5) + 1) hshift)
  exact (BigO.of_le hpoint).trans
    (BigO.const_mul_left 64 (BigO.refl quasilinearBound))

/-- The explicit peak-space budget is quasilinear under the reserved-register
input representation. -/
theorem spaceBound_bigO_quasilinear : spaceBound =O quasilinearBound := by
  have hpoint : ∀ n, spaceBound n ≤ 2 * quasilinearBound n := by
    intro n
    simp only [spaceBound, quasilinearBound]
    calc
      (n + 5) * (2 * bitlen (n + 5))
          = 2 * ((n + 5) * bitlen (n + 5)) := by ring
      _ ≤ 2 * ((n + 5) * (bitlen (n + 5) + 1)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (n + 5) (by omega))
  exact (BigO.of_le hpoint).trans
    (BigO.const_mul_left 2 (BigO.refl quasilinearBound))

end Hamming

end Structured

end RAM

end Complexity
