/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Scanner.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Scanner.Internal
public import LeanPool.BeyondBethe.Complexitylib.Asymptotics
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured

/-!
# Verified finite-state structured RAM scanners

This module exposes a reusable compiler from numeric finite automata to the
structured RAM frontend. Its correctness theorem includes an exact transition
count and explicit logarithmic-time and peak-space bounds, all transferred to
the concrete compiled RAM.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace Scanner

/-- Source-level correctness and explicit resource bounds. -/
theorem program_performance (spec : Spec) (bits : List Bool) :
    ∃ final cost space,
      Exec (program spec) (inputStore spec bits) final
          (stepCount spec bits.length) cost space ∧
      cost ≤ timeBound spec bits.length ∧
      space ≤ spaceBound spec bits.length ∧
      final lengthReg = Input.bitValue
        (spec.accept (bits.foldl spec.step spec.initial)) :=
  program_measured_internal spec bits

/-- End-to-end performance and correctness of the compiled concrete RAM. -/
theorem compiled_performance (spec : Spec) (bits : List Bool) :
    ∃ final cost space,
      Exec (program spec) (inputStore spec bits) final
          (stepCount spec bits.length) cost space ∧
      run (compiled spec) (stepCount spec bits.length)
          { pc := 0, regs := inputStore spec bits } =
        { pc := (program spec).codeSize, regs := final } ∧
      Halted (compiled spec)
        (run (compiled spec) (stepCount spec bits.length)
          { pc := 0, regs := inputStore spec bits }) ∧
      logTimeUpto (compiled spec) (stepCount spec bits.length)
          { pc := 0, regs := inputStore spec bits } ≤ timeBound spec bits.length ∧
      spaceUpto (compiled spec) (stepCount spec bits.length)
          { pc := 0, regs := inputStore spec bits } ≤ spaceBound spec bits.length ∧
      (run (compiled spec) (stepCount spec bits.length)
          { pc := 0, regs := inputStore spec bits }).regs lengthReg =
        Input.bitValue (spec.accept (bits.foldl spec.step spec.initial)) := by
  obtain ⟨final, cost, space, hexec, hcost, hspace, hresult⟩ :=
    program_performance spec bits
  have hcompiled := Exec.compile_correct hexec
  refine ⟨final, cost, space, hexec, hcompiled.1, Exec.compile_halted hexec,
    ?_, ?_, ?_⟩
  · change logTimeUpto (program spec).compile (stepCount spec bits.length)
        { pc := 0, regs := inputStore spec bits } ≤ timeBound spec bits.length
    rw [hcompiled.2.1]
    exact hcost
  · change spaceUpto (program spec).compile (stepCount spec bits.length)
        { pc := 0, regs := inputStore spec bits } ≤ spaceBound spec bits.length
    rw [hcompiled.2.2]
    exact hspace
  · change (run (program spec).compile (stepCount spec bits.length)
        { pc := 0, regs := inputStore spec bits }).regs lengthReg = _
    rw [hcompiled.1]
    exact hresult

/-- Source-level correctness and resource bounds for a typed scanner. -/
theorem typed_program_performance {State : Type} [FinEnum State]
    (typed : TypedSpec State) (bits : List Bool) :
    ∃ final cost space,
      Exec typed.program (typed.inputStore bits) final
          (typed.stepCount bits.length) cost space ∧
      cost ≤ typed.timeBound bits.length ∧
      space ≤ typed.spaceBound bits.length ∧
      final lengthReg = Input.bitValue
        (typed.accept (bits.foldl typed.step typed.initial)) :=
  typed_program_measured_internal typed bits

/-- End-to-end concrete RAM correctness for a typed scanner. -/
theorem typed_compiled_performance {State : Type} [FinEnum State]
    (typed : TypedSpec State) (bits : List Bool) :
    ∃ final cost space,
      Exec typed.program (typed.inputStore bits) final
          (typed.stepCount bits.length) cost space ∧
      run typed.compiled (typed.stepCount bits.length)
          { pc := 0, regs := typed.inputStore bits } =
        { pc := typed.program.codeSize, regs := final } ∧
      Halted typed.compiled
        (run typed.compiled (typed.stepCount bits.length)
          { pc := 0, regs := typed.inputStore bits }) ∧
      logTimeUpto typed.compiled (typed.stepCount bits.length)
          { pc := 0, regs := typed.inputStore bits } ≤ typed.timeBound bits.length ∧
      spaceUpto typed.compiled (typed.stepCount bits.length)
          { pc := 0, regs := typed.inputStore bits } ≤ typed.spaceBound bits.length ∧
      (run typed.compiled (typed.stepCount bits.length)
          { pc := 0, regs := typed.inputStore bits }).regs lengthReg =
        Input.bitValue (typed.accept (bits.foldl typed.step typed.initial)) := by
  obtain ⟨final, cost, space, hexec, hcost, hspace, hresult⟩ :=
    typed_program_performance typed bits
  have hcompiled := Exec.compile_correct hexec
  refine ⟨final, cost, space, hexec, hcompiled.1, Exec.compile_halted hexec,
    ?_, ?_, ?_⟩
  · change logTimeUpto typed.program.compile (typed.stepCount bits.length)
        { pc := 0, regs := typed.inputStore bits } ≤ typed.timeBound bits.length
    rw [hcompiled.2.1]
    exact hcost
  · change spaceUpto typed.program.compile (typed.stepCount bits.length)
        { pc := 0, regs := typed.inputStore bits } ≤ typed.spaceBound bits.length
    rw [hcompiled.2.2]
    exact hspace
  · change (run typed.program.compile (typed.stepCount bits.length)
        { pc := 0, regs := typed.inputStore bits }).regs lengthReg = _
    rw [hcompiled.1]
    exact hresult

/-- For each fixed scanner, its explicit time budget is quasilinear. -/
theorem timeBound_bigO_quasilinear (spec : Spec) :
    timeBound spec =O quasilinearBound spec := by
  have hpoint : ∀ n, timeBound spec n ≤ 64 * quasilinearBound spec n := by
    intro n
    simp only [timeBound, quasilinearBound]
    have hshift : n + spec.stateCount + 1 ≤ n + inputBase spec := by
      simp [inputBase, transitionBase]
      omega
    calc
      64 * (n + spec.stateCount + 1) *
            (bitlen (n + inputBase spec) + 1)
          = 64 * ((n + spec.stateCount + 1) *
              (bitlen (n + inputBase spec) + 1)) := by ring
      _ ≤ 64 * ((n + inputBase spec) *
            (bitlen (n + inputBase spec) + 1)) :=
        Nat.mul_le_mul_left 64
          (Nat.mul_le_mul_right (bitlen (n + inputBase spec) + 1) hshift)
  exact (BigO.of_le hpoint).trans
    (BigO.const_mul_left 64 (BigO.refl (quasilinearBound spec)))

/-- For each fixed scanner, its explicit peak-space budget is quasilinear. -/
theorem spaceBound_bigO_quasilinear (spec : Spec) :
    spaceBound spec =O quasilinearBound spec := by
  have hpoint : ∀ n, spaceBound spec n ≤ 2 * quasilinearBound spec n := by
    intro n
    simp only [spaceBound, quasilinearBound]
    calc
      (n + inputBase spec) * (2 * bitlen (n + inputBase spec))
          = 2 * ((n + inputBase spec) * bitlen (n + inputBase spec)) := by ring
      _ ≤ 2 * ((n + inputBase spec) *
            (bitlen (n + inputBase spec) + 1)) :=
        Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_left (n + inputBase spec) (by omega))
  exact (BigO.of_le hpoint).trans
    (BigO.const_mul_left 2 (BigO.refl (quasilinearBound spec)))

/-- The typed scanner's explicit time budget is quasilinear. -/
theorem typed_timeBound_bigO_quasilinear {State : Type} [FinEnum State]
    (typed : TypedSpec State) : typed.timeBound =O typed.quasilinearBound :=
  timeBound_bigO_quasilinear typed.numeric

/-- The typed scanner's explicit peak-space budget is quasilinear. -/
theorem typed_spaceBound_bigO_quasilinear {State : Type} [FinEnum State]
    (typed : TypedSpec State) : typed.spaceBound =O typed.quasilinearBound :=
  spaceBound_bigO_quasilinear typed.numeric

end Scanner

end Structured

end RAM

end Complexity
