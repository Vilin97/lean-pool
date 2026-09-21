/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.GateEval.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.GateEval.Internal
public import LeanPool.BeyondBethe.Complexitylib.Asymptotics
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured

/-!
# Verified structured RAM decoded-gate evaluator

This module exposes the mutable-data kernel used by the serialized-circuit
evaluator. Given an already-decoded, topologically valid gate, it performs two
indirect memo reads, evaluates the gate with branch-free Boolean arithmetic,
and indirectly appends the result in exactly twenty RAM transitions.
-/


public section

namespace Complexity

namespace RAM

namespace Structured

namespace GateEval

/-- Evaluate a decoded gate in any store satisfying the routine ABI.

The memo may be located above an arbitrary base address; the result is appended
there and every prior memo cell is preserved. -/
theorem routine_correct {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    ∃ final cost space,
      Exec program store final stepCount cost space ∧
      final outputReg = Input.bitValue (gate.eval value0 value1) ∧
      final (base + wires.length) = Input.bitValue (gate.eval value0 value1) ∧
      final baseReg = base ∧ final wireCountReg = wires.length ∧
      (∀ index (hindex : index < wires.length),
        final (base + index) = Input.bitValue wires[index]) ∧
      ∀ index, wireBase ≤ index → index ≠ base + wires.length →
        final index = store index :=
  routine_exec_internal hready value0 value1 hvalue0 hvalue1

/-- Source-level correctness with exact transitions and explicit resources. -/
theorem program_performance (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1)
    (hgate : gate.WellFormedAt wires.length) :
    ∃ final cost space,
      Exec program (inputStore gate wires) final stepCount cost space ∧
      cost ≤ timeBound wires.length ∧ space ≤ spaceBound wires.length ∧
      final outputReg = Input.bitValue (gate.eval value0 value1) ∧
      final (wireBase + wires.length) = Input.bitValue (gate.eval value0 value1) ∧
      ∀ index (hindex : index < wires.length),
        final (wireBase + index) = Input.bitValue wires[index] :=
  program_measured_internal gate wires value0 value1 hvalue0 hvalue1 hgate

/-- End-to-end concrete RAM performance and decoded-gate correctness. -/
theorem compiled_performance (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1)
    (hgate : gate.WellFormedAt wires.length) :
    ∃ final cost space,
      Exec program (inputStore gate wires) final stepCount cost space ∧
      run compiled stepCount { pc := 0, regs := inputStore gate wires } =
        { pc := program.codeSize, regs := final } ∧
      Halted compiled
        (run compiled stepCount { pc := 0, regs := inputStore gate wires }) ∧
      logTimeUpto compiled stepCount
          { pc := 0, regs := inputStore gate wires } ≤ timeBound wires.length ∧
      spaceUpto compiled stepCount
          { pc := 0, regs := inputStore gate wires } ≤ spaceBound wires.length ∧
      final outputReg = Input.bitValue (gate.eval value0 value1) ∧
      final (wireBase + wires.length) = Input.bitValue (gate.eval value0 value1) ∧
      ∀ index (hindex : index < wires.length),
        final (wireBase + index) = Input.bitValue wires[index] := by
  obtain ⟨final, cost, space, hexec, hcost, hspace, hresult, happended,
      hpreserved⟩ :=
    program_performance gate wires value0 value1 hvalue0 hvalue1 hgate
  have hcompiled := Exec.compile_correct hexec
  refine ⟨final, cost, space, hexec, hcompiled.1, Exec.compile_halted hexec,
    ?_, ?_, hresult, happended, hpreserved⟩
  · change logTimeUpto program.compile stepCount
        { pc := 0, regs := inputStore gate wires } ≤ timeBound wires.length
    rw [hcompiled.2.1]
    exact hcost
  · change spaceUpto program.compile stepCount
        { pc := 0, regs := inputStore gate wires } ≤ spaceBound wires.length
    rw [hcompiled.2.2]
    exact hspace

/-- One decoded gate takes logarithmic time in the current memo length. -/
theorem timeBound_bigO_logarithmic : timeBound =O logarithmicBound := by
  have hpoint : ∀ n, timeBound n ≤ 80 * logarithmicBound n := by
    intro n
    simp [timeBound, logarithmicBound]
  exact (BigO.of_le hpoint).trans
    (BigO.const_mul_left 80 (BigO.refl logarithmicBound))

/-- The explicit memo-space budget is quasilinear. -/
theorem spaceBound_bigO_quasilinear : spaceBound =O quasilinearBound := by
  have hpoint : ∀ n, spaceBound n ≤ 2 * quasilinearBound n := by
    intro n
    simp only [spaceBound, quasilinearBound]
    calc
      (n + wireBase + 1) * (2 * bitlen (n + wireBase + 1)) =
          2 * ((n + wireBase + 1) * bitlen (n + wireBase + 1)) := by ring
      _ ≤ 2 * ((n + wireBase + 1) *
          (bitlen (n + wireBase + 1) + 1)) :=
        Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_left (n + wireBase + 1) (by omega))
  exact (BigO.of_le hpoint).trans
    (BigO.const_mul_left 2 (BigO.refl quasilinearBound))

end GateEval

end Structured

end RAM

end Complexity
