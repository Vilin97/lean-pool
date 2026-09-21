/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.GateStep.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.GateStep.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured

/-!
# Verified structured RAM serialized-gate step

This module is the first end-to-end composition of the structured RAM parser
and mutable-data APIs. One fixed program consumes a canonical gate encoding,
invokes the same cursor loop for both unary references, discovers the following
memo base at runtime, evaluates the decoded gate, and appends its result.
-/


public section

namespace Complexity

namespace RAM

namespace Structured

namespace GateStep

/-- Source correctness and exact transition count for one canonical gate. -/
theorem program_correct (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    ∃ final cost space,
      Exec program (inputStore gate wires) final (stepCount gate) cost space ∧
      final GateEval.outputReg = Input.bitValue (gate.eval value0 value1) ∧
      final (memoBase gate + wires.length) =
        Input.bitValue (gate.eval value0 value1) ∧
      ∀ index (hindex : index < wires.length),
        final (memoBase gate + index) = Input.bitValue wires[index] :=
  program_exec_internal gate wires value0 value1 hvalue0 hvalue1

/-- Source correctness, exact transitions, and closed-form logarithmic resource
bounds for one serialized gate and its current memo. -/
theorem program_performance (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    ∃ final cost space,
      Exec program (inputStore gate wires) final (stepCount gate) cost space ∧
      cost ≤ timeBound gate wires ∧ space ≤ spaceBound gate wires ∧
      final GateEval.outputReg = Input.bitValue (gate.eval value0 value1) ∧
      final (memoBase gate + wires.length) =
        Input.bitValue (gate.eval value0 value1) ∧
      ∀ index (hindex : index < wires.length),
        final (memoBase gate + index) = Input.bitValue wires[index] :=
  program_measured_internal gate wires value0 value1 hvalue0 hvalue1

/-- Compilation preserves the exact serialized-gate run and its memo result. -/
theorem compiled_correct (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    ∃ final cost space,
      Exec program (inputStore gate wires) final (stepCount gate) cost space ∧
      run compiled (stepCount gate) { pc := 0, regs := inputStore gate wires } =
        { pc := program.codeSize, regs := final } ∧
      Halted compiled
        (run compiled (stepCount gate) { pc := 0, regs := inputStore gate wires }) ∧
      logTimeUpto compiled (stepCount gate)
        { pc := 0, regs := inputStore gate wires } = cost ∧
      spaceUpto compiled (stepCount gate)
        { pc := 0, regs := inputStore gate wires } = space ∧
      final GateEval.outputReg = Input.bitValue (gate.eval value0 value1) ∧
      final (memoBase gate + wires.length) =
        Input.bitValue (gate.eval value0 value1) ∧
      ∀ index (hindex : index < wires.length),
        final (memoBase gate + index) = Input.bitValue wires[index] := by
  obtain ⟨final, cost, space, hexec, houtput, happended, hpreserved⟩ :=
    program_correct gate wires value0 value1 hvalue0 hvalue1
  have hcompiled := Exec.compile_correct hexec
  exact ⟨final, cost, space, hexec, hcompiled.1, Exec.compile_halted hexec,
    hcompiled.2.1, hcompiled.2.2, houtput, happended, hpreserved⟩

/-- Compilation transfers the serialized-gate result and both source resource
bounds exactly to the concrete logarithmic-cost RAM. -/
theorem compiled_performance (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    ∃ final cost space,
      Exec program (inputStore gate wires) final (stepCount gate) cost space ∧
      cost ≤ timeBound gate wires ∧ space ≤ spaceBound gate wires ∧
      run compiled (stepCount gate) { pc := 0, regs := inputStore gate wires } =
        { pc := program.codeSize, regs := final } ∧
      Halted compiled
        (run compiled (stepCount gate) { pc := 0, regs := inputStore gate wires }) ∧
      logTimeUpto compiled (stepCount gate)
        { pc := 0, regs := inputStore gate wires } = cost ∧
      spaceUpto compiled (stepCount gate)
        { pc := 0, regs := inputStore gate wires } = space ∧
      final GateEval.outputReg = Input.bitValue (gate.eval value0 value1) ∧
      final (memoBase gate + wires.length) =
        Input.bitValue (gate.eval value0 value1) ∧
      ∀ index (hindex : index < wires.length),
        final (memoBase gate + index) = Input.bitValue wires[index] := by
  obtain ⟨final, cost, space, hexec, hcost, hspace,
      houtput, happended, hpreserved⟩ :=
    program_performance gate wires value0 value1 hvalue0 hvalue1
  have hcompiled := Exec.compile_correct hexec
  exact ⟨final, cost, space, hexec, hcost, hspace, hcompiled.1,
    Exec.compile_halted hexec, hcompiled.2.1, hcompiled.2.2,
    houtput, happended, hpreserved⟩

end GateStep

end Structured

end RAM

end Complexity
