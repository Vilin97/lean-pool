/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.PairValidate.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.PairValidate.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Scanner
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.PairValidate

/-!
# Verified structured RAM pair validator

This table-driven RAM program reimplements the same five-state automaton as
`TM.pairValidateTM`. Its proof gives an exact transition count, explicit
logarithmic-cost time and peak-space budgets, and an end-to-end compiled-RAM
correctness theorem for the canonical pair-encoding language.
-/


public section

namespace Complexity

namespace RAM

namespace Structured

namespace PairValidate

/-- The five-state pair validator takes exactly `24 + 9n` transitions. -/
@[simp] theorem stepCount_eq (inputLength : ℕ) :
    stepCount inputLength = 24 + 9 * inputLength := by
  rfl

/-- Source-level correctness and explicit resource bounds. -/
theorem program_performance (bits : List Bool) :
    ∃ final cost space,
      Exec program (inputStore bits) final (stepCount bits.length) cost space ∧
      cost ≤ timeBound bits.length ∧ space ≤ spaceBound bits.length ∧
      final lengthReg = Input.bitValue
        (TM.pairValidateAccept (bits.foldl TM.pairValidateStep .next)) :=
  program_measured_internal bits

/-- End-to-end compiled performance and language correctness. -/
theorem compiled_performance (bits : List Bool) :
    ∃ final cost space,
      Exec program (inputStore bits) final (stepCount bits.length) cost space ∧
      run compiled (stepCount bits.length) { pc := 0, regs := inputStore bits } =
        { pc := program.codeSize, regs := final } ∧
      Halted compiled
        (run compiled (stepCount bits.length) { pc := 0, regs := inputStore bits }) ∧
      logTimeUpto compiled (stepCount bits.length)
          { pc := 0, regs := inputStore bits } ≤ timeBound bits.length ∧
      spaceUpto compiled (stepCount bits.length)
          { pc := 0, regs := inputStore bits } ≤ spaceBound bits.length ∧
      (run compiled (stepCount bits.length) { pc := 0, regs := inputStore bits }).regs
          lengthReg = Input.bitValue
            (TM.pairValidateAccept (bits.foldl TM.pairValidateStep .next)) ∧
      ((run compiled (stepCount bits.length)
          { pc := 0, regs := inputStore bits }).regs lengthReg = 1 ↔
        bits ∈ validPairEncoding) := by
  obtain ⟨final, cost, space, hexec, hcost, hspace, hresult⟩ :=
    program_performance bits
  have hcompiled := Exec.compile_correct hexec
  refine ⟨final, cost, space, hexec, hcompiled.1, Exec.compile_halted hexec,
    ?_, ?_, ?_, ?_⟩
  · change logTimeUpto program.compile (stepCount bits.length)
        { pc := 0, regs := inputStore bits } ≤ timeBound bits.length
    rw [hcompiled.2.1]
    exact hcost
  · change spaceUpto program.compile (stepCount bits.length)
        { pc := 0, regs := inputStore bits } ≤ spaceBound bits.length
    rw [hcompiled.2.2]
    exact hspace
  · change (run program.compile (stepCount bits.length)
        { pc := 0, regs := inputStore bits }).regs lengthReg = _
    rw [hcompiled.1]
    exact hresult
  · change (run program.compile (stepCount bits.length)
        { pc := 0, regs := inputStore bits }).regs lengthReg = 1 ↔ _
    rw [hcompiled.1]
    change final lengthReg = 1 ↔ _
    rw [hresult]
    calc
      Input.bitValue (TM.pairValidateAccept
            (bits.foldl TM.pairValidateStep .next)) = 1 ↔
          TM.pairValidateAccept (bits.foldl TM.pairValidateStep .next) = true := by
            cases TM.pairValidateAccept (bits.foldl TM.pairValidateStep .next) <;>
              simp [Input.bitValue]
      _ ↔ (unpair? bits).isSome = true :=
        TM.pairValidateAccept_fold_eq_true_iff bits
      _ ↔ bits ∈ validPairEncoding := Iff.rfl

/-- The explicit logarithmic-cost time budget is quasilinear. -/
theorem timeBound_bigO_quasilinear : timeBound =O quasilinearBound := by
  exact Scanner.timeBound_bigO_quasilinear spec

/-- The explicit peak-space budget is quasilinear. -/
theorem spaceBound_bigO_quasilinear : spaceBound =O quasilinearBound := by
  exact Scanner.spaceBound_bigO_quasilinear spec

end PairValidate

end Structured

end RAM

end Complexity
