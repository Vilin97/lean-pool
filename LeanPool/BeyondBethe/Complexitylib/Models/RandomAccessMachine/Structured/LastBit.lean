/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.LastBit.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Scanner
public import LeanPool.BeyondBethe.Complexitylib.Languages.LastBit

/-!
# Verified structured RAM last-bit scanner

The typed scanner compiler supplies the implementation, exact execution proof,
and resource bounds. This module adds only agreement with the existing
`Language.lastBitZero` and `Language.lastBitOne` specifications.
-/


public section

namespace Complexity

namespace RAM

namespace Structured

namespace LastBit

/-- The three-state last-bit scanner takes exactly `18 + 9n` transitions. -/
@[simp] theorem stepCount_eq (target : Bool) (inputLength : ℕ) :
    stepCount target inputLength = 18 + 9 * inputLength := by
  rfl

/-- Source correctness and explicit resource bounds for the last-bit scanner. -/
theorem program_performance (target : Bool) (bits : List Bool) :
    ∃ final cost space,
      Exec (program target) (inputStore target bits) final
          (stepCount target bits.length) cost space ∧
      cost ≤ timeBound target bits.length ∧
      space ≤ spaceBound target bits.length ∧
      final verdictReg = Input.bitValue (decide (bits.getLast? = some target)) := by
  simpa [spec, lastBit_fold_eq_getLast?] using
    Scanner.typed_program_performance (spec target) bits

/-- End-to-end compiled performance and language correctness. -/
theorem compiled_performance (target : Bool) (bits : List Bool) :
    ∃ final cost space,
      Exec (program target) (inputStore target bits) final
          (stepCount target bits.length) cost space ∧
      run (compiled target) (stepCount target bits.length)
          { pc := 0, regs := inputStore target bits } =
        { pc := (program target).codeSize, regs := final } ∧
      Halted (compiled target)
        (run (compiled target) (stepCount target bits.length)
          { pc := 0, regs := inputStore target bits }) ∧
      logTimeUpto (compiled target) (stepCount target bits.length)
          { pc := 0, regs := inputStore target bits } ≤ timeBound target bits.length ∧
      spaceUpto (compiled target) (stepCount target bits.length)
          { pc := 0, regs := inputStore target bits } ≤ spaceBound target bits.length ∧
      ((run (compiled target) (stepCount target bits.length)
          { pc := 0, regs := inputStore target bits }).regs verdictReg = 1 ↔
        bits.getLast? = some target) := by
  obtain ⟨final, cost, space, hexec, hrun, hhalt, htime, hspace, hresult⟩ :=
    Scanner.typed_compiled_performance (spec target) bits
  refine ⟨final, cost, space, hexec, hrun, hhalt, htime, hspace, ?_⟩
  rw [show (run (compiled target) (stepCount target bits.length)
      { pc := 0, regs := inputStore target bits }).regs verdictReg =
        Input.bitValue (decide (bits.getLast? = some target)) by
      simpa [spec, lastBit_fold_eq_getLast?] using hresult]
  simp [Input.bitValue]

/-- The explicit time budget is quasilinear. -/
theorem timeBound_bigO_quasilinear (target : Bool) :
    timeBound target =O quasilinearBound target :=
  Scanner.typed_timeBound_bigO_quasilinear (spec target)

/-- The explicit peak-space budget is quasilinear. -/
theorem spaceBound_bigO_quasilinear (target : Bool) :
    spaceBound target =O quasilinearBound target :=
  Scanner.typed_spaceBound_bigO_quasilinear (spec target)

end LastBit

end Structured

end RAM

end Complexity
