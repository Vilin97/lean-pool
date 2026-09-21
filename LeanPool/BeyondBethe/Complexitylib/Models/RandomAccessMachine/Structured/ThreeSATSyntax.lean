/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.ThreeSATSyntax.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Scanner

/-!
# Verified structured RAM exact-3-CNF syntax scanner

The generic typed-scanner compiler supplies the entire implementation proof and
resource analysis for the existing 27-state `SAT.ThreeSAT.Syntax` automaton.
-/


public section

namespace Complexity

namespace RAM

namespace Structured

namespace ThreeSATSyntax

open SAT.ThreeSAT

/-- The 27-state syntax scanner takes exactly `90 + 9n` transitions. -/
@[simp] theorem stepCount_eq (inputLength : ℕ) :
    stepCount inputLength = 90 + 9 * inputLength := by
  rfl

/-- Source correctness and explicit resource bounds for syntax recognition. -/
theorem program_performance (bits : List Bool) :
    ∃ final cost space,
      Exec program (inputStore bits) final (stepCount bits.length) cost space ∧
      cost ≤ timeBound bits.length ∧ space ≤ spaceBound bits.length ∧
      final verdictReg = Input.bitValue
        (Syntax.accept (bits.foldl Syntax.bitStep Syntax.bitStart)) :=
  Scanner.typed_program_performance spec bits

/-- End-to-end compiled performance and syntax-language correctness. -/
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
      ((run compiled (stepCount bits.length)
          { pc := 0, regs := inputStore bits }).regs verdictReg = 1 ↔
        bits ∈ Syntax.language) := by
  obtain ⟨final, cost, space, hexec, hrun, hhalt, htime, hspace, hresult⟩ :=
    Scanner.typed_compiled_performance spec bits
  refine ⟨final, cost, space, hexec, hrun, hhalt, htime, hspace, ?_⟩
  rw [hresult]
  change Input.bitValue
    (Syntax.accept (bits.foldl Syntax.bitStep Syntax.bitStart)) = 1 ↔
      Syntax.accept (bits.foldl Syntax.bitStep Syntax.bitStart) = true
  cases Syntax.accept (bits.foldl Syntax.bitStep Syntax.bitStart) <;>
    simp [Input.bitValue]

/-- The explicit logarithmic-time budget is quasilinear. -/
theorem timeBound_bigO_quasilinear : timeBound =O quasilinearBound :=
  Scanner.typed_timeBound_bigO_quasilinear spec

/-- The explicit peak-space budget is quasilinear. -/
theorem spaceBound_bigO_quasilinear : spaceBound =O quasilinearBound :=
  Scanner.typed_spaceBound_bigO_quasilinear spec

end ThreeSATSyntax

end Structured

end RAM

end Complexity
