/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseSimDefs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

/-!
# Dense-overlay RAM program controller -- definitions
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- Recover dense register `R₀` through the overlay-aware lookup and emit its
Boolean verdict on the real output tape. -/
def denseProgramOutputTM {n : ℕ} (tapes : ControlInstructionTapes n) :
    TM (n + 1) :=
  TM.seqTM (denseOverlayLookupStaticTM tapes.lifted.data.lhsLookup 0)
    (registerVerdictTM tapes.liftedLhs)

/-- Exact dense final-verdict extraction bound. -/
def denseProgramOutputTime {n : ℕ} (tapes : ControlInstructionTapes n)
    (input : List Bool) (overlay : Store) : ℕ :=
  denseOverlayLookupStaticTime tapes.lifted.data.lhsLookup input.length
    overlay 0 + 1 + 1

/-- Fixed halt-aware loop for one concrete RAM program using dense overlay
steps and the representation-independent halt test. -/
def denseProgramLoopTM {n : ℕ} (tapes : ControlInstructionTapes n)
    (program : Program) : TM (n + 1) :=
  TM.loopTM (denseProgramStepTM tapes program) (programHaltTM tapes program)

/-- Bound for one dense loop body, halt test, their seams, and the three-step
rewind/check tail. -/
noncomputable def denseProgramLoopIterationTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot) : ℕ :=
  let next := snapshot.step program input
  denseProgramStepTime tapes program input snapshot.pc snapshot.overlay + 1 +
    programHaltTime tapes program next.pc + 1 + 3

/-- Sum of the first `fuel` dense loop-iteration bounds. -/
noncomputable def denseProgramLoopTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) : ℕ → DenseOverlay.Snapshot → ℕ
  | 0, _ => 0
  | fuel + 1, snapshot =>
      denseProgramLoopIterationTime tapes program input snapshot +
        denseProgramLoopTime tapes program input fuel
          (snapshot.step program input)

end Machine
end RegisterStore
end RAM
end Complexity
