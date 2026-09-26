/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Init.Defs

/-!
# Complete sparse RAM decision machine -- definitions
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Initialize the public RAM configuration, execute one fixed program through
its first halt, and extract the Boolean verdict from sparse register `R₀`. -/
def programDecisionTM {n : ℕ} (tapes : ControlInstructionTapes n)
    (program : Program) : TM (n + 1) :=
  TM.seqTM (programInitTM tapes)
    (TM.seqTM (programLoopTM tapes program) (programOutputTM tapes))

/-- Exact compositional bound for one fuel-certified RAM decision run. -/
noncomputable def programDecisionTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (fuel : ℕ) : ℕ :=
  let initial := programInitialSnapshot input
  let final := initial.run program fuel
  programInitTime tapes input + 1 +
    (programLoopTime tapes program (fuel + 1) initial + 1 +
      programOutputTime tapes final.store)

end Machine

end RegisterStore

end RAM

end Complexity
