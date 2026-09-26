/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseDefs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseInitDefs

/-!
# Complete dense-overlay RAM decision machine -- definitions
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- Initialize the immutable public-input bank and one-entry overlay, execute
one fixed program through its first halt, and extract decoded `R₀`. -/
def denseProgramDecisionTM {n : ℕ} (tapes : ControlInstructionTapes n)
    (program : Program) : TM (n + 1) :=
  TM.seqTM (denseProgramInitTM tapes)
    (TM.seqTM (denseProgramLoopTM tapes program)
      (denseProgramOutputTM tapes))

/-- Exact compositional bound for one fuel-certified dense RAM decision run. -/
noncomputable def denseProgramDecisionTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (fuel : ℕ) : ℕ :=
  let initial := DenseOverlay.Snapshot.initial input
  let final := initial.run program input fuel
  denseProgramInitTime tapes input + 1 +
    (denseProgramLoopTime tapes program input (fuel + 1) initial + 1 +
      denseProgramOutputTime tapes input final.overlay)

end Machine
end RegisterStore
end RAM
end Complexity
