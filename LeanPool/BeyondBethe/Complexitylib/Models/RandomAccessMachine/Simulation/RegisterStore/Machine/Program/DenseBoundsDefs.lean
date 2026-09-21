/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Bounds.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

/-!
# Dense-overlay RAM decision-machine resource-bound definitions

The optimized accounting keeps the live serialized overlay separate from the
width charged by the instruction actually selected at the current program
counter. This is the local product that sums quadratically over a run.
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- Width charged by the selected instruction, including the fixed program
literals. -/
def denseStepWidth (program : Program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot) : ℕ :=
  programStaticWidth program +
    RAM.stepLogCost program (snapshot.decode input) + 1

/-- Local amount of serialized data exposed to one dense simulated step. -/
def denseStepVolume (program : Program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot) : ℕ :=
  encodedStoreLength snapshot.overlay + input.length +
    denseStepWidth program input snapshot + 1

/-- Width-sensitive envelope for one selected dense step. The program
magnitude is fixed once the simulated RAM program is fixed. -/
def denseStepEnvelope (program : Program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot) : ℕ :=
  1000000000 * (programResourceMagnitude program + 1) ^ 2 *
    denseStepVolume program input snapshot *
    (denseStepWidth program input snapshot + 1)

/-- Potential controlling a complete dense run. Its square absorbs both live
overlay growth and the sum of selected-instruction widths. The explicit fuel
reserve also pays for the conservative loop timer after an early halt, when
the semantic RAM costs have become stationary. -/
def denseRunScale (program : Program) (input : List Bool) (fuel : ℕ)
    (snapshot : DenseOverlay.Snapshot) : ℕ :=
  encodedStoreLength snapshot.overlay + input.length + 2 +
    3 * ((programStaticWidth program + 1) *
      (fuel + RAM.unitTimeUpto program fuel (snapshot.decode input)) +
      RAM.logTimeUpto program fuel (snapshot.decode input))

/-- Quadratic envelope for a complete dense loop from an arbitrary valid
snapshot. -/
def denseProgramLoopEnvelope (program : Program) (input : List Bool)
    (fuel : ℕ) (snapshot : DenseOverlay.Snapshot) : ℕ :=
  2000000000 * (programResourceMagnitude program + 1) ^ 2 *
    (denseRunScale program input fuel snapshot) ^ 2

/-- Public-ABI quadratic envelope in input length and charged RAM time. -/
def denseProgramDecisionEnvelope (program : Program)
    (inputLength cost : ℕ) : ℕ :=
  500000000000 * (programResourceMagnitude program + 1) ^ 4 *
    (inputLength + cost + 1) ^ 2

end Machine
end RegisterStore
end RAM
end Complexity
