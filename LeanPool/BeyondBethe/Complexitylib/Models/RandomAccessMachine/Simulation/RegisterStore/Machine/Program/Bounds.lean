/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Bounds.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Bounds.Internal

/-!
# Sparse RAM decision-machine resource bounds
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- The fixed program magnitude is positive. -/
theorem programResourceMagnitude_pos (program : Program) :
    1 ≤ programResourceMagnitude program :=
  programResourceMagnitude_pos_internal program

/-- The fixed program length is absorbed by its resource magnitude. -/
theorem program_length_le_resourceMagnitude (program : Program) :
    program.length ≤ programResourceMagnitude program :=
  program_length_le_resourceMagnitude_internal program

/-- Every fixed program literal width is absorbed by the resource magnitude. -/
theorem programStaticWidth_le_resourceMagnitude (program : Program) :
    programStaticWidth program ≤ programResourceMagnitude program :=
  programStaticWidth_le_resourceMagnitude_internal program

/-- The common run scale is positive. -/
theorem programDecisionScale_pos (program : Program)
    (inputLength cost : ℕ) :
    1 ≤ programDecisionScale program inputLength cost :=
  programDecisionScale_pos_internal program inputLength cost

/-- A fuel-bounded halted RAM run whose fuel is charged by logarithmic time is
simulated by the concrete decision TM within the checked fourth-degree
envelope. -/
theorem programDecisionTime_le_envelope {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (fuel : ℕ)
    (hhalted : RAM.Halted program
      (RAM.run program fuel (RAM.initCfg input)))
    (hfuel : fuel ≤
      RAM.logTimeUpto program fuel (RAM.initCfg input)) :
    programDecisionTime tapes program input fuel ≤
      programDecisionEnvelope program input.length
        (RAM.logTimeUpto program fuel (RAM.initCfg input)) :=
  programDecisionTime_le_envelope_internal tapes program input fuel
    hhalted hfuel

/-- Increasing the charged RAM-time argument can only increase the concrete
simulation envelope. -/
theorem programDecisionEnvelope_mono_cost (program : Program)
    (inputLength left right : ℕ) (hle : left ≤ right) :
    programDecisionEnvelope program inputLength left ≤
      programDecisionEnvelope program inputLength right :=
  programDecisionEnvelope_mono_cost_internal program inputLength left right hle

end Machine

end RegisterStore

end RAM

end Complexity
