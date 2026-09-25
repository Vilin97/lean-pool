/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseBoundsDefs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseBoundsProof

/-!
# Dense-overlay RAM decision-machine resource bounds

This surface exposes the selected-width one-step bound, the amortized
quadratic loop bound, and the complete quadratic decision bound for the
optimized dense-input RAM simulator.
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- One selected dense RAM instruction is simulated in time proportional to
the live serialized volume times that instruction's actual charged width. -/
theorem denseProgramStepTime_le_envelope {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hpc : snapshot.pc ≤ programResourceMagnitude program) :
    denseProgramStepTime tapes program input snapshot.pc snapshot.overlay ≤
      denseStepEnvelope program input snapshot :=
  denseProgramStepTime_le_envelope_internal tapes program input snapshot
    hvalid hpc

/-- The complete conservative dense loop timer is bounded by the square of a
potential containing live data, remaining fuel, and remaining RAM cost. -/
theorem denseProgramLoopTime_le_envelope {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (fuel : ℕ)
    (snapshot : DenseOverlay.Snapshot)
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hpc : snapshot.pc ≤ programResourceMagnitude program) :
    denseProgramLoopTime tapes program input fuel snapshot ≤
      denseProgramLoopEnvelope program input fuel snapshot :=
  denseProgramLoopTime_le_envelope_internal tapes program input fuel snapshot
    hvalid hpc

/-- A halted dense RAM run whose fuel is charged by logarithmic time is
simulated within a quadratic envelope in input length plus charged RAM time. -/
theorem denseProgramDecisionTime_le_envelope {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (fuel : ℕ)
    (hhalted : RAM.Halted program
      (RAM.run program fuel (RAM.initCfg input)))
    (hfuel : fuel ≤
      RAM.logTimeUpto program fuel (RAM.initCfg input)) :
    denseProgramDecisionTime tapes program input fuel ≤
      denseProgramDecisionEnvelope program input.length
        (RAM.logTimeUpto program fuel (RAM.initCfg input)) :=
  denseProgramDecisionTime_le_envelope_internal tapes program input fuel
    hhalted hfuel

/-- Increasing the charged RAM-time argument can only enlarge the optimized
quadratic decision envelope. -/
theorem denseProgramDecisionEnvelope_mono_cost (program : Program)
    (inputLength left right : ℕ) (hle : left ≤ right) :
    denseProgramDecisionEnvelope program inputLength left ≤
      denseProgramDecisionEnvelope program inputLength right := by
  unfold denseProgramDecisionEnvelope
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (by omega) 2)

end Machine
end RegisterStore
end RAM
end Complexity
