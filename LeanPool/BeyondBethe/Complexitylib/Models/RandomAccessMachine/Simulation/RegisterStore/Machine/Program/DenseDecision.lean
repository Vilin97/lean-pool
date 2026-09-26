/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseDecisionDefs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseDecisionProof

/-!
# Complete dense-overlay RAM decision machine
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- The complete dense machine realizes one halted overlay run and emits its
decoded `R₀` verdict. -/
theorem denseProgramDecisionTM_hoareTime_run {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (fuel : ℕ)
    (hhalted : ((DenseOverlay.Snapshot.initial input).run program input fuel).Halted
      program) :
    (denseProgramDecisionTM tapes program).HoareTime
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _inp _work out =>
        let final := (DenseOverlay.Snapshot.initial input).run program input fuel
        out = registerVerdictOutput
          (DenseOverlay.read input final.overlay 0))
      (denseProgramDecisionTime tapes program input fuel) :=
  denseProgramDecisionTM_hoareTime_run_internal tapes program input fuel hhalted

/-- The fixed dense machine realizes a halted executable RAM run and emits its
public `R₀` verdict. -/
theorem denseProgramDecisionTM_hoareTime_ramRun {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (fuel : ℕ)
    (hhalted : RAM.Halted program
      (RAM.run program fuel (RAM.initCfg input))) :
    (denseProgramDecisionTM tapes program).HoareTime
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _inp _work out =>
        out = registerVerdictOutput
          (RAM.run program fuel (RAM.initCfg input)).verdict)
      (denseProgramDecisionTime tapes program input fuel) :=
  denseProgramDecisionTM_hoareTime_ramRun_internal tapes program input fuel
    hhalted

end Machine
end RegisterStore
end RAM
end Complexity
