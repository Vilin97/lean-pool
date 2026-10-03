/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Decision.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DecisionInternal

/-!
# Complete sparse RAM decision machine
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- The complete concrete machine realizes one halted pure sparse RAM run and
emits its `R₀` verdict. -/
theorem programDecisionTM_hoareTime_run {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (fuel : ℕ)
    (hhalted : ((programInitialSnapshot input).run program fuel).Halted program) :
    (programDecisionTM tapes program).HoareTime
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _inp _work out =>
        let final := (programInitialSnapshot input).run program fuel
        out = registerVerdictOutput (RegisterStore.read final.store 0))
      (programDecisionTime tapes program input fuel) :=
  programDecisionTM_hoareTime_run_internal tapes program input fuel hhalted

/-- The complete machine realizes a halted executable RAM run and emits its
public `R₀` verdict. -/
theorem programDecisionTM_hoareTime_ramRun {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (fuel : ℕ)
    (hhalted : RAM.Halted program
      (RAM.run program fuel (RAM.initCfg input))) :
    (programDecisionTM tapes program).HoareTime
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _inp _work out =>
        out = registerVerdictOutput
          (RAM.run program fuel (RAM.initCfg input)).verdict)
      (programDecisionTime tapes program input fuel) :=
  programDecisionTM_hoareTime_ramRun_internal tapes program input fuel hhalted

end Machine

end RegisterStore

end RAM

end Complexity
