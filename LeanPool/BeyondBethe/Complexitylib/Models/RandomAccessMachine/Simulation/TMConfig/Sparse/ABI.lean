/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.ABI.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.ABI.Internal.Resources

/-!
# Public RAM ABI for the fixed sparse TM simulator

The public RAM convention stores the input length in `R₀` and its raw bits in
`R₁, …, Rₙ`. The fixed marshaller relocates that unbounded prefix into the
sparse TM layout without assuming a length bound, despite its scratch registers
potentially overlapping the raw input. The complete decision program then runs
the fixed sparse simulator to a halted TM configuration and returns a public
Boolean verdict in `R₀`.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


/-- The fixed marshaller converts the public RAM input store into a complete
sparse representation of the TM's initial configuration. -/
theorem marshalInput_correct (tm : TM n) (x : List Bool) :
    ∃ final steps cost space,
      Structured.Exec (marshalInput tm) (initRegs x) final steps cost space ∧
      Represents tm (tm.initCfg x) final :=
  marshalInput_exec_internal tm x

/-- The complete fixed source program follows any exact halting TM run and
returns its output bit using the public RAM verdict convention `0/1`. -/
theorem decisionProgram_correct {tm : TM n} {steps : ℕ}
    {x : List Bool} {halted : Complexity.Cfg n tm.Q}
    (hreach : tm.reachesIn steps (tm.initCfg x) halted)
    (hhalted : tm.halted halted) :
    ∃ final sourceSteps cost space,
      Structured.Exec (decisionProgram tm) (initRegs x) final
        sourceSteps cost space ∧
      final stateReg = symbolCode (halted.output.cells 1) - 1 :=
  decisionProgram_exec_internal hreach hhalted

/-- Exact concrete-RAM transfer for the complete public-ABI simulator. Source
and target agree on final registers, logarithmic cost, and peak space. -/
theorem compiledDecision_correct {tm : TM n} {steps : ℕ}
    {x : List Bool} {halted : Complexity.Cfg n tm.Q}
    (hreach : tm.reachesIn steps (tm.initCfg x) halted)
    (hhalted : tm.halted halted) :
    ∃ final sourceSteps cost space,
      Structured.Exec (decisionProgram tm) (initRegs x) final
        sourceSteps cost space ∧
      run (compiledDecision tm) sourceSteps (initCfg x) =
        { pc := (decisionProgram tm).codeSize, regs := final } ∧
      Halted (compiledDecision tm)
        (run (compiledDecision tm) sourceSteps (initCfg x)) ∧
      logTimeUpto (compiledDecision tm) sourceSteps (initCfg x) = cost ∧
      spaceUpto (compiledDecision tm) sourceSteps (initCfg x) = space ∧
      final stateReg = symbolCode (halted.output.cells 1) - 1 :=
  compiledDecision_exec_internal hreach hhalted

/-- Concrete end-to-end resource transfer from the public RAM input ABI. The
program depends only on `tm`; a `steps`-step halting TM run determines bounded
RAM fuel, logarithmic cost, sparse-store space, and the same verdict. -/
theorem compiledDecision_resourceBound {tm : TM n} {steps : ℕ}
    {x : List Bool} {halted : Complexity.Cfg n tm.Q}
    (hreach : tm.reachesIn steps (tm.initCfg x) halted)
    (hhalted : tm.halted halted) :
    ∃ final sourceSteps cost space,
      Structured.Exec (decisionProgram tm) (initRegs x) final
        sourceSteps cost space ∧
      cost ≤ decisionTimeBound tm x.length steps ∧
      space ≤ spaceBound tm (marshalBound n x.length + steps) ∧
      run (compiledDecision tm) sourceSteps (initCfg x) =
        { pc := (decisionProgram tm).codeSize, regs := final } ∧
      Halted (compiledDecision tm)
        (run (compiledDecision tm) sourceSteps (initCfg x)) ∧
      logTimeUpto (compiledDecision tm) sourceSteps (initCfg x) = cost ∧
      spaceUpto (compiledDecision tm) sourceSteps (initCfg x) = space ∧
      final stateReg = symbolCode (halted.output.cells 1) - 1 :=
  compiledDecision_resourceBound_internal hreach hhalted

/-- Increasing the simulated TM step budget only increases the advertised
end-to-end public-ABI cost bound. -/
theorem decisionTimeBound_mono_steps (tm : TM n) (inputLength : ℕ)
    {steps larger : ℕ} (hle : steps ≤ larger) :
    decisionTimeBound tm inputLength steps ≤
      decisionTimeBound tm inputLength larger :=
  decisionTimeBound_mono_steps_internal tm inputLength hle

end Sparse

end TMConfig

end RAM

end Complexity
