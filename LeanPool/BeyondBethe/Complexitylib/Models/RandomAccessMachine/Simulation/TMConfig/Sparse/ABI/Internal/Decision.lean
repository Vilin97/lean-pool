/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.ABI.Internal.Marshal
import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Step.Internal.Iteration
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured

/-!
# End-to-end public-ABI sparse simulation -- proof internals
-/


public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


/-- The verdict extractor copies the represented halted output cell one into
the public verdict register. -/
theorem extractVerdict_exec_internal {tm : TM n}
    {halted : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm halted store) :
    let final := Structured.Basic.execList (extractVerdictOps n) store
    ∃ cost space,
      Structured.Exec (.basics (extractVerdictOps n)) store final
        (extractVerdictOps n).length cost space ∧
      final stateReg = symbolCode (halted.output.cells 1) - 1 := by
  let final := Structured.Basic.execList (extractVerdictOps n) store
  obtain ⟨cost, space, hexec⟩ :=
    Structured.Internal.exec_basics_exists (extractVerdictOps n) store
  have hcell : store (cellReg n (outputTape n) 1) =
      symbolCode (halted.output.cells 1) := by
    have hfield := hrepresents
      (Sum.inr (Sum.inr (outputTape n, 1)))
    simpa [fieldReg, fieldValue, tapeAt, outputTape] using hfield
  refine ⟨cost, space, hexec, ?_⟩
  let addressed :=
    (Structured.Basic.imm (addressReg n)
      (cellReg n (outputTape n) 1)).exec store
  have haddress : addressed (addressReg n) =
      cellReg n (outputTape n) 1 := by
    simp [addressed, Structured.Basic.exec]
  have hsource : addressed (cellReg n (outputTape n) 1) =
      store (cellReg n (outputTape n) 1) := by
    simp only [addressed, Structured.Basic.exec]
    rw [Function.update_of_ne]
    simp [cellReg, outputTape, cellBase, addressReg]
    omega
  let loaded :=
    (Structured.Basic.load stateReg (addressReg n)).exec addressed
  let oned := (Structured.Basic.imm (oneReg n) 1).exec loaded
  have hloadedState : loaded stateReg =
      symbolCode (halted.output.cells 1) := by
    simp only [loaded, Structured.Basic.exec, Function.update_self]
    rw [haddress, hsource, hcell]
  have honedState : oned stateReg = symbolCode (halted.output.cells 1) := by
    simp only [oned, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, oneReg])]
    exact hloadedState
  have honedOne : oned (oneReg n) = 1 := by
    simp [oned, Structured.Basic.exec]
  change (Structured.Basic.sub stateReg stateReg (oneReg n)).exec
    oned stateReg = _
  simp [Structured.Basic.exec, honedState, honedOne]

/-- From the public RAM input store, the complete fixed source program follows
any exact halting TM run and returns the halted output symbol in `R₀`. -/
theorem decisionProgram_exec_internal {tm : TM n} {steps : ℕ}
    {x : List Bool} {halted : Complexity.Cfg n tm.Q}
    (hreach : tm.reachesIn steps (tm.initCfg x) halted)
    (hhalted : tm.halted halted) :
    ∃ final sourceSteps cost space,
      Structured.Exec (decisionProgram tm) (initRegs x) final
        sourceSteps cost space ∧
      final stateReg = symbolCode (halted.output.cells 1) - 1 := by
  obtain ⟨marshaled, marshalSteps, marshalCost, marshalSpace,
      hmarshal, hrepresents⟩ := marshalInput_exec_internal tm x
  obtain ⟨simulated, simulationCost, simulationSpace,
      hsimulation, hhaltedRepresents⟩ :=
    runUntilHalt_exec_internal hreach hhalted hrepresents
      (fun _ => rfl) rfl
  let extracted := Structured.Basic.execList (extractVerdictOps n) simulated
  obtain ⟨extractCost, extractSpace, hextract, hverdict⟩ :=
    extractVerdict_exec_internal hhaltedRepresents
  have htail := Structured.Exec.seq hsimulation hextract
  have hexec := Structured.Exec.seq hmarshal htail
  refine ⟨extracted,
    marshalSteps + (runSteps tm steps (tm.initCfg x) +
      (extractVerdictOps n).length),
    marshalCost + (simulationCost + extractCost),
    max marshalSpace (max simulationSpace extractSpace), ?_, hverdict⟩
  simpa [decisionProgram, extracted] using hexec

/-- Exact transfer of the public-ABI decision program to its concrete compiled
RAM, including source/target store agreement, cost, and space. -/
theorem compiledDecision_exec_internal {tm : TM n} {steps : ℕ}
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
      final stateReg = symbolCode (halted.output.cells 1) - 1 := by
  obtain ⟨final, sourceSteps, cost, space, hexec, hverdict⟩ :=
    decisionProgram_exec_internal hreach hhalted
  have hcompiled := Structured.Exec.compile_correct hexec
  refine ⟨final, sourceSteps, cost, space, hexec, ?_, ?_, ?_, ?_, hverdict⟩
  · simpa [compiledDecision, initCfg] using hcompiled.1
  · simpa [compiledDecision, initCfg] using
      Structured.Exec.compile_halted hexec
  · simpa [compiledDecision, initCfg] using hcompiled.2.1
  · simpa [compiledDecision, initCfg] using hcompiled.2.2

end Sparse

end TMConfig

end RAM

end Complexity
