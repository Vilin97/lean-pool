/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Step.Internal.Dispatch

/-!
# Iterating the fixed sparse TM transition -- proof internals
-/


public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


private theorem stateCode_lt (tm : TM n) (state : tm.Q) :
    stateCode tm state < Fintype.card tm.Q :=
  (Fintype.equivFin tm.Q state).isLt

private theorem stateScratchReg_ne_one (n : ℕ) :
    stateScratchReg n ≠ oneReg n := by
  simp [stateScratchReg, oneReg]

private theorem cleared_apply_of_ne (store : Structured.Store) {test reg : ℕ}
    (hne : reg ≠ test) :
    Structured.Switch.cleared store test reg = store reg := by
  simp [Structured.Switch.cleared, Function.update_of_ne hne]

theorem continueCheck_exec_internal {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm cfg store) :
    ∃ final cost space,
      Structured.Exec (continueCheck tm) store final
        (continueSteps tm cfg) cost space ∧
      Represents tm cfg final ∧
      final (valueReg n) = runningFlag tm cfg.state ∧
      final (oneReg n) = 1 ∧
      final (tapeCountReg n) = n + 2 := by
  let loaded := Structured.Basic.execList (loadOps n) store
  obtain ⟨loadCost, loadSpace, hloadExec⟩ :=
    Structured.Internal.exec_basics_exists (loadOps n) store
  have hloaded := loadOps_loaded_internal hrepresents
  let cleared := Structured.Switch.cleared loaded (stateScratchReg n)
  have hrange := scratch_range_internal n
  have hclearedRepresents : Represents tm cfg cleared :=
    hloaded.1.update_control_internal hrange.2.2.2.1.1
      hrange.2.2.2.1.2
  have hclearedOne : cleared (oneReg n) = 1 := by
    exact (cleared_apply_of_ne loaded (stateScratchReg_ne_one n).symm).trans
      hloaded.2.2.1
  have hclearedCount : cleared (tapeCountReg n) = n + 2 := by
    have hne : tapeCountReg n ≠ stateScratchReg n := by
      simp [tapeCountReg, stateScratchReg]
    exact (cleared_apply_of_ne loaded hne).trans hloaded.2.2.2.1
  let final := (Structured.Basic.imm (valueReg n)
    (runningFlag tm cfg.state)).exec cleared
  obtain ⟨branchCost, branchSpace, hbranchExec⟩ :=
    Structured.Internal.exec_basics_exists
      [.imm (valueReg n) (runningFlag tm cfg.state)] cleared
  have hfinalRepresents : Represents tm cfg final := by
    exact hclearedRepresents.update_control_internal
      hrange.2.2.2.2.2.1.1 hrange.2.2.2.2.2.1.2
  have hfinalValue : final (valueReg n) = runningFlag tm cfg.state := by
    simp [final, Structured.Basic.exec]
  have hfinalOne : final (oneReg n) = 1 := by
    simpa [final, Structured.Basic.exec, oneReg, valueReg,
      Function.update_of_ne] using hclearedOne
  have hfinalCount : final (tapeCountReg n) = n + 2 := by
    simpa [final, Structured.Basic.exec, tapeCountReg, valueReg,
      Function.update_of_ne] using hclearedCount
  have hbranchState :
      (Fintype.equivFin tm.Q).symm
          ⟨stateCode tm cfg.state, stateCode_lt tm cfg.state⟩ = cfg.state :=
    (Fintype.equivFin tm.Q).symm_apply_apply cfg.state
  have hselectedBranch :
      ∃ cost space,
        Structured.Exec
          ((fun code : Fin (Fintype.card tm.Q) => .basics
            [.imm (valueReg n)
              (runningFlag tm ((Fintype.equivFin tm.Q).symm code))])
            ⟨stateCode tm cfg.state, stateCode_lt tm cfg.state⟩)
          cleared final 1 cost space := by
    refine ⟨branchCost, branchSpace, ?_⟩
    simpa [hbranchState, final] using hbranchExec
  obtain ⟨dispatchCost, dispatchSpace, hdispatch⟩ :=
    Structured.Switch.select_exec
      (fun code : Fin (Fintype.card tm.Q) => .basics
        [.imm (valueReg n)
          (runningFlag tm ((Fintype.equivFin tm.Q).symm code))])
      loaded final (stateCode_lt tm cfg.state) hloaded.2.2.2.2.1
      hloaded.2.2.1 (stateScratchReg_ne_one n) hselectedBranch
  refine ⟨final, loadCost + dispatchCost, max loadSpace dispatchSpace,
    ?_, hfinalRepresents, hfinalValue, hfinalOne, hfinalCount⟩
  simpa [continueCheck, continueDispatch, continueSteps, loaded] using
    Structured.Exec.seq hloadExec hdispatch

theorem starts_of_step_internal {tm : TM n}
    {cfg next : Complexity.Cfg n tm.Q} (hstep : tm.step cfg = some next)
    (hwork : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtput : cfg.output.cells 0 = Γ.start) :
    (∀ i, (next.work i).cells 0 = Γ.start) ∧
      next.output.cells 0 = Γ.start := by
  have hnotHalted := TM.state_ne_qhalt_of_step hstep
  rcases hdelta : tm.δ cfg.state cfg.input.read
      (fun i => (cfg.work i).read) cfg.output.read with
    ⟨nextState, workWrites, outputWrite, inputDirection,
      workDirections, outputDirection⟩
  rw [TM.step, if_neg hnotHalted, hdelta] at hstep
  dsimp only at hstep
  injection hstep with hnext
  subst next
  constructor
  · intro i
    rw [Tape.writeAndMove, Tape.move_cells]
    simp only [Tape.write]
    split
    · exact hwork i
    · change Function.update (cfg.work i).cells (cfg.work i).head
          (workWrites i).toΓ 0 = Γ.start
      rw [Function.update_of_ne]
      · exact hwork i
      · exact Ne.symm (by assumption)
  · rw [Tape.writeAndMove, Tape.move_cells]
    simp only [Tape.write]
    split
    · exact houtput
    · change Function.update cfg.output.cells cfg.output.head
          outputWrite.toΓ 0 = Γ.start
      rw [Function.update_of_ne]
      · exact houtput
      · exact Ne.symm (by assumption)

theorem loop_exec_internal {tm : TM n} {steps : ℕ}
    {cfg halted : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hreach : tm.reachesIn steps cfg halted)
    (hhalted : tm.halted halted)
    (hrepresents : Represents tm cfg store)
    (hflag : store (valueReg n) = runningFlag tm cfg.state)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start) :
    ∃ final cost space,
      Structured.Exec (.whileNonzero (valueReg n) (loopBody tm))
        store final (loopSteps tm steps cfg) cost space ∧
      Represents tm halted final := by
  induction hreach generalizing store with
  | zero =>
      have hzero : store (valueReg n) = 0 := by
        rw [hflag]
        simp [runningFlag, hhalted]
      refine ⟨store, bitlen (store (valueReg n)) + 1, store.space, ?_,
        hrepresents⟩
      simpa [loopSteps] using
        (Structured.Exec.whileZero (body := loopBody tm) hzero)
  | @step current successor tail finalCfg hstep htail ih =>
      have hnotHalted := TM.state_ne_qhalt_of_step hstep
      have hnonzero : store (valueReg n) ≠ 0 := by
        rw [hflag]
        simp [runningFlag, hnotHalted]
      obtain ⟨middle, stepCost, stepSpace, hprogram, hmiddleRepresents⟩ :=
        program_exec_internal hstep hrepresents hworkStart houtputStart
      obtain ⟨checked, checkCost, checkSpace, hcheck,
          hcheckedRepresents, hcheckedFlag, _hcheckedOne, _hcheckedCount⟩ :=
        continueCheck_exec_internal hmiddleRepresents
      have hstarts := starts_of_step_internal hstep hworkStart houtputStart
      obtain ⟨final, loopCost, loopSpace, hloop, hfinalRepresents⟩ :=
        ih hhalted hcheckedRepresents hcheckedFlag hstarts.1 hstarts.2
      have hbody : Structured.Exec (loopBody tm) store checked
          (stepCount tm current + continueSteps tm successor)
          (stepCost + checkCost) (max stepSpace checkSpace) := by
        simpa [loopBody] using Structured.Exec.seq hprogram hcheck
      refine ⟨final,
        bitlen (store (valueReg n)) + 1 + (stepCost + checkCost) + 1 + loopCost,
        max (max stepSpace checkSpace) loopSpace, ?_, hfinalRepresents⟩
      have hexec := Structured.Exec.whileNonzero hnonzero hbody hloop
      simpa [loopSteps, hstep, Nat.add_assoc] using hexec

theorem runUntilHalt_exec_internal {tm : TM n} {steps : ℕ}
    {cfg halted : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hreach : tm.reachesIn steps cfg halted)
    (hhalted : tm.halted halted)
    (hrepresents : Represents tm cfg store)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start) :
    ∃ final cost space,
      Structured.Exec (runUntilHalt tm) store final
        (runSteps tm steps cfg) cost space ∧
      Represents tm halted final := by
  obtain ⟨checked, checkCost, checkSpace, hcheck, hcheckedRepresents,
      hcheckedFlag, _hcheckedOne, _hcheckedCount⟩ :=
    continueCheck_exec_internal hrepresents
  obtain ⟨final, loopCost, loopSpace, hloop, hfinalRepresents⟩ :=
    loop_exec_internal hreach hhalted hcheckedRepresents hcheckedFlag
      hworkStart houtputStart
  refine ⟨final, checkCost + loopCost, max checkSpace loopSpace, ?_,
    hfinalRepresents⟩
  simpa [runUntilHalt, runSteps] using Structured.Exec.seq hcheck hloop

end Sparse

end TMConfig

end RAM

end Complexity
