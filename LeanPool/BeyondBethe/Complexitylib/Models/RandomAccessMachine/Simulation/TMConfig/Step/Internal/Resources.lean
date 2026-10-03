/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Step.Internal.Action
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Step.Internal.Load
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Switch

/-!
# Resource bounds for one TM-to-RAM transition -- proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Step


/-- Register and word bounds preserved by a simulated Turing-machine step. -/
abbrev StepEnvelope (tm : TM n) (bound : ℕ) :=
  Structured.Internal.StoreEnvelope (registerLimit n bound) (wordBound tm bound)

private theorem cleared_envelope {tm : TM n} {bound test : ℕ}
    {store : Structured.Store} (henvelope : StepEnvelope tm bound store)
    (htest : test < registerLimit n bound) :
    StepEnvelope tm bound (Structured.Switch.cleared store test) := by
  exact henvelope.update htest (by simp)

private theorem cleared_apply_of_ne' (store : Structured.Store) {test reg : ℕ}
    (hne : reg ≠ test) :
    Structured.Switch.cleared store test reg = store reg := by
  simp [Structured.Switch.cleared, Function.update_of_ne hne]

private theorem symbolReg_injective' (n bound : ℕ) :
    Function.Injective (symbolReg n bound) := by
  intro first second heq
  apply Fin.ext
  simp [symbolReg] at heq
  omega

private theorem symbolReg_ne_one' (n bound : ℕ) (tape : Fin (n + 2)) :
    symbolReg n bound tape ≠ oneReg n bound := by
  simp [symbolReg, oneReg]
  omega

private theorem stateScratchReg_ne_one' (n bound : ℕ) :
    stateScratchReg n bound ≠ oneReg n bound := by
  simp [stateScratchReg, oneReg]

private theorem stateScratchReg_ne_symbolReg' (n bound : ℕ)
    (tape : Fin (n + 2)) :
    symbolReg n bound tape ≠ stateScratchReg n bound := by
  simp [symbolReg, stateScratchReg]
  omega

theorem dispatchSymbols_measured_internal {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (state : tm.Q) (actual symbols : Fin (n + 2) → Γ)
    (remaining : List (Fin (n + 2)))
    (hstate : state = cfg.state)
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm bound cfg store)
    (hheads : HeadsBounded cfg bound)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (hone : store (oneReg n bound) = 1)
    (hactual : actual = readSymbols cfg)
    (hloaded : ∀ tape, tape ∈ remaining →
      store (symbolReg n bound tape) = symbolCode (actual tape))
    (hassigned : ∀ tape, tape ∉ remaining → symbols tape = actual tape)
    (hnodup : remaining.Nodup)
    (henvelope : StepEnvelope tm bound store) :
    ∃ final,
      Structured.Internal.MeasuredRuns
        (dispatchSymbols tm bound state remaining symbols) store final
        (dispatchSteps tm bound state actual remaining)
        (dispatchCost tm bound state actual remaining) (spaceBound tm bound) ∧
      Represents tm bound next final ∧ StepEnvelope tm bound final := by
  subst state
  subst actual
  induction remaining generalizing symbols store with
  | nil =>
      have hsymbols : symbols = readSymbols cfg := by
        funext tape
        exact hassigned tape (by simp)
      subst symbols
      let final := Structured.Basic.execList
        (actionOps tm bound cfg.state (readSymbols cfg)) store
      have haction := actionOps_measured_internal hstep hrepresents hheads
        hworkStart houtputStart hone henvelope
      refine ⟨final, ?_, haction.2.1, haction.2.2⟩
      simpa [dispatchSymbols, dispatchSteps, dispatchCost, final] using haction.1
  | cons tape rest ih =>
      have htapeCode := hloaded tape (by simp)
      have htestOne : symbolReg n bound tape ≠ oneReg n bound :=
        symbolReg_ne_one' n bound tape
      let cleared := Structured.Switch.cleared store (symbolReg n bound tape)
      have hclearedRepresents : Represents tm bound cfg cleared := by
        exact hrepresents.update_outside_internal (symbolReg_ge_internal n bound tape)
      have hclearedOne : cleared (oneReg n bound) = 1 := by
        exact (cleared_apply_of_ne' store htestOne.symm).trans hone
      have hclearedEnvelope : StepEnvelope tm bound cleared :=
        cleared_envelope henvelope
          ((scratch_lt_registerLimit_internal n bound).2.2.2.2.2 tape)
      have hclearedLoaded : ∀ candidate, candidate ∈ rest →
          cleared (symbolReg n bound candidate) =
            symbolCode (readSymbols cfg candidate) := by
        intro candidate hcandidate
        have hne : candidate ≠ tape := by
          intro heq
          subst candidate
          exact (List.nodup_cons.mp hnodup).1 hcandidate
        have hregs : symbolReg n bound candidate ≠ symbolReg n bound tape :=
          fun heq => hne ((symbolReg_injective' n bound) heq)
        exact (cleared_apply_of_ne' store hregs).trans
          (hloaded candidate (by simp [hcandidate]))
      have hclearedAssigned : ∀ candidate, candidate ∉ rest →
          Function.update symbols tape (readSymbols cfg tape) candidate =
            readSymbols cfg candidate := by
        intro candidate hnot
        by_cases heq : candidate = tape
        · subst candidate
          simp
        · rw [Function.update_of_ne heq]
          exact hassigned candidate (by simp [heq, hnot])
      obtain ⟨final, hbranch, hfinalRepresents, hfinalEnvelope⟩ :=
        ih (symbols := Function.update symbols tape (readSymbols cfg tape))
          (store := cleared) hclearedRepresents hclearedOne
          (hnodup := (List.nodup_cons.mp hnodup).2)
          (henvelope := hclearedEnvelope) hclearedLoaded hclearedAssigned
      have hselectedBranch : Structured.Internal.MeasuredRuns
          ((fun code : Fin 4 =>
            dispatchSymbols tm bound cfg.state rest
              (Function.update symbols tape (symbolAt code)))
            ⟨symbolCode (readSymbols cfg tape),
              symbolCode_lt_internal (readSymbols cfg tape)⟩)
          cleared final
          (dispatchSteps tm bound cfg.state (readSymbols cfg) rest)
          (dispatchCost tm bound cfg.state (readSymbols cfg) rest)
          (spaceBound tm bound) := by
        simpa [symbolAt_code_internal] using hbranch
      have hrun := Structured.Switch.select_measured
        (fun code : Fin 4 =>
          dispatchSymbols tm bound cfg.state rest
            (Function.update symbols tape (symbolAt code)))
        store final (symbolCode_lt_internal (readSymbols cfg tape))
        htapeCode hone htestOne
        ((scratch_lt_registerLimit_internal n bound).2.2.2.2.2 tape)
        henvelope hselectedBranch
      refine ⟨final, ?_, hfinalRepresents, hfinalEnvelope⟩
      simpa [dispatchSymbols, dispatchSteps, dispatchCost, wordWidth,
        Structured.Internal.valueWidth, spaceBound,
        Structured.Internal.envelopeSpace] using hrun

theorem dispatchState_measured_internal {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm bound cfg store)
    (hheads : HeadsBounded cfg bound)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (hone : store (oneReg n bound) = 1)
    (hstate : store (stateScratchReg n bound) = stateCode tm cfg.state)
    (hloaded : ∀ tape, store (symbolReg n bound tape) =
      symbolCode (readSymbols cfg tape))
    (henvelope : StepEnvelope tm bound store) :
    ∃ final,
      Structured.Internal.MeasuredRuns (dispatchState tm bound) store final
        (Structured.Switch.stepCount (stateCode tm cfg.state)
          (dispatchSteps tm bound cfg.state (readSymbols cfg)
            (List.finRange (n + 2))))
        (Structured.Switch.costBound (stateCode tm cfg.state)
          (dispatchCost tm bound cfg.state (readSymbols cfg)
            (List.finRange (n + 2))) (wordWidth tm bound))
        (spaceBound tm bound) ∧
      Represents tm bound next final ∧ StepEnvelope tm bound final := by
  let cleared := Structured.Switch.cleared store (stateScratchReg n bound)
  have hclearedRepresents : Represents tm bound cfg cleared := by
    exact hrepresents.update_outside_internal (stateScratchReg_ge_internal n bound)
  have hclearedOne : cleared (oneReg n bound) = 1 := by
    exact (cleared_apply_of_ne' store (stateScratchReg_ne_one' n bound).symm).trans hone
  have hclearedEnvelope : StepEnvelope tm bound cleared :=
    cleared_envelope henvelope
      (scratch_lt_registerLimit_internal n bound).2.2.1
  have hclearedLoaded : ∀ tape,
      cleared (symbolReg n bound tape) = symbolCode (readSymbols cfg tape) := by
    intro tape
    exact (cleared_apply_of_ne' store
      (stateScratchReg_ne_symbolReg' n bound tape)).trans (hloaded tape)
  have hbranchState :
      (Fintype.equivFin tm.Q).symm
          ⟨stateCode tm cfg.state, stateCode_lt_internal tm cfg.state⟩ =
        cfg.state :=
    (Fintype.equivFin tm.Q).symm_apply_apply cfg.state
  obtain ⟨final, hbranch, hfinalRepresents, hfinalEnvelope⟩ :=
    dispatchSymbols_measured_internal
      ((Fintype.equivFin tm.Q).symm
        ⟨stateCode tm cfg.state, stateCode_lt_internal tm cfg.state⟩)
      (readSymbols cfg) (fun _ => Γ.blank) (List.finRange (n + 2))
      hbranchState hstep hclearedRepresents hheads hworkStart houtputStart
      hclearedOne rfl (fun tape _ => hclearedLoaded tape) (by simp)
      (List.nodup_finRange (n + 2)) hclearedEnvelope
  have hselectedBranch : Structured.Internal.MeasuredRuns
      ((fun stateCode : Fin (Fintype.card tm.Q) =>
        dispatchSymbols tm bound ((Fintype.equivFin tm.Q).symm stateCode)
          (List.finRange (n + 2)) (fun _ => Γ.blank))
        ⟨stateCode tm cfg.state, stateCode_lt_internal tm cfg.state⟩)
      cleared final
      (dispatchSteps tm bound cfg.state (readSymbols cfg) (List.finRange (n + 2)))
      (dispatchCost tm bound cfg.state (readSymbols cfg) (List.finRange (n + 2)))
      (spaceBound tm bound) := by
    simpa [hbranchState] using hbranch
  have hrun := Structured.Switch.select_measured
    (fun stateCode : Fin (Fintype.card tm.Q) =>
      dispatchSymbols tm bound ((Fintype.equivFin tm.Q).symm stateCode)
        (List.finRange (n + 2)) (fun _ => Γ.blank))
    store final (stateCode_lt_internal tm cfg.state) hstate hone
    (stateScratchReg_ne_one' n bound)
    (scratch_lt_registerLimit_internal n bound).2.2.1 henvelope hselectedBranch
  refine ⟨final, ?_, hfinalRepresents, hfinalEnvelope⟩
  simpa [dispatchState, wordWidth, Structured.Internal.valueWidth, spaceBound,
    Structured.Internal.envelopeSpace] using hrun

theorem program_measured_internal {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm bound cfg store)
    (hwindow : WithinWindow cfg bound)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (henvelope : StepEnvelope tm bound store) :
    ∃ final,
      Structured.Internal.MeasuredRuns (program tm bound) store final
        (stepCount tm bound cfg) (timeBound tm bound cfg) (spaceBound tm bound) ∧
      Represents tm bound next final ∧ StepEnvelope tm bound final := by
  let loaded := Structured.Basic.execList (loadOps n bound) store
  have hload := loadOps_measured_internal hrepresents hwindow.2 henvelope
  have hloaded := loadOps_loaded_internal hrepresents hwindow.2
  obtain ⟨final, hdispatch, hfinalRepresents, hfinalEnvelope⟩ :=
    dispatchState_measured_internal hstep hloaded.1 hwindow.2 hworkStart
      houtputStart hloaded.2.2.1 hloaded.2.2.2.1 hloaded.2.2.2.2 hload.2
  have hrun := hload.1.seq hdispatch
  refine ⟨final, ?_, hfinalRepresents, hfinalEnvelope⟩
  simpa [program, stepCount, timeBound, loaded] using hrun

end Step

end TMConfig

end RAM

end Complexity
