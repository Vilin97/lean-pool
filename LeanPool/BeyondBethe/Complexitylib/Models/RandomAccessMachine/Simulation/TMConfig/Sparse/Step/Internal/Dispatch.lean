/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Step.Internal.Action
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Switch
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Step.Internal.Load

/-!
# Nested finite dispatch for the fixed sparse TM transition -- proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


private theorem cleared_represents {tm : TM n} {test : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm cfg store)
    (hlow : n + 3 ≤ test) (hhigh : test < cellBase n) :
    Represents tm cfg (Structured.Switch.cleared store test) := by
  exact hrepresents.update_control_internal hlow hhigh

private theorem cleared_apply_of_ne (store : Structured.Store) {test reg : ℕ}
    (hne : reg ≠ test) :
    Structured.Switch.cleared store test reg = store reg := by
  simp [Structured.Switch.cleared, Function.update_of_ne hne]

private theorem symbolReg_injective (n : ℕ) :
    Function.Injective (symbolReg n) := by
  intro first second heq
  apply Fin.ext
  simp [symbolReg] at heq
  omega

private theorem symbolReg_ne_one (n : ℕ) (tape : Fin (n + 2)) :
    symbolReg n tape ≠ oneReg n := by
  simp [symbolReg, oneReg]
  omega

private theorem stateScratchReg_ne_one (n : ℕ) :
    stateScratchReg n ≠ oneReg n := by
  simp [stateScratchReg, oneReg]

private theorem stateScratchReg_ne_symbolReg (n : ℕ)
    (tape : Fin (n + 2)) :
    symbolReg n tape ≠ stateScratchReg n := by
  simp [symbolReg, stateScratchReg]
  omega

private theorem stateCode_lt_internal (tm : TM n) (state : tm.Q) :
    stateCode tm state < Fintype.card tm.Q := by
  exact (Fintype.equivFin tm.Q state).isLt

theorem dispatchSymbols_exec_internal {tm : TM n}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (state : tm.Q) (actual symbols : Fin (n + 2) → Γ)
    (remaining : List (Fin (n + 2)))
    (hstate : state = cfg.state)
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm cfg store)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (hone : store (oneReg n) = 1)
    (htapeCount : store (tapeCountReg n) = n + 2)
    (hactual : actual = readSymbols cfg)
    (hloaded : ∀ tape, tape ∈ remaining →
      store (symbolReg n tape) = symbolCode (actual tape))
    (hassigned : ∀ tape, tape ∉ remaining → symbols tape = actual tape)
    (hnodup : remaining.Nodup) :
    ∃ final cost space,
      Structured.Exec (dispatchSymbols tm state remaining symbols)
        store final (dispatchSteps tm state actual remaining) cost space ∧
      Represents tm next final := by
  subst state
  subst actual
  induction remaining generalizing symbols store with
  | nil =>
      have hsymbols : symbols = readSymbols cfg := by
        funext tape
        exact hassigned tape (by simp)
      subst symbols
      obtain ⟨cost, space, hexec⟩ :=
        Structured.Internal.exec_basics_exists
          (actionOps tm cfg.state (readSymbols cfg)) store
      refine ⟨Structured.Basic.execList
        (actionOps tm cfg.state (readSymbols cfg)) store,
        cost, space, ?_, ?_⟩
      · simpa [dispatchSymbols, action, dispatchSteps] using hexec
      · exact actionOps_represents_internal hstep hrepresents hworkStart
          houtputStart hone htapeCount
  | cons tape rest ih =>
      have htapeCode := hloaded tape (by simp)
      have htestOne : symbolReg n tape ≠ oneReg n :=
        symbolReg_ne_one n tape
      let cleared := Structured.Switch.cleared store (symbolReg n tape)
      have hrange := scratch_range_internal n
      have hclearedRepresents : Represents tm cfg cleared :=
        cleared_represents hrepresents (hrange.2.2.2.2.2.2 tape).1
          (hrange.2.2.2.2.2.2 tape).2
      have hclearedOne : cleared (oneReg n) = 1 := by
        exact (cleared_apply_of_ne store htestOne.symm).trans hone
      have hclearedCount : cleared (tapeCountReg n) = n + 2 := by
        have hne : tapeCountReg n ≠ symbolReg n tape := by
          simp [tapeCountReg, symbolReg]
          omega
        exact (cleared_apply_of_ne store hne).trans htapeCount
      have hclearedLoaded : ∀ candidate, candidate ∈ rest →
          cleared (symbolReg n candidate) =
            symbolCode (readSymbols cfg candidate) := by
        intro candidate hcandidate
        have hne : candidate ≠ tape := by
          intro heq
          subst candidate
          exact (List.nodup_cons.mp hnodup).1 hcandidate
        have hregs : symbolReg n candidate ≠ symbolReg n tape :=
          fun heq => hne ((symbolReg_injective n) heq)
        exact (cleared_apply_of_ne store hregs).trans
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
      obtain ⟨final, branchCost, branchSpace, hbranch, hfinalRepresents⟩ :=
        ih (symbols := Function.update symbols tape (readSymbols cfg tape))
          (store := cleared) hclearedRepresents hclearedOne hclearedCount
          (List.nodup_cons.mp hnodup).2 hclearedLoaded hclearedAssigned
      have hselectedBranch :
          ∃ cost space,
            Structured.Exec
              ((fun code : Fin 4 =>
                dispatchSymbols tm cfg.state rest
                  (Function.update symbols tape (symbolDecode code.val)))
                ⟨symbolCode (readSymbols cfg tape),
                  symbolCode_lt_internal (readSymbols cfg tape)⟩)
              cleared final
              (dispatchSteps tm cfg.state (readSymbols cfg) rest)
              cost space := by
        refine ⟨branchCost, branchSpace, ?_⟩
        simpa [symbolDecode_code_internal] using hbranch
      obtain ⟨cost, space, hexec⟩ := Structured.Switch.select_exec
        (fun code : Fin 4 =>
          dispatchSymbols tm cfg.state rest
            (Function.update symbols tape (symbolDecode code.val)))
        store final (symbolCode_lt_internal (readSymbols cfg tape))
        htapeCode hone htestOne hselectedBranch
      refine ⟨final, cost, space, ?_, hfinalRepresents⟩
      simpa [dispatchSymbols, dispatchSteps] using hexec

theorem dispatchState_exec_internal {tm : TM n}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm cfg store)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (hone : store (oneReg n) = 1)
    (htapeCount : store (tapeCountReg n) = n + 2)
    (hstate : store (stateScratchReg n) = stateCode tm cfg.state)
    (hloaded : ∀ tape, store (symbolReg n tape) =
      symbolCode (readSymbols cfg tape)) :
    ∃ final cost space,
      Structured.Exec (dispatchState tm) store final
        (Structured.Switch.stepCount (stateCode tm cfg.state)
          (dispatchSteps tm cfg.state (readSymbols cfg)
            (List.finRange (n + 2)))) cost space ∧
      Represents tm next final := by
  let cleared := Structured.Switch.cleared store (stateScratchReg n)
  have hrange := scratch_range_internal n
  have hclearedRepresents : Represents tm cfg cleared :=
    cleared_represents hrepresents hrange.2.2.2.1.1 hrange.2.2.2.1.2
  have hclearedOne : cleared (oneReg n) = 1 := by
    exact (cleared_apply_of_ne store (stateScratchReg_ne_one n).symm).trans hone
  have hclearedCount : cleared (tapeCountReg n) = n + 2 := by
    have hne : tapeCountReg n ≠ stateScratchReg n := by
      simp [tapeCountReg, stateScratchReg]
    exact (cleared_apply_of_ne store hne).trans htapeCount
  have hclearedLoaded : ∀ tape,
      cleared (symbolReg n tape) = symbolCode (readSymbols cfg tape) := by
    intro tape
    exact (cleared_apply_of_ne store
      (stateScratchReg_ne_symbolReg n tape)).trans (hloaded tape)
  have hbranchState :
      (Fintype.equivFin tm.Q).symm
          ⟨stateCode tm cfg.state, stateCode_lt_internal tm cfg.state⟩ =
        cfg.state := by
    exact (Fintype.equivFin tm.Q).symm_apply_apply cfg.state
  obtain ⟨final, branchCost, branchSpace, hbranch, hfinalRepresents⟩ :=
    dispatchSymbols_exec_internal
      ((Fintype.equivFin tm.Q).symm
        ⟨stateCode tm cfg.state, stateCode_lt_internal tm cfg.state⟩)
      (readSymbols cfg) (fun _ => Γ.blank) (List.finRange (n + 2))
      hbranchState hstep hclearedRepresents hworkStart houtputStart
      hclearedOne hclearedCount rfl (fun tape _ => hclearedLoaded tape)
      (by simp) (List.nodup_finRange (n + 2))
  have hselectedBranch :
      ∃ cost space,
        Structured.Exec
          ((fun stateCode : Fin (Fintype.card tm.Q) =>
            dispatchSymbols tm ((Fintype.equivFin tm.Q).symm stateCode)
              (List.finRange (n + 2)) (fun _ => Γ.blank))
            ⟨stateCode tm cfg.state, stateCode_lt_internal tm cfg.state⟩)
          cleared final
          (dispatchSteps tm cfg.state (readSymbols cfg)
            (List.finRange (n + 2))) cost space := by
    refine ⟨branchCost, branchSpace, ?_⟩
    simpa [hbranchState] using hbranch
  obtain ⟨cost, space, hexec⟩ := Structured.Switch.select_exec
    (fun stateCode : Fin (Fintype.card tm.Q) =>
      dispatchSymbols tm ((Fintype.equivFin tm.Q).symm stateCode)
        (List.finRange (n + 2)) (fun _ => Γ.blank))
    store final (stateCode_lt_internal tm cfg.state) hstate hone
    (stateScratchReg_ne_one n) hselectedBranch
  refine ⟨final, cost, space, ?_, hfinalRepresents⟩
  simpa [dispatchState] using hexec

theorem program_exec_internal {tm : TM n}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm cfg store)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start) :
    ∃ final cost space,
      Structured.Exec (program tm) store final
        (stepCount tm cfg) cost space ∧
      Represents tm next final := by
  let loaded := Structured.Basic.execList (loadOps n) store
  obtain ⟨loadCost, loadSpace, hloadExec⟩ :=
    Structured.Internal.exec_basics_exists (loadOps n) store
  have hloaded := loadOps_loaded_internal hrepresents
  obtain ⟨final, dispatchCost, dispatchSpace, hdispatch,
      hfinalRepresents⟩ := dispatchState_exec_internal hstep hloaded.1
        hworkStart houtputStart hloaded.2.2.1 hloaded.2.2.2.1
        hloaded.2.2.2.2.1 hloaded.2.2.2.2.2
  refine ⟨final, loadCost + dispatchCost, max loadSpace dispatchSpace, ?_,
    hfinalRepresents⟩
  simpa [program, stepCount, loaded] using Structured.Exec.seq hloadExec hdispatch

/-- Register and word bounds preserved by sparse step dispatch. -/
abbrev ResourceEnvelope (tm : TM n) (bound : ℕ) :=
  Structured.Internal.StoreEnvelope (registerBound n (bound + 1))
    (wordBound tm bound)

private theorem control_lt_registerBound (n bound : ℕ) :
    cellBase n < registerBound n (bound + 1) := by
  simp [registerBound, cellReg, outputTape]
  omega

private theorem cleared_envelope {tm : TM n} {bound test : ℕ}
    {store : Structured.Store} (henvelope : ResourceEnvelope tm bound store)
    (htest : test < registerBound n (bound + 1)) :
    ResourceEnvelope tm bound (Structured.Switch.cleared store test) := by
  exact henvelope.update htest (by simp)

theorem dispatchSymbols_measured_internal {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (state : tm.Q) (actual symbols : Fin (n + 2) → Γ)
    (remaining : List (Fin (n + 2)))
    (hstate : state = cfg.state)
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm cfg store)
    (hheads : HeadsBounded cfg bound)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (hone : store (oneReg n) = 1)
    (htapeCount : store (tapeCountReg n) = n + 2)
    (hactual : actual = readSymbols cfg)
    (hloaded : ∀ tape, tape ∈ remaining →
      store (symbolReg n tape) = symbolCode (actual tape))
    (hassigned : ∀ tape, tape ∉ remaining → symbols tape = actual tape)
    (hnodup : remaining.Nodup)
    (henvelope : ResourceEnvelope tm bound store) :
    ∃ final,
      Structured.Internal.MeasuredRuns
        (dispatchSymbols tm state remaining symbols) store final
        (dispatchSteps tm state actual remaining)
        (dispatchCost tm bound state actual remaining)
        (spaceBound tm bound) ∧
      Represents tm next final ∧ ResourceEnvelope tm bound final := by
  subst state
  subst actual
  induction remaining generalizing symbols store with
  | nil =>
      have hsymbols : symbols = readSymbols cfg := by
        funext tape
        exact hassigned tape (by simp)
      subst symbols
      let final := Structured.Basic.execList
        (actionOps tm cfg.state (readSymbols cfg)) store
      have haction := actionOps_measured_internal hstep hrepresents hheads
        hworkStart houtputStart hone htapeCount henvelope
      refine ⟨final, ?_, haction.2.1, haction.2.2⟩
      simpa [dispatchSymbols, dispatchSteps, dispatchCost, final] using haction.1
  | cons tape rest ih =>
      have htapeCode := hloaded tape (by simp)
      have htestOne : symbolReg n tape ≠ oneReg n :=
        symbolReg_ne_one n tape
      let cleared := Structured.Switch.cleared store (symbolReg n tape)
      have hrange := scratch_range_internal n
      have hclearedRepresents : Represents tm cfg cleared :=
        cleared_represents hrepresents (hrange.2.2.2.2.2.2 tape).1
          (hrange.2.2.2.2.2.2 tape).2
      have hclearedOne : cleared (oneReg n) = 1 := by
        exact (cleared_apply_of_ne store htestOne.symm).trans hone
      have hclearedCount : cleared (tapeCountReg n) = n + 2 := by
        have hne : tapeCountReg n ≠ symbolReg n tape := by
          simp [tapeCountReg, symbolReg]
          omega
        exact (cleared_apply_of_ne store hne).trans htapeCount
      have hclearedEnvelope : ResourceEnvelope tm bound cleared :=
        cleared_envelope henvelope
          (lt_trans (hrange.2.2.2.2.2.2 tape).2
            (control_lt_registerBound n bound))
      have hclearedLoaded : ∀ candidate, candidate ∈ rest →
          cleared (symbolReg n candidate) =
            symbolCode (readSymbols cfg candidate) := by
        intro candidate hcandidate
        have hne : candidate ≠ tape := by
          intro heq
          subst candidate
          exact (List.nodup_cons.mp hnodup).1 hcandidate
        have hregs : symbolReg n candidate ≠ symbolReg n tape :=
          fun heq => hne ((symbolReg_injective n) heq)
        exact (cleared_apply_of_ne store hregs).trans
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
          (store := cleared) hclearedRepresents hclearedOne hclearedCount
          (List.nodup_cons.mp hnodup).2 hclearedEnvelope hclearedLoaded
          hclearedAssigned
      have hselectedBranch : Structured.Internal.MeasuredRuns
          ((fun code : Fin 4 =>
            dispatchSymbols tm cfg.state rest
              (Function.update symbols tape (symbolDecode code.val)))
            ⟨symbolCode (readSymbols cfg tape),
              symbolCode_lt_internal (readSymbols cfg tape)⟩)
          cleared final
          (dispatchSteps tm cfg.state (readSymbols cfg) rest)
          (dispatchCost tm bound cfg.state (readSymbols cfg) rest)
          (spaceBound tm bound) := by
        simpa [symbolDecode_code_internal] using hbranch
      have hrun := Structured.Switch.select_measured
        (fun code : Fin 4 =>
          dispatchSymbols tm cfg.state rest
            (Function.update symbols tape (symbolDecode code.val)))
        store final (symbolCode_lt_internal (readSymbols cfg tape))
        htapeCode hone htestOne
        (lt_trans (hrange.2.2.2.2.2.2 tape).2
          (control_lt_registerBound n bound))
        henvelope hselectedBranch
      refine ⟨final, ?_, hfinalRepresents, hfinalEnvelope⟩
      simpa [dispatchSymbols, dispatchSteps, dispatchCost, wordWidth,
        Structured.Internal.valueWidth, spaceBound,
        Structured.Internal.envelopeSpace] using hrun

theorem dispatchState_measured_internal {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm cfg store)
    (hheads : HeadsBounded cfg bound)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (hone : store (oneReg n) = 1)
    (htapeCount : store (tapeCountReg n) = n + 2)
    (hstate : store (stateScratchReg n) = stateCode tm cfg.state)
    (hloaded : ∀ tape, store (symbolReg n tape) =
      symbolCode (readSymbols cfg tape))
    (henvelope : ResourceEnvelope tm bound store) :
    ∃ final,
      Structured.Internal.MeasuredRuns (dispatchState tm) store final
        (Structured.Switch.stepCount (stateCode tm cfg.state)
          (dispatchSteps tm cfg.state (readSymbols cfg)
            (List.finRange (n + 2))))
        (Structured.Switch.costBound (stateCode tm cfg.state)
          (dispatchCost tm bound cfg.state (readSymbols cfg)
            (List.finRange (n + 2))) (wordWidth tm bound))
        (spaceBound tm bound) ∧
      Represents tm next final ∧ ResourceEnvelope tm bound final := by
  let cleared := Structured.Switch.cleared store (stateScratchReg n)
  have hrange := scratch_range_internal n
  have hclearedRepresents : Represents tm cfg cleared :=
    cleared_represents hrepresents hrange.2.2.2.1.1 hrange.2.2.2.1.2
  have hclearedOne : cleared (oneReg n) = 1 := by
    exact (cleared_apply_of_ne store (stateScratchReg_ne_one n).symm).trans hone
  have hclearedCount : cleared (tapeCountReg n) = n + 2 := by
    have hne : tapeCountReg n ≠ stateScratchReg n := by
      simp [tapeCountReg, stateScratchReg]
    exact (cleared_apply_of_ne store hne).trans htapeCount
  have hclearedEnvelope : ResourceEnvelope tm bound cleared :=
    cleared_envelope henvelope
      (lt_trans hrange.2.2.2.1.2 (control_lt_registerBound n bound))
  have hclearedLoaded : ∀ tape,
      cleared (symbolReg n tape) = symbolCode (readSymbols cfg tape) := by
    intro tape
    exact (cleared_apply_of_ne store
      (stateScratchReg_ne_symbolReg n tape)).trans (hloaded tape)
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
      hclearedOne hclearedCount rfl (fun tape _ => hclearedLoaded tape)
      (by simp) (List.nodup_finRange (n + 2)) hclearedEnvelope
  have hselectedBranch : Structured.Internal.MeasuredRuns
      ((fun stateCode : Fin (Fintype.card tm.Q) =>
        dispatchSymbols tm ((Fintype.equivFin tm.Q).symm stateCode)
          (List.finRange (n + 2)) (fun _ => Γ.blank))
        ⟨stateCode tm cfg.state, stateCode_lt_internal tm cfg.state⟩)
      cleared final
      (dispatchSteps tm cfg.state (readSymbols cfg) (List.finRange (n + 2)))
      (dispatchCost tm bound cfg.state (readSymbols cfg)
        (List.finRange (n + 2)))
      (spaceBound tm bound) := by
    simpa [hbranchState] using hbranch
  have hrun := Structured.Switch.select_measured
    (fun stateCode : Fin (Fintype.card tm.Q) =>
      dispatchSymbols tm ((Fintype.equivFin tm.Q).symm stateCode)
        (List.finRange (n + 2)) (fun _ => Γ.blank))
    store final (stateCode_lt_internal tm cfg.state) hstate hone
    (stateScratchReg_ne_one n)
    (lt_trans hrange.2.2.2.1.2 (control_lt_registerBound n bound))
    henvelope hselectedBranch
  refine ⟨final, ?_, hfinalRepresents, hfinalEnvelope⟩
  simpa [dispatchState, wordWidth, Structured.Internal.valueWidth, spaceBound,
    Structured.Internal.envelopeSpace] using hrun

end Sparse

end TMConfig

end RAM

end Complexity
