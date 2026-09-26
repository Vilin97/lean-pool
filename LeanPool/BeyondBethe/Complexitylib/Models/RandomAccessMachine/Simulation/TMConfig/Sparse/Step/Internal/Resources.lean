/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Step.Internal.Iteration
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Internal.Resources

/-!
# Resource envelopes for the fixed sparse TM simulator -- proof internals

The semantic simulation already records exact source steps, cost, and space.
This layer supplies the uniform finite-store envelope needed to turn those
measurements into explicit bounds depending only on input length and TM steps.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


/-- Shared envelope used by marshalling and repeated sparse simulation. -/
abbrev StepEnvelope (tm : TM n) (bound : ℕ) :=
  Structured.Internal.StoreEnvelope (registerBound n (bound + 1))
    (wordBound tm bound)

theorem bound_lt_registerBound_internal (n bound : ℕ) :
    bound < registerBound n (bound + 1) := by
  simp [registerBound, cellReg, outputTape, cellBase, Nat.mul_add]
  omega

theorem control_lt_registerBound_internal (n bound : ℕ) :
    cellBase n < registerBound n (bound + 1) := by
  simp [registerBound, cellReg, outputTape]
  omega

theorem cellReg_lt_registerBound_internal (tape : Fin (n + 2))
    {position bound : ℕ} (hposition : position ≤ bound + 1) :
    cellReg n tape position < registerBound n (bound + 1) := by
  have hmul := Nat.mul_le_mul_right (n + 2) hposition
  simp only [cellReg, registerBound, outputTape]
  omega

theorem cellReg_decode_internal (n reg : ℕ) (hreg : cellBase n ≤ reg) :
    cellReg n (decodeCellTape n reg) (decodeCellPosition n reg) = reg := by
  have hdivision := Nat.mod_add_div (reg - cellBase n) (n + 2)
  rw [Nat.mul_comm (n + 2)] at hdivision
  simp only [cellReg, decodeCellTape, decodeCellPosition]
  omega

theorem registerBound_le_wordBound_internal (tm : TM n) (bound : ℕ) :
    registerBound n (bound + 1) ≤ wordBound tm bound := by
  exact le_max_left _ _

theorem card_le_wordBound_internal (tm : TM n) (bound : ℕ) :
    Fintype.card tm.Q ≤ wordBound tm bound := by
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem bound_succ_le_wordBound_internal (tm : TM n) (bound : ℕ) :
    bound + 1 ≤ wordBound tm bound := by
  exact le_trans (le_max_right _ _) (le_max_right _ _)

private theorem tapeCount_le_wordBound (tm : TM n) (bound : ℕ) :
    n + 2 ≤ wordBound tm bound := by
  have hcontrol := control_lt_registerBound_internal n bound
  have hregister := registerBound_le_wordBound_internal tm bound
  simp [cellBase] at hcontrol
  omega

private theorem initRegs_index_le_length {x : List Bool} {reg : ℕ}
    (hnonzero : initRegs x reg ≠ 0) : reg ≤ x.length := by
  by_cases hreg : reg = 0
  · omega
  rw [initRegs, ite_eq_right hreg] at hnonzero
  cases hbit : x[reg - 1]? with
  | none => simp [hbit] at hnonzero
  | some bit =>
      have hindex : reg - 1 < x.length :=
        (List.getElem?_eq_some_iff.mp hbit).1
      omega

private theorem initRegs_value_le_length_succ (x : List Bool) (reg : ℕ) :
    initRegs x reg ≤ x.length + 1 := by
  rw [initRegs]
  split
  · omega
  · cases x[reg - 1]? with
    | none => simp
    | some bit => cases bit <;> simp

/-- The public RAM input store fits every sparse execution envelope whose bound
contains the input length. -/
theorem initRegs_envelope_internal (tm : TM n) (x : List Bool) (bound : ℕ)
    (hlength : x.length ≤ bound) : StepEnvelope tm bound (initRegs x) where
  index_lt _reg hnonzero :=
    lt_of_le_of_lt
      (le_trans (initRegs_index_le_length hnonzero) hlength)
      (bound_lt_registerBound_internal n bound)
  value_le reg :=
    le_trans (initRegs_value_le_length_succ x reg)
      (le_trans (Nat.add_le_add_right hlength 1)
        (bound_succ_le_wordBound_internal tm bound))

/-- The canonical sparse encoding fits the common execution envelope whenever
all heads and nonblank tape cells lie within the chosen bound. -/
theorem encodeRegs_envelope_internal (tm : TM n)
    (cfg : Complexity.Cfg n tm.Q) (bound : ℕ)
    (hbounded : Bounded cfg bound) (hheads : HeadsBounded cfg bound) :
    StepEnvelope tm bound (encodeRegs tm cfg) where
  index_lt reg hnonzero := by
    by_contra houtside
    have hindex : registerBound n (bound + 1) ≤ reg := by omega
    rw [encodeRegs] at hnonzero
    split at hnonzero
    · subst reg
      have := bound_lt_registerBound_internal n bound
      simp [stateReg] at hindex
      omega
    next hstate =>
      split at hnonzero
      · have hcontrol := control_lt_registerBound_internal n bound
        simp [cellBase] at hcontrol
        omega
      next hhead =>
        split at hnonzero
        · rename_i hcell
          have hreconstruct := cellReg_decode_internal n reg hcell
          have hposition : bound < decodeCellPosition n reg := by
            by_contra hlow
            have hpositionLe : decodeCellPosition n reg ≤ bound :=
              Nat.le_of_not_gt hlow
            have hcellLt := cellReg_lt_registerBound_internal
              (decodeCellTape n reg) (bound := bound)
              (show decodeCellPosition n reg ≤ bound + 1 by omega)
            rw [hreconstruct] at hcellLt
            omega
          rw [hbounded (decodeCellTape n reg) (decodeCellPosition n reg)
            hposition] at hnonzero
          simp [symbolCode] at hnonzero
        · simp at hnonzero
  value_le reg := by
    rw [encodeRegs]
    split
    · have hstateCode : stateCode tm cfg.state < Fintype.card tm.Q := by
        simp [stateCode]
      exact le_trans (Nat.le_of_lt hstateCode)
        (card_le_wordBound_internal tm bound)
    next hstate =>
      split
      · exact le_trans (hheads ⟨reg - 1, by omega⟩)
          (le_trans (Nat.le_succ bound)
            (bound_succ_le_wordBound_internal tm bound))
      next hhead =>
        split
        · have hsymbol := symbolCode_lt_internal
              ((tapeAt cfg (decodeCellTape n reg)).cells
                (decodeCellPosition n reg))
          have hfour : 4 ≤ registerBound n (bound + 1) := by
            have hcontrol := control_lt_registerBound_internal n bound
            simp [cellBase] at hcontrol
            omega
          exact le_trans (Nat.le_of_lt hsymbol)
            (le_trans hfour (registerBound_le_wordBound_internal tm bound))
        · exact Nat.zero_le _

private theorem setupOps_envelopeChain {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm cfg store)
    (henvelope : StepEnvelope tm bound store) :
    Structured.Internal.Basic.EnvelopeChain
      (registerBound n (bound + 1)) (wordBound tm bound)
      (setupOps n) store := by
  let first := (Structured.Basic.imm (zeroReg n) 0).exec store
  let second := (Structured.Basic.imm (oneReg n) 1).exec first
  let third := (Structured.Basic.imm (tapeCountReg n) (n + 2)).exec second
  let final := (Structured.Basic.add (stateScratchReg n) stateReg
    (zeroReg n)).exec third
  have hrange := scratch_range_internal n
  have hfirst : StepEnvelope tm bound first := by
    apply henvelope.execBasic
    · exact lt_trans hrange.1.2 (control_lt_registerBound_internal n bound)
    · simp [Structured.Internal.Basic.writeValue]
  have hone : 1 ≤ wordBound tm bound := by
    exact le_trans (show 1 ≤ n + 2 by omega)
      (tapeCount_le_wordBound tm bound)
  have hsecond : StepEnvelope tm bound second := by
    apply hfirst.execBasic
    · exact lt_trans hrange.2.1.2
        (control_lt_registerBound_internal n bound)
    · simpa [Structured.Internal.Basic.writeValue] using hone
  have hthird : StepEnvelope tm bound third := by
    apply hsecond.execBasic
    · exact lt_trans hrange.2.2.1.2
        (control_lt_registerBound_internal n bound)
    · simpa [Structured.Internal.Basic.writeValue] using
        tapeCount_le_wordBound tm bound
  have hstoreState : store stateReg = stateCode tm cfg.state := by
    have hstate := hrepresents (Sum.inl ⟨0, by omega⟩)
    exact hstate
  have hthirdState : third stateReg = store stateReg := by
    simp [third, second, first, Structured.Basic.exec, stateReg, zeroReg,
      oneReg, tapeCountReg, Function.update_of_ne]
  have hthirdZero : third (zeroReg n) = 0 := by
    simp [third, second, first, Structured.Basic.exec, zeroReg, oneReg,
      tapeCountReg, Function.update_of_ne]
  have hstateBound : stateCode tm cfg.state ≤ wordBound tm bound := by
    have hstateLt : stateCode tm cfg.state < Fintype.card tm.Q := by
      simp [stateCode]
    exact le_trans (Nat.le_of_lt hstateLt)
      (card_le_wordBound_internal tm bound)
  have hfinal : StepEnvelope tm bound final := by
    apply hthird.execBasic
    · exact lt_trans hrange.2.2.2.1.2
        (control_lt_registerBound_internal n bound)
    · simp only [Structured.Internal.Basic.writeValue]
      rw [hthirdState, hthirdZero, hstoreState, Nat.add_zero]
      exact hstateBound
  simpa [setupOps, first, second, third, final] using!
    And.intro henvelope
      (And.intro hfirst (And.intro hsecond (And.intro hthird hfinal)))

private theorem setupOps_represents {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm cfg store) :
    Represents tm cfg (Structured.Basic.execList (setupOps n) store) := by
  have hrange := scratch_range_internal n
  simp only [setupOps, Structured.Basic.execList]
  apply Represents.update_control_internal
  · apply Represents.update_control_internal
    · apply Represents.update_control_internal
      · exact hrepresents.update_control_internal hrange.1.1 hrange.1.2
      · exact hrange.2.1.1
      · exact hrange.2.1.2
    · exact hrange.2.2.1.1
    · exact hrange.2.2.1.2
  · exact hrange.2.2.2.1.1
  · exact hrange.2.2.2.1.2

private theorem setupOps_tapeCount (n : ℕ) (store : Structured.Store) :
    Structured.Basic.execList (setupOps n) store (tapeCountReg n) = n + 2 := by
  simp [setupOps, Structured.Basic.execList, Structured.Basic.exec, zeroReg,
    oneReg, tapeCountReg, stateScratchReg, Function.update_of_ne]

private theorem loadTapeOps_envelopeChain {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm cfg store) (tape : Fin (n + 2))
    (htapeCount : store (tapeCountReg n) = n + 2)
    (hhead : (tapeAt cfg tape).head ≤ bound)
    (henvelope : StepEnvelope tm bound store) :
    Structured.Internal.Basic.EnvelopeChain
      (registerBound n (bound + 1)) (wordBound tm bound)
      (loadTapeOps n tape) store := by
  let first := (Structured.Basic.imm (valueReg n)
    (cellBase n + tape.val)).exec store
  let multiplied := (Structured.Basic.mul (addressReg n) (headReg tape)
    (tapeCountReg n)).exec first
  let addressed := (Structured.Basic.add (addressReg n) (addressReg n)
    (valueReg n)).exec multiplied
  let final := (Structured.Basic.load (symbolReg n tape)
    (addressReg n)).exec addressed
  have hrange := scratch_range_internal n
  have hbaseLt : cellBase n + tape.val < registerBound n (bound + 1) := by
    have hcell := cellReg_lt_registerBound_internal tape
      (position := 0) (bound := bound) (by omega)
    simpa [cellReg] using hcell
  have hbaseBound : cellBase n + tape.val ≤ wordBound tm bound :=
    le_trans (Nat.le_of_lt hbaseLt)
      (registerBound_le_wordBound_internal tm bound)
  have hfirst : StepEnvelope tm bound first := by
    apply henvelope.execBasic
    · exact lt_trans hrange.2.2.2.2.2.1.2
        (control_lt_registerBound_internal n bound)
    · simpa [Structured.Internal.Basic.writeValue] using hbaseBound
  have hstoreHead : store (headReg tape) = (tapeAt cfg tape).head := by
    exact hrepresents (Sum.inr (Sum.inl tape))
  have hfirstHead : first (headReg tape) = store (headReg tape) := by
    have hne : headReg tape ≠ valueReg n := by
      simp [headReg, valueReg]
      omega
    simp [first, Structured.Basic.exec, Function.update_of_ne hne]
  have hfirstCount : first (tapeCountReg n) = store (tapeCountReg n) := by
    have hne : tapeCountReg n ≠ valueReg n := by
      simp [tapeCountReg, valueReg]
    simp [first, Structured.Basic.exec, Function.update_of_ne hne]
  have hproductBound : (tapeAt cfg tape).head * (n + 2) ≤
      wordBound tm bound := by
    have hcell := cellReg_lt_registerBound_internal tape
      (position := (tapeAt cfg tape).head) (bound := bound) (by omega)
    have hproduct : (tapeAt cfg tape).head * (n + 2) <
        registerBound n (bound + 1) := by
      simp [cellReg] at hcell
      omega
    exact le_trans (Nat.le_of_lt hproduct)
      (registerBound_le_wordBound_internal tm bound)
  have hmultiplied : StepEnvelope tm bound multiplied := by
    apply hfirst.execBasic
    · exact lt_trans hrange.2.2.2.2.1.2
        (control_lt_registerBound_internal n bound)
    · simp only [Structured.Internal.Basic.writeValue]
      rw [hfirstHead, hfirstCount, hstoreHead, htapeCount]
      exact hproductBound
  have hmultipliedAddress : multiplied (addressReg n) =
      (tapeAt cfg tape).head * (n + 2) := by
    simp only [multiplied, Structured.Basic.exec, Function.update_self]
    rw [hfirstHead, hfirstCount, hstoreHead, htapeCount]
  have hmultipliedValue : multiplied (valueReg n) =
      cellBase n + tape.val := by
    have hne : valueReg n ≠ addressReg n := by
      simp [valueReg, addressReg]
    simp [multiplied, first, Structured.Basic.exec,
      Function.update_of_ne hne]
  have hcellBound : cellReg n tape (tapeAt cfg tape).head ≤
      wordBound tm bound := by
    exact le_trans (Nat.le_of_lt
      (cellReg_lt_registerBound_internal tape (bound := bound) (by omega)))
      (registerBound_le_wordBound_internal tm bound)
  have haddressed : StepEnvelope tm bound addressed := by
    apply hmultiplied.execBasic
    · exact lt_trans hrange.2.2.2.2.1.2
        (control_lt_registerBound_internal n bound)
    · simp only [Structured.Internal.Basic.writeValue]
      rw [hmultipliedAddress, hmultipliedValue]
      simp [cellReg] at hcellBound
      omega
  have hfinal : StepEnvelope tm bound final := by
    apply haddressed.execBasic
    · exact lt_trans (hrange.2.2.2.2.2.2 tape).2
        (control_lt_registerBound_internal n bound)
    · exact haddressed.value_le (addressed (addressReg n))
  simpa [loadTapeOps, addressOps, first, multiplied, addressed, final] using!
    And.intro henvelope
      (And.intro hfirst (And.intro hmultiplied (And.intro haddressed hfinal)))

private theorem loadTapes_envelopeChain {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} (tapes : List (Fin (n + 2)))
    {store : Structured.Store} (hrepresents : Represents tm cfg store)
    (htapeCount : store (tapeCountReg n) = n + 2)
    (hheads : HeadsBounded cfg bound)
    (henvelope : StepEnvelope tm bound store) :
    Structured.Internal.Basic.EnvelopeChain
      (registerBound n (bound + 1)) (wordBound tm bound)
      (tapes.flatMap (loadTapeOps n)) store := by
  induction tapes generalizing store with
  | nil => exact henvelope
  | cons tape rest ih =>
      have hfirst := loadTapeOps_envelopeChain hrepresents tape htapeCount
        (hheads tape) henvelope
      have hfirstRepresents := loadTapeOps_represents_internal hrepresents tape
      have hcountPreserved :
          Structured.Basic.execList (loadTapeOps n tape) store
              (tapeCountReg n) = n + 2 := by
        have hvalue : tapeCountReg n ≠ valueReg n := by
          simp [tapeCountReg, valueReg]
        have haddress : tapeCountReg n ≠ addressReg n := by
          simp [tapeCountReg, addressReg]
        have hsymbol : tapeCountReg n ≠ symbolReg n tape := by
          simp [tapeCountReg, symbolReg]
          omega
        simpa [loadTapeOps, addressOps, Structured.Basic.execList,
          Structured.Basic.exec, Function.update_of_ne hvalue,
          Function.update_of_ne haddress, Function.update_of_ne hsymbol]
          using htapeCount
      have hrest := ih hfirstRepresents hcountPreserved hfirst.final
      simpa [List.flatMap_cons] using hfirst.append hrest

theorem loadOps_measured_internal {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm cfg store)
    (hheads : HeadsBounded cfg bound)
    (henvelope : StepEnvelope tm bound store) :
    let final := Structured.Basic.execList (loadOps n) store
    Structured.Internal.MeasuredRuns (.basics (loadOps n)) store final
      (loadOps n).length
      (4 * (loadOps n).length * wordWidth tm bound)
      (spaceBound tm bound) ∧ StepEnvelope tm bound final := by
  have hsetup := setupOps_envelopeChain hrepresents henvelope
  have hsetupRepresents : Represents tm cfg
      (Structured.Basic.execList (setupOps n) store) := by
    exact setupOps_represents hrepresents
  have hsetupCount :
      Structured.Basic.execList (setupOps n) store (tapeCountReg n) = n + 2 := by
    exact setupOps_tapeCount n store
  have htapes := loadTapes_envelopeChain (List.finRange (n + 2))
    hsetupRepresents hsetupCount hheads hsetup.final
  have hchain : Structured.Internal.Basic.EnvelopeChain
      (registerBound n (bound + 1)) (wordBound tm bound)
      (loadOps n) store := by
    simpa [loadOps] using hsetup.append htapes
  have hmeasured := Structured.Internal.MeasuredRuns.basicsEnvelopeChain
    (loadOps n) store hchain
  simpa [wordWidth, spaceBound, Structured.Internal.valueWidth,
    Structured.Internal.envelopeSpace] using hmeasured

private theorem cleared_apply_of_ne (store : Structured.Store) {test reg : ℕ}
    (hne : reg ≠ test) :
    Structured.Switch.cleared store test reg = store reg := by
  simp [Structured.Switch.cleared, Function.update_of_ne hne]

private theorem stateScratchReg_ne_one (n : ℕ) :
    stateScratchReg n ≠ oneReg n := by
  simp [stateScratchReg, oneReg]

theorem continueCheck_measured_internal {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm cfg store)
    (hheads : HeadsBounded cfg bound)
    (henvelope : StepEnvelope tm bound store) :
    ∃ final,
      Structured.Internal.MeasuredRuns (continueCheck tm) store final
        (continueSteps tm cfg) (continueTimeBound tm bound cfg)
        (spaceBound tm bound) ∧
      Represents tm cfg final ∧
      final (valueReg n) = runningFlag tm cfg.state ∧
      final (oneReg n) = 1 ∧
      final (tapeCountReg n) = n + 2 ∧
      StepEnvelope tm bound final := by
  let loaded := Structured.Basic.execList (loadOps n) store
  have hload := loadOps_measured_internal hrepresents hheads henvelope
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
  have hclearedEnvelope : StepEnvelope tm bound cleared := by
    exact hload.2.update
      (lt_trans hrange.2.2.2.1.2
        (control_lt_registerBound_internal n bound)) (by simp)
  let final := (Structured.Basic.imm (valueReg n)
    (runningFlag tm cfg.state)).exec cleared
  have hflagBound : runningFlag tm cfg.state ≤ wordBound tm bound := by
    have hone : 1 ≤ wordBound tm bound := by
      exact le_trans (show 1 ≤ n + 2 by omega)
        (tapeCount_le_wordBound tm bound)
    simp [runningFlag]
    split <;> omega
  have hfinalEnvelope : StepEnvelope tm bound final := by
    apply hclearedEnvelope.execBasic
    · exact lt_trans hrange.2.2.2.2.2.1.2
        (control_lt_registerBound_internal n bound)
    · simpa [Structured.Internal.Basic.writeValue] using hflagBound
  have hbranch := Structured.Internal.MeasuredRuns.basicEnvelope
    (Structured.Basic.imm (valueReg n) (runningFlag tm cfg.state))
    cleared hclearedEnvelope hfinalEnvelope
  have hbranchState :
      (Fintype.equivFin tm.Q).symm
          ⟨stateCode tm cfg.state, by simp [stateCode]⟩ = cfg.state :=
    (Fintype.equivFin tm.Q).symm_apply_apply cfg.state
  have hselectedBranch : Structured.Internal.MeasuredRuns
      ((fun code : Fin (Fintype.card tm.Q) => .basics
        [.imm (valueReg n)
          (runningFlag tm ((Fintype.equivFin tm.Q).symm code))])
        ⟨stateCode tm cfg.state, by simp [stateCode]⟩)
      cleared final 1 (4 * wordWidth tm bound) (spaceBound tm bound) := by
    simpa [hbranchState, final, wordWidth, Structured.Internal.valueWidth,
      spaceBound, Structured.Internal.envelopeSpace] using! hbranch
  have hdispatch := Structured.Switch.select_measured
    (fun code : Fin (Fintype.card tm.Q) => .basics
      [.imm (valueReg n)
        (runningFlag tm ((Fintype.equivFin tm.Q).symm code))])
    loaded final (by simp [stateCode]) hloaded.2.2.2.2.1
    hloaded.2.2.1 (stateScratchReg_ne_one n)
    (lt_trans hrange.2.2.2.1.2
      (control_lt_registerBound_internal n bound))
    hload.2 hselectedBranch
  have hrun := hload.1.seq hdispatch
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
  refine ⟨final, ?_, hfinalRepresents, hfinalValue, hfinalOne, hfinalCount,
    hfinalEnvelope⟩
  simpa [continueCheck, continueDispatch, continueSteps, continueTimeBound,
    loaded, wordWidth, Structured.Internal.valueWidth, spaceBound,
    Structured.Internal.envelopeSpace] using hrun

theorem headsBounded_step_internal {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} (hstep : tm.step cfg = some next)
    (hheads : HeadsBounded cfg bound) : HeadsBounded next (bound + 1) := by
  have hnotHalted := TM.state_ne_qhalt_of_step hstep
  rcases hdelta : tm.δ cfg.state cfg.input.read
      (fun i => (cfg.work i).read) cfg.output.read with
    ⟨nextState, workWrites, outputWrite, inputDirection,
      workDirections, outputDirection⟩
  rw [TM.step, ite_eq_right hnotHalted, hdelta] at hstep
  dsimp only at hstep
  injection hstep with hnext
  subst next
  intro tape
  by_cases hinput : tape = inputTape n
  · subst tape
    rw [show tapeAt
        { state := nextState
          input := cfg.input.move inputDirection
          work := fun i => (cfg.work i).writeAndMove
            (workWrites i).toΓ (workDirections i)
          output := cfg.output.writeAndMove outputWrite.toΓ outputDirection }
        (inputTape n) = cfg.input.move inputDirection by
      simpa [inputTape] using tapeAt_input_internal
        ({ state := nextState
           input := cfg.input.move inputDirection
           work := fun i => (cfg.work i).writeAndMove
             (workWrites i).toΓ (workDirections i)
           output := cfg.output.writeAndMove outputWrite.toΓ outputDirection } :
          Complexity.Cfg n tm.Q)]
    have h := hheads (inputTape n)
    rw [show tapeAt cfg (inputTape n) = cfg.input by
      simpa [inputTape] using tapeAt_input_internal cfg] at h
    cases inputDirection <;> simp [Tape.move] <;> omega
  · by_cases houtput : tape = outputTape n
    · subst tape
      rw [show tapeAt
          { state := nextState
            input := cfg.input.move inputDirection
            work := fun i => (cfg.work i).writeAndMove
              (workWrites i).toΓ (workDirections i)
            output := cfg.output.writeAndMove outputWrite.toΓ outputDirection }
          (outputTape n) = cfg.output.writeAndMove outputWrite.toΓ outputDirection by
        simpa [outputTape] using tapeAt_output_internal
          ({ state := nextState
             input := cfg.input.move inputDirection
             work := fun i => (cfg.work i).writeAndMove
               (workWrites i).toΓ (workDirections i)
             output := cfg.output.writeAndMove outputWrite.toΓ outputDirection } :
            Complexity.Cfg n tm.Q)]
      have h := hheads (outputTape n)
      rw [show tapeAt cfg (outputTape n) = cfg.output by
        simpa [outputTape] using tapeAt_output_internal cfg] at h
      cases outputDirection <;>
        simp [Tape.writeAndMove, Tape.move, Tape.write_head] <;> omega
    · let i : Fin n := ⟨tape.val - 1, by
        have hpositive : 0 < tape.val := by
          have hnezero : tape.val ≠ 0 := by
            intro hzero
            apply hinput
            apply Fin.ext
            simpa [inputTape] using hzero
          omega
        have hnotOutput : tape.val ≠ n + 1 := by
          intro heq
          apply houtput
          apply Fin.ext
          simpa [outputTape] using heq
        omega⟩
      have htape : tape = workTape i := by
        apply Fin.ext
        simp [i, workTape]
        have hpositive : 0 < tape.val := by
          have hnezero : tape.val ≠ 0 := by
            intro hzero
            apply hinput
            apply Fin.ext
            simpa [inputTape] using hzero
          omega
        omega
      rw [htape]
      rw [show tapeAt
          { state := nextState
            input := cfg.input.move inputDirection
            work := fun i => (cfg.work i).writeAndMove
              (workWrites i).toΓ (workDirections i)
            output := cfg.output.writeAndMove outputWrite.toΓ outputDirection }
          (workTape i) = (cfg.work i).writeAndMove
            (workWrites i).toΓ (workDirections i) by
        simpa [workTape] using tapeAt_work_internal
          ({ state := nextState
             input := cfg.input.move inputDirection
             work := fun i => (cfg.work i).writeAndMove
               (workWrites i).toΓ (workDirections i)
             output := cfg.output.writeAndMove outputWrite.toΓ outputDirection } :
            Complexity.Cfg n tm.Q) i]
      have h := hheads (workTape i)
      rw [show tapeAt cfg (workTape i) = cfg.work i by
        simpa [workTape] using tapeAt_work_internal cfg i] at h
      cases workDirections i <;>
        simp [Tape.writeAndMove, Tape.move, Tape.write_head] <;> omega

theorem program_measured_internal {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm cfg store)
    (hheads : HeadsBounded cfg bound)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (henvelope : StepEnvelope tm bound store) :
    ∃ final,
      Structured.Internal.MeasuredRuns (program tm) store final
        (stepCount tm cfg) (timeBound tm bound cfg) (spaceBound tm bound) ∧
      Represents tm next final ∧ StepEnvelope tm bound final := by
  let loaded := Structured.Basic.execList (loadOps n) store
  have hload := loadOps_measured_internal hrepresents hheads henvelope
  have hloaded := loadOps_loaded_internal hrepresents
  obtain ⟨final, hdispatch, hfinalRepresents, hfinalEnvelope⟩ :=
    dispatchState_measured_internal hstep hloaded.1 hheads hworkStart
      houtputStart hloaded.2.2.1 hloaded.2.2.2.1 hloaded.2.2.2.2.1
      hloaded.2.2.2.2.2 hload.2
  have hrun := hload.1.seq hdispatch
  refine ⟨final, ?_, hfinalRepresents, hfinalEnvelope⟩
  simpa [program, stepCount, timeBound, loaded] using hrun

private theorem headsBounded_mono {cfg : Complexity.Cfg n Q}
    {bound larger : ℕ} (hheads : HeadsBounded cfg bound)
    (hle : bound ≤ larger) : HeadsBounded cfg larger := by
  intro tape
  exact le_trans (hheads tape) hle

theorem loop_measured_internal {tm : TM n} {steps base : ℕ}
    {cfg halted : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hreach : tm.reachesIn steps cfg halted)
    (hhalted : tm.halted halted)
    (hrepresents : Represents tm cfg store)
    (hflag : store (valueReg n) = runningFlag tm cfg.state)
    (hheads : HeadsBounded cfg base)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (henvelope : StepEnvelope tm (base + steps) store) :
    ∃ final,
      Structured.Internal.MeasuredRuns
        (.whileNonzero (valueReg n) (loopBody tm)) store final
        (loopSteps tm steps cfg) (loopTimeBound tm base steps cfg)
        (spaceBound tm (base + steps)) ∧
      Represents tm halted final ∧
      StepEnvelope tm (base + steps) final := by
  induction hreach generalizing store base with
  | zero =>
      have hzero : store (valueReg n) = 0 := by
        rw [hflag]
        simp [runningFlag, hhalted]
      have hrun := Structured.Internal.MeasuredRuns.whileZeroEnvelope
        (body := loopBody tm) hzero henvelope
      refine ⟨store, ?_, hrepresents, henvelope⟩
      simpa [loopSteps, loopTimeBound, wordWidth, spaceBound,
        Structured.Internal.valueWidth,
        Structured.Internal.envelopeSpace] using hrun
  | @step current successor tail finalCfg hstep htail ih =>
      have hnotHalted := TM.state_ne_qhalt_of_step hstep
      have hnonzero : store (valueReg n) ≠ 0 := by
        rw [hflag]
        simp [runningFlag, hnotHalted]
      let bound := base + tail + 1
      have hheadsBound : HeadsBounded current bound :=
        headsBounded_mono hheads (by simp [bound]; omega)
      obtain ⟨middle, hprogram, hmiddleRepresents, hmiddleEnvelope⟩ :=
        program_measured_internal (bound := bound) hstep hrepresents
          hheadsBound hworkStart houtputStart (by
            simpa [bound, Nat.add_assoc] using henvelope)
      have hsuccessorHeads : HeadsBounded successor (base + 1) :=
        headsBounded_step_internal hstep hheads
      have hsuccessorHeadsBound : HeadsBounded successor bound :=
        headsBounded_mono hsuccessorHeads (by simp [bound])
      obtain ⟨checked, hcheck, hcheckedRepresents, hcheckedFlag,
          _hcheckedOne, _hcheckedCount, hcheckedEnvelope⟩ :=
        continueCheck_measured_internal (bound := bound) hmiddleRepresents
          hsuccessorHeadsBound hmiddleEnvelope
      have hstarts := starts_of_step_internal hstep hworkStart houtputStart
      have hboundEq : (base + 1) + tail = bound := by
        simp [bound]
        omega
      obtain ⟨final, hloop, hfinalRepresents, hfinalEnvelope⟩ :=
        ih (base := base + 1) hhalted hcheckedRepresents hcheckedFlag
          hsuccessorHeads hstarts.1 hstarts.2 (by
            rw [hboundEq]
            exact hcheckedEnvelope)
      rw [hboundEq] at hloop hfinalEnvelope
      have hbody := hprogram.seq hcheck
      have hloop' : Structured.Internal.MeasuredRuns
          (.whileNonzero (valueReg n) (loopBody tm)) checked final
          (loopSteps tm tail successor)
          (loopTimeBound tm (base + 1) tail successor)
          (spaceBound tm bound) := by
        exact hloop
      have hbody' : Structured.Internal.MeasuredRuns (loopBody tm) store checked
          (stepCount tm current + continueSteps tm successor)
          (timeBound tm bound current + continueTimeBound tm bound successor)
          (spaceBound tm bound) := by
        simpa [loopBody] using hbody
      have hrun := Structured.Internal.MeasuredRuns.whileNonzeroEnvelope
        hnonzero (by simpa [bound, Nat.add_assoc] using! henvelope) hbody' hloop'
      refine ⟨final, ?_, hfinalRepresents, ?_⟩
      · simpa [loopSteps, loopTimeBound, hstep, bound, wordWidth,
          Structured.Internal.valueWidth, spaceBound,
          Structured.Internal.envelopeSpace, Nat.add_assoc] using hrun
      · simpa [bound, Nat.add_assoc] using hfinalEnvelope

theorem runUntilHalt_measured_internal {tm : TM n} {steps base : ℕ}
    {cfg halted : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hreach : tm.reachesIn steps cfg halted)
    (hhalted : tm.halted halted)
    (hrepresents : Represents tm cfg store)
    (hheads : HeadsBounded cfg base)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (henvelope : StepEnvelope tm (base + steps) store) :
    ∃ final,
      Structured.Internal.MeasuredRuns (runUntilHalt tm) store final
        (runSteps tm steps cfg) (runTimeBound tm base steps cfg)
        (spaceBound tm (base + steps)) ∧
      Represents tm halted final ∧
      StepEnvelope tm (base + steps) final := by
  have hheadsBound : HeadsBounded cfg (base + steps) :=
    headsBounded_mono hheads (by omega)
  obtain ⟨checked, hcheck, hcheckedRepresents, hcheckedFlag,
      _hcheckedOne, _hcheckedCount, hcheckedEnvelope⟩ :=
    continueCheck_measured_internal (bound := base + steps) hrepresents
      hheadsBound henvelope
  obtain ⟨final, hloop, hfinalRepresents, hfinalEnvelope⟩ :=
    loop_measured_internal hreach hhalted hcheckedRepresents hcheckedFlag
      hheads hworkStart houtputStart hcheckedEnvelope
  have hrun := hcheck.seq hloop
  refine ⟨final, ?_, hfinalRepresents, hfinalEnvelope⟩
  simpa [runUntilHalt, runSteps, runTimeBound] using hrun

private theorem dispatchCost_eq_factor (tm : TM n) (bound : ℕ)
    (state : tm.Q) (actual : Fin (n + 2) → Γ)
    (remaining : List (Fin (n + 2))) :
    dispatchCost tm bound state actual remaining =
      dispatchFactor tm state actual remaining * wordWidth tm bound := by
  induction remaining with
  | nil => simp [dispatchCost, dispatchFactor]
  | cons tape rest ih =>
      simp [dispatchCost, dispatchFactor, Structured.Switch.costBound, ih]
      ring

theorem timeBound_le_stepFactor_internal (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) :
    timeBound tm bound cfg ≤ stepFactor tm * wordWidth tm bound := by
  have hfactor : 7 * stateCode tm cfg.state + 1 +
        dispatchFactor tm cfg.state (readSymbols cfg)
          (List.finRange (n + 2)) ≤
      Finset.univ.sup fun state : tm.Q =>
        Finset.univ.sup fun actual : Fin (n + 2) → Γ =>
          7 * stateCode tm state + 1 +
            dispatchFactor tm state actual (List.finRange (n + 2)) := by
    apply le_trans
      (Finset.le_sup
        (f := fun actual : Fin (n + 2) → Γ =>
          7 * stateCode tm cfg.state + 1 +
            dispatchFactor tm cfg.state actual (List.finRange (n + 2)))
        (Finset.mem_univ (readSymbols cfg)))
    exact Finset.le_sup
      (f := fun state : tm.Q =>
        Finset.univ.sup fun actual : Fin (n + 2) → Γ =>
          7 * stateCode tm state + 1 +
            dispatchFactor tm state actual (List.finRange (n + 2)))
      (Finset.mem_univ cfg.state)
  rw [timeBound, dispatchCost_eq_factor]
  simp only [Structured.Switch.costBound]
  calc
    4 * (loadOps n).length * wordWidth tm bound +
          ((7 * stateCode tm cfg.state + 1) * wordWidth tm bound +
            dispatchFactor tm cfg.state (readSymbols cfg)
              (List.finRange (n + 2)) * wordWidth tm bound)
        = (4 * (loadOps n).length +
            (7 * stateCode tm cfg.state + 1 +
              dispatchFactor tm cfg.state (readSymbols cfg)
                (List.finRange (n + 2)))) * wordWidth tm bound := by ring
    _ ≤ (4 * (loadOps n).length +
          Finset.univ.sup fun state : tm.Q =>
            Finset.univ.sup fun actual : Fin (n + 2) → Γ =>
              7 * stateCode tm state + 1 +
                dispatchFactor tm state actual (List.finRange (n + 2))) *
          wordWidth tm bound := Nat.mul_le_mul_right _
            (Nat.add_le_add_left hfactor _)
    _ = stepFactor tm * wordWidth tm bound := by rfl

theorem continueTimeBound_le_factor_internal (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) :
    continueTimeBound tm bound cfg ≤
      continueFactor tm * wordWidth tm bound := by
  have hstate : stateCode tm cfg.state < Fintype.card tm.Q := by
    simp [stateCode]
  simp only [continueTimeBound, Structured.Switch.costBound, continueFactor]
  calc
    4 * (loadOps n).length * wordWidth tm bound +
          ((7 * stateCode tm cfg.state + 1) * wordWidth tm bound +
            4 * wordWidth tm bound)
        = (4 * (loadOps n).length +
            (7 * stateCode tm cfg.state + 5)) * wordWidth tm bound := by ring
    _ ≤ (4 * (loadOps n).length +
          (7 * Fintype.card tm.Q + 5)) * wordWidth tm bound := by
      apply Nat.mul_le_mul_right
      omega

theorem loopTimeBound_le_linear_internal (tm : TM n) (base steps : ℕ)
    (cfg : Complexity.Cfg n tm.Q) :
    loopTimeBound tm base steps cfg ≤
      (steps * iterationFactor tm + 1) * wordWidth tm (base + steps) := by
  induction steps generalizing base cfg with
  | zero => simp [loopTimeBound]
  | succ steps ih =>
      rw [loopTimeBound]
      split
      · exact Nat.zero_le _
      · rename_i next hstep
        have hstepBound := timeBound_le_stepFactor_internal tm
          (base + steps + 1) cfg
        have hcheckBound := continueTimeBound_le_factor_internal tm
          (base + steps + 1) next
        have htail := ih (base := base + 1) (cfg := next)
        have hwidth : wordWidth tm ((base + 1) + steps) =
            wordWidth tm (base + (steps + 1)) := by
          congr 1
          omega
        rw [hwidth] at htail
        have hboundWidth : wordWidth tm (base + steps + 1) =
            wordWidth tm (base + (steps + 1)) := by
          congr 1
        rw [hboundWidth] at hstepBound hcheckBound
        calc
          3 * wordWidth tm (base + steps + 1) +
                timeBound tm (base + steps + 1) cfg +
                continueTimeBound tm (base + steps + 1) next +
                loopTimeBound tm (base + 1) steps next
              ≤ 3 * wordWidth tm (base + (steps + 1)) +
                stepFactor tm * wordWidth tm (base + (steps + 1)) +
                continueFactor tm * wordWidth tm (base + (steps + 1)) +
                (steps * iterationFactor tm + 1) *
                  wordWidth tm (base + (steps + 1)) := by
                    rw [hboundWidth]
                    omega
          _ = ((steps + 1) * iterationFactor tm + 1) *
                wordWidth tm (base + (steps + 1)) := by
                  simp [iterationFactor]
                  ring

theorem runTimeBound_le_linear_internal (tm : TM n) (base steps : ℕ)
    (cfg : Complexity.Cfg n tm.Q) :
    runTimeBound tm base steps cfg ≤
      ((steps + 1) * runFactor tm) * wordWidth tm (base + steps) := by
  have hcheck := continueTimeBound_le_factor_internal tm (base + steps) cfg
  have hloop := loopTimeBound_le_linear_internal tm base steps cfg
  rw [runTimeBound]
  calc
    continueTimeBound tm (base + steps) cfg + loopTimeBound tm base steps cfg
        ≤ continueFactor tm * wordWidth tm (base + steps) +
          (steps * iterationFactor tm + 1) *
            wordWidth tm (base + steps) := Nat.add_le_add hcheck hloop
    _ ≤ ((steps + 1) * runFactor tm) * wordWidth tm (base + steps) := by
      have hc : continueFactor tm ≤ (steps + 1) * continueFactor tm := by
        simpa only [one_mul] using
          Nat.mul_le_mul_right (continueFactor tm) (show 1 ≤ steps + 1 by omega)
      have hi : steps * iterationFactor tm ≤
          (steps + 1) * iterationFactor tm :=
        Nat.mul_le_mul_right (iterationFactor tm) (Nat.le_succ steps)
      have hone : 1 ≤ steps + 1 := by omega
      rw [show continueFactor tm * wordWidth tm (base + steps) +
          (steps * iterationFactor tm + 1) * wordWidth tm (base + steps) =
          (continueFactor tm + steps * iterationFactor tm + 1) *
            wordWidth tm (base + steps) by ring]
      apply Nat.mul_le_mul_right
      simp only [runFactor]
      calc
        continueFactor tm + steps * iterationFactor tm + 1
            ≤ (steps + 1) * continueFactor tm +
              (steps + 1) * iterationFactor tm + (steps + 1) := by omega
        _ = (steps + 1) *
              (continueFactor tm + iterationFactor tm + 1) := by ring

end Sparse

end TMConfig

end RAM

end Complexity
