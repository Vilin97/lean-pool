/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Internal.Resources
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Switch.Defs

/-!
# Finite numeric structured-RAM switches -- proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace Switch


open Internal

private theorem cleared_eq_self {store : Store} {test : ℕ}
    (htest : store test = 0) : cleared store test = store := by
  funext index
  by_cases hindex : index = test
  · subst index
    simp [cleared, htest]
  · simp [cleared, Function.update_of_ne hindex]

private theorem cleared_sub_eq (store : Store) (test one : ℕ) :
    cleared ((Basic.sub test test one).exec store) test = cleared store test := by
  funext index
  by_cases hindex : index = test
  · subst index
    simp [cleared]
  · simp [cleared, Basic.exec, Function.update_of_ne hindex]

theorem select_exec_internal {count test one : ℕ}
    (branch : Fin count → Cmd) (initial final : Store)
    {code branchSteps : ℕ}
    (hcode : code < count) (htest : initial test = code)
    (hone : initial one = 1) (hne : test ≠ one)
    (hbranch : ∃ cost space,
      Exec (branch ⟨code, hcode⟩) (cleared initial test) final
        branchSteps cost space) :
    ∃ cost space,
      Exec (select count test one branch) initial final
        (stepCount code branchSteps) cost space := by
  induction count generalizing code initial with
  | zero => omega
  | succ count ih =>
      by_cases hzero : code = 0
      · have htestZero : initial test = 0 := htest.trans hzero
        have hclear : cleared initial test = initial := cleared_eq_self htestZero
        obtain ⟨branchCost, branchSpace, hbranchExec⟩ := hbranch
        have hbranchZero :
            Exec (branch ⟨0, by omega⟩) initial final branchSteps
              branchCost branchSpace := by
          rw [← hclear]
          simpa [hzero] using hbranchExec
        refine ⟨bitlen (initial test) + 1 + branchCost,
          max initial.space branchSpace, ?_⟩
        simpa [select, stepCount, hzero] using
          Exec.ifZero htestZero hbranchZero
      · obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
        have hpredecessor : predecessor < count := by omega
        let next := (Basic.sub test test one).exec initial
        have hnextTest : next test = predecessor := by
          simp [next, Basic.exec, htest, hone]
        have hnextOne : next one = 1 := by
          rw [show next one = initial one by
            simp [next, Basic.exec, Function.update_of_ne (Ne.symm hne)]]
          exact hone
        have hclear : cleared next test = cleared initial test := by
          exact cleared_sub_eq initial test one
        have hrecursiveBranch :
            ∃ cost space,
              Exec ((fun index : Fin count => branch index.succ)
                ⟨predecessor, hpredecessor⟩)
                (cleared next test) final branchSteps cost space := by
          rw [hclear]
          simpa using hbranch
        obtain ⟨recursiveCost, recursiveSpace, hrecursive⟩ :=
          ih (branch := fun index => branch index.succ) (initial := next)
            hpredecessor hnextTest hnextOne hrecursiveBranch
        have hdecrement := Exec.basic (.sub test test one) initial
        have hsequence := Exec.seq hdecrement hrecursive
        have hnonzero : initial test ≠ 0 := by omega
        have hrun := Exec.ifNonzero
          (onZero := branch ⟨0, by omega⟩) hnonzero hsequence
        refine ⟨bitlen (initial test) + 1 +
            ((Basic.sub test test one).logCost initial + recursiveCost) + 1,
          max initial.space
            (max (max initial.space
              ((Basic.sub test test one).exec initial).space) recursiveSpace), ?_⟩
        convert! hrun using 1
        all_goals simp [stepCount]
        all_goals omega

theorem select_measured_internal {count test one indexBound valueBound : ℕ}
    (branch : Fin count → Cmd) (initial final : Store)
    {code branchSteps branchCost : ℕ}
    (hcode : code < count) (htest : initial test = code)
    (hone : initial one = 1) (hne : test ≠ one)
    (htestIndex : test < indexBound)
    (hinitial : StoreEnvelope indexBound valueBound initial)
    (hbranch : MeasuredRuns (branch ⟨code, hcode⟩) (cleared initial test)
      final branchSteps branchCost (envelopeSpace indexBound valueBound)) :
    MeasuredRuns (select count test one branch) initial final
      (stepCount code branchSteps)
      (costBound code branchCost (valueWidth valueBound))
      (envelopeSpace indexBound valueBound) := by
  induction count generalizing code initial with
  | zero => omega
  | succ count ih =>
      by_cases hzero : code = 0
      · have htestZero : initial test = 0 := htest.trans hzero
        have hclear : cleared initial test = initial := cleared_eq_self htestZero
        have hcount : 0 < count + 1 := by omega
        have hbranchZero :
            MeasuredRuns (branch ⟨0, hcount⟩) initial final branchSteps
              branchCost (envelopeSpace indexBound valueBound) := by
          rw [← hclear]
          simpa [hzero] using hbranch
        have hrun := MeasuredRuns.ifZeroEnvelope
          (onNonzero := .seq (.basic (.sub test test one))
            (select count test one (fun index => branch index.succ)))
          htestZero hinitial hbranchZero
        simpa [select, stepCount, costBound, hzero] using hrun
      · obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
        have hpredecessor : predecessor < count := by omega
        let next := (Basic.sub test test one).exec initial
        have hnextTest : next test = predecessor := by
          simp [next, Basic.exec, htest, hone]
        have hnextOne : next one = 1 := by
          rw [show next one = initial one by
            simp [next, Basic.exec, Function.update_of_ne (Ne.symm hne)]]
          exact hone
        have hnextEnvelope : StoreEnvelope indexBound valueBound next := by
          apply hinitial.execBasic (.sub test test one)
          · simpa using htestIndex
          · simp [Internal.Basic.writeValue, htest, hone]
            have hvalue := hinitial.value_le test
            omega
        have hclear : cleared next test = cleared initial test := by
          exact cleared_sub_eq initial test one
        have hrecursiveBranch :
            MeasuredRuns
              ((fun index : Fin count => branch index.succ)
                ⟨predecessor, hpredecessor⟩)
              (cleared next test) final branchSteps branchCost
              (envelopeSpace indexBound valueBound) := by
          rw [hclear]
          simpa using hbranch
        have hrecursive := ih (branch := fun index => branch index.succ)
          (initial := next) hpredecessor hnextTest hnextOne
          hnextEnvelope hrecursiveBranch
        have hdecrement := MeasuredRuns.basicEnvelope
          (.sub test test one) initial hinitial hnextEnvelope
        have hnonzero : initial test ≠ 0 := by omega
        have hrun := MeasuredRuns.ifNonzeroEnvelope
          (onZero := branch ⟨0, by omega⟩) hnonzero hinitial
          (hdecrement.seq hrecursive)
        convert! hrun using 1 <;> simp [stepCount, costBound]
        all_goals ring

end Switch

end Structured

end RAM

end Complexity
