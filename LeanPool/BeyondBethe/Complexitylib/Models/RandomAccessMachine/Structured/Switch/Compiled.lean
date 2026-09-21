/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured

/-!
# Compilation theorem for finite numeric structured-RAM switches
-/


public section

namespace Complexity

namespace RAM

namespace Structured

namespace Switch


open Internal

/-- End-to-end compilation of a measured finite switch. -/
theorem select_compiled {count test one indexBound valueBound : ℕ}
    (branch : Fin count → Cmd) (initial final : Store)
    {code branchSteps branchCost : ℕ}
    (hcode : code < count) (htest : initial test = code)
    (hone : initial one = 1) (hne : test ≠ one)
    (htestIndex : test < indexBound)
    (hinitial : StoreEnvelope indexBound valueBound initial)
    (hbranch : MeasuredRuns (branch ⟨code, hcode⟩) (cleared initial test)
      final branchSteps branchCost (envelopeSpace indexBound valueBound)) :
    ∃ cost space,
      Exec (select count test one branch) initial final
        (stepCount code branchSteps) cost space ∧
      run (select count test one branch).compile (stepCount code branchSteps)
          { pc := 0, regs := initial } =
        { pc := (select count test one branch).codeSize, regs := final } ∧
      Halted (select count test one branch).compile
        (run (select count test one branch).compile (stepCount code branchSteps)
          { pc := 0, regs := initial }) ∧
      logTimeUpto (select count test one branch).compile
          (stepCount code branchSteps) { pc := 0, regs := initial } ≤
        costBound code branchCost (valueWidth valueBound) ∧
      spaceUpto (select count test one branch).compile
          (stepCount code branchSteps) { pc := 0, regs := initial } ≤
        envelopeSpace indexBound valueBound := by
  obtain ⟨cost, space, hexec, hcost, hspace⟩ :=
    select_measured branch initial final hcode htest hone hne htestIndex
      hinitial hbranch
  have hcompiled := Exec.compile_correct hexec
  refine ⟨cost, space, hexec, hcompiled.1, Exec.compile_halted hexec, ?_, ?_⟩
  · rw [hcompiled.2.1]
    exact hcost
  · rw [hcompiled.2.2]
    exact hspace

end Switch

end Structured

end RAM

end Complexity
