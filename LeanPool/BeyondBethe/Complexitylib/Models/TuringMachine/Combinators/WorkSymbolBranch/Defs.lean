/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkBranch.Defs

/-!
# Direct work-symbol branch combinator — definitions

`TM.branchWorkSymbolTM idx symbol onEqual onDifferent` inspects one work tape
and runs `onEqual` exactly when the current symbol equals `symbol`. This is the
generic controller branch used by the sparse RAM lookup scan.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Inspect one work symbol and run the selected branch on the same tapes. -/
def branchWorkSymbolTM {n : ℕ} (idx : Fin n) (symbol : Γ)
    (onEqual onDifferent : TM n) : TM n where
  Q := WorkBranchQ onEqual.Q onDifferent.Q
  qstart := .inl .dispatch
  qhalt := .inl .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .inl .dispatch =>
        if wHeads idx = symbol then
          allReadBack
            (workBranchBlankState onEqual onDifferent onEqual.qstart)
            iHead wHeads oHead
        else
          allReadBack
            (workBranchNonblankState onEqual onDifferent onDifferent.qstart)
            iHead wHeads oHead
    | .inl .done => allIdle (.inl .done) iHead wHeads oHead
    | .inr (.inl q) =>
        if q = onEqual.qhalt then
          allReadBack (.inl .done) iHead wHeads oHead
        else
          let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
            onEqual.δ q iHead wHeads oHead
          (workBranchBlankState onEqual onDifferent q', workWrites,
            outputWrite, inputDir, workDirs, outputDir)
    | .inr (.inr q) =>
        if q = onDifferent.qhalt then
          allReadBack (.inl .done) iHead wHeads oHead
        else
          let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
            onDifferent.δ q iHead wHeads oHead
          (workBranchNonblankState onEqual onDifferent q', workWrites,
            outputWrite, inputDir, workDirs, outputDir)
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .inl .dispatch =>
        dsimp only
        split <;> exact rightOfStart_allReadBack iHead wHeads oHead
    | .inl .done => exact rightOfStart_allIdle iHead wHeads oHead
    | .inr (.inl q) =>
        dsimp only
        split
        · exact rightOfStart_allReadBack iHead wHeads oHead
        · exact onEqual.δ_right_of_start q iHead wHeads oHead
    | .inr (.inr q) =>
        dsimp only
        split
        · exact rightOfStart_allReadBack iHead wHeads oHead
        · exact onDifferent.δ_right_of_start q iHead wHeads oHead

/-- One dispatch step followed by either branch's advertised time. -/
def branchWorkSymbolTime (equalTime differentTime : ℕ) : ℕ :=
  1 + max equalTime differentTime

end TM

end Complexity
