/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators

/-!
# Direct work-symbol branch combinator -- definitions

`TM.branchWorkBlankTM idx onBlank onNonblank` inspects work tape `idx` once.
A blank selects `onBlank`; every other symbol selects `onNonblank`. The
dispatcher uses the ordinary read-back action on every tape and never uses the
output tape as control storage.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Finite driver states for direct work-symbol branching. -/
inductive WorkBranchPhase where
  | dispatch
  | done
  deriving DecidableEq

/-- `WorkBranchPhase` has exactly two states. -/
instance instFintypeWorkBranchPhase : Fintype WorkBranchPhase where
  elems := {.dispatch, .done}
  complete := fun phase => by cases phase <;> simp

/-- State space of a direct work-symbol branch. -/
abbrev WorkBranchQ (QBlank QNonblank : Type) :=
  WorkBranchPhase ⊕ (QBlank ⊕ QNonblank)

/-- Embed a blank-branch state, collapsing its halt state to the shared halt. -/
def workBranchBlankState {n : ℕ} (onBlank onNonblank : TM n)
    (q : onBlank.Q) : WorkBranchQ onBlank.Q onNonblank.Q :=
  if q = onBlank.qhalt then .inl .done else .inr (.inl q)

/-- Embed a nonblank-branch state, collapsing its halt state to the shared halt. -/
def workBranchNonblankState {n : ℕ} (onBlank onNonblank : TM n)
    (q : onNonblank.Q) : WorkBranchQ onBlank.Q onNonblank.Q :=
  if q = onNonblank.qhalt then .inl .done else .inr (.inr q)

/-- Uniform time bound for a one-step dispatch followed by either branch. -/
def branchWorkBlankTime (blankTime nonblankTime : ℕ) : ℕ :=
  1 + max blankTime nonblankTime

/-- Inspect one work symbol and run the selected branch on the same tapes.

The dispatcher selects `onBlank` exactly when `wHeads idx = Γ.blank` and
otherwise selects `onNonblank`. Branch halt states are collapsed into the
shared halt state on the same simulated transition, so there is no trailing
seam step and no extra tape action after a branch halts. -/
def branchWorkBlankTM {n : ℕ} (idx : Fin n)
    (onBlank onNonblank : TM n) : TM n where
  Q := WorkBranchQ onBlank.Q onNonblank.Q
  qstart := .inl .dispatch
  qhalt := .inl .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .inl .dispatch =>
        if wHeads idx = Γ.blank then
          allReadBack
            (workBranchBlankState onBlank onNonblank onBlank.qstart)
            iHead wHeads oHead
        else
          allReadBack
            (workBranchNonblankState onBlank onNonblank onNonblank.qstart)
            iHead wHeads oHead
    | .inl .done => allIdle (.inl .done) iHead wHeads oHead
    | .inr (.inl q) =>
        if q = onBlank.qhalt then
          allIdle (.inl .done) iHead wHeads oHead
        else
          let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
            onBlank.δ q iHead wHeads oHead
          (workBranchBlankState onBlank onNonblank q', workWrites,
            outputWrite, inputDir, workDirs, outputDir)
    | .inr (.inr q) =>
        if q = onNonblank.qhalt then
          allIdle (.inl .done) iHead wHeads oHead
        else
          let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
            onNonblank.δ q iHead wHeads oHead
          (workBranchNonblankState onBlank onNonblank q', workWrites,
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
        · exact rightOfStart_allIdle iHead wHeads oHead
        · exact onBlank.δ_right_of_start q iHead wHeads oHead
    | .inr (.inr q) =>
        dsimp only
        split
        · exact rightOfStart_allIdle iHead wHeads oHead
        · exact onNonblank.δ_right_of_start q iHead wHeads oHead

end TM

end Complexity
