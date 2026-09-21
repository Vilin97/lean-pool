/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.KuhnMatching
import Mathlib.Tactic

/-!
# A small-step evaluator for the Kuhn matching algorithm

The recursive search in `KuhnMatching` is convenient for its mathematical
correctness proof.  A Turing-machine implementation needs an explicit call
stack.  This file gives that stack machine, proves that it returns exactly the
same result as `kuhnSearch`, and charges every transition to the already proved
coordinate-inspection counter.

There is no encoding or complexity-class claim in this file.  Its purpose is
to isolate the semantic compiler-correctness argument from the subsequent
finite-word implementation.
-/

namespace BeyondBethe

/-- The information needed after a recursive alternating-path search returns.
On success the saved edge is installed.  On failure the parent row resumes at
its saved column suffix with its original mate table. -/
structure KuhnSearchFrame (n : ℕ) where
  fuel : ℕ
  remaining : List (Fin n)
  row : Fin n
  mate : ColumnMate n
  column : Fin n

/-- The outer frame remembers the rows not yet inserted and the mate table to
retain if the current root search fails. -/
structure KuhnBuildFrame (n : ℕ) where
  rows : List (Fin n)
  fallback : ColumnMate n

inductive KuhnFrame (n : ℕ)
  | search : KuhnSearchFrame n → KuhnFrame n
  | build : KuhnBuildFrame n → KuhnFrame n

/-- A call state, a returned search result, or the final mate table. -/
inductive KuhnEvalState (n : ℕ)
  | call (fuel : ℕ) (remaining : List (Fin n)) (row : Fin n)
      (seen : Finset (Fin n)) (mate : ColumnMate n)
      (stack : List (KuhnFrame n))
  | ret (result : KuhnSearchResult n) (stack : List (KuhnFrame n))
  | done (mate : ColumnMate n)

/-- One transition of the explicit-stack evaluator. -/
def kuhnEvalStep {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    KuhnEvalState n → KuhnEvalState n
  | .done mate => .done mate
  | .call 0 _remaining _row seen _mate stack =>
      .ret ⟨none, seen⟩ stack
  | .call (_fuel + 1) [] _row seen _mate stack =>
      .ret ⟨none, seen⟩ stack
  | .call (fuel + 1) (col :: remaining) row seen mate stack =>
      if col ∈ seen ∨ A row col = 0 then
        .call (fuel + 1) remaining row seen mate stack
      else
        let seen' := insert col seen
        match mate col with
        | none =>
            .ret ⟨some (Function.update mate col (some row)), seen'⟩ stack
        | some oldRow =>
            let frame : KuhnSearchFrame n :=
              ⟨fuel + 1, remaining, row, mate, col⟩
            .call fuel (List.finRange n) oldRow seen'
              (Function.update mate col none) (.search frame :: stack)
  | .ret result [] => .ret result []
  | .ret result (.search frame :: stack) =>
      match result.mate? with
      | some mate' =>
          .ret
            ⟨some (Function.update mate' frame.column (some frame.row)),
              result.seen⟩ stack
      | none =>
          .call frame.fuel frame.remaining frame.row result.seen
            frame.mate stack
  | .ret result (.build frame :: stack) =>
      let mate := result.mate?.getD frame.fallback
      match frame.rows with
      | [] => .done mate
      | row :: rows =>
          .call (n + 1) (List.finRange n) row ∅ mate
            (.build ⟨rows, mate⟩ :: stack)

/-- Exact number of small steps used to evaluate one recursive search call and
return its result without consuming the pre-existing continuation stack. -/
def kuhnSearchSteps {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    (fuel : ℕ) → List (Fin n) → Fin n → Finset (Fin n) →
      ColumnMate n → ℕ
  | 0, _remaining, _row, _seen, _mate => 1
  | _fuel + 1, [], _row, _seen, _mate => 1
  | fuel + 1, col :: remaining, row, seen, mate =>
      if col ∈ seen ∨ A row col = 0 then
        1 + kuhnSearchSteps A (fuel + 1) remaining row seen mate
      else
        let seen' := insert col seen
        match mate col with
        | none => 1
        | some oldRow =>
            let mateWithoutOld := Function.update mate col none
            let recursive :=
              kuhnSearch A fuel (List.finRange n) oldRow seen' mateWithoutOld
            let recursiveSteps :=
              kuhnSearchSteps A fuel (List.finRange n) oldRow seen'
                mateWithoutOld
            match recursive.mate? with
            | some _ => 2 + recursiveSteps
            | none => 2 + recursiveSteps +
                kuhnSearchSteps A (fuel + 1) remaining row recursive.seen mate
termination_by fuel remaining _row _seen _mate => (fuel, remaining.length)

/-- The stack evaluator is a semantics-preserving compilation of one
`kuhnSearch` call. -/
theorem kuhnEvalStep_iterate_call {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ)
    (remaining : List (Fin n)) (row : Fin n)
    (seen : Finset (Fin n)) (mate : ColumnMate n)
    (stack : List (KuhnFrame n)) :
    (kuhnEvalStep A)^[kuhnSearchSteps A fuel remaining row seen mate]
        (.call fuel remaining row seen mate stack) =
      .ret (kuhnSearch A fuel remaining row seen mate) stack := by
  fun_induction kuhnSearch generalizing stack with
  | case1 =>
      simp [kuhnSearchSteps, Function.iterate_one, kuhnEvalStep.eq_def,
        kuhnSearch]
  | case2 =>
      simp [kuhnSearchSteps, Function.iterate_one, kuhnEvalStep.eq_def,
        kuhnSearch]
  | case3 fuel col remaining row seen mate hskip ih =>
      rw [kuhnSearchSteps]
      simp only [hskip, ↓reduceIte]
      rw [show 1 + kuhnSearchSteps A (fuel + 1) remaining row seen mate =
          kuhnSearchSteps A (fuel + 1) remaining row seen mate + 1 by omega,
        Function.iterate_succ_apply, kuhnEvalStep.eq_def]
      simp only [hskip, ↓reduceIte]
      simpa [kuhnSearch, hskip] using ih stack
  | case4 fuel col remaining row seen mate hskip seen' hmate =>
      rw [kuhnSearchSteps]
      simp only [hskip, ↓reduceIte, hmate]
      simp [Function.iterate_one, kuhnEvalStep.eq_def, hskip, hmate, seen']
  | case5 fuel col remaining row seen mate hskip seen' oldRow hmate
      mateWithoutOld recursive mateRec hrec ih =>
      rw [kuhnSearchSteps]
      simp only [hskip, ↓reduceIte, hmate]
      rw [show recursive.mate? = some mateRec by exact hrec]
      simp only
      let frame : KuhnSearchFrame n :=
        ⟨fuel + 1, remaining, row, mate, col⟩
      let steps := kuhnSearchSteps A fuel (List.finRange n) oldRow seen'
        mateWithoutOld
      change (kuhnEvalStep A)^[2 + steps]
          (.call (fuel + 1) (col :: remaining) row seen mate stack) =
        .ret ⟨some (Function.update mateRec col (some row)), recursive.seen⟩
          stack
      calc
        (kuhnEvalStep A)^[2 + steps]
            (.call (fuel + 1) (col :: remaining) row seen mate stack) =
            kuhnEvalStep A
              ((kuhnEvalStep A)^[steps]
                (kuhnEvalStep A
                  (.call (fuel + 1) (col :: remaining) row seen mate stack))) := by
              rw [show 2 + steps = 1 + steps + 1 by omega,
                Function.iterate_add_apply, Function.iterate_add_apply,
                Function.iterate_one]
        _ = kuhnEvalStep A
              ((kuhnEvalStep A)^[steps]
                (.call fuel (List.finRange n) oldRow seen' mateWithoutOld
                  (.search frame :: stack))) := by
              simp [kuhnEvalStep.eq_def, hskip, hmate, seen',
                mateWithoutOld, frame]
        _ = kuhnEvalStep A (.ret recursive (.search frame :: stack)) := by
              rw [show (kuhnEvalStep A)^[steps]
                    (.call fuel (List.finRange n) oldRow seen' mateWithoutOld
                      (.search frame :: stack)) =
                  .ret recursive (.search frame :: stack) by
                simpa [steps, recursive] using
                  ih (.search frame :: stack)]
        _ = .ret
              ⟨some (Function.update mateRec col (some row)), recursive.seen⟩
              stack := by
              simp [kuhnEvalStep.eq_def, frame, hrec]
  | case6 fuel col remaining row seen mate hskip seen' oldRow hmate
      mateWithoutOld recursive hrec ihRec ihRec' ihContinue =>
      rw [kuhnSearchSteps]
      simp only [hskip, ↓reduceIte, hmate]
      rw [show recursive.mate? = none by exact hrec]
      simp only
      let frame : KuhnSearchFrame n :=
        ⟨fuel + 1, remaining, row, mate, col⟩
      let recursiveSteps := kuhnSearchSteps A fuel (List.finRange n) oldRow
        seen' mateWithoutOld
      let continueSteps := kuhnSearchSteps A (fuel + 1) remaining row
        recursive.seen mate
      change (kuhnEvalStep A)^[2 + recursiveSteps + continueSteps]
          (.call (fuel + 1) (col :: remaining) row seen mate stack) =
        .ret (kuhnSearch A (fuel + 1) remaining row recursive.seen mate) stack
      calc
        (kuhnEvalStep A)^[2 + recursiveSteps + continueSteps]
            (.call (fuel + 1) (col :: remaining) row seen mate stack) =
            (kuhnEvalStep A)^[continueSteps]
              (kuhnEvalStep A
                ((kuhnEvalStep A)^[recursiveSteps]
                  (kuhnEvalStep A
                    (.call (fuel + 1) (col :: remaining) row seen mate
                      stack)))) := by
              rw [show 2 + recursiveSteps + continueSteps =
                  continueSteps + 1 + recursiveSteps + 1 by omega,
                Function.iterate_add_apply, Function.iterate_add_apply,
                Function.iterate_add_apply, Function.iterate_one]
        _ = (kuhnEvalStep A)^[continueSteps]
              (kuhnEvalStep A
                ((kuhnEvalStep A)^[recursiveSteps]
                  (.call fuel (List.finRange n) oldRow seen' mateWithoutOld
                    (.search frame :: stack)))) := by
              simp [kuhnEvalStep.eq_def, hskip, hmate, seen',
                mateWithoutOld, frame]
        _ = (kuhnEvalStep A)^[continueSteps]
              (kuhnEvalStep A (.ret recursive (.search frame :: stack))) := by
              rw [show (kuhnEvalStep A)^[recursiveSteps]
                    (.call fuel (List.finRange n) oldRow seen' mateWithoutOld
                      (.search frame :: stack)) =
                  .ret recursive (.search frame :: stack) by
                simpa [recursiveSteps, recursive] using
                  ihRec' (.search frame :: stack)]
        _ = (kuhnEvalStep A)^[continueSteps]
              (.call (fuel + 1) remaining row recursive.seen mate stack) := by
              simp [kuhnEvalStep.eq_def, frame, hrec]
        _ = .ret (kuhnSearch A (fuel + 1) remaining row recursive.seen mate)
              stack := by
              simpa [continueSteps] using ihContinue stack

/-- Each evaluator transition is charged to at most three coordinate
inspections, with one terminal transition left over. -/
theorem kuhnSearchSteps_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ)
    (remaining : List (Fin n)) (row : Fin n)
    (seen : Finset (Fin n)) (mate : ColumnMate n) :
    kuhnSearchSteps A fuel remaining row seen mate ≤
      3 * kuhnSearchWork A fuel remaining row seen mate + 1 := by
  fun_induction kuhnSearchSteps with
  | case1 => simp [kuhnSearchWork]
  | case2 => simp [kuhnSearchWork]
  | case3 fuel col remaining row seen mate hskip ih =>
      simp only [kuhnSearchWork, hskip, ↓reduceIte]
      omega
  | case4 fuel col remaining row seen mate hskip hmate =>
      simp [kuhnSearchWork, hskip, hmate]
  | case5 fuel col remaining row seen mate hskip seen' oldRow hmate
      mateWithoutOld recursive recursiveSteps mateRec hrec ih =>
      simp only [kuhnSearchWork, hskip, ↓reduceIte, hmate]
      rw [show recursive.mate? = some mateRec by exact hrec]
      change 2 + recursiveSteps ≤
        3 * (1 + kuhnSearchWork A fuel (List.finRange n) oldRow seen'
          mateWithoutOld) + 1
      omega
  | case6 fuel col remaining row seen mate hskip seen' oldRow hmate
      mateWithoutOld recursive recursiveSteps hrec ihRec ihContinue =>
      simp only [kuhnSearchWork, hskip, ↓reduceIte, hmate]
      rw [show recursive.mate? = none by exact hrec]
      change 2 + recursiveSteps +
          kuhnSearchSteps A (fuel + 1) remaining row recursive.seen mate ≤
        3 * (1 + kuhnSearchWork A fuel (List.finRange n) oldRow seen'
          mateWithoutOld +
          kuhnSearchWork A (fuel + 1) remaining row recursive.seen mate) + 1
      omega

/-- Start (or finish) the explicit evaluator on a remaining row list. -/
def kuhnBuildEvalState {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (rows : List (Fin n)) (mate : ColumnMate n) : KuhnEvalState n :=
  match rows with
  | [] => .done mate
  | row :: rows =>
      .call (n + 1) (List.finRange n) row ∅ mate
        [.build ⟨rows, mate⟩]

/-- Exact number of transitions used by the explicit evaluator for the row
building phase. -/
def kuhnBuildSteps {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    List (Fin n) → ColumnMate n → ℕ
  | [], _mate => 0
  | row :: rows, mate =>
      let result := kuhnAugment A (n + 1) row ∅ mate
      kuhnSearchSteps A (n + 1) (List.finRange n) row ∅ mate + 1 +
        kuhnBuildSteps A rows (result.mate?.getD mate)

@[simp] theorem kuhnEvalStep_return_build {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (rows : List (Fin n))
    (fallback : ColumnMate n) (result : KuhnSearchResult n) :
    kuhnEvalStep A
        (.ret result [.build ⟨rows, fallback⟩]) =
      kuhnBuildEvalState A rows (result.mate?.getD fallback) := by
  cases rows <;> rfl

/-- The complete small-step evaluator returns exactly `kuhnBuild`. -/
theorem kuhnBuildEvalState_iterate {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (rows : List (Fin n))
    (mate : ColumnMate n) :
    (kuhnEvalStep A)^[kuhnBuildSteps A rows mate]
        (kuhnBuildEvalState A rows mate) =
      .done (kuhnBuild A rows mate) := by
  induction rows generalizing mate with
  | nil => simp [kuhnBuildSteps, kuhnBuildEvalState, kuhnBuild]
  | cons row rows ih =>
      let result := kuhnAugment A (n + 1) row ∅ mate
      let oneSteps :=
        kuhnSearchSteps A (n + 1) (List.finRange n) row ∅ mate
      let nextMate := result.mate?.getD mate
      rw [kuhnBuildSteps]
      change (kuhnEvalStep A)^[oneSteps + 1 + kuhnBuildSteps A rows nextMate]
          (KuhnEvalState.call (n + 1) (List.finRange n) row ∅ mate
            [.build ⟨rows, mate⟩]) = _
      rw [show oneSteps + 1 + kuhnBuildSteps A rows nextMate =
          kuhnBuildSteps A rows nextMate + 1 + oneSteps by omega,
        Function.iterate_add_apply, Function.iterate_add_apply,
        Function.iterate_one]
      rw [kuhnEvalStep_iterate_call]
      change (kuhnEvalStep A)^[kuhnBuildSteps A rows nextMate]
          (kuhnEvalStep A (.ret result [.build ⟨rows, mate⟩])) = _
      rw [kuhnEvalStep_return_build, ih]
      simp [kuhnBuild, result, nextMate]

/-- The whole build uses a cubic number of explicit-stack transitions. -/
theorem kuhnBuildSteps_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (rows : List (Fin n))
    (mate : ColumnMate n) :
    kuhnBuildSteps A rows mate ≤
      3 * kuhnBuildWork A rows mate + 2 * rows.length := by
  induction rows generalizing mate with
  | nil => simp [kuhnBuildSteps, kuhnBuildWork]
  | cons row rows ih =>
      let result := kuhnAugment A (n + 1) row ∅ mate
      have hone := kuhnSearchSteps_le A (n + 1) (List.finRange n)
        row ∅ mate
      have htail := ih (result.mate?.getD mate)
      change kuhnSearchSteps A (n + 1) (List.finRange n) row ∅ mate + 1 +
          kuhnBuildSteps A rows (result.mate?.getD mate) ≤
        3 * (kuhnSearchWork A (n + 1) (List.finRange n) row ∅ mate +
          kuhnBuildWork A rows (result.mate?.getD mate)) +
          2 * (rows.length + 1)
      omega

/-- Starting from the empty mate table and all rows, the evaluator returns the
same column mate used by the proved support-matching decision. -/
theorem kuhnFullBuildEvalState_iterate {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (kuhnEvalStep A)^[kuhnBuildSteps A (List.finRange n)
        (emptyColumnMate n)]
      (kuhnBuildEvalState A (List.finRange n) (emptyColumnMate n)) =
        .done (kuhnColumnMate A) := by
  simpa [kuhnColumnMate] using
    kuhnBuildEvalState_iterate A (List.finRange n) (emptyColumnMate n)

theorem kuhnFullBuildSteps_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    kuhnBuildSteps A (List.finRange n) (emptyColumnMate n) ≤
      3 * (n * (n + (n + 1) * n)) + 2 * n := by
  calc
    kuhnBuildSteps A (List.finRange n) (emptyColumnMate n) ≤
        3 * kuhnBuildWork A (List.finRange n) (emptyColumnMate n) +
          2 * (List.finRange n).length :=
      kuhnBuildSteps_le A _ _
    _ ≤ 3 * (n * (n + (n + 1) * n)) + 2 * n := by
      simp only [List.length_finRange]
      have hwork := kuhnBuildWork_le A (List.finRange n)
        (emptyColumnMate n)
      simp only [List.length_finRange] at hwork
      omega

end BeyondBethe
