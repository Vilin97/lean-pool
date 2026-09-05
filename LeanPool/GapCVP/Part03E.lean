/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part03D

/-! # GapCVP proof, part 03, continuation 05 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFEncodedClauseSort

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder

open GapCVP.CNFSortingDedup

/-- GapCVP reduction support. -/
structure DelimitedPairComparisonState where
  /-- GapCVP reduction support. -/
  first : Option Bool
  /-- GapCVP reduction support. -/
  second : Option Bool
  /-- GapCVP reduction support. -/
  outcome : EncodedWordOrdering
  deriving Fintype

/-- GapCVP reduction support. -/
def delimitedComparePeekFirst (stack : Fin 10)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState) :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  .peek stack (fun state bit => { state with first := bit })
    (.branch (fun state => state.first.isSome) present absent)

/-- GapCVP reduction support. -/
def delimitedComparePeekSecond (stack : Fin 10)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState) :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  .peek stack (fun state bit => { state with second := bit })
    (.branch (fun state => state.second.isSome) present absent)

/-- GapCVP reduction support. -/
def delimitedComparePop (stack : Fin 10)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState) :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  .pop stack (fun state _ => state) continuation

/-- GapCVP reduction support. -/
def delimitedComparePushFirst (stack : Fin 10)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState) :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  .push stack (fun state => state.first.getD false) continuation

/-- GapCVP reduction support. -/
def delimitedComparePushConstant (stack : Fin 10) (bit : Bool)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState) :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  .push stack (fun _ => bit) continuation

/-- GapCVP reduction support. -/
def delimitedCompareGoto (phase : Fin 12) :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  .load (fun state => ⟨none, none, state.outcome⟩)
    (.goto (fun _ => phase))

/-- GapCVP reduction support. -/
def delimitedCompareSetOutcome
    (outcome : EncodedWordOrdering) (phase : Fin 12) :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  .load (fun _ => ⟨none, none, outcome⟩)
    (.goto (fun _ => phase))

/-- GapCVP reduction support. -/
def delimitedCompareFirstPrefixStatement :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  delimitedComparePeekFirst 0
    (delimitedComparePop 0
      (delimitedComparePushFirst 7
        (delimitedComparePushConstant 8 true
          (.branch (fun state => state.first.getD false)
            (delimitedComparePushConstant 1 true
              (delimitedCompareGoto 0))
            (delimitedCompareGoto 1)))))
    (delimitedCompareSetOutcome .invalid 7)

/-- GapCVP reduction support. -/
def delimitedCompareFirstPayloadStatement :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  delimitedComparePeekFirst 1
    (delimitedComparePop 1
      (delimitedComparePeekFirst 0
        (delimitedComparePop 0
          (delimitedComparePushFirst 2
            (delimitedComparePushFirst 7
              (delimitedComparePushConstant 8 true
                (delimitedCompareGoto 1)))))
        (delimitedCompareSetOutcome .invalid 7)))
    (delimitedCompareGoto 2)

/-- GapCVP reduction support. -/
def delimitedCompareSecondPrefixStatement :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  delimitedComparePeekFirst 0
    (delimitedComparePop 0
      (delimitedComparePushFirst 7
        (delimitedComparePushConstant 8 true
          (.branch (fun state => state.first.getD false)
            (delimitedComparePushConstant 3 true
              (delimitedCompareGoto 2))
            (delimitedCompareGoto 3)))))
    (delimitedCompareSetOutcome .invalid 7)

/-- GapCVP reduction support. -/
def delimitedCompareSecondPayloadStatement :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  delimitedComparePeekFirst 3
    (delimitedComparePop 3
      (delimitedComparePeekFirst 0
        (delimitedComparePop 0
          (delimitedComparePushFirst 4
            (delimitedComparePushFirst 7
              (delimitedComparePushConstant 8 true
                (delimitedCompareGoto 3)))))
        (delimitedCompareSetOutcome .invalid 7)))
    (delimitedCompareGoto 4)

/-- GapCVP reduction support. -/
def delimitedCompareReverseFirstStatement :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  delimitedComparePeekFirst 2
    (delimitedComparePop 2
      (delimitedComparePushFirst 5 (delimitedCompareGoto 4)))
    (delimitedCompareGoto 5)

/-- GapCVP reduction support. -/
def delimitedCompareReverseSecondStatement :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  delimitedComparePeekFirst 4
    (delimitedComparePop 4
      (delimitedComparePushFirst 6 (delimitedCompareGoto 5)))
    (delimitedCompareGoto 6)

/-- GapCVP reduction support. -/
def delimitedCompareWordsStatement :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  delimitedComparePeekFirst 5
    (delimitedComparePeekSecond 6
      (.branch (fun state => state.first = state.second)
        (delimitedComparePop 5
          (delimitedComparePop 6 (delimitedCompareGoto 6)))
        (.branch (fun state => state.first = some false)
          (delimitedCompareSetOutcome .less 7)
          (delimitedCompareSetOutcome .greater 7)))
      (delimitedCompareSetOutcome .greater 7))
    (delimitedComparePeekSecond 6
      (delimitedCompareSetOutcome .less 7)
      (delimitedCompareSetOutcome .equal 7))

/-- GapCVP reduction support. -/
def delimitedCompareCleanupStatement :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  delimitedComparePeekFirst 1
    (delimitedComparePop 1 (delimitedCompareGoto 7))
    (delimitedComparePeekFirst 2
      (delimitedComparePop 2 (delimitedCompareGoto 7))
      (delimitedComparePeekFirst 3
        (delimitedComparePop 3 (delimitedCompareGoto 7))
        (delimitedComparePeekFirst 4
          (delimitedComparePop 4 (delimitedCompareGoto 7))
          (delimitedComparePeekFirst 5
            (delimitedComparePop 5 (delimitedCompareGoto 7))
            (delimitedComparePeekFirst 6
              (delimitedComparePop 6 (delimitedCompareGoto 7))
              (delimitedCompareGoto 8))))))

/-- GapCVP reduction support. -/
def delimitedCompareTrailingStatement :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  delimitedComparePeekFirst 0
    (delimitedComparePop 0
      (delimitedComparePushFirst 7
        (delimitedComparePushConstant 8 true
          (delimitedCompareGoto 8))))
    (delimitedCompareGoto 9)

/-- GapCVP reduction support. -/
def delimitedCompareOutcomeStatement :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  .push 9 (fun state => encodedWordOrderingSecond state.outcome)
    (.push 9 (fun state => encodedWordOrderingFirst state.outcome)
      (delimitedCompareGoto 10))

/-- GapCVP reduction support. -/
def delimitedCompareSourceStatement :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  delimitedComparePeekFirst 7
    (delimitedComparePop 7
      (delimitedComparePushFirst 9 (delimitedCompareGoto 10)))
    (delimitedComparePushConstant 9 false
      (delimitedCompareGoto 11))

/-- GapCVP reduction support. -/
def delimitedComparePrefixStatement :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  delimitedComparePeekFirst 8
    (delimitedComparePop 8
      (delimitedComparePushConstant 9 true
        (delimitedCompareGoto 11)))
    (.load (fun _ => ⟨none, none, .invalid⟩) .halt)

/-- GapCVP reduction support. -/
abbrev delimitedPairComparisonMachine : Turing.FinTM2 where
  K := Fin 10
  k₀ := 0
  k₁ := 9
  Γ _ := Bool
  Λ := Fin 12
  main := 0
  σ := DelimitedPairComparisonState
  initialState := ⟨none, none, .invalid⟩
  m phase :=
    if phase = (0 : Fin 12) then
      delimitedCompareFirstPrefixStatement
    else if phase = (1 : Fin 12) then
      delimitedCompareFirstPayloadStatement
    else if phase = (2 : Fin 12) then
      delimitedCompareSecondPrefixStatement
    else if phase = (3 : Fin 12) then
      delimitedCompareSecondPayloadStatement
    else if phase = (4 : Fin 12) then
      delimitedCompareReverseFirstStatement
    else if phase = (5 : Fin 12) then
      delimitedCompareReverseSecondStatement
    else if phase = (6 : Fin 12) then
      delimitedCompareWordsStatement
    else if phase = (7 : Fin 12) then
      delimitedCompareCleanupStatement
    else if phase = (8 : Fin 12) then
      delimitedCompareTrailingStatement
    else if phase = (9 : Fin 12) then
      delimitedCompareOutcomeStatement
    else if phase = (10 : Fin 12) then
      delimitedCompareSourceStatement
    else
      delimitedComparePrefixStatement

/-- GapCVP reduction support. -/
def delimitedCompareConfiguration (phase : Fin 12)
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.Cfg where
  l := some phase
  var := ⟨none, none, outcome⟩
  stk := ![input, firstCounter, firstReversed,
    secondCounter, secondReversed, firstForward, secondForward,
    source, sourcePrefix, output]

theorem delimitedPairComparisonMachine_init (input : List Bool) :
    Turing.initList delimitedPairComparisonMachine input =
      delimitedCompareConfiguration 0 .invalid
        input [] [] [] [] [] [] [] [] [] := by
  simp only [delimitedPairComparisonMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq,
      dite_eq_ite,
      delimitedCompareConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `delimitedCompareStepTac` machine-step simplifier. -/
macro "delimitedCompareStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [delimitedPairComparisonMachine,
          delimitedCompareConfiguration,
          delimitedComparePeekFirst, delimitedComparePeekSecond,
          delimitedComparePop, delimitedComparePushFirst,
          delimitedComparePushConstant, delimitedCompareGoto,
          delimitedCompareSetOutcome,
          delimitedCompareFirstPrefixStatement,
          delimitedCompareFirstPayloadStatement,
          delimitedCompareSecondPrefixStatement,
          delimitedCompareSecondPayloadStatement,
          delimitedCompareReverseFirstStatement,
          delimitedCompareReverseSecondStatement,
          delimitedCompareWordsStatement,
          delimitedCompareCleanupStatement,
          delimitedCompareTrailingStatement,
          delimitedCompareOutcomeStatement,
          delimitedCompareSourceStatement,
          delimitedComparePrefixStatement,
          encodedWordOrderingWord,
          encodedWordOrderingFirst, encodedWordOrderingSecond,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

theorem delimitedCompare_firstPrefix_true
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 0 outcome
        (true :: input) firstCounter firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 0 outcome
        input (true :: firstCounter) firstReversed
        secondCounter secondReversed firstForward secondForward
        (true :: source) (true :: sourcePrefix) output) := by
  delimitedCompareStepTac

theorem delimitedCompare_firstPrefix_delimiter
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 0 outcome
        (false :: input) firstCounter firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 1 outcome
        input firstCounter firstReversed
        secondCounter secondReversed firstForward secondForward
        (false :: source) (true :: sourcePrefix) output) := by
  delimitedCompareStepTac

theorem delimitedCompare_firstPrefix_missing
    (outcome : EncodedWordOrdering)
    (firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 0 outcome
        [] firstCounter firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 7 .invalid
        [] firstCounter firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) := by
  delimitedCompareStepTac

theorem delimitedCompare_firstPayload_step
    (outcome : EncodedWordOrdering) (bit marker : Bool)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 1 outcome
        (bit :: input) (marker :: firstCounter) firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 1 outcome
        input firstCounter (bit :: firstReversed)
        secondCounter secondReversed firstForward secondForward
        (bit :: source) (true :: sourcePrefix) output) := by
  cases bit <;> cases marker <;> delimitedCompareStepTac

theorem delimitedCompare_firstPayload_finish
    (outcome : EncodedWordOrdering)
    (input firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 1 outcome
        input [] firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 2 outcome
        input [] firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) := by
  delimitedCompareStepTac

theorem delimitedCompare_firstPayload_missing
    (outcome : EncodedWordOrdering) (marker : Bool)
    (firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 1 outcome
        [] (marker :: firstCounter) firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 7 .invalid
        [] firstCounter firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) := by
  cases marker <;> delimitedCompareStepTac

theorem delimitedCompare_secondPrefix_true
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 2 outcome
        (true :: input) firstCounter firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 2 outcome
        input firstCounter firstReversed
        (true :: secondCounter) secondReversed
        firstForward secondForward
        (true :: source) (true :: sourcePrefix) output) := by
  delimitedCompareStepTac

theorem delimitedCompare_secondPrefix_delimiter
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 2 outcome
        (false :: input) firstCounter firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 3 outcome
        input firstCounter firstReversed
        secondCounter secondReversed firstForward secondForward
        (false :: source) (true :: sourcePrefix) output) := by
  delimitedCompareStepTac

theorem delimitedCompare_secondPrefix_missing
    (outcome : EncodedWordOrdering)
    (firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 2 outcome
        [] firstCounter firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 7 .invalid
        [] firstCounter firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) := by
  delimitedCompareStepTac

theorem delimitedCompare_secondPayload_step
    (outcome : EncodedWordOrdering) (bit marker : Bool)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 3 outcome
        (bit :: input) firstCounter firstReversed
        (marker :: secondCounter) secondReversed
        firstForward secondForward source sourcePrefix output) =
      some (delimitedCompareConfiguration 3 outcome
        input firstCounter firstReversed
        secondCounter (bit :: secondReversed)
        firstForward secondForward
        (bit :: source) (true :: sourcePrefix) output) := by
  cases bit <;> cases marker <;> delimitedCompareStepTac

theorem delimitedCompare_secondPayload_finish
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 3 outcome
        input firstCounter firstReversed
        [] secondReversed firstForward secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 4 outcome
        input firstCounter firstReversed
        [] secondReversed firstForward secondForward
        source sourcePrefix output) := by
  delimitedCompareStepTac

theorem delimitedCompare_secondPayload_missing
    (outcome : EncodedWordOrdering) (marker : Bool)
    (firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 3 outcome
        [] firstCounter firstReversed
        (marker :: secondCounter) secondReversed
        firstForward secondForward source sourcePrefix output) =
      some (delimitedCompareConfiguration 7 .invalid
        [] firstCounter firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) := by
  cases marker <;> delimitedCompareStepTac

theorem delimitedCompare_reverseFirst_step
    (outcome : EncodedWordOrdering) (bit : Bool)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 4 outcome
        input firstCounter (bit :: firstReversed)
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 4 outcome
        input firstCounter firstReversed
        secondCounter secondReversed (bit :: firstForward)
        secondForward source sourcePrefix output) := by
  cases bit <;> delimitedCompareStepTac

theorem delimitedCompare_reverseFirst_finish
    (outcome : EncodedWordOrdering)
    (input firstCounter secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 4 outcome
        input firstCounter []
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 5 outcome
        input firstCounter []
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) := by
  delimitedCompareStepTac

theorem delimitedCompare_reverseSecond_step
    (outcome : EncodedWordOrdering) (bit : Bool)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 5 outcome
        input firstCounter firstReversed
        secondCounter (bit :: secondReversed)
        firstForward secondForward source sourcePrefix output) =
      some (delimitedCompareConfiguration 5 outcome
        input firstCounter firstReversed
        secondCounter secondReversed firstForward
        (bit :: secondForward) source sourcePrefix output) := by
  cases bit <;> delimitedCompareStepTac

theorem delimitedCompare_reverseSecond_finish
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 5 outcome
        input firstCounter firstReversed
        secondCounter [] firstForward secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 6 outcome
        input firstCounter firstReversed
        secondCounter [] firstForward secondForward
        source sourcePrefix output) := by
  delimitedCompareStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem delimitedCompare_words_equalBit
    (outcome : EncodedWordOrdering) (bit : Bool)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 6 outcome
        input firstCounter firstReversed
        secondCounter secondReversed
        (bit :: firstForward) (bit :: secondForward)
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 6 outcome
        input firstCounter firstReversed
        secondCounter secondReversed
        firstForward secondForward source sourcePrefix output) := by
  cases bit <;> delimitedCompareStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem delimitedCompare_words_lessBit
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 6 outcome
        input firstCounter firstReversed
        secondCounter secondReversed
        (false :: firstForward) (true :: secondForward)
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 7 .less
        input firstCounter firstReversed
        secondCounter secondReversed
        (false :: firstForward) (true :: secondForward)
        source sourcePrefix output) := by
  delimitedCompareStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem delimitedCompare_words_greaterBit
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 6 outcome
        input firstCounter firstReversed
        secondCounter secondReversed
        (true :: firstForward) (false :: secondForward)
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 7 .greater
        input firstCounter firstReversed
        secondCounter secondReversed
        (true :: firstForward) (false :: secondForward)
        source sourcePrefix output) := by
  delimitedCompareStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem delimitedCompare_words_firstEmpty
    (outcome : EncodedWordOrdering) (bit : Bool)
    (input firstCounter firstReversed secondCounter secondReversed
      secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 6 outcome
        input firstCounter firstReversed
        secondCounter secondReversed [] (bit :: secondForward)
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 7 .less
        input firstCounter firstReversed
        secondCounter secondReversed [] (bit :: secondForward)
        source sourcePrefix output) := by
  cases bit <;> delimitedCompareStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem delimitedCompare_words_secondEmpty
    (outcome : EncodedWordOrdering) (bit : Bool)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 6 outcome
        input firstCounter firstReversed
        secondCounter secondReversed (bit :: firstForward) []
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 7 .greater
        input firstCounter firstReversed
        secondCounter secondReversed (bit :: firstForward) []
        source sourcePrefix output) := by
  cases bit <;> delimitedCompareStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem delimitedCompare_words_bothEmpty
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 6 outcome
        input firstCounter firstReversed
        secondCounter secondReversed [] []
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 7 .equal
        input firstCounter firstReversed
        secondCounter secondReversed [] []
        source sourcePrefix output) := by
  delimitedCompareStepTac

theorem delimitedCompare_cleanup_firstCounter
    (outcome : EncodedWordOrdering) (bit : Bool)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 7 outcome
        input (bit :: firstCounter) firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 7 outcome
        input firstCounter firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) := by
  cases bit <;> delimitedCompareStepTac

theorem delimitedCompare_cleanup_firstReversed
    (outcome : EncodedWordOrdering) (bit : Bool)
    (input firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 7 outcome
        input [] (bit :: firstReversed)
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 7 outcome
        input [] firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output) := by
  cases bit <;> delimitedCompareStepTac

theorem delimitedCompare_cleanup_secondCounter
    (outcome : EncodedWordOrdering) (bit : Bool)
    (input secondCounter secondReversed firstForward secondForward
      source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 7 outcome
        input [] [] (bit :: secondCounter) secondReversed
        firstForward secondForward source sourcePrefix output) =
      some (delimitedCompareConfiguration 7 outcome
        input [] [] secondCounter secondReversed
        firstForward secondForward source sourcePrefix output) := by
  cases bit <;> delimitedCompareStepTac

theorem delimitedCompare_cleanup_secondReversed
    (outcome : EncodedWordOrdering) (bit : Bool)
    (input secondReversed firstForward secondForward
      source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 7 outcome
        input [] [] [] (bit :: secondReversed)
        firstForward secondForward source sourcePrefix output) =
      some (delimitedCompareConfiguration 7 outcome
        input [] [] [] secondReversed
        firstForward secondForward source sourcePrefix output) := by
  cases bit <;> delimitedCompareStepTac

theorem delimitedCompare_cleanup_firstForward
    (outcome : EncodedWordOrdering) (bit : Bool)
    (input firstForward secondForward
      source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 7 outcome
        input [] [] [] [] (bit :: firstForward) secondForward
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 7 outcome
        input [] [] [] [] firstForward secondForward
        source sourcePrefix output) := by
  cases bit <;> delimitedCompareStepTac

theorem delimitedCompare_cleanup_secondForward
    (outcome : EncodedWordOrdering) (bit : Bool)
    (input secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 7 outcome
        input [] [] [] [] [] (bit :: secondForward)
        source sourcePrefix output) =
      some (delimitedCompareConfiguration 7 outcome
        input [] [] [] [] [] secondForward
        source sourcePrefix output) := by
  cases bit <;> delimitedCompareStepTac

theorem delimitedCompare_cleanup_finish
    (outcome : EncodedWordOrdering)
    (input source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 7 outcome
        input [] [] [] [] [] [] source sourcePrefix output) =
      some (delimitedCompareConfiguration 8 outcome
        input [] [] [] [] [] [] source sourcePrefix output) := by
  delimitedCompareStepTac

theorem delimitedCompare_trailing_step
    (outcome : EncodedWordOrdering) (bit : Bool)
    (input source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 8 outcome
        (bit :: input) [] [] [] [] [] [] source sourcePrefix output) =
      some (delimitedCompareConfiguration 8 outcome
        input [] [] [] [] [] []
        (bit :: source) (true :: sourcePrefix) output) := by
  cases bit <;> delimitedCompareStepTac

theorem delimitedCompare_trailing_finish
    (outcome : EncodedWordOrdering)
    (source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 8 outcome
        [] [] [] [] [] [] [] source sourcePrefix output) =
      some (delimitedCompareConfiguration 9 outcome
        [] [] [] [] [] [] [] source sourcePrefix output) := by
  delimitedCompareStepTac

theorem delimitedCompare_outcome_step
    (outcome : EncodedWordOrdering)
    (source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 9 outcome
        [] [] [] [] [] [] [] source sourcePrefix output) =
      some (delimitedCompareConfiguration 10 outcome
        [] [] [] [] [] [] [] source sourcePrefix
        (encodedWordOrderingWord outcome ++ output)) := by
  cases outcome <;> delimitedCompareStepTac

theorem delimitedCompare_source_step
    (outcome : EncodedWordOrdering) (bit : Bool)
    (source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 10 outcome
        [] [] [] [] [] [] [] (bit :: source) sourcePrefix output) =
      some (delimitedCompareConfiguration 10 outcome
        [] [] [] [] [] [] [] source sourcePrefix (bit :: output)) := by
  cases bit <;> delimitedCompareStepTac

theorem delimitedCompare_source_finish
    (outcome : EncodedWordOrdering)
    (sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 10 outcome
        [] [] [] [] [] [] [] [] sourcePrefix output) =
      some (delimitedCompareConfiguration 11 outcome
        [] [] [] [] [] [] [] [] sourcePrefix (false :: output)) := by
  delimitedCompareStepTac

theorem delimitedCompare_prefix_step
    (outcome : EncodedWordOrdering) (bit : Bool)
    (sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 11 outcome
        [] [] [] [] [] [] [] [] (bit :: sourcePrefix) output) =
      some (delimitedCompareConfiguration 11 outcome
        [] [] [] [] [] [] [] [] sourcePrefix (true :: output)) := by
  cases bit <;> delimitedCompareStepTac

theorem delimitedCompare_prefix_finish
    (outcome : EncodedWordOrdering) (output : List Bool) :
    delimitedPairComparisonMachine.step
      (delimitedCompareConfiguration 11 outcome
        [] [] [] [] [] [] [] [] [] output) =
      some (Turing.haltList delimitedPairComparisonMachine output) := by
  cases outcome <;> delimitedCompareStepTac

end CNFEncodedClauseSort

end GapCVP

end
