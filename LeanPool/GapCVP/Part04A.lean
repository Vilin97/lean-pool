/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part03

/-! # GapCVP proof, part 04 -/

noncomputable section

open StateTransition (EvalsToInTime)
open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFFiniteRecordSort

open Computability Turing GapCVP.ThreeCNFReduction

/-- GapCVP reduction support. -/
def sourceOrderedDistinctRecords
    {α : Type} [Encodable α] [DecidableEq α]
    (records : List α) : List α :=
  sortedElements records.toFinset

@[simp] theorem sourceOrderedDistinctRecords_sortedElements
    {α : Type} [Encodable α] [DecidableEq α]
    (records : Finset α) :
    sourceOrderedDistinctRecords (sortedElements records) =
      sortedElements records := by
  simp only [sourceOrderedDistinctRecords, sortedElements, Finset.sort_toFinset]

end CNFFiniteRecordSort

namespace CNFInputDependentRecordSort

open Computability Turing GapCVP.CNFFiniteRecordSort

theorem sourceOrderedDistinctRecords_eq_of_nodup_pairwise
    {α : Type} [Encodable α] [DecidableEq α]
    (source candidate : List α)
    (hmembership : ∀ record : α,
      record ∈ candidate ↔ record ∈ source)
    (hnodup : candidate.Nodup)
    (hpairwise : candidate.Pairwise
      (fun first second =>
        Encodable.encode first ≤ Encodable.encode second)) :
    sourceOrderedDistinctRecords source = candidate := by
  let relation : α → α → Prop :=
    fun first second =>
      Encodable.encode first ≤ Encodable.encode second
  let : IsTrans α relation :=
    ⟨fun _ _ _ hab hbc => Nat.le_trans hab hbc⟩
  let : Std.Antisymm relation :=
    ⟨fun _ _ hab hba =>
      Encodable.encode_injective (Nat.le_antisymm hab hba)⟩
  let : Std.Total relation :=
    ⟨fun _ _ => Nat.le_total _ _⟩
  have hset : source.toFinset = candidate.toFinset := by
    ext record
    simpa only [List.mem_toFinset] using (hmembership record).symm
  change source.toFinset.sort relation = candidate
  rw [hset]
  exact (List.toFinset_sort relation hnodup).2 hpairwise

end CNFInputDependentRecordSort

namespace CNFNaturalOrderComparator

open Computability Turing GapCVP.BinaryEncoding GapCVP.CNFEncodedClauseSort

/-- GapCVP reduction support. -/
def littleEndianNaturalValue : List Bool → ℕ
  | [] => 0
  | false :: remaining => 2 * littleEndianNaturalValue remaining
  | true :: remaining => 2 * littleEndianNaturalValue remaining + 1

@[simp] private theorem littleEndianNaturalValue_encodePosNum (number : PosNum) :
    littleEndianNaturalValue (Computability.encodePosNum number) =
      (number : ℕ) := by
  induction number with
  | one => rfl
  | bit0 number ih =>
      simp only [encodePosNum, littleEndianNaturalValue, ih, PosNum.cast_bit0]
      omega
  | bit1 number ih =>
      simp only [encodePosNum, littleEndianNaturalValue, ih, PosNum.cast_bit1,
          Nat.add_right_cancel_iff]
      omega

@[simp] private theorem littleEndianNaturalValue_encodeNum (number : Num) :
    littleEndianNaturalValue (Computability.encodeNum number) =
      (number : ℕ) := by
  cases number with
  | zero => rfl
  | pos number =>
      exact littleEndianNaturalValue_encodePosNum number

@[simp] theorem littleEndianNaturalValue_encodeNat (number : ℕ) :
    littleEndianNaturalValue (Computability.encodeNat number) = number := by
  change littleEndianNaturalValue
    (Computability.encodeNum (number : Num)) = number
  rw [littleEndianNaturalValue_encodeNum, Num.to_of_nat]

private def littleEndianNaturalFold :
    EncodedWordOrdering → List Bool → List Bool → EncodedWordOrdering
  | current, [], [] => current
  | current, false :: first, [] =>
      littleEndianNaturalFold current first []
  | _, true :: first, [] =>
      littleEndianNaturalFold .greater first []
  | current, [], false :: second =>
      littleEndianNaturalFold current [] second
  | _, [], true :: second =>
      littleEndianNaturalFold .less [] second
  | current, false :: first, false :: second =>
      littleEndianNaturalFold current first second
  | _, false :: first, true :: second =>
      littleEndianNaturalFold .less first second
  | _, true :: first, false :: second =>
      littleEndianNaturalFold .greater first second
  | current, true :: first, true :: second =>
      littleEndianNaturalFold current first second
termination_by _ first second => first.length + second.length
decreasing_by all_goals simp_wf <;> omega

/-- GapCVP reduction support. -/
def littleEndianNaturalOrdering
    (first second : List Bool) : EncodedWordOrdering :=
  littleEndianNaturalFold .equal first second

private theorem littleEndianNaturalFold_eq_value_order
    (first second : List Bool) (current : EncodedWordOrdering) :
    littleEndianNaturalFold current first second =
      if littleEndianNaturalValue first <
          littleEndianNaturalValue second then .less
      else if littleEndianNaturalValue second <
          littleEndianNaturalValue first then .greater
      else current := by
  induction first generalizing second current with
  | nil =>
      induction second generalizing current with
      | nil => simp only [littleEndianNaturalFold, littleEndianNaturalValue, lt_self_iff_false,
          ↓reduceIte]
      | cons bit remaining ih =>
          cases bit <;>
            simp [littleEndianNaturalFold, littleEndianNaturalValue, ih]
  | cons bit first ih =>
      cases second with
      | nil =>
          cases bit <;>
            simp [littleEndianNaturalFold, littleEndianNaturalValue, ih] <;>
            split_ifs <;> simp_all
      | cons next second =>
          cases bit <;> cases next <;>
            simp [littleEndianNaturalFold, littleEndianNaturalValue, ih] <;>
            split_ifs <;> simp_all <;> omega

theorem littleEndianNaturalOrdering_eq_value_order
    (first second : List Bool) :
    littleEndianNaturalOrdering first second =
      if littleEndianNaturalValue first <
          littleEndianNaturalValue second then .less
      else if littleEndianNaturalValue second <
          littleEndianNaturalValue first then .greater
      else .equal := by
  exact littleEndianNaturalFold_eq_value_order first second .equal

@[simp] theorem littleEndianNaturalOrdering_encodeNat
    (first second : ℕ) :
    littleEndianNaturalOrdering
        (Computability.encodeNat first)
        (Computability.encodeNat second) =
      if first < second then .less
      else if second < first then .greater
      else .equal := by
  simp only [littleEndianNaturalOrdering_eq_value_order, littleEndianNaturalValue_encodeNat]

/-- GapCVP reduction support. -/
def delimitedNaturalPairOrdering (input : List Bool) :
    EncodedWordOrdering :=
  match readLengthPrefixedWord input with
  | none => .invalid
  | some (first, remaining) =>
      match readLengthPrefixedWord remaining with
      | none => .invalid
      | some (second, _) => littleEndianNaturalOrdering first second

/-- GapCVP reduction support. -/
def sourcePreservingDelimitedNaturalComparisonWord
    (input : List Bool) : List Bool :=
  lengthPrefixedWord input ++
    encodedWordOrderingWord (delimitedNaturalPairOrdering input)

/-- Internal support shared across GapCVP continuation modules. -/
theorem delimitedNaturalPairOrdering_valid
    (first second suffix : List Bool) :
    delimitedNaturalPairOrdering
      (lengthPrefixedWord first ++
        lengthPrefixedWord second ++ suffix) =
      littleEndianNaturalOrdering first second := by
  simp only [delimitedNaturalPairOrdering, List.append_assoc, readLengthPrefixedWord_append]

theorem delimitedNaturalPairOrdering_encodeNat
    (first second : ℕ) (suffix : List Bool) :
    delimitedNaturalPairOrdering
      (lengthPrefixedWord (Computability.encodeNat first) ++
        lengthPrefixedWord (Computability.encodeNat second) ++ suffix) =
      if first < second then .less
      else if second < first then .greater
      else .equal := by
  rw [delimitedNaturalPairOrdering_valid,
    littleEndianNaturalOrdering_encodeNat]

private def naturalCompareConsumeBoth
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState) :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  delimitedComparePop 5 (delimitedComparePop 6 continuation)

/-- Internal support shared across GapCVP continuation modules. -/
def naturalCompareWordsStatement :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  delimitedComparePeekFirst 5
    (delimitedComparePeekSecond 6
      (.branch (fun state => state.first = state.second)
        (naturalCompareConsumeBoth (delimitedCompareGoto 6))
        (.branch (fun state => state.first = some false)
          (naturalCompareConsumeBoth
            (delimitedCompareSetOutcome .less 6))
          (naturalCompareConsumeBoth
            (delimitedCompareSetOutcome .greater 6))))
      (.branch (fun state => state.first = some false)
        (delimitedComparePop 5 (delimitedCompareGoto 6))
        (delimitedComparePop 5
          (delimitedCompareSetOutcome .greater 6))))
    (delimitedComparePeekSecond 6
      (.branch (fun state => state.second = some false)
        (delimitedComparePop 6 (delimitedCompareGoto 6))
        (delimitedComparePop 6
          (delimitedCompareSetOutcome .less 6)))
      (.branch (fun state => state.outcome = .invalid)
        (delimitedCompareSetOutcome .equal 7)
        (delimitedCompareGoto 7)))

/-- Internal support shared across GapCVP continuation modules. -/
abbrev delimitedNaturalComparisonMachine : Turing.FinTM2 where
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
      naturalCompareWordsStatement
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

/-- Internal support shared across GapCVP continuation modules. -/
def naturalCompareConfiguration (phase : Fin 12)
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedNaturalComparisonMachine.Cfg :=
  delimitedCompareConfiguration phase outcome
    input firstCounter firstReversed secondCounter secondReversed
    firstForward secondForward source sourcePrefix output

/-- Internal support shared across GapCVP continuation modules. -/
theorem delimitedNaturalComparisonMachine_init (input : List Bool) :
    Turing.initList delimitedNaturalComparisonMachine input =
      naturalCompareConfiguration 0 .invalid
        input [] [] [] [] [] [] [] [] [] := by
  exact delimitedPairComparisonMachine_init input

/-- Executes the `naturalCompareStepTac` machine-step simplifier. -/
macro "naturalCompareStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [delimitedNaturalComparisonMachine,
          naturalCompareConfiguration, delimitedCompareConfiguration,
          naturalCompareWordsStatement, naturalCompareConsumeBoth,
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

private theorem naturalCompare_words_equalBit
    (outcome : EncodedWordOrdering) (bit : Bool)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedNaturalComparisonMachine.step
      (naturalCompareConfiguration 6 outcome
        input firstCounter firstReversed secondCounter secondReversed
        (bit :: firstForward) (bit :: secondForward)
        source sourcePrefix output) =
      some (naturalCompareConfiguration 6 outcome
        input firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output) := by
  cases bit <;> naturalCompareStepTac

private theorem naturalCompare_words_lessBit
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedNaturalComparisonMachine.step
      (naturalCompareConfiguration 6 outcome
        input firstCounter firstReversed secondCounter secondReversed
        (false :: firstForward) (true :: secondForward)
        source sourcePrefix output) =
      some (naturalCompareConfiguration 6 .less
        input firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output) := by
  naturalCompareStepTac

private theorem naturalCompare_words_greaterBit
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedNaturalComparisonMachine.step
      (naturalCompareConfiguration 6 outcome
        input firstCounter firstReversed secondCounter secondReversed
        (true :: firstForward) (false :: secondForward)
        source sourcePrefix output) =
      some (naturalCompareConfiguration 6 .greater
        input firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output) := by
  naturalCompareStepTac

private theorem naturalCompare_words_firstEmpty_false
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      secondForward source sourcePrefix output : List Bool) :
    delimitedNaturalComparisonMachine.step
      (naturalCompareConfiguration 6 outcome
        input firstCounter firstReversed secondCounter secondReversed
        [] (false :: secondForward) source sourcePrefix output) =
      some (naturalCompareConfiguration 6 outcome
        input firstCounter firstReversed secondCounter secondReversed
        [] secondForward source sourcePrefix output) := by
  naturalCompareStepTac

private theorem naturalCompare_words_firstEmpty_true
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      secondForward source sourcePrefix output : List Bool) :
    delimitedNaturalComparisonMachine.step
      (naturalCompareConfiguration 6 outcome
        input firstCounter firstReversed secondCounter secondReversed
        [] (true :: secondForward) source sourcePrefix output) =
      some (naturalCompareConfiguration 6 .less
        input firstCounter firstReversed secondCounter secondReversed
        [] secondForward source sourcePrefix output) := by
  naturalCompareStepTac

private theorem naturalCompare_words_secondEmpty_false
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward source sourcePrefix output : List Bool) :
    delimitedNaturalComparisonMachine.step
      (naturalCompareConfiguration 6 outcome
        input firstCounter firstReversed secondCounter secondReversed
        (false :: firstForward) [] source sourcePrefix output) =
      some (naturalCompareConfiguration 6 outcome
        input firstCounter firstReversed secondCounter secondReversed
        firstForward [] source sourcePrefix output) := by
  naturalCompareStepTac

private theorem naturalCompare_words_secondEmpty_true
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward source sourcePrefix output : List Bool) :
    delimitedNaturalComparisonMachine.step
      (naturalCompareConfiguration 6 outcome
        input firstCounter firstReversed secondCounter secondReversed
        (true :: firstForward) [] source sourcePrefix output) =
      some (naturalCompareConfiguration 6 .greater
        input firstCounter firstReversed secondCounter secondReversed
        firstForward [] source sourcePrefix output) := by
  naturalCompareStepTac

private theorem naturalCompare_words_bothEmpty_invalid
    (input firstCounter firstReversed secondCounter secondReversed
      source sourcePrefix output : List Bool) :
    delimitedNaturalComparisonMachine.step
      (naturalCompareConfiguration 6 .invalid
        input firstCounter firstReversed secondCounter secondReversed
        [] [] source sourcePrefix output) =
      some (naturalCompareConfiguration 7 .equal
        input firstCounter firstReversed secondCounter secondReversed
        [] [] source sourcePrefix output) := by
  naturalCompareStepTac

private theorem naturalCompare_words_bothEmpty
    (outcome : EncodedWordOrdering)
    (hvalid : outcome ≠ .invalid)
    (input firstCounter firstReversed secondCounter secondReversed
      source sourcePrefix output : List Bool) :
    delimitedNaturalComparisonMachine.step
      (naturalCompareConfiguration 6 outcome
        input firstCounter firstReversed secondCounter secondReversed
        [] [] source sourcePrefix output) =
      some (naturalCompareConfiguration 7 outcome
        input firstCounter firstReversed secondCounter secondReversed
        [] [] source sourcePrefix output) := by
  cases outcome with
  | invalid => exact (hvalid rfl).elim
  | less => naturalCompareStepTac
  | equal => naturalCompareStepTac
  | greater => naturalCompareStepTac

private def naturalComparisonEffectiveOutcome
    (outcome : EncodedWordOrdering) : EncodedWordOrdering :=
  if outcome = .invalid then .equal else outcome

private def naturalCompare_wordsTrace
    (outcome : EncodedWordOrdering)
    (first second input firstCounter firstReversed
      secondCounter secondReversed source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedNaturalComparisonMachine.step
      (naturalCompareConfiguration 6 outcome
        input firstCounter firstReversed secondCounter secondReversed
        first second source sourcePrefix output)
      (some (naturalCompareConfiguration 7
        (littleEndianNaturalFold
          (naturalComparisonEffectiveOutcome outcome) first second)
        input firstCounter firstReversed secondCounter secondReversed
        [] [] source sourcePrefix output))
      (first.length + second.length + 1) := by
  induction first generalizing second outcome with
  | nil =>
      induction second generalizing outcome with
      | nil =>
          cases outcome with
          | invalid =>
              simpa only [FinTM2.step, Fin.isValue, naturalComparisonEffectiveOutcome, ↓reduceIte,
                  littleEndianNaturalFold,
                  List.length_nil, add_zero, zero_add] using
                  oneStep _ _
                    (naturalCompare_words_bothEmpty_invalid input firstCounter firstReversed
                        secondCounter secondReversed source
                      sourcePrefix output)
          | less =>
              simpa only [FinTM2.step, Fin.isValue, naturalComparisonEffectiveOutcome,
                  reduceCtorEq, ↓reduceIte,
                  littleEndianNaturalFold, List.length_nil, add_zero, zero_add] using
                  oneStep _ _
                    (naturalCompare_words_bothEmpty .less (by decide) input firstCounter
                        firstReversed secondCounter secondReversed
                      source sourcePrefix output)
          | equal =>
              simpa only [FinTM2.step, Fin.isValue, naturalComparisonEffectiveOutcome,
                  reduceCtorEq, ↓reduceIte,
                  littleEndianNaturalFold, List.length_nil, add_zero, zero_add] using
                  oneStep _ _
                    (naturalCompare_words_bothEmpty .equal (by decide) input firstCounter
                        firstReversed secondCounter secondReversed
                      source sourcePrefix output)
          | greater =>
              simpa only [FinTM2.step, Fin.isValue, naturalComparisonEffectiveOutcome,
                  reduceCtorEq, ↓reduceIte,
                  littleEndianNaturalFold, List.length_nil, add_zero, zero_add] using
                  oneStep _ _
                    (naturalCompare_words_bothEmpty .greater (by decide) input firstCounter
                        firstReversed secondCounter secondReversed
                      source sourcePrefix output)
      | cons bit remaining ih =>
          cases bit with
          | false =>
              have hfirst := oneStep _ _ (naturalCompare_words_firstEmpty_false outcome
                  input firstCounter firstReversed
                  secondCounter secondReversed remaining
                  source sourcePrefix output)
              have hrest := ih (outcome := outcome)
              have hfull := EvalsToInTime.trans delimitedNaturalComparisonMachine.step
                _ _ _ _ _ hfirst hrest
              simpa only [FinTM2.step, Fin.isValue, littleEndianNaturalFold, List.length_nil,
                  List.length_cons, zero_add,
                  Nat.add_assoc, Nat.reduceAdd] using hfull
          | true =>
              have hfirst := oneStep _ _ (naturalCompare_words_firstEmpty_true outcome
                  input firstCounter firstReversed
                  secondCounter secondReversed remaining
                  source sourcePrefix output)
              have hrest := ih (outcome := .less)
              have hfull := EvalsToInTime.trans delimitedNaturalComparisonMachine.step
                _ _ _ _ _ hfirst hrest
              simpa only [FinTM2.step, Fin.isValue, naturalComparisonEffectiveOutcome,
                  littleEndianNaturalFold,
                  List.length_nil, List.length_cons, zero_add, Nat.add_assoc, Nat.reduceAdd,
                      reduceCtorEq, ↓reduceIte] using hfull
  | cons bit remaining ih =>
      cases second with
      | nil =>
          cases bit with
          | false =>
              have hfirst := oneStep _ _ (naturalCompare_words_secondEmpty_false outcome
                  input firstCounter firstReversed
                  secondCounter secondReversed remaining
                  source sourcePrefix output)
              have hrest := ih (second := []) (outcome := outcome)
              have hfull := EvalsToInTime.trans delimitedNaturalComparisonMachine.step
                _ _ _ _ _ hfirst hrest
              simpa only [FinTM2.step, Fin.isValue, littleEndianNaturalFold, List.length_cons,
                  List.length_nil, add_zero,
                  Nat.add_assoc, Nat.reduceAdd] using hfull
          | true =>
              have hfirst := oneStep _ _ (naturalCompare_words_secondEmpty_true outcome
                  input firstCounter firstReversed
                  secondCounter secondReversed remaining
                  source sourcePrefix output)
              have hrest := ih (second := []) (outcome := .greater)
              have hfull := EvalsToInTime.trans delimitedNaturalComparisonMachine.step
                _ _ _ _ _ hfirst hrest
              simpa only [FinTM2.step, Fin.isValue, naturalComparisonEffectiveOutcome,
                  littleEndianNaturalFold,
                  List.length_cons, List.length_nil, add_zero, Nat.add_assoc, Nat.reduceAdd,
                      reduceCtorEq, ↓reduceIte] using hfull
      | cons next second =>
          cases bit <;> cases next
          · have hfirst := oneStep _ _ (naturalCompare_words_equalBit outcome false
                input firstCounter firstReversed
                secondCounter secondReversed remaining second
                source sourcePrefix output)
            have hrest := ih (second := second) (outcome := outcome)
            have hfull := EvalsToInTime.trans delimitedNaturalComparisonMachine.step
              _ _ _ _ _ hfirst hrest
            exact rebound (by simpa only [FinTM2.step, Fin.isValue, littleEndianNaturalFold,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
                                  Nat.reduceAdd] using hfull)
              (by simp only [List.length_cons]; omega)
          · have hfirst := oneStep _ _ (naturalCompare_words_lessBit outcome
                input firstCounter firstReversed
                secondCounter secondReversed remaining second
                source sourcePrefix output)
            have hrest := ih (second := second) (outcome := .less)
            have hfull := EvalsToInTime.trans delimitedNaturalComparisonMachine.step
              _ _ _ _ _ hfirst hrest
            exact rebound (by simpa only [FinTM2.step, Fin.isValue,
                naturalComparisonEffectiveOutcome, littleEndianNaturalFold,
                                  reduceCtorEq, ↓reduceIte, Nat.add_assoc, Nat.add_comm,
                                      Nat.add_left_comm, Nat.reduceAdd] using hfull)
              (by simp only [List.length_cons]; omega)
          · have hfirst := oneStep _ _ (naturalCompare_words_greaterBit outcome
                input firstCounter firstReversed
                secondCounter secondReversed remaining second
                source sourcePrefix output)
            have hrest := ih (second := second) (outcome := .greater)
            have hfull := EvalsToInTime.trans delimitedNaturalComparisonMachine.step
              _ _ _ _ _ hfirst hrest
            exact rebound (by simpa only [FinTM2.step, Fin.isValue,
                naturalComparisonEffectiveOutcome, littleEndianNaturalFold,
                                  reduceCtorEq, ↓reduceIte, Nat.add_assoc, Nat.add_comm,
                                      Nat.add_left_comm, Nat.reduceAdd] using hfull)
              (by simp only [List.length_cons]; omega)
          · have hfirst := oneStep _ _ (naturalCompare_words_equalBit outcome true
                input firstCounter firstReversed
                secondCounter secondReversed remaining second
                source sourcePrefix output)
            have hrest := ih (second := second) (outcome := outcome)
            have hfull := EvalsToInTime.trans delimitedNaturalComparisonMachine.step
              _ _ _ _ _ hfirst hrest
            exact rebound (by simpa only [FinTM2.step, Fin.isValue, littleEndianNaturalFold,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
                                  Nat.reduceAdd] using hfull)
              (by simp only [List.length_cons]; omega)

/-- Internal support shared across GapCVP continuation modules. -/
def naturalCompareWordsTraceInitial
    (first second input firstCounter firstReversed
      secondCounter secondReversed source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedNaturalComparisonMachine.step
      (naturalCompareConfiguration 6 .invalid
        input firstCounter firstReversed secondCounter secondReversed
        first second source sourcePrefix output)
      (some (naturalCompareConfiguration 7
        (littleEndianNaturalOrdering first second)
        input firstCounter firstReversed secondCounter secondReversed
        [] [] source sourcePrefix output))
      (first.length + second.length + 1) := by
  simpa only [FinTM2.step, Fin.isValue, littleEndianNaturalOrdering,
      naturalComparisonEffectiveOutcome,
      ↓reduceIte] using
      naturalCompare_wordsTrace .invalid first second input firstCounter firstReversed
          secondCounter secondReversed source
        sourcePrefix output

end CNFNaturalOrderComparator

namespace CNFNaturalOrderTotalComparator

open Computability Turing GapCVP.BinaryEncoding GapCVP.CNFEncodedClauseSort
open GapCVP.CNFNaturalOrderComparator

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem delimitedNaturalPairOrdering_missingFirst
    (count : ℕ) :
    delimitedNaturalPairOrdering (List.replicate count true) = .invalid := by
  simp only [delimitedNaturalPairOrdering, readLengthPrefixedWord,
      SourceTotalStructuralDecoder.readUnaryPrefix_missing]

/-- Internal support shared across GapCVP continuation modules. -/
theorem delimitedNaturalPairOrdering_shortFirst
    (count : ℕ) (payload : List Bool)
    (hshort : payload.length < count) :
    delimitedNaturalPairOrdering
      (List.replicate count true ++ false :: payload) = .invalid := by
  have hnot : ¬ count ≤ payload.length := by omega
  simp only [delimitedNaturalPairOrdering, readLengthPrefixedWord, readUnaryPrefix_replicate, hnot,
      ↓reduceIte]

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem delimitedNaturalPairOrdering_missingSecond
    (first : List Bool) (count : ℕ) :
    delimitedNaturalPairOrdering
      (lengthPrefixedWord first ++
        List.replicate count true) = .invalid := by
  unfold delimitedNaturalPairOrdering
  rw [readLengthPrefixedWord_append first
    (List.replicate count true)]
  simp only [readLengthPrefixedWord, SourceTotalStructuralDecoder.readUnaryPrefix_missing]

/-- Internal support shared across GapCVP continuation modules. -/
theorem delimitedNaturalPairOrdering_shortSecond
    (first : List Bool) (count : ℕ) (payload : List Bool)
    (hshort : payload.length < count) :
    delimitedNaturalPairOrdering
      (lengthPrefixedWord first ++
        (List.replicate count true ++ false :: payload)) = .invalid := by
  unfold delimitedNaturalPairOrdering
  rw [readLengthPrefixedWord_append first
    (List.replicate count true ++ false :: payload)]
  have hnot : ¬ count ≤ payload.length := by omega
  simp only [readLengthPrefixedWord, readUnaryPrefix_replicate, hnot, ↓reduceIte]

theorem sourcePreservingNaturalComparison_valid
    (first second suffix : List Bool) :
    sourcePreservingDelimitedNaturalComparisonWord
        (lengthPrefixedWord first ++
          lengthPrefixedWord second ++ suffix) =
      lengthPrefixedWord
        (lengthPrefixedWord first ++
          lengthPrefixedWord second ++ suffix) ++
        encodedWordOrderingWord
          (littleEndianNaturalOrdering first second) := by
  simp only [sourcePreservingDelimitedNaturalComparisonWord]
  rw [delimitedNaturalPairOrdering_valid]

end CNFNaturalOrderTotalComparator

namespace CNFNaturalOrderCertifiedComparator

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.CNFSortingDedup GapCVP.CNFEncodedClauseSort GapCVP.CNFNaturalOrderComparator
open GapCVP.CNFNaturalOrderTotalComparator

/-- Internal support shared across GapCVP continuation modules. -/
theorem certifiedNatural_step_eq_old
    (configuration : delimitedNaturalComparisonMachine.Cfg)
    (hphase : configuration.l ≠ some (6 : Fin 12)) :
    delimitedNaturalComparisonMachine.step configuration =
      delimitedPairComparisonMachine.step configuration := by
  rcases configuration with ⟨phase, state, stackWords⟩
  cases phase with
  | none =>
      simp only [FinTM2.step, TM2.step]
      rfl
  | some phase =>
      have hnot : phase ≠ (6 : Fin 12) := by
        simpa only [Fin.isValue, ne_eq, Option.some.injEq] using hphase
      have hprogram :
          delimitedNaturalComparisonMachine.m phase =
            delimitedPairComparisonMachine.m phase := by
        simp only [delimitedNaturalComparisonMachine, Fin.isValue, hnot, ↓reduceIte]
      change
        some (Turing.TM2.stepAux
          (delimitedNaturalComparisonMachine.m phase) state stackWords) =
        some (Turing.TM2.stepAux
          (delimitedPairComparisonMachine.m phase) state stackWords)
      rw [hprogram]

end CNFNaturalOrderCertifiedComparator

end GapCVP

end
