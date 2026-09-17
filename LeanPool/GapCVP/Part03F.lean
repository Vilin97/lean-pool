/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part03E

/-! # GapCVP proof, part 03, continuation 06 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFEncodedClauseSort

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder

open GapCVP.CNFSortingDedup

namespace DelimitedCompareTrace

/-- Lifts each old-machine step outside the specialized comparison phase. -/
abbrev NonComparisonStepLift
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg) :=
  ∀ {first next}, first.l ≠ some (6 : Fin 12) →
    delimitedPairComparisonMachine.step first = some next →
    EvalsToInTime chosenStep first (some next) 1

/-- Clears the six comparison work tapes using any compatible machine step. -/
def cleanup (chosenStep : delimitedPairComparisonMachine.Cfg →
    Option delimitedPairComparisonMachine.Cfg) (lift : NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 7 outcome
        input firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 8 outcome
        input [] [] [] [] [] [] source sourcePrefix output))
      (firstCounter.length + firstReversed.length +
        secondCounter.length + secondReversed.length +
        firstForward.length + secondForward.length + 1) := by
  have hfirstCounter := TraceGolf.sweepTrace chosenStep
    (fun current => delimitedCompareConfiguration 7 outcome input current firstReversed
      secondCounter secondReversed firstForward secondForward source sourcePrefix output)
    (fun bit remaining => lift (by simp [delimitedCompareConfiguration])
      (delimitedCompare_cleanup_firstCounter outcome bit input remaining firstReversed
        secondCounter secondReversed firstForward secondForward source sourcePrefix output))
    firstCounter
  have hfirstReversed := TraceGolf.sweepTrace chosenStep
    (fun current => delimitedCompareConfiguration 7 outcome input [] current secondCounter
      secondReversed firstForward secondForward source sourcePrefix output)
    (fun bit remaining => lift (by simp [delimitedCompareConfiguration])
      (delimitedCompare_cleanup_firstReversed outcome bit input remaining secondCounter
        secondReversed firstForward secondForward source sourcePrefix output))
    firstReversed
  have hsecondCounter := TraceGolf.sweepTrace chosenStep
    (fun current => delimitedCompareConfiguration 7 outcome input [] [] current secondReversed
      firstForward secondForward source sourcePrefix output)
    (fun bit remaining => lift (by simp [delimitedCompareConfiguration])
      (delimitedCompare_cleanup_secondCounter outcome bit input remaining secondReversed
        firstForward secondForward source sourcePrefix output))
    secondCounter
  have hsecondReversed := TraceGolf.sweepTrace chosenStep
    (fun current => delimitedCompareConfiguration 7 outcome input [] [] [] current firstForward
      secondForward source sourcePrefix output)
    (fun bit remaining => lift (by simp [delimitedCompareConfiguration])
      (delimitedCompare_cleanup_secondReversed outcome bit input remaining firstForward
        secondForward source sourcePrefix output))
    secondReversed
  have hfirstForward := TraceGolf.sweepTrace chosenStep
    (fun current => delimitedCompareConfiguration 7 outcome input [] [] [] [] current
      secondForward source sourcePrefix output)
    (fun bit remaining => lift (by simp [delimitedCompareConfiguration])
      (delimitedCompare_cleanup_firstForward outcome bit input remaining secondForward
        source sourcePrefix output))
    firstForward
  have hsecondForward := TraceGolf.sweepTrace chosenStep
    (fun current => delimitedCompareConfiguration 7 outcome input [] [] [] [] [] current
      source sourcePrefix output)
    (fun bit remaining => lift (by simp [delimitedCompareConfiguration])
      (delimitedCompare_cleanup_secondForward outcome bit input remaining
        source sourcePrefix output))
    secondForward
  have hfinish := lift (by simp [delimitedCompareConfiguration])
    (delimitedCompare_cleanup_finish outcome input source sourcePrefix output)
  have h01 := EvalsToInTime.trans chosenStep _ _ _ _ _ hfirstCounter hfirstReversed
  have h012 := EvalsToInTime.trans chosenStep _ _ _ _ _ h01 hsecondCounter
  have h0123 := EvalsToInTime.trans chosenStep _ _ _ _ _ h012 hsecondReversed
  have h01234 := EvalsToInTime.trans chosenStep _ _ _ _ _ h0123 hfirstForward
  have h012345 := EvalsToInTime.trans chosenStep _ _ _ _ _ h01234 hsecondForward
  have hfull := EvalsToInTime.trans chosenStep _ _ _ _ _ h012345 hfinish
  exact rebound hfull (by omega)

end DelimitedCompareTrace

/-- Restores the trailing input using any compatible machine step. -/
def DelimitedCompareTrace.trailing
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg) (lift : NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering)
    (input source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 8 outcome
        input [] [] [] [] [] [] source sourcePrefix output)
      (some (delimitedCompareConfiguration 9 outcome
        [] [] [] [] [] [] [] (input.reverse ++ source)
        (List.replicate input.length true ++ sourcePrefix) output))
      (input.length + 1) := by
  induction input generalizing source sourcePrefix with
  | nil =>
      simpa only [List.reverse_nil, List.nil_append, List.length_nil, List.replicate_zero,
          zero_add] using
        lift (by simp [delimitedCompareConfiguration])
          (delimitedCompare_trailing_finish outcome source sourcePrefix output)
  | cons bit remaining ih =>
      have hfirst := lift (by simp [delimitedCompareConfiguration])
        (delimitedCompare_trailing_step outcome bit remaining source sourcePrefix output)
      have hrest := ih (source := bit :: source) (sourcePrefix := true :: sourcePrefix)
      simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
          List.length_cons, List.replicate_succ, Nat.add_assoc, Nat.reduceAdd,
          replicate_append_bit_cons] using
        EvalsToInTime.trans chosenStep _ _ _ _ _ hfirst hrest

/-- Restores the saved source using any compatible machine step. -/
def DelimitedCompareTrace.source
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering) (source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 10 outcome
        [] [] [] [] [] [] [] source sourcePrefix output)
      (some (delimitedCompareConfiguration 11 outcome
        [] [] [] [] [] [] [] [] sourcePrefix (false :: (source.reverse ++ output))))
      (source.length + 1) := by
  induction source generalizing output with
  | nil =>
      simpa only [List.reverse_nil, List.nil_append, List.length_nil, zero_add] using
        lift (by simp [delimitedCompareConfiguration])
          (delimitedCompare_source_finish outcome sourcePrefix output)
  | cons bit remaining ih =>
      have hfirst := lift (by simp [delimitedCompareConfiguration])
        (delimitedCompare_source_step outcome bit remaining sourcePrefix output)
      have hrest := ih (output := bit :: output)
      simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using
        EvalsToInTime.trans chosenStep _ _ _ _ _ hfirst hrest

/-- Restores prefix markers and halts using any compatible machine step. -/
def DelimitedCompareTrace.prefix
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering) (sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 11 outcome
        [] [] [] [] [] [] [] [] sourcePrefix output)
      (some (Turing.haltList delimitedPairComparisonMachine
        (List.replicate sourcePrefix.length true ++ output)))
      (sourcePrefix.length + 1) := by
  induction sourcePrefix generalizing output with
  | nil =>
      simpa only [List.length_nil, List.replicate_zero, List.nil_append, zero_add] using
        lift (by simp [delimitedCompareConfiguration])
          (delimitedCompare_prefix_finish outcome output)
  | cons bit remaining ih =>
      have hfirst := lift (by simp [delimitedCompareConfiguration])
        (delimitedCompare_prefix_step outcome bit remaining output)
      have hrest := ih (output := true :: output)
      simpa only [List.length_cons, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd, SourceStructuralDecoder.replicate_true_append_cons] using
        EvalsToInTime.trans chosenStep _ _ _ _ _ hfirst hrest

/-- GapCVP reduction support. -/
def delimitedCompareRestoredWord
    (outcome : EncodedWordOrdering)
    (input source sourcePrefix output : List Bool) : List Bool :=
  List.replicate (input.length + sourcePrefix.length) true ++
    false ::
      (source.reverse ++ input ++ encodedWordOrderingWord outcome ++ output)

/-- Restores every saved tape and halts using any compatible machine step. -/
def DelimitedCompareTrace.finish
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 7 outcome
        input firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (Turing.haltList delimitedPairComparisonMachine
        (delimitedCompareRestoredWord outcome input source sourcePrefix output)))
      (firstCounter.length + firstReversed.length +
        secondCounter.length + secondReversed.length +
        firstForward.length + secondForward.length +
        3 * input.length + source.length + sourcePrefix.length + 5) := by
  have hcleanup := DelimitedCompareTrace.cleanup chosenStep lift outcome
    input firstCounter firstReversed secondCounter secondReversed
    firstForward secondForward source sourcePrefix output
  have htrailing := DelimitedCompareTrace.trailing chosenStep lift outcome
    input source sourcePrefix output
  have houtcome := lift (by simp [delimitedCompareConfiguration])
    (delimitedCompare_outcome_step outcome
      (input.reverse ++ source)
      (List.replicate input.length true ++ sourcePrefix) output)
  have hsource := DelimitedCompareTrace.source chosenStep lift outcome
    (input.reverse ++ source)
    (List.replicate input.length true ++ sourcePrefix)
    (encodedWordOrderingWord outcome ++ output)
  have hprefix :
      EvalsToInTime chosenStep (delimitedCompareConfiguration 11 outcome
          [] [] [] [] [] [] [] []
          (List.replicate input.length true ++ sourcePrefix)
          (false :: ((input.reverse ++ source).reverse ++
            (encodedWordOrderingWord outcome ++ output))))
        (some (Turing.haltList delimitedPairComparisonMachine
          (delimitedCompareRestoredWord outcome input source sourcePrefix output)))
        ((List.replicate input.length true ++ sourcePrefix).length + 1) := by
    simpa only [List.reverse_append, List.reverse_reverse, List.append_assoc,
        delimitedCompareRestoredWord, List.length_append, List.length_replicate] using
      DelimitedCompareTrace.prefix chosenStep lift outcome
        (List.replicate input.length true ++ sourcePrefix)
        (false :: ((input.reverse ++ source).reverse ++
          (encodedWordOrderingWord outcome ++ output)))
  have hfirst := EvalsToInTime.trans chosenStep _ _ _ _ _ hcleanup htrailing
  have hsecond := EvalsToInTime.trans chosenStep _ _ _ _ _ hfirst houtcome
  have hthird := EvalsToInTime.trans chosenStep _ _ _ _ _ hsecond hsource
  have hfull := EvalsToInTime.trans chosenStep _ _ _ _ _ hthird hprefix
  apply rebound hfull
  simp only [List.length_append, List.length_reverse, List.length_replicate]
  omega

/-- Internal support shared across GapCVP continuation modules. -/
def delimitedCompareFinishTrace
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 7 outcome
        input firstCounter firstReversed
        secondCounter secondReversed firstForward secondForward
        source sourcePrefix output)
      (some (Turing.haltList delimitedPairComparisonMachine
        (delimitedCompareRestoredWord outcome
          input source sourcePrefix output)))
      (firstCounter.length + firstReversed.length +
        secondCounter.length + secondReversed.length +
        firstForward.length + secondForward.length +
        3 * input.length + source.length + sourcePrefix.length + 5) := by
  exact DelimitedCompareTrace.finish delimitedPairComparisonMachine.step
    (fun _ transition => oneStep _ _ transition) outcome input firstCounter firstReversed
    secondCounter secondReversed firstForward secondForward source sourcePrefix output

/-- Reads the first unary prefix using any compatible machine step. -/
def DelimitedCompareTrace.firstPrefix
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering) (count : ℕ)
    (tail firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 0 outcome
        (List.replicate count true ++ false :: tail)
        firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 1 outcome
        tail (List.replicate count true ++ firstCounter)
        firstReversed secondCounter secondReversed
        firstForward secondForward
        (false :: (List.replicate count true ++ source))
        (List.replicate (count + 1) true ++ sourcePrefix) output))
      (count + 1) := by
  induction count generalizing firstCounter source sourcePrefix with
  | zero =>
      simpa only [List.replicate_zero, List.nil_append, zero_add, List.replicate_one,
          List.cons_append] using
        lift (by simp [delimitedCompareConfiguration])
          (delimitedCompare_firstPrefix_delimiter outcome tail firstCounter firstReversed
            secondCounter secondReversed firstForward secondForward source sourcePrefix output)
  | succ count ih =>
      have hfirst := lift (by simp [delimitedCompareConfiguration])
        (delimitedCompare_firstPrefix_true outcome
          (List.replicate count true ++ false :: tail) firstCounter firstReversed
          secondCounter secondReversed firstForward secondForward source sourcePrefix output)
      have hrest := ih (firstCounter := true :: firstCounter)
        (source := true :: source) (sourcePrefix := true :: sourcePrefix)
      simpa only [List.replicate_succ, List.cons_append, Nat.add_assoc, Nat.reduceAdd,
          replicate_append_bit_cons] using
        EvalsToInTime.trans chosenStep _ _ _ _ _ hfirst hrest

/-- Internal support shared across GapCVP continuation modules. -/
def delimitedCompareFirstPrefixTrace
    (outcome : EncodedWordOrdering) (count : ℕ)
    (tail firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 0 outcome
        (List.replicate count true ++ false :: tail)
        firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 1 outcome
        tail (List.replicate count true ++ firstCounter)
        firstReversed secondCounter secondReversed
        firstForward secondForward
        (false :: (List.replicate count true ++ source))
        (List.replicate (count + 1) true ++ sourcePrefix) output))
      (count + 1) := by
  exact DelimitedCompareTrace.firstPrefix delimitedPairComparisonMachine.step
    (fun _ transition => oneStep _ _ transition) outcome count tail firstCounter firstReversed
    secondCounter secondReversed firstForward secondForward source sourcePrefix output

/-- Detects a missing first delimiter using any compatible machine step. -/
def DelimitedCompareTrace.firstMissingPrefix
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering) (count : ℕ)
    (firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 0 outcome
        (List.replicate count true)
        firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 7 .invalid
        [] (List.replicate count true ++ firstCounter)
        firstReversed secondCounter secondReversed
        firstForward secondForward
        (List.replicate count true ++ source)
        (List.replicate count true ++ sourcePrefix) output))
      (count + 1) := by
  induction count generalizing firstCounter source sourcePrefix with
  | zero =>
      simpa only [List.replicate_zero, List.nil_append, zero_add] using
        lift (by simp [delimitedCompareConfiguration])
          (delimitedCompare_firstPrefix_missing outcome firstCounter firstReversed secondCounter
            secondReversed firstForward secondForward source sourcePrefix output)
  | succ count ih =>
      have hfirst := lift (by simp [delimitedCompareConfiguration])
        (delimitedCompare_firstPrefix_true outcome (List.replicate count true)
          firstCounter firstReversed secondCounter secondReversed firstForward secondForward
          source sourcePrefix output)
      have hrest := ih (firstCounter := true :: firstCounter)
        (source := true :: source) (sourcePrefix := true :: sourcePrefix)
      simpa only [List.replicate_succ, List.cons_append, Nat.add_assoc, Nat.reduceAdd,
          replicate_append_bit_cons] using
        EvalsToInTime.trans chosenStep _ _ _ _ _ hfirst hrest

/-- Internal support shared across GapCVP continuation modules. -/
def delimitedCompareFirstMissingPrefixTrace
    (outcome : EncodedWordOrdering) (count : ℕ)
    (firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 0 outcome
        (List.replicate count true)
        firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 7 .invalid
        [] (List.replicate count true ++ firstCounter)
        firstReversed secondCounter secondReversed
        firstForward secondForward
        (List.replicate count true ++ source)
        (List.replicate count true ++ sourcePrefix) output))
      (count + 1) := by
  exact DelimitedCompareTrace.firstMissingPrefix delimitedPairComparisonMachine.step
    (fun _ transition => oneStep _ _ transition) outcome count firstCounter firstReversed
    secondCounter secondReversed firstForward secondForward source sourcePrefix output

/-- Reads the first payload using any compatible machine step. -/
private def DelimitedCompareTrace.firstPayload
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering)
    (payload tail firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 1 outcome
        (payload ++ tail) (List.replicate payload.length true)
        firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 2 outcome
        tail [] (payload.reverse ++ firstReversed)
        secondCounter secondReversed firstForward secondForward
        (payload.reverse ++ source)
        (List.replicate payload.length true ++ sourcePrefix) output))
      (payload.length + 1) := by
  induction payload generalizing firstReversed source sourcePrefix with
  | nil =>
      simpa only [List.nil_append, List.length_nil, List.replicate_zero, List.reverse_nil,
          zero_add] using
        lift (by simp [delimitedCompareConfiguration])
          (delimitedCompare_firstPayload_finish outcome tail firstReversed secondCounter
            secondReversed firstForward secondForward source sourcePrefix output)
  | cons bit remaining ih =>
      have hfirst := lift (by simp [delimitedCompareConfiguration])
        (delimitedCompare_firstPayload_step outcome bit true (remaining ++ tail)
          (List.replicate remaining.length true) firstReversed secondCounter secondReversed
          firstForward secondForward source sourcePrefix output)
      have hrest := ih (firstReversed := bit :: firstReversed)
        (source := bit :: source) (sourcePrefix := true :: sourcePrefix)
      simpa only [List.cons_append, List.length_cons, List.replicate_succ, List.reverse_cons,
          List.append_assoc, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
          replicate_append_bit_cons] using
        EvalsToInTime.trans chosenStep _ _ _ _ _ hfirst hrest

/-- Reads an incomplete first payload using any compatible machine step. -/
def DelimitedCompareTrace.firstPartialPayload
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering)
    (payload remainingCounter firstReversed
      secondCounter secondReversed firstForward secondForward
      source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 1 outcome
        payload (List.replicate payload.length true ++ remainingCounter)
        firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 1 outcome
        [] remainingCounter (payload.reverse ++ firstReversed)
        secondCounter secondReversed firstForward secondForward
        (payload.reverse ++ source)
        (List.replicate payload.length true ++ sourcePrefix) output))
      payload.length := by
  induction payload generalizing firstReversed source sourcePrefix with
  | nil =>
      simpa only [List.length_nil, List.replicate_zero, List.nil_append, List.reverse_nil] using
        EvalsToInTime.refl chosenStep
          (delimitedCompareConfiguration 1 outcome [] remainingCounter firstReversed
            secondCounter secondReversed firstForward secondForward source sourcePrefix output)
  | cons bit remaining ih =>
      have hfirst := lift (by simp [delimitedCompareConfiguration])
        (delimitedCompare_firstPayload_step outcome bit true remaining
          (List.replicate remaining.length true ++ remainingCounter) firstReversed secondCounter
          secondReversed firstForward secondForward source sourcePrefix output)
      have hrest := ih (firstReversed := bit :: firstReversed)
        (source := bit :: source) (sourcePrefix := true :: sourcePrefix)
      simpa only [List.length_cons, List.replicate_succ, List.cons_append, List.reverse_cons,
          List.append_assoc, List.nil_append, replicate_append_bit_cons] using
        EvalsToInTime.trans chosenStep _ _ _ _ _ hfirst hrest

/-- Internal support shared across GapCVP continuation modules. -/
def delimitedCompareFirstPartialPayloadTrace
    (outcome : EncodedWordOrdering)
    (payload remainingCounter firstReversed
      secondCounter secondReversed firstForward secondForward
      source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 1 outcome
        payload
        (List.replicate payload.length true ++ remainingCounter)
        firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 1 outcome
        [] remainingCounter (payload.reverse ++ firstReversed)
        secondCounter secondReversed firstForward secondForward
        (payload.reverse ++ source)
        (List.replicate payload.length true ++ sourcePrefix) output))
      payload.length := by
  exact DelimitedCompareTrace.firstPartialPayload delimitedPairComparisonMachine.step
    (fun _ transition => oneStep _ _ transition) outcome payload remainingCounter firstReversed
    secondCounter secondReversed firstForward secondForward source sourcePrefix output

/-- Reads the second unary prefix using any compatible machine step. -/
def DelimitedCompareTrace.secondPrefix
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering) (count : ℕ)
    (tail firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 2 outcome
        (List.replicate count true ++ false :: tail)
        firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 3 outcome
        tail firstCounter firstReversed
        (List.replicate count true ++ secondCounter) secondReversed
        firstForward secondForward
        (false :: (List.replicate count true ++ source))
        (List.replicate (count + 1) true ++ sourcePrefix) output))
      (count + 1) := by
  induction count generalizing secondCounter source sourcePrefix with
  | zero =>
      simpa only [List.replicate_zero, List.nil_append, zero_add, List.replicate_one,
          List.cons_append] using
        lift (by simp [delimitedCompareConfiguration])
          (delimitedCompare_secondPrefix_delimiter outcome tail firstCounter firstReversed
            secondCounter secondReversed firstForward secondForward source sourcePrefix output)
  | succ count ih =>
      have hfirst := lift (by simp [delimitedCompareConfiguration])
        (delimitedCompare_secondPrefix_true outcome
          (List.replicate count true ++ false :: tail) firstCounter firstReversed
          secondCounter secondReversed firstForward secondForward source sourcePrefix output)
      have hrest := ih (secondCounter := true :: secondCounter)
        (source := true :: source) (sourcePrefix := true :: sourcePrefix)
      simpa only [List.replicate_succ, List.cons_append, Nat.add_assoc, Nat.reduceAdd,
          replicate_append_bit_cons] using
        EvalsToInTime.trans chosenStep _ _ _ _ _ hfirst hrest

/-- Internal support shared across GapCVP continuation modules. -/
def delimitedCompareSecondPrefixTrace
    (outcome : EncodedWordOrdering) (count : ℕ)
    (tail firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 2 outcome
        (List.replicate count true ++ false :: tail)
        firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 3 outcome
        tail firstCounter firstReversed
        (List.replicate count true ++ secondCounter) secondReversed
        firstForward secondForward
        (false :: (List.replicate count true ++ source))
        (List.replicate (count + 1) true ++ sourcePrefix) output))
      (count + 1) := by
  exact DelimitedCompareTrace.secondPrefix delimitedPairComparisonMachine.step
    (fun _ transition => oneStep _ _ transition) outcome count tail firstCounter firstReversed
    secondCounter secondReversed firstForward secondForward source sourcePrefix output

/-- Detects a missing second delimiter using any compatible machine step. -/
def DelimitedCompareTrace.secondMissingPrefix
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering) (count : ℕ)
    (firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 2 outcome
        (List.replicate count true)
        firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 7 .invalid
        [] firstCounter firstReversed
        (List.replicate count true ++ secondCounter) secondReversed
        firstForward secondForward
        (List.replicate count true ++ source)
        (List.replicate count true ++ sourcePrefix) output))
      (count + 1) := by
  induction count generalizing secondCounter source sourcePrefix with
  | zero =>
      simpa only [List.replicate_zero, List.nil_append, zero_add] using
        lift (by simp [delimitedCompareConfiguration])
          (delimitedCompare_secondPrefix_missing outcome firstCounter firstReversed secondCounter
            secondReversed firstForward secondForward source sourcePrefix output)
  | succ count ih =>
      have hfirst := lift (by simp [delimitedCompareConfiguration])
        (delimitedCompare_secondPrefix_true outcome (List.replicate count true)
          firstCounter firstReversed secondCounter secondReversed firstForward secondForward
          source sourcePrefix output)
      have hrest := ih (secondCounter := true :: secondCounter)
        (source := true :: source) (sourcePrefix := true :: sourcePrefix)
      simpa only [List.replicate_succ, List.cons_append, Nat.add_assoc, Nat.reduceAdd,
          replicate_append_bit_cons] using
        EvalsToInTime.trans chosenStep _ _ _ _ _ hfirst hrest

/-- Internal support shared across GapCVP continuation modules. -/
def delimitedCompareSecondMissingPrefixTrace
    (outcome : EncodedWordOrdering) (count : ℕ)
    (firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 2 outcome
        (List.replicate count true)
        firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 7 .invalid
        [] firstCounter firstReversed
        (List.replicate count true ++ secondCounter) secondReversed
        firstForward secondForward
        (List.replicate count true ++ source)
        (List.replicate count true ++ sourcePrefix) output))
      (count + 1) := by
  exact DelimitedCompareTrace.secondMissingPrefix delimitedPairComparisonMachine.step
    (fun _ transition => oneStep _ _ transition) outcome count firstCounter firstReversed
    secondCounter secondReversed firstForward secondForward source sourcePrefix output

/-- Reads the second payload using any compatible machine step. -/
private def DelimitedCompareTrace.secondPayload
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering)
    (payload tail firstCounter firstReversed secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 3 outcome
        (payload ++ tail) firstCounter firstReversed
        (List.replicate payload.length true) secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 4 outcome
        tail firstCounter firstReversed [] (payload.reverse ++ secondReversed)
        firstForward secondForward (payload.reverse ++ source)
        (List.replicate payload.length true ++ sourcePrefix) output))
      (payload.length + 1) := by
  induction payload generalizing secondReversed source sourcePrefix with
  | nil =>
      simpa only [List.nil_append, List.length_nil, List.replicate_zero, List.reverse_nil,
          zero_add] using
        lift (by simp [delimitedCompareConfiguration])
          (delimitedCompare_secondPayload_finish outcome tail firstCounter firstReversed
            secondReversed firstForward secondForward source sourcePrefix output)
  | cons bit remaining ih =>
      have hfirst := lift (by simp [delimitedCompareConfiguration])
        (delimitedCompare_secondPayload_step outcome bit true (remaining ++ tail)
          firstCounter firstReversed (List.replicate remaining.length true) secondReversed
          firstForward secondForward source sourcePrefix output)
      have hrest := ih (secondReversed := bit :: secondReversed)
        (source := bit :: source) (sourcePrefix := true :: sourcePrefix)
      simpa only [List.cons_append, List.length_cons, List.replicate_succ, List.reverse_cons,
          List.append_assoc, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
          replicate_append_bit_cons] using
        EvalsToInTime.trans chosenStep _ _ _ _ _ hfirst hrest

/-- Reads an incomplete second payload using any compatible machine step. -/
def DelimitedCompareTrace.secondPartialPayload
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering)
    (payload remainingCounter firstCounter firstReversed
      secondReversed firstForward secondForward
      source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 3 outcome
        payload firstCounter firstReversed
        (List.replicate payload.length true ++ remainingCounter)
        secondReversed firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 3 outcome
        [] firstCounter firstReversed remainingCounter
        (payload.reverse ++ secondReversed) firstForward secondForward
        (payload.reverse ++ source)
        (List.replicate payload.length true ++ sourcePrefix) output))
      payload.length := by
  induction payload generalizing secondReversed source sourcePrefix with
  | nil =>
      simpa only [List.length_nil, List.replicate_zero, List.nil_append, List.reverse_nil] using
        EvalsToInTime.refl chosenStep
          (delimitedCompareConfiguration 3 outcome [] firstCounter firstReversed remainingCounter
            secondReversed firstForward secondForward source sourcePrefix output)
  | cons bit remaining ih =>
      have hfirst := lift (by simp [delimitedCompareConfiguration])
        (delimitedCompare_secondPayload_step outcome bit true remaining firstCounter firstReversed
          (List.replicate remaining.length true ++ remainingCounter) secondReversed firstForward
          secondForward source sourcePrefix output)
      have hrest := ih (secondReversed := bit :: secondReversed)
        (source := bit :: source) (sourcePrefix := true :: sourcePrefix)
      simpa only [List.length_cons, List.replicate_succ, List.cons_append, List.reverse_cons,
          List.append_assoc, List.nil_append, replicate_append_bit_cons] using
        EvalsToInTime.trans chosenStep _ _ _ _ _ hfirst hrest

/-- Internal support shared across GapCVP continuation modules. -/
def delimitedCompareSecondPartialPayloadTrace
    (outcome : EncodedWordOrdering)
    (payload remainingCounter firstCounter firstReversed
      secondReversed firstForward secondForward
      source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 3 outcome
        payload firstCounter firstReversed
        (List.replicate payload.length true ++ remainingCounter)
        secondReversed firstForward secondForward
        source sourcePrefix output)
      (some (delimitedCompareConfiguration 3 outcome
        [] firstCounter firstReversed remainingCounter
        (payload.reverse ++ secondReversed)
        firstForward secondForward
        (payload.reverse ++ source)
        (List.replicate payload.length true ++ sourcePrefix) output))
      payload.length := by
  exact DelimitedCompareTrace.secondPartialPayload delimitedPairComparisonMachine.step
    (fun _ transition => oneStep _ _ transition) outcome payload remainingCounter firstCounter
    firstReversed secondReversed firstForward secondForward source sourcePrefix output

/-- Reads the first length-prefixed record using any compatible machine step. -/
def DelimitedCompareTrace.firstRecord
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering)
    (payload tail firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 0 outcome
        (lengthPrefixedWord payload ++ tail)
        [] firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 2 outcome
        tail [] (payload.reverse ++ firstReversed)
        secondCounter secondReversed firstForward secondForward
        ((lengthPrefixedWord payload).reverse ++ source)
        (List.replicate (lengthPrefixedWord payload).length true ++ sourcePrefix) output))
      (2 * payload.length + 2) := by
  have hprefix := DelimitedCompareTrace.firstPrefix chosenStep lift outcome
    payload.length (payload ++ tail) [] firstReversed secondCounter secondReversed
    firstForward secondForward source sourcePrefix output
  simp only [List.append_nil] at hprefix
  have hpayload := DelimitedCompareTrace.firstPayload chosenStep lift outcome
    payload tail firstReversed secondCounter secondReversed firstForward secondForward
    (false :: (List.replicate payload.length true ++ source))
    (List.replicate (payload.length + 1) true ++ sourcePrefix) output
  have hfull := EvalsToInTime.trans chosenStep _ _ _ _ _ hprefix hpayload
  have hsource : payload.reverse ++
      (false :: (List.replicate payload.length true ++ source)) =
      (lengthPrefixedWord payload).reverse ++ source := by
    simp only [lengthPrefixedWord, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.append_assoc, List.cons_append, List.nil_append]
  have hmarkers : List.replicate payload.length true ++
      (List.replicate (payload.length + 1) true ++ sourcePrefix) =
      List.replicate (lengthPrefixedWord payload).length true ++ sourcePrefix := by
    have hlength : payload.length + (payload.length + 1) =
        (lengthPrefixedWord payload).length := by
      simp only [lengthPrefixedWord, List.length_append, List.length_replicate, List.length_cons]
    rw [← List.append_assoc, ← List.replicate_add, hlength]
  rw [hsource, hmarkers] at hfull
  have hcast : EvalsToInTime chosenStep
      (delimitedCompareConfiguration 0 outcome (lengthPrefixedWord payload ++ tail)
        [] firstReversed secondCounter secondReversed firstForward secondForward
        source sourcePrefix output)
      (some (delimitedCompareConfiguration 2 outcome tail []
        (payload.reverse ++ firstReversed) secondCounter secondReversed firstForward secondForward
        ((lengthPrefixedWord payload).reverse ++ source)
        (List.replicate (lengthPrefixedWord payload).length true ++ sourcePrefix) output))
      ((payload.length + 1) + (payload.length + 1)) := by
    simpa only [lengthPrefixedWord, List.append_assoc, List.cons_append] using hfull
  exact rebound hcast (by omega)

/-- Internal support shared across GapCVP continuation modules. -/
def delimitedCompareFirstRecordTrace
    (outcome : EncodedWordOrdering)
    (payload tail firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 0 outcome
        (lengthPrefixedWord payload ++ tail)
        [] firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 2 outcome
        tail [] (payload.reverse ++ firstReversed)
        secondCounter secondReversed firstForward secondForward
        ((lengthPrefixedWord payload).reverse ++ source)
        (List.replicate (lengthPrefixedWord payload).length true ++
          sourcePrefix)
        output))
      (2 * payload.length + 2) := by
  exact DelimitedCompareTrace.firstRecord delimitedPairComparisonMachine.step
    (fun _ transition => oneStep _ _ transition) outcome payload tail firstReversed
    secondCounter secondReversed firstForward secondForward source sourcePrefix output

/-- Reads the second length-prefixed record using any compatible machine step. -/
def DelimitedCompareTrace.secondRecord
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering)
    (payload tail firstCounter firstReversed secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 2 outcome
        (lengthPrefixedWord payload ++ tail)
        firstCounter firstReversed [] secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 4 outcome
        tail firstCounter firstReversed [] (payload.reverse ++ secondReversed)
        firstForward secondForward ((lengthPrefixedWord payload).reverse ++ source)
        (List.replicate (lengthPrefixedWord payload).length true ++ sourcePrefix) output))
      (2 * payload.length + 2) := by
  have hprefix := DelimitedCompareTrace.secondPrefix chosenStep lift outcome
    payload.length (payload ++ tail) firstCounter firstReversed [] secondReversed
    firstForward secondForward source sourcePrefix output
  simp only [List.append_nil] at hprefix
  have hpayload := DelimitedCompareTrace.secondPayload chosenStep lift outcome
    payload tail firstCounter firstReversed secondReversed firstForward secondForward
    (false :: (List.replicate payload.length true ++ source))
    (List.replicate (payload.length + 1) true ++ sourcePrefix) output
  have hfull := EvalsToInTime.trans chosenStep _ _ _ _ _ hprefix hpayload
  have hsource : payload.reverse ++
      (false :: (List.replicate payload.length true ++ source)) =
      (lengthPrefixedWord payload).reverse ++ source := by
    simp only [lengthPrefixedWord, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.append_assoc, List.cons_append, List.nil_append]
  have hmarkers : List.replicate payload.length true ++
      (List.replicate (payload.length + 1) true ++ sourcePrefix) =
      List.replicate (lengthPrefixedWord payload).length true ++ sourcePrefix := by
    have hlength : payload.length + (payload.length + 1) =
        (lengthPrefixedWord payload).length := by
      simp only [lengthPrefixedWord, List.length_append, List.length_replicate, List.length_cons]
    rw [← List.append_assoc, ← List.replicate_add, hlength]
  rw [hsource, hmarkers] at hfull
  have hcast : EvalsToInTime chosenStep
      (delimitedCompareConfiguration 2 outcome (lengthPrefixedWord payload ++ tail)
        firstCounter firstReversed [] secondReversed firstForward secondForward
        source sourcePrefix output)
      (some (delimitedCompareConfiguration 4 outcome tail firstCounter firstReversed []
        (payload.reverse ++ secondReversed) firstForward secondForward
        ((lengthPrefixedWord payload).reverse ++ source)
        (List.replicate (lengthPrefixedWord payload).length true ++ sourcePrefix) output))
      ((payload.length + 1) + (payload.length + 1)) := by
    simpa only [lengthPrefixedWord, List.append_assoc, List.cons_append] using hfull
  exact rebound hcast (by omega)

/-- Reverses the first payload using any compatible machine step. -/
private def DelimitedCompareTrace.reverseFirst
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 4 outcome
        input firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 5 outcome
        input firstCounter [] secondCounter secondReversed
        (firstReversed.reverse ++ firstForward) secondForward source sourcePrefix output))
      (firstReversed.length + 1) := by
  induction firstReversed generalizing firstForward with
  | nil =>
      simpa only [List.reverse_nil, List.nil_append, List.length_nil, zero_add] using
        lift (by simp [delimitedCompareConfiguration])
          (delimitedCompare_reverseFirst_finish outcome input firstCounter secondCounter
            secondReversed firstForward secondForward source sourcePrefix output)
  | cons bit remaining ih =>
      have hfirst := lift (by simp [delimitedCompareConfiguration])
        (delimitedCompare_reverseFirst_step outcome bit input firstCounter remaining
          secondCounter secondReversed firstForward secondForward source sourcePrefix output)
      have hrest := ih (firstForward := bit :: firstForward)
      simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using
        EvalsToInTime.trans chosenStep _ _ _ _ _ hfirst hrest

/-- Reverses the second payload using any compatible machine step. -/
private def DelimitedCompareTrace.reverseSecond
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime chosenStep (delimitedCompareConfiguration 5 outcome
        input firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (delimitedCompareConfiguration 6 outcome
        input firstCounter firstReversed secondCounter []
        firstForward (secondReversed.reverse ++ secondForward) source sourcePrefix output))
      (secondReversed.length + 1) := by
  induction secondReversed generalizing secondForward with
  | nil =>
      simpa only [List.reverse_nil, List.nil_append, List.length_nil, zero_add] using
        lift (by simp [delimitedCompareConfiguration])
          (delimitedCompare_reverseSecond_finish outcome input firstCounter firstReversed
            secondCounter firstForward secondForward source sourcePrefix output)
  | cons bit remaining ih =>
      have hfirst := lift (by simp [delimitedCompareConfiguration])
        (delimitedCompare_reverseSecond_step outcome bit input firstCounter firstReversed
          secondCounter remaining firstForward secondForward source sourcePrefix output)
      have hrest := ih (secondForward := bit :: secondForward)
      simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using
        EvalsToInTime.trans chosenStep _ _ _ _ _ hfirst hrest

private def lexicographicEncodedWordResiduals :
    List Bool → List Bool → List Bool × List Bool
  | [], right => ([], right)
  | bit :: left, [] => (bit :: left, [])
  | false :: left, true :: right =>
      (false :: left, true :: right)
  | true :: left, false :: right =>
      (true :: left, false :: right)
  | false :: left, false :: right =>
      lexicographicEncodedWordResiduals left right
  | true :: left, true :: right =>
      lexicographicEncodedWordResiduals left right

private def delimitedCompare_wordsTrace
    (outcome : EncodedWordOrdering)
    (first second input firstCounter firstReversed
      secondCounter secondReversed source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 6 outcome
        input firstCounter firstReversed secondCounter secondReversed
        first second source sourcePrefix output)
      (some (delimitedCompareConfiguration 7
        (lexicographicEncodedWordOrdering first second)
        input firstCounter firstReversed secondCounter secondReversed
        (lexicographicEncodedWordResiduals first second).1
        (lexicographicEncodedWordResiduals first second).2
        source sourcePrefix output))
      (first.length + 1) := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil =>
          simpa only [FinTM2.step, Fin.isValue, lexicographicEncodedWordOrdering,
              lexicographicEncodedWordResiduals,
              List.length_nil, zero_add] using
              oneStep _ _
                (delimitedCompare_words_bothEmpty outcome input firstCounter firstReversed
                    secondCounter secondReversed source
                  sourcePrefix output)
      | cons bit remaining =>
          simpa only [FinTM2.step, Fin.isValue, lexicographicEncodedWordOrdering,
              lexicographicEncodedWordResiduals,
              List.length_nil, zero_add] using
              oneStep _ _
                (delimitedCompare_words_firstEmpty outcome bit input firstCounter firstReversed
                    secondCounter secondReversed
                  remaining source sourcePrefix output)
  | cons bit remaining ih =>
      cases second with
      | nil =>
          have hstep := oneStep _ _ (delimitedCompare_words_secondEmpty outcome bit
              input firstCounter firstReversed
              secondCounter secondReversed remaining
              source sourcePrefix output)
          have hcast :
              EvalsToInTime delimitedPairComparisonMachine.step
                (delimitedCompareConfiguration 6 outcome
                  input firstCounter firstReversed
                  secondCounter secondReversed
                  (bit :: remaining) [] source sourcePrefix output)
                (some (delimitedCompareConfiguration 7
                  (lexicographicEncodedWordOrdering
                    (bit :: remaining) [])
                  input firstCounter firstReversed
                  secondCounter secondReversed
                  (lexicographicEncodedWordResiduals
                    (bit :: remaining) []).1
                  (lexicographicEncodedWordResiduals
                    (bit :: remaining) []).2
                  source sourcePrefix output))
                1 := by
            simpa only [FinTM2.step, Fin.isValue, lexicographicEncodedWordOrdering,
                lexicographicEncodedWordResiduals] using hstep
          exact rebound hcast (by simp only [List.length_cons, le_add_iff_nonneg_left, zero_le])
      | cons next secondRemaining =>
          cases bit <;> cases next
          · have hfirst := oneStep _ _ (delimitedCompare_words_equalBit outcome false
                input firstCounter firstReversed
                secondCounter secondReversed remaining secondRemaining
                source sourcePrefix output)
            have hrest := ih (second := secondRemaining)
            have hfull := EvalsToInTime.trans delimitedPairComparisonMachine.step
                _ _ _ _ _ hfirst hrest
            simpa only [FinTM2.step, Fin.isValue, lexicographicEncodedWordOrdering,
                lexicographicEncodedWordResiduals,
                List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hfull
          · have hstep := oneStep _ _ (delimitedCompare_words_lessBit outcome
                input firstCounter firstReversed
                secondCounter secondReversed remaining secondRemaining
                source sourcePrefix output)
            have hcast :
                EvalsToInTime delimitedPairComparisonMachine.step
                  (delimitedCompareConfiguration 6 outcome
                    input firstCounter firstReversed
                    secondCounter secondReversed
                    (false :: remaining) (true :: secondRemaining)
                    source sourcePrefix output)
                  (some (delimitedCompareConfiguration 7
                    (lexicographicEncodedWordOrdering
                      (false :: remaining) (true :: secondRemaining))
                    input firstCounter firstReversed
                    secondCounter secondReversed
                    (lexicographicEncodedWordResiduals
                      (false :: remaining) (true :: secondRemaining)).1
                    (lexicographicEncodedWordResiduals
                      (false :: remaining) (true :: secondRemaining)).2
                    source sourcePrefix output))
                  1 := by
              simpa only [FinTM2.step, Fin.isValue, lexicographicEncodedWordOrdering,
                  lexicographicEncodedWordResiduals] using hstep
            exact rebound hcast (by simp only [List.length_cons, le_add_iff_nonneg_left, zero_le])
          · have hstep := oneStep _ _ (delimitedCompare_words_greaterBit outcome
                input firstCounter firstReversed
                secondCounter secondReversed remaining secondRemaining
                source sourcePrefix output)
            have hcast :
                EvalsToInTime delimitedPairComparisonMachine.step
                  (delimitedCompareConfiguration 6 outcome
                    input firstCounter firstReversed
                    secondCounter secondReversed
                    (true :: remaining) (false :: secondRemaining)
                    source sourcePrefix output)
                  (some (delimitedCompareConfiguration 7
                    (lexicographicEncodedWordOrdering
                      (true :: remaining) (false :: secondRemaining))
                    input firstCounter firstReversed
                    secondCounter secondReversed
                    (lexicographicEncodedWordResiduals
                      (true :: remaining) (false :: secondRemaining)).1
                    (lexicographicEncodedWordResiduals
                      (true :: remaining) (false :: secondRemaining)).2
                    source sourcePrefix output))
                  1 := by
              simpa only [FinTM2.step, Fin.isValue, lexicographicEncodedWordOrdering,
                  lexicographicEncodedWordResiduals] using hstep
            exact rebound hcast (by simp only [List.length_cons, le_add_iff_nonneg_left, zero_le])
          · have hfirst := oneStep _ _ (delimitedCompare_words_equalBit outcome true
                input firstCounter firstReversed
                secondCounter secondReversed remaining secondRemaining
                source sourcePrefix output)
            have hrest := ih (second := secondRemaining)
            have hfull := EvalsToInTime.trans delimitedPairComparisonMachine.step
                _ _ _ _ _ hfirst hrest
            simpa only [FinTM2.step, Fin.isValue, lexicographicEncodedWordOrdering,
                lexicographicEncodedWordResiduals,
                List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hfull

private theorem lexicographicEncodedWordResiduals_first_length_le
    (first second : List Bool) :
    (lexicographicEncodedWordResiduals first second).1.length ≤
      first.length := by
  induction first generalizing second with
  | nil => simp only [lexicographicEncodedWordResiduals, List.length_nil, Std.le_refl]
  | cons bit remaining ih =>
      cases second with
      | nil => simp only [lexicographicEncodedWordResiduals, List.length_cons, Std.le_refl]
      | cons next second =>
          cases bit <;> cases next
          · simpa only [lexicographicEncodedWordResiduals, List.length_cons, Nat.succ_eq_add_one]
              using
                Nat.le_trans (ih second) (Nat.le_succ remaining.length)
          · simp only [lexicographicEncodedWordResiduals, List.length_cons, Std.le_refl]
          · simp only [lexicographicEncodedWordResiduals, List.length_cons, Std.le_refl]
          · simpa only [lexicographicEncodedWordResiduals, List.length_cons, Nat.succ_eq_add_one]
              using
                Nat.le_trans (ih second) (Nat.le_succ remaining.length)

private theorem lexicographicEncodedWordResiduals_second_length_le
    (first second : List Bool) :
    (lexicographicEncodedWordResiduals first second).2.length ≤
      second.length := by
  induction first generalizing second with
  | nil => simp only [lexicographicEncodedWordResiduals, Std.le_refl]
  | cons bit remaining ih =>
      cases second with
      | nil => simp only [lexicographicEncodedWordResiduals, List.length_nil, Std.le_refl]
      | cons next second =>
          cases bit <;> cases next
          · simpa only [lexicographicEncodedWordResiduals, List.length_cons, Nat.succ_eq_add_one]
              using
                Nat.le_trans (ih second) (Nat.le_succ second.length)
          · simp only [lexicographicEncodedWordResiduals, List.length_cons, Std.le_refl]
          · simp only [lexicographicEncodedWordResiduals, List.length_cons, Std.le_refl]
          · simpa only [lexicographicEncodedWordResiduals, List.length_cons, Nat.succ_eq_add_one]
              using
                Nat.le_trans (ih second) (Nat.le_succ second.length)

/-- Parses both records, runs a supplied phase-six comparison, and restores the input. -/
def DelimitedCompareTrace.validAssembly
    (chosenStep : delimitedPairComparisonMachine.Cfg →
      Option delimitedPairComparisonMachine.Cfg)
    (lift : DelimitedCompareTrace.NonComparisonStepLift chosenStep)
    (first second suffix firstResidual secondResidual : List Bool)
    (comparisonOutcome : EncodedWordOrdering) (comparisonTime : ℕ)
    (comparisonTrace : EvalsToInTime chosenStep
      (delimitedCompareConfiguration 6 .invalid
        suffix [] [] [] [] first second
        ((lengthPrefixedWord second).reverse ++ (lengthPrefixedWord first).reverse)
        (List.replicate (lengthPrefixedWord second).length true ++
          List.replicate (lengthPrefixedWord first).length true) [])
      (some (delimitedCompareConfiguration 7 comparisonOutcome
        suffix [] [] [] [] firstResidual secondResidual
        ((lengthPrefixedWord second).reverse ++ (lengthPrefixedWord first).reverse)
        (List.replicate (lengthPrefixedWord second).length true ++
          List.replicate (lengthPrefixedWord first).length true) []))
      comparisonTime) :
    EvalsToInTime chosenStep
      (delimitedCompareConfiguration 0 .invalid
        (lengthPrefixedWord first ++ lengthPrefixedWord second ++ suffix)
        [] [] [] [] [] [] [] [] [])
      (some (Turing.haltList delimitedPairComparisonMachine
        (delimitedCompareRestoredWord comparisonOutcome suffix
          ((lengthPrefixedWord second).reverse ++ (lengthPrefixedWord first).reverse)
          (List.replicate (lengthPrefixedWord second).length true ++
            List.replicate (lengthPrefixedWord first).length true) [])))
      ((2 * first.length + 2) + (2 * second.length + 2) +
        (first.length + 1) + (second.length + 1) + comparisonTime +
        (firstResidual.length + secondResidual.length + 3 * suffix.length +
          ((lengthPrefixedWord second).reverse ++
            (lengthPrefixedWord first).reverse).length +
          (List.replicate (lengthPrefixedWord second).length true ++
            List.replicate (lengthPrefixedWord first).length true).length + 5)) := by
  let firstCode := lengthPrefixedWord first
  let secondCode := lengthPrefixedWord second
  let saved := secondCode.reverse ++ firstCode.reverse
  let prefixMarkers :=
    List.replicate secondCode.length true ++ List.replicate firstCode.length true
  have hfirst := DelimitedCompareTrace.firstRecord chosenStep lift .invalid first
    (lengthPrefixedWord second ++ suffix) [] [] [] [] [] [] [] []
  have hfirst' : EvalsToInTime chosenStep
      (delimitedCompareConfiguration 0 .invalid
        (lengthPrefixedWord first ++ lengthPrefixedWord second ++ suffix)
        [] [] [] [] [] [] [] [] [])
      (some (delimitedCompareConfiguration 2 .invalid
        (lengthPrefixedWord second ++ suffix) [] first.reverse [] [] [] []
        firstCode.reverse (List.replicate firstCode.length true) []))
      (2 * first.length + 2) := by
    simpa [firstCode, List.append_assoc] using hfirst
  have hsecond := DelimitedCompareTrace.secondRecord chosenStep lift .invalid second suffix
    [] first.reverse [] [] [] firstCode.reverse (List.replicate firstCode.length true) []
  have hsecond' : EvalsToInTime chosenStep
      (delimitedCompareConfiguration 2 .invalid
        (lengthPrefixedWord second ++ suffix) [] first.reverse [] [] [] []
        firstCode.reverse (List.replicate firstCode.length true) [])
      (some (delimitedCompareConfiguration 4 .invalid
        suffix [] first.reverse [] second.reverse [] [] saved prefixMarkers []))
      (2 * second.length + 2) := by
    simpa [firstCode, secondCode, saved, prefixMarkers] using hsecond
  have hreverseFirst := DelimitedCompareTrace.reverseFirst chosenStep lift .invalid
    suffix [] first.reverse [] second.reverse [] [] saved prefixMarkers []
  have hreverseFirst' : EvalsToInTime chosenStep
      (delimitedCompareConfiguration 4 .invalid
        suffix [] first.reverse [] second.reverse [] [] saved prefixMarkers [])
      (some (delimitedCompareConfiguration 5 .invalid
        suffix [] [] [] second.reverse first [] saved prefixMarkers []))
      (first.length + 1) := by
    simpa using hreverseFirst
  have hreverseSecond := DelimitedCompareTrace.reverseSecond chosenStep lift .invalid
    suffix [] [] [] second.reverse first [] saved prefixMarkers []
  have hreverseSecond' : EvalsToInTime chosenStep
      (delimitedCompareConfiguration 5 .invalid
        suffix [] [] [] second.reverse first [] saved prefixMarkers [])
      (some (delimitedCompareConfiguration 6 .invalid
        suffix [] [] [] [] first second saved prefixMarkers []))
      (second.length + 1) := by
    simpa using hreverseSecond
  have hfinish := DelimitedCompareTrace.finish chosenStep lift comparisonOutcome
    suffix [] [] [] [] firstResidual secondResidual saved prefixMarkers []
  have h01 := EvalsToInTime.trans chosenStep _ _ _ _ _ hfirst' hsecond'
  have h012 := EvalsToInTime.trans chosenStep _ _ _ _ _ h01 hreverseFirst'
  have h0123 := EvalsToInTime.trans chosenStep _ _ _ _ _ h012 hreverseSecond'
  have h01234 := EvalsToInTime.trans chosenStep _ _ _ _ _ h0123 comparisonTrace
  have hfull := EvalsToInTime.trans chosenStep _ _ _ _ _ h01234 hfinish
  apply rebound hfull
  simp only [firstCode, secondCode, saved, prefixMarkers, List.length_nil, zero_add,
    List.length_append, List.length_reverse, List.length_replicate]
  omega

/-- Internal support shared across GapCVP continuation modules. -/
def delimitedCompareValidTrace
    (first second suffix : List Bool) :
    EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 0 .invalid
        (lengthPrefixedWord first ++
          lengthPrefixedWord second ++ suffix)
        [] [] [] [] [] [] [] [] [])
      (some (Turing.haltList delimitedPairComparisonMachine
        (sourcePreservingDelimitedPairComparisonWord
          (lengthPrefixedWord first ++
            lengthPrefixedWord second ++ suffix))))
      (24 *
        ((lengthPrefixedWord first ++
          lengthPrefixedWord second ++ suffix).length + 1) + 24) := by
  let firstCode := lengthPrefixedWord first
  let secondCode := lengthPrefixedWord second
  let saved := secondCode.reverse ++ firstCode.reverse
  let prefixMarkers := List.replicate secondCode.length true ++
    List.replicate firstCode.length true
  have hcompare := delimitedCompare_wordsTrace .invalid
    first second suffix [] [] [] [] saved prefixMarkers []
  have hassembly := DelimitedCompareTrace.validAssembly
    delimitedPairComparisonMachine.step (fun _ transition => oneStep _ _ transition)
    first second suffix
    (lexicographicEncodedWordResiduals first second).1
    (lexicographicEncodedWordResiduals first second).2
    (lexicographicEncodedWordOrdering first second) (first.length + 1)
    (by simpa only [firstCode, secondCode, saved, prefixMarkers] using hcompare)
  have hprefixLength :
      suffix.length + prefixMarkers.length =
        (lengthPrefixedWord first ++
          lengthPrefixedWord second ++ suffix).length := by
    simp only [prefixMarkers, firstCode, secondCode,
      List.length_append, List.length_replicate,
      lengthPrefixedWord_length]
    omega
  have hrestored :
      delimitedCompareRestoredWord
        (lexicographicEncodedWordOrdering first second)
        suffix saved prefixMarkers [] =
      sourcePreservingDelimitedPairComparisonWord
        (lengthPrefixedWord first ++
          lengthPrefixedWord second ++ suffix) := by
    simp only [delimitedCompareRestoredWord,
      sourcePreservingDelimitedPairComparisonWord,
      delimitedPairWordOrdering_valid, List.append_nil]
    rw [hprefixLength]
    simp [saved, firstCode, secondCode, lengthPrefixedWord,
      List.reverse_append, List.append_assoc]
  rw [← hrestored]
  apply rebound hassembly
  have hfirstResidual :=
    lexicographicEncodedWordResiduals_first_length_le first second
  have hsecondResidual :=
    lexicographicEncodedWordResiduals_second_length_le first second
  simp only [List.length_append, List.length_reverse, List.length_replicate,
    lengthPrefixedWord_length]
  omega

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem delimitedPairWordOrdering_missingFirst
    (count : ℕ) :
    delimitedPairWordOrdering (List.replicate count true) = .invalid := by
  simp only [delimitedPairWordOrdering, readLengthPrefixedWord, readUnaryPrefix_missing]

/-- Internal support shared across GapCVP continuation modules. -/
theorem delimitedPairWordOrdering_shortFirst
    (count : ℕ) (payload : List Bool)
    (hshort : payload.length < count) :
    delimitedPairWordOrdering
      (List.replicate count true ++ false :: payload) = .invalid := by
  have hinsufficient : ¬ count ≤ payload.length := by
    omega
  simp only [delimitedPairWordOrdering, readLengthPrefixedWord, readUnaryPrefix_replicate,
      hinsufficient,
      ↓reduceIte]

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem delimitedPairWordOrdering_missingSecond
    (first : List Bool) (count : ℕ) :
    delimitedPairWordOrdering
      (lengthPrefixedWord first ++
        List.replicate count true) = .invalid := by
  unfold delimitedPairWordOrdering
  rw [readLengthPrefixedWord_append first
    (List.replicate count true)]
  simp only [readLengthPrefixedWord, readUnaryPrefix_missing]

/-- Internal support shared across GapCVP continuation modules. -/
theorem delimitedPairWordOrdering_shortSecond
    (first : List Bool) (count : ℕ) (payload : List Bool)
    (hshort : payload.length < count) :
    delimitedPairWordOrdering
      (lengthPrefixedWord first ++
        (List.replicate count true ++ false :: payload)) = .invalid := by
  unfold delimitedPairWordOrdering
  rw [readLengthPrefixedWord_append first
    (List.replicate count true ++ false :: payload)]
  have hinsufficient : ¬ count ≤ payload.length := by
    omega
  simp only [readLengthPrefixedWord, readUnaryPrefix_replicate, hinsufficient, ↓reduceIte]

end CNFEncodedClauseSort

end GapCVP

end
