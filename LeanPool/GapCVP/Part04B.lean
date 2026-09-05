/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part04A

/-! # GapCVP proof, part 04, continuation 02 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFNaturalOrderCertifiedComparator

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder

open GapCVP.CNFSortingDedup GapCVP.CNFEncodedClauseSort GapCVP.CNFNaturalOrderComparator

open GapCVP.CNFNaturalOrderTotalComparator

private def certifiedNatural_liftStep
    {first next : delimitedNaturalComparisonMachine.Cfg}
    (hphase : first.l ≠ some (6 : Fin 12))
    (hstep : delimitedPairComparisonMachine.step first = some next) :
    EvalsToInTime delimitedNaturalComparisonMachine.step first (some next) 1 :=
  oneStep first next
    ((certifiedNatural_step_eq_old first hphase).trans hstep)





private def certifiedNatural_finishTrace
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedNaturalComparisonMachine.step
      (naturalCompareConfiguration 7 outcome
        input firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (Turing.haltList delimitedNaturalComparisonMachine
        (delimitedCompareRestoredWord outcome
          input source sourcePrefix output)))
      (firstCounter.length + firstReversed.length +
        secondCounter.length + secondReversed.length +
        firstForward.length + secondForward.length +
        3 * input.length + source.length + sourcePrefix.length + 5) := by
  change EvalsToInTime delimitedNaturalComparisonMachine.step
    (delimitedCompareConfiguration 7 outcome input firstCounter firstReversed
      secondCounter secondReversed firstForward secondForward source sourcePrefix output)
    (some (Turing.haltList delimitedPairComparisonMachine
      (delimitedCompareRestoredWord outcome input source sourcePrefix output)))
    (firstCounter.length + firstReversed.length +
      secondCounter.length + secondReversed.length +
      firstForward.length + secondForward.length +
      3 * input.length + source.length + sourcePrefix.length + 5)
  exact DelimitedCompareTrace.finish delimitedNaturalComparisonMachine.step
    certifiedNatural_liftStep outcome input firstCounter firstReversed secondCounter
    secondReversed firstForward secondForward source sourcePrefix output

private def certifiedNatural_firstPrefixTrace
    (outcome : EncodedWordOrdering) (count : ℕ)
    (tail firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedNaturalComparisonMachine.step (naturalCompareConfiguration 0 outcome
        (List.replicate count true ++ false :: tail)
        firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (naturalCompareConfiguration 1 outcome
        tail (List.replicate count true ++ firstCounter)
        firstReversed secondCounter secondReversed
        firstForward secondForward
        (false :: (List.replicate count true ++ source))
        (List.replicate (count + 1) true ++ sourcePrefix) output))
      (count + 1) := by
  exact DelimitedCompareTrace.firstPrefix delimitedNaturalComparisonMachine.step
    certifiedNatural_liftStep outcome count tail firstCounter firstReversed secondCounter
    secondReversed firstForward secondForward source sourcePrefix output

private def certifiedNatural_firstMissingPrefixTrace
    (outcome : EncodedWordOrdering) (count : ℕ)
    (firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedNaturalComparisonMachine.step (naturalCompareConfiguration 0 outcome
        (List.replicate count true)
        firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (naturalCompareConfiguration 7 .invalid
        [] (List.replicate count true ++ firstCounter)
        firstReversed secondCounter secondReversed
        firstForward secondForward
        (List.replicate count true ++ source)
        (List.replicate count true ++ sourcePrefix) output))
      (count + 1) := by
  exact DelimitedCompareTrace.firstMissingPrefix delimitedNaturalComparisonMachine.step
    certifiedNatural_liftStep outcome count firstCounter firstReversed secondCounter secondReversed
    firstForward secondForward source sourcePrefix output

private def certifiedNatural_firstPartialPayloadTrace
    (outcome : EncodedWordOrdering)
    (payload remainingCounter firstReversed
      secondCounter secondReversed firstForward secondForward
      source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedNaturalComparisonMachine.step (naturalCompareConfiguration 1 outcome
        payload (List.replicate payload.length true ++ remainingCounter)
        firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (naturalCompareConfiguration 1 outcome
        [] remainingCounter (payload.reverse ++ firstReversed)
        secondCounter secondReversed firstForward secondForward
        (payload.reverse ++ source)
        (List.replicate payload.length true ++ sourcePrefix) output))
      payload.length := by
  exact DelimitedCompareTrace.firstPartialPayload delimitedNaturalComparisonMachine.step
    certifiedNatural_liftStep outcome payload remainingCounter firstReversed secondCounter
    secondReversed firstForward secondForward source sourcePrefix output

private def certifiedNatural_secondPrefixTrace
    (outcome : EncodedWordOrdering) (count : ℕ)
    (tail firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedNaturalComparisonMachine.step (naturalCompareConfiguration 2 outcome
        (List.replicate count true ++ false :: tail)
        firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (naturalCompareConfiguration 3 outcome
        tail firstCounter firstReversed
        (List.replicate count true ++ secondCounter) secondReversed
        firstForward secondForward
        (false :: (List.replicate count true ++ source))
        (List.replicate (count + 1) true ++ sourcePrefix) output))
      (count + 1) := by
  exact DelimitedCompareTrace.secondPrefix delimitedNaturalComparisonMachine.step
    certifiedNatural_liftStep outcome count tail firstCounter firstReversed secondCounter
    secondReversed firstForward secondForward source sourcePrefix output

private def certifiedNatural_secondMissingPrefixTrace
    (outcome : EncodedWordOrdering) (count : ℕ)
    (firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedNaturalComparisonMachine.step (naturalCompareConfiguration 2 outcome
        (List.replicate count true)
        firstCounter firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (naturalCompareConfiguration 7 .invalid
        [] firstCounter firstReversed
        (List.replicate count true ++ secondCounter) secondReversed
        firstForward secondForward
        (List.replicate count true ++ source)
        (List.replicate count true ++ sourcePrefix) output))
      (count + 1) := by
  exact DelimitedCompareTrace.secondMissingPrefix delimitedNaturalComparisonMachine.step
    certifiedNatural_liftStep outcome count firstCounter firstReversed secondCounter secondReversed
    firstForward secondForward source sourcePrefix output

private def certifiedNatural_secondPartialPayloadTrace
    (outcome : EncodedWordOrdering)
    (payload remainingCounter firstCounter firstReversed
      secondReversed firstForward secondForward
      source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedNaturalComparisonMachine.step (naturalCompareConfiguration 3 outcome
        payload firstCounter firstReversed
        (List.replicate payload.length true ++ remainingCounter)
        secondReversed firstForward secondForward
        source sourcePrefix output)
      (some (naturalCompareConfiguration 3 outcome
        [] firstCounter firstReversed remainingCounter
        (payload.reverse ++ secondReversed)
        firstForward secondForward
        (payload.reverse ++ source)
        (List.replicate payload.length true ++ sourcePrefix) output))
      payload.length := by
  exact DelimitedCompareTrace.secondPartialPayload delimitedNaturalComparisonMachine.step
    certifiedNatural_liftStep outcome payload remainingCounter firstCounter firstReversed
    secondReversed firstForward secondForward source sourcePrefix output

private def certifiedNatural_firstRecordTrace
    (outcome : EncodedWordOrdering)
    (payload tail firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    EvalsToInTime delimitedNaturalComparisonMachine.step (naturalCompareConfiguration 0 outcome
        (lengthPrefixedWord payload ++ tail)
        [] firstReversed secondCounter secondReversed
        firstForward secondForward source sourcePrefix output)
      (some (naturalCompareConfiguration 2 outcome
        tail [] (payload.reverse ++ firstReversed)
        secondCounter secondReversed firstForward secondForward
        ((lengthPrefixedWord payload).reverse ++ source)
        (List.replicate (lengthPrefixedWord payload).length true ++
          sourcePrefix) output))
      (2 * payload.length + 2) := by
  exact DelimitedCompareTrace.firstRecord delimitedNaturalComparisonMachine.step
    certifiedNatural_liftStep outcome payload tail firstReversed secondCounter secondReversed
    firstForward secondForward source sourcePrefix output


private def certifiedNatural_validTrace
    (first second suffix : List Bool) :
    EvalsToInTime delimitedNaturalComparisonMachine.step (naturalCompareConfiguration 0 .invalid
        (lengthPrefixedWord first ++
          lengthPrefixedWord second ++ suffix)
        [] [] [] [] [] [] [] [] [])
      (some (Turing.haltList delimitedNaturalComparisonMachine
        (sourcePreservingDelimitedNaturalComparisonWord
          (lengthPrefixedWord first ++
            lengthPrefixedWord second ++ suffix))))
      (24 *
        ((lengthPrefixedWord first ++
          lengthPrefixedWord second ++ suffix).length + 1) + 24) := by
  change EvalsToInTime delimitedNaturalComparisonMachine.step
    (delimitedCompareConfiguration 0 .invalid
      (lengthPrefixedWord first ++ lengthPrefixedWord second ++ suffix)
      [] [] [] [] [] [] [] [] [])
    (some (Turing.haltList delimitedPairComparisonMachine
      (sourcePreservingDelimitedNaturalComparisonWord
        (lengthPrefixedWord first ++ lengthPrefixedWord second ++ suffix))))
    (24 * ((lengthPrefixedWord first ++
      lengthPrefixedWord second ++ suffix).length + 1) + 24)
  let firstCode := lengthPrefixedWord first
  let secondCode := lengthPrefixedWord second
  let saved := secondCode.reverse ++ firstCode.reverse
  let prefixMarkers := List.replicate secondCode.length true ++
    List.replicate firstCode.length true
  have hcompare := naturalCompareWordsTraceInitial
    first second suffix [] [] [] [] saved prefixMarkers []
  change @EvalsToInTime delimitedPairComparisonMachine.Cfg
      delimitedNaturalComparisonMachine.step
      (delimitedCompareConfiguration 6 .invalid
        suffix [] [] [] [] first second saved prefixMarkers [])
      (some (delimitedCompareConfiguration 7
        (littleEndianNaturalOrdering first second)
        suffix [] [] [] [] [] [] saved prefixMarkers []))
      (first.length + second.length + 1) at hcompare
  have hassembly := DelimitedCompareTrace.validAssembly
    delimitedNaturalComparisonMachine.step certifiedNatural_liftStep
    first second suffix [] [] (littleEndianNaturalOrdering first second)
    (first.length + second.length + 1)
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
        (littleEndianNaturalOrdering first second)
        suffix saved prefixMarkers [] =
      sourcePreservingDelimitedNaturalComparisonWord
        (lengthPrefixedWord first ++
          lengthPrefixedWord second ++ suffix) := by
    simp only [delimitedCompareRestoredWord,
      sourcePreservingDelimitedNaturalComparisonWord,
      delimitedNaturalPairOrdering_valid, List.append_nil]
    rw [hprefixLength]
    simp [saved, firstCode, secondCode, lengthPrefixedWord,
      List.reverse_append, List.append_assoc]
  rw [← hrestored]
  apply rebound hassembly
  simp only [List.length_append, List.length_reverse, List.length_replicate,
    List.length_nil, lengthPrefixedWord_length]
  omega

private def certifiedNatural_missingFirstTrace (count : ℕ) :
    EvalsToInTime delimitedNaturalComparisonMachine.step (naturalCompareConfiguration 0 .invalid
        (List.replicate count true) [] [] [] [] [] [] [] [] [])
      (some (Turing.haltList delimitedNaturalComparisonMachine
        (sourcePreservingDelimitedNaturalComparisonWord
          (List.replicate count true))))
      (24 * ((List.replicate count true).length + 1) + 24) := by
  have hscan :
      EvalsToInTime delimitedNaturalComparisonMachine.step
        (naturalCompareConfiguration 0 .invalid
          (List.replicate count true) [] [] [] [] [] [] [] [] [])
        (some (naturalCompareConfiguration 7 .invalid
          [] (List.replicate count true) [] [] [] [] []
          (List.replicate count true)
          (List.replicate count true) []))
        (count + 1) := by
    simpa only [FinTM2.step, Fin.isValue, List.append_nil] using
        certifiedNatural_firstMissingPrefixTrace .invalid count [] [] [] [] [] [] [] [] []
  have hfinish := certifiedNatural_finishTrace .invalid
    [] (List.replicate count true) [] [] [] [] []
    (List.replicate count true) (List.replicate count true) []
  have hrestored :
      delimitedCompareRestoredWord .invalid []
        (List.replicate count true) (List.replicate count true) [] =
      sourcePreservingDelimitedNaturalComparisonWord
        (List.replicate count true) := by
    simp only [delimitedCompareRestoredWord, List.length_nil, List.length_replicate, zero_add,
        List.reverse_replicate, List.append_nil, sourcePreservingDelimitedNaturalComparisonWord,
            lengthPrefixedWord,
        delimitedNaturalPairOrdering_missingFirst, List.append_assoc, List.cons_append]
  rw [hrestored] at hfinish
  have hfull := EvalsToInTime.trans delimitedNaturalComparisonMachine.step _ _ _ _ _ hscan hfinish
  apply rebound hfull
  simp only [List.length_replicate, List.length_nil]
  omega

private def certifiedNatural_truncatedFirstTrace
    (count : ℕ) (payload : List Bool)
    (hshort : payload.length < count) :
    EvalsToInTime delimitedNaturalComparisonMachine.step (naturalCompareConfiguration 0 .invalid
        (List.replicate count true ++ false :: payload)
        [] [] [] [] [] [] [] [] [])
      (some (Turing.haltList delimitedNaturalComparisonMachine
        (sourcePreservingDelimitedNaturalComparisonWord
          (List.replicate count true ++ false :: payload))))
      (24 *
        ((List.replicate count true ++ false :: payload).length + 1) + 24) := by
  let extra := count - payload.length - 1
  have hcount : count = payload.length + extra + 1 := by
    dsimp [extra]
    omega
  have hcounter :
      List.replicate count true =
        List.replicate payload.length true ++
          List.replicate (extra + 1) true := by
    have hsplit : count = payload.length + (extra + 1) := by omega
    rw [hsplit, List.replicate_add]
  let saved := payload.reverse ++ false :: List.replicate count true
  let prefixMarkers :=
    List.replicate payload.length true ++
      List.replicate (count + 1) true
  have hprefix :
      EvalsToInTime delimitedNaturalComparisonMachine.step
        (naturalCompareConfiguration 0 .invalid
          (List.replicate count true ++ false :: payload)
          [] [] [] [] [] [] [] [] [])
        (some (naturalCompareConfiguration 1 .invalid
          payload (List.replicate count true) [] [] [] [] []
          (false :: List.replicate count true)
          (List.replicate (count + 1) true) []))
        (count + 1) := by
    simpa only [FinTM2.step, Fin.isValue, List.append_nil] using
        certifiedNatural_firstPrefixTrace .invalid count payload [] [] [] [] [] [] [] [] []
  have hpartial :
      EvalsToInTime delimitedNaturalComparisonMachine.step
        (naturalCompareConfiguration 1 .invalid
          payload (List.replicate count true) [] [] [] [] []
          (false :: List.replicate count true)
          (List.replicate (count + 1) true) [])
        (some (naturalCompareConfiguration 1 .invalid
          [] (true :: List.replicate extra true)
          payload.reverse [] [] [] [] saved prefixMarkers []))
        payload.length := by
    have hremaining :
        List.replicate (extra + 1) true =
          true :: List.replicate extra true := by
      simp only [List.replicate_succ]
    have hraw := certifiedNatural_firstPartialPayloadTrace
      .invalid payload (List.replicate (extra + 1) true)
      [] [] [] [] [] (false :: List.replicate count true)
      (List.replicate (count + 1) true) []
    rw [← hcounter, hremaining] at hraw
    simpa only [saved, prefixMarkers, List.append_nil] using hraw
  have hmissing := certifiedNatural_liftStep
    (by simp only [delimitedCompareConfiguration, Fin.isValue, ne_eq, Option.some.injEq,
        Fin.reduceEq,
            not_false_eq_true])
    (delimitedCompare_firstPayload_missing .invalid true
      (List.replicate extra true) payload.reverse
      [] [] [] [] saved prefixMarkers [])
  have hfinish := certifiedNatural_finishTrace .invalid
    [] (List.replicate extra true) payload.reverse
    [] [] [] [] saved prefixMarkers []
  have hprefixLength :
      prefixMarkers.length =
        (List.replicate count true ++ false :: payload).length := by
    simp only [prefixMarkers, List.length_append,
      List.length_replicate, List.length_cons]
    omega
  have hordering :=
    delimitedNaturalPairOrdering_shortFirst count payload hshort
  have hrestored :
      delimitedCompareRestoredWord .invalid []
        saved prefixMarkers [] =
      sourcePreservingDelimitedNaturalComparisonWord
        (List.replicate count true ++ false :: payload) := by
    simp only [delimitedCompareRestoredWord,
      sourcePreservingDelimitedNaturalComparisonWord,
      hordering, List.length_nil, Nat.zero_add, List.append_nil]
    rw [hprefixLength]
    simp only [List.length_append, List.length_replicate, List.length_cons, List.reverse_append,
        List.reverse_cons, List.reverse_replicate, List.reverse_reverse, List.append_assoc,
            List.cons_append,
        List.nil_append, lengthPrefixedWord, saved]
  rw [hrestored] at hfinish
  have h01 := EvalsToInTime.trans delimitedNaturalComparisonMachine.step _ _ _ _ _ hprefix hpartial
  have h012 := EvalsToInTime.trans delimitedNaturalComparisonMachine.step _ _ _ _ _ h01 hmissing
  have hfull := EvalsToInTime.trans delimitedNaturalComparisonMachine.step _ _ _ _ _ h012 hfinish
  apply rebound hfull
  simp only [saved, prefixMarkers, List.length_append,
    List.length_replicate, List.length_reverse,
    List.length_cons, List.length_nil]
  omega

private def certifiedNatural_missingSecondTrace
    (first : List Bool) (count : ℕ) :
    EvalsToInTime delimitedNaturalComparisonMachine.step (naturalCompareConfiguration 0 .invalid
        (lengthPrefixedWord first ++ List.replicate count true)
        [] [] [] [] [] [] [] [] [])
      (some (Turing.haltList delimitedNaturalComparisonMachine
        (sourcePreservingDelimitedNaturalComparisonWord
          (lengthPrefixedWord first ++ List.replicate count true))))
      (24 *
        ((lengthPrefixedWord first ++ List.replicate count true).length +
          1) + 24) := by
  let firstCode := lengthPrefixedWord first
  let saved := List.replicate count true ++ firstCode.reverse
  let prefixMarkers :=
    List.replicate count true ++
      List.replicate firstCode.length true
  have hfirst :
      EvalsToInTime delimitedNaturalComparisonMachine.step
        (naturalCompareConfiguration 0 .invalid
          (lengthPrefixedWord first ++ List.replicate count true)
          [] [] [] [] [] [] [] [] [])
        (some (naturalCompareConfiguration 2 .invalid
          (List.replicate count true)
          [] first.reverse [] [] [] [] firstCode.reverse
          (List.replicate firstCode.length true) []))
        (2 * first.length + 2) := by
    simpa [firstCode] using certifiedNatural_firstRecordTrace
      .invalid first (List.replicate count true)
      [] [] [] [] [] [] [] []
  have hmissing :
      EvalsToInTime delimitedNaturalComparisonMachine.step
        (naturalCompareConfiguration 2 .invalid
          (List.replicate count true)
          [] first.reverse [] [] [] [] firstCode.reverse
          (List.replicate firstCode.length true) [])
        (some (naturalCompareConfiguration 7 .invalid
          [] [] first.reverse (List.replicate count true)
          [] [] [] saved prefixMarkers []))
        (count + 1) := by
    simpa [saved, prefixMarkers] using
      certifiedNatural_secondMissingPrefixTrace .invalid count
        [] first.reverse [] [] [] []
        firstCode.reverse (List.replicate firstCode.length true) []
  have hfinish := certifiedNatural_finishTrace .invalid
    [] [] first.reverse (List.replicate count true)
    [] [] [] saved prefixMarkers []
  have hprefixLength :
      prefixMarkers.length =
        (lengthPrefixedWord first ++ List.replicate count true).length := by
    simp only [prefixMarkers, firstCode,
      List.length_append, List.length_replicate]
    omega
  have hrestored :
      delimitedCompareRestoredWord .invalid []
        saved prefixMarkers [] =
      sourcePreservingDelimitedNaturalComparisonWord
        (lengthPrefixedWord first ++ List.replicate count true) := by
    simp only [delimitedCompareRestoredWord,
      sourcePreservingDelimitedNaturalComparisonWord,
      delimitedNaturalPairOrdering_missingSecond,
      List.length_nil, Nat.zero_add, List.append_nil]
    rw [hprefixLength]
    simp [saved, firstCode, lengthPrefixedWord,
      List.reverse_append, List.append_assoc]
  rw [hrestored] at hfinish
  have hfirstTwo := EvalsToInTime.trans
    delimitedNaturalComparisonMachine.step _ _ _ _ _ hfirst hmissing
  have hfull := EvalsToInTime.trans
    delimitedNaturalComparisonMachine.step _ _ _ _ _ hfirstTwo hfinish
  apply rebound hfull
  simp only [saved, prefixMarkers, firstCode,
    List.length_append, List.length_replicate,
    List.length_reverse, List.length_nil,
    lengthPrefixedWord_length]
  omega

private def certifiedNatural_truncatedSecondTrace
    (first : List Bool) (count : ℕ) (payload : List Bool)
    (hshort : payload.length < count) :
    EvalsToInTime delimitedNaturalComparisonMachine.step (naturalCompareConfiguration 0 .invalid
        (lengthPrefixedWord first ++
          (List.replicate count true ++ false :: payload))
        [] [] [] [] [] [] [] [] [])
      (some (Turing.haltList delimitedNaturalComparisonMachine
        (sourcePreservingDelimitedNaturalComparisonWord
          (lengthPrefixedWord first ++
            (List.replicate count true ++ false :: payload)))))
      (24 *
        ((lengthPrefixedWord first ++
          (List.replicate count true ++ false :: payload)).length + 1) +
        24) := by
  let extra := count - payload.length - 1
  have hcount : count = payload.length + extra + 1 := by
    dsimp [extra]
    omega
  have hcounter :
      List.replicate count true =
        List.replicate payload.length true ++
          List.replicate (extra + 1) true := by
    have hsplit : count = payload.length + (extra + 1) := by omega
    rw [hsplit, List.replicate_add]
  let firstCode := lengthPrefixedWord first
  let saved := payload.reverse ++
    false :: (List.replicate count true ++ firstCode.reverse)
  let prefixMarkers :=
    List.replicate payload.length true ++
      (List.replicate (count + 1) true ++
        List.replicate firstCode.length true)
  have hfirst :
      EvalsToInTime delimitedNaturalComparisonMachine.step
        (naturalCompareConfiguration 0 .invalid
          (lengthPrefixedWord first ++
            (List.replicate count true ++ false :: payload))
          [] [] [] [] [] [] [] [] [])
        (some (naturalCompareConfiguration 2 .invalid
          (List.replicate count true ++ false :: payload)
          [] first.reverse [] [] [] [] firstCode.reverse
          (List.replicate firstCode.length true) []))
        (2 * first.length + 2) := by
    simpa [firstCode] using certifiedNatural_firstRecordTrace
      .invalid first (List.replicate count true ++ false :: payload)
      [] [] [] [] [] [] [] []
  have hprefix :
      EvalsToInTime delimitedNaturalComparisonMachine.step
        (naturalCompareConfiguration 2 .invalid
          (List.replicate count true ++ false :: payload)
          [] first.reverse [] [] [] [] firstCode.reverse
          (List.replicate firstCode.length true) [])
        (some (naturalCompareConfiguration 3 .invalid
          payload [] first.reverse
          (List.replicate count true) [] [] []
          (false :: (List.replicate count true ++ firstCode.reverse))
          (List.replicate (count + 1) true ++
            List.replicate firstCode.length true) []))
        (count + 1) := by
    simpa using certifiedNatural_secondPrefixTrace .invalid count
      payload [] first.reverse [] [] [] []
      firstCode.reverse (List.replicate firstCode.length true) []
  have hpartial :
      EvalsToInTime delimitedNaturalComparisonMachine.step
        (naturalCompareConfiguration 3 .invalid
          payload [] first.reverse
          (List.replicate count true) [] [] []
          (false :: (List.replicate count true ++ firstCode.reverse))
          (List.replicate (count + 1) true ++
            List.replicate firstCode.length true) [])
        (some (naturalCompareConfiguration 3 .invalid
          [] [] first.reverse (true :: List.replicate extra true)
          payload.reverse [] [] saved prefixMarkers []))
        payload.length := by
    have hremaining :
        List.replicate (extra + 1) true =
          true :: List.replicate extra true := by
      simp [List.replicate_succ]
    have hraw := certifiedNatural_secondPartialPayloadTrace
      .invalid payload (List.replicate (extra + 1) true)
      [] first.reverse [] [] []
      (false :: (List.replicate count true ++ firstCode.reverse))
      (List.replicate (count + 1) true ++
        List.replicate firstCode.length true) []
    rw [← hcounter, hremaining] at hraw
    simpa only [saved, prefixMarkers, List.append_nil] using hraw
  have hmissing := certifiedNatural_liftStep
    (by simp [delimitedCompareConfiguration])
    (delimitedCompare_secondPayload_missing .invalid true
      [] first.reverse (List.replicate extra true)
      payload.reverse [] [] saved prefixMarkers [])
  have hfinish := certifiedNatural_finishTrace .invalid
    [] [] first.reverse (List.replicate extra true)
    payload.reverse [] [] saved prefixMarkers []
  have hprefixLength :
      prefixMarkers.length =
        (lengthPrefixedWord first ++
          (List.replicate count true ++ false :: payload)).length := by
    simp only [prefixMarkers, firstCode, List.length_append,
      List.length_replicate, List.length_cons,
      lengthPrefixedWord_length]
    omega
  have hordering :=
    delimitedNaturalPairOrdering_shortSecond first count payload hshort
  have hrestored :
      delimitedCompareRestoredWord .invalid []
        saved prefixMarkers [] =
      sourcePreservingDelimitedNaturalComparisonWord
        (lengthPrefixedWord first ++
          (List.replicate count true ++ false :: payload)) := by
    simp only [delimitedCompareRestoredWord,
      sourcePreservingDelimitedNaturalComparisonWord,
      hordering, List.length_nil, Nat.zero_add, List.append_nil]
    rw [hprefixLength]
    simp [saved, firstCode, lengthPrefixedWord,
      List.reverse_append, List.append_assoc]
  rw [hrestored] at hfinish
  have h01 := EvalsToInTime.trans delimitedNaturalComparisonMachine.step _ _ _ _ _ hfirst hprefix
  have h012 := EvalsToInTime.trans delimitedNaturalComparisonMachine.step _ _ _ _ _ h01 hpartial
  have h0123 := EvalsToInTime.trans delimitedNaturalComparisonMachine.step _ _ _ _ _ h012 hmissing
  have hfull := EvalsToInTime.trans delimitedNaturalComparisonMachine.step _ _ _ _ _ h0123 hfinish
  apply rebound hfull
  simp only [saved, prefixMarkers, firstCode,
    List.length_append, List.length_replicate,
    List.length_reverse, List.length_cons, List.length_nil,
    lengthPrefixedWord_length]
  omega

private def certifiedNatural_totalTrace (input : List Bool) :
    EvalsToInTime delimitedNaturalComparisonMachine.step (naturalCompareConfiguration 0 .invalid
        input [] [] [] [] [] [] [] [] [])
      (some (Turing.haltList delimitedNaturalComparisonMachine
        (sourcePreservingDelimitedNaturalComparisonWord input)))
      (24 * (input.length + 1) + 24) := by
  cases unaryInputSplit input with
  | inl witness =>
      obtain ⟨count, hinput⟩ := witness
      subst input
      exact certifiedNatural_missingFirstTrace count
  | inr witness =>
      obtain ⟨count, tail, hinput⟩ := witness
      subst input
      by_cases hlength : count ≤ tail.length
      · let first := tail.take count
        let rest := tail.drop count
        have hfirstRecord :
            List.replicate count true ++ false :: tail =
              lengthPrefixedWord first ++ rest := by
          simpa only using validInput_reconstruct count tail hlength
        rw [hfirstRecord]
        cases unaryInputSplit rest with
        | inl secondWitness =>
            obtain ⟨secondCount, hsecond⟩ := secondWitness
            rw [hsecond]
            exact certifiedNatural_missingSecondTrace first secondCount
        | inr secondWitness =>
            obtain ⟨secondCount, secondTail, hsecond⟩ := secondWitness
            rw [hsecond]
            by_cases hsecondLength : secondCount ≤ secondTail.length
            · have hsecondRecord := validInput_reconstruct
                secondCount secondTail hsecondLength
              rw [hsecondRecord]
              simpa only [FinTM2.step, Fin.isValue, List.length_append, lengthPrefixedWord_length,
                  List.length_take,
                  List.length_drop, List.append_assoc] using
                  certifiedNatural_validTrace first (secondTail.take secondCount) (secondTail.drop
                      secondCount)
            · exact certifiedNatural_truncatedSecondTrace
                first secondCount secondTail
                (Nat.lt_of_not_ge hsecondLength)
      · exact certifiedNatural_truncatedFirstTrace
          count tail (Nat.lt_of_not_ge hlength)

/-- GapCVP reduction support. -/
def sourcePreservingDelimitedNaturalComparisonComputable :
    BitTM
      sourcePreservingDelimitedNaturalComparisonWord where
  tm := delimitedNaturalComparisonMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 24 * (Polynomial.X + 1) + 24
  outputsFun input := {
    steps := (certifiedNatural_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun,
              delimitedNaturalComparisonMachine_init, Option.map_some] using
          (certifiedNatural_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (certifiedNatural_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq, Polynomial.eval_add,
          Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one, ge_iff_le] using hsteps
  }

end CNFNaturalOrderCertifiedComparator

namespace CNFPolynomialRowMarkerTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

/-- GapCVP reduction support. -/
def sourcePreservingPolynomialMarkerWord
    (polynomial : Polynomial ℕ)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord input ++
    lengthPrefixedWord
      (List.replicate (polynomial.eval input.length) true)

private theorem read_sourcePreservingPolynomialMarkerWord
    (polynomial : Polynomial ℕ)
    (input : List Bool) :
    readLengthPrefixedWord
        (sourcePreservingPolynomialMarkerWord polynomial input) =
      some
        (input,
          lengthPrefixedWord
            (List.replicate (polynomial.eval input.length) true)) := by
  exact readLengthPrefixedWord_append input
    (lengthPrefixedWord
      (List.replicate (polynomial.eval input.length) true))

/-- Internal support shared across GapCVP continuation modules. -/
theorem firstFieldSuffix_sourcePreservingPolynomialMarkerWord
    (polynomial : Polynomial ℕ)
    (input : List Bool) :
    firstFieldSuffix
        (sourcePreservingPolynomialMarkerWord polynomial input) =
      lengthPrefixedWord
        (List.replicate (polynomial.eval input.length) true) := by
  unfold firstFieldSuffix
  rw [read_sourcePreservingPolynomialMarkerWord]

/-- Internal support shared across GapCVP continuation modules. -/
def polynomialRowMarkerHorner
    (polynomial : Polynomial ℕ) (value : ℕ) :
    ℕ → ℕ → ℕ
  | 0, accumulator => accumulator
  | stage + 1, accumulator =>
      polynomialRowMarkerHorner polynomial value stage
        (accumulator * value + polynomial.coeff stage)

private theorem polynomialRowMarkerHorner_closed
    (polynomial : Polynomial ℕ)
    (value stages accumulator : ℕ) :
    polynomialRowMarkerHorner
        polynomial value stages accumulator =
      accumulator * value ^ stages +
        ∑ stage ∈ Finset.range stages,
          polynomial.coeff stage * value ^ stage := by
  induction stages generalizing accumulator with
  | zero =>
      simp only [polynomialRowMarkerHorner, pow_zero, mul_one, Finset.range_zero, Finset.sum_empty,
          add_zero]
  | succ stage ih =>
      rw [polynomialRowMarkerHorner, ih,
        Finset.sum_range_succ, pow_succ]
      ring

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarkerHorner_eval
    (polynomial : Polynomial ℕ)
    (value : ℕ) :
    polynomialRowMarkerHorner
        polynomial value (polynomial.natDegree + 1) 0 =
      polynomial.eval value := by
  rw [polynomialRowMarkerHorner_closed]
  simp only [zero_mul, zero_add]
  have hdegree :
      polynomial.natDegree < polynomial.natDegree + 1 := by
    omega
  simpa only using (Polynomial.eval_eq_sum_range' (x := value) hdegree).symm

/-- Internal support shared across GapCVP continuation modules. -/
abbrev PolynomialRowMarkerStage (polynomial : Polynomial ℕ) :=
  Fin (polynomial.natDegree + 1)

/-- Internal support shared across GapCVP continuation modules. -/
def polynomialRowMarkerTopStage
    (polynomial : Polynomial ℕ) :
    PolynomialRowMarkerStage polynomial :=
  ⟨polynomial.natDegree, by omega⟩

private def polynomialRowMarkerPeek
    (polynomial : Polynomial ℕ)
    (stack : Fin 7)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool) :=
  .peek stack (fun _ bit => bit)
    (.branch (fun bit => bit.isSome) present absent)

private def polynomialRowMarkerPop
    (polynomial : Polynomial ℕ)
    (stack : Fin 7)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool) :=
  .pop stack (fun bit _ => bit) continuation

private def polynomialRowMarkerPushBit
    (polynomial : Polynomial ℕ)
    (stack : Fin 7)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool) :=
  .push stack (fun bit => bit.getD false) continuation

private def polynomialRowMarkerPushConstant
    (polynomial : Polynomial ℕ)
    (stack : Fin 7) (bit : Bool)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool) :=
  .push stack (fun _ => bit) continuation

private def polynomialRowMarkerGoto
    (polynomial : Polynomial ℕ)
    (phase : Fin 9)
    (stage : PolynomialRowMarkerStage polynomial) :
    Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => (phase, stage)))

private def polynomialRowMarkerPushBits
    (polynomial : Polynomial ℕ)
    (stack : Fin 7) :
    List Bool →
      Turing.TM2.Stmt
        (fun _ : Fin 7 => Bool)
        (Fin 9 × PolynomialRowMarkerStage polynomial)
        (Option Bool) →
      Turing.TM2.Stmt
        (fun _ : Fin 7 => Bool)
        (Fin 9 × PolynomialRowMarkerStage polynomial)
        (Option Bool)
  | [], continuation => continuation
  | bit :: remaining, continuation =>
      polynomialRowMarkerPushConstant polynomial stack bit
        (polynomialRowMarkerPushBits polynomial stack
          remaining continuation)

private theorem polynomialRowMarkerPushBits_stepAux
    (polynomial : Polynomial ℕ)
    (stack : Fin 7)
    (bits : List Bool)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool))
    (state : Option Bool)
    (stackWords : (index : Fin 7) → List Bool) :
    Turing.TM2.stepAux
        (polynomialRowMarkerPushBits
          polynomial stack bits continuation)
        state stackWords =
      Turing.TM2.stepAux continuation state
        (Function.update stackWords stack
          (bits.reverse ++ stackWords stack)) := by
  induction bits generalizing stackWords with
  | nil =>
      simp only [polynomialRowMarkerPushBits, List.reverse_nil, List.nil_append,
          Function.update_eq_self]
  | cons bit remaining ih =>
      simp only [polynomialRowMarkerPushBits,
        polynomialRowMarkerPushConstant,
        Turing.TM2.stepAux]
      rw [ih]
      congr 1
      funext index
      by_cases heq : index = stack
      · subst index
        simp only [Function.update, ↓reduceDIte, List.reverse_cons, List.append_assoc,
            List.cons_append,
            List.nil_append]
      · simp only [Function.update, heq, ↓reduceDIte]

/-- Internal support shared across GapCVP continuation modules. -/
def polynomialRowMarkerScanStatement
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial) :
    Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool) :=
  polynomialRowMarkerPeek polynomial 0
    (polynomialRowMarkerPop polynomial 0
      (polynomialRowMarkerPushBit polynomial 1
        (polynomialRowMarkerPushConstant polynomial 2 true
          (polynomialRowMarkerGoto polynomial 0 stage))))
    (polynomialRowMarkerGoto polynomial 1 stage)

/-- Internal support shared across GapCVP continuation modules. -/
def polynomialRowMarkerMultiplyStatement
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial) :
    Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool) :=
  polynomialRowMarkerPeek polynomial 4
    (polynomialRowMarkerPop polynomial 4
      (polynomialRowMarkerGoto polynomial 2 stage))
    (polynomialRowMarkerGoto polynomial 4 stage)

/-- Internal support shared across GapCVP continuation modules. -/
def polynomialRowMarkerBaseStatement
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial) :
    Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool) :=
  polynomialRowMarkerPeek polynomial 2
    (polynomialRowMarkerPop polynomial 2
      (polynomialRowMarkerPushConstant polynomial 3 true
        (polynomialRowMarkerPushConstant polynomial 5 true
          (polynomialRowMarkerGoto polynomial 2 stage))))
    (polynomialRowMarkerGoto polynomial 3 stage)

/-- Internal support shared across GapCVP continuation modules. -/
def polynomialRowMarkerRestoreBaseStatement
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial) :
    Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool) :=
  polynomialRowMarkerPeek polynomial 3
    (polynomialRowMarkerPop polynomial 3
      (polynomialRowMarkerPushConstant polynomial 2 true
        (polynomialRowMarkerGoto polynomial 3 stage)))
    (polynomialRowMarkerGoto polynomial 1 stage)

/-- Internal support shared across GapCVP continuation modules. -/
def polynomialRowMarkerPredStage
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (_hstage : stage.val ≠ 0) :
    PolynomialRowMarkerStage polynomial :=
  ⟨stage.val - 1, by have h := stage.isLt; omega⟩

/-- Internal support shared across GapCVP continuation modules. -/
def polynomialRowMarkerCoefficientStatement
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial) :
    Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool) :=
  polynomialRowMarkerPeek polynomial 5
    (polynomialRowMarkerPop polynomial 5
      (polynomialRowMarkerPushConstant polynomial 4 true
        (polynomialRowMarkerGoto polynomial 4 stage)))
    (if hzero : stage.val = 0 then
      polynomialRowMarkerPushBits polynomial 4
        (List.replicate (polynomial.coeff stage.val) true)
        (polynomialRowMarkerGoto polynomial 5 stage)
    else
      polynomialRowMarkerPushBits polynomial 4
        (List.replicate (polynomial.coeff stage.val) true)
        (polynomialRowMarkerGoto polynomial 1
          (polynomialRowMarkerPredStage polynomial stage hzero)))

/-- Internal support shared across GapCVP continuation modules. -/
def polynomialRowMarkerPayloadStatement
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial) :
    Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool) :=
  polynomialRowMarkerPeek polynomial 4
    (polynomialRowMarkerPop polynomial 4
      (polynomialRowMarkerPushConstant polynomial 5 true
        (polynomialRowMarkerPushConstant polynomial 6 true
          (polynomialRowMarkerGoto polynomial 5 stage))))
    (polynomialRowMarkerPushConstant polynomial 6 false
      (polynomialRowMarkerGoto polynomial 6 stage))

/-- Internal support shared across GapCVP continuation modules. -/
def polynomialRowMarkerHeaderStatement
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial) :
    Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool) :=
  polynomialRowMarkerPeek polynomial 5
    (polynomialRowMarkerPop polynomial 5
      (polynomialRowMarkerPushConstant polynomial 6 true
        (polynomialRowMarkerGoto polynomial 6 stage)))
    (polynomialRowMarkerGoto polynomial 7 stage)

/-- Internal support shared across GapCVP continuation modules. -/
def polynomialRowMarkerSourceStatement
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial) :
    Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool) :=
  polynomialRowMarkerPeek polynomial 1
    (polynomialRowMarkerPop polynomial 1
      (polynomialRowMarkerPushBit polynomial 6
        (polynomialRowMarkerGoto polynomial 7 stage)))
    (polynomialRowMarkerPushConstant polynomial 6 false
      (polynomialRowMarkerGoto polynomial 8 stage))

/-- Internal support shared across GapCVP continuation modules. -/
def polynomialRowMarkerPrefixStatement
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial) :
    Turing.TM2.Stmt
      (fun _ : Fin 7 => Bool)
      (Fin 9 × PolynomialRowMarkerStage polynomial)
      (Option Bool) :=
  polynomialRowMarkerPeek polynomial 2
    (polynomialRowMarkerPop polynomial 2
      (polynomialRowMarkerPushConstant polynomial 6 true
        (polynomialRowMarkerGoto polynomial 8 stage)))
    .halt

/-- Internal support shared across GapCVP continuation modules. -/
abbrev polynomialRowMarkerMachine
    (polynomial : Polynomial ℕ) : Turing.FinTM2 where
  K := Fin 7
  k₀ := 0
  k₁ := 6
  Γ _ := Bool
  Λ := Fin 9 × PolynomialRowMarkerStage polynomial
  main := (0, polynomialRowMarkerTopStage polynomial)
  σ := Option Bool
  initialState := none
  m label :=
    if label.1 = (0 : Fin 9) then
      polynomialRowMarkerScanStatement polynomial label.2
    else if label.1 = (1 : Fin 9) then
      polynomialRowMarkerMultiplyStatement polynomial label.2
    else if label.1 = (2 : Fin 9) then
      polynomialRowMarkerBaseStatement polynomial label.2
    else if label.1 = (3 : Fin 9) then
      polynomialRowMarkerRestoreBaseStatement polynomial label.2
    else if label.1 = (4 : Fin 9) then
      polynomialRowMarkerCoefficientStatement polynomial label.2
    else if label.1 = (5 : Fin 9) then
      polynomialRowMarkerPayloadStatement polynomial label.2
    else if label.1 = (6 : Fin 9) then
      polynomialRowMarkerHeaderStatement polynomial label.2
    else if label.1 = (7 : Fin 9) then
      polynomialRowMarkerSourceStatement polynomial label.2
    else
      polynomialRowMarkerPrefixStatement polynomial label.2

/-- Internal support shared across GapCVP continuation modules. -/
def polynomialRowMarkerConfiguration
    (polynomial : Polynomial ℕ)
    (phase : Fin 9)
    (stage : PolynomialRowMarkerStage polynomial)
    (input source base baseScratch accumulator product output :
      List Bool) :
    (polynomialRowMarkerMachine polynomial).Cfg where
  l := some (phase, stage)
  var := none
  stk := ![input, source, base, baseScratch,
    accumulator, product, output]

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarkerMachine_init
    (polynomial : Polynomial ℕ)
    (input : List Bool) :
    Turing.initList (polynomialRowMarkerMachine polynomial) input =
      polynomialRowMarkerConfiguration polynomial
        0 (polynomialRowMarkerTopStage polynomial)
        input [] [] [] [] [] [] := by
  simp only [polynomialRowMarkerMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq,
      dite_eq_ite,
      polynomialRowMarkerConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `polynomialRowMarkerStepTac` machine-step simplifier. -/
macro "polynomialRowMarkerStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [polynomialRowMarkerMachine,
          polynomialRowMarkerConfiguration,
          polynomialRowMarkerPeek, polynomialRowMarkerPop,
          polynomialRowMarkerPushBit,
          polynomialRowMarkerPushConstant,
          polynomialRowMarkerGoto,
          polynomialRowMarkerScanStatement,
          polynomialRowMarkerMultiplyStatement,
          polynomialRowMarkerBaseStatement,
          polynomialRowMarkerRestoreBaseStatement,
          polynomialRowMarkerCoefficientStatement,
          polynomialRowMarkerPayloadStatement,
          polynomialRowMarkerHeaderStatement,
          polynomialRowMarkerSourceStatement,
          polynomialRowMarkerPrefixStatement,
          polynomialRowMarkerPushBits_stepAux,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_scan_step
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (bit : Bool)
    (input source base baseScratch accumulator product output :
      List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 0 stage
          (bit :: input) source base baseScratch
          accumulator product output) =
      some
        (polynomialRowMarkerConfiguration polynomial 0 stage
          input (bit :: source) (true :: base) baseScratch
          accumulator product output) := by
  cases bit <;> polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_scan_finish
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (source base baseScratch accumulator product output :
      List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 0 stage
          [] source base baseScratch accumulator product output) =
      some
        (polynomialRowMarkerConfiguration polynomial 1 stage
          [] source base baseScratch accumulator product output) := by
  polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_multiply_step
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (source base baseScratch accumulator product output :
      List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 1 stage
          [] source base baseScratch (true :: accumulator)
          product output) =
      some
        (polynomialRowMarkerConfiguration polynomial 2 stage
          [] source base baseScratch accumulator product output) := by
  polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_multiply_finish
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (source base baseScratch product output : List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 1 stage
          [] source base baseScratch [] product output) =
      some
        (polynomialRowMarkerConfiguration polynomial 4 stage
          [] source base baseScratch [] product output) := by
  polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_base_step
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (source base baseScratch accumulator product output :
      List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 2 stage
          [] source (true :: base) baseScratch
          accumulator product output) =
      some
        (polynomialRowMarkerConfiguration polynomial 2 stage
          [] source base (true :: baseScratch)
          accumulator (true :: product) output) := by
  polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_base_finish
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (source baseScratch accumulator product output : List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 2 stage
          [] source [] baseScratch accumulator product output) =
      some
        (polynomialRowMarkerConfiguration polynomial 3 stage
          [] source [] baseScratch accumulator product output) := by
  polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_restoreBase_step
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (source base baseScratch accumulator product output :
      List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 3 stage
          [] source base (true :: baseScratch)
          accumulator product output) =
      some
        (polynomialRowMarkerConfiguration polynomial 3 stage
          [] source (true :: base) baseScratch
          accumulator product output) := by
  polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_restoreBase_finish
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (source base accumulator product output : List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 3 stage
          [] source base [] accumulator product output) =
      some
        (polynomialRowMarkerConfiguration polynomial 1 stage
          [] source base [] accumulator product output) := by
  polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_product_step
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (source base accumulator product output : List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 4 stage
          [] source base [] accumulator (true :: product) output) =
      some
        (polynomialRowMarkerConfiguration polynomial 4 stage
          [] source base [] (true :: accumulator) product output) := by
  polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_coefficient_zero_step
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (hstage : stage.val = 0)
    (source base accumulator output : List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 4 stage
          [] source base [] accumulator [] output) =
      some
        (polynomialRowMarkerConfiguration polynomial 5 stage
          [] source base []
          (List.replicate (polynomial.coeff stage.val) true ++
            accumulator)
          [] output) := by
  have hstage' : stage = (0 : PolynomialRowMarkerStage polynomial) :=
    Fin.ext hstage
  polynomialRowMarkerStepTac;
    simp only [Fin.isValue, hstage', ↓reduceDIte, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      polynomialRowMarkerPushBits_stepAux, TM2.stepAux, List.reverse_replicate, Matrix.cons_val];
    try { congr 2; funext stack; fin_cases stack <;>
      simp [Function.update] }

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_coefficient_succ_step
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (hstage : stage.val ≠ 0)
    (source base accumulator output : List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 4 stage
          [] source base [] accumulator [] output) =
      some
        (polynomialRowMarkerConfiguration polynomial 1
          (polynomialRowMarkerPredStage polynomial stage hstage)
          [] source base []
          (List.replicate (polynomial.coeff stage.val) true ++
            accumulator)
          [] output) := by
  have hstage' : stage ≠ (0 : PolynomialRowMarkerStage polynomial) := by
    intro heq
    apply hstage
    simpa only [Fin.val_eq_zero_iff, Fin.coe_ofNat_eq_mod, Nat.zero_mod] using congrArg Fin.val heq
  polynomialRowMarkerStepTac;
    simp only [Fin.isValue, hstage', ↓reduceDIte, polynomialRowMarkerPushBits_stepAux, TM2.stepAux,
      List.reverse_replicate, Matrix.cons_val];
    try { congr 2; funext stack; fin_cases stack <;>
      simp [Function.update] }

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_payload_step
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (source base accumulator product output : List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 5 stage
          [] source base [] (true :: accumulator)
          product output) =
      some
        (polynomialRowMarkerConfiguration polynomial 5 stage
          [] source base [] accumulator
          (true :: product) (true :: output)) := by
  polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_payload_finish
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (source base product output : List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 5 stage
          [] source base [] [] product output) =
      some
        (polynomialRowMarkerConfiguration polynomial 6 stage
          [] source base [] [] product (false :: output)) := by
  polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_header_step
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (source base product output : List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 6 stage
          [] source base [] [] (true :: product) output) =
      some
        (polynomialRowMarkerConfiguration polynomial 6 stage
          [] source base [] [] product (true :: output)) := by
  polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_header_finish
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (source base output : List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 6 stage
          [] source base [] [] [] output) =
      some
        (polynomialRowMarkerConfiguration polynomial 7 stage
          [] source base [] [] [] output) := by
  polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_source_step
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (bit : Bool)
    (source base output : List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 7 stage
          [] (bit :: source) base [] [] [] output) =
      some
        (polynomialRowMarkerConfiguration polynomial 7 stage
          [] source base [] [] [] (bit :: output)) := by
  cases bit <;> polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_source_finish
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (base output : List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 7 stage
          [] [] base [] [] [] output) =
      some
        (polynomialRowMarkerConfiguration polynomial 8 stage
          [] [] base [] [] [] (false :: output)) := by
  polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_prefix_step
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (base output : List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 8 stage
          [] [] (true :: base) [] [] [] output) =
      some
        (polynomialRowMarkerConfiguration polynomial 8 stage
          [] [] base [] [] [] (true :: output)) := by
  polynomialRowMarkerStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem polynomialRowMarker_finish
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (output : List Bool) :
    (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 8 stage
          [] [] [] [] [] [] output) =
      some
        (Turing.haltList
          (polynomialRowMarkerMachine polynomial) output) := by
  polynomialRowMarkerStepTac

end CNFPolynomialRowMarkerTM

end GapCVP

end
