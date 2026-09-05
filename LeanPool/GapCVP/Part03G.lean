/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part03F

/-! # GapCVP proof, part 03, continuation 07 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFEncodedClauseSort

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder

open GapCVP.CNFSortingDedup

private def delimitedCompare_missingFirstTrace (count : ℕ) :
    EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 0 .invalid
        (List.replicate count true) [] [] [] [] [] [] [] [] [])
      (some (Turing.haltList delimitedPairComparisonMachine
        (sourcePreservingDelimitedPairComparisonWord
          (List.replicate count true))))
      (24 * ((List.replicate count true).length + 1) + 24) := by
  have hscan :
      EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 0 .invalid
          (List.replicate count true) [] [] [] [] [] [] [] [] [])
        (some (delimitedCompareConfiguration 7 .invalid
          [] (List.replicate count true) [] [] [] [] []
          (List.replicate count true)
          (List.replicate count true) []))
        (count + 1) := by
    simpa only [FinTM2.step, Fin.isValue, List.append_nil] using
        delimitedCompareFirstMissingPrefixTrace .invalid count [] [] [] [] [] [] [] [] []
  have hfinish := delimitedCompareFinishTrace .invalid
    [] (List.replicate count true) [] [] [] [] []
    (List.replicate count true) (List.replicate count true) []
  have hrestored :
      delimitedCompareRestoredWord .invalid []
        (List.replicate count true) (List.replicate count true) [] =
      sourcePreservingDelimitedPairComparisonWord
        (List.replicate count true) := by
    simp only [delimitedCompareRestoredWord, List.length_nil, List.length_replicate, zero_add,
        List.reverse_replicate, List.append_nil, sourcePreservingDelimitedPairComparisonWord,
            lengthPrefixedWord,
        delimitedPairWordOrdering_missingFirst, List.append_assoc, List.cons_append]
  rw [hrestored] at hfinish
  have hfull := EvalsToInTime.trans delimitedPairComparisonMachine.step _ _ _ _ _ hscan hfinish
  apply rebound hfull
  simp only [List.length_replicate, List.length_nil]
  omega

private def delimitedCompare_truncatedFirstTrace
    (count : ℕ) (payload : List Bool)
    (hshort : payload.length < count) :
    EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 0 .invalid
        (List.replicate count true ++ false :: payload)
        [] [] [] [] [] [] [] [] [])
      (some (Turing.haltList delimitedPairComparisonMachine
        (sourcePreservingDelimitedPairComparisonWord
          (List.replicate count true ++ false :: payload))))
      (24 *
        ((List.replicate count true ++ false :: payload).length + 1) +
        24) := by
  let extra := count - payload.length - 1
  have hcount : count = payload.length + extra + 1 := by
    dsimp [extra]
    omega
  have hcounter :
      List.replicate count true =
        List.replicate payload.length true ++
          List.replicate (extra + 1) true := by
    have hsplit : count = payload.length + (extra + 1) := by
      omega
    rw [hsplit, List.replicate_add]
  let saved :=
    payload.reverse ++ false :: List.replicate count true
  let prefixMarkers :=
    List.replicate payload.length true ++
      List.replicate (count + 1) true
  have hprefix :
      EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 0 .invalid
          (List.replicate count true ++ false :: payload)
          [] [] [] [] [] [] [] [] [])
        (some (delimitedCompareConfiguration 1 .invalid
          payload (List.replicate count true) [] [] [] [] []
          (false :: List.replicate count true)
          (List.replicate (count + 1) true) []))
        (count + 1) := by
    simpa only [FinTM2.step, Fin.isValue, List.append_nil] using
        delimitedCompareFirstPrefixTrace .invalid count payload [] [] [] [] [] [] [] [] []
  have hpartial :
      EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 1 .invalid
          payload (List.replicate count true) [] [] [] [] []
          (false :: List.replicate count true)
          (List.replicate (count + 1) true) [])
        (some (delimitedCompareConfiguration 1 .invalid
          [] (true :: List.replicate extra true)
          payload.reverse [] [] [] [] saved prefixMarkers []))
        payload.length := by
    have hremaining :
        List.replicate (extra + 1) true =
          true :: List.replicate extra true := by
      simp only [List.replicate_succ]
    have hraw := delimitedCompareFirstPartialPayloadTrace
      .invalid payload (List.replicate (extra + 1) true)
      [] [] [] [] []
      (false :: List.replicate count true)
      (List.replicate (count + 1) true) []
    rw [← hcounter, hremaining] at hraw
    simpa only [saved, prefixMarkers, List.append_nil] using hraw
  have hmissing := oneStep _ _ (delimitedCompare_firstPayload_missing .invalid true
      (List.replicate extra true) payload.reverse
      [] [] [] [] saved prefixMarkers [])
  have hfinish := delimitedCompareFinishTrace .invalid
    [] (List.replicate extra true) payload.reverse
    [] [] [] [] saved prefixMarkers []
  have hprefixLength :
      prefixMarkers.length =
        (List.replicate count true ++ false :: payload).length := by
    simp only [prefixMarkers, List.length_append,
      List.length_replicate, List.length_cons]
    omega
  have hordering :=
    delimitedPairWordOrdering_shortFirst count payload hshort
  have hrestored :
      delimitedCompareRestoredWord .invalid []
        saved prefixMarkers [] =
      sourcePreservingDelimitedPairComparisonWord
        (List.replicate count true ++ false :: payload) := by
    simp only [delimitedCompareRestoredWord,
      sourcePreservingDelimitedPairComparisonWord,
      hordering, List.length_nil, Nat.zero_add, List.append_nil]
    rw [hprefixLength]
    simp only [List.length_append, List.length_replicate, List.length_cons, List.reverse_append,
        List.reverse_cons, List.reverse_replicate, List.reverse_reverse, List.append_assoc,
            List.cons_append,
        List.nil_append, lengthPrefixedWord, saved]
  rw [hrestored] at hfinish
  have h01 := EvalsToInTime.trans delimitedPairComparisonMachine.step _ _ _ _ _ hprefix hpartial
  have h012 := EvalsToInTime.trans delimitedPairComparisonMachine.step _ _ _ _ _ h01 hmissing
  have hfull := EvalsToInTime.trans delimitedPairComparisonMachine.step _ _ _ _ _ h012 hfinish
  apply rebound hfull
  simp only [saved, prefixMarkers,
    List.length_append, List.length_replicate,
    List.length_reverse, List.length_cons, List.length_nil]
  omega

private def delimitedCompare_missingSecondTrace
    (first : List Bool) (count : ℕ) :
    EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 0 .invalid
        (lengthPrefixedWord first ++ List.replicate count true)
        [] [] [] [] [] [] [] [] [])
      (some (Turing.haltList delimitedPairComparisonMachine
        (sourcePreservingDelimitedPairComparisonWord
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
      EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 0 .invalid
          (lengthPrefixedWord first ++ List.replicate count true)
          [] [] [] [] [] [] [] [] [])
        (some (delimitedCompareConfiguration 2 .invalid
          (List.replicate count true)
          [] first.reverse [] [] [] [] firstCode.reverse
          (List.replicate firstCode.length true) []))
        (2 * first.length + 2) := by
    simpa [firstCode] using delimitedCompareFirstRecordTrace
      .invalid first (List.replicate count true)
      [] [] [] [] [] [] [] []
  have hmissing :
      EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 2 .invalid
          (List.replicate count true)
          [] first.reverse [] [] [] [] firstCode.reverse
          (List.replicate firstCode.length true) [])
        (some (delimitedCompareConfiguration 7 .invalid
          [] [] first.reverse (List.replicate count true)
          [] [] [] saved prefixMarkers []))
        (count + 1) := by
    simpa [saved, prefixMarkers] using
      delimitedCompareSecondMissingPrefixTrace .invalid count
        [] first.reverse [] [] [] []
        firstCode.reverse (List.replicate firstCode.length true) []
  have hfinish := delimitedCompareFinishTrace .invalid
    [] [] first.reverse (List.replicate count true)
    [] [] [] saved prefixMarkers []
  have hprefixLength :
      prefixMarkers.length =
        (lengthPrefixedWord first ++
          List.replicate count true).length := by
    simp only [prefixMarkers, firstCode,
      List.length_append, List.length_replicate]
    omega
  have hrestored :
      delimitedCompareRestoredWord .invalid []
        saved prefixMarkers [] =
      sourcePreservingDelimitedPairComparisonWord
        (lengthPrefixedWord first ++ List.replicate count true) := by
    simp only [delimitedCompareRestoredWord,
      sourcePreservingDelimitedPairComparisonWord,
      delimitedPairWordOrdering_missingSecond,
      List.length_nil, Nat.zero_add, List.append_nil]
    rw [hprefixLength]
    simp [saved, firstCode, lengthPrefixedWord,
      List.reverse_append, List.append_assoc]
  rw [hrestored] at hfinish
  have hfirstTwo := EvalsToInTime.trans
    delimitedPairComparisonMachine.step _ _ _ _ _ hfirst hmissing
  have hfull := EvalsToInTime.trans delimitedPairComparisonMachine.step _ _ _ _ _ hfirstTwo hfinish
  apply rebound hfull
  simp only [saved, prefixMarkers, firstCode,
    List.length_append, List.length_replicate,
    List.length_reverse, List.length_nil,
    lengthPrefixedWord_length]
  omega

private def delimitedCompare_truncatedSecondTrace
    (first : List Bool) (count : ℕ) (payload : List Bool)
    (hshort : payload.length < count) :
    EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 0 .invalid
        (lengthPrefixedWord first ++
          (List.replicate count true ++ false :: payload))
        [] [] [] [] [] [] [] [] [])
      (some (Turing.haltList delimitedPairComparisonMachine
        (sourcePreservingDelimitedPairComparisonWord
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
    have hsplit : count = payload.length + (extra + 1) := by
      omega
    rw [hsplit, List.replicate_add]
  let firstCode := lengthPrefixedWord first
  let saved :=
    payload.reverse ++
      false :: (List.replicate count true ++ firstCode.reverse)
  let prefixMarkers :=
    List.replicate payload.length true ++
      (List.replicate (count + 1) true ++
        List.replicate firstCode.length true)
  have hfirst :
      EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 0 .invalid
          (lengthPrefixedWord first ++
            (List.replicate count true ++ false :: payload))
          [] [] [] [] [] [] [] [] [])
        (some (delimitedCompareConfiguration 2 .invalid
          (List.replicate count true ++ false :: payload)
          [] first.reverse [] [] [] []
          firstCode.reverse
          (List.replicate firstCode.length true) []))
        (2 * first.length + 2) := by
    simpa [firstCode] using
      delimitedCompareFirstRecordTrace .invalid first
        (List.replicate count true ++ false :: payload)
        [] [] [] [] [] [] [] []
  have hprefix :
      EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 2 .invalid
          (List.replicate count true ++ false :: payload)
          [] first.reverse [] [] [] []
          firstCode.reverse
          (List.replicate firstCode.length true) [])
        (some (delimitedCompareConfiguration 3 .invalid
          payload [] first.reverse
          (List.replicate count true) [] [] []
          (false ::
            (List.replicate count true ++ firstCode.reverse))
          (List.replicate (count + 1) true ++
            List.replicate firstCode.length true) []))
        (count + 1) := by
    simpa using delimitedCompareSecondPrefixTrace .invalid count
      payload [] first.reverse [] [] [] []
      firstCode.reverse (List.replicate firstCode.length true) []
  have hpartial :
      EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 3 .invalid
          payload [] first.reverse
          (List.replicate count true) [] [] []
          (false ::
            (List.replicate count true ++ firstCode.reverse))
          (List.replicate (count + 1) true ++
            List.replicate firstCode.length true) [])
        (some (delimitedCompareConfiguration 3 .invalid
          [] [] first.reverse (true :: List.replicate extra true)
          payload.reverse [] [] saved prefixMarkers []))
        payload.length := by
    have hremaining :
        List.replicate (extra + 1) true =
          true :: List.replicate extra true := by
      simp [List.replicate_succ]
    have hraw := delimitedCompareSecondPartialPayloadTrace
      .invalid payload (List.replicate (extra + 1) true)
      [] first.reverse [] [] []
      (false :: (List.replicate count true ++ firstCode.reverse))
      (List.replicate (count + 1) true ++
        List.replicate firstCode.length true) []
    rw [← hcounter, hremaining] at hraw
    simpa only [saved, prefixMarkers, List.append_nil] using hraw
  have hmissing := oneStep _ _ (delimitedCompare_secondPayload_missing .invalid true
      [] first.reverse (List.replicate extra true)
      payload.reverse [] [] saved prefixMarkers [])
  have hfinish := delimitedCompareFinishTrace .invalid
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
    delimitedPairWordOrdering_shortSecond first count payload hshort
  have hrestored :
      delimitedCompareRestoredWord .invalid []
        saved prefixMarkers [] =
      sourcePreservingDelimitedPairComparisonWord
        (lengthPrefixedWord first ++
          (List.replicate count true ++ false :: payload)) := by
    simp only [delimitedCompareRestoredWord,
      sourcePreservingDelimitedPairComparisonWord,
      hordering, List.length_nil, Nat.zero_add, List.append_nil]
    rw [hprefixLength]
    simp [saved, firstCode, lengthPrefixedWord,
      List.reverse_append, List.append_assoc]
  rw [hrestored] at hfinish
  have h01 := EvalsToInTime.trans delimitedPairComparisonMachine.step _ _ _ _ _ hfirst hprefix
  have h012 := EvalsToInTime.trans delimitedPairComparisonMachine.step _ _ _ _ _ h01 hpartial
  have h0123 := EvalsToInTime.trans delimitedPairComparisonMachine.step _ _ _ _ _ h012 hmissing
  have hfull := EvalsToInTime.trans delimitedPairComparisonMachine.step _ _ _ _ _ h0123 hfinish
  apply rebound hfull
  simp only [saved, prefixMarkers, firstCode,
    List.length_append, List.length_replicate,
    List.length_reverse, List.length_cons, List.length_nil,
    lengthPrefixedWord_length]
  omega

private def delimitedCompare_totalTrace (input : List Bool) :
    EvalsToInTime delimitedPairComparisonMachine.step (delimitedCompareConfiguration 0 .invalid
        input [] [] [] [] [] [] [] [] [])
      (some (Turing.haltList delimitedPairComparisonMachine
        (sourcePreservingDelimitedPairComparisonWord input)))
      (24 * (input.length + 1) + 24) := by
  cases unaryInputSplit input with
  | inl witness =>
      obtain ⟨count, hinput⟩ := witness
      subst input
      exact delimitedCompare_missingFirstTrace count
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
            exact delimitedCompare_missingSecondTrace
              first secondCount
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
                  delimitedCompareValidTrace first (secondTail.take secondCount) (secondTail.drop
                      secondCount)
            · exact delimitedCompare_truncatedSecondTrace
                first secondCount secondTail
                (Nat.lt_of_not_ge hsecondLength)
      · exact delimitedCompare_truncatedFirstTrace
          count tail (Nat.lt_of_not_ge hlength)

/-- GapCVP reduction support. -/
def sourcePreservingDelimitedPairComparisonComputable :
    BitTM
      sourcePreservingDelimitedPairComparisonWord where
  tm := delimitedPairComparisonMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 24 * (Polynomial.X + 1) + 24
  outputsFun input := {
    steps := (delimitedCompare_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, delimitedPairComparisonMachine_init,
              Option.map_some] using
          (delimitedCompare_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (delimitedCompare_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq, Polynomial.eval_add,
          Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one, ge_iff_le] using hsteps
  }

theorem lexicographicEncodedWordOrdering_eq_equal_iff
    (first second : List Bool) :
    lexicographicEncodedWordOrdering first second = .equal ↔
      first = second := by
  induction first generalizing second with
  | nil =>
      cases second <;>
        simp [lexicographicEncodedWordOrdering]
  | cons bit remaining ih =>
      cases second with
      | nil => simp only [lexicographicEncodedWordOrdering, reduceCtorEq]
      | cons next second =>
          cases bit <;> cases next <;>
            simp [lexicographicEncodedWordOrdering, ih]

end CNFEncodedClauseSort


end GapCVP

end
