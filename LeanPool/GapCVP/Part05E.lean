/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part05D

/-! # GapCVP proof, part 05, continuation 05 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFFlatAdjacentRecordSwapTotalCert

open Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder

open GapCVP.SourceFormulaStructuralDecoder GapCVP.CNFFlatAdjacentRecordSwapTM

private def flatAdjacentRecord_failureTrace
    (input first second counter : List Bool) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 6 input first second counter)
      (some (Turing.haltList actualFlatAdjacentRecordSwapMachine []))
      (input.length + first.length + second.length + counter.length + 1) := by
  have hinput := TraceGolf.sweep actualFlatAdjacentRecordSwapMachine.step
    (fun current => flatAdjacentRecordConfiguration 6 current first second counter)
    (fun bit remaining => flatAdjacentRecord_failure_input bit remaining first second counter)
    input
  have hfirst := TraceGolf.sweep actualFlatAdjacentRecordSwapMachine.step
    (fun current => flatAdjacentRecordConfiguration 6 [] current second counter)
    (fun bit remaining => flatAdjacentRecord_failure_first bit remaining second counter)
    first
  have hsecond := TraceGolf.sweep actualFlatAdjacentRecordSwapMachine.step
    (fun current => flatAdjacentRecordConfiguration 6 [] [] current counter)
    (fun bit remaining => flatAdjacentRecord_failure_second bit remaining counter)
    second
  have hcounter := TraceGolf.sweepThen actualFlatAdjacentRecordSwapMachine.step
    (fun current => flatAdjacentRecordConfiguration 6 [] [] [] current)
    flatAdjacentRecord_failure_counter counter flatAdjacentRecord_failure_finish
  have h01 := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step _ _ _ _ _ hinput hfirst
  have h012 := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step _ _ _ _ _ h01 hsecond
  have hfull := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step _ _ _ _ _
    h012 hcounter
  exact rebound hfull (by omega)

private def flatAdjacentRecord_firstPrefixTrace
    (count : ℕ) (tail first second counter : List Bool) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 0
        (List.replicate count true ++ false :: tail)
        first second counter)
      (some (flatAdjacentRecordConfiguration 1 tail
        (false :: (List.replicate count true ++ first))
        second (List.replicate count true ++ counter)))
      (count + 1) := by
  induction count generalizing first counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (flatAdjacentRecord_firstPrefix_false tail first second counter)
  | succ count ih =>
      have hfirst := oneStep _ _ (flatAdjacentRecord_firstPrefix_true
          (List.replicate count true ++ false :: tail)
          first second counter)
      have hrest := ih (true :: first) (true :: counter)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step _ _ _ _ _ hfirst hrest

private def flatAdjacentRecord_missingFirstPrefixTrace
    (count : ℕ) (first second counter : List Bool) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 0
        (List.replicate count true) first second counter)
      (some (flatAdjacentRecordConfiguration 6 []
        (List.replicate count true ++ first) second
        (List.replicate count true ++ counter)))
      (count + 1) := by
  induction count generalizing first counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (flatAdjacentRecord_firstPrefix_missing first second counter)
  | succ count ih =>
      have hfirst := oneStep _ _ (flatAdjacentRecord_firstPrefix_true
          (List.replicate count true) first second counter)
      have hrest := ih (true :: first) (true :: counter)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step _ _ _ _ _ hfirst hrest

private def flatAdjacentRecord_firstPayloadTrace
    (payload tail first second : List Bool) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 1
        (payload ++ tail) first second
        (List.replicate payload.length true))
      (some (flatAdjacentRecordConfiguration 2 tail
        (payload.reverse ++ first) second []))
      (payload.length + 1) := by
  induction payload generalizing first with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.nil_append, List.length_nil, List.replicate_zero,
          List.reverse_nil,
          zero_add] using oneStep _ _ (flatAdjacentRecord_firstPayload_finish tail first second)
  | cons bit payload ih =>
      have hfirst := oneStep _ _ (flatAdjacentRecord_firstPayload_step bit
          (payload ++ tail) first second
          (List.replicate payload.length true))
      have hrest := ih (bit :: first)
      simpa only [FinTM2.step, Fin.isValue, List.cons_append, List.length_cons,
          List.replicate_succ,
          List.reverse_cons, List.append_assoc, List.nil_append, Nat.add_assoc, Nat.reduceAdd]
              using
          EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step _ _ _ _ _ hfirst hrest

private def flatAdjacentRecord_shortFirstPayloadTrace
    (payload : List Bool) (extra : ℕ)
    (first second : List Bool) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 1
        payload first second
        (List.replicate (payload.length + extra + 1) true))
      (some (flatAdjacentRecordConfiguration 6 []
        (payload.reverse ++ first) second
        (List.replicate (extra + 1) true)))
      (payload.length + 1) := by
  induction payload generalizing first with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, zero_add, List.replicate_succ,
          List.reverse_nil,
          List.nil_append] using
          oneStep _ _ (flatAdjacentRecord_firstPayload_missing first second (List.replicate extra
              true))
  | cons bit payload ih =>
      have hfirst := oneStep _ _ (flatAdjacentRecord_firstPayload_step
          bit payload first second
          (List.replicate (payload.length + extra + 1) true))
      have hrest := ih (bit :: first)
      have hcount :
          payload.length + 1 + extra + 1 =
            (payload.length + extra + 1) + 1 := by
        omega
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, hcount, List.replicate_succ,
          List.reverse_cons,
          List.append_assoc, List.cons_append, List.nil_append] using
          EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step _ _ _ _ _ hfirst hrest

private def flatAdjacentRecord_secondPrefixTrace
    (count : ℕ) (tail first second counter : List Bool) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 2
        (List.replicate count true ++ false :: tail)
        first second counter)
      (some (flatAdjacentRecordConfiguration 3 tail first
        (false :: (List.replicate count true ++ second))
        (List.replicate count true ++ counter)))
      (count + 1) := by
  induction count generalizing second counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (flatAdjacentRecord_secondPrefix_false tail first second counter)
  | succ count ih =>
      have hfirst := oneStep _ _ (flatAdjacentRecord_secondPrefix_true
          (List.replicate count true ++ false :: tail)
          first second counter)
      have hrest := ih (true :: second) (true :: counter)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step _ _ _ _ _ hfirst hrest

private def flatAdjacentRecord_missingSecondPrefixTrace
    (count : ℕ) (first second counter : List Bool) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 2
        (List.replicate count true) first second counter)
      (some (flatAdjacentRecordConfiguration 6 []
        first (List.replicate count true ++ second)
        (List.replicate count true ++ counter)))
      (count + 1) := by
  induction count generalizing second counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (flatAdjacentRecord_secondPrefix_missing first second counter)
  | succ count ih =>
      have hfirst := oneStep _ _ (flatAdjacentRecord_secondPrefix_true
          (List.replicate count true) first second counter)
      have hrest := ih (true :: second) (true :: counter)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step _ _ _ _ _ hfirst hrest

private def flatAdjacentRecord_secondPayloadTrace
    (payload tail first second : List Bool) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 3
        (payload ++ tail) first second
        (List.replicate payload.length true))
      (some (flatAdjacentRecordConfiguration 4 tail first
        (payload.reverse ++ second) []))
      (payload.length + 1) := by
  induction payload generalizing second with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.nil_append, List.length_nil, List.replicate_zero,
          List.reverse_nil,
          zero_add] using oneStep _ _ (flatAdjacentRecord_secondPayload_finish tail first second)
  | cons bit payload ih =>
      have hfirst := oneStep _ _ (flatAdjacentRecord_secondPayload_step bit
          (payload ++ tail) first second
          (List.replicate payload.length true))
      have hrest := ih (bit :: second)
      simpa only [FinTM2.step, Fin.isValue, List.cons_append, List.length_cons,
          List.replicate_succ,
          List.reverse_cons, List.append_assoc, List.nil_append, Nat.add_assoc, Nat.reduceAdd]
              using
          EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step _ _ _ _ _ hfirst hrest

private def flatAdjacentRecord_shortSecondPayloadTrace
    (payload : List Bool) (extra : ℕ)
    (first second : List Bool) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 3
        payload first second
        (List.replicate (payload.length + extra + 1) true))
      (some (flatAdjacentRecordConfiguration 6 []
        first (payload.reverse ++ second)
        (List.replicate (extra + 1) true)))
      (payload.length + 1) := by
  induction payload generalizing second with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, zero_add, List.replicate_succ,
          List.reverse_nil,
          List.nil_append] using
          oneStep _ _ (flatAdjacentRecord_secondPayload_missing first second (List.replicate extra
              true))
  | cons bit payload ih =>
      have hfirst := oneStep _ _ (flatAdjacentRecord_secondPayload_step
          bit payload first second
          (List.replicate (payload.length + extra + 1) true))
      have hrest := ih (bit :: second)
      have hcount :
          payload.length + 1 + extra + 1 =
            (payload.length + extra + 1) + 1 := by
        omega
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, hcount, List.replicate_succ,
          List.reverse_cons,
          List.append_assoc, List.cons_append, List.nil_append] using
          EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step _ _ _ _ _ hfirst hrest

private def flatAdjacentRecord_restoreFirstTrace
    (input first second : List Bool) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 4 input first second [])
      (some (flatAdjacentRecordConfiguration 5
        (first.reverse ++ input) [] second []))
      (first.length + 1) := by
  induction first generalizing input with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (flatAdjacentRecord_restoreFirst_finish input second)
  | cons bit first ih =>
      have hfirst := oneStep _ _ (flatAdjacentRecord_restoreFirst_step
          bit input first second)
      have hrest := ih (bit :: input)
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using
          EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step _ _ _ _ _ hfirst hrest

private def flatAdjacentRecord_restoreSecondTrace
    (input second : List Bool) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 5 input [] second [])
      (some (Turing.haltList actualFlatAdjacentRecordSwapMachine
        (second.reverse ++ input)))
      (second.length + 1) := by
  induction second generalizing input with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (flatAdjacentRecord_restoreSecond_finish input)
  | cons bit second ih =>
      have hfirst := oneStep _ _ (flatAdjacentRecord_restoreSecond_step bit input second)
      have hrest := ih (bit :: input)
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using
          EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step _ _ _ _ _ hfirst hrest

private def flatAdjacentRecord_validTrace
    (first second suffix : List Bool) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 0
        (lengthPrefixedWord first ++
          lengthPrefixedWord second ++ suffix) [] [] [])
      (some (Turing.haltList actualFlatAdjacentRecordSwapMachine
        (lengthPrefixedWord second ++
          lengthPrefixedWord first ++ suffix)))
      (4 * first.length + 4 * second.length + 8) := by
  have hfirstPrefix := flatAdjacentRecord_firstPrefixTrace
    first.length
    (first ++ lengthPrefixedWord second ++ suffix) [] [] []
  have hfirstPayload := flatAdjacentRecord_firstPayloadTrace
    first (lengthPrefixedWord second ++ suffix)
    (false :: List.replicate first.length true) []
  have hsecondPrefix := flatAdjacentRecord_secondPrefixTrace
    second.length (second ++ suffix)
    (first.reverse ++ false :: List.replicate first.length true)
    [] []
  have hsecondPayload := flatAdjacentRecord_secondPayloadTrace
    second suffix
    (first.reverse ++ false :: List.replicate first.length true)
    (false :: List.replicate second.length true)
  have hrestoreFirst := flatAdjacentRecord_restoreFirstTrace
    suffix (first.reverse ++ false ::
      List.replicate first.length true)
    (second.reverse ++ false ::
      List.replicate second.length true)
  have hrestoreSecond := flatAdjacentRecord_restoreSecondTrace
    ((first.reverse ++ false ::
      List.replicate first.length true).reverse ++ suffix)
    (second.reverse ++ false ::
      List.replicate second.length true)
  simp only [lengthPrefixedWord, List.append_nil, List.append_assoc]
    at hfirstPrefix hfirstPayload hsecondPrefix hsecondPayload
  have h01 := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step
    _ _ _ _ _ hfirstPrefix hfirstPayload
  have h012 := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step
    _ _ _ _ _ h01 hsecondPrefix
  have h0123 := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step
    _ _ _ _ _ h012 hsecondPayload
  have h01234 := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step
    _ _ _ _ _ h0123 hrestoreFirst
  have hfull := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step
    _ _ _ _ _ h01234 hrestoreSecond
  have hbounded := rebound (newBudget := 4 * first.length + 4 * second.length + 8)
    hfull (by
      simp only [List.length_append, List.length_reverse,
        List.length_cons, List.length_replicate]
      omega)
  simpa only [FinTM2.step, Fin.isValue, lengthPrefixedWord, List.append_assoc, List.cons_append,
      List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_reverse,
          List.nil_append] using
      hbounded

/-- GapCVP reduction support. -/
def flatAdjacentRecordSwapTimePolynomial : Polynomial ℕ :=
  16 * Polynomial.X + 32

private def flatAdjacentRecord_missingFirstTotalTrace
    (count : ℕ) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 0
        (List.replicate count true) [] [] [])
      (some (Turing.haltList actualFlatAdjacentRecordSwapMachine []))
      (flatAdjacentRecordSwapTimePolynomial.eval
        (List.replicate count true).length) := by
  have hscan := flatAdjacentRecord_missingFirstPrefixTrace
    count [] [] []
  simp only [List.append_nil] at hscan
  have hclean := flatAdjacentRecord_failureTrace []
    (List.replicate count true) []
    (List.replicate count true)
  have hfull := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step
    _ _ _ _ _ hscan hclean
  exact rebound hfull (by
    simp only [List.length_nil, List.length_replicate, zero_add, add_zero,
        flatAdjacentRecordSwapTimePolynomial,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    omega)

private def flatAdjacentRecord_shortFirstTotalTrace
    (payload : List Bool) (extra : ℕ) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 0
        (List.replicate (payload.length + extra + 1) true ++
          false :: payload) [] [] [])
      (some (Turing.haltList actualFlatAdjacentRecordSwapMachine []))
      (flatAdjacentRecordSwapTimePolynomial.eval
        (List.replicate (payload.length + extra + 1) true ++
          false :: payload).length) := by
  have hprefix := flatAdjacentRecord_firstPrefixTrace
    (payload.length + extra + 1) payload [] [] []
  have hshort := flatAdjacentRecord_shortFirstPayloadTrace
    payload extra
    (false :: List.replicate (payload.length + extra + 1) true)
    []
  simp only [List.append_nil] at hprefix
  have hscan := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step
    _ _ _ _ _ hprefix hshort
  have hclean := flatAdjacentRecord_failureTrace []
    (payload.reverse ++ false ::
      List.replicate (payload.length + extra + 1) true)
    [] (List.replicate (extra + 1) true)
  have hfull := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step
    _ _ _ _ _ hscan hclean
  exact rebound hfull (by
    simp only [List.length_nil, List.length_append, List.length_reverse, List.length_cons,
        List.length_replicate,
        zero_add, add_zero, flatAdjacentRecordSwapTimePolynomial, Polynomial.eval_add,
            Polynomial.eval_mul,
        Polynomial.eval_ofNat, Polynomial.eval_X]
    omega)

private def flatAdjacentRecord_missingSecondTotalTrace
    (first : List Bool) (count : ℕ) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 0
        (lengthPrefixedWord first ++
          List.replicate count true) [] [] [])
      (some (Turing.haltList actualFlatAdjacentRecordSwapMachine []))
      (flatAdjacentRecordSwapTimePolynomial.eval
        (lengthPrefixedWord first ++
          List.replicate count true).length) := by
  have hfirstPrefix := flatAdjacentRecord_firstPrefixTrace
    first.length (first ++ List.replicate count true) [] [] []
  have hfirstPayload := flatAdjacentRecord_firstPayloadTrace
    first (List.replicate count true)
    (false :: List.replicate first.length true) []
  have hsecond := flatAdjacentRecord_missingSecondPrefixTrace
    count (first.reverse ++ false ::
      List.replicate first.length true) [] []
  simp only [List.append_nil]
    at hfirstPrefix hfirstPayload hsecond
  have h01 := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step
    _ _ _ _ _ hfirstPrefix hfirstPayload
  have hscan := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step
    _ _ _ _ _ h01 hsecond
  have hclean := flatAdjacentRecord_failureTrace []
    (first.reverse ++ false :: List.replicate first.length true)
    (List.replicate count true)
    (List.replicate count true)
  have hfull := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step
    _ _ _ _ _ hscan hclean
  have hbounded := rebound (newBudget := flatAdjacentRecordSwapTimePolynomial.eval
      (lengthPrefixedWord first ++
        List.replicate count true).length)
    hfull (by
      simp only [List.length_nil, List.length_append, List.length_reverse, List.length_cons,
          List.length_replicate,
          zero_add, lengthPrefixedWord_length, flatAdjacentRecordSwapTimePolynomial,
              Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X]
      omega)
  simpa only [FinTM2.step, Fin.isValue, lengthPrefixedWord, List.append_assoc, List.cons_append,
      List.length_append, List.length_replicate, List.length_cons] using hbounded

private def flatAdjacentRecord_shortSecondTotalTrace
    (first payload : List Bool) (extra : ℕ) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 0
        (lengthPrefixedWord first ++
          (List.replicate (payload.length + extra + 1) true ++
            false :: payload)) [] [] [])
      (some (Turing.haltList actualFlatAdjacentRecordSwapMachine []))
      (flatAdjacentRecordSwapTimePolynomial.eval
        (lengthPrefixedWord first ++
          (List.replicate (payload.length + extra + 1) true ++
            false :: payload)).length) := by
  have hfirstPrefix := flatAdjacentRecord_firstPrefixTrace
    first.length
    (first ++ (List.replicate (payload.length + extra + 1) true ++
      false :: payload)) [] [] []
  have hfirstPayload := flatAdjacentRecord_firstPayloadTrace
    first
    (List.replicate (payload.length + extra + 1) true ++
      false :: payload)
    (false :: List.replicate first.length true) []
  have hsecondPrefix := flatAdjacentRecord_secondPrefixTrace
    (payload.length + extra + 1) payload
    (first.reverse ++ false :: List.replicate first.length true)
    [] []
  have hsecondShort := flatAdjacentRecord_shortSecondPayloadTrace
    payload extra
    (first.reverse ++ false :: List.replicate first.length true)
    (false :: List.replicate (payload.length + extra + 1) true)
  simp only [List.append_nil]
    at hfirstPrefix hfirstPayload hsecondPrefix
  have h01 := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step
    _ _ _ _ _ hfirstPrefix hfirstPayload
  have h012 := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step
    _ _ _ _ _ h01 hsecondPrefix
  have hscan := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step
    _ _ _ _ _ h012 hsecondShort
  have hclean := flatAdjacentRecord_failureTrace []
    (first.reverse ++ false :: List.replicate first.length true)
    (payload.reverse ++ false ::
      List.replicate (payload.length + extra + 1) true)
    (List.replicate (extra + 1) true)
  have hfull := EvalsToInTime.trans actualFlatAdjacentRecordSwapMachine.step
    _ _ _ _ _ hscan hclean
  have hbounded := rebound (newBudget := flatAdjacentRecordSwapTimePolynomial.eval
      (lengthPrefixedWord first ++
        (List.replicate (payload.length + extra + 1) true ++
          false :: payload)).length)
    hfull (by
      simp only [List.length_nil, List.length_append, List.length_reverse, List.length_cons,
          List.length_replicate,
          zero_add, lengthPrefixedWord_length, flatAdjacentRecordSwapTimePolynomial,
              Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X]
      omega)
  simpa only [FinTM2.step, Fin.isValue, lengthPrefixedWord, List.append_assoc, List.cons_append,
      List.length_append, List.length_replicate, List.length_cons] using hbounded

/-- GapCVP reduction support. -/
noncomputable def flatAdjacentRecordTotalTrace
    (input : List Bool) :
    EvalsToInTime actualFlatAdjacentRecordSwapMachine.step
      (flatAdjacentRecordConfiguration 0 input [] [] [])
      (some (Turing.haltList actualFlatAdjacentRecordSwapMachine
        (flatAdjacentRecordSwapOutput input)))
      (flatAdjacentRecordSwapTimePolynomial.eval input.length) := by
  cases unaryInputSplit input with
  | inl missing =>
      obtain ⟨count, hshape⟩ := missing
      subst input
      have hphysical := flatAdjacentRecord_missingFirstTotalTrace count
      simpa only [FinTM2.step, Fin.isValue, flatAdjacentRecordSwapOutput,
          flatAdjacent_readLengthPrefixedWord_missing, List.length_replicate] using hphysical
  | inr firstInput =>
      obtain ⟨count, tail, hshape⟩ := firstInput
      subst input
      by_cases hfirst : count ≤ tail.length
      · have hreconstruct := validInput_reconstruct count tail hfirst
        cases unaryInputSplit (tail.drop count) with
        | inl missingSecond =>
            obtain ⟨secondCount, hsecondShape⟩ := missingSecond
            have hinput :
                List.replicate count true ++ false :: tail =
                  lengthPrefixedWord (tail.take count) ++
                    List.replicate secondCount true := by
              rw [hreconstruct, hsecondShape]
            rw [hinput]
            have hphysical := flatAdjacentRecord_missingSecondTotalTrace
              (tail.take count) secondCount
            simpa only [FinTM2.step, Fin.isValue, flatAdjacentRecordSwapOutput,
                readLengthPrefixedWord_append,
                flatAdjacent_readLengthPrefixedWord_missing, List.length_append,
                    lengthPrefixedWord_length, List.length_take,
                List.length_replicate] using hphysical
        | inr secondInput =>
            obtain ⟨secondCount, secondTail, hsecondShape⟩ := secondInput
            by_cases hsecond : secondCount ≤ secondTail.length
            · have hsecondReconstruct :=
                validInput_reconstruct secondCount secondTail hsecond
              have hinput :
                  List.replicate count true ++ false :: tail =
                    lengthPrefixedWord (tail.take count) ++
                      lengthPrefixedWord
                        (secondTail.take secondCount) ++
                      secondTail.drop secondCount := by
                rw [hreconstruct, hsecondShape,
                  hsecondReconstruct, List.append_assoc]
              rw [hinput]
              have hphysical := flatAdjacentRecord_validTrace
                (tail.take count)
                (secondTail.take secondCount)
                (secondTail.drop secondCount)
              have hbounded := rebound (newBudget := flatAdjacentRecordSwapTimePolynomial.eval
                  (lengthPrefixedWord (tail.take count) ++
                    lengthPrefixedWord
                      (secondTail.take secondCount) ++
                    secondTail.drop secondCount).length)
                hphysical (by
                  simp only [List.length_take, List.append_assoc, List.length_append,
                      lengthPrefixedWord_length,
                      List.length_drop, flatAdjacentRecordSwapTimePolynomial, Polynomial.eval_add,
                          Polynomial.eval_mul,
                      Polynomial.eval_ofNat, Polynomial.eval_X, Nat.reduceLeDiff]
                  omega)
              simpa only [FinTM2.step, Fin.isValue, List.append_assoc,
                  flatAdjacentRecordSwapOutput,
                  readLengthPrefixedWord_append, List.length_append, lengthPrefixedWord_length,
                      List.length_take,
                  List.length_drop] using hbounded
            · have hshort : secondTail.length < secondCount :=
                Nat.lt_of_not_ge hsecond
              let extra := secondCount - secondTail.length - 1
              have hcount :
                  secondCount = secondTail.length + extra + 1 := by
                dsimp [extra]
                omega
              have hinput :
                  List.replicate count true ++ false :: tail =
                    lengthPrefixedWord (tail.take count) ++
                      (List.replicate
                        (secondTail.length + extra + 1) true ++
                        false :: secondTail) := by
                rw [hreconstruct, hsecondShape, hcount]
              rw [hinput]
              have hphysical := flatAdjacentRecord_shortSecondTotalTrace
                (tail.take count) secondTail extra
              simpa only [FinTM2.step, Fin.isValue, flatAdjacentRecordSwapOutput,
                  readLengthPrefixedWord_append,
                  flatAdjacent_readLengthPrefixedWord_short, List.length_append,
                      lengthPrefixedWord_length, List.length_take,
                  List.length_replicate, List.length_cons] using hphysical
      · have hshort : tail.length < count :=
          Nat.lt_of_not_ge hfirst
        let extra := count - tail.length - 1
        have hcount : count = tail.length + extra + 1 := by
          dsimp [extra]
          omega
        rw [hcount]
        have hphysical := flatAdjacentRecord_shortFirstTotalTrace
          tail extra
        simpa only [FinTM2.step, Fin.isValue, flatAdjacentRecordSwapOutput,
            flatAdjacent_readLengthPrefixedWord_short,
            List.length_append, List.length_replicate, List.length_cons] using hphysical

/-- GapCVP reduction support. -/
noncomputable abbrev flatAdjacentRecordSwapComputable :
    BitTM
      flatAdjacentRecordSwapOutput where
  tm := actualFlatAdjacentRecordSwapMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := flatAdjacentRecordSwapTimePolynomial
  outputsFun input := {
    steps := (flatAdjacentRecordTotalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun,
              actualFlatAdjacentRecordSwapMachine_init,
          Option.map_some] using (flatAdjacentRecordTotalTrace input).evals_in_steps
    steps_le_m := by
      change (flatAdjacentRecordTotalTrace input).steps ≤
        flatAdjacentRecordSwapTimePolynomial.eval input.length
      exact (flatAdjacentRecordTotalTrace input).steps_le_m
  }

private def flatFieldSeparatorDropOutput (input : List Bool) : List Bool :=
  (flatAdjacentRecordSwapOutput input).tail

private noncomputable def flatFieldSeparatorDropComputable :
    BitTM
      flatFieldSeparatorDropOutput := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    flatAdjacentRecordSwapComputable dropHeadComputable
  change BitTM
    (fun input => (flatAdjacentRecordSwapOutput input).tail)
  simpa only [Function.comp_def] using hphysical

@[simp] private theorem flatFieldSeparatorDropOutput_valid
    (payload original : List Bool) :
    flatFieldSeparatorDropOutput
      (lengthPrefixedWord payload ++ false :: original) =
        lengthPrefixedWord payload ++ original := by
  change
    (flatAdjacentRecordSwapOutput
      (lengthPrefixedWord payload ++ false :: original)).tail =
      lengthPrefixedWord payload ++ original
  have hswap := flatAdjacentRecordSwapOutput_records
    payload [] original
  simpa only [lengthPrefixedWord, List.append_assoc, List.cons_append, List.length_nil,
      List.replicate_zero,
      List.nil_append, List.tail_cons] using congrArg List.tail hswap

end CNFFlatAdjacentRecordSwapTotalCert

namespace CNFFlatPhysicalBinaryAppendTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CLStructuralPrefixWriter GapCVP.SourceOriginalSourcePreservingTM
open GapCVP.SourceWholeOutputValidBranchRecordTM GapCVP.CNFFlatAdjacentRecordSwapTotalCert

/-- GapCVP reduction support. -/
def flatPhysicalPrependComputedRecordOutput
    (worker : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  flatFieldSeparatorDropOutput
    (originalSourcePreservingOutput
      (fun source => lengthPrefixedWord (worker source)) input)

/-- GapCVP reduction support. -/
noncomputable def flatPhysicalPrependComputedRecordComputable
    {worker : List Bool → List Bool}
    (computer : BitTM worker) :
    BitTM
      (flatPhysicalPrependComputedRecordOutput worker) := by
  have hrecord := GapCVP.TMComposition.computableInPolyTime
    computer structuralPrefixWriterComputable
  have hpreserved := originalSourcePreservingComputable hrecord
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hpreserved flatFieldSeparatorDropComputable
  change BitTM
    (fun input : List Bool => flatFieldSeparatorDropOutput
      (originalSourcePreservingOutput
        (fun source => lengthPrefixedWord (worker source)) input))
  simpa only [Function.comp_def] using hphysical

@[simp] theorem flatPhysicalPrependComputedRecordOutput_eq
    (worker : List Bool → List Bool) (input : List Bool) :
    flatPhysicalPrependComputedRecordOutput worker input =
      lengthPrefixedWord (worker input) ++ input := by
  unfold flatPhysicalPrependComputedRecordOutput
    originalSourcePreservingOutput
  exact flatFieldSeparatorDropOutput_valid (worker input) input

private def flatPhysicalFirstFieldWorker
    (worker : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  worker (firstFieldContents input)

private noncomputable def flatPhysicalFirstFieldWorkerComputable
    {worker : List Bool → List Bool}
    (computer : BitTM worker) :
    BitTM
      (flatPhysicalFirstFieldWorker worker) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable computer
  change BitTM
    (fun input : List Bool => worker (firstFieldContents input))
  simpa only [Function.comp_def] using hphysical

private def flatPhysicalSecondFieldWorker
    (worker : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  worker (firstFieldContents (firstFieldSuffix input))

private noncomputable def flatPhysicalSecondFieldWorkerComputable
    {worker : List Bool → List Bool}
    (computer : BitTM worker) :
    BitTM
      (flatPhysicalSecondFieldWorker worker) := by
  have hcontents := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hcontents computer
  change BitTM
    (fun input : List Bool =>
      worker (firstFieldContents (firstFieldSuffix input)))
  simpa only [Function.comp_def] using hphysical

private def flatPhysicalBinaryAppendOutput
    (first second : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  firstFieldSuffix
    (sourceFlatAtomicRecordStep
      (sourceFlatAtomicRecordStep
        (flatPhysicalPrependComputedRecordOutput
          (flatPhysicalSecondFieldWorker first)
          (flatPhysicalPrependComputedRecordOutput
            (flatPhysicalFirstFieldWorker second)
            (lengthPrefixedWord input)))))

private noncomputable def flatPhysicalBinaryAppendComputable
    {first second : List Bool → List Bool}
    (firstComputer : BitTM first)
    (secondComputer : BitTM second) :
    BitTM
      (flatPhysicalBinaryAppendOutput first second) := by
  have hsecond := flatPhysicalPrependComputedRecordComputable
    (flatPhysicalFirstFieldWorkerComputable secondComputer)
  have hfirst := flatPhysicalPrependComputedRecordComputable
    (flatPhysicalSecondFieldWorkerComputable firstComputer)
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    structuralPrefixWriterComputable hsecond
  have hboth := GapCVP.TMComposition.computableInPolyTime
    hprefix hfirst
  have hrotateFirst := GapCVP.TMComposition.computableInPolyTime
    hboth sourceFlatAtomicRecordComputable
  have hrotateSecond := GapCVP.TMComposition.computableInPolyTime
    hrotateFirst sourceFlatAtomicRecordComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hrotateSecond firstFieldSuffixComputable
  change BitTM
    (fun input : List Bool =>
      firstFieldSuffix
        (sourceFlatAtomicRecordStep
          (sourceFlatAtomicRecordStep
            (flatPhysicalPrependComputedRecordOutput
              (flatPhysicalSecondFieldWorker first)
              (flatPhysicalPrependComputedRecordOutput
                (flatPhysicalFirstFieldWorker second)
                (lengthPrefixedWord input))))))
  simpa only [flatPhysicalPrependComputedRecordOutput_eq, Function.comp_def] using hphysical

@[simp] private theorem flatPhysicalBinaryAppendOutput_eq
    (first second : List Bool → List Bool)
    (input : List Bool) :
    flatPhysicalBinaryAppendOutput first second input =
      first input ++ second input := by
  have hcontents : firstFieldContents (lengthPrefixedWord input) =
      input := by
    simpa only [List.append_nil] using firstFieldContents_valid input []
  unfold flatPhysicalBinaryAppendOutput
  simp only [sourceFlatAtomicRecordStep, flatPhysicalPrependComputedRecordOutput_eq,
      flatPhysicalFirstFieldWorker, hcontents, flatPhysicalSecondFieldWorker,
          firstFieldSuffix_valid,
      readLengthPrefixedWord_append, List.append_assoc]

/-- GapCVP reduction support. -/
noncomputable def pointwiseAppendComputable
    {first second : List Bool → List Bool}
    (firstComputer : BitTM first)
    (secondComputer : BitTM second) :
    BitTM
      (fun input => first input ++ second input) := by
  have hphysical := flatPhysicalBinaryAppendComputable
    firstComputer secondComputer
  have heq :
      flatPhysicalBinaryAppendOutput first second =
        (fun input => first input ++ second input) := by
    funext input
    exact flatPhysicalBinaryAppendOutput_eq first second input
  rwa [heq] at hphysical

end CNFFlatPhysicalBinaryAppendTM

namespace CNFCappedUnaryMinimumTM

open Turing GapCVP.BinaryEncoding GapCVP.CNFUnaryPairIndexTM

/-- GapCVP reduction support. -/
def cappedUnaryMinimumOutput (input : List Bool) : List Bool :=
  match readUnaryPrefix input with
  | none => []
  | some (first, remaining) =>
      match readUnaryPrefix remaining with
      | none => []
      | some (second, _) =>
          List.replicate (min first second) true

@[simp] theorem cappedUnaryMinimumOutput_pair
    (first second : ℕ) (suffix : List Bool) :
    cappedUnaryMinimumOutput
      (unarySourcePairWord first second ++ suffix) =
      List.replicate (min first second) true := by
  simp only [cappedUnaryMinimumOutput, unarySourcePairWord, List.append_assoc, List.cons_append,
      List.nil_append, readUnaryPrefix_replicate]

private def cappedUnaryMinimumPeek (stack : Fin 3)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  .peek stack (fun _ inspected => inspected)
    (.branch (fun inspected => inspected.isSome) present absent)

private def cappedUnaryMinimumPop (stack : Fin 3)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  .pop stack (fun inspected _ => inspected) continuation

private def cappedUnaryMinimumPush (stack : Fin 3) (bit : Bool)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  .push stack (fun _ => bit) continuation

private def cappedUnaryMinimumGoto (phase : Fin 4) :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => phase))

/-- Internal support shared across GapCVP continuation modules. -/
def cappedUnaryMinimumFirstStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  cappedUnaryMinimumPeek 0
    (.branch (fun inspected => inspected.getD false)
      (cappedUnaryMinimumPop 0
        (cappedUnaryMinimumPush 1 true
          (cappedUnaryMinimumGoto 0)))
      (cappedUnaryMinimumPop 0
        (cappedUnaryMinimumGoto 1)))
    (cappedUnaryMinimumGoto 3)

/-- Internal support shared across GapCVP continuation modules. -/
def cappedUnaryMinimumSecondStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  cappedUnaryMinimumPeek 0
    (.branch (fun inspected => inspected.getD false)
      (cappedUnaryMinimumPeek 1
        (cappedUnaryMinimumPop 0
          (cappedUnaryMinimumPop 1
            (cappedUnaryMinimumPush 2 true
              (cappedUnaryMinimumGoto 1))))
        (cappedUnaryMinimumPop 0
          (cappedUnaryMinimumGoto 1)))
      (cappedUnaryMinimumPop 0
        (cappedUnaryMinimumGoto 2)))
    (cappedUnaryMinimumGoto 3)

/-- Internal support shared across GapCVP continuation modules. -/
def cappedUnaryMinimumSuccessStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  cappedUnaryMinimumPeek 0
    (cappedUnaryMinimumPop 0 (cappedUnaryMinimumGoto 2))
    (cappedUnaryMinimumPeek 1
      (cappedUnaryMinimumPop 1 (cappedUnaryMinimumGoto 2))
      .halt)

/-- Internal support shared across GapCVP continuation modules. -/
def cappedUnaryMinimumFailureStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  cappedUnaryMinimumPeek 0
    (cappedUnaryMinimumPop 0 (cappedUnaryMinimumGoto 3))
    (cappedUnaryMinimumPeek 1
      (cappedUnaryMinimumPop 1 (cappedUnaryMinimumGoto 3))
      (cappedUnaryMinimumPeek 2
        (cappedUnaryMinimumPop 2 (cappedUnaryMinimumGoto 3))
        .halt))

/-- Internal support shared across GapCVP continuation modules. -/
abbrev actualCappedUnaryMinimumMachine : Turing.FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Fin 4
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 4) then
      cappedUnaryMinimumFirstStatement
    else if phase = (1 : Fin 4) then
      cappedUnaryMinimumSecondStatement
    else if phase = (2 : Fin 4) then
      cappedUnaryMinimumSuccessStatement
    else
      cappedUnaryMinimumFailureStatement

/-- Internal support shared across GapCVP continuation modules. -/
def cappedUnaryMinimumConfiguration
    (phase : Fin 4) (input first output : List Bool) :
    actualCappedUnaryMinimumMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, first, output]

/-- Internal support shared across GapCVP continuation modules. -/
theorem actualCappedUnaryMinimumMachine_init
    (input : List Bool) :
    Turing.initList actualCappedUnaryMinimumMachine input =
      cappedUnaryMinimumConfiguration 0 input [] [] := by
  simp only [actualCappedUnaryMinimumMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq,
      dite_eq_ite,
      cappedUnaryMinimumConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `cappedUnaryMinimumStepTac` machine-step simplifier. -/
macro "cappedUnaryMinimumStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [actualCappedUnaryMinimumMachine,
          cappedUnaryMinimumConfiguration,
          cappedUnaryMinimumPeek,
          cappedUnaryMinimumPop,
          cappedUnaryMinimumPush,
          cappedUnaryMinimumGoto,
          cappedUnaryMinimumFirstStatement,
          cappedUnaryMinimumSecondStatement,
          cappedUnaryMinimumSuccessStatement,
          cappedUnaryMinimumFailureStatement,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

/-- Internal support shared across GapCVP continuation modules. -/
theorem cappedUnaryMinimum_first_true
    (input first output : List Bool) :
    actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 0
        (true :: input) first output) =
      some (cappedUnaryMinimumConfiguration 0
        input (true :: first) output) := by
  cappedUnaryMinimumStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem cappedUnaryMinimum_first_false
    (input first output : List Bool) :
    actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 0
        (false :: input) first output) =
      some (cappedUnaryMinimumConfiguration 1
        input first output) := by
  cappedUnaryMinimumStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem cappedUnaryMinimum_first_missing
    (first output : List Bool) :
    actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 0 [] first output) =
      some (cappedUnaryMinimumConfiguration 3
        [] first output) := by
  cappedUnaryMinimumStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem cappedUnaryMinimum_second_true_counter
    (input first output : List Bool) :
    actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 1
        (true :: input) (true :: first) output) =
      some (cappedUnaryMinimumConfiguration 1
        input first (true :: output)) := by
  cappedUnaryMinimumStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem cappedUnaryMinimum_second_true_empty
    (input output : List Bool) :
    actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 1
        (true :: input) [] output) =
      some (cappedUnaryMinimumConfiguration 1
        input [] output) := by
  cappedUnaryMinimumStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem cappedUnaryMinimum_second_false
    (input first output : List Bool) :
    actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 1
        (false :: input) first output) =
      some (cappedUnaryMinimumConfiguration 2
        input first output) := by
  cappedUnaryMinimumStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem cappedUnaryMinimum_second_missing
    (first output : List Bool) :
    actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 1 [] first output) =
      some (cappedUnaryMinimumConfiguration 3
        [] first output) := by
  cappedUnaryMinimumStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem cappedUnaryMinimum_success_input
    (bit : Bool) (input first output : List Bool) :
    actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 2
        (bit :: input) first output) =
      some (cappedUnaryMinimumConfiguration 2
        input first output) := by
  cases bit <;> cappedUnaryMinimumStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem cappedUnaryMinimum_success_first
    (bit : Bool) (first output : List Bool) :
    actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 2
        [] (bit :: first) output) =
      some (cappedUnaryMinimumConfiguration 2
        [] first output) := by
  cases bit <;> cappedUnaryMinimumStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem cappedUnaryMinimum_success_finish
    (output : List Bool) :
    actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 2 [] [] output) =
      some (Turing.haltList actualCappedUnaryMinimumMachine
        output) := by
  cappedUnaryMinimumStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem cappedUnaryMinimum_failure_input
    (bit : Bool) (input first output : List Bool) :
    actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 3
        (bit :: input) first output) =
      some (cappedUnaryMinimumConfiguration 3
        input first output) := by
  cases bit <;> cappedUnaryMinimumStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem cappedUnaryMinimum_failure_first
    (bit : Bool) (first output : List Bool) :
    actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 3
        [] (bit :: first) output) =
      some (cappedUnaryMinimumConfiguration 3
        [] first output) := by
  cases bit <;> cappedUnaryMinimumStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem cappedUnaryMinimum_failure_output
    (bit : Bool) (output : List Bool) :
    actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 3
        [] [] (bit :: output)) =
      some (cappedUnaryMinimumConfiguration 3
        [] [] output) := by
  cases bit <;> cappedUnaryMinimumStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem cappedUnaryMinimum_failure_finish :
    actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 3 [] [] []) =
      some (Turing.haltList actualCappedUnaryMinimumMachine
        []) := by
  cappedUnaryMinimumStepTac

end CNFCappedUnaryMinimumTM

end GapCVP

end
