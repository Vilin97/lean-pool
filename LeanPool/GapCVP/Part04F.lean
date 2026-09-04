/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part04E

/-! # GapCVP proof, part 04, continuation 06 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFFlatStructuralRecordWorkerTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder

open GapCVP.OutputBoundedDependentRecordFold GapCVP.CNFTypedRecordWorkerTM

private def flatLiteralRecord_prefixTrace
    (sign : Option Bool) (count : ℕ)
    (tail counter reversed markers suffix output : List Bool) :
    EvalsToInTime actualFlatLiteralRecordWorker.step (flatLiteralRecordConfiguration 0 sign
        (List.replicate count true ++ false :: tail)
        counter reversed markers suffix output)
      (some (flatLiteralRecordConfiguration 1 sign
        tail (List.replicate count true ++ counter)
        reversed markers suffix output))
      (count + 1) := by
  induction count generalizing counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (flatLiteralRecord_prefix_false sign tail counter reversed markers suffix
              output)
  | succ count ih =>
      have hfirst := oneStep _ _ (flatLiteralRecord_prefix_true sign
          (List.replicate count true ++ false :: tail)
          counter reversed markers suffix output)
      have hrest := ih (true :: counter)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _ hfirst hrest

private def flatLiteralRecord_missingPrefixTrace
    (sign : Option Bool) (count : ℕ)
    (counter reversed markers suffix output : List Bool) :
    EvalsToInTime actualFlatLiteralRecordWorker.step (flatLiteralRecordConfiguration 0 sign
        (List.replicate count true)
        counter reversed markers suffix output)
      (some (flatLiteralRecordConfiguration 7 sign
        [] (List.replicate count true ++ counter)
        reversed markers suffix output))
      (count + 1) := by
  induction count generalizing counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (flatLiteralRecord_prefix_missing sign counter reversed markers suffix
              output)
  | succ count ih =>
      have hfirst := oneStep _ _ (flatLiteralRecord_prefix_true sign
          (List.replicate count true)
          counter reversed markers suffix output)
      have hrest := ih (true :: counter)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _ hfirst hrest

private def flatLiteralRecord_payloadTrace
    (sign : Bool) (payload input reversed markers suffix output : List Bool) :
    EvalsToInTime actualFlatLiteralRecordWorker.step (flatLiteralRecordConfiguration 2 (some sign)
        (payload ++ input) (List.replicate payload.length true)
        reversed markers suffix output)
      (some (flatLiteralRecordConfiguration 3 (some sign)
        input [] (payload.reverse ++ reversed)
        (List.replicate payload.length true ++ markers)
        suffix (sign :: output)))
      (payload.length + 1) := by
  induction payload generalizing reversed markers with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.nil_append, List.length_nil, List.replicate_zero,
          List.reverse_nil,
          zero_add] using oneStep _ _ (flatLiteralRecord_payload_finish sign input reversed markers
              suffix output)
  | cons bit payload ih =>
      have hfirst := oneStep _ _ (flatLiteralRecord_payload_step (some sign) bit true
          (payload ++ input) (List.replicate payload.length true)
          reversed markers suffix output)
      have hrest := ih (bit :: reversed) (true :: markers)
      simpa only [FinTM2.step, Fin.isValue, List.cons_append, List.length_cons,
          List.replicate_succ,
          List.reverse_cons, List.append_assoc, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _ hfirst hrest

private def flatLiteralRecord_restoreTrace
    (sign : Option Bool)
    (input reversed markers suffix output : List Bool) :
    EvalsToInTime actualFlatLiteralRecordWorker.step (flatLiteralRecordConfiguration 3 sign
        input [] reversed markers suffix output)
      (some (flatLiteralRecordConfiguration 4 sign
        input [] [] markers suffix
        (false :: (reversed.reverse ++ output))))
      (reversed.length + 1) := by
  induction reversed generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (flatLiteralRecord_restore_finish sign input markers suffix output)
  | cons bit reversed ih =>
      have hfirst := oneStep _ _ (flatLiteralRecord_restore_step sign bit
          input reversed markers suffix output)
      have hrest := ih (bit :: output)
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using
          EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _ hfirst hrest

private def flatLiteralRecord_markerTrace
    (sign : Option Bool)
    (input markers suffix output : List Bool) :
    EvalsToInTime actualFlatLiteralRecordWorker.step (flatLiteralRecordConfiguration 4 sign
        input [] [] markers suffix output)
      (some (flatLiteralRecordConfiguration 5 sign
        input [] [] [] suffix
        (List.replicate markers.length true ++ output)))
      (markers.length + 1) := by
  induction markers generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, List.replicate_zero, List.nil_append,
          zero_add] using
          oneStep _ _ (flatLiteralRecord_marker_finish sign input suffix output)
  | cons bit markers ih =>
      have hfirst := oneStep _ _ (flatLiteralRecord_marker_step sign bit
          input markers suffix output)
      have hrest := ih (true :: output)
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, List.replicate_succ,
          List.cons_append, Nat.add_assoc,
          Nat.reduceAdd, SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _ hfirst hrest

private def flatLiteralRecord_suffixScanTrace
    (sign : Option Bool)
    (input suffix output : List Bool) :
    EvalsToInTime actualFlatLiteralRecordWorker.step (flatLiteralRecordConfiguration 5 sign
        input [] [] [] suffix output)
      (some (flatLiteralRecordConfiguration 6 sign
        [] [] [] [] (input.reverse ++ suffix) output))
      (input.length + 1) := by
  induction input generalizing suffix with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (flatLiteralRecord_suffix_scan_finish sign suffix output)
  | cons bit input ih =>
      have hfirst := oneStep _ _ (flatLiteralRecord_suffix_scan_step sign bit
          input suffix output)
      have hrest := ih (bit :: suffix)
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using
          EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _ hfirst hrest

private def flatLiteralRecord_suffixRestoreTrace
    (sign : Option Bool) (suffix output : List Bool) :
    EvalsToInTime actualFlatLiteralRecordWorker.step (flatLiteralRecordConfiguration 6 sign
        [] [] [] [] suffix output)
      (some (Turing.haltList actualFlatLiteralRecordWorker
        (suffix.reverse ++ output)))
      (suffix.length + 1) := by
  induction suffix generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (flatLiteralRecord_suffix_restore_finish sign output)
  | cons bit suffix ih =>
      have hfirst := oneStep _ _ (flatLiteralRecord_suffix_restore_step sign bit suffix output)
      have hrest := ih (bit :: output)
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using
          EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _ hfirst hrest

private def flatLiteralRecord_invalidTrace
    (sign : Option Bool)
    (input count reversed markers : List Bool) :
    EvalsToInTime actualFlatLiteralRecordWorker.step (flatLiteralRecordConfiguration 7 sign
        input count reversed markers [] [])
      (some (Turing.haltList actualFlatLiteralRecordWorker []))
      (input.length + count.length + reversed.length +
        markers.length + 1) := by
  induction count generalizing input reversed markers with
  | cons bit count ih =>
      have hfirst := oneStep _ _ (flatLiteralRecord_invalid_count sign bit
          input count reversed markers)
      have hrest := ih input reversed markers
      exact rebound (EvalsToInTime.trans
          actualFlatLiteralRecordWorker.step _ _ _ _ _ hfirst hrest)
        (by simp only [List.length_cons, add_le_add_iff_right, Order.add_one_le_iff,
            add_lt_add_iff_right,
                add_lt_add_iff_left, lt_add_iff_pos_right, Order.lt_one_iff])
  | nil =>
      induction reversed generalizing input markers with
      | cons bit reversed ih =>
          have hfirst := oneStep _ _ (flatLiteralRecord_invalid_reversed sign bit
              input reversed markers)
          have hrest := ih input markers
          exact rebound (EvalsToInTime.trans
              actualFlatLiteralRecordWorker.step _ _ _ _ _ hfirst hrest)
            (by simp only [List.length_nil, add_zero, List.length_cons, add_le_add_iff_right,
                Order.add_one_le_iff,
                    add_lt_add_iff_right, add_lt_add_iff_left, lt_add_iff_pos_right,
                        Order.lt_one_iff])
      | nil =>
          induction markers generalizing input with
          | cons bit markers ih =>
              have hfirst := oneStep _ _ (flatLiteralRecord_invalid_markers sign bit input markers)
              have hrest := ih input
              exact rebound (EvalsToInTime.trans
                  actualFlatLiteralRecordWorker.step _ _ _ _ _
                  hfirst hrest)
                (by simp only [List.length_nil, add_zero, List.length_cons, add_le_add_iff_right,
                    Order.add_one_le_iff,
                        add_lt_add_iff_left, lt_add_iff_pos_right, Order.lt_one_iff])
          | nil =>
              induction input with
              | nil =>
                  simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero, zero_add] using
                      oneStep _ _ (flatLiteralRecord_invalid_finish sign)
              | cons bit input ih =>
                  have hfirst := oneStep _ _ (flatLiteralRecord_invalid_input sign bit input)
                  exact rebound (EvalsToInTime.trans
                      actualFlatLiteralRecordWorker.step _ _ _ _ _
                      hfirst ih)
                    (by simp only [List.length_nil, add_zero, List.length_cons, Std.le_refl])

private def flatLiteralRecord_truncatedPayloadTrace
    (sign : Bool) (payload : List Bool) (count : ℕ)
    (hshort : payload.length < count)
    (reversed markers : List Bool) :
    EvalsToInTime actualFlatLiteralRecordWorker.step (flatLiteralRecordConfiguration 2 (some sign)
        payload (List.replicate count true)
        reversed markers [] [])
      (some (flatLiteralRecordConfiguration 7 (some sign)
        [] (List.replicate (count - payload.length) true)
        (payload.reverse ++ reversed)
        (List.replicate payload.length true ++ markers) [] []))
      (payload.length + 1) := by
  induction payload generalizing count reversed markers with
  | nil =>
      cases count with
      | zero => simp only [List.length_nil, lt_self_iff_false] at hshort
      | succ count =>
          simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.length_nil, tsub_zero,
              List.reverse_nil,
              List.nil_append, List.replicate_zero, zero_add] using
              oneStep _ _ (flatLiteralRecord_payload_missing (some sign) true (List.replicate count
                  true) reversed markers [] [])
  | cons bit payload ih =>
      cases count with
      | zero => simp only [List.length_cons, not_lt_zero] at hshort
      | succ count =>
          have hcount : payload.length < count := by
            simp only [List.length_cons] at hshort
            omega
          have hfirst := oneStep _ _ (flatLiteralRecord_payload_step (some sign) bit true
              payload (List.replicate count true)
              reversed markers [] [])
          have hrest := ih count hcount
            (bit :: reversed) (true :: markers)
          simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.length_cons,
              Nat.reduceSubDiff,
              List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
                  Nat.add_assoc, Nat.reduceAdd,
              SourceStructuralDecoder.replicate_true_append_cons] using
              EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _ hfirst hrest

private def flatLiteralRecord_validTrace
    (sign : Bool) (payload suffix : List Bool) :
    EvalsToInTime actualFlatLiteralRecordWorker.step (flatLiteralRecordConfiguration 0 none
        (lengthPrefixedWord (sign :: payload) ++ suffix)
        [] [] [] [] [])
      (some (Turing.haltList actualFlatLiteralRecordWorker
        (suffix ++ lengthPrefixedWord payload ++ [sign])))
      (8 * (lengthPrefixedWord (sign :: payload) ++ suffix).length +
        16) := by
  have hprefix := flatLiteralRecord_prefixTrace
    none (payload.length + 1)
    (sign :: (payload ++ suffix)) [] [] [] [] []
  simp only [List.append_nil, List.replicate_succ] at hprefix
  have hsign := oneStep _ _ (flatLiteralRecord_sign_step none sign true
      (payload ++ suffix)
      (List.replicate payload.length true) [] [] [] [])
  have hpayload := flatLiteralRecord_payloadTrace
    sign payload suffix [] [] [] []
  simp only [List.append_nil] at hpayload
  have hrestore := flatLiteralRecord_restoreTrace
    (some sign) suffix payload.reverse
    (List.replicate payload.length true) [] [sign]
  simp only [List.reverse_reverse] at hrestore
  have hmarkers := flatLiteralRecord_markerTrace
    (some sign) suffix (List.replicate payload.length true)
    [] (false :: (payload ++ [sign]))
  simp only [List.length_replicate] at hmarkers
  have hsuffixScan := flatLiteralRecord_suffixScanTrace
    (some sign) suffix []
    (List.replicate payload.length true ++
      false :: (payload ++ [sign]))
  simp only [List.append_nil] at hsuffixScan
  have hsuffixRestore := flatLiteralRecord_suffixRestoreTrace
    (some sign) suffix.reverse
    (List.replicate payload.length true ++
      false :: (payload ++ [sign]))
  simp only [List.reverse_reverse, List.length_reverse] at hsuffixRestore
  have hprefixSign := EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _
    hprefix hsign
  have hprefixPayload := EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _
    hprefixSign hpayload
  have hprefixRestore := EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _
    hprefixPayload hrestore
  have hprefixMarkers := EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _
    hprefixRestore hmarkers
  have hprefixSuffix := EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _
    hprefixMarkers hsuffixScan
  have hfull := EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _
    hprefixSuffix hsuffixRestore
  have hbounded := rebound (newBudget :=
      8 * (lengthPrefixedWord (sign :: payload) ++ suffix).length +
        16) hfull (by
      simp only [List.length_reverse, lengthPrefixedWord, List.length_cons, List.append_assoc,
          List.cons_append,
          List.length_append, List.length_replicate]
      omega)
  simpa only [FinTM2.step, Fin.isValue, lengthPrefixedWord, List.length_cons, List.replicate_succ,
      List.cons_append, List.append_assoc, List.length_append, List.length_replicate]
          using hbounded

private def flatLiteralRecord_totalTrace (input : List Bool) :
    EvalsToInTime actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 0 none input [] [] [] [] [])
      (some (Turing.haltList actualFlatLiteralRecordWorker
        (flatLiteralRecordStep input)))
      (20 * input.length + 30) := by
  cases unaryInputSplit input with
  | inl witness =>
      obtain ⟨count, hinput⟩ := witness
      subst input
      have hprefix := flatLiteralRecord_missingPrefixTrace
        none count [] [] [] [] []
      simp only [List.append_nil] at hprefix
      have hclean := flatLiteralRecord_invalidTrace
        none [] (List.replicate count true) [] []
      have hfull := EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _
        hprefix hclean
      have hbounded := rebound (newBudget :=
          20 * (List.replicate count true).length + 30)
        hfull (by simp only [List.length_nil, List.length_replicate, zero_add, add_zero]; omega)
      simpa only [FinTM2.step, Fin.isValue, flatLiteralRecordStep, readLengthPrefixedWord,
          readUnaryPrefix_missing,
          List.length_replicate] using hbounded
  | inr witness =>
      obtain ⟨count, tail, hinput⟩ := witness
      subst input
      cases count with
      | zero =>
          have hprefix := flatLiteralRecord_prefixTrace
            none 0 tail [] [] [] [] []
          have hsign := oneStep _ _ (flatLiteralRecord_sign_empty none tail [] [] [] [])
          have hclean := flatLiteralRecord_invalidTrace
            none tail [] [] []
          have hfirst := EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _
            hprefix hsign
          have hfull := EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _
            hfirst hclean
          have hbounded := rebound (newBudget :=
              20 * (List.replicate 0 true ++ false :: tail).length +
                30)
            hfull (by simp only [List.length_nil, add_zero, zero_add, Nat.reduceAdd,
                List.replicate_zero, List.nil_append,
                          List.length_cons, add_le_add_iff_right]; omega)
          simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append,
              flatLiteralRecordStep,
              readLengthPrefixedWord, readUnaryPrefix, zero_le, ↓reduceIte, List.take_zero,
                  List.drop_zero,
              List.length_cons] using hbounded
      | succ count =>
          cases tail with
          | nil =>
              have hprefix := flatLiteralRecord_prefixTrace
                none (count + 1) [] [] [] [] [] []
              simp only [List.append_nil,
                List.replicate_succ] at hprefix
              have hsign := oneStep _ _ (flatLiteralRecord_sign_missing none true
                  (List.replicate count true) [] [] [] [])
              have hclean := flatLiteralRecord_invalidTrace
                none [] (true :: List.replicate count true) [] []
              have hfirst := EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _
                hprefix hsign
              have hfull := EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _
                hfirst hclean
              have hbounded := rebound (newBudget :=
                  20 * (List.replicate (count + 1) true ++
                    [false]).length + 30)
                hfull (by simp only [List.length_nil, List.length_cons, List.length_replicate,
                    zero_add, add_zero, List.length_append]; omega)
              have hempty :
                  flatLiteralRecordStep
                    (List.replicate (count + 1) true ++ [false]) = [] := by
                simp only [flatLiteralRecordStep, readLengthPrefixedWord,
                    readUnaryPrefix_replicate, List.length_nil,
                    nonpos_iff_eq_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
              rw [hempty]
              simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append,
                  List.length_cons,
                  List.length_append, List.length_replicate, List.length_nil, zero_add]
                      using hbounded
          | cons sign tail =>
              by_cases hlength : count ≤ tail.length
              · have houter :
                    count + 1 ≤ (sign :: tail).length := by
                    simp only [List.length_cons]
                    omega
                have hshape := validInput_reconstruct
                  (count + 1) (sign :: tail) houter
                have hshape' :
                    List.replicate (count + 1) true ++
                      false :: sign :: tail =
                    lengthPrefixedWord
                        (sign :: tail.take count) ++
                      tail.drop count := by
                  simpa only [List.take_succ_cons, List.drop_succ_cons] using hshape
                rw [hshape']
                have hvalid := flatLiteralRecord_validTrace
                  sign (tail.take count) (tail.drop count)
                have hbounded := rebound (newBudget :=
                    20 * (lengthPrefixedWord
                      (sign :: tail.take count) ++
                      tail.drop count).length + 30)
                  hvalid (by omega)
                simpa only [FinTM2.step, Fin.isValue, flatLiteralRecordStep,
                    readLengthPrefixedWord_append, List.append_assoc,
                    List.length_append, lengthPrefixedWord_length, List.length_cons,
                        List.length_take, List.length_drop] using hbounded
              · have hshort : tail.length < count := by omega
                have hprefix := flatLiteralRecord_prefixTrace
                  none (count + 1) (sign :: tail)
                  [] [] [] [] []
                simp only [List.append_nil,
                  List.replicate_succ] at hprefix
                have hsign := oneStep _ _ (flatLiteralRecord_sign_step none sign true
                    tail (List.replicate count true)
                    [] [] [] [])
                have htruncated :=
                  flatLiteralRecord_truncatedPayloadTrace
                    sign tail count hshort [] []
                simp only [List.append_nil] at htruncated
                have hclean := flatLiteralRecord_invalidTrace
                  (some sign) []
                  (List.replicate (count - tail.length) true)
                  tail.reverse
                  (List.replicate tail.length true)
                have hfirst := EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _
                  hprefix hsign
                have hsecond := EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _
                  hfirst htruncated
                have hfull := EvalsToInTime.trans actualFlatLiteralRecordWorker.step _ _ _ _ _
                  hsecond hclean
                have hbounded := rebound (newBudget :=
                    20 * (List.replicate (count + 1) true ++
                      false :: sign :: tail).length + 30)
                  hfull (by
                    simp only [List.length_nil, List.length_replicate, zero_add,
                        List.length_reverse, List.length_append,
                        List.length_cons]
                    omega)
                have hempty :
                    flatLiteralRecordStep
                      (List.replicate (count + 1) true ++
                        false :: sign :: tail) = [] := by
                  simp only [flatLiteralRecordStep, readLengthPrefixedWord,
                      readUnaryPrefix_replicate, List.length_cons,
                      add_le_add_iff_right, hlength, ↓reduceIte]
                rw [hempty]
                simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append,
                    List.length_cons,
                    List.length_append, List.length_replicate] using hbounded

private noncomputable def actualFlatLiteralRecordWorkerComputable :
    BitTM
      flatLiteralRecordStep where
  tm := actualFlatLiteralRecordWorker
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 20 * Polynomial.X + 30
  outputsFun input := {
    steps := (flatLiteralRecord_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, actualFlatLiteralRecordWorker_init,
              Option.map_some] using
          (flatLiteralRecord_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (flatLiteralRecord_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq, Polynomial.eval_add,
          Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X, ge_iff_le] using hsteps
  }

private noncomputable def actualFlatLiteralRecordFoldComputable :
    BitTM
      (boundedRecordFoldOutput flatLiteralRecordStep) :=
  boundedDependentRecordFoldComputable
    actualFlatLiteralRecordWorkerComputable
    Polynomial.X
    flatLiteralRecordStep_polynomiallyBoundedFoldStates

/-- GapCVP reduction support. -/
def flatThreeClauseLiterals (clauses : ThreeCNF) : List Literal :=
  clauses.flatMap (fun clause => [clause 0, clause 1, clause 2])

@[simp] private theorem flatThreeClauseLiterals_length
    (clauses : ThreeCNF) :
    (flatThreeClauseLiterals clauses).length = 3 * clauses.length := by
  induction clauses with
  | nil => simp only [flatThreeClauseLiterals, Fin.isValue, List.flatMap_nil, List.length_nil,
      mul_zero]
  | cons clause remaining ih =>
      simp only [flatThreeClauseLiterals, Fin.isValue, List.length_flatMap, List.length_cons,
          List.length_nil,
          zero_add, Nat.reduceAdd, List.map_const', List.sum_replicate, smul_eq_mul,
              List.flatMap_cons, List.cons_append,
          List.nil_append] at ih ⊢
      omega

private theorem flatThreeClauseLiterals_encoded
    (clauses : ThreeCNF) :
    (flatThreeClauseLiterals clauses).flatMap encodeLiteral =
      clauses.flatMap encodeThreeClause := by
  induction clauses with
  | nil => simp only [flatThreeClauseLiterals, Fin.isValue, List.flatMap_nil]
  | cons clause remaining ih =>
      simpa only [flatThreeClauseLiterals, Fin.isValue, List.flatMap_cons, List.cons_append,
          List.nil_append,
          encodeThreeClause, List.append_assoc, List.append_cancel_left_eq] using ih

end CNFFlatStructuralRecordWorkerTM

namespace CNFFlatSourceOrder

open GapCVP.ThreeCNFReduction GapCVP.CNFEncodedClauseSort

private def flatSourceListValue : List ℕ → ℕ
  | [] => 0
  | head :: tail => Nat.succ (Nat.pair head (flatSourceListValue tail))

private theorem flatSourceListValue_map_encode
    {α : Type} [Encodable α] (records : List α) :
    flatSourceListValue (records.map Encodable.encode) =
      Encodable.encode records := by
  induction records with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, flatSourceListValue, ih, Nat.succ_eq_add_one,
          Encodable.encode_list_cons]

/-- GapCVP reduction support. -/
def cappedFlatSourceListValue (cap : ℕ) : List ℕ → ℕ
  | [] => 0
  | head :: tail =>
      min cap
        (Nat.succ
          (Nat.pair head (cappedFlatSourceListValue cap tail)))

private theorem cappedFlatSourceListValue_eq_min
    (cap : ℕ) (records : List ℕ) :
    cappedFlatSourceListValue cap records =
      min cap (flatSourceListValue records) := by
  induction records with
  | nil => simp only [cappedFlatSourceListValue, flatSourceListValue, zero_le, inf_of_le_right]
  | cons head tail ih =>
      simp only [cappedFlatSourceListValue, flatSourceListValue, ih]
      by_cases hcap : cap ≤ flatSourceListValue tail
      · have hleft :
            cap ≤ Nat.succ (Nat.pair head cap) :=
          (Nat.right_le_pair head cap).trans (Nat.le_succ _)
        have hright :
            cap ≤ Nat.succ
              (Nat.pair head (flatSourceListValue tail)) :=
          hcap.trans
            ((Nat.right_le_pair head (flatSourceListValue tail)).trans
              (Nat.le_succ _))
        simp only [Nat.min_eq_left hcap, Nat.succ_eq_add_one, Nat.min_eq_left hleft,
            Nat.min_eq_left hright]
      · have hle : flatSourceListValue tail ≤ cap :=
          Nat.le_of_lt (Nat.lt_of_not_ge hcap)
        simp only [Nat.min_eq_right hle, Nat.succ_eq_add_one]

/-- GapCVP reduction support. -/
def flatSourceNaturalOrdering (first second : ℕ) : EncodedWordOrdering :=
  if first < second then .less
  else if second < first then .greater
  else .equal

private theorem flatSourceNaturalOrdering_capped_right
    (literal : ℕ) (records : List ℕ) :
    flatSourceNaturalOrdering literal
        (cappedFlatSourceListValue (literal + 1) records) =
      flatSourceNaturalOrdering literal
        (flatSourceListValue records) := by
  rw [cappedFlatSourceListValue_eq_min]
  by_cases hvalue : flatSourceListValue records ≤ literal
  · have hcap :
        min (literal + 1) (flatSourceListValue records) =
          flatSourceListValue records :=
        Nat.min_eq_right (by omega)
    rw [hcap]
  · have hlt : literal < flatSourceListValue records := by omega
    have hcap :
        min (literal + 1) (flatSourceListValue records) = literal + 1 :=
        Nat.min_eq_left (by omega)
    rw [hcap]
    simp only [flatSourceNaturalOrdering, lt_add_iff_pos_right, Order.lt_one_iff, ↓reduceIte, hlt]

private theorem flatSourceNaturalOrdering_capped_left
    (records : List ℕ) (literal : ℕ) :
    flatSourceNaturalOrdering
        (cappedFlatSourceListValue (literal + 1) records) literal =
      flatSourceNaturalOrdering
        (flatSourceListValue records) literal := by
  rw [cappedFlatSourceListValue_eq_min]
  by_cases hvalue : flatSourceListValue records ≤ literal
  · have hcap :
        min (literal + 1) (flatSourceListValue records) =
          flatSourceListValue records :=
        Nat.min_eq_right (by omega)
    rw [hcap]
  · have hlt : literal < flatSourceListValue records := by omega
    have hcap :
        min (literal + 1) (flatSourceListValue records) = literal + 1 :=
        Nat.min_eq_left (by omega)
    rw [hcap]
    simp only [flatSourceNaturalOrdering, add_lt_iff_neg_left, not_lt_zero, ↓reduceIte,
        lt_add_iff_pos_right,
        Order.lt_one_iff, hlt, right_eq_ite_iff, reduceCtorEq, imp_false, not_lt, Nat.le_of_lt hlt]

/-- GapCVP reduction support. -/
def resolveFlatSourceOrder
    (major : EncodedWordOrdering) (first second : ℕ) :
    EncodedWordOrdering :=
  match major with
  | .equal => flatSourceNaturalOrdering first second
  | other => other

private theorem flatSourceSquareBlock_lt
    {firstMajor secondMajor firstOffset secondOffset : ℕ}
    (hfirst : firstOffset ≤ firstMajor)
    (_hsecond : secondOffset ≤ secondMajor)
    (hmajor : firstMajor < secondMajor) :
    firstMajor ^ 2 + firstOffset + 1 <
      secondMajor ^ 2 + secondOffset + 1 := by
  have hstep : firstMajor + 1 ≤ secondMajor := by omega
  have hsquare := Nat.mul_self_le_mul_self hstep
  linarith

private theorem flatSourceSquareBlock_ordering
    (firstMajor secondMajor firstOffset secondOffset : ℕ)
    (hfirst : firstOffset ≤ firstMajor)
    (hsecond : secondOffset ≤ secondMajor) :
    flatSourceNaturalOrdering
        (firstMajor ^ 2 + firstOffset + 1)
        (secondMajor ^ 2 + secondOffset + 1) =
      resolveFlatSourceOrder
        (flatSourceNaturalOrdering firstMajor secondMajor)
        firstOffset secondOffset := by
  rcases lt_trichotomy firstMajor secondMajor with hmajor | hmajor | hmajor
  · have hvalue := flatSourceSquareBlock_lt hfirst hsecond hmajor
    simp only [flatSourceNaturalOrdering, hvalue, ↓reduceIte, resolveFlatSourceOrder, hmajor]
  · subst secondMajor
    simp only [flatSourceNaturalOrdering, Order.lt_add_one_iff, Order.add_one_le_iff,
        add_lt_add_iff_left,
        resolveFlatSourceOrder, lt_self_iff_false, ↓reduceIte]
  · have hvalue := flatSourceSquareBlock_lt hsecond hfirst hmajor
    simp only [flatSourceNaturalOrdering, Nat.not_lt_of_gt hvalue, ↓reduceIte, hvalue,
        resolveFlatSourceOrder,
        Nat.not_lt_of_gt hmajor, hmajor]

private def flatSourceListMajor (head : ℕ) : List ℕ → ℕ
  | [] => head
  | next :: tail => flatSourceListValue (next :: tail)

private theorem flatSourceList_head_le_major
    (head : ℕ) (tail : List ℕ)
    (hsorted : (head :: tail).Pairwise (· ≤ ·)) :
    head ≤ flatSourceListMajor head tail := by
  cases tail with
  | nil => simp only [flatSourceListMajor, Std.le_refl]
  | cons next remaining =>
      have hnext : head ≤ next :=
        (List.pairwise_cons.mp hsorted).1 next (by simp only [List.mem_cons, true_or])
      have hp := Nat.left_le_pair next
        (flatSourceListValue remaining)
      simp only [flatSourceListMajor, flatSourceListValue]
      omega

private theorem flatSourceListValue_cons_eq_square
    (head : ℕ) (tail : List ℕ)
    (hsorted : (head :: tail).Pairwise (· ≤ ·)) :
    flatSourceListValue (head :: tail) =
      (flatSourceListMajor head tail) ^ 2 + head + 1 := by
  cases tail with
  | nil =>
      simp only [flatSourceListValue, Nat.pair, not_lt_zero, ↓reduceIte, add_zero,
          Nat.succ_eq_add_one,
        flatSourceListMajor, pow_two]
  | cons next remaining =>
      have hnext : head ≤ next :=
        (List.pairwise_cons.mp hsorted).1 next (by simp only [List.mem_cons, true_or])
      have hp := Nat.left_le_pair next
        (flatSourceListValue remaining)
      have hlt : head < flatSourceListValue (next :: remaining) := by
        simp only [flatSourceListValue]
        omega
      simp only [flatSourceListMajor]
      change
        Nat.succ
            (Nat.pair head (flatSourceListValue (next :: remaining))) =
          (flatSourceListValue (next :: remaining)) ^ 2 + head + 1
      rw [Nat.pair, ite_eq_left hlt, pow_two]

/-- GapCVP reduction support. -/
def flatSortedSourceListOrdering :
    List ℕ → List ℕ → EncodedWordOrdering
  | [], [] => .equal
  | [], _ :: _ => .less
  | _ :: _, [] => .greater
  | [head₁], [head₂] =>
      resolveFlatSourceOrder
        (flatSourceNaturalOrdering head₁ head₂)
        head₁ head₂
  | [head₁], head₂ :: next₂ :: tail₂ =>
      resolveFlatSourceOrder
        (flatSourceNaturalOrdering head₁
          (cappedFlatSourceListValue (head₁ + 1) (next₂ :: tail₂)))
        head₁ head₂
  | head₁ :: next₁ :: tail₁, [head₂] =>
      resolveFlatSourceOrder
        (flatSourceNaturalOrdering
          (cappedFlatSourceListValue (head₂ + 1) (next₁ :: tail₁))
          head₂)
        head₁ head₂
  | head₁ :: next₁ :: tail₁, head₂ :: next₂ :: tail₂ =>
      resolveFlatSourceOrder
        (flatSortedSourceListOrdering
          (next₁ :: tail₁) (next₂ :: tail₂))
        head₁ head₂
termination_by first second => first.length + second.length
decreasing_by simp_wf; omega

private theorem flatSortedSourceListOrdering_eq_godel
    (first second : List ℕ)
    (hfirst : first.Pairwise (· ≤ ·))
    (hsecond : second.Pairwise (· ≤ ·)) :
    flatSortedSourceListOrdering first second =
      flatSourceNaturalOrdering
        (flatSourceListValue first) (flatSourceListValue second) := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil =>
          simp only [flatSortedSourceListOrdering, flatSourceNaturalOrdering, flatSourceListValue,
              lt_self_iff_false,
              ↓reduceIte]
      | cons head tail =>
          simp only [flatSortedSourceListOrdering, flatSourceNaturalOrdering, flatSourceListValue,
              Nat.succ_eq_add_one,
              lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, ↓reduceIte]
  | cons firstHead firstTail ih =>
      cases second with
      | nil =>
          simp only [flatSortedSourceListOrdering, flatSourceNaturalOrdering, flatSourceListValue,
              Nat.succ_eq_add_one,
              not_lt_zero, ↓reduceIte, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le]
      | cons secondHead secondTail =>
          have hfirstMajor := flatSourceList_head_le_major
            firstHead firstTail hfirst
          have hsecondMajor := flatSourceList_head_le_major
            secondHead secondTail hsecond
          rw [flatSourceListValue_cons_eq_square
            firstHead firstTail hfirst,
            flatSourceListValue_cons_eq_square
              secondHead secondTail hsecond]
          rw [flatSourceSquareBlock_ordering _ _ _ _
            hfirstMajor hsecondMajor]
          cases firstTail with
          | nil =>
              cases secondTail with
              | nil =>
                  simp only [flatSortedSourceListOrdering, flatSourceListMajor]
              | cons next tail =>
                  simp only [flatSortedSourceListOrdering, flatSourceNaturalOrdering_capped_right,
                      flatSourceListMajor]
          | cons next tail =>
              cases secondTail with
              | nil =>
                  simp only [flatSortedSourceListOrdering, flatSourceNaturalOrdering_capped_left,
                      flatSourceListMajor]
              | cons other remaining =>
                  have hfirstTail :
                      (next :: tail).Pairwise (· ≤ ·) :=
                    (List.pairwise_cons.mp hfirst).2
                  have hsecondTail :
                      (other :: remaining).Pairwise (· ≤ ·) :=
                    (List.pairwise_cons.mp hsecond).2
                  simp only [flatSortedSourceListOrdering,
                    flatSourceListMajor]
                  rw [ih (other :: remaining)
                    hfirstTail hsecondTail]

/-- GapCVP reduction support. -/
def flatSourceFinsetCodes
    {α : Type} [Encodable α] (records : Finset α) : List ℕ :=
  (sortedElements records).map Encodable.encode

private theorem flatSourceFinsetCodes_value
    {α : Type} [Encodable α] (records : Finset α) :
    flatSourceListValue (flatSourceFinsetCodes records) =
      Encodable.encode records := by
  change
    flatSourceListValue
        ((sortedElements records).map Encodable.encode) =
      Encodable.encode records
  rw [flatSourceListValue_map_encode]
  rfl

private theorem flatSourceFinsetCodes_pairwise
    {α : Type} [Encodable α] (records : Finset α) :
    (flatSourceFinsetCodes records).Pairwise (· ≤ ·) := by
  let : IsTrans α
      (fun first second : α =>
        Encodable.encode first ≤ Encodable.encode second) :=
    ⟨fun _ _ _ hfirst hsecond => Nat.le_trans hfirst hsecond⟩
  let : Std.Antisymm
      (fun first second : α =>
        Encodable.encode first ≤ Encodable.encode second) :=
    ⟨fun _ _ hfirst hsecond =>
      Encodable.encode_injective (Nat.le_antisymm hfirst hsecond)⟩
  let : Std.Total
      (fun first second : α =>
        Encodable.encode first ≤ Encodable.encode second) :=
    ⟨fun _ _ => Nat.le_total _ _⟩
  simp only [flatSourceFinsetCodes, sortedElements, List.pairwise_map, Finset.pairwise_sort]

theorem flatSourceFinsetOrdering_eq_godel
    {α : Type} [Encodable α] (first second : Finset α) :
    flatSortedSourceListOrdering
        (flatSourceFinsetCodes first)
        (flatSourceFinsetCodes second) =
      flatSourceNaturalOrdering
        (Encodable.encode first) (Encodable.encode second) := by
  rw [flatSortedSourceListOrdering_eq_godel
    (flatSourceFinsetCodes first) (flatSourceFinsetCodes second)
    (flatSourceFinsetCodes_pairwise first)
    (flatSourceFinsetCodes_pairwise second),
    flatSourceFinsetCodes_value, flatSourceFinsetCodes_value]

theorem flatSourceFinsetOrdering_equal_iff
    {α : Type} [Encodable α] (first second : Finset α) :
    flatSortedSourceListOrdering
        (flatSourceFinsetCodes first)
        (flatSourceFinsetCodes second) = .equal ↔ first = second := by
  rw [flatSourceFinsetOrdering_eq_godel]
  constructor
  · intro horder
    have hcode : Encodable.encode first = Encodable.encode second := by
      by_cases hless : Encodable.encode first < Encodable.encode second
      · simp only [flatSourceNaturalOrdering, hless, ↓reduceIte, reduceCtorEq] at horder
      · by_cases hgreater :
          Encodable.encode second < Encodable.encode first
        · simp only [flatSourceNaturalOrdering, hless, ↓reduceIte, hgreater, reduceCtorEq]
            at horder
        · exact Nat.le_antisymm
            (Nat.le_of_not_gt hgreater) (Nat.le_of_not_gt hless)
    exact Encodable.encode_injective hcode
  · intro hrecords
    subst second
    simp only [flatSourceNaturalOrdering, lt_self_iff_false, ↓reduceIte]

end CNFFlatSourceOrder

namespace CNFFlatWholeWordFoldTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.CLStructuralWholeCNFOutputTM GapCVP.CNFFiniteRecordSort
open GapCVP.CNFBoundedRecordFoldTM GapCVP.CNFFlatStructuralRecordWorkerTM
open GapCVP.OutputBoundedDependentRecordFold

private theorem flatLiteralRecordStep_iterate_preservedSuffix
    (pending : List Literal) (suffix : List Bool) :
    ((flatLiteralRecordStep^[pending.length])
      (flatSignedLiteralDescriptorStream pending ++ suffix)) =
      suffix ++ pending.flatMap encodeLiteral := by
  induction pending generalizing suffix with
  | nil => simp only [List.length_nil, flatSignedLiteralDescriptorStream, List.flatMap_nil,
      List.nil_append,
               Function.iterate_zero, id_eq, List.append_nil]
  | cons literal remaining ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [flatSignedLiteralDescriptorStream,
        List.flatMap_cons, List.append_assoc]
      rw [flatLiteralRecordStep_descriptor]
      simpa only [List.append_assoc, flatSignedLiteralDescriptorStream] using ih (suffix ++
          encodeLiteral literal)

/-- GapCVP reduction support. -/
def structuralThreeCNFFlatFoldInput
    (clauses : ThreeCNF) : List Bool :=
  unaryBoundedFoldWord (3 * clauses.length)
    (flatSignedLiteralDescriptorStream
        (flatThreeClauseLiterals clauses) ++
      lengthPrefixedWord (encodeNat clauses.length))

private theorem boundedRecordFoldOutput_structuralThreeCNF
    (clauses : ThreeCNF) :
    boundedRecordFoldOutput flatLiteralRecordStep
      (structuralThreeCNFFlatFoldInput clauses) =
      encodeThreeCNF clauses := by
  simp only [structuralThreeCNFFlatFoldInput,
    boundedRecordFoldOutput, parseUnaryBoundedFold_word]
  rw [← flatThreeClauseLiterals_length]
  rw [flatLiteralRecordStep_iterate_preservedSuffix]
  rw [flatThreeClauseLiterals_encoded]
  rfl

/-- GapCVP reduction support. -/
def totalVerifierSortedFiveFamilyFlatFoldInput
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) : List Bool :=
  structuralThreeCNFFlatFoldInput
    (encodeFormulaFrom 0
      (sourceOrderedDistinctRecords
        (totalVerifierFiveFamilySourceClauseCandidates
          bound machine input)))

private theorem boundedRecordFoldOutput_totalVerifierSortedFiveFamilies
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) :
    boundedRecordFoldOutput flatLiteralRecordStep
      (totalVerifierSortedFiveFamilyFlatFoldInput
        bound machine input) =
      structuralWholeCNFWord bound machine input := by
  unfold totalVerifierSortedFiveFamilyFlatFoldInput
  rw [boundedRecordFoldOutput_structuralThreeCNF]
  exact encodeThreeCNF_totalVerifierFiveFamilies
    bound machine input

/-- GapCVP reduction support. -/
noncomputable def actualWholeStructuralCNFOutputComputableOfFlatPreparation
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (preparation : BitTM
      (totalVerifierSortedFiveFamilyFlatFoldInput bound machine)) :
    BitTM
      (structuralWholeCNFWord bound machine) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    preparation actualFlatLiteralRecordFoldComputable
  have hequality :
      (fun input : List Bool =>
        boundedRecordFoldOutput flatLiteralRecordStep
          (totalVerifierSortedFiveFamilyFlatFoldInput
            bound machine input)) =
        structuralWholeCNFWord bound machine := by
    funext input
    exact boundedRecordFoldOutput_totalVerifierSortedFiveFamilies
      bound machine input
  rw [← hequality]
  simpa only [Function.comp_def] using hphysical

end CNFFlatWholeWordFoldTM

namespace CNFFlatSourceOrderPolynomialBounds

open GapCVP.CL GapCVP.CLStructuralCNFVariableBounds GapCVP.CNFFlatSourceOrder

/-- GapCVP reduction support. -/
def tableauSignedLiteralCodeBound (time symbols : ℕ) : ℕ :=
  (tableauFiniteVariableCodeBound time symbols + 2) ^ 2

private theorem tableauSignedLiteral_encode_lt
    {time symbols : ℕ} (literal : SignedLiteral time symbols) :
    Encodable.encode literal <
      tableauSignedLiteralCodeBound time symbols := by
  obtain ⟨atom, sign⟩ := literal
  have hvariable := tableauVariable_encode_lt atom
  have hsign : Encodable.encode sign ≤ 1 := by
    cases sign <;> simp
  change Nat.pair (Encodable.encode atom) (Encodable.encode sign) <
    tableauSignedLiteralCodeBound time symbols
  calc
    Nat.pair (Encodable.encode atom) (Encodable.encode sign) <
        (max (Encodable.encode atom) (Encodable.encode sign) + 1) ^ 2 :=
      Nat.pair_lt_max_add_one_sq _ _
    _ ≤ (tableauFiniteVariableCodeBound time symbols + 2) ^ 2 := by
      apply Nat.pow_le_pow_left
      omega

theorem flatSourceClauseLiteralCode_lt
    {time symbols : ℕ} (clause : Clause time symbols)
    (code : ℕ) (hcode : code ∈ flatSourceFinsetCodes clause) :
    code < tableauSignedLiteralCodeBound time symbols := by
  obtain ⟨literal, _, rfl⟩ :=
    List.mem_map.mp hcode
  exact tableauSignedLiteral_encode_lt literal

end CNFFlatSourceOrderPolynomialBounds

namespace CNFFlatSourceGridDescriptorTM

open Computability Turing GapCVP.CL GapCVP.ThreeCNFReduction GapCVP.BinaryEncoding
open GapCVP.CLStructuralPrefixWriter GapCVP.CLStructuralNaturalBinaryWriter
open GapCVP.SourceMachineCert GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatStructuralRecordWorkerTM

/-- GapCVP reduction support. -/
def polynomialSignedLiteralDescriptorWord
    (polynomial : Polynomial ℕ) (sign : Bool)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
    (sign :: encodeNat (polynomial.eval input.length))

private noncomputable def polynomialSignedLiteralDescriptorComputable
    (polynomial : Polynomial ℕ) (sign : Bool) :
    BitTM
      (polynomialSignedLiteralDescriptorWord polynomial sign) := by
  have hunary := polynomialValueUnaryComputable polynomial
  have hbinary := GapCVP.TMComposition.computableInPolyTime
    hunary structuralNaturalBinaryWriterComputable
  have hsign := GapCVP.TMComposition.computableInPolyTime
    hbinary (prependBitComputable sign)
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    hsign structuralPrefixWriterComputable
  change BitTM
    (fun input : List Bool =>
      lengthPrefixedWord
        (sign :: encodeNat (polynomial.eval input.length)))
  simpa only [Function.comp_def, List.length_replicate] using hprefix

/-- GapCVP reduction support. -/
def tableauSourceSignedLiteralDescriptorWord
    (sign : Bool) : List Bool → List Bool :=
  polynomialSignedLiteralDescriptorWord (4 * Polynomial.X) sign

/-- GapCVP reduction support. -/
noncomputable def tableauSourceSignedLiteralDescriptorComputable
    (sign : Bool) :
    BitTM
      (tableauSourceSignedLiteralDescriptorWord sign) :=
  polynomialSignedLiteralDescriptorComputable
    (4 * Polynomial.X) sign

@[simp] theorem tableauSourceSignedLiteralDescriptorWord_variable
    {T S : ℕ} (sourceVar : Variable T S) (sign : Bool) :
    tableauSourceSignedLiteralDescriptorWord sign
      (List.replicate (Encodable.encode sourceVar) true) =
      flatSignedLiteralDescriptor
        (sourceVariable sourceVar, sign) := by
  simp only [tableauSourceSignedLiteralDescriptorWord, polynomialSignedLiteralDescriptorWord,
      List.length_replicate, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
          flatSignedLiteralDescriptor,
      sourceVariable]

/-- GapCVP reduction support. -/
def accumulatorSignedLiteralDescriptorWord
    (sign : Bool) : List Bool → List Bool :=
  polynomialSignedLiteralDescriptorWord
    (4 * Polynomial.X + 1) sign

/-- GapCVP reduction support. -/
noncomputable def accumulatorSignedLiteralDescriptorComputable
    (sign : Bool) :
    BitTM
      (accumulatorSignedLiteralDescriptorWord sign) :=
  polynomialSignedLiteralDescriptorComputable
    (4 * Polynomial.X + 1) sign

@[simp] theorem accumulatorSignedLiteralDescriptorWord_index
    (clauseIndex prefixIndex : ℕ) (sign : Bool) :
    accumulatorSignedLiteralDescriptorWord sign
      (List.replicate (Nat.pair clauseIndex prefixIndex) true) =
      flatSignedLiteralDescriptor
        (accumulatorVariable clauseIndex prefixIndex, sign) := by
  simp only [accumulatorSignedLiteralDescriptorWord, polynomialSignedLiteralDescriptorWord,
      List.length_replicate, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
          Polynomial.eval_X,
      Polynomial.eval_one, flatSignedLiteralDescriptor, accumulatorVariable,
          Encodable.encode_prod_val,
      Encodable.encode_nat]

/-- GapCVP reduction support. -/
def paddingSignedLiteralDescriptorWord
    (index : ℕ) (sign : Bool) : List Bool → List Bool :=
  polynomialSignedLiteralDescriptorWord (Polynomial.C index) sign

/-- GapCVP reduction support. -/
noncomputable def paddingSignedLiteralDescriptorComputable
    (index : ℕ) (sign : Bool) :
    BitTM
      (paddingSignedLiteralDescriptorWord index sign) :=
  polynomialSignedLiteralDescriptorComputable
    (Polynomial.C index) sign

@[simp] theorem paddingSignedLiteralDescriptorWord_eq
    (index : ℕ) (sign : Bool) (input : List Bool) :
    paddingSignedLiteralDescriptorWord index sign input =
      flatSignedLiteralDescriptor (index, sign) := by
  simp only [paddingSignedLiteralDescriptorWord, polynomialSignedLiteralDescriptorWord, eq_natCast,
      Polynomial.eval_natCast, Nat.cast_id, flatSignedLiteralDescriptor]

end CNFFlatSourceGridDescriptorTM

namespace CNFUnaryPairIndexTM

open Computability Turing GapCVP.BinaryEncoding

/-- GapCVP reduction support. -/
def unarySourcePairWord (first second : ℕ) : List Bool :=
  List.replicate first true ++
    false :: (List.replicate second true ++ [false])

/-- GapCVP reduction support. -/
def unarySourcePairOutput (input : List Bool) : List Bool :=
  match readUnaryPrefix input with
  | none => []
  | some (first, remaining) =>
      match readUnaryPrefix remaining with
      | some (second, []) =>
          List.replicate (Nat.pair first second) true
      | _ => []

@[simp] theorem unarySourcePairOutput_word
    (first second : ℕ) :
    unarySourcePairOutput (unarySourcePairWord first second) =
      List.replicate (Nat.pair first second) true := by
  simp only [unarySourcePairOutput, unarySourcePairWord, readUnaryPrefix_replicate]

private def unaryPairPeek (stack : Fin 9)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  .peek stack (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome) present absent)

private def unaryPairPop (stack : Fin 9)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  .pop stack (fun symbol _ => symbol) continuation

private def unaryPairPush (stack : Fin 9)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  .push stack (fun _ => true) continuation

private def unaryPairGoto (phase : Fin 12) :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => phase))

/-- GapCVP reduction support. -/
def unaryPairFirstStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  unaryPairPeek 0
    (.branch (fun symbol => symbol.getD false)
      (unaryPairPop 0 (unaryPairPush 1 (unaryPairGoto 0)))
      (unaryPairPop 0 (unaryPairGoto 1)))
    (unaryPairGoto 11)

/-- GapCVP reduction support. -/
def unaryPairSecondStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  unaryPairPeek 0
    (.branch (fun symbol => symbol.getD false)
      (unaryPairPop 0 (unaryPairPush 2 (unaryPairGoto 1)))
      (unaryPairPop 0 (unaryPairGoto 2)))
    (unaryPairGoto 11)

/-- GapCVP reduction support. -/
def unaryPairCompareStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  unaryPairPeek 0
    (unaryPairGoto 11)
    (unaryPairPeek 1
      (unaryPairPeek 2
        (unaryPairPop 1
          (unaryPairPop 2
            (unaryPairPush 3
              (unaryPairPush 4 (unaryPairGoto 2)))))
        (unaryPairGoto 3))
      (unaryPairPeek 2
        (unaryPairGoto 5)
        (unaryPairGoto 3)))

/-- GapCVP reduction support. -/
def unaryPairGreaterBaseStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  unaryPairPeek 1
    (unaryPairPop 1
      (unaryPairPush 5
        (unaryPairPush 6
          (unaryPairPush 7 (unaryPairGoto 3)))))
    (unaryPairPeek 3
      (unaryPairPop 3
        (unaryPairPush 5
          (unaryPairPush 6
            (unaryPairPush 7 (unaryPairGoto 3)))))
      (unaryPairGoto 4))

/-- GapCVP reduction support. -/
def unaryPairGreaterOffsetStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  unaryPairPeek 4
    (unaryPairPop 4
      (unaryPairPush 7 (unaryPairGoto 4)))
    (unaryPairGoto 7)

/-- GapCVP reduction support. -/
def unaryPairLessBaseStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  unaryPairPeek 2
    (unaryPairPop 2
      (unaryPairPush 5
        (unaryPairPush 6 (unaryPairGoto 5))))
    (unaryPairPeek 4
      (unaryPairPop 4
        (unaryPairPush 5
          (unaryPairPush 6 (unaryPairGoto 5))))
      (unaryPairGoto 6))

/-- GapCVP reduction support. -/
def unaryPairLessOffsetStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  unaryPairPeek 3
    (unaryPairPop 3
      (unaryPairPush 7 (unaryPairGoto 6)))
    (unaryPairGoto 7)

/-- GapCVP reduction support. -/
def unaryPairOuterStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  unaryPairPeek 6
    (unaryPairPop 6 (unaryPairGoto 8))
    (unaryPairGoto 10)

/-- GapCVP reduction support. -/
def unaryPairSquareCopyStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  unaryPairPeek 5
    (unaryPairPop 5
      (unaryPairPush 8
        (unaryPairPush 7 (unaryPairGoto 8))))
    (unaryPairGoto 9)

/-- GapCVP reduction support. -/
def unaryPairSquareRestoreStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  unaryPairPeek 8
    (unaryPairPop 8
      (unaryPairPush 5 (unaryPairGoto 9)))
    (unaryPairGoto 7)

/-- GapCVP reduction support. -/
def unaryPairSquareCleanupStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  unaryPairPeek 5
    (unaryPairPop 5 (unaryPairGoto 10))
    .halt

/-- GapCVP reduction support. -/
def unaryPairFailureStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 9 => Bool) (Fin 12) (Option Bool) :=
  unaryPairPeek 0
    (unaryPairPop 0 (unaryPairGoto 11))
    (unaryPairPeek 1
      (unaryPairPop 1 (unaryPairGoto 11))
      (unaryPairPeek 2
        (unaryPairPop 2 (unaryPairGoto 11))
        (unaryPairPeek 3
          (unaryPairPop 3 (unaryPairGoto 11))
          (unaryPairPeek 4
            (unaryPairPop 4 (unaryPairGoto 11))
            (unaryPairPeek 5
              (unaryPairPop 5 (unaryPairGoto 11))
              (unaryPairPeek 6
                (unaryPairPop 6 (unaryPairGoto 11))
                (unaryPairPeek 8
                  (unaryPairPop 8 (unaryPairGoto 11))
                  .halt)))))))

/-- GapCVP reduction support. -/
abbrev actualUnaryPairIndexMachine : Turing.FinTM2 where
  K := Fin 9
  k₀ := 0
  k₁ := 7
  Γ _ := Bool
  Λ := Fin 12
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 12) then unaryPairFirstStatement
    else if phase = (1 : Fin 12) then unaryPairSecondStatement
    else if phase = (2 : Fin 12) then unaryPairCompareStatement
    else if phase = (3 : Fin 12) then unaryPairGreaterBaseStatement
    else if phase = (4 : Fin 12) then unaryPairGreaterOffsetStatement
    else if phase = (5 : Fin 12) then unaryPairLessBaseStatement
    else if phase = (6 : Fin 12) then unaryPairLessOffsetStatement
    else if phase = (7 : Fin 12) then unaryPairOuterStatement
    else if phase = (8 : Fin 12) then unaryPairSquareCopyStatement
    else if phase = (9 : Fin 12) then unaryPairSquareRestoreStatement
    else if phase = (10 : Fin 12) then unaryPairSquareCleanupStatement
    else unaryPairFailureStatement

/-- GapCVP reduction support. -/
def unaryPairConfiguration (phase : Fin 12)
    (input first second matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    actualUnaryPairIndexMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, first, second, matchedFirst, matchedSecond,
    base, outer, output, scratch]

theorem actualUnaryPairIndexMachine_init (input : List Bool) :
    Turing.initList actualUnaryPairIndexMachine input =
      unaryPairConfiguration 0 input [] [] [] [] [] [] [] [] := by
  simp only [actualUnaryPairIndexMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq,
      dite_eq_ite,
      unaryPairConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `unaryPairStepTac` machine-step simplifier. -/
macro "unaryPairStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [actualUnaryPairIndexMachine, unaryPairConfiguration,
          unaryPairPeek, unaryPairPop, unaryPairPush, unaryPairGoto,
          unaryPairFirstStatement, unaryPairSecondStatement,
          unaryPairCompareStatement, unaryPairGreaterBaseStatement,
          unaryPairGreaterOffsetStatement, unaryPairLessBaseStatement,
          unaryPairLessOffsetStatement, unaryPairOuterStatement,
          unaryPairSquareCopyStatement, unaryPairSquareRestoreStatement,
          unaryPairSquareCleanupStatement, unaryPairFailureStatement,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

theorem unaryPair_first_true
    (input first second matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 0
        (true :: input) first second matchedFirst matchedSecond
        base outer output scratch) =
      some (unaryPairConfiguration 0 input
        (true :: first) second matchedFirst matchedSecond
        base outer output scratch) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_first_false
    (input first second matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 0
        (false :: input) first second matchedFirst matchedSecond
        base outer output scratch) =
      some (unaryPairConfiguration 1 input
        first second matchedFirst matchedSecond
        base outer output scratch) := by
  unaryPairStepTac

theorem unaryPair_first_missing
    (first second matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 0 []
        first second matchedFirst matchedSecond
        base outer output scratch) =
      some (unaryPairConfiguration 11 []
        first second matchedFirst matchedSecond
        base outer output scratch) := by
  unaryPairStepTac

theorem unaryPair_second_true
    (input first second matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 1
        (true :: input) first second matchedFirst matchedSecond
        base outer output scratch) =
      some (unaryPairConfiguration 1 input first
        (true :: second) matchedFirst matchedSecond
        base outer output scratch) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_second_false
    (input first second matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 1
        (false :: input) first second matchedFirst matchedSecond
        base outer output scratch) =
      some (unaryPairConfiguration 2 input first second
        matchedFirst matchedSecond base outer output scratch) := by
  unaryPairStepTac

theorem unaryPair_second_missing
    (first second matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 1 [] first second
        matchedFirst matchedSecond base outer output scratch) =
      some (unaryPairConfiguration 11 [] first second
        matchedFirst matchedSecond base outer output scratch) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_compare_match
    (first second matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 2 []
        (true :: first) (true :: second)
        matchedFirst matchedSecond base outer output scratch) =
      some (unaryPairConfiguration 2 [] first second
        (true :: matchedFirst) (true :: matchedSecond)
        base outer output scratch) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_compare_greater
    (first matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 2 [] first []
        matchedFirst matchedSecond base outer output scratch) =
      some (unaryPairConfiguration 3 [] first []
        matchedFirst matchedSecond base outer output scratch) := by
  cases first <;> unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_compare_less
    (second matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 2 [] [] (true :: second)
        matchedFirst matchedSecond base outer output scratch) =
      some (unaryPairConfiguration 5 [] [] (true :: second)
        matchedFirst matchedSecond base outer output scratch) := by
  unaryPairStepTac

theorem unaryPair_compare_trailing
    (bit : Bool)
    (input first second matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 2 (bit :: input)
        first second matchedFirst matchedSecond
        base outer output scratch) =
      some (unaryPairConfiguration 11 (bit :: input)
        first second matchedFirst matchedSecond
        base outer output scratch) := by
  cases bit <;> unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_greater_base_first
    (first matchedFirst matchedSecond base outer output : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 3 []
        (true :: first) [] matchedFirst matchedSecond
        base outer output []) =
      some (unaryPairConfiguration 3 [] first []
        matchedFirst matchedSecond
        (true :: base) (true :: outer) (true :: output) []) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_greater_base_matched
    (matchedFirst matchedSecond base outer output : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 3 [] [] []
        (true :: matchedFirst) matchedSecond
        base outer output []) =
      some (unaryPairConfiguration 3 [] [] []
        matchedFirst matchedSecond
        (true :: base) (true :: outer) (true :: output) []) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_greater_base_finish
    (matchedSecond base outer output : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 3 [] [] [] [] matchedSecond
        base outer output []) =
      some (unaryPairConfiguration 4 [] [] [] [] matchedSecond
        base outer output []) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_greater_offset_step
    (matchedSecond base outer output : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 4 [] [] [] []
        (true :: matchedSecond) base outer output []) =
      some (unaryPairConfiguration 4 [] [] [] [] matchedSecond
        base outer (true :: output) []) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_greater_offset_finish
    (base outer output : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 4 [] [] [] [] []
        base outer output []) =
      some (unaryPairConfiguration 7 [] [] [] [] []
        base outer output []) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_less_base_second
    (second matchedFirst matchedSecond base outer output : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 5 [] [] (true :: second)
        matchedFirst matchedSecond base outer output []) =
      some (unaryPairConfiguration 5 [] [] second
        matchedFirst matchedSecond
        (true :: base) (true :: outer) output []) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_less_base_matched
    (matchedFirst matchedSecond base outer output : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 5 [] [] []
        matchedFirst (true :: matchedSecond)
        base outer output []) =
      some (unaryPairConfiguration 5 [] [] []
        matchedFirst matchedSecond
        (true :: base) (true :: outer) output []) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_less_base_finish
    (matchedFirst base outer output : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 5 [] [] [] matchedFirst []
        base outer output []) =
      some (unaryPairConfiguration 6 [] [] [] matchedFirst []
        base outer output []) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_less_offset_step
    (matchedFirst base outer output : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 6 [] [] []
        (true :: matchedFirst) [] base outer output []) =
      some (unaryPairConfiguration 6 [] [] []
        matchedFirst [] base outer (true :: output) []) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_less_offset_finish
    (base outer output : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 6 [] [] [] [] []
        base outer output []) =
      some (unaryPairConfiguration 7 [] [] [] [] []
        base outer output []) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_outer_step
    (base outer output : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 7 [] [] [] [] []
        base (true :: outer) output []) =
      some (unaryPairConfiguration 8 [] [] [] [] []
        base outer output []) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_outer_finish
    (base output : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 7 [] [] [] [] []
        base [] output []) =
      some (unaryPairConfiguration 10 [] [] [] [] []
        base [] output []) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_square_copy_step
    (base outer output scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 8 [] [] [] [] []
        (true :: base) outer output scratch) =
      some (unaryPairConfiguration 8 [] [] [] [] []
        base outer (true :: output) (true :: scratch)) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_square_copy_finish
    (outer output scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 8 [] [] [] [] []
        [] outer output scratch) =
      some (unaryPairConfiguration 9 [] [] [] [] []
        [] outer output scratch) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_square_restore_step
    (base outer output scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 9 [] [] [] [] []
        base outer output (true :: scratch)) =
      some (unaryPairConfiguration 9 [] [] [] [] []
        (true :: base) outer output scratch) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_square_restore_finish
    (base outer output : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 9 [] [] [] [] []
        base outer output []) =
      some (unaryPairConfiguration 7 [] [] [] [] []
        base outer output []) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_square_cleanup_step
    (base output : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 10 [] [] [] [] []
        (true :: base) [] output []) =
      some (unaryPairConfiguration 10 [] [] [] [] []
        base [] output []) := by
  unaryPairStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem unaryPair_square_cleanup_finish (output : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 10 [] [] [] [] [] [] [] output []) =
      some (Turing.haltList actualUnaryPairIndexMachine output) := by
  unaryPairStepTac

theorem unaryPair_failure_input_step
    (bit : Bool)
    (input first second matchedFirst matchedSecond
      base outer scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 11 (bit :: input)
        first second matchedFirst matchedSecond base outer [] scratch) =
      some (unaryPairConfiguration 11 input
        first second matchedFirst matchedSecond base outer [] scratch) := by
  cases bit <;> unaryPairStepTac

theorem unaryPair_failure_first_step
    (bit : Bool)
    (first second matchedFirst matchedSecond
      base outer scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 11 []
        (bit :: first) second matchedFirst matchedSecond
        base outer [] scratch) =
      some (unaryPairConfiguration 11 [] first second
        matchedFirst matchedSecond base outer [] scratch) := by
  cases bit <;> unaryPairStepTac

theorem unaryPair_failure_second_step
    (bit : Bool)
    (second matchedFirst matchedSecond
      base outer scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 11 [] []
        (bit :: second) matchedFirst matchedSecond
        base outer [] scratch) =
      some (unaryPairConfiguration 11 [] [] second
        matchedFirst matchedSecond base outer [] scratch) := by
  cases bit <;> unaryPairStepTac

theorem unaryPair_failure_matchedFirst_step
    (bit : Bool)
    (matchedFirst matchedSecond base outer scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 11 [] [] []
        (bit :: matchedFirst) matchedSecond
        base outer [] scratch) =
      some (unaryPairConfiguration 11 [] [] []
        matchedFirst matchedSecond base outer [] scratch) := by
  cases bit <;> unaryPairStepTac

theorem unaryPair_failure_matchedSecond_step
    (bit : Bool)
    (matchedSecond base outer scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 11 [] [] [] []
        (bit :: matchedSecond) base outer [] scratch) =
      some (unaryPairConfiguration 11 [] [] [] []
        matchedSecond base outer [] scratch) := by
  cases bit <;> unaryPairStepTac

theorem unaryPair_failure_base_step
    (bit : Bool) (base outer scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 11 [] [] [] [] []
        (bit :: base) outer [] scratch) =
      some (unaryPairConfiguration 11 [] [] [] [] []
        base outer [] scratch) := by
  cases bit <;> unaryPairStepTac

theorem unaryPair_failure_outer_step
    (bit : Bool) (outer scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 11 [] [] [] [] [] []
        (bit :: outer) [] scratch) =
      some (unaryPairConfiguration 11 [] [] [] [] [] []
        outer [] scratch) := by
  cases bit <;> unaryPairStepTac

theorem unaryPair_failure_scratch_step
    (bit : Bool) (scratch : List Bool) :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 11 [] [] [] [] [] [] []
        [] (bit :: scratch)) =
      some (unaryPairConfiguration 11 [] [] [] [] [] [] []
        [] scratch) := by
  cases bit <;> unaryPairStepTac

theorem unaryPair_failure_finish :
    actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 11 [] [] [] [] [] [] [] [] []) =
      some (Turing.haltList actualUnaryPairIndexMachine []) := by
  unaryPairStepTac

end CNFUnaryPairIndexTM

namespace CNFUnaryPairIndexTotalCert

open Computability Turing GapCVP.CNFUnaryPairIndexTM

theorem unaryPair_replicate_append_true
    (count : ℕ) (suffix : List Bool) :
    List.replicate count true ++ true :: suffix =
      List.replicate (count + 1) true ++ suffix := by
  simp only [SourceStructuralDecoder.replicate_true_append_cons, List.replicate_succ',
      List.append_nil,
      List.cons_append]

end CNFUnaryPairIndexTotalCert

end GapCVP

end
