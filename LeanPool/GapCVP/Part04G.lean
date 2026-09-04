/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part04F

/-! # GapCVP proof, part 04, continuation 07 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFUnaryPairIndexTotalCert

open Computability Turing GapCVP.CNFUnaryPairIndexTM

/-- GapCVP reduction support. -/
def unaryPairFirstTrace
    (count : ℕ)
    (tail first second matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    EvalsToInTime actualUnaryPairIndexMachine.step (unaryPairConfiguration 0
        (List.replicate count true ++ false :: tail)
        first second matchedFirst matchedSecond
        base outer output scratch)
      (some (unaryPairConfiguration 1 tail
        (List.replicate count true ++ first)
        second matchedFirst matchedSecond
        base outer output scratch))
      (count + 1) := by
  induction count generalizing first with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (unaryPair_first_false tail first second matchedFirst matchedSecond base
              outer output scratch)
  | succ count ih =>
      have hfirst := oneStep _ _ (unaryPair_first_true
          (List.replicate count true ++ false :: tail)
          first second matchedFirst matchedSecond
          base outer output scratch)
      have hrest := ih (true :: first)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_comm,
          Nat.add_left_comm,
          Nat.reduceAdd, SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest

/-- GapCVP reduction support. -/
def unaryPairSecondTrace
    (count : ℕ)
    (tail first second matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    EvalsToInTime actualUnaryPairIndexMachine.step (unaryPairConfiguration 1
        (List.replicate count true ++ false :: tail)
        first second matchedFirst matchedSecond
        base outer output scratch)
      (some (unaryPairConfiguration 2 tail first
        (List.replicate count true ++ second)
        matchedFirst matchedSecond base outer output scratch))
      (count + 1) := by
  induction count generalizing second with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (unaryPair_second_false tail first second matchedFirst matchedSecond base
              outer output scratch)
  | succ count ih =>
      have hfirst := oneStep _ _ (unaryPair_second_true
          (List.replicate count true ++ false :: tail)
          first second matchedFirst matchedSecond
          base outer output scratch)
      have hrest := ih (true :: second)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_comm,
          Nat.add_left_comm,
          Nat.reduceAdd, SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest

private def unaryPair_squareCopyTrace
    (count : ℕ) (outer output scratch : List Bool) :
    EvalsToInTime actualUnaryPairIndexMachine.step (unaryPairConfiguration 8 [] [] [] [] []
        (List.replicate count true) outer output scratch)
      (some (unaryPairConfiguration 9 [] [] [] [] [] []
        outer (List.replicate count true ++ output)
        (List.replicate count true ++ scratch)))
      (count + 1) := by
  induction count generalizing output scratch with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (unaryPair_square_copy_finish outer output scratch)
  | succ count ih =>
      have hfirst := oneStep _ _ (unaryPair_square_copy_step
          (List.replicate count true)
          outer output scratch)
      have hrest := ih (true :: output) (true :: scratch)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest

private def unaryPair_squareRestoreTrace
    (count : ℕ) (base outer output : List Bool) :
    EvalsToInTime actualUnaryPairIndexMachine.step (unaryPairConfiguration 9 [] [] [] [] []
        base outer output (List.replicate count true))
      (some (unaryPairConfiguration 7 [] [] [] [] []
        (List.replicate count true ++ base)
        outer output []))
      (count + 1) := by
  induction count generalizing base with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (unaryPair_square_restore_finish base outer output)
  | succ count ih =>
      have hfirst := oneStep _ _ (unaryPair_square_restore_step
          base outer output (List.replicate count true))
      have hrest := ih (true :: base)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest

private def unaryPair_squareCleanupTrace
    (count : ℕ) (output : List Bool) :
    EvalsToInTime actualUnaryPairIndexMachine.step (unaryPairConfiguration 10 [] [] [] [] []
        (List.replicate count true) [] output [])
      (some (Turing.haltList actualUnaryPairIndexMachine output))
      (count + 1) := by
  induction count with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, zero_add] using
          oneStep _ _ (unaryPair_square_cleanup_finish output)
  | succ count ih =>
      have hfirst := oneStep _ _ (unaryPair_square_cleanup_step
          (List.replicate count true) output)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, Nat.add_assoc, Nat.reduceAdd]
          using
          EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst ih

/-- GapCVP reduction support. -/
def unaryPairSquareTrace
    (baseCount outerCount : ℕ) (output : List Bool) :
    EvalsToInTime actualUnaryPairIndexMachine.step (unaryPairConfiguration 7 [] [] [] [] []
        (List.replicate baseCount true)
        (List.replicate outerCount true) output [])
      (some (Turing.haltList actualUnaryPairIndexMachine
        (List.replicate (baseCount * outerCount) true ++ output)))
      (outerCount * (2 * baseCount + 3) + baseCount + 2) := by
  induction outerCount generalizing output with
  | zero =>
      have houter := oneStep _ _ (unaryPair_outer_finish
          (List.replicate baseCount true) output)
      have hclean := unaryPair_squareCleanupTrace baseCount output
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, mul_zero, List.nil_append,
          zero_mul, zero_add,
          Nat.add_assoc, Nat.reduceAdd] using EvalsToInTime.trans actualUnaryPairIndexMachine.step
              _ _ _ _ _ houter hclean
  | succ outerCount ih =>
      have houter := oneStep _ _ (unaryPair_outer_step (List.replicate baseCount true)
          (List.replicate outerCount true) output)
      have hcopy := unaryPair_squareCopyTrace baseCount
        (List.replicate outerCount true) output []
      simp only [List.append_nil] at hcopy
      have hrestore := unaryPair_squareRestoreTrace baseCount []
        (List.replicate outerCount true)
        (List.replicate baseCount true ++ output)
      simp only [List.append_nil] at hrestore
      have hcycleFirst := EvalsToInTime.trans
        actualUnaryPairIndexMachine.step _ _ _ _ _ houter hcopy
      have hcycle := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _
        hcycleFirst hrestore
      have hrest := ih (List.replicate baseCount true ++ output)
      have hfull := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hcycle hrest
      have htarget :
          List.replicate (baseCount * outerCount) true ++
            (List.replicate baseCount true ++ output) =
          List.replicate (baseCount * (outerCount + 1)) true ++
            output := by
        simp only [Nat.mul_succ, List.replicate_add,
          List.append_assoc]
      have hbounded := rebound (newBudget :=
          (outerCount + 1) * (2 * baseCount + 3) +
            baseCount + 2)
        hfull (by
          simp only [Nat.succ_mul, one_mul]
          omega)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, htarget] using hbounded

/-- GapCVP reduction support. -/
def unaryPairComparedConfiguration
    (first second matched : ℕ) :
    actualUnaryPairIndexMachine.Cfg :=
  if first < second then
    unaryPairConfiguration 5 [] []
      (List.replicate (second - first) true)
      (List.replicate (matched + first) true)
      (List.replicate (matched + first) true)
      [] [] [] []
  else
    unaryPairConfiguration 3 []
      (List.replicate (first - second) true) []
      (List.replicate (matched + second) true)
      (List.replicate (matched + second) true)
      [] [] [] []

/-- GapCVP reduction support. -/
def unaryPairCompareTrace
    (first second matched : ℕ) :
    EvalsToInTime actualUnaryPairIndexMachine.step (unaryPairConfiguration 2 []
        (List.replicate first true)
        (List.replicate second true)
        (List.replicate matched true)
        (List.replicate matched true)
        [] [] [] [])
      (some (unaryPairComparedConfiguration first second matched))
      (min first second + 1) := by
  induction first generalizing second matched with
  | zero =>
      cases second with
      | zero =>
          simpa only [FinTM2.step, Fin.isValue, List.replicate_zero,
              unaryPairComparedConfiguration, lt_self_iff_false,
              ↓reduceIte, tsub_self, add_zero, min_self, zero_add] using
              oneStep _ _ (unaryPair_compare_greater [] (List.replicate matched true)
                  (List.replicate matched true) [] [] [] [])
      | succ second =>
          simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.replicate_succ,
              unaryPairComparedConfiguration, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le,
                  ↓reduceIte, tsub_zero, add_zero,
              le_add_iff_nonneg_left, inf_of_le_left, zero_add] using
              oneStep _ _
                (unaryPair_compare_less (List.replicate second true) (List.replicate matched true)
                    (List.replicate matched true)
                  [] [] [] [])
  | succ first ih =>
      cases second with
      | zero =>
          simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.replicate_zero,
              unaryPairComparedConfiguration, not_lt_zero, ↓reduceIte, tsub_zero, add_zero,
                  le_add_iff_nonneg_left, zero_le,
              inf_of_le_right, zero_add] using
              oneStep _ _
                (unaryPair_compare_greater (List.replicate (first + 1) true) (List.replicate
                    matched true)
                  (List.replicate matched true) [] [] [] [])
      | succ second =>
          have hfirst := oneStep _ _ (unaryPair_compare_match
              (List.replicate first true)
              (List.replicate second true)
              (List.replicate matched true)
              (List.replicate matched true) [] [] [] [])
          have hrest := ih second (matched + 1)
          have hfull := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _
            hfirst hrest
          simpa only [FinTM2.step, Fin.isValue, List.replicate_succ,
              unaryPairComparedConfiguration,
              Order.lt_add_one_iff, Order.add_one_le_iff, Nat.succ_sub_succ_eq_sub,
                  Nat.add_left_comm, Nat.succ_min_succ,
              Nat.succ_eq_add_one, Nat.add_comm, Nat.reduceAdd] using hfull

/-- GapCVP reduction support. -/
def unaryPairGreaterBaseTrace
    (first matchedFirst matchedSecond : ℕ)
    (base outer output : List Bool) :
    EvalsToInTime actualUnaryPairIndexMachine.step (unaryPairConfiguration 3 []
        (List.replicate first true) []
        (List.replicate matchedFirst true)
        (List.replicate matchedSecond true)
        base outer output [])
      (some (unaryPairConfiguration 4 [] [] [] []
        (List.replicate matchedSecond true)
        (List.replicate (first + matchedFirst) true ++ base)
        (List.replicate (first + matchedFirst) true ++ outer)
        (List.replicate (first + matchedFirst) true ++ output) []))
      (first + matchedFirst + 1) := by
  induction first generalizing base outer output with
  | zero =>
      induction matchedFirst generalizing base outer output with
      | zero =>
          simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, add_zero, List.nil_append,
              zero_add] using
              oneStep _ _ (unaryPair_greater_base_finish (List.replicate matchedSecond true) base
                  outer output)
      | succ matchedFirst ih =>
          have hfirst := oneStep _ _ (unaryPair_greater_base_matched
              (List.replicate matchedFirst true)
              (List.replicate matchedSecond true)
              base outer output)
          have hrest := ih
            (true :: base) (true :: outer) (true :: output)
          simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.replicate_succ, zero_add,
              List.cons_append,
              Nat.add_assoc, Nat.reduceAdd, SourceStructuralDecoder.replicate_true_append_cons]
                  using
              EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest
  | succ first ih =>
      have hfirst := oneStep _ _ (unaryPair_greater_base_first
          (List.replicate first true)
          (List.replicate matchedFirst true)
          (List.replicate matchedSecond true)
          base outer output)
      have hrest := ih
        (true :: base) (true :: outer) (true :: output)
      have hfull := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest
      simp only [unaryPair_replicate_append_true] at hfull
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, Nat.add_comm, Nat.add_left_comm,
          Nat.reduceAdd,
          Nat.add_assoc] using hfull

/-- GapCVP reduction support. -/
def unaryPairGreaterOffsetTrace
    (count : ℕ) (base outer output : List Bool) :
    EvalsToInTime actualUnaryPairIndexMachine.step (unaryPairConfiguration 4 [] [] [] []
        (List.replicate count true) base outer output [])
      (some (unaryPairConfiguration 7 [] [] [] [] []
        base outer (List.replicate count true ++ output) []))
      (count + 1) := by
  induction count generalizing output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (unaryPair_greater_offset_finish base outer output)
  | succ count ih =>
      have hfirst := oneStep _ _ (unaryPair_greater_offset_step
          (List.replicate count true) base outer output)
      have hrest := ih (true :: output)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest

/-- GapCVP reduction support. -/
def unaryPairLessBaseTrace
    (second matchedFirst matchedSecond : ℕ)
    (base outer output : List Bool) :
    EvalsToInTime actualUnaryPairIndexMachine.step (unaryPairConfiguration 5 [] []
        (List.replicate second true)
        (List.replicate matchedFirst true)
        (List.replicate matchedSecond true)
        base outer output [])
      (some (unaryPairConfiguration 6 [] [] []
        (List.replicate matchedFirst true) []
        (List.replicate (second + matchedSecond) true ++ base)
        (List.replicate (second + matchedSecond) true ++ outer)
        output []))
      (second + matchedSecond + 1) := by
  induction second generalizing base outer with
  | zero =>
      induction matchedSecond generalizing base outer with
      | zero =>
          simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, add_zero, List.nil_append,
              zero_add] using
              oneStep _ _ (unaryPair_less_base_finish (List.replicate matchedFirst true) base outer
                  output)
      | succ matchedSecond ih =>
          have hfirst := oneStep _ _ (unaryPair_less_base_matched
              (List.replicate matchedFirst true)
              (List.replicate matchedSecond true)
              base outer output)
          have hrest := ih (true :: base) (true :: outer)
          simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.replicate_succ, zero_add,
              List.cons_append,
              Nat.add_assoc, Nat.reduceAdd, SourceStructuralDecoder.replicate_true_append_cons]
                  using
              EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest
  | succ second ih =>
      have hfirst := oneStep _ _ (unaryPair_less_base_second
          (List.replicate second true)
          (List.replicate matchedFirst true)
          (List.replicate matchedSecond true)
          base outer output)
      have hrest := ih (true :: base) (true :: outer)
      have hfull := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest
      simp only [unaryPair_replicate_append_true] at hfull
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, Nat.add_comm, Nat.add_left_comm,
          Nat.reduceAdd,
          Nat.add_assoc] using hfull

/-- GapCVP reduction support. -/
def unaryPairLessOffsetTrace
    (count : ℕ) (base outer output : List Bool) :
    EvalsToInTime actualUnaryPairIndexMachine.step (unaryPairConfiguration 6 [] [] []
        (List.replicate count true) [] base outer output [])
      (some (unaryPairConfiguration 7 [] [] [] [] []
        base outer (List.replicate count true ++ output) []))
      (count + 1) := by
  induction count generalizing output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (unaryPair_less_offset_finish base outer output)
  | succ count ih =>
      have hfirst := oneStep _ _ (unaryPair_less_offset_step
          (List.replicate count true) base outer output)
      have hrest := ih (true :: output)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest

end CNFUnaryPairIndexTotalCert


end GapCVP

end
