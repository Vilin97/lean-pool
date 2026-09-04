/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part05B

/-! # GapCVP proof, part 05, continuation 03 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace SourceLatticeStructuralRationalRadiusTM

open Turing GapCVP.SourceLatticeNormalizedSectionSynthesis

private def rationalRadiusFailureMeasure
    (input base outer restore output : List Bool) : ℕ :=
  input.length + base.length + outer.length +
    restore.length + output.length

private def rationalRadius_failureTrace
    (input base outer restore output : List Bool) :
    EvalsToInTime rationalRadiusMachine.step (rationalRadiusConfiguration 6
        input base outer restore output)
      (some (Turing.haltList rationalRadiusMachine [false]))
      (rationalRadiusFailureMeasure
        input base outer restore output + 1) := by
  induction input generalizing base outer restore output with
  | cons bit input ih =>
      have hfirst := oneStep _ _ (rationalRadius_failure_input_step
          bit input base outer restore output)
      have hrest := ih base outer restore output
      have hfull := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hfirst hrest
      exact rebound hfull (by
        simp only [rationalRadiusFailureMeasure, List.length_cons, add_le_add_iff_right,
            Order.add_one_le_iff,
            add_lt_add_iff_right, lt_add_iff_pos_right, Order.lt_one_iff])
  | nil =>
      induction base generalizing outer restore output with
      | cons bit base ih =>
          have hfirst := oneStep _ _ (rationalRadius_failure_base_step
              bit base outer restore output)
          have hrest := ih outer restore output
          have hfull := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hfirst hrest
          exact rebound hfull (by
            simp only [rationalRadiusFailureMeasure, List.length_nil, zero_add, List.length_cons,
                add_le_add_iff_right,
                Order.add_one_le_iff, add_lt_add_iff_right, lt_add_iff_pos_right,
                    Order.lt_one_iff])
      | nil =>
          induction outer generalizing restore output with
          | cons bit outer ih =>
              have hfirst := oneStep _ _ (rationalRadius_failure_outer_step
                  bit outer restore output)
              have hrest := ih restore output
              have hfull := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hfirst hrest
              exact rebound hfull (by
                simp only [rationalRadiusFailureMeasure, List.length_nil, add_zero, zero_add,
                    List.length_cons,
                    add_le_add_iff_right, Order.add_one_le_iff, add_lt_add_iff_right,
                        lt_add_iff_pos_right, Order.lt_one_iff])
          | nil =>
              induction restore generalizing output with
              | cons bit restore ih =>
                  have hfirst := oneStep _ _ (rationalRadius_failure_restore_step
                      bit restore output)
                  have hrest := ih output
                  have hfull := EvalsToInTime.trans
                    rationalRadiusMachine.step _ _ _ _ _ hfirst hrest
                  exact rebound hfull (by
                    simp only [rationalRadiusFailureMeasure, List.length_nil, add_zero, zero_add,
                        List.length_cons,
                        add_le_add_iff_right, Order.add_one_le_iff, add_lt_add_iff_right,
                            lt_add_iff_pos_right, Order.lt_one_iff])
              | nil =>
                  induction output with
                  | nil =>
                      simpa only [FinTM2.step, Fin.isValue, rationalRadiusFailureMeasure,
                          List.length_nil, add_zero, zero_add] using
                          oneStep _ _ rationalRadius_failure_finish
                  | cons bit output ih =>
                      have hfirst := oneStep _ _ (rationalRadius_failure_output_step bit output)
                      have hfull := EvalsToInTime.trans
                        rationalRadiusMachine.step _ _ _ _ _ hfirst ih
                      exact rebound hfull (by
                        simp only [rationalRadiusFailureMeasure, List.length_nil, add_zero,
                            zero_add, List.length_cons, Std.le_refl])

private def rationalRadius_copyTrace
    (count : ℕ) (outer restore output : List Bool) :
    EvalsToInTime rationalRadiusMachine.step (rationalRadiusConfiguration 3 []
        (List.replicate count true) outer restore output)
      (some (rationalRadiusConfiguration 4 [] [] outer
        (List.replicate count true ++ restore)
        (List.replicate count true ++ output)))
      (count + 1) := by
  induction count generalizing restore output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (rationalRadius_copy_finish outer restore output)
  | succ count ih =>
      have hfirst := oneStep _ _ (rationalRadius_copy_step
          (List.replicate count true) outer restore output)
      have hrest := ih (true :: restore) (true :: output)
      have hfull := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

private def rationalRadius_restoreTrace
    (count : ℕ) (base outer output : List Bool) :
    EvalsToInTime rationalRadiusMachine.step (rationalRadiusConfiguration 4 [] base outer
        (List.replicate count true) output)
      (some (rationalRadiusConfiguration 2 []
        (List.replicate count true ++ base) outer [] output))
      (count + 1) := by
  induction count generalizing base with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (rationalRadius_restore_finish base outer output)
  | succ count ih =>
      have hfirst := oneStep _ _ (rationalRadius_restore_step base outer
          (List.replicate count true) output)
      have hrest := ih (true :: base)
      have hfull := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

private def rationalRadius_baseCopyTrace
    (baseSize : ℕ) (outer output : List Bool) :
    EvalsToInTime rationalRadiusMachine.step (rationalRadiusConfiguration 3 []
        (List.replicate baseSize true) outer [] output)
      (some (rationalRadiusConfiguration 2 []
        (List.replicate baseSize true) outer []
        (List.replicate baseSize true ++ output)))
      (2 * baseSize + 2) := by
  have hcopy := rationalRadius_copyTrace baseSize outer [] output
  simp only [List.append_nil] at hcopy
  have hrestore := rationalRadius_restoreTrace
    baseSize [] outer (List.replicate baseSize true ++ output)
  simp only [List.append_nil] at hrestore
  have hfull := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hcopy hrestore
  exact rebound hfull (by omega)

private def rationalRadius_cleanupTrace
    (count : ℕ) (output : List Bool) :
    EvalsToInTime rationalRadiusMachine.step (rationalRadiusConfiguration 5 []
        (List.replicate count true) [] [] output)
      (some (Turing.haltList rationalRadiusMachine
        (true :: output)))
      (count + 1) := by
  induction count with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, zero_add] using
          oneStep _ _ (rationalRadius_cleanup_finish output)
  | succ count ih =>
      have hfirst := oneStep _ _ (rationalRadius_cleanup_base_step
          (List.replicate count true) output)
      have hfull := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hfirst ih
      exact rebound hfull (by omega)

private def rationalRadius_outerTrace
    (baseSize count : ℕ) (output : List Bool) :
    EvalsToInTime rationalRadiusMachine.step (rationalRadiusConfiguration 2 []
        (List.replicate baseSize true)
        (List.replicate count true) [] output)
      (some (Turing.haltList rationalRadiusMachine
        (true ::
          (List.replicate (count * baseSize) true ++ output))))
      (count * (2 * baseSize + 3) + baseSize + 2) := by
  induction count generalizing output with
  | zero =>
      have hfirst := oneStep _ _ (rationalRadius_outer_finish
          (List.replicate baseSize true) [] output)
      have hcleanup := rationalRadius_cleanupTrace baseSize output
      have hfull := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hfirst hcleanup
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, zero_mul, List.nil_append,
          zero_add] using hfull
  | succ count ih =>
      have hdispatch := oneStep _ _ (rationalRadius_outer_step
          (List.replicate baseSize true)
          (List.replicate count true) [] output)
      have hcopy := rationalRadius_baseCopyTrace
        baseSize (List.replicate count true) output
      have hprefix := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hdispatch hcopy
      have hrest := ih (List.replicate baseSize true ++ output)
      have hblocks :
          List.replicate (count * baseSize) true ++
              (List.replicate baseSize true ++ output) =
            List.replicate ((count + 1) * baseSize)
              true ++ output := by
        rw [Nat.add_mul, Nat.one_mul,
          List.replicate_add, List.append_assoc]
      rw [hblocks] at hrest
      have hfull := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hprefix hrest
      have hbounded := rebound (newBudget :=
          (count + 1) * (2 * baseSize + 3) + baseSize + 2)
        hfull (by
          simp only [Nat.mul_add, Nat.add_mul, one_mul]
          omega)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ] using hbounded

private def rationalRadiusScanOutput
    (input : List Bool) (count : ℕ) : List Bool :=
  if input.all (fun bit => bit) then
    true :: List.replicate
      (4 * (count + input.length) ^ 2 +
        2 * (count + input.length) + 1) true
  else
    [false]

private def rationalRadiusScanBudget
    (input : List Bool) (count : ℕ) : ℕ :=
  64 * (count + input.length + 1) ^ 2 +
    32 * (input.length + 1) + 64

private def rationalRadius_scanTrace
    (input : List Bool) (count : ℕ) :
    EvalsToInTime rationalRadiusMachine.step (rationalRadiusConfiguration 1 input
        (List.replicate (2 * count) true)
        (List.replicate (2 * count) true) []
        (List.replicate (2 * count + 1) true))
      (some (Turing.haltList rationalRadiusMachine
        (rationalRadiusScanOutput input count)))
      (rationalRadiusScanBudget input count) := by
  induction input generalizing count with
  | nil =>
      have hfirst := oneStep _ _ (rationalRadius_scan_finish
          (List.replicate (2 * count) true)
          (List.replicate (2 * count) true) []
          (List.replicate (2 * count + 1) true))
      have houter := rationalRadius_outerTrace
        (2 * count) (2 * count)
        (List.replicate (2 * count + 1) true)
      have hword :
          List.replicate ((2 * count) * (2 * count)) true ++
              List.replicate (2 * count + 1) true =
            List.replicate
              (4 * count ^ 2 + 2 * count + 1) true := by
        rw [← List.replicate_add]
        congr 1
        ring
      rw [hword] at houter
      have hfull := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hfirst houter
      have hbounded := rebound (newBudget := rationalRadiusScanBudget [] count)
        hfull (by
          simp only [rationalRadiusScanBudget, List.length_nil, add_zero, pow_two, zero_add,
              mul_one,
              add_le_add_iff_right]
          nlinarith)
      simpa only [FinTM2.step, Fin.isValue, rationalRadiusScanOutput, List.all_nil, ↓reduceIte,
          List.length_nil,
          add_zero] using hbounded
  | cons bit input ih =>
      cases bit with
      | false =>
          have hfirst := oneStep _ _ (rationalRadius_scan_false_step input
              (List.replicate (2 * count) true)
              (List.replicate (2 * count) true) []
              (List.replicate (2 * count + 1) true))
          have hfailure := rationalRadius_failureTrace input
            (List.replicate (2 * count) true)
            (List.replicate (2 * count) true) []
            (List.replicate (2 * count + 1) true)
          have hfull := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hfirst hfailure
          have hbounded := rebound (newBudget := rationalRadiusScanBudget
              (false :: input) count)
            hfull (by
              simp only [rationalRadiusFailureMeasure, List.length_replicate, List.length_nil,
                  add_zero,
                  rationalRadiusScanBudget, List.length_cons, pow_two, add_le_add_iff_right]
              nlinarith)
          simpa only [FinTM2.step, Fin.isValue, rationalRadiusScanOutput, List.all_cons,
              Bool.false_and,
              Bool.false_eq_true, ↓reduceIte] using hbounded
      | true =>
          have hfirst := oneStep _ _ (rationalRadius_scan_true_step input
              (List.replicate (2 * count) true)
              (List.replicate (2 * count) true) []
              (List.replicate (2 * count + 1) true))
          have hrest := ih (count + 1)
          have hbase :
              List.replicate (2 * (count + 1)) true =
                true :: true ::
                  List.replicate (2 * count) true := by
            rw [show 2 * (count + 1) =
              (2 * count + 1) + 1 by omega,
              List.replicate_succ, List.replicate_succ]
          have houtput :
              List.replicate (2 * (count + 1) + 1) true =
                true :: true ::
                  List.replicate (2 * count + 1) true := by
            rw [show 2 * (count + 1) + 1 =
              ((2 * count + 1) + 1) + 1 by omega,
              List.replicate_succ, List.replicate_succ]
          rw [hbase, houtput] at hrest
          have htarget :
              rationalRadiusScanOutput input (count + 1) =
                rationalRadiusScanOutput
                  (true :: input) count := by
            simp only [rationalRadiusScanOutput, List.all_eq_true, Bool.forall_bool,
                Bool.false_eq_true, imp_false,
                implies_true, and_true, Nat.add_comm, Nat.add_left_comm, ite_not, List.all_cons,
                    Bool.true_and, List.length_cons]
          rw [htarget] at hrest
          have hfull := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hfirst hrest
          have hbounded := rebound (newBudget := rationalRadiusScanBudget
              (true :: input) count)
            hfull (by
              simp only [rationalRadiusScanBudget, pow_two, List.length_cons, add_le_add_iff_right,
                  Nat.reduceLeDiff,
                  Order.add_one_le_iff]
              nlinarith)
          exact hbounded

/-- GapCVP reduction support. -/
def rationalRadiusUnaryOutput : List Bool → List Bool
  | [] => [false]
  | false :: _ => [false]
  | true :: input => rationalRadiusScanOutput input 0

private def rationalRadiusInputBudget (input : List Bool) : ℕ :=
  128 * input.length ^ 2 + 128 * input.length + 256

private def rationalRadius_totalTrace (input : List Bool) :
    EvalsToInTime rationalRadiusMachine.step (rationalRadiusConfiguration 0 input [] [] [] [])
      (some (Turing.haltList rationalRadiusMachine
        (rationalRadiusUnaryOutput input)))
      (rationalRadiusInputBudget input) := by
  cases input with
  | nil =>
      have hfirst := oneStep _ _ (rationalRadius_marker_missing_step [] [] [] [])
      have hfailure := rationalRadius_failureTrace [] [] [] [] []
      have hfull := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hfirst hfailure
      have hbounded := rebound (newBudget := rationalRadiusInputBudget [])
        hfull (by
          simp only [rationalRadiusFailureMeasure, List.length_nil, add_zero, zero_add,
              Nat.reduceAdd,
              rationalRadiusInputBudget, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
                  mul_zero, Nat.reduceLeDiff])
      simpa only [FinTM2.step, Fin.isValue, rationalRadiusUnaryOutput] using hbounded
  | cons bit input =>
      cases bit with
      | false =>
          have hfirst := oneStep _ _ (rationalRadius_marker_false_step input [] [] [] [])
          have hfailure := rationalRadius_failureTrace
            input [] [] [] []
          have hfull := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hfirst hfailure
          have hbounded := rebound (newBudget := rationalRadiusInputBudget
              (false :: input))
            hfull (by
              simp only [rationalRadiusFailureMeasure, List.length_nil, add_zero,
                  rationalRadiusInputBudget,
                  List.length_cons, pow_two, add_le_add_iff_right]
              nlinarith)
          simpa only [FinTM2.step, Fin.isValue, rationalRadiusUnaryOutput] using hbounded
      | true =>
          have hfirst := oneStep _ _ (rationalRadius_marker_true_step input [] [] [] [])
          have hscan :
              EvalsToInTime rationalRadiusMachine.step
                (rationalRadiusConfiguration 1
                  input [] [] [] [true])
                (some (Turing.haltList rationalRadiusMachine
                  (rationalRadiusScanOutput input 0)))
                (rationalRadiusScanBudget input 0) := by
            simpa only [FinTM2.step, Fin.isValue, mul_zero, List.replicate_zero, zero_add,
                List.replicate_one] using
                rationalRadius_scanTrace input 0
          have hfull := EvalsToInTime.trans rationalRadiusMachine.step _ _ _ _ _ hfirst hscan
          have hbounded := rebound (newBudget := rationalRadiusInputBudget
              (true :: input))
            hfull (by
              simp only [rationalRadiusScanBudget, zero_add, pow_two, rationalRadiusInputBudget,
                  List.length_cons,
                  add_le_add_iff_right]
              nlinarith)
          simpa only [FinTM2.step, Fin.isValue, rationalRadiusUnaryOutput] using hbounded

/-- GapCVP reduction support. -/
noncomputable def rationalRadiusUnaryComputable :
    BitTM
      rationalRadiusUnaryOutput where
  tm := rationalRadiusMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 128 * Polynomial.X ^ 2 +
    128 * Polynomial.X + 256
  outputsFun input := {
    steps := (rationalRadius_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, rationalRadiusMachine_init,
              Option.map_some] using
          (rationalRadius_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (rationalRadius_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, rationalRadiusInputBudget, bitEncoding, id_eq,
          Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_X,
              ge_iff_le] using hsteps
  }

theorem rationalRadiusUnaryOutput_marked
    (number : ℕ) :
    rationalRadiusUnaryOutput
        (true :: List.replicate number true) =
      true :: List.replicate
        (4 * number ^ 2 + 2 * number + 1) true := by
  simp only [rationalRadiusUnaryOutput, rationalRadiusScanOutput, List.all_replicate, ite_self,
      ↓reduceIte,
      List.length_replicate, zero_add]

end SourceLatticeStructuralRationalRadiusTM

namespace SourceInterpolationRowTM

open GapCVP.BinaryEncoding

theorem readUnaryPrefix_some_decompose
    (input : List Bool) (count : ℕ) (suffix : List Bool)
    (hread : readUnaryPrefix input = some (count, suffix)) :
    input = List.replicate count true ++ false :: suffix := by
  induction input generalizing count suffix with
  | nil => simp only [readUnaryPrefix, reduceCtorEq] at hread
  | cons bit rest ih =>
      cases bit with
      | false =>
          simp only [readUnaryPrefix, Option.some.injEq, Prod.mk.injEq] at hread
          rcases hread with ⟨rfl, rfl⟩
          rfl
      | true =>
          cases hrest : readUnaryPrefix rest with
          | none => simp only [readUnaryPrefix, hrest, reduceCtorEq] at hread
          | some pair =>
              rcases pair with ⟨number, tail⟩
              simp only [readUnaryPrefix, hrest, Option.some.injEq, Prod.mk.injEq] at hread
              rcases hread with ⟨rfl, rfl⟩
              have htail := ih number tail hrest
              simp only [htail, List.replicate_succ, List.cons_append]

theorem readUnaryPrefix_none_eq_replicate
    (input : List Bool)
    (hread : readUnaryPrefix input = none) :
    input = List.replicate input.length true := by
  induction input with
  | nil => rfl
  | cons bit rest ih =>
      cases bit with
      | false => simp only [readUnaryPrefix, reduceCtorEq] at hread
      | true =>
          cases hrest : readUnaryPrefix rest with
          | none =>
              have htail := ih hrest
              simpa only [List.length_cons, List.replicate_succ]
                using congrArg (fun tail : List Bool => true :: tail) htail
          | some pair =>
              simp only [readUnaryPrefix, hrest, reduceCtorEq] at hread

end SourceInterpolationRowTM

namespace SourceWholeOutputAssemblyTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceLatticeFormulaPreservation
open GapCVP.SourceLatticeDependentSectionComputation GapCVP.FormulaTotalCert
open GapCVP.OutputBoundedDependentRecordFold

/-- GapCVP reduction support. -/
def sourceVectorStructuralRecords
    {α : Type*} [Encodable α]
    (n : ℕ) (values : Fin n → α) : List (List Bool) :=
  List.ofFn (fun index => encodeAtomic (values index))

theorem sourceVectorStructuralRecords_flatten
    {α : Type*} [Encodable α]
    (n : ℕ) (values : Fin n → α) :
    (sourceVectorStructuralRecords n values).flatten =
      encodeFinValues n values := by
  induction n with
  | zero =>
      simp only [sourceVectorStructuralRecords, List.ofFn_zero, List.flatten_nil, encodeFinValues]
  | succ n ih =>
      have htail := ih (fun index : Fin n => values index.succ)
      have hfull := congrArg
        (fun tail : List Bool => encodeAtomic (values 0) ++ tail)
        htail
      simpa only [sourceVectorStructuralRecords, List.ofFn_succ, List.flatten_cons,
          encodeFinValues,
          List.append_cancel_left_eq] using hfull

/-- GapCVP reduction support. -/
def sourceMatrixStructuralRecords
    (m n : ℕ) (matrix : Fin m → Fin n → ℤ) :
    List (List Bool) :=
  (List.ofFn (fun row =>
    sourceVectorStructuralRecords n (matrix row))).flatten

theorem sourceMatrixStructuralRecords_flatten
    (m n : ℕ) (matrix : Fin m → Fin n → ℤ) :
    (sourceMatrixStructuralRecords m n matrix).flatten =
      encodeMatrixRows m n matrix := by
  induction m with
  | zero =>
      simp only [sourceMatrixStructuralRecords, List.ofFn_zero, List.flatten_nil, encodeMatrixRows]
  | succ m ih =>
      have htail := ih (fun index : Fin m => matrix index.succ)
      have hfull := congrArg
        (fun tail : List Bool =>
          encodeFinValues n (matrix 0) ++ tail)
        htail
      simpa only [sourceMatrixStructuralRecords, List.ofFn_succ, List.flatten_cons,
          List.flatten_append,
          sourceVectorStructuralRecords_flatten, encodeMatrixRows, List.append_cancel_left_eq]
              using hfull

@[simp] theorem sourceVectorStructuralRecords_length
    {α : Type*} [Encodable α]
    (n : ℕ) (values : Fin n → α) :
    (sourceVectorStructuralRecords n values).length = n := by
  simp only [sourceVectorStructuralRecords, List.length_ofFn]

@[simp] theorem sourceMatrixStructuralRecords_length
    (m n : ℕ) (matrix : Fin m → Fin n → ℤ) :
    (sourceMatrixStructuralRecords m n matrix).length = m * n := by
  induction m with
  | zero =>
      simp only [sourceMatrixStructuralRecords, List.ofFn_zero, List.flatten_nil, List.length_nil,
          zero_mul]
  | succ m ih =>
      have htail := ih (fun index : Fin m => matrix index.succ)
      have hfull := congrArg (fun length : ℕ => n + length) htail
      simpa only [sourceMatrixStructuralRecords, List.ofFn_succ, List.flatten_cons,
          List.length_append,
          sourceVectorStructuralRecords_length, List.length_flatten, List.map_ofFn, Nat.succ_mul,
              Nat.add_comm,
          Nat.add_left_cancel_iff] using hfull

/-- GapCVP reduction support. -/
def sourceLatticeStructuralRecords
    (lattice : GapCVPInstance) : List (List Bool) :=
  [encodeAtomic lattice.dimension, encodeAtomic lattice.radius] ++
    sourceVectorStructuralRecords lattice.dimension lattice.target ++
    sourceMatrixStructuralRecords lattice.dimension lattice.dimension
      (Matrix.of.symm lattice.basis)

theorem sourceLatticeStructuralRecords_flatten
    (lattice : GapCVPInstance) :
    (sourceLatticeStructuralRecords lattice).flatten =
      encodeGapCVPInstance lattice := by
  simp only [sourceLatticeStructuralRecords, List.cons_append, List.nil_append, List.flatten_cons,
      List.flatten_append, sourceVectorStructuralRecords_flatten,
      encodeGapCVPInstance, List.append_assoc]
  rw [sourceMatrixStructuralRecords_flatten]

@[simp] theorem sourceLatticeStructuralRecords_length
    (lattice : GapCVPInstance) :
    (sourceLatticeStructuralRecords lattice).length =
      2 + lattice.dimension +
        lattice.dimension * lattice.dimension := by
  simp only [sourceLatticeStructuralRecords, List.cons_append, List.nil_append, List.length_cons,
      List.length_append, sourceVectorStructuralRecords_length]
  rw [sourceMatrixStructuralRecords_length]
  omega

/-- GapCVP reduction support. -/
def constructiveCanonicalSourceMarker (input : List Bool) : Bool :=
  match decodeThreeCNF input with
  | none => false
  | some formula => decide (encodeThreeCNF formula = input)

private theorem validatedPreservedFormulaOutput_constructiveMarker
    (input : List Bool) :
    validatedPreservedFormulaOutput input =
      constructiveCanonicalSourceMarker input :: input := by
  unfold validatedPreservedFormulaOutput
  rw [Function.comp_apply, formulaPreservedOutput_eq_expected]
  cases hdecode : decodeThreeCNF input with
  | none =>
      simp only [canonicalFormulaExpected, hdecode, sourceMarkerRotatedOutput_append_marker,
          constructiveCanonicalSourceMarker]
  | some formula =>
      by_cases hcanonical : encodeThreeCNF formula = input
      · simp only [canonicalFormulaExpected, hdecode, hcanonical, ↓reduceIte,
          sourceMarkerRotatedOutput_append_marker,
            constructiveCanonicalSourceMarker, decide_true]
      · simp only [canonicalFormulaExpected, hdecode, hcanonical, ↓reduceIte,
          sourceMarkerRotatedOutput_append_marker,
            constructiveCanonicalSourceMarker, decide_false]

/-- GapCVP reduction support. -/
noncomputable def constructiveCanonicalSourceMarkerComputable :
    BitTM
      (fun input => constructiveCanonicalSourceMarker input :: input) := by
  have hfunctions : validatedPreservedFormulaOutput =
      (fun input => constructiveCanonicalSourceMarker input :: input) :=
    funext validatedPreservedFormulaOutput_constructiveMarker
  rw [← hfunctions]
  exact validatedPreservedFormulaComputable

theorem sourceAtomicFoldSeed_length_le
    (input : List Bool) (count : ℕ) (seed : List Bool)
    (hparse : parseUnaryBoundedFold input = some (count, seed)) :
    seed.length ≤ input.length := by
  exact GapCVP.CNFTypedRecordWorkerTM.parsedUnaryFold_seed_length_le input count seed hparse

end SourceWholeOutputAssemblyTM

namespace SourceWholeOutputValidBranchRecordTM

open Turing GapCVP.BinaryEncoding GapCVP.FormulaSemanticCert
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceWholeOutputAssemblyTM

/-- GapCVP reduction support. -/
def sourceFlatAtomicDescriptor (record : List Bool) : List Bool :=
  lengthPrefixedWord record

/-- GapCVP reduction support. -/
def sourceFlatAtomicRecordStep (input : List Bool) : List Bool :=
  match readLengthPrefixedWord input with
  | none => []
  | some (record, pending) => pending ++ record

@[simp] theorem sourceFlatAtomicRecordStep_descriptor
    (record pending : List Bool) :
    sourceFlatAtomicRecordStep
        (sourceFlatAtomicDescriptor record ++ pending) =
      pending ++ record := by
  simp only [sourceFlatAtomicRecordStep, sourceFlatAtomicDescriptor, readLengthPrefixedWord_append]

/-- GapCVP reduction support. -/
def sourceFlatAtomicDescriptorStream
    (records : List (List Bool)) : List Bool :=
  records.flatMap sourceFlatAtomicDescriptor

theorem sourceFlatAtomicRecordStep_iterate_descriptors
    (records : List (List Bool)) (emitted : List Bool) :
    ((sourceFlatAtomicRecordStep^[records.length])
      (sourceFlatAtomicDescriptorStream records ++ emitted)) =
        emitted ++ records.flatten := by
  induction records generalizing emitted with
  | nil =>
      simp only [List.length_nil, sourceFlatAtomicDescriptorStream, List.flatMap_nil,
          List.nil_append,
          Function.iterate_zero, id_eq, List.flatten_nil, List.append_nil]
  | cons record remaining ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [sourceFlatAtomicDescriptorStream,
        List.flatMap_cons, List.append_assoc]
      rw [sourceFlatAtomicRecordStep_descriptor]
      simpa only [List.append_assoc, List.flatten_cons, sourceFlatAtomicDescriptorStream] using
          ih (emitted ++ record)

private theorem sourceFlatAtomicRecordStep_length_le
    (input : List Bool) :
    (sourceFlatAtomicRecordStep input).length ≤ input.length := by
  cases hread : readLengthPrefixedWord input with
  | none =>
      simp only [sourceFlatAtomicRecordStep, hread, List.length_nil, zero_le]
  | some parsed =>
      obtain ⟨record, pending⟩ := parsed
      have hinput := readLengthPrefixedWord_some_reconstruct
        input record pending hread
      simp only [sourceFlatAtomicRecordStep, hread]
      rw [hinput]
      simp only [List.length_append,
        lengthPrefixedWord_length]
      omega

private theorem sourceFlatAtomicRecordStep_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates
      sourceFlatAtomicRecordStep Polynomial.X := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage hstage
  have hseed := sourceAtomicFoldSeed_length_le
    input count seed hparse
  have hiterate : ∀ number : ℕ,
      ((sourceFlatAtomicRecordStep^[number]) seed).length ≤
        seed.length := by
    intro number
    induction number with
    | zero => simp only [Function.iterate_zero, id_eq, Std.le_refl]
    | succ number ih =>
        rw [Function.iterate_succ_apply']
        exact (sourceFlatAtomicRecordStep_length_le _).trans ih
  simpa only [Polynomial.eval_X, ge_iff_le] using (hiterate stage).trans hseed

private def sourceFlatAtomicPeek (stack : Fin 5)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) :=
  .peek stack (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome) present absent)

private def sourceFlatAtomicPop (stack : Fin 5)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) :=
  .pop stack (fun state _ => state) continuation

private def sourceFlatAtomicPushBit (stack : Fin 5)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) :=
  .push stack (fun state => state.getD false) continuation

private def sourceFlatAtomicPushConstant (stack : Fin 5) (bit : Bool)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) :=
  .push stack (fun _ => bit) continuation

private def sourceFlatAtomicGoto (phase : Fin 6) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => phase))

private def sourceFlatAtomicPrefixStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) :=
  sourceFlatAtomicPeek 0
    (.branch (fun state => state.getD false)
      (sourceFlatAtomicPop 0
        (sourceFlatAtomicPushConstant 1 true
          (sourceFlatAtomicGoto 0)))
      (sourceFlatAtomicPop 0 (sourceFlatAtomicGoto 1)))
    (sourceFlatAtomicGoto 5)

private def sourceFlatAtomicPayloadStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) :=
  sourceFlatAtomicPeek 1
    (sourceFlatAtomicPop 1
      (sourceFlatAtomicPeek 0
        (sourceFlatAtomicPop 0
          (sourceFlatAtomicPushBit 2
            (sourceFlatAtomicGoto 1)))
        (sourceFlatAtomicGoto 5)))
    (sourceFlatAtomicGoto 2)

private def sourceFlatAtomicPayloadOutputStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) :=
  sourceFlatAtomicPeek 2
    (sourceFlatAtomicPop 2
      (sourceFlatAtomicPushBit 4
        (sourceFlatAtomicGoto 2)))
    (sourceFlatAtomicGoto 3)

private def sourceFlatAtomicPendingStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) :=
  sourceFlatAtomicPeek 0
    (sourceFlatAtomicPop 0
      (sourceFlatAtomicPushBit 3
        (sourceFlatAtomicGoto 3)))
    (sourceFlatAtomicGoto 4)

private def sourceFlatAtomicRestoreStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) :=
  sourceFlatAtomicPeek 3
    (sourceFlatAtomicPop 3
      (sourceFlatAtomicPushBit 4
        (sourceFlatAtomicGoto 4)))
    .halt

private def sourceFlatAtomicFailureStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) :=
  sourceFlatAtomicPeek 0
    (sourceFlatAtomicPop 0 (sourceFlatAtomicGoto 5))
    (sourceFlatAtomicPeek 1
      (sourceFlatAtomicPop 1 (sourceFlatAtomicGoto 5))
      (sourceFlatAtomicPeek 2
        (sourceFlatAtomicPop 2 (sourceFlatAtomicGoto 5))
        (sourceFlatAtomicPeek 3
          (sourceFlatAtomicPop 3 (sourceFlatAtomicGoto 5))
          (sourceFlatAtomicPeek 4
            (sourceFlatAtomicPop 4 (sourceFlatAtomicGoto 5))
            .halt))))

private abbrev sourceFlatAtomicRecordMachine : Turing.FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Fin 6
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 6) then sourceFlatAtomicPrefixStatement
    else if phase = (1 : Fin 6) then sourceFlatAtomicPayloadStatement
    else if phase = (2 : Fin 6) then
      sourceFlatAtomicPayloadOutputStatement
    else if phase = (3 : Fin 6) then sourceFlatAtomicPendingStatement
    else if phase = (4 : Fin 6) then sourceFlatAtomicRestoreStatement
    else sourceFlatAtomicFailureStatement

private def sourceFlatAtomicConfiguration (phase : Fin 6)
    (input counter payload pending output : List Bool) :
    sourceFlatAtomicRecordMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, counter, payload, pending, output]

private theorem sourceFlatAtomicRecordMachine_init (input : List Bool) :
    Turing.initList sourceFlatAtomicRecordMachine input =
      sourceFlatAtomicConfiguration 0 input [] [] [] [] := by
  simp only [sourceFlatAtomicRecordMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq,
      dite_eq_ite,
      sourceFlatAtomicConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `sourceFlatAtomicStepTac` machine-step simplifier. -/
macro "sourceFlatAtomicStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [sourceFlatAtomicRecordMachine,
          sourceFlatAtomicConfiguration,
          sourceFlatAtomicPeek, sourceFlatAtomicPop,
          sourceFlatAtomicPushBit, sourceFlatAtomicPushConstant,
          sourceFlatAtomicGoto, sourceFlatAtomicPrefixStatement,
          sourceFlatAtomicPayloadStatement,
          sourceFlatAtomicPayloadOutputStatement,
          sourceFlatAtomicPendingStatement,
          sourceFlatAtomicRestoreStatement,
          sourceFlatAtomicFailureStatement,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

private theorem sourceFlatAtomic_prefix_true
    (input counter payload pending output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 0
        (true :: input) counter payload pending output) =
      some (sourceFlatAtomicConfiguration 0
        input (true :: counter) payload pending output) := by
  sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_prefix_delimiter
    (input counter payload pending output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 0
        (false :: input) counter payload pending output) =
      some (sourceFlatAtomicConfiguration 1
        input counter payload pending output) := by
  sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_prefix_missing
    (counter payload pending output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 0
        [] counter payload pending output) =
      some (sourceFlatAtomicConfiguration 5
        [] counter payload pending output) := by
  sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_payload_step
    (bit : Bool) (input counter payload pending output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 1
        (bit :: input) (true :: counter)
        payload pending output) =
      some (sourceFlatAtomicConfiguration 1
        input counter (bit :: payload) pending output) := by
  cases bit <;> sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_payload_missing
    (counter payload pending output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 1
        [] (true :: counter) payload pending output) =
      some (sourceFlatAtomicConfiguration 5
        [] counter payload pending output) := by
  sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_payload_finish
    (input payload pending output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 1
        input [] payload pending output) =
      some (sourceFlatAtomicConfiguration 2
        input [] payload pending output) := by
  sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_payload_output_step
    (bit : Bool) (input payload pending output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 2
        input [] (bit :: payload) pending output) =
      some (sourceFlatAtomicConfiguration 2
        input [] payload pending (bit :: output)) := by
  cases bit <;> sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_payload_output_finish
    (input pending output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 2
        input [] [] pending output) =
      some (sourceFlatAtomicConfiguration 3
        input [] [] pending output) := by
  sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_pending_step
    (bit : Bool) (input pending output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 3
        (bit :: input) [] [] pending output) =
      some (sourceFlatAtomicConfiguration 3
        input [] [] (bit :: pending) output) := by
  cases bit <;> sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_pending_finish
    (pending output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 3
        [] [] [] pending output) =
      some (sourceFlatAtomicConfiguration 4
        [] [] [] pending output) := by
  sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_restore_step
    (bit : Bool) (pending output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 4
        [] [] [] (bit :: pending) output) =
      some (sourceFlatAtomicConfiguration 4
        [] [] [] pending (bit :: output)) := by
  cases bit <;> sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_restore_finish (output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 4 [] [] [] [] output) =
      some (Turing.haltList sourceFlatAtomicRecordMachine output) := by
  sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_failure_input_step
    (bit : Bool) (input counter payload pending output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 5
        (bit :: input) counter payload pending output) =
      some (sourceFlatAtomicConfiguration 5
        input counter payload pending output) := by
  cases bit <;> sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_failure_counter_step
    (bit : Bool) (counter payload pending output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 5
        [] (bit :: counter) payload pending output) =
      some (sourceFlatAtomicConfiguration 5
        [] counter payload pending output) := by
  cases bit <;> sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_failure_payload_step
    (bit : Bool) (payload pending output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 5
        [] [] (bit :: payload) pending output) =
      some (sourceFlatAtomicConfiguration 5
        [] [] payload pending output) := by
  cases bit <;> sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_failure_pending_step
    (bit : Bool) (pending output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 5
        [] [] [] (bit :: pending) output) =
      some (sourceFlatAtomicConfiguration 5
        [] [] [] pending output) := by
  cases bit <;> sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_failure_output_step
    (bit : Bool) (output : List Bool) :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 5
        [] [] [] [] (bit :: output)) =
      some (sourceFlatAtomicConfiguration 5
        [] [] [] [] output) := by
  cases bit <;> sourceFlatAtomicStepTac

private theorem sourceFlatAtomic_failure_finish :
    sourceFlatAtomicRecordMachine.step
      (sourceFlatAtomicConfiguration 5 [] [] [] [] []) =
      some (Turing.haltList sourceFlatAtomicRecordMachine []) := by
  sourceFlatAtomicStepTac

private def sourceFlatAtomicSweepTrace
    {Configuration : Type*}
    (step : Configuration → Option Configuration)
    (configuration : List Bool → Configuration)
    (hstep : ∀ (bit : Bool) (remaining : List Bool),
      step (configuration (bit :: remaining)) =
        some (configuration remaining))
    (symbols : List Bool) :
    EvalsToInTime step (configuration symbols)
      (some (configuration []))
      symbols.length := by
  induction symbols with
  | nil =>
      simpa only [List.length_nil] using EvalsToInTime.refl step (configuration [])
  | cons bit symbols ih =>
      have hfirst : EvalsToInTime step
          (configuration (bit :: symbols))
          (some (configuration symbols)) 1 := {
        steps := 1
        evals_in_steps := hstep bit symbols
        steps_le_m := Nat.le_refl 1
      }
      have hfull := EvalsToInTime.trans step _ _ _ _ _ hfirst ih
      simpa only [List.length_cons] using hfull

private def sourceFlatAtomicFailureBudget
    (input counter payload pending output : List Bool) : ℕ :=
  input.length + counter.length + payload.length +
    pending.length + output.length + 1

private def sourceFlatAtomic_failureTrace
    (input counter payload pending output : List Bool) :
    EvalsToInTime sourceFlatAtomicRecordMachine.step (sourceFlatAtomicConfiguration 5
        input counter payload pending output)
      (some (Turing.haltList sourceFlatAtomicRecordMachine []))
      (sourceFlatAtomicFailureBudget
        input counter payload pending output) := by
  have hinput := sourceFlatAtomicSweepTrace
    sourceFlatAtomicRecordMachine.step
    (fun current => sourceFlatAtomicConfiguration 5
      current counter payload pending output)
    (fun bit remaining => sourceFlatAtomic_failure_input_step
      bit remaining counter payload pending output)
    input
  have hcounter := sourceFlatAtomicSweepTrace
    sourceFlatAtomicRecordMachine.step
    (fun current => sourceFlatAtomicConfiguration 5
      [] current payload pending output)
    (fun bit remaining => sourceFlatAtomic_failure_counter_step
      bit remaining payload pending output)
    counter
  have hpayload := sourceFlatAtomicSweepTrace
    sourceFlatAtomicRecordMachine.step
    (fun current => sourceFlatAtomicConfiguration 5
      [] [] current pending output)
    (fun bit remaining => sourceFlatAtomic_failure_payload_step
      bit remaining pending output)
    payload
  have hpending := sourceFlatAtomicSweepTrace
    sourceFlatAtomicRecordMachine.step
    (fun current => sourceFlatAtomicConfiguration 5
      [] [] [] current output)
    (fun bit remaining => sourceFlatAtomic_failure_pending_step
      bit remaining output)
    pending
  have houtput := sourceFlatAtomicSweepTrace
    sourceFlatAtomicRecordMachine.step
    (fun current => sourceFlatAtomicConfiguration 5
      [] [] [] [] current)
    (fun bit remaining => sourceFlatAtomic_failure_output_step
      bit remaining)
    output
  have hfinish := oneStep _ _ sourceFlatAtomic_failure_finish
  have hfirst := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step _ _ _ _ _ hinput hcounter
  have hsecond := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step _ _ _ _ _ hfirst hpayload
  have hthird := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step _ _ _ _ _ hsecond hpending
  have hfourth := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step _ _ _ _ _ hthird houtput
  have hfull := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step _ _ _ _ _ hfourth hfinish
  exact rebound hfull (by
    simp only [sourceFlatAtomicFailureBudget]
    omega)

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceFlatAtomic_trueCounter_append
    (count : ℕ) (counter : List Bool) :
    List.replicate count true ++ true :: counter =
      List.replicate (count + 1) true ++ counter := by
  exact GapCVP.CNFUnaryPairIndexTotalCert.unaryPair_replicate_append_true count counter

private def sourceFlatAtomic_prefixTrace
    (count : ℕ)
    (tail counter payload pending output : List Bool) :
    EvalsToInTime sourceFlatAtomicRecordMachine.step (sourceFlatAtomicConfiguration 0
        (List.replicate count true ++ false :: tail)
        counter payload pending output)
      (some (sourceFlatAtomicConfiguration 1
        tail (List.replicate count true ++ counter)
        payload pending output))
      (count + 1) := by
  induction count generalizing counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceFlatAtomic_prefix_delimiter tail counter payload pending output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceFlatAtomic_prefix_true
          (List.replicate count true ++ false :: tail)
          counter payload pending output)
      have hrest := ih (true :: counter)
      have hfull := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step
        1 (count + 1) _ _ _ hfirst hrest
      rw [sourceFlatAtomic_trueCounter_append count counter] at hfull
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_comm,
          Nat.add_left_comm,
          Nat.reduceAdd] using hfull

private def sourceFlatAtomic_payloadTrace
    (record tail payload pending output : List Bool) :
    EvalsToInTime sourceFlatAtomicRecordMachine.step (sourceFlatAtomicConfiguration 1
        (record ++ tail)
        (List.replicate record.length true)
        payload pending output)
      (some (sourceFlatAtomicConfiguration 2
        tail [] (record.reverse ++ payload) pending output))
      (record.length + 1) := by
  induction record generalizing payload with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.nil_append, List.length_nil, List.replicate_zero,
          List.reverse_nil,
          zero_add] using oneStep _ _ (sourceFlatAtomic_payload_finish tail payload pending output)
  | cons bit remaining ih =>
      have hfirst := oneStep _ _ (sourceFlatAtomic_payload_step bit
          (remaining ++ tail)
          (List.replicate remaining.length true)
          payload pending output)
      have hrest := ih (bit :: payload)
      have hfull := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step
        1 (remaining.length + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.cons_append, List.length_cons,
          List.replicate_succ,
          List.reverse_cons, List.append_assoc, List.nil_append, Nat.add_comm, Nat.add_left_comm,
              Nat.reduceAdd] using hfull

private def sourceFlatAtomic_payloadOutputTrace
    (input payload pending output : List Bool) :
    EvalsToInTime sourceFlatAtomicRecordMachine.step (sourceFlatAtomicConfiguration 2
        input [] payload pending output)
      (some (sourceFlatAtomicConfiguration 3
        input [] [] pending (payload.reverse ++ output)))
      (payload.length + 1) := by
  induction payload generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (sourceFlatAtomic_payload_output_finish input pending output)
  | cons bit remaining ih =>
      have hfirst := oneStep _ _ (sourceFlatAtomic_payload_output_step
          bit input remaining pending output)
      have hrest := ih (bit :: output)
      have hfull := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step
        1 (remaining.length + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using hfull

private def sourceFlatAtomic_pendingTrace
    (input pending output : List Bool) :
    EvalsToInTime sourceFlatAtomicRecordMachine.step (sourceFlatAtomicConfiguration 3
        input [] [] pending output)
      (some (sourceFlatAtomicConfiguration 4
        [] [] [] (input.reverse ++ pending) output))
      (input.length + 1) := by
  induction input generalizing pending with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (sourceFlatAtomic_pending_finish pending output)
  | cons bit remaining ih =>
      have hfirst := oneStep _ _ (sourceFlatAtomic_pending_step
          bit remaining pending output)
      have hrest := ih (bit :: pending)
      have hfull := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step
        1 (remaining.length + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using hfull

private def sourceFlatAtomic_restoreTrace
    (pending output : List Bool) :
    EvalsToInTime sourceFlatAtomicRecordMachine.step (sourceFlatAtomicConfiguration 4
        [] [] [] pending output)
      (some (Turing.haltList sourceFlatAtomicRecordMachine
        (pending.reverse ++ output)))
      (pending.length + 1) := by
  induction pending generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (sourceFlatAtomic_restore_finish output)
  | cons bit remaining ih =>
      have hfirst := oneStep _ _ (sourceFlatAtomic_restore_step bit remaining output)
      have hrest := ih (bit :: output)
      have hfull := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step
        1 (remaining.length + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using hfull

private def sourceFlatAtomic_validTrace
    (record pending : List Bool) :
    EvalsToInTime sourceFlatAtomicRecordMachine.step (Turing.initList sourceFlatAtomicRecordMachine
        (sourceFlatAtomicDescriptor record ++ pending))
      (some (Turing.haltList sourceFlatAtomicRecordMachine
        (pending ++ record)))
      (4 * (sourceFlatAtomicDescriptor record ++ pending).length + 8) := by
  have hprefix := sourceFlatAtomic_prefixTrace
    record.length (record ++ pending) [] [] [] []
  simp only [List.append_nil] at hprefix
  rw [← sourceFlatAtomicRecordMachine_init] at hprefix
  have hpayload := sourceFlatAtomic_payloadTrace
    record pending [] [] []
  simp only [List.append_nil] at hpayload
  have hemit := sourceFlatAtomic_payloadOutputTrace
    pending record.reverse [] []
  simp only [List.reverse_reverse, List.append_nil] at hemit
  have hpending := sourceFlatAtomic_pendingTrace
    pending [] record
  simp only [List.append_nil] at hpending
  have hrestore := sourceFlatAtomic_restoreTrace
    pending.reverse record
  simp only [List.reverse_reverse] at hrestore
  have hfirst := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step _ _ _ _ _ hprefix hpayload
  have hsecond := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step _ _ _ _ _ hfirst hemit
  have hthird := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step _ _ _ _ _ hsecond hpending
  have hfull := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step _ _ _ _ _ hthird hrestore
  have hinput :
      List.replicate record.length true ++
          false :: (record ++ pending) =
        sourceFlatAtomicDescriptor record ++ pending := by
    simp only [sourceFlatAtomicDescriptor, lengthPrefixedWord, List.append_assoc, List.cons_append]
  rw [hinput] at hfull
  exact rebound hfull (by
    simp only [List.length_reverse, sourceFlatAtomicDescriptor, lengthPrefixedWord,
        List.append_assoc,
        List.cons_append, List.length_append, List.length_replicate, List.length_cons]
    omega)

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceFlatAtomic_readUnaryPrefix_some
    (input : List Bool) (count : ℕ) (tail : List Bool)
    (hread : readUnaryPrefix input = some (count, tail)) :
    input = List.replicate count true ++ false :: tail := by
  exact GapCVP.SourceInterpolationRowTM.readUnaryPrefix_some_decompose input count tail hread

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceFlatAtomic_readUnaryPrefix_none
    (input : List Bool)
    (hread : readUnaryPrefix input = none) :
    input = List.replicate input.length true := by
  exact GapCVP.SourceInterpolationRowTM.readUnaryPrefix_none_eq_replicate input hread

private def sourceFlatAtomic_missingPrefixTrace
    (count : ℕ) (counter payload pending output : List Bool) :
    EvalsToInTime sourceFlatAtomicRecordMachine.step (sourceFlatAtomicConfiguration 0
        (List.replicate count true) counter payload pending output)
      (some (sourceFlatAtomicConfiguration 5
        [] (List.replicate count true ++ counter)
        payload pending output))
      (count + 1) := by
  induction count generalizing counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceFlatAtomic_prefix_missing counter payload pending output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceFlatAtomic_prefix_true
          (List.replicate count true)
          counter payload pending output)
      have hrest := ih (true :: counter)
      have hfull := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step
        1 (count + 1) _ _ _ hfirst hrest
      rw [sourceFlatAtomic_trueCounter_append count counter] at hfull
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_comm,
          Nat.add_left_comm,
          Nat.reduceAdd] using hfull

private def sourceFlatAtomic_truncatedPayloadTrace
    (payload : List Bool) (missing : ℕ)
    (copied pending output : List Bool) :
    EvalsToInTime sourceFlatAtomicRecordMachine.step (sourceFlatAtomicConfiguration 1
        payload
        (List.replicate (payload.length + missing + 1) true)
        copied pending output)
      (some (sourceFlatAtomicConfiguration 5
        [] (List.replicate missing true)
        (payload.reverse ++ copied) pending output))
      (payload.length + 1) := by
  induction payload generalizing copied with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, zero_add, List.replicate_succ,
          List.reverse_nil,
          List.nil_append] using
          oneStep _ _ (sourceFlatAtomic_payload_missing (List.replicate missing true) copied
              pending output)
  | cons bit remaining ih =>
      have hcounter :
          List.replicate
              ((bit :: remaining).length + missing + 1) true =
            true :: List.replicate
              (remaining.length + missing + 1) true := by
        have hexponent :
            (bit :: remaining).length + missing + 1 =
              (remaining.length + missing + 1) + 1 := by
          simp only [List.length_cons]
          omega
        rw [hexponent, List.replicate_succ]
      rw [hcounter]
      have hfirst := oneStep _ _ (sourceFlatAtomic_payload_step bit remaining
          (List.replicate
            (remaining.length + missing + 1) true)
          copied pending output)
      have hrest := ih (bit :: copied)
      have hfull := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step
        1 (remaining.length + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, Nat.add_comm, Nat.add_assoc, List.reverse_cons,
          List.append_assoc,
          List.cons_append, List.nil_append, List.length_cons, Nat.add_left_comm, Nat.reduceAdd]
              using hfull

private noncomputable def sourceFlatAtomicTimePolynomial : Polynomial ℕ :=
  8 * Polynomial.X + 16

private noncomputable def sourceFlatAtomic_totalTrace (input : List Bool) :
    EvalsToInTime sourceFlatAtomicRecordMachine.step
      (Turing.initList sourceFlatAtomicRecordMachine input)
      (some (Turing.haltList sourceFlatAtomicRecordMachine
        (sourceFlatAtomicRecordStep input)))
      (sourceFlatAtomicTimePolynomial.eval input.length) := by
  cases hprefix : readUnaryPrefix input with
  | none =>
      have hshape := sourceFlatAtomic_readUnaryPrefix_none
        input hprefix
      have hscan := sourceFlatAtomic_missingPrefixTrace
        input.length [] [] [] []
      simp only [List.append_nil] at hscan
      rw [← hshape, ← sourceFlatAtomicRecordMachine_init] at hscan
      have hfailure := sourceFlatAtomic_failureTrace
        [] input [] [] []
      have hfull := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step
        _ _ _ _ _ hscan hfailure
      have houtput : sourceFlatAtomicRecordStep input = [] := by
        simp only [sourceFlatAtomicRecordStep, readLengthPrefixedWord, hprefix]
      rw [houtput]
      exact rebound hfull (by
        simp only [sourceFlatAtomicFailureBudget, List.length_nil, zero_add, add_zero,
            sourceFlatAtomicTimePolynomial,
            Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
        omega)
  | some parsed =>
      obtain ⟨count, tail⟩ := parsed
      have hshape := sourceFlatAtomic_readUnaryPrefix_some
        input count tail hprefix
      by_cases hcomplete : count ≤ tail.length
      · have hread :
            readLengthPrefixedWord input =
              some (tail.take count, tail.drop count) := by
          simp only [readLengthPrefixedWord, hprefix, hcomplete, ↓reduceIte]
        have hdescriptor := readLengthPrefixedWord_some_reconstruct
          input (tail.take count) (tail.drop count) hread
        have hphysical := sourceFlatAtomic_validTrace
          (tail.take count) (tail.drop count)
        simp only [sourceFlatAtomicDescriptor] at hphysical
        rw [← hdescriptor] at hphysical
        have houtput :
            sourceFlatAtomicRecordStep input =
              tail.drop count ++ tail.take count := by
          simp only [sourceFlatAtomicRecordStep, hread]
        rw [houtput]
        exact rebound hphysical (by
          simp only [sourceFlatAtomicTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
              Polynomial.eval_ofNat,
              Polynomial.eval_X, Nat.reduceLeDiff]
          omega)
      · have hshort : tail.length < count := by omega
        let missing : ℕ := count - tail.length - 1
        have hcount : count = tail.length + missing + 1 := by
          dsimp [missing]
          omega
        have hscan := sourceFlatAtomic_prefixTrace
          count tail [] [] [] []
        simp only [List.append_nil] at hscan
        rw [← hshape, ← sourceFlatAtomicRecordMachine_init] at hscan
        have hcopy := sourceFlatAtomic_truncatedPayloadTrace
          tail missing [] [] []
        simp only [List.append_nil] at hcopy
        rw [← hcount] at hcopy
        have hfailure := sourceFlatAtomic_failureTrace
          [] (List.replicate missing true) tail.reverse [] []
        have hfirst := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step
          _ _ _ _ _ hscan hcopy
        have hfull := EvalsToInTime.trans sourceFlatAtomicRecordMachine.step
          _ _ _ _ _ hfirst hfailure
        have houtput : sourceFlatAtomicRecordStep input = [] := by
          simp only [sourceFlatAtomicRecordStep, readLengthPrefixedWord, hprefix, hcomplete,
              ↓reduceIte]
        rw [houtput]
        exact rebound hfull (by
          simp only [sourceFlatAtomicFailureBudget, List.length_nil, List.length_replicate,
              zero_add,
              List.length_reverse, add_zero, sourceFlatAtomicTimePolynomial, Polynomial.eval_add,
                  Polynomial.eval_mul,
              Polynomial.eval_ofNat, Polynomial.eval_X]
          have hlength := congrArg List.length hshape
          simp only [List.length_append,
            List.length_replicate, List.length_cons] at hlength
          omega)

/-- GapCVP reduction support. -/
noncomputable def sourceFlatAtomicRecordComputable :
    BitTM
      sourceFlatAtomicRecordStep where
  tm := sourceFlatAtomicRecordMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := sourceFlatAtomicTimePolynomial
  outputsFun input := {
    steps := (sourceFlatAtomic_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, Option.map_some] using
          (sourceFlatAtomic_totalTrace input).evals_in_steps
    steps_le_m := by
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq] using (sourceFlatAtomic_totalTrace
          input).steps_le_m
  }

/-- GapCVP reduction support. -/
noncomputable def sourceFlatAtomicRecordFoldComputable :
    BitTM
      (boundedRecordFoldOutput sourceFlatAtomicRecordStep) :=
  boundedDependentRecordFoldComputable
    sourceFlatAtomicRecordComputable Polynomial.X
    sourceFlatAtomicRecordStep_polynomiallyBoundedFoldStates

theorem boundedRecordFoldOutput_sourceFlatAtomicDescriptors
    (records : List (List Bool)) :
    boundedRecordFoldOutput sourceFlatAtomicRecordStep
      (unaryBoundedFoldWord records.length
        (sourceFlatAtomicDescriptorStream records)) =
      records.flatten := by
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word]
  simpa only [List.append_nil, List.nil_append]
      using sourceFlatAtomicRecordStep_iterate_descriptors records []

end SourceWholeOutputValidBranchRecordTM

namespace SourceCanonicalUnaryGridIndexTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceWholeOutputValidBranchRecordTM

/-- GapCVP reduction support. -/
def sourceCanonicalUnaryGridIndexDescriptor
    (index : ℕ) : List Bool :=
  lengthPrefixedWord (List.replicate index true)

/-- GapCVP reduction support. -/
def sourceCanonicalUnaryGridIndexDescriptors
    (count : ℕ) : List Bool :=
  (List.range count).flatMap sourceCanonicalUnaryGridIndexDescriptor

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceCanonicalUnaryGridIndexDescriptors_succ
    (count : ℕ) :
    sourceCanonicalUnaryGridIndexDescriptors (count + 1) =
      sourceCanonicalUnaryGridIndexDescriptors count ++
        sourceCanonicalUnaryGridIndexDescriptor count := by
  simp only [sourceCanonicalUnaryGridIndexDescriptors, List.range_succ, List.flatMap_append,
      List.flatMap_cons,
      List.flatMap_nil, List.append_nil]

/-- GapCVP reduction support. -/
def sourceCanonicalUnaryGridIndexOutput
    (input : List Bool) : List Bool :=
  match readUnaryPrefix input with
  | none => []
  | some (count, source) =>
      sourceCanonicalUnaryGridIndexDescriptors count ++ source

@[simp] theorem sourceCanonicalUnaryGridIndexOutput_valid
    (count : ℕ) (source : List Bool) :
    sourceCanonicalUnaryGridIndexOutput
        (List.replicate count true ++ false :: source) =
      sourceCanonicalUnaryGridIndexDescriptors count ++ source := by
  simp only [sourceCanonicalUnaryGridIndexOutput, readUnaryPrefix_replicate]

private def sourceGridIndexPeek (stack : Fin 5)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  .peek stack (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome) present absent)

private def sourceGridIndexPop (stack : Fin 5)
    (next : Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  .pop stack (fun state _ => state) next

private def sourceGridIndexPushBit (stack : Fin 5)
    (next : Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  .push stack (fun state => state.getD false) next

private def sourceGridIndexPushConstant (stack : Fin 5) (bit : Bool)
    (next : Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  .push stack (fun _ => bit) next

private def sourceGridIndexGoto (phase : Fin 7) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => phase))

/-- Internal support shared across GapCVP continuation modules. -/
def sourceGridIndexPrefixStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  sourceGridIndexPeek 0
    (.branch (fun state => state.getD false)
      (sourceGridIndexPop 0
        (sourceGridIndexPushConstant 1 true
          (sourceGridIndexGoto 0)))
      (sourceGridIndexPop 0 (sourceGridIndexGoto 1)))
    (sourceGridIndexGoto 6)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceGridIndexArchiveStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  sourceGridIndexPeek 0
    (sourceGridIndexPop 0
      (sourceGridIndexPushBit 3 (sourceGridIndexGoto 1)))
    (sourceGridIndexGoto 2)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceGridIndexSourceRestoreStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  sourceGridIndexPeek 3
    (sourceGridIndexPop 3
      (sourceGridIndexPushBit 4 (sourceGridIndexGoto 2)))
    (sourceGridIndexGoto 3)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceGridIndexOuterStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  sourceGridIndexPeek 1
    (sourceGridIndexPop 1 (sourceGridIndexGoto 4))
    .halt

/-- Internal support shared across GapCVP continuation modules. -/
def sourceGridIndexCopyStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  sourceGridIndexPeek 1
    (sourceGridIndexPop 1
      (sourceGridIndexPushConstant 2 true
        (sourceGridIndexPushConstant 4 true
          (sourceGridIndexGoto 4))))
    (sourceGridIndexPushConstant 4 false
      (sourceGridIndexGoto 5))

/-- Internal support shared across GapCVP continuation modules. -/
def sourceGridIndexTemplateRestoreStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  sourceGridIndexPeek 2
    (sourceGridIndexPop 2
      (sourceGridIndexPushConstant 1 true
        (sourceGridIndexPushConstant 4 true
          (sourceGridIndexGoto 5))))
    (sourceGridIndexGoto 3)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceGridIndexFailureStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  sourceGridIndexPeek 1
    (sourceGridIndexPop 1 (sourceGridIndexGoto 6))
    .halt

/-- Internal support shared across GapCVP continuation modules. -/
abbrev sourceCanonicalUnaryGridIndexMachine : Turing.FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Fin 7
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 7) then sourceGridIndexPrefixStatement
    else if phase = (1 : Fin 7) then sourceGridIndexArchiveStatement
    else if phase = (2 : Fin 7) then
      sourceGridIndexSourceRestoreStatement
    else if phase = (3 : Fin 7) then sourceGridIndexOuterStatement
    else if phase = (4 : Fin 7) then sourceGridIndexCopyStatement
    else if phase = (5 : Fin 7) then
      sourceGridIndexTemplateRestoreStatement
    else sourceGridIndexFailureStatement

/-- Internal support shared across GapCVP continuation modules. -/
def sourceGridIndexConfiguration (phase : Fin 7)
    (input counter scratch archive output : List Bool) :
    sourceCanonicalUnaryGridIndexMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, counter, scratch, archive, output]

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceCanonicalUnaryGridIndexMachine_init
    (input : List Bool) :
    Turing.initList sourceCanonicalUnaryGridIndexMachine input =
      sourceGridIndexConfiguration 0 input [] [] [] [] := by
  simp only [sourceCanonicalUnaryGridIndexMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq,
      dite_eq_ite,
      sourceGridIndexConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `sourceGridIndexStepTac` machine-step simplifier. -/
macro "sourceGridIndexStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [sourceCanonicalUnaryGridIndexMachine,
          sourceGridIndexConfiguration,
          sourceGridIndexPeek, sourceGridIndexPop,
          sourceGridIndexPushBit, sourceGridIndexPushConstant,
          sourceGridIndexGoto,
          sourceGridIndexPrefixStatement,
          sourceGridIndexArchiveStatement,
          sourceGridIndexSourceRestoreStatement,
          sourceGridIndexOuterStatement,
          sourceGridIndexCopyStatement,
          sourceGridIndexTemplateRestoreStatement,
          sourceGridIndexFailureStatement,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceGridIndex_prefix_true
    (input counter scratch archive output : List Bool) :
    sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 0
        (true :: input) counter scratch archive output) =
      some (sourceGridIndexConfiguration 0
        input (true :: counter) scratch archive output) := by
  sourceGridIndexStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceGridIndex_prefix_false
    (input counter scratch archive output : List Bool) :
    sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 0
        (false :: input) counter scratch archive output) =
      some (sourceGridIndexConfiguration 1
        input counter scratch archive output) := by
  sourceGridIndexStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceGridIndex_prefix_missing
    (counter scratch archive output : List Bool) :
    sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 0
        [] counter scratch archive output) =
      some (sourceGridIndexConfiguration 6
        [] counter scratch archive output) := by
  sourceGridIndexStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceGridIndex_archive_step
    (bit : Bool) (input counter scratch archive output : List Bool) :
    sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 1
        (bit :: input) counter scratch archive output) =
      some (sourceGridIndexConfiguration 1
        input counter scratch (bit :: archive) output) := by
  cases bit <;> sourceGridIndexStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceGridIndex_archive_finish
    (counter scratch archive output : List Bool) :
    sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 1
        [] counter scratch archive output) =
      some (sourceGridIndexConfiguration 2
        [] counter scratch archive output) := by
  sourceGridIndexStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceGridIndex_source_restore_step
    (bit : Bool) (counter scratch archive output : List Bool) :
    sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 2
        [] counter scratch (bit :: archive) output) =
      some (sourceGridIndexConfiguration 2
        [] counter scratch archive (bit :: output)) := by
  cases bit <;> sourceGridIndexStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceGridIndex_source_restore_finish
    (counter scratch output : List Bool) :
    sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 2
        [] counter scratch [] output) =
      some (sourceGridIndexConfiguration 3
        [] counter scratch [] output) := by
  sourceGridIndexStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceGridIndex_outer_step
    (counter output : List Bool) :
    sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 3
        [] (true :: counter) [] [] output) =
      some (sourceGridIndexConfiguration 4
        [] counter [] [] output) := by
  sourceGridIndexStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceGridIndex_outer_finish (output : List Bool) :
    sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 3 [] [] [] [] output) =
      some (Turing.haltList
        sourceCanonicalUnaryGridIndexMachine output) := by
  sourceGridIndexStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceGridIndex_copy_step
    (counter scratch output : List Bool) :
    sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 4
        [] (true :: counter) scratch [] output) =
      some (sourceGridIndexConfiguration 4
        [] counter (true :: scratch) [] (true :: output)) := by
  sourceGridIndexStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceGridIndex_copy_finish
    (scratch output : List Bool) :
    sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 4
        [] [] scratch [] output) =
      some (sourceGridIndexConfiguration 5
        [] [] scratch [] (false :: output)) := by
  sourceGridIndexStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceGridIndex_template_restore_step
    (counter scratch output : List Bool) :
    sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 5
        [] counter (true :: scratch) [] output) =
      some (sourceGridIndexConfiguration 5
        [] (true :: counter) scratch [] (true :: output)) := by
  sourceGridIndexStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceGridIndex_template_restore_finish
    (counter output : List Bool) :
    sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 5
        [] counter [] [] output) =
      some (sourceGridIndexConfiguration 3
        [] counter [] [] output) := by
  sourceGridIndexStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceGridIndex_failure_step
    (counter : List Bool) :
    sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 6
        [] (true :: counter) [] [] []) =
      some (sourceGridIndexConfiguration 6
        [] counter [] [] []) := by
  sourceGridIndexStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceGridIndex_failure_finish :
    sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 6 [] [] [] [] []) =
      some (Turing.haltList
        sourceCanonicalUnaryGridIndexMachine []) := by
  sourceGridIndexStepTac

end SourceCanonicalUnaryGridIndexTM

end GapCVP

end
