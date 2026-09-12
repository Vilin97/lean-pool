/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part05E

/-! # GapCVP proof, part 05, continuation 06 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFCappedUnaryMinimumTM

open Turing GapCVP.BinaryEncoding GapCVP.CNFUnaryPairIndexTM

end CNFCappedUnaryMinimumTM

namespace CNFCappedUnaryMinimumTotalCert

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.CNFUnaryPairIndexTM GapCVP.CNFCappedUnaryMinimumTM

private def cappedUnaryMinimum_successTrace
    (input first output : List Bool) :
    EvalsToInTime actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 2 input first output)
      (some (Turing.haltList actualCappedUnaryMinimumMachine
        output))
      (input.length + first.length + 1) := by
  have hinput := TraceGolf.sweep actualCappedUnaryMinimumMachine.step
    (fun current => cappedUnaryMinimumConfiguration 2 current first output)
    (fun bit remaining => cappedUnaryMinimum_success_input bit remaining first output)
    input
  have hfirst := TraceGolf.sweepThen actualCappedUnaryMinimumMachine.step
    (fun current => cappedUnaryMinimumConfiguration 2 [] current output)
    (fun bit remaining => cappedUnaryMinimum_success_first bit remaining output)
    first (cappedUnaryMinimum_success_finish output)
  exact rebound
    (EvalsToInTime.trans actualCappedUnaryMinimumMachine.step _ _ _ _ _ hinput hfirst)
    (by omega)

private def cappedUnaryMinimum_failureTrace
    (input first output : List Bool) :
    EvalsToInTime actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 3 input first output)
      (some (Turing.haltList actualCappedUnaryMinimumMachine []))
      (input.length + first.length + output.length + 1) := by
  have hinput := TraceGolf.sweep actualCappedUnaryMinimumMachine.step
    (fun current => cappedUnaryMinimumConfiguration 3 current first output)
    (fun bit remaining => cappedUnaryMinimum_failure_input bit remaining first output)
    input
  have hfirst := TraceGolf.sweep actualCappedUnaryMinimumMachine.step
    (fun current => cappedUnaryMinimumConfiguration 3 [] current output)
    (fun bit remaining => cappedUnaryMinimum_failure_first bit remaining output)
    first
  have houtput := TraceGolf.sweepThen actualCappedUnaryMinimumMachine.step
    (fun current => cappedUnaryMinimumConfiguration 3 [] [] current)
    cappedUnaryMinimum_failure_output output cappedUnaryMinimum_failure_finish
  have h01 := EvalsToInTime.trans actualCappedUnaryMinimumMachine.step _ _ _ _ _ hinput hfirst
  have hfull := EvalsToInTime.trans actualCappedUnaryMinimumMachine.step _ _ _ _ _ h01 houtput
  exact rebound hfull (by omega)

private def cappedUnaryMinimum_firstTrace
    (count : ℕ) (tail first output : List Bool) :
    EvalsToInTime actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 0
        (List.replicate count true ++ false :: tail)
        first output)
      (some (cappedUnaryMinimumConfiguration 1 tail
        (List.replicate count true ++ first) output))
      (count + 1) := by
  induction count generalizing first with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (cappedUnaryMinimum_first_false tail first output)
  | succ count ih =>
      have hfirst := oneStep _ _ (cappedUnaryMinimum_first_true
          (List.replicate count true ++ false :: tail)
          first output)
      have hrest := ih (true :: first)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualCappedUnaryMinimumMachine.step _ _ _ _ _ hfirst hrest

private def cappedUnaryMinimum_missingFirstTrace
    (count : ℕ) (first output : List Bool) :
    EvalsToInTime actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 0
        (List.replicate count true) first output)
      (some (cappedUnaryMinimumConfiguration 3 []
        (List.replicate count true ++ first) output))
      (count + 1) := by
  induction count generalizing first with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (cappedUnaryMinimum_first_missing first output)
  | succ count ih =>
      have hfirst := oneStep _ _ (cappedUnaryMinimum_first_true
          (List.replicate count true) first output)
      have hrest := ih (true :: first)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualCappedUnaryMinimumMachine.step _ _ _ _ _ hfirst hrest

private def cappedUnaryMinimum_secondTrace
    (first second : ℕ) (suffix output : List Bool) :
    EvalsToInTime actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 1
        (List.replicate second true ++ false :: suffix)
        (List.replicate first true) output)
      (some (cappedUnaryMinimumConfiguration 2 suffix
        (List.replicate (first - second) true)
        (List.replicate (min first second) true ++ output)))
      (second + 1) := by
  induction second generalizing first output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, tsub_zero,
          zero_le,
          inf_of_le_right, zero_add] using
          oneStep _ _ (cappedUnaryMinimum_second_false suffix (List.replicate first true) output)
  | succ second ih =>
      cases first with
      | zero =>
          have hfirst := oneStep _ _ (cappedUnaryMinimum_second_true_empty
              (List.replicate second true ++ false :: suffix)
              output)
          have hrest := ih 0 output
          simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append,
              List.replicate_zero, zero_tsub,
              le_add_iff_nonneg_left, zero_le, inf_of_le_left, List.nil_append, Nat.add_assoc,
                  Nat.reduceAdd] using
              EvalsToInTime.trans actualCappedUnaryMinimumMachine.step _ _ _ _ _ hfirst hrest
      | succ first =>
          have hfirst := oneStep _ _ (cappedUnaryMinimum_second_true_counter
              (List.replicate second true ++ false :: suffix)
              (List.replicate first true) output)
          have hrest := ih first (true :: output)
          simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append,
              Nat.succ_sub_succ,
              Nat.succ_min_succ, Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd,
              SourceStructuralDecoder.replicate_true_append_cons] using
              EvalsToInTime.trans actualCappedUnaryMinimumMachine.step _ _ _ _ _ hfirst hrest

private def cappedUnaryMinimum_missingSecondTrace
    (first second : ℕ) (output : List Bool) :
    EvalsToInTime actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 1
        (List.replicate second true)
        (List.replicate first true) output)
      (some (cappedUnaryMinimumConfiguration 3 []
        (List.replicate (first - second) true)
        (List.replicate (min first second) true ++ output)))
      (second + 1) := by
  induction second generalizing first output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, tsub_zero, zero_le,
          inf_of_le_right,
          List.nil_append, zero_add] using oneStep _ _ (cappedUnaryMinimum_second_missing
              (List.replicate first true) output)
  | succ second ih =>
      cases first with
      | zero =>
          have hfirst := oneStep _ _ (cappedUnaryMinimum_second_true_empty
              (List.replicate second true) output)
          have hrest := ih 0 output
          simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.replicate_zero,
              zero_tsub,
              le_add_iff_nonneg_left, zero_le, inf_of_le_left, List.nil_append, Nat.add_assoc,
                  Nat.reduceAdd] using
              EvalsToInTime.trans actualCappedUnaryMinimumMachine.step _ _ _ _ _ hfirst hrest
      | succ first =>
          have hfirst := oneStep _ _ (cappedUnaryMinimum_second_true_counter
              (List.replicate second true)
              (List.replicate first true) output)
          have hrest := ih first (true :: output)
          simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, Nat.succ_sub_succ,
              Nat.succ_min_succ,
              Nat.succ_eq_add_one, List.cons_append, Nat.add_assoc, Nat.reduceAdd,
              SourceStructuralDecoder.replicate_true_append_cons] using
              EvalsToInTime.trans actualCappedUnaryMinimumMachine.step _ _ _ _ _ hfirst hrest

private def cappedUnaryMinimum_validTrace
    (first second : ℕ) (suffix : List Bool) :
    EvalsToInTime actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 0
        (unarySourcePairWord first second ++ suffix) [] [])
      (some (Turing.haltList actualCappedUnaryMinimumMachine
        (List.replicate (min first second) true)))
      (first + second + suffix.length +
        (first - second) + 3) := by
  have hfirst := cappedUnaryMinimum_firstTrace first
    (List.replicate second true ++ false :: suffix) [] []
  simp only [List.append_nil] at hfirst
  have hsecond := cappedUnaryMinimum_secondTrace
    first second suffix []
  simp only [List.append_nil] at hsecond
  have hscan := EvalsToInTime.trans actualCappedUnaryMinimumMachine.step
    _ _ _ _ _ hfirst hsecond
  have hclean := cappedUnaryMinimum_successTrace
    suffix (List.replicate (first - second) true)
    (List.replicate (min first second) true)
  have hfull := EvalsToInTime.trans actualCappedUnaryMinimumMachine.step
    _ _ _ _ _ hscan hclean
  have hbudget := rebound (newBudget := first + second + suffix.length +
      (first - second) + 3) hfull (by
        simp only [List.length_replicate]
        omega)
  simpa only [FinTM2.step, Fin.isValue, unarySourcePairWord, List.append_assoc, List.cons_append,
      List.nil_append] using hbudget

private def cappedUnaryMinimumTimePolynomial : Polynomial ℕ :=
  8 * Polynomial.X + 16

private def cappedUnaryMinimum_totalTrace (input : List Bool) :
    EvalsToInTime actualCappedUnaryMinimumMachine.step
      (cappedUnaryMinimumConfiguration 0 input [] [])
      (some (Turing.haltList actualCappedUnaryMinimumMachine
        (cappedUnaryMinimumOutput input)))
      (cappedUnaryMinimumTimePolynomial.eval input.length) := by
  cases unaryInputSplit input with
  | inl witness =>
      obtain ⟨first, hinput⟩ := witness
      subst input
      have hfirst := cappedUnaryMinimum_missingFirstTrace
        first [] []
      simp only [List.append_nil] at hfirst
      have hclean := cappedUnaryMinimum_failureTrace
        [] (List.replicate first true) []
      have hfull := EvalsToInTime.trans actualCappedUnaryMinimumMachine.step
        _ _ _ _ _ hfirst hclean
      have hbounded := rebound (newBudget := cappedUnaryMinimumTimePolynomial.eval
          (List.replicate first true).length) hfull (by
            simp only [List.length_nil, List.length_replicate, zero_add, add_zero,
                cappedUnaryMinimumTimePolynomial,
                Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
                    at *
            omega)
      simpa only [FinTM2.step, Fin.isValue, cappedUnaryMinimumOutput, readUnaryPrefix_missing,
          List.length_replicate] using hbounded
  | inr witness =>
      obtain ⟨first, tail, hinput⟩ := witness
      subst input
      cases unaryInputSplit tail with
      | inl missing =>
          obtain ⟨second, htail⟩ := missing
          subst tail
          have hfirst := cappedUnaryMinimum_firstTrace
            first (List.replicate second true) [] []
          simp only [List.append_nil] at hfirst
          have hsecond := cappedUnaryMinimum_missingSecondTrace
            first second []
          simp only [List.append_nil] at hsecond
          have hscan := EvalsToInTime.trans actualCappedUnaryMinimumMachine.step
            _ _ _ _ _ hfirst hsecond
          have hclean := cappedUnaryMinimum_failureTrace
            [] (List.replicate (first - second) true)
            (List.replicate (min first second) true)
          have hfull := EvalsToInTime.trans actualCappedUnaryMinimumMachine.step
            _ _ _ _ _ hscan hclean
          have hbounded := rebound (newBudget := cappedUnaryMinimumTimePolynomial.eval
              (List.replicate first true ++
                false :: List.replicate second true).length)
            hfull (by
              simp only [List.length_nil, List.length_replicate, zero_add, Nat.sub_add_min_cancel,
                  List.length_append,
                  List.length_cons, cappedUnaryMinimumTimePolynomial, Polynomial.eval_add,
                      Polynomial.eval_mul, Polynomial.eval_ofNat,
                  Polynomial.eval_X] at *
              have hmin : min first second ≤ first :=
                Nat.min_le_left first second
              omega)
          simpa only [FinTM2.step, Fin.isValue, cappedUnaryMinimumOutput,
              readUnaryPrefix_replicate,
              readUnaryPrefix_missing, List.length_append, List.length_replicate, List.length_cons]
                  using hbounded
      | inr present =>
          obtain ⟨second, suffix, htail⟩ := present
          subst tail
          have hvalid := cappedUnaryMinimum_validTrace
            first second suffix
          have hbounded := rebound (newBudget := cappedUnaryMinimumTimePolynomial.eval
              (List.replicate first true ++ false ::
                (List.replicate second true ++ false :: suffix)).length)
            hvalid (by
              simp only [List.length_append, List.length_replicate, List.length_cons,
                  cappedUnaryMinimumTimePolynomial,
                  Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
                      Polynomial.eval_X, Nat.reduceLeDiff] at *
              omega)
          simpa only [FinTM2.step, Fin.isValue, cappedUnaryMinimumOutput,
              readUnaryPrefix_replicate, List.length_append,
              List.length_replicate, List.length_cons, unarySourcePairWord, List.append_assoc,
                  List.cons_append,
              List.nil_append] using hbounded

/-- GapCVP reduction support. -/
noncomputable def actualCappedUnaryMinimumComputable :
    BitTM
      cappedUnaryMinimumOutput where
  tm := actualCappedUnaryMinimumMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := cappedUnaryMinimumTimePolynomial
  outputsFun input := {
    steps := (cappedUnaryMinimum_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun,
              actualCappedUnaryMinimumMachine_init, Option.map_some] using
          (cappedUnaryMinimum_totalTrace input).evals_in_steps
    steps_le_m := by
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq] using
          (cappedUnaryMinimum_totalTrace input).steps_le_m
  }

end CNFCappedUnaryMinimumTotalCert

namespace CNFCappedUnaryPairArithmeticTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.SourceMachineCert GapCVP.SourceOriginalSourcePreservingTM GapCVP.CNFUnaryPairIndexTM
open GapCVP.CNFUnaryPairIndexTotalRuntimeCert GapCVP.CNFSourcePairPrefixWorkerTM
open GapCVP.CNFSourcePairPrefixWorkerTotalCert GapCVP.CNFCappedUnaryMinimumTM
open GapCVP.CNFCappedUnaryMinimumTotalCert

/-- GapCVP reduction support. -/
def unaryPrefixSuffixOutput (input : List Bool) : List Bool :=
  match readUnaryPrefix input with
  | none => []
  | some (_, suffix) => suffix

@[simp] theorem unaryPrefixSuffixOutput_valid
    (count : ℕ) (suffix : List Bool) :
    unaryPrefixSuffixOutput
      (List.replicate count true ++ false :: suffix) = suffix := by
  simp only [unaryPrefixSuffixOutput, readUnaryPrefix_replicate]

private abbrev actualUnaryPrefixSuffixMachine : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m _ :=
    .peek () (fun _ inspected => inspected)
      (.branch (fun inspected => inspected.isSome)
        (.branch (fun inspected => inspected.getD false)
          (.pop () (fun _ _ => none)
            (.goto (fun _ => ())))
          (.pop () (fun _ _ => none) .halt))
        .halt)

private def unaryPrefixSuffixConfiguration (input : List Bool) :
    actualUnaryPrefixSuffixMachine.Cfg where
  l := some ()
  var := none
  stk := fun _ => input

private theorem actualUnaryPrefixSuffixMachine_init
    (input : List Bool) :
    Turing.initList actualUnaryPrefixSuffixMachine input =
      unaryPrefixSuffixConfiguration input := by
  simp only [actualUnaryPrefixSuffixMachine, initList, ↓reduceDIte, eq_mpr_eq_cast, cast_eq,
      unaryPrefixSuffixConfiguration]
  rfl

private theorem unaryPrefixSuffix_true_step (input : List Bool) :
    actualUnaryPrefixSuffixMachine.step
      (unaryPrefixSuffixConfiguration (true :: input)) =
      some (unaryPrefixSuffixConfiguration input) := by
  compactMachineStepTac [actualUnaryPrefixSuffixMachine, unaryPrefixSuffixConfiguration]

private theorem unaryPrefixSuffix_false_step (input : List Bool) :
    actualUnaryPrefixSuffixMachine.step
      (unaryPrefixSuffixConfiguration (false :: input)) =
      some (Turing.haltList actualUnaryPrefixSuffixMachine input) := by
  compactMachineStepTac [actualUnaryPrefixSuffixMachine, unaryPrefixSuffixConfiguration]

private theorem unaryPrefixSuffix_missing_step :
    actualUnaryPrefixSuffixMachine.step
      (unaryPrefixSuffixConfiguration []) =
      some (Turing.haltList actualUnaryPrefixSuffixMachine []) := by
  compactMachineStepTac [actualUnaryPrefixSuffixMachine, unaryPrefixSuffixConfiguration]

private def unaryPrefixSuffix_validTrace
    (count : ℕ) (suffix : List Bool) :
    EvalsToInTime actualUnaryPrefixSuffixMachine.step
      (unaryPrefixSuffixConfiguration
        (List.replicate count true ++ false :: suffix))
      (some (Turing.haltList actualUnaryPrefixSuffixMachine suffix))
      (count + 1) := by
  induction count with
  | zero =>
      simpa only [FinTM2.step, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (unaryPrefixSuffix_false_step suffix)
  | succ count ih =>
      have hfirst := oneStep _ _ (unaryPrefixSuffix_true_step
          (List.replicate count true ++ false :: suffix))
      simpa only [FinTM2.step, List.replicate_succ, List.cons_append, Nat.add_assoc, Nat.reduceAdd]
          using
          EvalsToInTime.trans actualUnaryPrefixSuffixMachine.step _ _ _ _ _ hfirst ih

private def unaryPrefixSuffix_missingTrace
    (count : ℕ) :
    EvalsToInTime actualUnaryPrefixSuffixMachine.step
      (unaryPrefixSuffixConfiguration
        (List.replicate count true))
      (some (Turing.haltList actualUnaryPrefixSuffixMachine []))
      (count + 1) := by
  induction count with
  | zero =>
      simpa only [FinTM2.step, List.replicate_zero, zero_add] using oneStep _ _
          unaryPrefixSuffix_missing_step
  | succ count ih =>
      have hfirst := oneStep _ _ (unaryPrefixSuffix_true_step
          (List.replicate count true))
      simpa only [FinTM2.step, List.replicate_succ, Nat.add_assoc, Nat.reduceAdd] using
          EvalsToInTime.trans actualUnaryPrefixSuffixMachine.step _ _ _ _ _ hfirst ih

private def unaryPrefixSuffix_totalTrace (input : List Bool) :
    EvalsToInTime actualUnaryPrefixSuffixMachine.step
      (unaryPrefixSuffixConfiguration input)
      (some (Turing.haltList actualUnaryPrefixSuffixMachine
        (unaryPrefixSuffixOutput input)))
      ((Polynomial.X + 1 : Polynomial ℕ).eval input.length) := by
  cases unaryInputSplit input with
  | inl witness =>
      obtain ⟨count, hinput⟩ := witness
      subst input
      have htrace := unaryPrefixSuffix_missingTrace count
      simpa only [FinTM2.step, unaryPrefixSuffixOutput, readUnaryPrefix_missing,
          List.length_replicate,
          Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using htrace
  | inr witness =>
      obtain ⟨count, suffix, hinput⟩ := witness
      subst input
      have htrace := unaryPrefixSuffix_validTrace count suffix
      refine {
        steps := htrace.steps
        evals_in_steps := ?_
        steps_le_m := ?_
      }
      · simpa only [Option.bind_eq_bind, FinTM2.step, unaryPrefixSuffixOutput,
          readUnaryPrefix_replicate] using
            htrace.evals_in_steps
      · have hsteps := htrace.steps_le_m
        simp only [FinTM2.step, List.length_append, List.length_replicate, List.length_cons,
            Polynomial.eval_add,
            Polynomial.eval_X, Polynomial.eval_one, ge_iff_le]
        omega

/-- GapCVP reduction support. -/
noncomputable def actualUnaryPrefixSuffixComputable :
    BitTM
      unaryPrefixSuffixOutput where
  tm := actualUnaryPrefixSuffixMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun input := {
    steps := (unaryPrefixSuffix_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Equiv.invFun_as_coe, Equiv.refl_symm,
          Equiv.coe_refl,
          bitEncoding, id_eq, List.map_id_fun, actualUnaryPrefixSuffixMachine_init,
              Option.map_some] using
          (unaryPrefixSuffix_totalTrace input).evals_in_steps
    steps_le_m := by
      simpa only [FinTM2.step, bitEncoding, id_eq, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_one] using (unaryPrefixSuffix_totalTrace input).steps_le_m
  }

private def unaryCappedTailPairWord (input : List Bool) : List Bool :=
  unarySourcePairOutput
    (sourcePairPrefixOutput (unaryPrefixSuffixOutput input))

private noncomputable def actualUnaryCappedTailPairComputable :
    BitTM
      unaryCappedTailPairWord := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    actualUnaryPrefixSuffixComputable
    actualSourcePairPrefixComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hprefix actualUnaryPairIndexComputable
  change BitTM
    (fun input : List Bool =>
      unarySourcePairOutput
        (sourcePairPrefixOutput (unaryPrefixSuffixOutput input)))
  simpa only [Function.comp_def] using hphysical

private def unaryCappedSuccessorPairWord (input : List Bool) : List Bool :=
  true :: unaryCappedTailPairWord input

private noncomputable def actualUnaryCappedSuccessorPairComputable :
    BitTM
      unaryCappedSuccessorPairWord := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    actualUnaryCappedTailPairComputable
    (prependBitComputable true)
  change BitTM
    (fun input : List Bool => true :: unaryCappedTailPairWord input)
  simpa only [Function.comp_def] using hphysical

/-- GapCVP reduction support. -/
def cappedUnarySourcePairRecurrenceWord
    (input : List Bool) : List Bool :=
  cappedUnaryMinimumOutput
    (originalSourcePreservingOutput
      unaryCappedSuccessorPairWord input)

private noncomputable def actualCappedUnarySourcePairRecurrenceComputable :
    BitTM
      cappedUnarySourcePairRecurrenceWord := by
  have hpreserved := originalSourcePreservingComputable
    actualUnaryCappedSuccessorPairComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hpreserved actualCappedUnaryMinimumComputable
  change BitTM
    (fun input : List Bool =>
      cappedUnaryMinimumOutput
        (originalSourcePreservingOutput
          unaryCappedSuccessorPairWord input))
  simpa only [Function.comp_def] using hphysical

@[simp] theorem cappedUnarySourcePairRecurrenceWord_valid
    (cap head tail : ℕ) (suffix : List Bool) :
    cappedUnarySourcePairRecurrenceWord
      (List.replicate cap true ++ false ::
        (unarySourcePairWord head tail ++ suffix)) =
      List.replicate
        (min cap (Nat.succ (Nat.pair head tail))) true := by
  let source := List.replicate cap true ++ false ::
    (unarySourcePairWord head tail ++ suffix)
  have hpair :
      unaryCappedTailPairWord source =
        List.replicate (Nat.pair head tail) true := by
    simp only [unaryCappedTailPairWord, unaryPrefixSuffixOutput_valid, sourcePairPrefixOutput_pair,
        unarySourcePairOutput_word, source]
  change
    cappedUnaryMinimumOutput
      (unaryCappedSuccessorPairWord source ++ false :: source) = _
  simp only [unaryCappedSuccessorPairWord, hpair]
  rw [show true :: List.replicate (Nat.pair head tail) true =
    List.replicate (Nat.succ (Nat.pair head tail)) true by
      simp only [Nat.succ_eq_add_one, List.replicate_succ]]
  simp only [cappedUnaryMinimumOutput, Nat.succ_eq_add_one, readUnaryPrefix_replicate,
      Nat.min_comm, source]

end CNFCappedUnaryPairArithmeticTM

namespace CNFCappedFlatSourceListFoldTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert
open GapCVP.SourceUniformTuringTM GapCVP.CNFUnaryPairIndexTM GapCVP.CNFSourcePairPrefixWorkerTM
open GapCVP.CNFSourcePairPrefixWorkerTotalCert GapCVP.CNFCappedUnaryMinimumTM
open GapCVP.CNFCappedUnaryMinimumTotalCert GapCVP.CNFCappedUnaryPairArithmeticTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM

/-- GapCVP reduction support. -/
def flatUnaryDropFields (count : ℕ) (input : List Bool) : List Bool :=
  (unaryPrefixSuffixOutput^[count]) input

/-- GapCVP reduction support. -/
noncomputable def flatUnaryDropFieldsComputable :
    (count : ℕ) →
      BitTM
        (flatUnaryDropFields count)
  | 0 => by
      have hidentity := prependWordComputable []
      change BitTM
        (fun input : List Bool =>
          (unaryPrefixSuffixOutput^[0]) input)
      simpa only [Function.iterate_zero, id_eq, List.nil_append] using hidentity
  | count + 1 => by
      have hphysical := GapCVP.TMComposition.computableInPolyTime
        (flatUnaryDropFieldsComputable count)
        actualUnaryPrefixSuffixComputable
      change BitTM
        (fun input : List Bool =>
          (unaryPrefixSuffixOutput^[count + 1]) input)
      simpa only [Function.iterate_succ_apply', Function.comp_def, flatUnaryDropFields]
          using hphysical

/-- GapCVP reduction support. -/
def flatDuplicatedUnaryValueWord (input : List Bool) : List Bool :=
  cappedUnaryMinimumOutput input

/-- GapCVP reduction support. -/
noncomputable def flatDuplicatedUnaryValueComputable :
    BitTM
      flatDuplicatedUnaryValueWord :=
  actualCappedUnaryMinimumComputable

/-- GapCVP reduction support. -/
def flatDuplicatedUnaryFieldWord (input : List Bool) : List Bool :=
  flatDuplicatedUnaryValueWord input ++ [false]

private noncomputable def flatDuplicatedUnaryFieldComputable :
    BitTM
      flatDuplicatedUnaryFieldWord := by
  have hphysical := pointwiseAppendComputable
    flatDuplicatedUnaryValueComputable
    (constantWordComputable [false])
  exact hphysical

/-- GapCVP reduction support. -/
def flatDuplicatedUnaryFieldAt
    (offset : ℕ) (input : List Bool) : List Bool :=
  flatDuplicatedUnaryFieldWord (flatUnaryDropFields offset input)

private noncomputable def flatDuplicatedUnaryFieldAtComputable
    (offset : ℕ) :
    BitTM
      (flatDuplicatedUnaryFieldAt offset) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (flatUnaryDropFieldsComputable offset)
    flatDuplicatedUnaryFieldComputable
  change BitTM
    (fun input : List Bool =>
      flatDuplicatedUnaryFieldWord (flatUnaryDropFields offset input))
  simpa only [Function.comp_def] using hphysical

/-- GapCVP reduction support. -/
def flatCappedUnarySourceListQuery
    (input : List Bool) : List Bool :=
  flatDuplicatedUnaryFieldAt 0 input ++
    flatDuplicatedUnaryFieldAt 2 input ++
      flatDuplicatedUnaryFieldAt 4 input

private noncomputable def flatCappedUnarySourceListQueryComputable :
    BitTM
      flatCappedUnarySourceListQuery := by
  have htail := pointwiseAppendComputable
    (flatDuplicatedUnaryFieldAtComputable 2)
    (flatDuplicatedUnaryFieldAtComputable 4)
  have hphysical := pointwiseAppendComputable
    (flatDuplicatedUnaryFieldAtComputable 0) htail
  have heq :
      (fun input : List Bool =>
        flatDuplicatedUnaryFieldAt 0 input ++
          (flatDuplicatedUnaryFieldAt 2 input ++
            flatDuplicatedUnaryFieldAt 4 input)) =
        flatCappedUnarySourceListQuery := by
    funext input
    simp only [flatCappedUnarySourceListQuery, List.append_assoc]
  rw [← heq]
  exact hphysical

/-- GapCVP reduction support. -/
def flatCappedUnarySourceListNextField
    (input : List Bool) : List Bool :=
  cappedUnarySourcePairRecurrenceWord
      (flatCappedUnarySourceListQuery input) ++ [false]

private noncomputable def flatCappedUnarySourceListNextFieldComputable :
    BitTM
      flatCappedUnarySourceListNextField := by
  have hrecurrence := GapCVP.TMComposition.computableInPolyTime
    flatCappedUnarySourceListQueryComputable
    actualCappedUnarySourcePairRecurrenceComputable
  have hphysical := pointwiseAppendComputable hrecurrence
    (constantWordComputable [false])
  change BitTM
    (fun input : List Bool =>
      cappedUnarySourcePairRecurrenceWord
        (flatCappedUnarySourceListQuery input) ++ [false])
  simpa only [Function.comp_apply] using hphysical

/-- GapCVP reduction support. -/
def flatCappedUnaryPendingPair
    (input : List Bool) : List Bool :=
  sourcePairPrefixOutput (flatUnaryDropFields 6 input)

private noncomputable def flatCappedUnaryPendingPairComputable :
    BitTM
      flatCappedUnaryPendingPair := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (flatUnaryDropFieldsComputable 6)
    actualSourcePairPrefixComputable
  change BitTM
    (fun input : List Bool =>
      sourcePairPrefixOutput (flatUnaryDropFields 6 input))
  simpa only [Function.comp_def] using hphysical

/-- GapCVP reduction support. -/
def flatCappedUnaryPendingRemainder
    (input : List Bool) : List Bool :=
  flatUnaryDropFields 2 (flatUnaryDropFields 6 input)

private noncomputable def flatCappedUnaryPendingRemainderComputable :
    BitTM
      flatCappedUnaryPendingRemainder := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (flatUnaryDropFieldsComputable 6)
    (flatUnaryDropFieldsComputable 2)
  change BitTM
    (fun input : List Bool =>
      flatUnaryDropFields 2 (flatUnaryDropFields 6 input))
  simpa only [Function.comp_def] using hphysical

/-- GapCVP reduction support. -/
def flatCappedUnarySourceListStep
    (input : List Bool) : List Bool :=
  flatDuplicatedUnaryFieldAt 0 input ++
    flatDuplicatedUnaryFieldAt 0 input ++
      flatCappedUnaryPendingPair input ++
        flatCappedUnarySourceListNextField input ++
          flatCappedUnarySourceListNextField input ++
            flatCappedUnaryPendingRemainder input

/-- GapCVP reduction support. -/
noncomputable def flatCappedUnarySourceListStepComputable :
    BitTM
      flatCappedUnarySourceListStep := by
  have hlast := pointwiseAppendComputable
    flatCappedUnarySourceListNextFieldComputable
    flatCappedUnaryPendingRemainderComputable
  have hsecond := pointwiseAppendComputable
    flatCappedUnarySourceListNextFieldComputable hlast
  have hpending := pointwiseAppendComputable
    flatCappedUnaryPendingPairComputable hsecond
  have hcapSecond := pointwiseAppendComputable
    (flatDuplicatedUnaryFieldAtComputable 0) hpending
  have hphysical := pointwiseAppendComputable
    (flatDuplicatedUnaryFieldAtComputable 0) hcapSecond
  have heq :
      (fun input : List Bool =>
        flatDuplicatedUnaryFieldAt 0 input ++
          (flatDuplicatedUnaryFieldAt 0 input ++
            (flatCappedUnaryPendingPair input ++
              (flatCappedUnarySourceListNextField input ++
                (flatCappedUnarySourceListNextField input ++
                  flatCappedUnaryPendingRemainder input))))) =
        flatCappedUnarySourceListStep := by
    funext input
    simp only [flatCappedUnarySourceListStep, List.append_assoc]
  rw [← heq]
  exact hphysical

/-- GapCVP reduction support. -/
def flatDuplicatedUnaryField (value : ℕ) : List Bool :=
  unarySourcePairWord value value

/-- GapCVP reduction support. -/
def flatDuplicatedUnarySourceStream
    (records : List ℕ) : List Bool :=
  records.flatMap flatDuplicatedUnaryField

/-- GapCVP reduction support. -/
def flatCappedUnarySourceListState
    (cap accumulator : ℕ) : List ℕ → List Bool
  | [] =>
      flatDuplicatedUnaryField cap ++
        flatDuplicatedUnaryField accumulator
  | head :: remaining =>
      flatDuplicatedUnaryField cap ++
        flatDuplicatedUnaryField head ++
          flatDuplicatedUnaryField accumulator ++
            flatDuplicatedUnarySourceStream remaining

@[simp] theorem flatUnaryDropFields_two_unaryPair
    (first second : ℕ) (suffix : List Bool) :
    flatUnaryDropFields 2
      (unarySourcePairWord first second ++ suffix) = suffix := by
  simp [flatUnaryDropFields, Function.iterate_succ_apply',
    unarySourcePairWord, unaryPrefixSuffixOutput_valid,
    List.append_assoc]

theorem flatUnaryDropFields_four_unaryPairs
    (first second third fourth : ℕ) (suffix : List Bool) :
    flatUnaryDropFields 4
      (unarySourcePairWord first second ++
        unarySourcePairWord third fourth ++ suffix) = suffix := by
  simp [flatUnaryDropFields, Function.iterate_succ_apply',
    unarySourcePairWord, unaryPrefixSuffixOutput_valid,
    List.append_assoc]

theorem flatUnaryDropFields_six_unaryPairs
    (first second third fourth fifth sixth : ℕ)
    (suffix : List Bool) :
    flatUnaryDropFields 6
      (unarySourcePairWord first second ++
        unarySourcePairWord third fourth ++
          unarySourcePairWord fifth sixth ++ suffix) = suffix := by
  simp [flatUnaryDropFields, Function.iterate_succ_apply',
    unarySourcePairWord, unaryPrefixSuffixOutput_valid,
    List.append_assoc]

@[simp] private theorem flatDuplicatedUnaryFieldWord_pair
    (value : ℕ) (suffix : List Bool) :
    flatDuplicatedUnaryFieldWord
      (flatDuplicatedUnaryField value ++ suffix) =
      List.replicate value true ++ [false] := by
  simp only [flatDuplicatedUnaryFieldWord, flatDuplicatedUnaryValueWord, flatDuplicatedUnaryField,
      cappedUnaryMinimumOutput_pair, min_self]

@[simp] private theorem sourcePairPrefixOutput_flatDuplicatedUnaryStream_cons
    (head : ℕ) (remaining : List ℕ) :
    sourcePairPrefixOutput
      (flatDuplicatedUnarySourceStream (head :: remaining)) =
      flatDuplicatedUnaryField head := by
  simp only [flatDuplicatedUnarySourceStream, List.flatMap_cons, flatDuplicatedUnaryField,
      sourcePairPrefixOutput_pair]

@[simp] private theorem flatUnaryDropFields_flatDuplicatedUnaryStream_cons
    (head : ℕ) (remaining : List ℕ) :
    flatUnaryDropFields 2
      (flatDuplicatedUnarySourceStream (head :: remaining)) =
      flatDuplicatedUnarySourceStream remaining := by
  simp only [flatDuplicatedUnarySourceStream, List.flatMap_cons, flatDuplicatedUnaryField,
      flatUnaryDropFields_two_unaryPair]

@[simp] theorem flatCappedUnarySourceListStep_state
    (cap head accumulator : ℕ) (remaining : List ℕ) :
    flatCappedUnarySourceListStep
      (flatCappedUnarySourceListState
        cap accumulator (head :: remaining)) =
      flatCappedUnarySourceListState
        cap
        (min cap (Nat.succ (Nat.pair head accumulator)))
        remaining := by
  let source := flatCappedUnarySourceListState
    cap accumulator (head :: remaining)
  have hcap : flatDuplicatedUnaryFieldAt 0 source =
      List.replicate cap true ++ [false] := by
    dsimp [source, flatCappedUnarySourceListState,
      flatDuplicatedUnaryFieldAt, flatUnaryDropFields]
    simpa [flatDuplicatedUnaryField, List.append_assoc] using
      flatDuplicatedUnaryFieldWord_pair cap
        (flatDuplicatedUnaryField head ++
          flatDuplicatedUnaryField accumulator ++
          flatDuplicatedUnarySourceStream remaining)
  have hhead : flatDuplicatedUnaryFieldAt 2 source =
      List.replicate head true ++ [false] := by
    dsimp [source, flatCappedUnarySourceListState,
      flatDuplicatedUnaryFieldAt]
    simp only [flatDuplicatedUnaryField, List.append_assoc]
    rw [flatUnaryDropFields_two_unaryPair]
    simpa [flatDuplicatedUnaryField, List.append_assoc] using
      flatDuplicatedUnaryFieldWord_pair head
        (flatDuplicatedUnaryField accumulator ++
          flatDuplicatedUnarySourceStream remaining)
  have haccumulator : flatDuplicatedUnaryFieldAt 4 source =
      List.replicate accumulator true ++ [false] := by
    dsimp [source, flatCappedUnarySourceListState,
      flatDuplicatedUnaryFieldAt]
    simp only [flatDuplicatedUnaryField, List.append_assoc]
    have hdrop := flatUnaryDropFields_four_unaryPairs
      cap cap head head
      (unarySourcePairWord accumulator accumulator ++
        flatDuplicatedUnarySourceStream remaining)
    simp only [List.append_assoc] at hdrop
    rw [hdrop]
    simpa [flatDuplicatedUnaryField] using
      flatDuplicatedUnaryFieldWord_pair accumulator
        (flatDuplicatedUnarySourceStream remaining)
  have hpending : flatUnaryDropFields 6 source =
      flatDuplicatedUnarySourceStream remaining := by
    dsimp [source, flatCappedUnarySourceListState]
    exact flatUnaryDropFields_six_unaryPairs
      cap cap head head accumulator accumulator
      (flatDuplicatedUnarySourceStream remaining)
  have hquery : flatCappedUnarySourceListQuery source =
      List.replicate cap true ++ false ::
        unarySourcePairWord head accumulator := by
    unfold flatCappedUnarySourceListQuery
    rw [hcap, hhead, haccumulator]
    simp [unarySourcePairWord, List.append_assoc]
  have hnext : flatCappedUnarySourceListNextField source =
      List.replicate
        (min cap (Nat.succ (Nat.pair head accumulator))) true ++
          [false] := by
    unfold flatCappedUnarySourceListNextField
    rw [hquery]
    simpa using congrArg
      (fun output : List Bool => output ++ [false])
      (cappedUnarySourcePairRecurrenceWord_valid
        cap head accumulator [])
  change flatCappedUnarySourceListStep source = _
  unfold flatCappedUnarySourceListStep
    flatCappedUnaryPendingPair flatCappedUnaryPendingRemainder
  rw [hcap, hnext, hpending]
  cases remaining with
  | nil =>
      simp [flatCappedUnarySourceListState,
        flatDuplicatedUnarySourceStream,
        flatDuplicatedUnaryField,
        sourcePairPrefixOutput,
        readUnaryPrefix,
        flatUnaryDropFields,
        unarySourcePairWord,
        unaryPrefixSuffixOutput,
        List.append_assoc]
  | cons next tail =>
      rw [sourcePairPrefixOutput_flatDuplicatedUnaryStream_cons,
        flatUnaryDropFields_flatDuplicatedUnaryStream_cons]
      simp [flatCappedUnarySourceListState,
        flatDuplicatedUnaryField,
        unarySourcePairWord, List.append_assoc]

end CNFCappedFlatSourceListFoldTM


end GapCVP

end
