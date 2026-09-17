/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part06A

/-! # GapCVP proof, part 06, continuation 02 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace SourceUnaryIntegerMultiplicationTM

section

open Turing GapCVP.BinaryEncoding

end

section

open Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder

private def sourceIntegerMultiplication_leftTrace
    (count : ℕ) (remaining left right restore output : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 0
        (List.replicate count true ++ false :: remaining)
        left right restore output)
      (some (sourceIntegerMultiplicationConfiguration 1
        remaining (List.replicate count true ++ left)
        right restore output))
      (count + 1) := by
  induction count generalizing left with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceIntegerMultiplication_left_delimiter remaining left right restore
              output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceIntegerMultiplication_left_true
          (List.replicate count true ++ false :: remaining)
          left right restore output)
      have hrest := ih (true :: left)
      have hfull := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
        _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

private def sourceIntegerMultiplication_leftMissingTrace
    (count : ℕ) (left right restore output : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 0
        (List.replicate count true) left right restore output)
      (some (sourceIntegerMultiplicationConfiguration 6
        [] (List.replicate count true ++ left)
        right restore output))
      (count + 1) := by
  induction count generalizing left with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceIntegerMultiplication_left_missing left right restore output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceIntegerMultiplication_left_true
          (List.replicate count true)
          left right restore output)
      have hrest := ih (true :: left)
      have hfull := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
        _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

private def sourceIntegerMultiplication_rightTrace
    (count : ℕ) (left right restore output : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 1
        (List.replicate count true) left right restore output)
      (some (sourceIntegerMultiplicationConfiguration 2
        [] left (List.replicate count true ++ right)
        restore output))
      (count + 1) := by
  induction count generalizing right with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceIntegerMultiplication_right_finish left right restore output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceIntegerMultiplication_right_true
          (List.replicate count true)
          left right restore output)
      have hrest := ih (true :: right)
      have hfull := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
        _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

private def sourceIntegerMultiplication_rightInvalidTrace
    (count : ℕ) (remaining left right restore output : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 1
        (List.replicate count true ++ false :: remaining)
        left right restore output)
      (some (sourceIntegerMultiplicationConfiguration 6
        remaining left (List.replicate count true ++ right)
        restore output))
      (count + 1) := by
  induction count generalizing right with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceIntegerMultiplication_right_false remaining left right restore output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceIntegerMultiplication_right_true
          (List.replicate count true ++ false :: remaining)
          left right restore output)
      have hrest := ih (true :: right)
      have hfull := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
        _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

private def sourceIntegerMultiplication_copyTrace
    (count : ℕ) (left restore output : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 3
        [] left (List.replicate count true) restore output)
      (some (sourceIntegerMultiplicationConfiguration 4
        [] left [] (List.replicate count true ++ restore)
        (List.replicate count true ++ output)))
      (count + 1) := by
  induction count generalizing restore output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceIntegerMultiplication_copy_finish left restore output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceIntegerMultiplication_copy_step left
          (List.replicate count true) restore output)
      have hrest := ih (true :: restore) (true :: output)
      have hfull := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
        _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

private def sourceIntegerMultiplication_restoreTrace
    (count : ℕ) (left right output : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 4
        [] left right (List.replicate count true) output)
      (some (sourceIntegerMultiplicationConfiguration 2
        [] left (List.replicate count true ++ right) [] output))
      (count + 1) := by
  induction count generalizing right with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceIntegerMultiplication_restore_finish left right output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceIntegerMultiplication_restore_step
          left right (List.replicate count true) output)
      have hrest := ih (true :: right)
      have hfull := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
        _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

private def sourceIntegerMultiplication_baseCopyTrace
    (rightSize : ℕ) (left output : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 3
        [] left (List.replicate rightSize true) [] output)
      (some (sourceIntegerMultiplicationConfiguration 2
        [] left (List.replicate rightSize true) []
        (List.replicate rightSize true ++ output)))
      (2 * rightSize + 2) := by
  have hcopy := sourceIntegerMultiplication_copyTrace
    rightSize left [] output
  simp only [List.append_nil] at hcopy
  have hrestore := sourceIntegerMultiplication_restoreTrace
    rightSize left []
    (List.replicate rightSize true ++ output)
  simp only [List.append_nil] at hrestore
  have hfull := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
    _ _ _ _ _ hcopy hrestore
  exact rebound hfull (by omega)

private def sourceIntegerMultiplication_productTrace
    (leftSize rightSize : ℕ) (output : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 2
        [] (List.replicate leftSize true)
        (List.replicate rightSize true) [] output)
      (some (sourceIntegerMultiplicationConfiguration 5
        [] [] (List.replicate rightSize true) []
        (List.replicate (leftSize * rightSize) true ++ output)))
      (leftSize * (2 * rightSize + 3) + 1) := by
  induction leftSize generalizing output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, zero_mul, List.nil_append,
          zero_add] using
          oneStep _ _ (sourceIntegerMultiplication_outer_finish (List.replicate rightSize true) []
              output)
  | succ leftSize ih =>
      have houter := oneStep _ _ (sourceIntegerMultiplication_outer_step
          (List.replicate leftSize true)
          (List.replicate rightSize true) [] output)
      have hcopy := sourceIntegerMultiplication_baseCopyTrace
        rightSize (List.replicate leftSize true) output
      have hready := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
        _ _ _ _ _ houter hcopy
      have hrest := ih (List.replicate rightSize true ++ output)
      have hblocks :
          List.replicate (leftSize * rightSize) true ++
              (List.replicate rightSize true ++ output) =
            List.replicate ((leftSize + 1) * rightSize) true ++
              output := by
        rw [Nat.add_mul, Nat.one_mul,
          List.replicate_add, List.append_assoc]
      rw [hblocks] at hrest
      have hfull := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
        _ _ _ _ _ hready hrest
      have hnormalized :
          EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
            (sourceIntegerMultiplicationConfiguration 2
              [] (List.replicate (leftSize + 1) true)
              (List.replicate rightSize true) [] output)
            (some (sourceIntegerMultiplicationConfiguration 5
              [] [] (List.replicate rightSize true) []
              (List.replicate ((leftSize + 1) * rightSize) true ++
                output)))
            ((leftSize * (2 * rightSize + 3) + 1) +
              ((2 * rightSize + 2) + 1)) := by
        simpa only [List.replicate_succ, Nat.add_assoc]
          using hfull
      exact rebound hnormalized (by
        simp only [Nat.mul_add, Nat.add_mul, one_mul]
        omega)

private def sourceIntegerMultiplication_successTrace
    (count : ℕ) (output : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 5
        [] [] (List.replicate count true) [] output)
      (some (Turing.haltList
        sourceUnaryIntegerMultiplicationMachine output))
      (count + 1) := by
  induction count with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, zero_add] using
          oneStep _ _ (sourceIntegerMultiplication_success_finish output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceIntegerMultiplication_success_step
          (List.replicate count true) output)
      have hfull := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
        _ _ _ _ _ hfirst ih
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, Nat.add_assoc, Nat.reduceAdd]
          using hfull

private def sourceIntegerMultiplication_failureInputTrace
    (input left right restore output : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 6
        input left right restore output)
      (some (sourceIntegerMultiplicationConfiguration 7
        [] left right restore output))
      (input.length + 1) := by
  exact TraceGolf.sweepThen sourceUnaryIntegerMultiplicationMachine.step
    (fun current => sourceIntegerMultiplicationConfiguration 6
      current left right restore output)
    (fun bit remaining => sourceIntegerMultiplication_failure_input_step
      bit remaining left right restore output)
    input (sourceIntegerMultiplication_failure_input_finish left right restore output)

private def sourceIntegerMultiplication_failureLeftTrace
    (left right restore output : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 7
        [] left right restore output)
      (some (sourceIntegerMultiplicationConfiguration 8
        [] [] right restore output))
      (left.length + 1) := by
  exact TraceGolf.sweepThen sourceUnaryIntegerMultiplicationMachine.step
    (fun current => sourceIntegerMultiplicationConfiguration 7
      [] current right restore output)
    (fun bit remaining => sourceIntegerMultiplication_failure_left_step
      bit remaining right restore output)
    left (sourceIntegerMultiplication_failure_left_finish right restore output)

private def sourceIntegerMultiplication_failureRightTrace
    (right restore output : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 8
        [] [] right restore output)
      (some (sourceIntegerMultiplicationConfiguration 9
        [] [] [] restore output))
      (right.length + 1) := by
  exact TraceGolf.sweepThen sourceUnaryIntegerMultiplicationMachine.step
    (fun current => sourceIntegerMultiplicationConfiguration 8
      [] [] current restore output)
    (fun bit remaining => sourceIntegerMultiplication_failure_right_step
      bit remaining restore output)
    right (sourceIntegerMultiplication_failure_right_finish restore output)

private def sourceIntegerMultiplication_failureRestoreTrace
    (restore output : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 9
        [] [] [] restore output)
      (some (sourceIntegerMultiplicationConfiguration 10
        [] [] [] [] output))
      (restore.length + 1) := by
  exact TraceGolf.sweepThen sourceUnaryIntegerMultiplicationMachine.step
    (fun current => sourceIntegerMultiplicationConfiguration 9 [] [] [] current output)
    (fun bit remaining => sourceIntegerMultiplication_failure_restore_step
      bit remaining output)
    restore (sourceIntegerMultiplication_failure_restore_finish output)

private def sourceIntegerMultiplication_failureOutputTrace
    (output : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 10
        [] [] [] [] output)
      (some (Turing.haltList
        sourceUnaryIntegerMultiplicationMachine []))
      (output.length + 1) := by
  exact TraceGolf.sweepThen sourceUnaryIntegerMultiplicationMachine.step
    (fun current => sourceIntegerMultiplicationConfiguration 10 [] [] [] [] current)
    sourceIntegerMultiplication_failure_output_step output
    sourceIntegerMultiplication_failure_finish

private def sourceIntegerMultiplication_failureTrace
    (input left right restore output : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 6
        input left right restore output)
      (some (Turing.haltList
        sourceUnaryIntegerMultiplicationMachine []))
      (input.length + left.length + right.length +
        restore.length + output.length + 5) := by
  have hinput := sourceIntegerMultiplication_failureInputTrace
    input left right restore output
  have hleft := sourceIntegerMultiplication_failureLeftTrace
    left right restore output
  have hright := sourceIntegerMultiplication_failureRightTrace
    right restore output
  have hrestore := sourceIntegerMultiplication_failureRestoreTrace
    restore output
  have houtput := sourceIntegerMultiplication_failureOutputTrace
    output
  have hfirst := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
    _ _ _ _ _ hinput hleft
  have hsecond := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
    _ _ _ _ _ hfirst hright
  have hthird := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
    _ _ _ _ _ hsecond hrestore
  have hfull := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
    _ _ _ _ _ hthird houtput
  exact rebound hfull (by omega)

private def sourceIntegerMultiplicationValidBudget
    (left right : ℕ) : ℕ :=
  left * (2 * right + 3) + left + 2 * right + 4

private def sourceIntegerMultiplication_validTrace
    (left right : ℕ) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (sourceIntegerMultiplicationConfiguration 0
        (sourceUnaryIntegerMultiplicationQuery left right)
        [] [] [] [])
      (some (Turing.haltList
        sourceUnaryIntegerMultiplicationMachine
        (List.replicate (left * right) true)))
      (sourceIntegerMultiplicationValidBudget left right) := by
  have hleft := sourceIntegerMultiplication_leftTrace
    left (List.replicate right true) [] [] [] []
  simp only [List.append_nil] at hleft
  have hright := sourceIntegerMultiplication_rightTrace
    right (List.replicate left true) [] [] []
  simp only [List.append_nil] at hright
  have hproduct := sourceIntegerMultiplication_productTrace
    left right []
  simp only [List.append_nil] at hproduct
  have hcleanup := sourceIntegerMultiplication_successTrace
    right (List.replicate (left * right) true)
  have hfirst := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
    _ _ _ _ _ hleft hright
  have hsecond := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
    _ _ _ _ _ hfirst hproduct
  have hfull := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
    _ _ _ _ _ hsecond hcleanup
  change EvalsToInTime
    sourceUnaryIntegerMultiplicationMachine.step
    (sourceIntegerMultiplicationConfiguration 0
      (List.replicate left true ++
        false :: List.replicate right true)
      [] [] [] [])
    (some (Turing.haltList
      sourceUnaryIntegerMultiplicationMachine
      (List.replicate (left * right) true)))
    (sourceIntegerMultiplicationValidBudget left right)
  exact rebound hfull (by
    simp only [sourceIntegerMultiplicationValidBudget]
    omega)

private def sourceIntegerMultiplicationInputBudget
    (input : List Bool) : ℕ :=
  16 * (input.length + 1) ^ 2 + 32

private theorem sourceIntegerMultiplication_validBudget_le
    (left right : ℕ) :
    sourceIntegerMultiplicationValidBudget left right ≤
      sourceIntegerMultiplicationInputBudget
        (sourceUnaryIntegerMultiplicationQuery left right) := by
  simp only [sourceIntegerMultiplicationValidBudget, sourceIntegerMultiplicationInputBudget,
      sourceUnaryIntegerMultiplicationQuery, List.length_append, List.length_replicate,
          List.length_cons,
      add_le_add_iff_right]
  nlinarith [Nat.zero_le (left * left),
    Nat.zero_le (right * right)]

private noncomputable def sourceIntegerMultiplication_totalTrace
    (input : List Bool) :
    EvalsToInTime sourceUnaryIntegerMultiplicationMachine.step
      (Turing.initList sourceUnaryIntegerMultiplicationMachine input)
      (some (Turing.haltList sourceUnaryIntegerMultiplicationMachine
        (sourceUnaryIntegerMultiplicationOutput input)))
      (sourceIntegerMultiplicationInputBudget input) := by
  rw [sourceUnaryIntegerMultiplicationMachine_init]
  cases unaryInputSplit input with
  | inl witness =>
      obtain ⟨count, hinput⟩ := witness
      subst input
      have hscan := sourceIntegerMultiplication_leftMissingTrace
        count [] [] [] []
      simp only [List.append_nil] at hscan
      have hcleanup := sourceIntegerMultiplication_failureTrace
        [] (List.replicate count true) [] [] []
      have hfull := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
        _ _ _ _ _ hscan hcleanup
      have hbounded := rebound (newBudget := sourceIntegerMultiplicationInputBudget
          (List.replicate count true))
        hfull (by
          simp only [List.length_nil, List.length_replicate, zero_add, add_zero,
              sourceIntegerMultiplicationInputBudget]
          nlinarith [Nat.zero_le (count * count)])
      simpa only [FinTM2.step, Fin.isValue, sourceUnaryIntegerMultiplicationOutput,
          readUnaryPrefix_missing] using
          hbounded
  | inr witness =>
      obtain ⟨left, remaining, hinput⟩ := witness
      subst input
      cases unaryInputSplit remaining with
      | inl second =>
          obtain ⟨right, hremaining⟩ := second
          subst remaining
          have hvalid := sourceIntegerMultiplication_validTrace
            left right
          have hbounded := rebound hvalid
            (sourceIntegerMultiplication_validBudget_le left right)
          simpa only [FinTM2.step, Fin.isValue, sourceUnaryIntegerMultiplicationOutput,
              readUnaryPrefix_replicate,
              List.all_replicate, ite_self, ↓reduceIte, List.length_replicate,
                  sourceUnaryIntegerMultiplicationQuery] using
              hbounded
      | inr excess =>
          obtain ⟨right, suffix, hremaining⟩ := excess
          subst remaining
          have hleft := sourceIntegerMultiplication_leftTrace
            left
            (List.replicate right true ++ false :: suffix)
            [] [] [] []
          simp only [List.append_nil] at hleft
          have hright := sourceIntegerMultiplication_rightInvalidTrace
            right suffix (List.replicate left true) [] [] []
          simp only [List.append_nil] at hright
          have hcleanup := sourceIntegerMultiplication_failureTrace
            suffix (List.replicate left true)
            (List.replicate right true) [] []
          have hfirst := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
            _ _ _ _ _ hleft hright
          have hfull := EvalsToInTime.trans sourceUnaryIntegerMultiplicationMachine.step
            _ _ _ _ _ hfirst hcleanup
          have hbounded := rebound (newBudget := sourceIntegerMultiplicationInputBudget
              (List.replicate left true ++
                false :: (List.replicate right true ++
                  false :: suffix)))
            hfull (by
              simp only [List.length_replicate, List.length_nil, add_zero,
                  sourceIntegerMultiplicationInputBudget,
                  List.length_append, List.length_cons]
              nlinarith [Nat.zero_le (left * left),
                Nat.zero_le (right * right),
                Nat.zero_le (suffix.length * suffix.length)])
          simpa only [FinTM2.step, Fin.isValue, sourceUnaryIntegerMultiplicationOutput,
              readUnaryPrefix_replicate,
              List.all_append, List.all_replicate, ite_self, List.all_cons, Bool.false_and,
                  Bool.and_false, Bool.false_eq_true,
              ↓reduceIte] using hbounded

private noncomputable def sourceIntegerMultiplicationTimePolynomial :
    Polynomial ℕ :=
  16 * (Polynomial.X + 1) ^ 2 + 32

private theorem sourceIntegerMultiplicationTimePolynomial_eval
    (input : List Bool) :
    sourceIntegerMultiplicationTimePolynomial.eval
        (bitEncoding input).length =
      sourceIntegerMultiplicationInputBudget input := by
  simp only [bitEncoding, id_eq, sourceIntegerMultiplicationTimePolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one, sourceIntegerMultiplicationInputBudget]

/-- GapCVP reduction support. -/
noncomputable def sourceUnaryIntegerMultiplicationComputable :
    BitTM
      sourceUnaryIntegerMultiplicationOutput where
  tm := sourceUnaryIntegerMultiplicationMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := sourceIntegerMultiplicationTimePolynomial
  outputsFun input := {
    steps := (sourceIntegerMultiplication_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, Option.map_some] using
          (sourceIntegerMultiplication_totalTrace input).evals_in_steps
    steps_le_m := by
      rw [sourceIntegerMultiplicationTimePolynomial_eval]
      exact (sourceIntegerMultiplication_totalTrace input).steps_le_m
  }

end

end SourceUnaryIntegerMultiplicationTM

namespace SourceMixedRadixPreservedFourFamilyRecordTM

open Turing GapCVP.BinaryEncoding
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceWholeOutputValidBranchRecordTM
open GapCVP.SourceOriginalSourcePreservingTM GapCVP.CLStructuralPrefixWriter

private def sourcePhysicalAtomicDescriptorOutput
    (atom : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  sourceFlatAtomicDescriptor (atom input)

private noncomputable def sourcePhysicalAtomicDescriptorComputable
    {atom : List Bool → List Bool}
    (computer : BitTM atom) :
    BitTM (sourcePhysicalAtomicDescriptorOutput atom) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    computer structuralPrefixWriterComputable
  change BitTM
    (fun input => lengthPrefixedWord (atom input))
  simpa only [Function.comp_def] using hphysical

/-- GapCVP reduction support. -/
def sourcePreservedPhysicalAtomicDescriptorOutput
    (atom : List Bool → List Bool) : List Bool → List Bool :=
  originalSourcePreservingOutput
    (sourcePhysicalAtomicDescriptorOutput atom)

/-- GapCVP reduction support. -/
noncomputable def sourcePreservedPhysicalAtomicDescriptorComputable
    {atom : List Bool → List Bool}
    (computer : BitTM atom) :
    BitTM
      (sourcePreservedPhysicalAtomicDescriptorOutput atom) :=
  originalSourcePreservingComputable
    (sourcePhysicalAtomicDescriptorComputable computer)

@[simp] theorem sourcePreservedPhysicalAtomicDescriptorOutput_eq
    (atom : List Bool → List Bool) (input : List Bool) :
    sourcePreservedPhysicalAtomicDescriptorOutput atom input =
      sourceFlatAtomicDescriptor (atom input) ++ false :: input := by
  rfl

end SourceMixedRadixPreservedFourFamilyRecordTM

namespace SourceMixedRadixUnaryQuotientRemainderTM

section

open Turing

/-- Internal support shared across GapCVP continuation modules. -/
structure SourceUnaryDivisionState where
  /-- Whether the encoded division input is valid. -/
  valid : Bool
  /-- The current scanned bit, when present. -/
  current : Option Bool
  deriving Fintype

private def sourceUnaryDivisionControl (valid : Bool) : SourceUnaryDivisionState :=
  ⟨valid, none⟩

private def sourceUnaryDivisionPeek (stack : Fin 8)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState) :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  .peek stack (fun state symbol => { state with current := symbol })
    (.branch (fun state => state.current.isSome) present absent)

private def sourceUnaryDivisionPop (stack : Fin 8)
    (next : Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState) :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  .pop stack (fun state _ => state) next

private def sourceUnaryDivisionGoto (phase : Fin 13) :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  .load (fun state => sourceUnaryDivisionControl state.valid)
    (.goto (fun _ => phase))

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionDividendStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  sourceUnaryDivisionPeek 0
    (sourceUnaryDivisionPop 0
      (.push 1 (fun state => state.current.getD false)
        (.branch (fun state => state.current.getD false)
          (.push 2 (fun _ => true) (sourceUnaryDivisionGoto 0))
          (sourceUnaryDivisionGoto 1))))
    (.load (fun _ => sourceUnaryDivisionControl false)
      (.goto (fun _ => (2 : Fin 13))))

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionModulusStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  sourceUnaryDivisionPeek 0
    (sourceUnaryDivisionPop 0
      (.push 1 (fun state => state.current.getD false)
        (.branch (fun state => state.current.getD false)
          (.push 3 (fun _ => true) (sourceUnaryDivisionGoto 1))
          (sourceUnaryDivisionGoto 2))))
    (.load (fun _ => sourceUnaryDivisionControl false)
      (.goto (fun _ => (2 : Fin 13))))

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionArchiveSuffixStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  sourceUnaryDivisionPeek 0
    (sourceUnaryDivisionPop 0
      (.push 1 (fun state => state.current.getD false)
        (sourceUnaryDivisionGoto 2)))
    (sourceUnaryDivisionGoto 3)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionRestoreSourceStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  sourceUnaryDivisionPeek 1
    (sourceUnaryDivisionPop 1
      (.push 7 (fun state => state.current.getD false)
        (sourceUnaryDivisionGoto 3)))
    (.push 7 (fun _ => false) (sourceUnaryDivisionGoto 4))

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionDispatchStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  .branch (fun state => state.valid)
    (sourceUnaryDivisionPeek 3
      (sourceUnaryDivisionGoto 5)
      (.push 7 (fun _ => false) (sourceUnaryDivisionGoto 9)))
    (.push 7 (fun _ => false) (sourceUnaryDivisionGoto 9))

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionMatchStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  sourceUnaryDivisionPeek 3
    (sourceUnaryDivisionPeek 2
      (sourceUnaryDivisionPop 2
        (sourceUnaryDivisionPop 3
          (.push 4 (fun _ => true)
            (.push 6 (fun _ => true)
              (sourceUnaryDivisionGoto 5)))))
      (sourceUnaryDivisionGoto 7))
    (sourceUnaryDivisionGoto 6)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionRestoreModulusStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  sourceUnaryDivisionPeek 4
    (sourceUnaryDivisionPop 4
      (sourceUnaryDivisionPop 6
        (.push 3 (fun _ => true)
          (sourceUnaryDivisionGoto 6))))
    (.push 5 (fun _ => true) (sourceUnaryDivisionGoto 5))

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionEmitRemainderStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  sourceUnaryDivisionPeek 6
    (sourceUnaryDivisionPop 6
      (.push 7 (fun _ => true) (sourceUnaryDivisionGoto 7)))
    (.push 7 (fun _ => false) (sourceUnaryDivisionGoto 8))

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionEmitQuotientStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  sourceUnaryDivisionPeek 5
    (sourceUnaryDivisionPop 5
      (.push 7 (fun _ => true) (sourceUnaryDivisionGoto 8)))
    (sourceUnaryDivisionGoto 9)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionCleanupModulusStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  sourceUnaryDivisionPeek 3
    (sourceUnaryDivisionPop 3 (sourceUnaryDivisionGoto 9))
    (sourceUnaryDivisionGoto 10)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionCleanupScratchStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  sourceUnaryDivisionPeek 4
    (sourceUnaryDivisionPop 4 (sourceUnaryDivisionGoto 10))
    (sourceUnaryDivisionGoto 11)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionCleanupDividendStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  sourceUnaryDivisionPeek 2
    (sourceUnaryDivisionPop 2 (sourceUnaryDivisionGoto 11))
    (sourceUnaryDivisionGoto 12)

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionCleanupPartialStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 13) SourceUnaryDivisionState :=
  sourceUnaryDivisionPeek 6
    (sourceUnaryDivisionPop 6 (sourceUnaryDivisionGoto 12))
    (.load (fun _ => sourceUnaryDivisionControl true) .halt)

/-- Internal support shared across GapCVP continuation modules. -/
abbrev sourceUnaryDivisionMachine : Turing.FinTM2 where
  K := Fin 8
  k₀ := 0
  k₁ := 7
  Γ _ := Bool
  Λ := Fin 13
  main := 0
  σ := SourceUnaryDivisionState
  initialState := sourceUnaryDivisionControl true
  m phase :=
    if phase = (0 : Fin 13) then
      sourceUnaryDivisionDividendStatement
    else if phase = (1 : Fin 13) then
      sourceUnaryDivisionModulusStatement
    else if phase = (2 : Fin 13) then
      sourceUnaryDivisionArchiveSuffixStatement
    else if phase = (3 : Fin 13) then
      sourceUnaryDivisionRestoreSourceStatement
    else if phase = (4 : Fin 13) then
      sourceUnaryDivisionDispatchStatement
    else if phase = (5 : Fin 13) then
      sourceUnaryDivisionMatchStatement
    else if phase = (6 : Fin 13) then
      sourceUnaryDivisionRestoreModulusStatement
    else if phase = (7 : Fin 13) then
      sourceUnaryDivisionEmitRemainderStatement
    else if phase = (8 : Fin 13) then
      sourceUnaryDivisionEmitQuotientStatement
    else if phase = (9 : Fin 13) then
      sourceUnaryDivisionCleanupModulusStatement
    else if phase = (10 : Fin 13) then
      sourceUnaryDivisionCleanupScratchStatement
    else if phase = (11 : Fin 13) then
      sourceUnaryDivisionCleanupDividendStatement
    else sourceUnaryDivisionCleanupPartialStatement

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionConfiguration
    (phase : Fin 13) (valid : Bool)
    (input archive dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.Cfg where
  l := some phase
  var := sourceUnaryDivisionControl valid
  stk := ![input, archive, dividend, modulus, modulusScratch,
    quotient, residueStack, output]

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivisionMachine_init (input : List Bool) :
    Turing.initList sourceUnaryDivisionMachine input =
      sourceUnaryDivisionConfiguration 0 true
        input [] [] [] [] [] [] [] := by
  simp only [sourceUnaryDivisionMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq,
      dite_eq_ite,
      sourceUnaryDivisionConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `sourceUnaryDivisionStepTac` machine-step simplifier. -/
macro "sourceUnaryDivisionStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [sourceUnaryDivisionMachine,
          sourceUnaryDivisionConfiguration,
          sourceUnaryDivisionControl,
          sourceUnaryDivisionPeek, sourceUnaryDivisionPop,
          sourceUnaryDivisionGoto,
          sourceUnaryDivisionDividendStatement,
          sourceUnaryDivisionModulusStatement,
          sourceUnaryDivisionArchiveSuffixStatement,
          sourceUnaryDivisionRestoreSourceStatement,
          sourceUnaryDivisionDispatchStatement,
          sourceUnaryDivisionMatchStatement,
          sourceUnaryDivisionRestoreModulusStatement,
          sourceUnaryDivisionEmitRemainderStatement,
          sourceUnaryDivisionEmitQuotientStatement,
          sourceUnaryDivisionCleanupModulusStatement,
          sourceUnaryDivisionCleanupScratchStatement,
          sourceUnaryDivisionCleanupDividendStatement,
          sourceUnaryDivisionCleanupPartialStatement,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_dividend_true
    (valid : Bool)
    (input archive dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 0 valid
        (true :: input) archive dividend modulus
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 0 valid
        input (true :: archive) (true :: dividend) modulus
        modulusScratch quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_dividend_false
    (valid : Bool)
    (input archive dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 0 valid
        (false :: input) archive dividend modulus
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 1 valid
        input (false :: archive) dividend modulus
        modulusScratch quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_dividend_missing
    (valid : Bool)
    (archive dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 0 valid
        [] archive dividend modulus
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 2 false
        [] archive dividend modulus
        modulusScratch quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_modulus_true
    (valid : Bool)
    (input archive dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 1 valid
        (true :: input) archive dividend modulus
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 1 valid
        input (true :: archive) dividend (true :: modulus)
        modulusScratch quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_modulus_false
    (valid : Bool)
    (input archive dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 1 valid
        (false :: input) archive dividend modulus
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 2 valid
        input (false :: archive) dividend modulus
        modulusScratch quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_modulus_missing
    (valid : Bool)
    (archive dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 1 valid
        [] archive dividend modulus
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 2 false
        [] archive dividend modulus
        modulusScratch quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_suffix_step
    (valid bit : Bool)
    (input archive dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 2 valid
        (bit :: input) archive dividend modulus
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 2 valid
        input (bit :: archive) dividend modulus
        modulusScratch quotient residueStack output) := by
  cases bit <;> sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_suffix_finish
    (valid : Bool)
    (archive dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 2 valid
        [] archive dividend modulus
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 3 valid
        [] archive dividend modulus
        modulusScratch quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_restoreSource_step
    (valid bit : Bool)
    (archive dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 3 valid
        [] (bit :: archive) dividend modulus
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 3 valid
        [] archive dividend modulus
        modulusScratch quotient residueStack (bit :: output)) := by
  cases bit <;> sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_restoreSource_finish
    (valid : Bool)
    (dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 3 valid
        [] [] dividend modulus
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 4 valid
        [] [] dividend modulus
        modulusScratch quotient residueStack (false :: output)) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_dispatch_valid
    (modulusTail dividend modulusScratch
      quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 4 true
        [] [] dividend (true :: modulusTail)
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 5 true
        [] [] dividend (true :: modulusTail)
        modulusScratch quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_dispatch_zero
    (dividend modulusScratch quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 4 true
        [] [] dividend []
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 9 true
        [] [] dividend []
        modulusScratch quotient residueStack (false :: output)) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_dispatch_invalid
    (dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 4 false
        [] [] dividend modulus
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 9 false
        [] [] dividend modulus
        modulusScratch quotient residueStack (false :: output)) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_match_step
    (valid : Bool)
    (dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 5 valid
        [] [] (true :: dividend) (true :: modulus)
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 5 valid
        [] [] dividend modulus
        (true :: modulusScratch) quotient
        (true :: residueStack) output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_match_full
    (valid : Bool)
    (dividend modulusScratch quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 5 valid
        [] [] dividend []
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 6 valid
        [] [] dividend []
        modulusScratch quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_match_partial
    (valid : Bool)
    (modulus modulusScratch quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 5 valid
        [] [] [] (true :: modulus)
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 7 valid
        [] [] [] (true :: modulus)
        modulusScratch quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_restoreModulus_step
    (valid : Bool)
    (dividend modulus modulusScratch quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 6 valid
        [] [] dividend modulus
        (true :: modulusScratch) quotient (true :: residueStack) output) =
      some (sourceUnaryDivisionConfiguration 6 valid
        [] [] dividend (true :: modulus)
        modulusScratch quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_restoreModulus_finish
    (valid : Bool)
    (dividend modulus quotient output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 6 valid
        [] [] dividend modulus [] quotient [] output) =
      some (sourceUnaryDivisionConfiguration 5 valid
        [] [] dividend modulus [] (true :: quotient) [] output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_emitRemainder_step
    (valid : Bool)
    (modulus modulusScratch quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 7 valid
        [] [] [] modulus
        modulusScratch quotient (true :: residueStack) output) =
      some (sourceUnaryDivisionConfiguration 7 valid
        [] [] [] modulus
        modulusScratch quotient residueStack (true :: output)) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_emitRemainder_finish
    (valid : Bool)
    (modulus modulusScratch quotient output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 7 valid
        [] [] [] modulus
        modulusScratch quotient [] output) =
      some (sourceUnaryDivisionConfiguration 8 valid
        [] [] [] modulus
        modulusScratch quotient [] (false :: output)) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_emitQuotient_step
    (valid : Bool)
    (modulus modulusScratch quotient output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 8 valid
        [] [] [] modulus
        modulusScratch (true :: quotient) [] output) =
      some (sourceUnaryDivisionConfiguration 8 valid
        [] [] [] modulus
        modulusScratch quotient [] (true :: output)) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_emitQuotient_finish
    (valid : Bool)
    (modulus modulusScratch output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 8 valid
        [] [] [] modulus
        modulusScratch [] [] output) =
      some (sourceUnaryDivisionConfiguration 9 valid
        [] [] [] modulus
        modulusScratch [] [] output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_cleanupModulus_step
    (valid : Bool)
    (modulus modulusScratch dividend quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 9 valid
        [] [] dividend (true :: modulus)
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 9 valid
        [] [] dividend modulus
        modulusScratch quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_cleanupModulus_finish
    (valid : Bool)
    (modulusScratch dividend quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 9 valid
        [] [] dividend []
        modulusScratch quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 10 valid
        [] [] dividend []
        modulusScratch quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_cleanupScratch_step
    (valid : Bool)
    (modulusScratch dividend quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 10 valid
        [] [] dividend []
        (true :: modulusScratch) quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 10 valid
        [] [] dividend []
        modulusScratch quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_cleanupScratch_finish
    (valid : Bool)
    (dividend quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 10 valid
        [] [] dividend [] [] quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 11 valid
        [] [] dividend [] [] quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_cleanupDividend_step
    (valid : Bool)
    (dividend quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 11 valid
        [] [] (true :: dividend) [] [] quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 11 valid
        [] [] dividend [] [] quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_cleanupDividend_finish
    (valid : Bool)
    (quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 11 valid
        [] [] [] [] [] quotient residueStack output) =
      some (sourceUnaryDivisionConfiguration 12 valid
        [] [] [] [] [] quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_cleanupPartial_step
    (valid : Bool)
    (quotient residueStack output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 12 valid
        [] [] [] [] [] quotient (true :: residueStack) output) =
      some (sourceUnaryDivisionConfiguration 12 valid
        [] [] [] [] [] quotient residueStack output) := by
  sourceUnaryDivisionStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivision_cleanupPartial_finish
    (valid : Bool) (output : List Bool) :
    sourceUnaryDivisionMachine.step
      (sourceUnaryDivisionConfiguration 12 valid
        [] [] [] [] [] [] [] output) =
      some (Turing.haltList sourceUnaryDivisionMachine output) := by
  sourceUnaryDivisionStepTac

end

section

open Turing GapCVP.BinaryEncoding

/-- GapCVP reduction support. -/
def sourceUnaryDivisionQuery
    (dividend modulus : ℕ) (source : List Bool) : List Bool :=
  List.replicate dividend true ++
    false :: (List.replicate modulus true ++ false :: source)

/-- GapCVP reduction support. -/
def sourceUnaryDivisionOutput (input : List Bool) : List Bool :=
  match readUnaryPrefix input with
  | none => false :: false :: input
  | some (dividend, remaining) =>
      match readUnaryPrefix remaining with
      | none => false :: false :: input
      | some (modulus, _) =>
          if modulus = 0 then false :: false :: input
          else
            List.replicate (dividend / modulus) true ++
              false :: (List.replicate (dividend % modulus) true ++
                false :: input)

@[simp] theorem sourceUnaryDivisionOutput_valid
    (dividend modulus : ℕ) (source : List Bool)
    (hmodulus : 0 < modulus) :
    sourceUnaryDivisionOutput
        (sourceUnaryDivisionQuery dividend modulus source) =
      List.replicate (dividend / modulus) true ++
        false :: (List.replicate (dividend % modulus) true ++
          false :: sourceUnaryDivisionQuery dividend modulus source) := by
  simp only [sourceUnaryDivisionOutput, sourceUnaryDivisionQuery, readUnaryPrefix_replicate,
      Nat.ne_of_gt hmodulus, ↓reduceIte]

end

end SourceMixedRadixUnaryQuotientRemainderTM

end GapCVP

end
