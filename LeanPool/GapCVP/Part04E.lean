/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part04D

/-! # GapCVP proof, part 04, continuation 05 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFTypedRecordWorkerTM

open Turing GapCVP.CL GapCVP.OutputBoundedDependentRecordFold

end CNFTypedRecordWorkerTM

namespace OutputBoundedDependentRecordFold

open Turing

private noncomputable def boundedFold_validScanTrace
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (count : ℕ) (seed : List Bool) (counter : List Bool) :
    EvalsToInTime (boundedDependentRecordFoldMachine computer).step
      (boundedFoldScanConfiguration computer
        (List.map computer.inputAlphabet.invFun
          (unaryBoundedFoldWord count seed)) counter)
      (some (boundedFoldDispatchConfiguration computer
        (List.map computer.inputAlphabet.invFun seed)
        (List.replicate count true ++ counter)))
      (count + 1) := by
  induction count generalizing counter with
  | zero =>
      simpa only [FinTM2.step, Equiv.invFun_as_coe, unaryBoundedFoldWord, List.replicate_zero,
          List.nil_append,
          List.map_cons, zero_add] using
          oneStep _ _ (boundedFold_scan_delimiter computer (List.map computer.inputAlphabet.invFun
              seed) counter)
  | succ count ih =>
      have hfirst := oneStep _ _ (boundedFold_scan_true computer
          (List.map computer.inputAlphabet.invFun
            (unaryBoundedFoldWord count seed)) counter)
      have hrest := ih (true :: counter)
      have hfull := EvalsToInTime.trans (boundedDependentRecordFoldMachine computer).step
        1 (count + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, Equiv.invFun_as_coe, unaryBoundedFoldWord, List.replicate_succ,
          List.cons_append,
          List.map_cons, List.map_append, List.map_replicate, Nat.add_comm, Nat.add_left_comm,
              Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

private noncomputable def boundedFold_drainTrace
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (output : List (computer.tm.Γ computer.tm.k₁))
    (counter scratch : List Bool) :
    EvalsToInTime (boundedDependentRecordFoldMachine computer).step
      (boundedFoldDrainConfiguration computer output counter scratch)
      (some (boundedFoldRestoreConfiguration computer [] counter
        (List.map computer.outputAlphabet output.reverse ++ scratch)))
      (output.length + 1) := by
  induction output generalizing scratch with
  | nil =>
      simpa only [FinTM2.step, List.reverse_nil, List.map_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (boundedFold_drain_finish computer counter scratch)
  | cons symbol remaining ih =>
      have hfirst := oneStep _ _ (boundedFold_drain_step computer symbol remaining
          counter scratch)
      have hrest := ih (computer.outputAlphabet symbol :: scratch)
      have hfull := EvalsToInTime.trans (boundedDependentRecordFoldMachine computer).step
        1 (remaining.length + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, List.reverse_cons, List.map_append, List.map_reverse, List.map_cons,
          List.map_nil,
          List.append_assoc, List.cons_append, List.nil_append, List.length_cons, Nat.add_comm]
              using hfull

private noncomputable def boundedFold_restoreTrace
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (scratch : List Bool)
    (input : List (computer.tm.Γ computer.tm.k₀))
    (counter : List Bool) :
    EvalsToInTime (boundedDependentRecordFoldMachine computer).step
      (boundedFoldRestoreConfiguration computer input
        counter scratch)
      (some (boundedFoldDispatchConfiguration computer
        (List.map computer.inputAlphabet.invFun scratch.reverse ++ input)
        counter))
      (scratch.length + 1) := by
  induction scratch generalizing input with
  | nil =>
      simpa only [FinTM2.step, Equiv.invFun_as_coe, List.reverse_nil, List.map_nil,
          List.nil_append,
          List.length_nil, zero_add] using oneStep _ _ (boundedFold_restore_finish computer input
              counter)
  | cons bit remaining ih =>
      have hfirst := oneStep _ _ (boundedFold_restore_step computer input counter bit remaining)
      have hrest := ih
        (computer.inputAlphabet.invFun bit :: input)
      have hfull := EvalsToInTime.trans (boundedDependentRecordFoldMachine computer).step
        1 (remaining.length + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, Equiv.invFun_as_coe, List.reverse_cons, List.map_append,
          List.map_reverse,
          List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append,
              List.length_cons, Nat.add_comm,
          Nat.add_left_comm, Nat.reduceAdd] using hfull

private noncomputable def boundedFold_outputTransportTrace
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (output counter : List Bool) :
    EvalsToInTime (boundedDependentRecordFoldMachine computer).step
      (boundedFoldDrainConfiguration computer
        (List.map computer.outputAlphabet.invFun output) counter [])
      (some (boundedFoldDispatchConfiguration computer
        (List.map computer.inputAlphabet.invFun output) counter))
      (2 * output.length + 2) := by
  have hfirst := boundedFold_drainTrace computer
    (List.map computer.outputAlphabet.invFun output) counter []
  simp only [List.append_nil] at hfirst
  have hrestore := boundedFold_restoreTrace computer
    (List.map computer.outputAlphabet
      (List.map computer.outputAlphabet.invFun output).reverse)
    [] counter
  simp only [List.append_nil] at hrestore
  have hfull := EvalsToInTime.trans (boundedDependentRecordFoldMachine computer).step
    ((List.map computer.outputAlphabet.invFun output).length + 1)
    ((List.map computer.outputAlphabet
      (List.map computer.outputAlphabet.invFun output).reverse).length + 1)
    _ _ _ hfirst hrestore
  refine {
    steps := hfull.steps
    evals_in_steps := ?_
    steps_le_m := ?_
  }
  · simpa only [Option.bind_eq_bind, FinTM2.step, Equiv.invFun_as_coe, List.map_reverse,
      List.map_map,
        Function.comp_def, Equiv.apply_symm_apply, List.map_id_fun', id_eq, List.reverse_reverse]
            using hfull.evals_in_steps
  · have hbudget := hfull.steps_le_m
    simp only [List.length_map, List.length_reverse] at hbudget
    omega

private noncomputable def boundedFold_workerExecutionTrace
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (input counter : List Bool) :
    EvalsToInTime (boundedDependentRecordFoldMachine computer).step
      (boundedFoldWorkerConfiguration computer counter
        (Turing.initList computer.tm
          (List.map computer.inputAlphabet.invFun input)))
      (some (boundedFoldDrainConfiguration computer
        (List.map computer.outputAlphabet.invFun (worker input))
        counter []))
      (computer.time.eval input.length) := by
  have hphysical :=
    GapCVP.TMComposition.evalsToInTimeMapOfStep
      computer.tm.step
      (boundedDependentRecordFoldMachine computer).step
      (boundedFoldWorkerConfiguration computer counter)
      (boundedFoldWorkerConfiguration_step computer counter)
      (computer.outputsFun input)
  simpa only [FinTM2.step, bitEncoding, Equiv.invFun_as_coe, id_eq,
      boundedFoldWorkerConfiguration_halt] using
      hphysical

private noncomputable def boundedFoldRunBudget
    {worker : List Bool → List Bool}
    (computer : BitTM worker) : ℕ → List Bool → ℕ
  | 0, _ => 1
  | count + 1, seed =>
      1 + computer.time.eval seed.length +
        (2 * (worker seed).length + 2) +
        boundedFoldRunBudget computer count (worker seed)

private noncomputable def boundedFold_iterationTrace
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (count : ℕ) (seed : List Bool) :
    EvalsToInTime (boundedDependentRecordFoldMachine computer).step
      (boundedFoldDispatchConfiguration computer
        (List.map computer.inputAlphabet.invFun seed)
        (List.replicate count true))
      (some (Turing.haltList
        (boundedDependentRecordFoldMachine computer)
        (List.map computer.inputAlphabet.invFun
          ((worker^[count]) seed))))
      (boundedFoldRunBudget computer count seed) := by
  induction count generalizing seed with
  | zero =>
      change EvalsToInTime
        (boundedDependentRecordFoldMachine computer).step
        (boundedFoldDispatchConfiguration computer
          (List.map computer.inputAlphabet.invFun seed) [])
        (some (Turing.haltList
          (boundedDependentRecordFoldMachine computer)
          (List.map computer.inputAlphabet.invFun seed))) 1
      exact oneStep _ _ (boundedFold_dispatch_finish computer
          (List.map computer.inputAlphabet.invFun seed))
  | succ count ih =>
      have hdispatch := oneStep _ _ (boundedFold_dispatch_step computer
          (List.map computer.inputAlphabet.invFun seed)
          (List.replicate count true))
      have hworker := boundedFold_workerExecutionTrace
        computer seed (List.replicate count true)
      have htransport := boundedFold_outputTransportTrace
        computer (worker seed) (List.replicate count true)
      have hremaining := ih (worker seed)
      have hfirst := EvalsToInTime.trans (boundedDependentRecordFoldMachine computer).step
        1 (computer.time.eval seed.length)
        _ _ _ hdispatch hworker
      have hsecond := EvalsToInTime.trans (boundedDependentRecordFoldMachine computer).step
        (computer.time.eval seed.length + 1)
        (2 * (worker seed).length + 2)
        _ _ _ hfirst htransport
      have hfull := EvalsToInTime.trans (boundedDependentRecordFoldMachine computer).step
        ((2 * (worker seed).length + 2) +
          (computer.time.eval seed.length + 1))
        (boundedFoldRunBudget computer count (worker seed))
        _ _ _ hsecond hremaining
      refine {
        steps := hfull.steps
        evals_in_steps := ?_
        steps_le_m := ?_
      }
      · simpa only [List.replicate_succ,
          Function.iterate_succ_apply] using hfull.evals_in_steps
      · have hbudget := hfull.steps_le_m
        simp only [boundedFoldRunBudget]
        omega

private noncomputable def boundedFold_validTotalTrace
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (count : ℕ) (seed : List Bool) :
    EvalsToInTime (boundedDependentRecordFoldMachine computer).step
      (Turing.initList (boundedDependentRecordFoldMachine computer)
        (List.map computer.inputAlphabet.invFun
          (unaryBoundedFoldWord count seed)))
      (some (Turing.haltList
        (boundedDependentRecordFoldMachine computer)
        (List.map computer.inputAlphabet.invFun
          ((worker^[count]) seed))))
      (count + 1 + boundedFoldRunBudget computer count seed) := by
  have hscan := boundedFold_validScanTrace
    computer count seed []
  simp only [List.append_nil] at hscan
  rw [← boundedDependentRecordFoldMachine_init] at hscan
  have hrun := boundedFold_iterationTrace computer count seed
  have hfull := EvalsToInTime.trans (boundedDependentRecordFoldMachine computer).step
    (count + 1) (boundedFoldRunBudget computer count seed)
    _ _ _ hscan hrun
  refine {
    steps := hfull.steps
    evals_in_steps := hfull.evals_in_steps
    steps_le_m := ?_
  }
  have hbudget := hfull.steps_le_m
  omega

theorem parseUnaryBoundedFold_eq_word
    (input : List Bool) (count : ℕ) (seed : List Bool)
    (hparse : parseUnaryBoundedFold input = some (count, seed)) :
    input = unaryBoundedFoldWord count seed := by
  induction input generalizing count seed with
  | nil => simp only [parseUnaryBoundedFold, reduceCtorEq] at hparse
  | cons marker remaining ih =>
      cases marker with
      | false =>
          simp only [parseUnaryBoundedFold, Option.some.injEq, Prod.mk.injEq] at hparse
          obtain ⟨rfl, rfl⟩ := hparse
          rfl
      | true =>
          cases hremaining : parseUnaryBoundedFold remaining with
          | none =>
              simp only [parseUnaryBoundedFold, hremaining, Option.map_none, reduceCtorEq]
                  at hparse
          | some parsed =>
              obtain ⟨parsedCount, parsedSeed⟩ := parsed
              simp only [parseUnaryBoundedFold, hremaining, Option.map_some, Option.some.injEq,
                  Prod.mk.injEq] at hparse
              obtain ⟨rfl, rfl⟩ := hparse
              have hexact := ih parsedCount parsedSeed hremaining
              simp only [hexact, unaryBoundedFoldWord, List.replicate_succ, List.cons_append]

private theorem parseUnaryBoundedFold_none_eq_replicate
    (input : List Bool)
    (hparse : parseUnaryBoundedFold input = none) :
    input = List.replicate input.length true := by
  induction input with
  | nil => rfl
  | cons marker remaining ih =>
      cases marker with
      | false => simp only [parseUnaryBoundedFold, reduceCtorEq] at hparse
      | true =>
          have hremaining :
              parseUnaryBoundedFold remaining = none := by
            cases hcase : parseUnaryBoundedFold remaining with
            | none => rfl
            | some parsed =>
                simp only [parseUnaryBoundedFold, hcase, Option.map_some, reduceCtorEq] at hparse
          have hexact := ih hremaining
          change true :: remaining =
            true :: List.replicate remaining.length true
          exact congrArg (List.cons true) hexact

private noncomputable def boundedFold_missingScanTrace
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (count : ℕ) (counter : List Bool) :
    EvalsToInTime (boundedDependentRecordFoldMachine computer).step
      (boundedFoldScanConfiguration computer
        (List.map computer.inputAlphabet.invFun
          (List.replicate count true)) counter)
      (some (boundedFoldMalformedConfiguration computer
        (List.replicate count true ++ counter)))
      (count + 1) := by
  induction count generalizing counter with
  | zero =>
      simpa only [FinTM2.step, Equiv.invFun_as_coe, List.replicate_zero, List.map_nil,
          List.nil_append,
          zero_add] using oneStep _ _ (boundedFold_scan_missing computer counter)
  | succ count ih =>
      have hfirst := oneStep _ _ (boundedFold_scan_true computer
          (List.map computer.inputAlphabet.invFun
            (List.replicate count true)) counter)
      have hrest := ih (true :: counter)
      have hfull := EvalsToInTime.trans (boundedDependentRecordFoldMachine computer).step
        1 (count + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, Equiv.invFun_as_coe, List.replicate_succ, List.map_cons,
          List.map_replicate,
          List.cons_append, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

private noncomputable def boundedFold_malformedTrace
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (count : ℕ) :
    EvalsToInTime (boundedDependentRecordFoldMachine computer).step
      (boundedFoldMalformedConfiguration computer
        (List.replicate count true))
      (some (Turing.haltList
        (boundedDependentRecordFoldMachine computer) []))
      (count + 1) := by
  induction count with
  | zero =>
      exact oneStep _ _ (boundedFold_malformed_finish computer)
  | succ count ih =>
      have hfirst := oneStep _ _ (boundedFold_malformed_step computer
          (List.replicate count true))
      have hfull := EvalsToInTime.trans (boundedDependentRecordFoldMachine computer).step
        1 (count + 1) _ _ _ hfirst ih
      simpa only [FinTM2.step, List.replicate_succ, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd]
          using hfull

private noncomputable def boundedFold_malformedTotalTrace
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (count : ℕ) :
    EvalsToInTime (boundedDependentRecordFoldMachine computer).step
      (Turing.initList (boundedDependentRecordFoldMachine computer)
        (List.map computer.inputAlphabet.invFun
          (List.replicate count true)))
      (some (Turing.haltList
        (boundedDependentRecordFoldMachine computer) []))
      (2 * count + 2) := by
  have hscan := boundedFold_missingScanTrace computer count []
  simp only [List.append_nil] at hscan
  rw [← boundedDependentRecordFoldMachine_init] at hscan
  have hclear := boundedFold_malformedTrace computer count
  have hfull := EvalsToInTime.trans (boundedDependentRecordFoldMachine computer).step
    (count + 1) (count + 1) _ _ _ hscan hclear
  refine {
    steps := hfull.steps
    evals_in_steps := hfull.evals_in_steps
    steps_le_m := ?_
  }
  have hbudget := hfull.steps_le_m
  omega

private noncomputable def boundedDependentRecordFoldTimePolynomial
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (bound : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X *
      (computer.time.comp bound + 2 * bound + 3) +
    2 * Polynomial.X + 5

private theorem boundedFoldRunBudget_le
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (bound : Polynomial ℕ)
    (inputLength count : ℕ)
    (seed : List Bool)
    (hstates : ∀ stage : ℕ, stage ≤ count →
      ((worker^[stage]) seed).length ≤ bound.eval inputLength) :
    boundedFoldRunBudget computer count seed ≤
      count *
        (computer.time.eval (bound.eval inputLength) +
          2 * bound.eval inputLength + 3) + 1 := by
  induction count generalizing seed with
  | zero => simp only [boundedFoldRunBudget, zero_mul, zero_add, Std.le_refl]
  | succ count ih =>
      have hseed : seed.length ≤ bound.eval inputLength := by
        simpa only [Function.iterate_zero, id_eq] using hstates 0 (by omega)
      have htime :
          computer.time.eval seed.length ≤
            computer.time.eval (bound.eval inputLength) :=
        GapCVP.TMComposition.natPolynomial_eval_monotone
          computer.time hseed
      have houtput : (worker seed).length ≤
          bound.eval inputLength := by
        simpa only [Function.iterate_one] using hstates 1 (by omega)
      have hremaining :
          ∀ stage : ℕ, stage ≤ count →
            ((worker^[stage]) (worker seed)).length ≤
              bound.eval inputLength := by
        intro stage hstage
        simpa only [Function.iterate_succ_apply] using
          hstates (stage + 1) (by omega)
      have htail := ih (worker seed) hremaining
      let cost :=
        computer.time.eval (bound.eval inputLength) +
          2 * bound.eval inputLength + 3
      have htail' :
          boundedFoldRunBudget computer count (worker seed) ≤
            count * cost + 1 := by
        simpa only using htail
      change
        1 + computer.time.eval seed.length +
            (2 * (worker seed).length + 2) +
            boundedFoldRunBudget computer count (worker seed) ≤
          (count + 1) * cost + 1
      calc
        _ ≤ 1 + computer.time.eval (bound.eval inputLength) +
            (2 * bound.eval inputLength + 2) +
            (count * cost + 1) := by omega
        _ = (count + 1) * cost + 1 := by
          dsimp [cost]
          ring

private theorem boundedFold_validTotalBudget_le
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (bound : Polynomial ℕ)
    (hbounded : PolynomiallyBoundedFoldStates worker bound)
    (input : List Bool) (count : ℕ) (seed : List Bool)
    (hparse : parseUnaryBoundedFold input = some (count, seed)) :
    count + 1 + boundedFoldRunBudget computer count seed ≤
      (boundedDependentRecordFoldTimePolynomial
        computer bound).eval input.length := by
  have bounded := hbounded
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq] at bounded
  have hcount := parsedUnaryFold_count_le_length
    input count seed hparse
  have hstates := bounded input count seed hparse
  have hrun := boundedFoldRunBudget_le computer bound
    input.length count seed hstates
  let transitionCost :=
    computer.time.eval (bound.eval input.length) +
      2 * bound.eval input.length + 3
  have hproduct :
      count * transitionCost ≤ input.length * transitionCost :=
    Nat.mul_le_mul_right transitionCost hcount
  simp only [boundedDependentRecordFoldTimePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_X,
    Polynomial.eval_ofNat]
  change count + 1 + boundedFoldRunBudget computer count seed ≤
    input.length * transitionCost + 2 * input.length + 5
  change boundedFoldRunBudget computer count seed ≤
    count * transitionCost + 1 at hrun
  omega

private theorem boundedFold_malformedTotalBudget_le
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (bound : Polynomial ℕ) (inputLength : ℕ) :
    2 * inputLength + 2 ≤
      (boundedDependentRecordFoldTimePolynomial
        computer bound).eval inputLength := by
  simp only [boundedDependentRecordFoldTimePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_X,
    Polynomial.eval_ofNat]
  omega

private noncomputable def boundedDependentRecordFold_totalTrace
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (bound : Polynomial ℕ)
    (hbounded : PolynomiallyBoundedFoldStates worker bound)
    (input : List Bool) :
    EvalsToInTime (boundedDependentRecordFoldMachine computer).step
      (Turing.initList (boundedDependentRecordFoldMachine computer)
        (List.map computer.inputAlphabet.invFun input))
      (some (Turing.haltList
        (boundedDependentRecordFoldMachine computer)
        (List.map computer.inputAlphabet.invFun
          (boundedRecordFoldOutput worker input))))
      ((boundedDependentRecordFoldTimePolynomial
        computer bound).eval input.length) := by
  cases hparse : parseUnaryBoundedFold input with
  | none =>
      have hinput := parseUnaryBoundedFold_none_eq_replicate
        input hparse
      have hphysical := boundedFold_malformedTotalTrace
        computer input.length
      rw [← hinput] at hphysical
      have hbudget := boundedFold_malformedTotalBudget_le
        computer bound input.length
      have htotal := rebound hphysical hbudget
      convert htotal using 1;
        simp [boundedRecordFoldOutput, hparse]; rfl
  | some parsed =>
      obtain ⟨count, seed⟩ := parsed
      have hinput := parseUnaryBoundedFold_eq_word
        input count seed hparse
      have hphysical := boundedFold_validTotalTrace
        computer count seed
      rw [← hinput] at hphysical
      have hbudget := boundedFold_validTotalBudget_le
        computer bound hbounded input count seed hparse
      have htotal := rebound hphysical hbudget
      simpa only [FinTM2.step, Equiv.invFun_as_coe, boundedRecordFoldOutput, hparse] using htotal

/-- GapCVP reduction support. -/
noncomputable def boundedDependentRecordFoldComputable
    {worker : List Bool → List Bool}
    (computer : BitTM worker)
    (bound : Polynomial ℕ)
    (hbounded : PolynomiallyBoundedFoldStates worker bound) :
    BitTM
      (boundedRecordFoldOutput worker) where
  tm := boundedDependentRecordFoldMachine computer
  inputAlphabet := computer.inputAlphabet
  outputAlphabet := computer.inputAlphabet
  time := boundedDependentRecordFoldTimePolynomial
    computer bound
  outputsFun input := by
    change EvalsToInTime
      (boundedDependentRecordFoldMachine computer).step
      (Turing.initList (boundedDependentRecordFoldMachine computer)
        (List.map computer.inputAlphabet.invFun input))
      (some (Turing.haltList
        (boundedDependentRecordFoldMachine computer)
        (List.map computer.inputAlphabet.invFun
          (boundedRecordFoldOutput worker input))))
      ((boundedDependentRecordFoldTimePolynomial
        computer bound).eval input.length)
    exact boundedDependentRecordFold_totalTrace
      computer bound hbounded input

end OutputBoundedDependentRecordFold

namespace CNFFlatStructuralRecordWorkerTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.CNFTypedRecordWorkerTM

/-- GapCVP reduction support. -/
def flatSignedLiteralDescriptor (literal : Literal) : List Bool :=
  lengthPrefixedWord (literal.2 :: encodeNat literal.1)

/-- Internal support shared across GapCVP continuation modules. -/
def flatLiteralRecordStep (input : List Bool) : List Bool :=
  match readLengthPrefixedWord input with
  | some (sign :: payload, suffix) =>
      suffix ++ lengthPrefixedWord payload ++ [sign]
  | _ => []

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem flatLiteralRecordStep_descriptor
    (literal : Literal) (suffix : List Bool) :
    flatLiteralRecordStep
      (flatSignedLiteralDescriptor literal ++ suffix) =
        suffix ++ encodeLiteral literal := by
  rcases literal with ⟨index, sign⟩
  simp only [flatLiteralRecordStep, flatSignedLiteralDescriptor, readLengthPrefixedWord_append,
      List.append_assoc, encodeLiteral]

/-- GapCVP reduction support. -/
def flatSignedLiteralDescriptorStream
    (literals : List Literal) : List Bool :=
  literals.flatMap flatSignedLiteralDescriptor

private theorem flatLiteralRecordStep_length_le (input : List Bool) :
    (flatLiteralRecordStep input).length ≤ input.length := by
  cases unaryInputSplit input with
  | inl witness =>
      obtain ⟨count, hinput⟩ := witness
      subst input
      simp only [flatLiteralRecordStep, readLengthPrefixedWord, readUnaryPrefix_missing,
          List.length_nil,
          List.length_replicate, zero_le]
  | inr witness =>
      obtain ⟨count, tail, hinput⟩ := witness
      subst input
      by_cases hlength : count ≤ tail.length
      · rw [validInput_reconstruct count tail hlength]
        generalize hbody : tail.take count = body
        cases body with
        | nil =>
            simp only [flatLiteralRecordStep, readLengthPrefixedWord_append, List.length_nil,
                List.length_append,
                lengthPrefixedWord_length, mul_zero, zero_add, List.length_drop, zero_le]
        | cons sign payload =>
            simp only [flatLiteralRecordStep,
              readLengthPrefixedWord_append,
              List.length_append, lengthPrefixedWord_length,
              List.length_cons, List.length_nil, List.length_drop]
            omega
      · simp only [flatLiteralRecordStep, readLengthPrefixedWord, readUnaryPrefix_replicate,
          hlength, ↓reduceIte,
            List.length_nil, List.length_append, List.length_replicate, List.length_cons, zero_le]

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecordStep_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates
      flatLiteralRecordStep Polynomial.X := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage hstage
  have hseed : seed.length ≤ input.length :=
    parsedUnaryFold_seed_length_le input count seed hparse
  have hiterate : ∀ n : ℕ,
      ((flatLiteralRecordStep^[n]) seed).length ≤ seed.length := by
    intro n
    induction n with
    | zero => simp only [Function.iterate_zero, id_eq, Std.le_refl]
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (flatLiteralRecordStep_length_le _).trans ih
  simpa only [Polynomial.eval_X, ge_iff_le] using (hiterate stage).trans hseed

/-- Internal support shared across GapCVP continuation modules. -/
structure FlatLiteralRecordState where
  /-- The inspected literal bit, when present. -/
  inspected : Option Bool
  /-- The literal sign bit, when present. -/
  sign : Option Bool
  deriving Fintype

private def flatLiteralRecordPeek (stack : Fin 6)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState) :
    Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState :=
  .peek stack (fun state bit => { state with inspected := bit })
    (.branch (fun state => state.inspected.isSome) present absent)

private def flatLiteralRecordPop (stack : Fin 6)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState) :
    Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState :=
  .pop stack (fun state _ => state) continuation

private def flatLiteralRecordPushBit (stack : Fin 6)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState) :
    Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState :=
  .push stack (fun state => state.inspected.getD false) continuation

private def flatLiteralRecordPushConstant (stack : Fin 6) (bit : Bool)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState) :
    Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState :=
  .push stack (fun _ => bit) continuation

private def flatLiteralRecordGoto (phase : Fin 8) :
    Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState :=
  .load (fun state => { state with inspected := none })
    (.goto (fun _ => phase))

/-- Internal support shared across GapCVP continuation modules. -/
def flatLiteralRecordPrefixStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState :=
  flatLiteralRecordPeek 0
    (.branch (fun state => state.inspected.getD false)
      (flatLiteralRecordPop 0
        (flatLiteralRecordPushConstant 1 true
          (flatLiteralRecordGoto 0)))
      (flatLiteralRecordPop 0
        (flatLiteralRecordGoto 1)))
    (flatLiteralRecordGoto 7)

/-- Internal support shared across GapCVP continuation modules. -/
def flatLiteralRecordSignStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState :=
  flatLiteralRecordPeek 1
    (flatLiteralRecordPeek 0
      (flatLiteralRecordPop 1
        (flatLiteralRecordPop 0
          (.load (fun state =>
              { inspected := none, sign := state.inspected })
            (.goto (fun _ => (2 : Fin 8))))))
      (flatLiteralRecordGoto 7))
    (flatLiteralRecordGoto 7)

/-- Internal support shared across GapCVP continuation modules. -/
def flatLiteralRecordPayloadStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState :=
  flatLiteralRecordPeek 1
    (flatLiteralRecordPeek 0
      (flatLiteralRecordPop 1
        (flatLiteralRecordPop 0
          (flatLiteralRecordPushBit 2
            (flatLiteralRecordPushConstant 3 true
              (flatLiteralRecordGoto 2)))))
      (flatLiteralRecordGoto 7))
    (.push 5 (fun state => state.sign.getD false)
      (flatLiteralRecordGoto 3))

/-- Internal support shared across GapCVP continuation modules. -/
def flatLiteralRecordRestoreStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState :=
  flatLiteralRecordPeek 2
    (flatLiteralRecordPop 2
      (flatLiteralRecordPushBit 5
        (flatLiteralRecordGoto 3)))
    (flatLiteralRecordPushConstant 5 false
      (flatLiteralRecordGoto 4))

/-- Internal support shared across GapCVP continuation modules. -/
def flatLiteralRecordMarkerStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState :=
  flatLiteralRecordPeek 3
    (flatLiteralRecordPop 3
      (flatLiteralRecordPushConstant 5 true
        (flatLiteralRecordGoto 4)))
    (flatLiteralRecordGoto 5)

/-- Internal support shared across GapCVP continuation modules. -/
def flatLiteralRecordSuffixScanStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState :=
  flatLiteralRecordPeek 0
    (flatLiteralRecordPop 0
      (flatLiteralRecordPushBit 4
        (flatLiteralRecordGoto 5)))
    (flatLiteralRecordGoto 6)

/-- Internal support shared across GapCVP continuation modules. -/
def flatLiteralRecordSuffixRestoreStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState :=
  flatLiteralRecordPeek 4
    (flatLiteralRecordPop 4
      (flatLiteralRecordPushBit 5
        (flatLiteralRecordGoto 6)))
    (.load (fun _ => { inspected := none, sign := none }) .halt)

/-- Internal support shared across GapCVP continuation modules. -/
def flatLiteralRecordInvalidStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 8) FlatLiteralRecordState :=
  flatLiteralRecordPeek 1
    (flatLiteralRecordPop 1 (flatLiteralRecordGoto 7))
    (flatLiteralRecordPeek 2
      (flatLiteralRecordPop 2 (flatLiteralRecordGoto 7))
      (flatLiteralRecordPeek 3
        (flatLiteralRecordPop 3 (flatLiteralRecordGoto 7))
        (flatLiteralRecordPeek 0
          (flatLiteralRecordPop 0 (flatLiteralRecordGoto 7))
          (.load (fun _ => { inspected := none, sign := none })
            .halt))))

/-- Internal support shared across GapCVP continuation modules. -/
abbrev actualFlatLiteralRecordWorker : Turing.FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 5
  Γ _ := Bool
  Λ := Fin 8
  main := 0
  σ := FlatLiteralRecordState
  initialState := { inspected := none, sign := none }
  m phase :=
    if phase = (0 : Fin 8) then flatLiteralRecordPrefixStatement
    else if phase = (1 : Fin 8) then flatLiteralRecordSignStatement
    else if phase = (2 : Fin 8) then flatLiteralRecordPayloadStatement
    else if phase = (3 : Fin 8) then flatLiteralRecordRestoreStatement
    else if phase = (4 : Fin 8) then flatLiteralRecordMarkerStatement
    else if phase = (5 : Fin 8) then flatLiteralRecordSuffixScanStatement
    else if phase = (6 : Fin 8) then flatLiteralRecordSuffixRestoreStatement
    else flatLiteralRecordInvalidStatement

/-- Internal support shared across GapCVP continuation modules. -/
def flatLiteralRecordConfiguration (phase : Fin 8)
    (sign : Option Bool)
    (input count reversed markers suffix output : List Bool) :
    actualFlatLiteralRecordWorker.Cfg where
  l := some phase
  var := { inspected := none, sign := sign }
  stk := ![input, count, reversed, markers, suffix, output]

/-- Internal support shared across GapCVP continuation modules. -/
theorem actualFlatLiteralRecordWorker_init (input : List Bool) :
    Turing.initList actualFlatLiteralRecordWorker input =
      flatLiteralRecordConfiguration 0 none input [] [] [] [] [] := by
  simp only [actualFlatLiteralRecordWorker, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq,
      dite_eq_ite,
      flatLiteralRecordConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `flatLiteralRecordStepTac` machine-step simplifier. -/
macro "flatLiteralRecordStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [actualFlatLiteralRecordWorker,
          flatLiteralRecordConfiguration, flatLiteralRecordPeek,
          flatLiteralRecordPop, flatLiteralRecordPushBit,
          flatLiteralRecordPushConstant, flatLiteralRecordGoto,
          flatLiteralRecordPrefixStatement,
          flatLiteralRecordSignStatement,
          flatLiteralRecordPayloadStatement,
          flatLiteralRecordRestoreStatement,
          flatLiteralRecordMarkerStatement,
          flatLiteralRecordSuffixScanStatement,
          flatLiteralRecordSuffixRestoreStatement,
          flatLiteralRecordInvalidStatement,
          Turing.haltList, Turing.FinTM2.step, Turing.TM2.step,
          Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_prefix_true
    (sign : Option Bool)
    (input count reversed markers suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 0 sign
        (true :: input) count reversed markers suffix output) =
      some (flatLiteralRecordConfiguration 0 sign input
        (true :: count) reversed markers suffix output) := by
  flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_prefix_false
    (sign : Option Bool)
    (input count reversed markers suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 0 sign
        (false :: input) count reversed markers suffix output) =
      some (flatLiteralRecordConfiguration 1 sign
        input count reversed markers suffix output) := by
  flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_prefix_missing
    (sign : Option Bool)
    (count reversed markers suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 0 sign
        [] count reversed markers suffix output) =
      some (flatLiteralRecordConfiguration 7 sign
        [] count reversed markers suffix output) := by
  flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_sign_step
    (oldSign : Option Bool) (sign marker : Bool)
    (input count reversed markers suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 1 oldSign
        (sign :: input) (marker :: count)
        reversed markers suffix output) =
      some (flatLiteralRecordConfiguration 2 (some sign)
        input count reversed markers suffix output) := by
  cases sign <;> cases marker <;> flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_sign_empty
    (sign : Option Bool)
    (input reversed markers suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 1 sign
        input [] reversed markers suffix output) =
      some (flatLiteralRecordConfiguration 7 sign
        input [] reversed markers suffix output) := by
  flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_sign_missing
    (sign : Option Bool) (marker : Bool)
    (count reversed markers suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 1 sign
        [] (marker :: count) reversed markers suffix output) =
      some (flatLiteralRecordConfiguration 7 sign
        [] (marker :: count) reversed markers suffix output) := by
  cases marker <;> flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_payload_step
    (sign : Option Bool) (bit marker : Bool)
    (input count reversed markers suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 2 sign
        (bit :: input) (marker :: count)
        reversed markers suffix output) =
      some (flatLiteralRecordConfiguration 2 sign input count
        (bit :: reversed) (true :: markers) suffix output) := by
  cases bit <;> cases marker <;> flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_payload_finish
    (sign : Bool)
    (input reversed markers suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 2 (some sign)
        input [] reversed markers suffix output) =
      some (flatLiteralRecordConfiguration 3 (some sign)
        input [] reversed markers suffix (sign :: output)) := by
  cases sign <;> flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_payload_missing
    (sign : Option Bool) (marker : Bool)
    (count reversed markers suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 2 sign
        [] (marker :: count) reversed markers suffix output) =
      some (flatLiteralRecordConfiguration 7 sign
        [] (marker :: count) reversed markers suffix output) := by
  cases marker <;> flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_restore_step
    (sign : Option Bool) (bit : Bool)
    (input reversed markers suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 3 sign
        input [] (bit :: reversed) markers suffix output) =
      some (flatLiteralRecordConfiguration 3 sign
        input [] reversed markers suffix (bit :: output)) := by
  cases bit <;> flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_restore_finish
    (sign : Option Bool)
    (input markers suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 3 sign
        input [] [] markers suffix output) =
      some (flatLiteralRecordConfiguration 4 sign
        input [] [] markers suffix (false :: output)) := by
  flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_marker_step
    (sign : Option Bool) (marker : Bool)
    (input markers suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 4 sign
        input [] [] (marker :: markers) suffix output) =
      some (flatLiteralRecordConfiguration 4 sign
        input [] [] markers suffix (true :: output)) := by
  cases marker <;> flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_marker_finish
    (sign : Option Bool)
    (input suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 4 sign
        input [] [] [] suffix output) =
      some (flatLiteralRecordConfiguration 5 sign
        input [] [] [] suffix output) := by
  flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_suffix_scan_step
    (sign : Option Bool) (bit : Bool)
    (input suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 5 sign
        (bit :: input) [] [] [] suffix output) =
      some (flatLiteralRecordConfiguration 5 sign
        input [] [] [] (bit :: suffix) output) := by
  cases bit <;> flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_suffix_scan_finish
    (sign : Option Bool) (suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 5 sign
        [] [] [] [] suffix output) =
      some (flatLiteralRecordConfiguration 6 sign
        [] [] [] [] suffix output) := by
  flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_suffix_restore_step
    (sign : Option Bool) (bit : Bool)
    (suffix output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 6 sign
        [] [] [] [] (bit :: suffix) output) =
      some (flatLiteralRecordConfiguration 6 sign
        [] [] [] [] suffix (bit :: output)) := by
  cases bit <;> flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_suffix_restore_finish
    (sign : Option Bool) (output : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 6 sign
        [] [] [] [] [] output) =
      some (Turing.haltList actualFlatLiteralRecordWorker output) := by
  flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_invalid_count
    (sign : Option Bool) (bit : Bool)
    (input count reversed markers : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 7 sign
        input (bit :: count) reversed markers [] []) =
      some (flatLiteralRecordConfiguration 7 sign
        input count reversed markers [] []) := by
  cases bit <;> flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_invalid_reversed
    (sign : Option Bool) (bit : Bool)
    (input reversed markers : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 7 sign
        input [] (bit :: reversed) markers [] []) =
      some (flatLiteralRecordConfiguration 7 sign
        input [] reversed markers [] []) := by
  cases bit <;> flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_invalid_markers
    (sign : Option Bool) (bit : Bool)
    (input markers : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 7 sign
        input [] [] (bit :: markers) [] []) =
      some (flatLiteralRecordConfiguration 7 sign
        input [] [] markers [] []) := by
  cases bit <;> flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_invalid_input
    (sign : Option Bool) (bit : Bool) (input : List Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 7 sign
        (bit :: input) [] [] [] [] []) =
      some (flatLiteralRecordConfiguration 7 sign
        input [] [] [] [] []) := by
  cases bit <;> flatLiteralRecordStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatLiteralRecord_invalid_finish (sign : Option Bool) :
    actualFlatLiteralRecordWorker.step
      (flatLiteralRecordConfiguration 7 sign
        [] [] [] [] [] []) =
      some (Turing.haltList actualFlatLiteralRecordWorker []) := by
  flatLiteralRecordStepTac

end CNFFlatStructuralRecordWorkerTM

end GapCVP

end
