/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part05A

/-! # GapCVP proof, part 05, continuation 02 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFSourcePairPrefixWorkerTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.CNFUnaryPairIndexTM

end CNFSourcePairPrefixWorkerTM

namespace CNFSourcePairPrefixWorkerTotalCert

open Computability Turing GapCVP.SourceTotalStructuralDecoder GapCVP.CNFUnaryPairIndexTM
open GapCVP.CNFSourcePairPrefixWorkerTM

private def sourcePairPrefix_firstTrace
    (count : ℕ) (tail first second output : List Bool) :
    EvalsToInTime actualSourcePairPrefixMachine.step (sourcePairPrefixConfiguration 0
        (List.replicate count true ++ false :: tail)
        first second output)
      (some (sourcePairPrefixConfiguration 1 tail
        (List.replicate count true ++ first) second output))
      (count + 1) := by
  induction count generalizing first with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourcePairPrefix_first_false tail first second output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourcePairPrefix_first_true
          (List.replicate count true ++ false :: tail)
          first second output)
      have hrest := ih (true :: first)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _ hfirst hrest

private def sourcePairPrefix_secondTrace
    (count : ℕ) (tail first second output : List Bool) :
    EvalsToInTime actualSourcePairPrefixMachine.step (sourcePairPrefixConfiguration 1
        (List.replicate count true ++ false :: tail)
        first second output)
      (some (sourcePairPrefixConfiguration 2 tail first
        (List.replicate count true ++ second)
        (false :: output)))
      (count + 1) := by
  induction count generalizing second with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourcePairPrefix_second_false tail first second output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourcePairPrefix_second_true
          (List.replicate count true ++ false :: tail)
          first second output)
      have hrest := ih (true :: second)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _ hfirst hrest

private def sourcePairPrefix_suffixTrace
    (suffix first second output : List Bool) :
    EvalsToInTime actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 2 suffix first second output)
      (some (sourcePairPrefixConfiguration 3
        [] first second output))
      (suffix.length + 1) := by
  induction suffix with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, zero_add] using
          oneStep _ _ (sourcePairPrefix_suffix_finish first second output)
  | cons bit suffix ih =>
      have hfirst := oneStep _ _ (sourcePairPrefix_suffix_step bit suffix
          first second output)
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, Nat.add_assoc, Nat.reduceAdd] using
          EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _ hfirst ih

private def sourcePairPrefix_secondRestoreTrace
    (count : ℕ) (first output : List Bool) :
    EvalsToInTime actualSourcePairPrefixMachine.step (sourcePairPrefixConfiguration 3
        [] first (List.replicate count true) output)
      (some (sourcePairPrefixConfiguration 4 [] first []
        (false :: (List.replicate count true ++ output))))
      (count + 1) := by
  induction count generalizing output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourcePairPrefix_secondRestore_finish first output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourcePairPrefix_secondRestore_step first
          (List.replicate count true) output)
      have hrest := ih (true :: output)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _ hfirst hrest

private def sourcePairPrefix_firstRestoreTrace
    (count : ℕ) (output : List Bool) :
    EvalsToInTime actualSourcePairPrefixMachine.step (sourcePairPrefixConfiguration 4
        [] (List.replicate count true) [] output)
      (some (Turing.haltList actualSourcePairPrefixMachine
        (List.replicate count true ++ output)))
      (count + 1) := by
  induction count generalizing output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourcePairPrefix_firstRestore_finish output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourcePairPrefix_firstRestore_step
          (List.replicate count true) output)
      have hrest := ih (true :: output)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _ hfirst hrest

private def sourcePairPrefix_validTrace
    (first second : ℕ) (suffix : List Bool) :
    EvalsToInTime actualSourcePairPrefixMachine.step (sourcePairPrefixConfiguration 0
        (unarySourcePairWord first second ++ suffix) [] [] [])
      (some (Turing.haltList actualSourcePairPrefixMachine
        (unarySourcePairWord first second)))
      (2 * first + 2 * second + suffix.length + 5) := by
  have hfirst := sourcePairPrefix_firstTrace first
    (List.replicate second true ++ false :: suffix)
    [] [] []
  simp only [List.append_nil] at hfirst
  have hsecond := sourcePairPrefix_secondTrace second suffix
    (List.replicate first true) [] []
  simp only [List.append_nil] at hsecond
  have hscan := EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _ hfirst hsecond
  have hsuffix := sourcePairPrefix_suffixTrace suffix
    (List.replicate first true)
    (List.replicate second true) [false]
  have hbeforeRestore := EvalsToInTime.trans
    actualSourcePairPrefixMachine.step _ _ _ _ _ hscan hsuffix
  have hsecondRestore := sourcePairPrefix_secondRestoreTrace second
    (List.replicate first true) [false]
  have hbeforeFirst := EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _
    hbeforeRestore hsecondRestore
  have hfirstRestore := sourcePairPrefix_firstRestoreTrace first
    (false :: (List.replicate second true ++ [false]))
  have hfull := EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _
    hbeforeFirst hfirstRestore
  have hbounded := rebound (newBudget := 2 * first + 2 * second + suffix.length + 5)
    hfull (by omega)
  simpa only [FinTM2.step, Fin.isValue, unarySourcePairWord, List.append_assoc, List.cons_append,
      List.nil_append] using hbounded

private def sourcePairPrefix_failureTrace
    (input first second output : List Bool) :
    EvalsToInTime actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 5 input first second output)
      (some (Turing.haltList actualSourcePairPrefixMachine []))
      (input.length + first.length + second.length +
        output.length + 1) := by
  induction input generalizing first second output with
  | cons bit input ih =>
      have hfirst := oneStep _ _ (sourcePairPrefix_failure_input_step bit input
          first second output)
      have hrest := ih first second output
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, Nat.add_comm, Nat.add_left_comm,
          Nat.reduceAdd,
          Nat.add_assoc] using EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _
              hfirst hrest
  | nil =>
      induction first generalizing second output with
      | cons bit first ih =>
          have hfirst := oneStep _ _ (sourcePairPrefix_failure_first_step bit first
              second output)
          have hrest := ih second output
          simpa only [FinTM2.step, Fin.isValue, List.length_nil, List.length_cons, zero_add,
              Nat.add_comm,
              Nat.add_left_comm, Nat.reduceAdd, Nat.add_assoc] using
              EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _ hfirst hrest
      | nil =>
          induction second generalizing output with
          | cons bit second ih =>
              have hfirst := oneStep _ _ (sourcePairPrefix_failure_second_step bit
                  second output)
              have hrest := ih output
              simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero, List.length_cons,
                  zero_add, Nat.add_comm,
                  Nat.add_left_comm, Nat.reduceAdd, Nat.add_assoc] using
                  EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _ hfirst hrest
          | nil =>
              induction output with
              | cons bit output ih =>
                  have hfirst := oneStep _ _ (sourcePairPrefix_failure_output_step bit output)
                  simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero,
                      List.length_cons, zero_add, Nat.add_comm,
                      Nat.add_left_comm, Nat.reduceAdd] using EvalsToInTime.trans
                          actualSourcePairPrefixMachine.step _ _ _ _ _ hfirst ih
              | nil =>
                  simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero, zero_add] using
                      oneStep _ _ sourcePairPrefix_failure_finish

private def sourcePairPrefix_firstMissingTrace
    (count : ℕ) (first second output : List Bool) :
    EvalsToInTime actualSourcePairPrefixMachine.step (sourcePairPrefixConfiguration 0
        (List.replicate count true) first second output)
      (some (sourcePairPrefixConfiguration 5 []
        (List.replicate count true ++ first) second output))
      (count + 1) := by
  induction count generalizing first with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourcePairPrefix_first_missing first second output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourcePairPrefix_first_true
          (List.replicate count true) first second output)
      have hrest := ih (true :: first)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _ hfirst hrest

private def sourcePairPrefix_secondMissingTrace
    (count : ℕ) (first second output : List Bool) :
    EvalsToInTime actualSourcePairPrefixMachine.step (sourcePairPrefixConfiguration 1
        (List.replicate count true) first second output)
      (some (sourcePairPrefixConfiguration 5 [] first
        (List.replicate count true ++ second) output))
      (count + 1) := by
  induction count generalizing second with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourcePairPrefix_second_missing first second output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourcePairPrefix_second_true
          (List.replicate count true) first second output)
      have hrest := ih (true :: second)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _ hfirst hrest

private def sourcePairPrefix_totalTrace (input : List Bool) :
    EvalsToInTime actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 0 input [] [] [])
      (some (Turing.haltList actualSourcePairPrefixMachine
        (sourcePairPrefixOutput input)))
      (6 * input.length + 12) := by
  cases unaryInputSplit input with
  | inl witness =>
      obtain ⟨count, hinput⟩ := witness
      subst input
      have hprefix := sourcePairPrefix_firstMissingTrace count
        [] [] []
      simp only [List.append_nil] at hprefix
      have hclean := sourcePairPrefix_failureTrace []
        (List.replicate count true) [] []
      have hfull := EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _
        hprefix hclean
      have hbounded := rebound (newBudget := 6 * (List.replicate count true).length + 12)
        hfull (by simp only [List.length_nil, List.length_replicate, zero_add, add_zero]; omega)
      simpa only [FinTM2.step, Fin.isValue, sourcePairPrefixOutput, readUnaryPrefix_missing,
          List.length_replicate] using hbounded
  | inr witness =>
      obtain ⟨first, remaining, hinput⟩ := witness
      subst input
      cases unaryInputSplit remaining with
      | inl missing =>
          obtain ⟨second, hremaining⟩ := missing
          subst remaining
          have hfirst := sourcePairPrefix_firstTrace first
            (List.replicate second true) [] [] []
          simp only [List.append_nil] at hfirst
          have hsecond := sourcePairPrefix_secondMissingTrace second
            (List.replicate first true) [] []
          simp only [List.append_nil] at hsecond
          have hscan := EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _
            hfirst hsecond
          have hclean := sourcePairPrefix_failureTrace []
            (List.replicate first true)
            (List.replicate second true) []
          have hfull := EvalsToInTime.trans actualSourcePairPrefixMachine.step _ _ _ _ _
            hscan hclean
          have hbounded := rebound (newBudget := 6 *
              (List.replicate first true ++
                false :: List.replicate second true).length + 12)
            hfull (by
              simp only [List.length_nil, List.length_replicate, zero_add, add_zero,
                  List.length_append, List.length_cons]
              omega)
          simpa only [FinTM2.step, Fin.isValue, sourcePairPrefixOutput,
              BinaryEncoding.readUnaryPrefix_replicate,
              readUnaryPrefix_missing, List.length_append, List.length_replicate, List.length_cons]
                  using hbounded
      | inr delimited =>
          obtain ⟨second, suffix, hremaining⟩ := delimited
          subst remaining
          have hvalid := sourcePairPrefix_validTrace
            first second suffix
          have hbounded := rebound (newBudget := 6 *
              (unarySourcePairWord first second ++ suffix).length + 12)
            hvalid (by
              simp only [unarySourcePairWord, List.append_assoc, List.cons_append, List.nil_append,
                  List.length_append,
                  List.length_replicate, List.length_cons, add_le_add_iff_right]
              omega)
          simpa only [FinTM2.step, Fin.isValue, sourcePairPrefixOutput,
              BinaryEncoding.readUnaryPrefix_replicate,
              unarySourcePairWord, List.length_append, List.length_replicate, List.length_cons,
                  List.append_assoc,
              List.cons_append, List.nil_append] using hbounded

/-- GapCVP reduction support. -/
noncomputable def actualSourcePairPrefixComputable :
    BitTM
      sourcePairPrefixOutput where
  tm := actualSourcePairPrefixMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 6 * Polynomial.X + 12
  outputsFun input := {
    steps := (sourcePairPrefix_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, actualSourcePairPrefixMachine_init,
              Option.map_some] using
          (sourcePairPrefix_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (sourcePairPrefix_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq, Polynomial.eval_add,
          Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X, ge_iff_le] using hsteps
  }

end CNFSourcePairPrefixWorkerTotalCert

namespace SourceLatticeFormulaPreservation

open Turing GapCVP.FormulaTuringTM GapCVP.FormulaTotalCert GapCVP.FormulaSemanticCert

private def formulaPreservationCanonicalStack (stack : Fin 6) : Fin 8 :=
  ⟨stack.val, by omega⟩

private def formulaPreservationCanonicalLabel (phase : Fin 17) : Fin 20 :=
  ⟨phase.val, by omega⟩

private def liftFormulaPreservationCanonicalStmt :
    Turing.TM2.Stmt (fun _ : Fin 6 => Bool)
      (Fin 17) (Option Bool) →
    Turing.TM2.Stmt (fun _ : Fin 8 => Bool)
      (Fin 20) (Option Bool)
  | .push stack push continuation =>
      .push (formulaPreservationCanonicalStack stack) push
        (liftFormulaPreservationCanonicalStmt continuation)
  | .peek stack peek continuation =>
      .peek (formulaPreservationCanonicalStack stack) peek
        (liftFormulaPreservationCanonicalStmt continuation)
  | .pop stack pop continuation =>
      .pop (formulaPreservationCanonicalStack stack) pop
        (liftFormulaPreservationCanonicalStmt continuation)
  | .load load continuation =>
      .load load (liftFormulaPreservationCanonicalStmt continuation)
  | .branch branch yes no =>
      .branch branch
        (liftFormulaPreservationCanonicalStmt yes)
        (liftFormulaPreservationCanonicalStmt no)
  | .goto target =>
      .goto (fun state =>
        formulaPreservationCanonicalLabel (target state))
  | .halt =>
      .goto (fun _ => (19 : Fin 20))

private def formulaPreservationPeek (stack : Fin 8)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 20) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 20) (Option Bool) :=
  .peek stack (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome) present absent)

private def formulaPreservationPop (stack : Fin 8)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 20) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 20) (Option Bool) :=
  .pop stack (fun state _ => state) continuation

private def formulaPreservationPush (stack : Fin 8)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 20) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 20) (Option Bool) :=
  .push stack (fun state => state.getD false) continuation

private def formulaPreservationGoto (phase : Fin 20) :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 20) (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => phase))

private def formulaPreservationCopyStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 20) (Option Bool) :=
  formulaPreservationPeek 0
    (formulaPreservationPop 0
      (formulaPreservationPush 6
        (formulaPreservationPush 7
          (formulaPreservationGoto 17))))
    (formulaPreservationGoto 18)

private def formulaPreservationRestoreStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 20) (Option Bool) :=
  formulaPreservationPeek 7
    (formulaPreservationPop 7
      (formulaPreservationPush 0
        (formulaPreservationGoto 18)))
    (formulaPreservationGoto 0)

private def formulaPreservationOutputStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 8 => Bool) (Fin 20) (Option Bool) :=
  formulaPreservationPeek 6
    (formulaPreservationPop 6
      (formulaPreservationPush 5
        (formulaPreservationGoto 19)))
    .halt

private abbrev formulaPreservationMachine : Turing.FinTM2 where
  K := Fin 8
  k₀ := 0
  k₁ := 5
  Γ _ := Bool
  Λ := Fin 20
  main := 17
  σ := Option Bool
  initialState := none
  m phase :=
    if h : phase.val < 17 then
      liftFormulaPreservationCanonicalStmt
        (canonicalFormulaMachine.m ⟨phase.val, h⟩)
    else if phase = (17 : Fin 20) then
      formulaPreservationCopyStatement
    else if phase = (18 : Fin 20) then
      formulaPreservationRestoreStatement
    else
      formulaPreservationOutputStatement

private def formulaPreservationConfiguration (phase : Fin 20)
    (input counter field binary borrow output backup scratch : List Bool) :
    formulaPreservationMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, counter, field, binary,
    borrow, output, backup, scratch]

private theorem formulaPreservationMachine_init (input : List Bool) :
    Turing.initList formulaPreservationMachine input =
      formulaPreservationConfiguration 17
        input [] [] [] [] [] [] [] := by
  simp only [formulaPreservationMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq,
      dite_eq_ite,
    formulaPreservationConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `formulaPreservationStepTac` machine-step simplifier. -/
macro "formulaPreservationStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [formulaPreservationMachine,
          formulaPreservationConfiguration,
          formulaPreservationCopyStatement,
          formulaPreservationRestoreStatement,
          formulaPreservationOutputStatement,
          formulaPreservationPeek,
          formulaPreservationPop, formulaPreservationPush,
          formulaPreservationGoto, Turing.haltList,
          Turing.FinTM2.step, Turing.TM2.step,
          Turing.TM2.stepAux] <;>
         try { congr 2; funext stack; fin_cases stack <;>
           (first | rfl | simp [Function.update]) } <;>
         try rfl)))

private theorem formulaPreservation_copy_step (bit : Bool)
    (input counter field binary borrow output backup scratch : List Bool) :
    formulaPreservationMachine.step
      (formulaPreservationConfiguration 17
        (bit :: input) counter field binary borrow output backup scratch) =
      some (formulaPreservationConfiguration 17
        input counter field binary borrow output
        (bit :: backup) (bit :: scratch)) := by
  cases bit <;> formulaPreservationStepTac

private theorem formulaPreservation_copy_finish
    (counter field binary borrow output backup scratch : List Bool) :
    formulaPreservationMachine.step
      (formulaPreservationConfiguration 17
        [] counter field binary borrow output backup scratch) =
      some (formulaPreservationConfiguration 18
        [] counter field binary borrow output backup scratch) := by
  formulaPreservationStepTac

private theorem formulaPreservation_restore_step (bit : Bool)
    (input counter field binary borrow output backup scratch : List Bool) :
    formulaPreservationMachine.step
      (formulaPreservationConfiguration 18
        input counter field binary borrow output backup
        (bit :: scratch)) =
      some (formulaPreservationConfiguration 18
        (bit :: input) counter field binary borrow output backup scratch) := by
  cases bit <;> formulaPreservationStepTac

private theorem formulaPreservation_restore_finish
    (input counter field binary borrow output backup : List Bool) :
    formulaPreservationMachine.step
      (formulaPreservationConfiguration 18
        input counter field binary borrow output backup []) =
      some (formulaPreservationConfiguration 0
        input counter field binary borrow output backup []) := by
  formulaPreservationStepTac

private theorem formulaPreservation_output_step (bit : Bool)
    (input counter field binary borrow output backup scratch : List Bool) :
    formulaPreservationMachine.step
      (formulaPreservationConfiguration 19
        input counter field binary borrow output
        (bit :: backup) scratch) =
      some (formulaPreservationConfiguration 19
        input counter field binary borrow (bit :: output)
        backup scratch) := by
  cases bit <;> formulaPreservationStepTac

private theorem formulaPreservation_output_finish (output : List Bool) :
    formulaPreservationMachine.step
      (formulaPreservationConfiguration 19
        [] [] [] [] [] output [] []) =
      some (Turing.haltList formulaPreservationMachine output) := by
  formulaPreservationStepTac

private def formulaPreservationCanonicalStacks
    (source : (stack : Fin 6) → List Bool)
    (backup scratch : List Bool) :
    (stack : Fin 8) → List Bool :=
  ![source 0, source 1, source 2, source 3,
    source 4, source 5, backup, scratch]

@[simp] private theorem formulaPreservationCanonicalStacks_apply
    (source : (stack : Fin 6) → List Bool)
    (backup scratch : List Bool) (stack : Fin 6) :
    formulaPreservationCanonicalStacks source backup scratch
        (formulaPreservationCanonicalStack stack) = source stack := by
  fin_cases stack <;>
    simp [formulaPreservationCanonicalStacks,
      formulaPreservationCanonicalStack]

private theorem formulaPreservationCanonicalStacks_update
    (source : (stack : Fin 6) → List Bool)
    (backup scratch : List Bool) (stack : Fin 6)
    (value : List Bool) :
    formulaPreservationCanonicalStacks
        (Function.update source stack value)
        backup scratch =
      Function.update
        (formulaPreservationCanonicalStacks source backup scratch)
        (formulaPreservationCanonicalStack stack) value := by
  funext target
  fin_cases stack <;> fin_cases target <;>
    simp [formulaPreservationCanonicalStacks,
      formulaPreservationCanonicalStack, Function.update]

private def formulaPreservationCanonicalConfiguration
    (source : canonicalFormulaMachine.Cfg)
    (backup scratch : List Bool) :
    formulaPreservationMachine.Cfg where
  l := match source.l with
    | some phase => some (formulaPreservationCanonicalLabel phase)
    | none => some 19
  var := source.var
  stk := formulaPreservationCanonicalStacks
    source.stk backup scratch

private theorem formulaPreservationCanonicalProgram (phase : Fin 17) :
    formulaPreservationMachine.m
        (formulaPreservationCanonicalLabel phase) =
      liftFormulaPreservationCanonicalStmt
        (canonicalFormulaMachine.m phase) := by
  simp only [formulaPreservationMachine, Fin.isValue, formulaPreservationCanonicalLabel, Fin.is_lt,
    ↓reduceDIte, Fin.eta]
  rfl

private theorem liftFormulaPreservationCanonicalStmt_stepAux
    (statement : Turing.TM2.Stmt
      (fun _ : Fin 6 => Bool) (Fin 17) (Option Bool))
    (state : Option Bool)
    (source : (stack : Fin 6) → List Bool)
    (backup scratch : List Bool) :
    Turing.TM2.stepAux
        (liftFormulaPreservationCanonicalStmt statement)
        state
        (formulaPreservationCanonicalStacks
          source backup scratch) =
      formulaPreservationCanonicalConfiguration
        (Turing.TM2.stepAux statement state source)
        backup scratch := by
  induction statement generalizing state source with
  | push stack push continuation ih =>
      simp only [liftFormulaPreservationCanonicalStmt,
        Turing.TM2.stepAux,
        formulaPreservationCanonicalStacks_apply]
      rw [← formulaPreservationCanonicalStacks_update]
      exact ih state (Function.update source stack
        (push state :: source stack))
  | peek stack peek continuation ih =>
      simpa only [liftFormulaPreservationCanonicalStmt,
        Turing.TM2.stepAux,
        formulaPreservationCanonicalStacks_apply] using
        ih (peek state (source stack).head?) source
  | pop stack pop continuation ih =>
      simp only [liftFormulaPreservationCanonicalStmt,
        Turing.TM2.stepAux,
        formulaPreservationCanonicalStacks_apply]
      rw [← formulaPreservationCanonicalStacks_update]
      exact ih (pop state (source stack).head?)
        (Function.update source stack (source stack).tail)
  | load load continuation ih =>
      simpa only [liftFormulaPreservationCanonicalStmt,
        Turing.TM2.stepAux] using
        ih (load state) source
  | branch branch yes no ihyes ihno =>
      cases hbranch : branch state with
      | false =>
          simpa only [liftFormulaPreservationCanonicalStmt, TM2.stepAux, hbranch, Bool.cond_false]
              using ihno state source
      | true =>
          simpa only [liftFormulaPreservationCanonicalStmt, TM2.stepAux, hbranch, Bool.cond_true]
              using ihyes state source
  | goto target =>
      rfl
  | halt =>
      rfl

private theorem formulaPreservationCanonicalConfiguration_step
    (backup scratch : List Bool)
    (source target : canonicalFormulaMachine.Cfg)
    (hstep : canonicalFormulaMachine.step source = some target) :
    formulaPreservationMachine.step
      (formulaPreservationCanonicalConfiguration
        source backup scratch) =
      some (formulaPreservationCanonicalConfiguration
        target backup scratch) := by
  rcases source with ⟨phase, state, sourceStacks⟩
  cases phase with
  | none =>
      simp only [FinTM2.step, TM2.step, reduceCtorEq] at hstep
  | some phase =>
      change some (Turing.TM2.stepAux
        (canonicalFormulaMachine.m phase)
        state sourceStacks) = some target at hstep
      have htarget := Option.some.inj hstep
      subst target
      change some (Turing.TM2.stepAux
        (formulaPreservationMachine.m
          (formulaPreservationCanonicalLabel phase))
        state (formulaPreservationCanonicalStacks
          sourceStacks backup scratch)) =
        some (formulaPreservationCanonicalConfiguration
          (Turing.TM2.stepAux
            (canonicalFormulaMachine.m phase)
            state sourceStacks)
          backup scratch)
      rw [formulaPreservationCanonicalProgram,
        liftFormulaPreservationCanonicalStmt_stepAux]
      rfl

private noncomputable def formulaPreservationCanonical_evalsToInTime
    (backup scratch : List Bool)
    {source target : canonicalFormulaMachine.Cfg}
    {budget : ℕ}
    (trace : EvalsToInTime
      canonicalFormulaMachine.step
      source (some target) budget) :
    EvalsToInTime formulaPreservationMachine.step
      (formulaPreservationCanonicalConfiguration
        source backup scratch)
      (some (formulaPreservationCanonicalConfiguration
        target backup scratch)) budget :=
  GapCVP.TMComposition.evalsToInTimeMapOfStep
    canonicalFormulaMachine.step
    formulaPreservationMachine.step
    (fun state => formulaPreservationCanonicalConfiguration
      state backup scratch)
    (formulaPreservationCanonicalConfiguration_step
      backup scratch)
    trace

private def formulaPreservation_copyTrace
    (input counter field binary borrow output backup scratch : List Bool) :
    EvalsToInTime formulaPreservationMachine.step (formulaPreservationConfiguration 17
        input counter field binary borrow output backup scratch)
      (some (formulaPreservationConfiguration 18
        [] counter field binary borrow output
        (input.reverse ++ backup) (input.reverse ++ scratch)))
      (input.length + 1) := by
  induction input generalizing backup scratch with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, Fin.mk_eq_zero, Fin.val_eq_zero_iff, Fin.mk_eq_one,
          List.reverse_nil,
          List.nil_append, List.length_nil, zero_add] using
          oneStep _ _ (formulaPreservation_copy_finish counter field binary borrow output backup
              scratch)
  | cons bit rest ih =>
      have hfirst := oneStep _ _ (formulaPreservation_copy_step bit rest
          counter field binary borrow output backup scratch)
      have hrest := ih (bit :: backup) (bit :: scratch)
      have hfull := EvalsToInTime.trans formulaPreservationMachine.step 1 (rest.length + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, Fin.mk_eq_zero, Fin.val_eq_zero_iff, Fin.mk_eq_one,
          List.reverse_cons,
          List.append_assoc, List.cons_append, List.nil_append, List.length_cons, Nat.add_assoc,
              Nat.reduceAdd] using hfull

private def formulaPreservation_restoreTrace
    (scratch input counter field binary borrow output backup : List Bool) :
    EvalsToInTime formulaPreservationMachine.step (formulaPreservationConfiguration 18
        input counter field binary borrow output backup scratch)
      (some (formulaPreservationConfiguration 0
        (scratch.reverse ++ input) counter field binary
        borrow output backup []))
      (scratch.length + 1) := by
  induction scratch generalizing input with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, Fin.mk_eq_zero, Fin.val_eq_zero_iff, Fin.mk_eq_one,
          List.reverse_nil,
          List.nil_append, List.length_nil, zero_add] using
          oneStep _ _ (formulaPreservation_restore_finish input counter field binary borrow output
              backup)
  | cons bit rest ih =>
      have hfirst := oneStep _ _ (formulaPreservation_restore_step bit
          input counter field binary borrow output backup rest)
      have hrest := ih (bit :: input)
      have hfull := EvalsToInTime.trans formulaPreservationMachine.step 1 (rest.length + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, Fin.mk_eq_zero, Fin.val_eq_zero_iff, Fin.mk_eq_one,
          List.reverse_cons,
          List.append_assoc, List.cons_append, List.nil_append, List.length_cons, Nat.add_assoc,
              Nat.reduceAdd] using hfull

private theorem formulaPreservationCanonical_initial
    (input backup scratch : List Bool) :
    formulaPreservationCanonicalConfiguration
        (canonicalConfiguration 0 input [] [] [] [] [])
        backup scratch =
      formulaPreservationConfiguration 0
        input [] [] [] [] [] backup scratch := by
  simp only [formulaPreservationCanonicalConfiguration, canonicalConfiguration, Fin.isValue,
      formulaPreservationCanonicalLabel, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.zero_eta,
      formulaPreservationCanonicalStacks, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val,
      formulaPreservationConfiguration]
  rfl

private theorem formulaPreservationCanonical_halt
    (output backup scratch : List Bool) :
    formulaPreservationCanonicalConfiguration
        (Turing.haltList canonicalFormulaMachine output)
        backup scratch =
      formulaPreservationConfiguration 19
        [] [] [] [] [] output backup scratch := by
  simp only [formulaPreservationCanonicalConfiguration, canonicalFormulaMachine, Fin.isValue,
      haltList,
      eq_mpr_eq_cast, cast_eq, dite_eq_ite, formulaPreservationCanonicalStacks, Fin.reduceEq,
          ↓reduceIte,
      formulaPreservationConfiguration]
  rfl

private def formulaPreservation_outputTrace
    (backup output : List Bool) :
    EvalsToInTime formulaPreservationMachine.step (formulaPreservationConfiguration 19
        [] [] [] [] [] output backup [])
      (some (Turing.haltList formulaPreservationMachine
        (backup.reverse ++ output)))
      (backup.length + 1) := by
  induction backup generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, Fin.mk_eq_zero, Fin.val_eq_zero_iff, Fin.mk_eq_one,
          List.reverse_nil,
          List.nil_append, List.length_nil, zero_add] using oneStep _ _
              (formulaPreservation_output_finish output)
  | cons bit rest ih =>
      have hfirst := oneStep _ _ (formulaPreservation_output_step bit
          [] [] [] [] [] output rest [])
      have hrest := ih (bit :: output)
      have hfull := EvalsToInTime.trans formulaPreservationMachine.step 1 (rest.length + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, Fin.mk_eq_zero, Fin.val_eq_zero_iff, Fin.mk_eq_one,
          List.reverse_cons,
          List.append_assoc, List.cons_append, List.nil_append, List.length_cons, Nat.add_assoc,
              Nat.reduceAdd] using hfull

/-- Internal support shared across GapCVP continuation modules. -/
def formulaPreservedOutput (input : List Bool) : List Bool :=
  input ++ canonicalMachineOutput input

private def formulaPreservationInputBudget (input : List Bool) : ℕ :=
  canonicalInputBudget input + 4 * input.length + 4

private noncomputable def formulaPreservation_totalTrace (input : List Bool) :
    EvalsToInTime formulaPreservationMachine.step (formulaPreservationConfiguration 17
        input [] [] [] [] [] [] [])
      (some (Turing.haltList formulaPreservationMachine
        (formulaPreservedOutput input)))
      (formulaPreservationInputBudget input) := by
  have hcopy := formulaPreservation_copyTrace
    input [] [] [] [] [] [] []
  simp only [List.append_nil] at hcopy
  have hrestore := formulaPreservation_restoreTrace
    input.reverse [] [] [] [] [] [] input.reverse
  simp only [List.reverse_reverse, List.append_nil,
    List.length_reverse] at hrestore
  have hcanonical := formulaPreservationCanonical_evalsToInTime
    input.reverse [] (canonicalTotalTrace input)
  rw [formulaPreservationCanonical_initial,
    formulaPreservationCanonical_halt] at hcanonical
  have houtput := formulaPreservation_outputTrace
    input.reverse (canonicalMachineOutput input)
  simp only [List.reverse_reverse, List.length_reverse] at houtput
  have hfirst := EvalsToInTime.trans formulaPreservationMachine.step _ _ _ _ _ hcopy hrestore
  have hsecond := EvalsToInTime.trans formulaPreservationMachine.step _ _ _ _ _ hfirst hcanonical
  have hfull := EvalsToInTime.trans formulaPreservationMachine.step _ _ _ _ _ hsecond houtput
  apply rebound hfull
  simp only [formulaPreservationInputBudget]
  omega

private noncomputable def formulaPreservationComputable :
    BitTM
      formulaPreservedOutput where
  tm := formulaPreservationMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time :=
    64 * (Polynomial.X + 1) * (Polynomial.X + 1) +
      64 + 4 * Polynomial.X + 4
  outputsFun input := {
    steps := (formulaPreservation_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Fin.mk_eq_zero,
          Fin.val_eq_zero_iff, Fin.mk_eq_one,
          Equiv.invFun_as_coe, Equiv.refl_symm, Equiv.coe_refl, bitEncoding, id_eq,
              List.map_id_fun,
          formulaPreservationMachine_init, Option.map_some] using (formulaPreservation_totalTrace
              input).evals_in_steps
    steps_le_m := by
      have hsteps := (formulaPreservation_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, Fin.mk_eq_zero, Fin.val_eq_zero_iff, Fin.mk_eq_one,
          formulaPreservationInputBudget, canonicalInputBudget, bitEncoding, id_eq,
              Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one, ge_iff_le] using hsteps
  }

/-- Internal support shared across GapCVP continuation modules. -/
theorem formulaPreservedOutput_eq_expected (input : List Bool) :
    formulaPreservedOutput input =
      input ++ canonicalFormulaExpected input := by
  simp only [formulaPreservedOutput, canonicalMachineOutput_eq_expected]

end SourceLatticeFormulaPreservation

namespace SourceLatticeDependentSectionComputation

open Turing GapCVP.SourceLatticeFormulaPreservation

private def sourceMarkerPeek (stack : Fin 3)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  .peek stack (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome) present absent)

private def sourceMarkerPop (stack : Fin 3)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  .pop stack (fun state _ => state) continuation

private def sourceMarkerPush (stack : Fin 3)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  .push stack (fun state => state.getD false) continuation

private def sourceMarkerGoto (phase : Fin 4) :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => phase))

private abbrev sourceMarkerRotationMachine : Turing.FinTM2 where
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
      sourceMarkerPeek 0
        (sourceMarkerPop 0
          (sourceMarkerPush 1 (sourceMarkerGoto 0)))
        (sourceMarkerGoto 1)
    else if phase = (1 : Fin 4) then
      sourceMarkerPeek 1
        (sourceMarkerPop 1
          (sourceMarkerPush 0 (sourceMarkerGoto 2)))
        (.push 0 (fun _ => false) (sourceMarkerGoto 2))
    else if phase = (2 : Fin 4) then
      sourceMarkerPeek 1
        (sourceMarkerPop 1
          (sourceMarkerPush 2 (sourceMarkerGoto 2)))
        (sourceMarkerGoto 3)
    else
      sourceMarkerPeek 0
        (sourceMarkerPop 0
          (sourceMarkerPush 2 (.load (fun _ => none) .halt)))
        .halt

private def sourceMarkerConfiguration (phase : Fin 4)
    (input scratch output : List Bool) :
    sourceMarkerRotationMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, scratch, output]

private theorem sourceMarkerRotationMachine_init (input : List Bool) :
    Turing.initList sourceMarkerRotationMachine input =
      sourceMarkerConfiguration 0 input [] [] := by
  simp only [sourceMarkerRotationMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq,
      dite_eq_ite,
      sourceMarkerConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `sourceMarkerStepTac` machine-step simplifier. -/
macro "sourceMarkerStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [sourceMarkerRotationMachine,
          sourceMarkerConfiguration, sourceMarkerPeek,
          sourceMarkerPop, sourceMarkerPush, sourceMarkerGoto,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
         try { congr 2; funext stack; fin_cases stack <;>
           (first | rfl | simp [Function.update]) } <;>
         try rfl)))

private theorem sourceMarker_copy_step (bit : Bool)
    (input scratch output : List Bool) :
    sourceMarkerRotationMachine.step
      (sourceMarkerConfiguration 0
        (bit :: input) scratch output) =
      some (sourceMarkerConfiguration 0
        input (bit :: scratch) output) := by
  cases bit <;> sourceMarkerStepTac

private theorem sourceMarker_copy_finish
    (scratch output : List Bool) :
    sourceMarkerRotationMachine.step
      (sourceMarkerConfiguration 0 [] scratch output) =
      some (sourceMarkerConfiguration 1 [] scratch output) := by
  sourceMarkerStepTac

private theorem sourceMarker_extract_step (bit : Bool)
    (scratch output : List Bool) :
    sourceMarkerRotationMachine.step
      (sourceMarkerConfiguration 1 [] (bit :: scratch) output) =
      some (sourceMarkerConfiguration 2 [bit] scratch output) := by
  cases bit <;> sourceMarkerStepTac

private theorem sourceMarker_extract_missing (output : List Bool) :
    sourceMarkerRotationMachine.step
      (sourceMarkerConfiguration 1 [] [] output) =
      some (sourceMarkerConfiguration 2 [false] [] output) := by
  sourceMarkerStepTac

private theorem sourceMarker_restore_step (bit : Bool)
    (input scratch output : List Bool) :
    sourceMarkerRotationMachine.step
      (sourceMarkerConfiguration 2
        input (bit :: scratch) output) =
      some (sourceMarkerConfiguration 2
        input scratch (bit :: output)) := by
  cases bit <;> sourceMarkerStepTac

private theorem sourceMarker_restore_finish
    (input output : List Bool) :
    sourceMarkerRotationMachine.step
      (sourceMarkerConfiguration 2 input [] output) =
      some (sourceMarkerConfiguration 3 input [] output) := by
  sourceMarkerStepTac

private theorem sourceMarker_output_finish (bit : Bool)
    (output : List Bool) :
    sourceMarkerRotationMachine.step
      (sourceMarkerConfiguration 3 [bit] [] output) =
      some (Turing.haltList sourceMarkerRotationMachine
        (bit :: output)) := by
  cases bit <;> sourceMarkerStepTac

private def sourceMarker_copyTrace
    (input scratch output : List Bool) :
    EvalsToInTime sourceMarkerRotationMachine.step
      (sourceMarkerConfiguration 0 input scratch output)
      (some (sourceMarkerConfiguration 1 []
        (input.reverse ++ scratch) output))
      (input.length + 1) := by
  induction input generalizing scratch with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (sourceMarker_copy_finish scratch output)
  | cons bit rest ih =>
      have hfirst := oneStep _ _ (sourceMarker_copy_step bit rest scratch output)
      have hrest := ih (bit :: scratch)
      have hfull := EvalsToInTime.trans sourceMarkerRotationMachine.step 1 (rest.length + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hfull

private def sourceMarker_restoreTrace
    (scratch input output : List Bool) :
    EvalsToInTime sourceMarkerRotationMachine.step
      (sourceMarkerConfiguration 2 input scratch output)
      (some (sourceMarkerConfiguration 3 input []
        (scratch.reverse ++ output)))
      (scratch.length + 1) := by
  induction scratch generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (sourceMarker_restore_finish input output)
  | cons bit rest ih =>
      have hfirst := oneStep _ _ (sourceMarker_restore_step bit input rest output)
      have hrest := ih (bit :: output)
      have hfull := EvalsToInTime.trans sourceMarkerRotationMachine.step 1 (rest.length + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hfull

/-- Internal support shared across GapCVP continuation modules. -/
def sourceMarkerRotatedOutput (input : List Bool) : List Bool :=
  match input.reverse with
  | [] => [false]
  | marker :: formula => marker :: formula.reverse

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem sourceMarkerRotatedOutput_append_marker
    (input : List Bool) (marker : Bool) :
    sourceMarkerRotatedOutput (input ++ [marker]) =
      marker :: input := by
  simp only [sourceMarkerRotatedOutput, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.reverse_reverse]

private def sourceMarker_totalTrace (input : List Bool) :
    EvalsToInTime sourceMarkerRotationMachine.step (sourceMarkerConfiguration 0 input [] [])
      (some (Turing.haltList sourceMarkerRotationMachine
        (sourceMarkerRotatedOutput input)))
      (2 * input.length + 5) := by
  have hcopy := sourceMarker_copyTrace input [] []
  simp only [List.append_nil] at hcopy
  cases input with
  | nil =>
      have hextract := oneStep _ _ (sourceMarker_extract_missing [])
      have hrestore := sourceMarker_restoreTrace [] [false] []
      have hfinish := oneStep _ _ (sourceMarker_output_finish false [])
      have hfirst := EvalsToInTime.trans sourceMarkerRotationMachine.step _ _ _ _ _ hcopy hextract
      have hsecond := EvalsToInTime.trans sourceMarkerRotationMachine.step _ _ _ _ _ hfirst
          hrestore
      have hfull := EvalsToInTime.trans sourceMarkerRotationMachine.step _ _ _ _ _ hsecond hfinish
      have hbounded := rebound (newBudget := 2 * ([] : List Bool).length + 5)
        hfull (by simp only [List.length_nil, zero_add, Nat.reduceAdd, mul_zero, Nat.reduceLeDiff])
      simpa only [FinTM2.step, Fin.isValue, sourceMarkerRotatedOutput, List.reverse_nil,
          List.length_nil, mul_zero,
          zero_add] using hbounded
  | cons first rest =>
      cases hreverse : (first :: rest).reverse with
      | nil =>
          have hnonempty :
              0 < (first :: rest).reverse.length := by simp only [List.reverse_cons,
                  List.length_append, List.length_reverse, List.length_cons, List.length_nil,
                                                           zero_add, lt_add_iff_pos_left,
                                                               Order.lt_add_one_iff, zero_le]
          rw [hreverse] at hnonempty
          simp only [List.length_nil, lt_self_iff_false] at hnonempty
      | cons marker formula =>
          rw [hreverse] at hcopy
          have hextract := oneStep _ _ (sourceMarker_extract_step marker formula [])
          have hrestore := sourceMarker_restoreTrace
            formula [marker] []
          simp only [List.append_nil] at hrestore
          have hfinish := oneStep _ _ (sourceMarker_output_finish marker formula.reverse)
          have hfirst := EvalsToInTime.trans
            sourceMarkerRotationMachine.step _ _ _ _ _ hcopy hextract
          have hsecond := EvalsToInTime.trans
            sourceMarkerRotationMachine.step _ _ _ _ _ hfirst hrestore
          have hfull := EvalsToInTime.trans
            sourceMarkerRotationMachine.step _ _ _ _ _ hsecond hfinish
          have hlength :
              formula.length + 1 = (first :: rest).length := by
            have h := congrArg List.length hreverse
            simpa only [List.length_reverse, List.length_cons] using
              h.symm
          have hbounded := rebound (newBudget := 2 * (first :: rest).length + 5)
            hfull (by
              simp only [List.length_cons] at hlength ⊢
              omega)
          simpa only [FinTM2.step, Fin.isValue, sourceMarkerRotatedOutput, hreverse,
              List.length_cons] using hbounded

private noncomputable def sourceMarkerRotationComputable :
    BitTM
      sourceMarkerRotatedOutput where
  tm := sourceMarkerRotationMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 5
  outputsFun input := {
    steps := (sourceMarker_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, sourceMarkerRotationMachine_init,
              Option.map_some] using
          (sourceMarker_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (sourceMarker_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq, Polynomial.eval_add,
          Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X, ge_iff_le] using hsteps
  }

/-- Internal support shared across GapCVP continuation modules. -/
def validatedPreservedFormulaOutput : List Bool → List Bool :=
  sourceMarkerRotatedOutput ∘ formulaPreservedOutput

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def validatedPreservedFormulaComputable :
    BitTM
      validatedPreservedFormulaOutput :=
  GapCVP.TMComposition.computableInPolyTime
    formulaPreservationComputable sourceMarkerRotationComputable

end SourceLatticeDependentSectionComputation

namespace SourceLatticeNormalizedSectionSynthesis

open Turing

/-- Internal support shared across GapCVP continuation modules. -/
def normalizedRadiusPeek (stack : Fin 5)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  .peek stack (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome) present absent)

/-- Internal support shared across GapCVP continuation modules. -/
def normalizedRadiusPop (stack : Fin 5)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  .pop stack (fun _ _ => none) continuation

/-- Internal support shared across GapCVP continuation modules. -/
def normalizedRadiusPush (stack : Fin 5)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  .push stack (fun _ => true) continuation

/-- Internal support shared across GapCVP continuation modules. -/
def normalizedRadiusGoto (phase : Fin 7) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => phase))

private def normalizedRadiusFailureCheck (stack : Fin 5)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  normalizedRadiusPeek stack
    (normalizedRadiusPop stack (normalizedRadiusGoto 6))
    continuation

end SourceLatticeNormalizedSectionSynthesis

namespace SourceLatticeStructuralRadiusNumerator

open Turing

private def radiusMarkerTailPeek (stack : Fin 3)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool) :=
  .peek stack (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome) present absent)

private def radiusMarkerTailPop (stack : Fin 3)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool) :=
  .pop stack (fun symbol _ => symbol) continuation

private def radiusMarkerTailPush (stack : Fin 3)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool) :=
  .push stack (fun symbol => symbol.getD false) continuation

private def radiusMarkerTailGoto (phase : Fin 3) :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => phase))

private def radiusMarkerTailDropStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool) :=
  radiusMarkerTailPeek 0
    (radiusMarkerTailPop 0 (radiusMarkerTailGoto 1))
    .halt

private def radiusMarkerTailCopyStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool) :=
  radiusMarkerTailPeek 0
    (radiusMarkerTailPop 0
      (radiusMarkerTailPush 1 (radiusMarkerTailGoto 1)))
    (radiusMarkerTailGoto 2)

private def radiusMarkerTailOutputStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool) :=
  radiusMarkerTailPeek 1
    (radiusMarkerTailPop 1
      (radiusMarkerTailPush 2 (radiusMarkerTailGoto 2)))
    .halt

private abbrev radiusMarkerTailMachine : Turing.FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 3) then
      radiusMarkerTailDropStatement
    else if phase = (1 : Fin 3) then
      radiusMarkerTailCopyStatement
    else
      radiusMarkerTailOutputStatement

private def radiusMarkerTailConfiguration (phase : Fin 3)
    (input scratch output : List Bool) : radiusMarkerTailMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, scratch, output]

private theorem radiusMarkerTailMachine_init (input : List Bool) :
    Turing.initList radiusMarkerTailMachine input =
      radiusMarkerTailConfiguration 0 input [] [] := by
  simp only [radiusMarkerTailMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq, dite_eq_ite,
      radiusMarkerTailConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `radiusMarkerTailStepTac` machine-step simplifier. -/
macro "radiusMarkerTailStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [radiusMarkerTailMachine, radiusMarkerTailConfiguration,
          radiusMarkerTailPeek, radiusMarkerTailPop,
          radiusMarkerTailPush, radiusMarkerTailGoto,
          radiusMarkerTailDropStatement,
          radiusMarkerTailCopyStatement,
          radiusMarkerTailOutputStatement,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

private theorem radiusMarkerTail_empty_finish :
    radiusMarkerTailMachine.step
      (radiusMarkerTailConfiguration 0 [] [] []) =
      some (Turing.haltList radiusMarkerTailMachine []) := by
  radiusMarkerTailStepTac

private theorem radiusMarkerTail_drop_step (bit : Bool)
    (input scratch output : List Bool) :
    radiusMarkerTailMachine.step
      (radiusMarkerTailConfiguration 0
        (bit :: input) scratch output) =
      some (radiusMarkerTailConfiguration 1
        input scratch output) := by
  cases bit <;> radiusMarkerTailStepTac

private theorem radiusMarkerTail_copy_step (bit : Bool)
    (input scratch output : List Bool) :
    radiusMarkerTailMachine.step
      (radiusMarkerTailConfiguration 1
        (bit :: input) scratch output) =
      some (radiusMarkerTailConfiguration 1
        input (bit :: scratch) output) := by
  cases bit <;> radiusMarkerTailStepTac

private theorem radiusMarkerTail_copy_finish
    (scratch output : List Bool) :
    radiusMarkerTailMachine.step
      (radiusMarkerTailConfiguration 1 [] scratch output) =
      some (radiusMarkerTailConfiguration 2 [] scratch output) := by
  radiusMarkerTailStepTac

private theorem radiusMarkerTail_output_step (bit : Bool)
    (scratch output : List Bool) :
    radiusMarkerTailMachine.step
      (radiusMarkerTailConfiguration 2
        [] (bit :: scratch) output) =
      some (radiusMarkerTailConfiguration 2
        [] scratch (bit :: output)) := by
  cases bit <;> radiusMarkerTailStepTac

private theorem radiusMarkerTail_output_finish (output : List Bool) :
    radiusMarkerTailMachine.step
      (radiusMarkerTailConfiguration 2 [] [] output) =
      some (Turing.haltList radiusMarkerTailMachine output) := by
  radiusMarkerTailStepTac

private def radiusMarkerTail_copyTrace
    (input scratch output : List Bool) :
    EvalsToInTime radiusMarkerTailMachine.step
      (radiusMarkerTailConfiguration 1 input scratch output)
      (some (radiusMarkerTailConfiguration 2 []
        (input.reverse ++ scratch) output))
      (input.length + 1) := by
  induction input generalizing scratch with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (radiusMarkerTail_copy_finish scratch output)
  | cons bit input ih =>
      have hfirst := oneStep _ _ (radiusMarkerTail_copy_step bit input scratch output)
      have hrest := ih (bit :: scratch)
      have hfull := EvalsToInTime.trans radiusMarkerTailMachine.step _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hfull

private def radiusMarkerTail_outputTrace (scratch output : List Bool) :
    EvalsToInTime radiusMarkerTailMachine.step (radiusMarkerTailConfiguration 2 [] scratch output)
      (some (Turing.haltList radiusMarkerTailMachine
        (scratch.reverse ++ output)))
      (scratch.length + 1) := by
  induction scratch generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (radiusMarkerTail_output_finish output)
  | cons bit scratch ih =>
      have hfirst := oneStep _ _ (radiusMarkerTail_output_step bit scratch output)
      have hrest := ih (bit :: output)
      have hfull := EvalsToInTime.trans radiusMarkerTailMachine.step _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hfull

private def radiusMarkerTail_totalTrace (input : List Bool) :
    EvalsToInTime radiusMarkerTailMachine.step (radiusMarkerTailConfiguration 0 input [] [])
      (some (Turing.haltList radiusMarkerTailMachine input.tail))
      (2 * input.length + 3) := by
  cases input with
  | nil =>
      exact rebound (oneStep _ _ radiusMarkerTail_empty_finish)
        (by simp only [List.length_nil, mul_zero, zero_add, Nat.one_le_ofNat])
  | cons bit input =>
      have hdrop := oneStep _ _ (radiusMarkerTail_drop_step bit input [] [])
      have hcopy := radiusMarkerTail_copyTrace input [] []
      simp only [List.append_nil] at hcopy
      have houtput := radiusMarkerTail_outputTrace input.reverse []
      simp only [List.reverse_reverse, List.append_nil] at houtput
      have hfirst := EvalsToInTime.trans radiusMarkerTailMachine.step _ _ _ _ _ hdrop hcopy
      have hfull := EvalsToInTime.trans radiusMarkerTailMachine.step _ _ _ _ _ hfirst houtput
      exact rebound hfull (by
        simp only [List.length_reverse, List.length_cons]
        omega)

/-- GapCVP reduction support. -/
noncomputable def radiusMarkerTailComputable :
    Turing.TM2ComputableInPolyTime GapCVP.bitEncoding
      GapCVP.bitEncoding (fun input : List Bool => input.tail) where
  tm := radiusMarkerTailMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun input := {
    steps := (radiusMarkerTail_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, radiusMarkerTailMachine_init,
              List.map_tail,
          Option.map_some] using (radiusMarkerTail_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (radiusMarkerTail_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq, Polynomial.eval_add,
          Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X, ge_iff_le] using hsteps
  }

end SourceLatticeStructuralRadiusNumerator

namespace SourceLatticeStructuralRationalRadius

open GapCVP.BinaryEncoding

private theorem sourceRationalNatCast_encode_pair (number : ℕ) :
    Encodable.encode (number : ℚ) =
      Nat.pair (2 * number) 1 := by
  rfl

private theorem sourceRationalNatCast_encode (number : ℕ) :
    Encodable.encode (number : ℚ) =
      4 * number ^ 2 + 2 * number + 1 := by
  rw [sourceRationalNatCast_encode_pair]
  by_cases hzero : number = 0
  · subst number
    norm_num [Nat.pair]
  · have hcomparison : ¬ 2 * number < 1 := by omega
    simp only [Nat.pair, hcomparison, ↓reduceIte, Nat.add_right_cancel_iff]
    ring

theorem sourceRationalNatCast_atomic (number : ℕ) :
    encodeAtomic (number : ℚ) =
      lengthPrefixedWord
        (Computability.encodeNat
          (4 * number ^ 2 + 2 * number + 1)) := by
  simp only [encodeAtomic, sourceRationalNatCast_encode]

end SourceLatticeStructuralRationalRadius

namespace SourceLatticeStructuralRationalRadiusTM

open Turing GapCVP.SourceLatticeNormalizedSectionSynthesis

/-- Internal support shared across GapCVP continuation modules. -/
def rationalRadiusFailureStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 5 => Bool) (Fin 7) (Option Bool) :=
  normalizedRadiusFailureCheck 0
    (normalizedRadiusFailureCheck 1
      (normalizedRadiusFailureCheck 2
        (normalizedRadiusFailureCheck 3
          (normalizedRadiusFailureCheck 4
            (.push 4 (fun _ => false)
              (.load (fun _ => none) .halt))))))

/-- Internal support shared across GapCVP continuation modules. -/
abbrev rationalRadiusMachine : Turing.FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Fin 7
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 7) then
      normalizedRadiusPeek 0
        (.branch (fun symbol => symbol == some true)
          (normalizedRadiusPop 0
            (normalizedRadiusPush 4 (normalizedRadiusGoto 1)))
          (normalizedRadiusPop 0 (normalizedRadiusGoto 6)))
        (normalizedRadiusGoto 6)
    else if phase = (1 : Fin 7) then
      normalizedRadiusPeek 0
        (.branch (fun symbol => symbol == some true)
          (normalizedRadiusPop 0
            (normalizedRadiusPush 1
              (normalizedRadiusPush 1
                (normalizedRadiusPush 2
                  (normalizedRadiusPush 2
                    (normalizedRadiusPush 4
                      (normalizedRadiusPush 4
                        (normalizedRadiusGoto 1))))))))
          (normalizedRadiusPop 0 (normalizedRadiusGoto 6)))
        (normalizedRadiusGoto 2)
    else if phase = (2 : Fin 7) then
      normalizedRadiusPeek 2
        (normalizedRadiusPop 2 (normalizedRadiusGoto 3))
        (normalizedRadiusGoto 5)
    else if phase = (3 : Fin 7) then
      normalizedRadiusPeek 1
        (normalizedRadiusPop 1
          (normalizedRadiusPush 3
            (normalizedRadiusPush 4 (normalizedRadiusGoto 3))))
        (normalizedRadiusGoto 4)
    else if phase = (4 : Fin 7) then
      normalizedRadiusPeek 3
        (normalizedRadiusPop 3
          (normalizedRadiusPush 1 (normalizedRadiusGoto 4)))
        (normalizedRadiusGoto 2)
    else if phase = (5 : Fin 7) then
      normalizedRadiusPeek 1
        (normalizedRadiusPop 1 (normalizedRadiusGoto 5))
        (.push 4 (fun _ => true)
          (.load (fun _ => none) .halt))
    else
      rationalRadiusFailureStatement

/-- Internal support shared across GapCVP continuation modules. -/
def rationalRadiusConfiguration (phase : Fin 7)
    (input base outer restore output : List Bool) :
    rationalRadiusMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, base, outer, restore, output]

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadiusMachine_init (input : List Bool) :
    Turing.initList rationalRadiusMachine input =
      rationalRadiusConfiguration 0 input [] [] [] [] := by
  simp only [rationalRadiusMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq, dite_eq_ite,
      rationalRadiusConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `rationalRadiusStepTac` machine-step simplifier. -/
macro "rationalRadiusStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [rationalRadiusMachine,
          rationalRadiusConfiguration,
          rationalRadiusFailureStatement,
          normalizedRadiusPeek, normalizedRadiusPop,
          normalizedRadiusPush, normalizedRadiusGoto,
          normalizedRadiusFailureCheck,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_marker_true_step
    (input base outer restore output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 0
        (true :: input) base outer restore output) =
      some (rationalRadiusConfiguration 1
        input base outer restore (true :: output)) := by
  rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_marker_false_step
    (input base outer restore output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 0
        (false :: input) base outer restore output) =
      some (rationalRadiusConfiguration 6
        input base outer restore output) := by
  rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_marker_missing_step
    (base outer restore output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 0 []
        base outer restore output) =
      some (rationalRadiusConfiguration 6 []
        base outer restore output) := by
  rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_scan_true_step
    (input base outer restore output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 1
        (true :: input) base outer restore output) =
      some (rationalRadiusConfiguration 1 input
        (true :: true :: base)
        (true :: true :: outer)
        restore (true :: true :: output)) := by
  rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_scan_false_step
    (input base outer restore output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 1
        (false :: input) base outer restore output) =
      some (rationalRadiusConfiguration 6
        input base outer restore output) := by
  rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_scan_finish
    (base outer restore output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 1 []
        base outer restore output) =
      some (rationalRadiusConfiguration 2 []
        base outer restore output) := by
  rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_outer_step
    (base outer restore output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 2 []
        base (true :: outer) restore output) =
      some (rationalRadiusConfiguration 3 []
        base outer restore output) := by
  rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_outer_finish
    (base restore output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 2 []
        base [] restore output) =
      some (rationalRadiusConfiguration 5 []
        base [] restore output) := by
  rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_copy_step
    (base outer restore output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 3 []
        (true :: base) outer restore output) =
      some (rationalRadiusConfiguration 3 []
        base outer (true :: restore) (true :: output)) := by
  rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_copy_finish
    (outer restore output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 3 []
        [] outer restore output) =
      some (rationalRadiusConfiguration 4 []
        [] outer restore output) := by
  rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_restore_step
    (base outer restore output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 4 []
        base outer (true :: restore) output) =
      some (rationalRadiusConfiguration 4 []
        (true :: base) outer restore output) := by
  rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_restore_finish
    (base outer output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 4 []
        base outer [] output) =
      some (rationalRadiusConfiguration 2 []
        base outer [] output) := by
  rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_cleanup_base_step
    (base output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 5 []
        (true :: base) [] [] output) =
      some (rationalRadiusConfiguration 5 []
        base [] [] output) := by
  rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_cleanup_finish (output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 5 [] [] [] [] output) =
      some (Turing.haltList rationalRadiusMachine
        (true :: output)) := by
  rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_failure_input_step
    (bit : Bool) (input base outer restore output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 6
        (bit :: input) base outer restore output) =
      some (rationalRadiusConfiguration 6
        input base outer restore output) := by
  cases bit <;> rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_failure_base_step
    (bit : Bool) (base outer restore output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 6 []
        (bit :: base) outer restore output) =
      some (rationalRadiusConfiguration 6 []
        base outer restore output) := by
  cases bit <;> rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_failure_outer_step
    (bit : Bool) (outer restore output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 6 [] []
        (bit :: outer) restore output) =
      some (rationalRadiusConfiguration 6 [] []
        outer restore output) := by
  cases bit <;> rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_failure_restore_step
    (bit : Bool) (restore output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 6 [] [] []
        (bit :: restore) output) =
      some (rationalRadiusConfiguration 6 [] [] []
        restore output) := by
  cases bit <;> rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_failure_output_step
    (bit : Bool) (output : List Bool) :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 6 [] [] [] []
        (bit :: output)) =
      some (rationalRadiusConfiguration 6 [] [] [] [] output) := by
  cases bit <;> rationalRadiusStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem rationalRadius_failure_finish :
    rationalRadiusMachine.step
      (rationalRadiusConfiguration 6 [] [] [] [] []) =
      some (Turing.haltList rationalRadiusMachine [false]) := by
  rationalRadiusStepTac

end SourceLatticeStructuralRationalRadiusTM

end GapCVP

end
