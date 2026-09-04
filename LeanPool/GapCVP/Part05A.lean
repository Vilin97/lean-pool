/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part04

/-! # GapCVP proof, part 05 -/

noncomputable section

open StateTransition (EvalsToInTime)
open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFUnaryPairIndexTotalRuntimeCert

open Computability Turing GapCVP.SourceTotalStructuralDecoder GapCVP.CNFUnaryPairIndexTM
open GapCVP.CNFUnaryPairIndexTotalCert

private def unaryPairValidBudget (first second : ℕ) : ℕ :=
  (first + 1) + (second + 1) + (min first second + 1) +
    if first < second then
      ((second - first) + first + 1) + (first + 1) +
        (second * (2 * second + 3) + second + 2)
    else
      ((first - second) + second + 1) + (second + 1) +
        (first * (2 * first + 3) + first + 2)

private def unaryPair_validTrace (first second : ℕ) :
    EvalsToInTime actualUnaryPairIndexMachine.step (unaryPairConfiguration 0
        (unarySourcePairWord first second)
        [] [] [] [] [] [] [] [])
      (some (Turing.haltList actualUnaryPairIndexMachine
        (List.replicate (Nat.pair first second) true)))
      (unaryPairValidBudget first second) := by
  have hfirst := unaryPairFirstTrace first
    (List.replicate second true ++ [false])
    [] [] [] [] [] [] [] []
  simp only [List.append_nil] at hfirst
  have hsecond := unaryPairSecondTrace second []
    (List.replicate first true) [] [] [] [] [] [] []
  simp only [List.append_nil] at hsecond
  have hscan := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hsecond
  by_cases hlt : first < second
  · have hcomparison := unaryPairCompareTrace first second 0
    simp only [FinTM2.step, Fin.isValue, List.replicate_zero, unaryPairComparedConfiguration, hlt,
        ↓reduceIte,
        zero_add] at hcomparison
    have hbeforeBase := EvalsToInTime.trans
      actualUnaryPairIndexMachine.step _ _ _ _ _ hscan hcomparison
    have hbase := unaryPairLessBaseTrace
      (second - first) first first [] [] []
    simp only [List.append_nil] at hbase
    have hrestore : second - first + first = second :=
      Nat.sub_add_cancel (Nat.le_of_lt hlt)
    rw [hrestore] at hbase
    have hbeforeOffset := EvalsToInTime.trans
      actualUnaryPairIndexMachine.step _ _ _ _ _ hbeforeBase hbase
    have hoffset := unaryPairLessOffsetTrace first
      (List.replicate second true)
      (List.replicate second true) []
    simp only [List.append_nil] at hoffset
    have hbeforeSquare := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _
      hbeforeOffset hoffset
    have hsquare := unaryPairSquareTrace
      second second (List.replicate first true)
    have houtput :
        List.replicate (second * second) true ++
          List.replicate first true =
        List.replicate (Nat.pair first second) true := by
      rw [← List.replicate_add, Nat.pair, ite_eq_left hlt]
    rw [houtput] at hsquare
    have hfull := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _
      hbeforeSquare hsquare
    have hbounded := rebound (newBudget := unaryPairValidBudget first second)
      hfull (by
        simp only [unaryPairValidBudget, hlt, ↓reduceIte]; omega)
    simpa only [FinTM2.step, Fin.isValue, unarySourcePairWord] using hbounded
  · have hcomparison := unaryPairCompareTrace first second 0
    simp only [FinTM2.step, Fin.isValue, List.replicate_zero, unaryPairComparedConfiguration, hlt,
        ↓reduceIte,
        zero_add] at hcomparison
    have hbeforeBase := EvalsToInTime.trans
      actualUnaryPairIndexMachine.step _ _ _ _ _ hscan hcomparison
    have hbase := unaryPairGreaterBaseTrace
      (first - second) second second [] [] []
    simp only [List.append_nil] at hbase
    have hrestore : first - second + second = first :=
      Nat.sub_add_cancel (Nat.le_of_not_gt hlt)
    rw [hrestore] at hbase
    have hbeforeOffset := EvalsToInTime.trans
      actualUnaryPairIndexMachine.step _ _ _ _ _ hbeforeBase hbase
    have hoffset := unaryPairGreaterOffsetTrace second
      (List.replicate first true)
      (List.replicate first true)
      (List.replicate first true)
    have hbeforeSquare := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _
      hbeforeOffset hoffset
    have hsquare := unaryPairSquareTrace
      first first
      (List.replicate second true ++ List.replicate first true)
    have houtput :
        List.replicate (first * first) true ++
          (List.replicate second true ++
            List.replicate first true) =
        List.replicate (Nat.pair first second) true := by
      rw [← List.replicate_add, ← List.replicate_add,
        Nat.pair, ite_eq_right hlt]
      simp only [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
    rw [houtput] at hsquare
    have hfull := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _
      hbeforeSquare hsquare
    have hbounded := rebound (newBudget := unaryPairValidBudget first second)
      hfull (by
        simp only [unaryPairValidBudget, hlt, ↓reduceIte]; omega)
    simpa only [FinTM2.step, Fin.isValue, unarySourcePairWord] using hbounded

private def unaryPair_failureTrace
    (input first second matchedFirst matchedSecond
      base outer scratch : List Bool) :
    EvalsToInTime actualUnaryPairIndexMachine.step (unaryPairConfiguration 11 input first second
        matchedFirst matchedSecond base outer [] scratch)
      (some (Turing.haltList actualUnaryPairIndexMachine []))
      (input.length + first.length + second.length +
        matchedFirst.length + matchedSecond.length +
        base.length + outer.length + scratch.length + 1) := by
  induction input generalizing first second matchedFirst
      matchedSecond base outer scratch with
  | cons bit input ih =>
      have hfirst := oneStep _ _ (unaryPair_failure_input_step bit input first second
          matchedFirst matchedSecond base outer scratch)
      have hrest := ih first second matchedFirst matchedSecond
        base outer scratch
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, Nat.add_comm, Nat.add_left_comm,
          Nat.reduceAdd,
          Nat.add_assoc] using EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _
              hfirst hrest
  | nil =>
      induction first generalizing second matchedFirst matchedSecond
          base outer scratch with
      | cons bit first ih =>
          have hfirst := oneStep _ _ (unaryPair_failure_first_step bit first second
              matchedFirst matchedSecond base outer scratch)
          have hrest := ih second matchedFirst matchedSecond
            base outer scratch
          simpa only [FinTM2.step, Fin.isValue, List.length_nil, List.length_cons, zero_add,
              Nat.add_comm,
              Nat.add_left_comm, Nat.reduceAdd, Nat.add_assoc] using
              EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest
      | nil =>
          induction second generalizing matchedFirst matchedSecond
              base outer scratch with
          | cons bit second ih =>
              have hfirst := oneStep _ _ (unaryPair_failure_second_step bit second
                  matchedFirst matchedSecond base outer scratch)
              have hrest := ih matchedFirst matchedSecond
                base outer scratch
              simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero, List.length_cons,
                  zero_add, Nat.add_comm,
                  Nat.add_left_comm, Nat.reduceAdd, Nat.add_assoc] using
                  EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest
          | nil =>
              induction matchedFirst generalizing matchedSecond
                  base outer scratch with
              | cons bit matchedFirst ih =>
                  have hfirst := oneStep _ _ (unaryPair_failure_matchedFirst_step bit
                      matchedFirst matchedSecond base outer scratch)
                  have hrest := ih matchedSecond base outer scratch
                  simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero,
                      List.length_cons, zero_add, Nat.add_comm,
                      Nat.add_left_comm, Nat.reduceAdd, Nat.add_assoc] using
                      EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest
              | nil =>
                  induction matchedSecond generalizing
                      base outer scratch with
                  | cons bit matchedSecond ih =>
                      have hfirst := oneStep _ _ (unaryPair_failure_matchedSecond_step bit
                          matchedSecond base outer scratch)
                      have hrest := ih base outer scratch
                      simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero,
                          List.length_cons, zero_add, Nat.add_comm,
                          Nat.add_left_comm, Nat.reduceAdd, Nat.add_assoc] using
                          EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst
                              hrest
                  | nil =>
                      induction base generalizing outer scratch with
                      | cons bit base ih =>
                          have hfirst := oneStep _ _ (unaryPair_failure_base_step bit
                              base outer scratch)
                          have hrest := ih outer scratch
                          simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero,
                              List.length_cons, zero_add, Nat.add_comm,
                              Nat.add_left_comm, Nat.reduceAdd, Nat.add_assoc] using
                              EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst
                                  hrest
                      | nil =>
                          induction outer generalizing scratch with
                          | cons bit outer ih =>
                              have hfirst := oneStep _ _ (unaryPair_failure_outer_step bit
                                  outer scratch)
                              have hrest := ih scratch
                              simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero,
                                  List.length_cons, zero_add, Nat.add_comm,
                                  Nat.add_left_comm, Nat.reduceAdd, Nat.add_assoc] using
                                  EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _
                                      hfirst hrest
                          | nil =>
                              induction scratch with
                              | cons bit scratch ih =>
                                  have hfirst := oneStep _ _ (unaryPair_failure_scratch_step
                                      bit scratch)
                                  simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero,
                                      List.length_cons, zero_add, Nat.add_comm,
                                      Nat.add_left_comm, Nat.reduceAdd] using EvalsToInTime.trans
                                          actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst ih
                              | nil =>
                                  simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero,
                                      zero_add] using
                                      oneStep _ _ unaryPair_failure_finish

private def unaryPair_firstMissingTrace
    (count : ℕ)
    (first second matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    EvalsToInTime actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 0 (List.replicate count true)
        first second matchedFirst matchedSecond
        base outer output scratch)
      (some (unaryPairConfiguration 11 []
        (List.replicate count true ++ first) second
        matchedFirst matchedSecond base outer output scratch))
      (count + 1) := by
  induction count generalizing first with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (unaryPair_first_missing first second matchedFirst matchedSecond base outer
              output scratch)
  | succ count ih =>
      have hfirst := oneStep _ _ (unaryPair_first_true (List.replicate count true)
          first second matchedFirst matchedSecond
          base outer output scratch)
      have hrest := ih (true :: first)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest

private def unaryPair_secondMissingTrace
    (count : ℕ)
    (first second matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    EvalsToInTime actualUnaryPairIndexMachine.step
      (unaryPairConfiguration 1 (List.replicate count true)
        first second matchedFirst matchedSecond
        base outer output scratch)
      (some (unaryPairConfiguration 11 [] first
        (List.replicate count true ++ second)
        matchedFirst matchedSecond base outer output scratch))
      (count + 1) := by
  induction count generalizing second with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (unaryPair_second_missing first second matchedFirst matchedSecond base outer
              output scratch)
  | succ count ih =>
      have hfirst := oneStep _ _ (unaryPair_second_true (List.replicate count true)
          first second matchedFirst matchedSecond
          base outer output scratch)
      have hrest := ih (true :: second)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest

private def unaryPairInputBudget (input : List Bool) : ℕ :=
  64 * input.length ^ 2 + 128 * input.length + 128

private theorem unaryPairValidBudget_le_quadratic
    (first second : ℕ) :
    unaryPairValidBudget first second ≤
      64 * (first + second + 2) ^ 2 +
        128 * (first + second + 2) + 128 := by
  unfold unaryPairValidBudget
  split_ifs with hlt
  · have hle : first ≤ second := Nat.le_of_lt hlt
    rw [min_eq_left hle, Nat.sub_add_cancel hle]
    nlinarith
  · have hle : second ≤ first := Nat.le_of_not_gt hlt
    rw [min_eq_right hle, Nat.sub_add_cancel hle]
    nlinarith

private def unaryPair_totalTrace (input : List Bool) :
    EvalsToInTime actualUnaryPairIndexMachine.step (unaryPairConfiguration 0 input
        [] [] [] [] [] [] [] [])
      (some (Turing.haltList actualUnaryPairIndexMachine
        (unarySourcePairOutput input)))
      (unaryPairInputBudget input) := by
  cases unaryInputSplit input with
  | inl witness =>
      obtain ⟨count, hinput⟩ := witness
      subst input
      have hprefix := unaryPair_firstMissingTrace count
        [] [] [] [] [] [] [] []
      simp only [List.append_nil] at hprefix
      have hclean := unaryPair_failureTrace []
        (List.replicate count true) [] [] [] [] [] []
      have hfull := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hprefix hclean
      have hbounded := rebound (newBudget := unaryPairInputBudget
          (List.replicate count true))
        hfull (by
          simp only [unaryPairInputBudget,
            List.length_replicate, List.length_nil]
          nlinarith)
      simpa only [FinTM2.step, Fin.isValue, unarySourcePairOutput, readUnaryPrefix_missing]
          using hbounded
  | inr witness =>
      obtain ⟨first, tail, hinput⟩ := witness
      subst input
      cases unaryInputSplit tail with
      | inl missing =>
          obtain ⟨second, htail⟩ := missing
          subst tail
          have hfirst := unaryPairFirstTrace first
            (List.replicate second true)
            [] [] [] [] [] [] [] []
          simp only [List.append_nil] at hfirst
          have hsecond := unaryPair_secondMissingTrace second
            (List.replicate first true)
            [] [] [] [] [] [] []
          simp only [List.append_nil] at hsecond
          have hscan := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _
            hfirst hsecond
          have hclean := unaryPair_failureTrace []
            (List.replicate first true)
            (List.replicate second true) [] [] [] [] []
          have hfull := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _
            hscan hclean
          have hbounded := rebound (newBudget := unaryPairInputBudget
              (List.replicate first true ++
                false :: List.replicate second true))
            hfull (by
              simp only [unaryPairInputBudget,
                List.length_append, List.length_replicate,
                List.length_cons, List.length_nil]
              nlinarith)
          simpa only [FinTM2.step, Fin.isValue, unarySourcePairOutput,
              BinaryEncoding.readUnaryPrefix_replicate,
              readUnaryPrefix_missing] using hbounded
      | inr delimited =>
          obtain ⟨second, remaining, htail⟩ := delimited
          subst tail
          cases remaining with
          | nil =>
              have hvalid := unaryPair_validTrace first second
              have hbounded := rebound (newBudget := unaryPairInputBudget
                  (unarySourcePairWord first second))
                hvalid (by
                  simpa only [unaryPairInputBudget, unarySourcePairWord, List.length_append,
                      List.length_replicate,
                      List.length_cons, List.length_nil, zero_add, Nat.add_assoc, Nat.reduceAdd]
                          using
                      unaryPairValidBudget_le_quadratic first second)
              simpa only [FinTM2.step, Fin.isValue, unarySourcePairOutput,
                  BinaryEncoding.readUnaryPrefix_replicate,
                  unarySourcePairWord] using hbounded
          | cons bit remaining =>
              have hfirst := unaryPairFirstTrace first
                (List.replicate second true ++
                  false :: bit :: remaining)
                [] [] [] [] [] [] [] []
              simp only [List.append_nil] at hfirst
              have hsecond := unaryPairSecondTrace second
                (bit :: remaining)
                (List.replicate first true)
                [] [] [] [] [] [] []
              simp only [List.append_nil] at hsecond
              have hscan := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _
                hfirst hsecond
              have htrailing := oneStep _ _ (unaryPair_compare_trailing bit remaining
                  (List.replicate first true)
                  (List.replicate second true)
                  [] [] [] [] [] [])
              have hreject := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _
                hscan htrailing
              have hclean := unaryPair_failureTrace
                (bit :: remaining)
                (List.replicate first true)
                (List.replicate second true)
                [] [] [] [] []
              have hfull := EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _
                hreject hclean
              have hbounded := rebound (newBudget := unaryPairInputBudget
                  (List.replicate first true ++
                    false :: (List.replicate second true ++
                      false :: bit :: remaining)))
                hfull (by
                  simp only [unaryPairInputBudget,
                    List.length_append, List.length_replicate,
                    List.length_cons, List.length_nil]
                  nlinarith)
              simpa only [FinTM2.step, Fin.isValue, unarySourcePairOutput,
                  BinaryEncoding.readUnaryPrefix_replicate] using
                  hbounded

/-- GapCVP reduction support. -/
noncomputable def actualUnaryPairIndexComputable :
    BitTM
      unarySourcePairOutput where
  tm := actualUnaryPairIndexMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 64 * Polynomial.X ^ 2 + 128 * Polynomial.X + 128
  outputsFun input := {
    steps := (unaryPair_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, actualUnaryPairIndexMachine_init,
              Option.map_some] using
          (unaryPair_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (unaryPair_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, unaryPairInputBudget, bitEncoding, id_eq,
          Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_X,
              ge_iff_le] using hsteps
  }

end CNFUnaryPairIndexTotalRuntimeCert

namespace CNFPairedSourceGridDescriptorTM

open Computability Turing GapCVP.ThreeCNFReduction GapCVP.CNFFlatStructuralRecordWorkerTM
open GapCVP.CNFFlatSourceGridDescriptorTM GapCVP.CNFUnaryPairIndexTM
open GapCVP.CNFUnaryPairIndexTotalRuntimeCert

/-- GapCVP reduction support. -/
def pairedAccumulatorSignedLiteralDescriptorWord
    (sign : Bool) (input : List Bool) : List Bool :=
  accumulatorSignedLiteralDescriptorWord sign
    (unarySourcePairOutput input)

/-- GapCVP reduction support. -/
noncomputable def pairedAccumulatorSignedLiteralDescriptorComputable
    (sign : Bool) :
    BitTM
      (pairedAccumulatorSignedLiteralDescriptorWord sign) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    actualUnaryPairIndexComputable
    (accumulatorSignedLiteralDescriptorComputable sign)
  change BitTM
    (fun input : List Bool =>
      accumulatorSignedLiteralDescriptorWord sign
        (unarySourcePairOutput input))
  simpa only [Function.comp_def] using hphysical

@[simp] theorem pairedAccumulatorSignedLiteralDescriptorWord_pair
    (clauseIndex prefixIndex : ℕ) (sign : Bool) :
    pairedAccumulatorSignedLiteralDescriptorWord sign
      (unarySourcePairWord clauseIndex prefixIndex) =
      flatSignedLiteralDescriptor
        (accumulatorVariable clauseIndex prefixIndex, sign) := by
  simp only [pairedAccumulatorSignedLiteralDescriptorWord, unarySourcePairOutput_word,
      accumulatorSignedLiteralDescriptorWord_index]

end CNFPairedSourceGridDescriptorTM

namespace CNFSourcePairPrefixWorkerTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.CNFUnaryPairIndexTM

/-- GapCVP reduction support. -/
def sourcePairPrefixOutput (input : List Bool) : List Bool :=
  match readUnaryPrefix input with
  | none => []
  | some (first, remaining) =>
      match readUnaryPrefix remaining with
      | none => []
      | some (second, _) => unarySourcePairWord first second

@[simp] theorem sourcePairPrefixOutput_pair
    (first second : ℕ) (suffix : List Bool) :
    sourcePairPrefixOutput
      (unarySourcePairWord first second ++ suffix) =
      unarySourcePairWord first second := by
  simp only [sourcePairPrefixOutput, unarySourcePairWord, List.append_assoc, List.cons_append,
      List.nil_append,
      readUnaryPrefix_replicate]

private def sourcePairPrefixPeek (stack : Fin 4)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 6) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 6) (Option Bool) :=
  .peek stack (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome) present absent)

private def sourcePairPrefixPop (stack : Fin 4)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 6) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 6) (Option Bool) :=
  .pop stack (fun symbol _ => symbol) continuation

private def sourcePairPrefixPush (stack : Fin 4) (bit : Bool)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 6) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 6) (Option Bool) :=
  .push stack (fun _ => bit) continuation

private def sourcePairPrefixGoto (phase : Fin 6) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 6) (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => phase))

/-- Internal support shared across GapCVP continuation modules. -/
def sourcePairPrefixFirstStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 6) (Option Bool) :=
  sourcePairPrefixPeek 0
    (.branch (fun symbol => symbol.getD false)
      (sourcePairPrefixPop 0
        (sourcePairPrefixPush 1 true (sourcePairPrefixGoto 0)))
      (sourcePairPrefixPop 0 (sourcePairPrefixGoto 1)))
    (sourcePairPrefixGoto 5)

/-- Internal support shared across GapCVP continuation modules. -/
def sourcePairPrefixSecondStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 6) (Option Bool) :=
  sourcePairPrefixPeek 0
    (.branch (fun symbol => symbol.getD false)
      (sourcePairPrefixPop 0
        (sourcePairPrefixPush 2 true (sourcePairPrefixGoto 1)))
      (sourcePairPrefixPop 0
        (sourcePairPrefixPush 3 false (sourcePairPrefixGoto 2))))
    (sourcePairPrefixGoto 5)

/-- Internal support shared across GapCVP continuation modules. -/
def sourcePairPrefixSuffixStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 6) (Option Bool) :=
  sourcePairPrefixPeek 0
    (sourcePairPrefixPop 0 (sourcePairPrefixGoto 2))
    (sourcePairPrefixGoto 3)

/-- Internal support shared across GapCVP continuation modules. -/
def sourcePairPrefixSecondRestoreStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 6) (Option Bool) :=
  sourcePairPrefixPeek 2
    (sourcePairPrefixPop 2
      (sourcePairPrefixPush 3 true (sourcePairPrefixGoto 3)))
    (sourcePairPrefixPush 3 false (sourcePairPrefixGoto 4))

/-- Internal support shared across GapCVP continuation modules. -/
def sourcePairPrefixFirstRestoreStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 6) (Option Bool) :=
  sourcePairPrefixPeek 1
    (sourcePairPrefixPop 1
      (sourcePairPrefixPush 3 true (sourcePairPrefixGoto 4)))
    .halt

/-- Internal support shared across GapCVP continuation modules. -/
def sourcePairPrefixFailureStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 6) (Option Bool) :=
  sourcePairPrefixPeek 0
    (sourcePairPrefixPop 0 (sourcePairPrefixGoto 5))
    (sourcePairPrefixPeek 1
      (sourcePairPrefixPop 1 (sourcePairPrefixGoto 5))
      (sourcePairPrefixPeek 2
        (sourcePairPrefixPop 2 (sourcePairPrefixGoto 5))
        (sourcePairPrefixPeek 3
          (sourcePairPrefixPop 3 (sourcePairPrefixGoto 5))
          .halt)))

/-- Internal support shared across GapCVP continuation modules. -/
abbrev actualSourcePairPrefixMachine : Turing.FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Fin 6
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 6) then sourcePairPrefixFirstStatement
    else if phase = (1 : Fin 6) then sourcePairPrefixSecondStatement
    else if phase = (2 : Fin 6) then sourcePairPrefixSuffixStatement
    else if phase = (3 : Fin 6) then
      sourcePairPrefixSecondRestoreStatement
    else if phase = (4 : Fin 6) then
      sourcePairPrefixFirstRestoreStatement
    else sourcePairPrefixFailureStatement

/-- Internal support shared across GapCVP continuation modules. -/
def sourcePairPrefixConfiguration (phase : Fin 6)
    (input first second output : List Bool) :
    actualSourcePairPrefixMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, first, second, output]

/-- Internal support shared across GapCVP continuation modules. -/
theorem actualSourcePairPrefixMachine_init (input : List Bool) :
    Turing.initList actualSourcePairPrefixMachine input =
      sourcePairPrefixConfiguration 0 input [] [] [] := by
  simp only [actualSourcePairPrefixMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq,
      dite_eq_ite,
      sourcePairPrefixConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `sourcePairPrefixStepTac` machine-step simplifier. -/
macro "sourcePairPrefixStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [actualSourcePairPrefixMachine,
          sourcePairPrefixConfiguration,
          sourcePairPrefixPeek, sourcePairPrefixPop,
          sourcePairPrefixPush, sourcePairPrefixGoto,
          sourcePairPrefixFirstStatement,
          sourcePairPrefixSecondStatement,
          sourcePairPrefixSuffixStatement,
          sourcePairPrefixSecondRestoreStatement,
          sourcePairPrefixFirstRestoreStatement,
          sourcePairPrefixFailureStatement,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_first_true
    (input first second output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 0
        (true :: input) first second output) =
      some (sourcePairPrefixConfiguration 0
        input (true :: first) second output) := by
  sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_first_false
    (input first second output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 0
        (false :: input) first second output) =
      some (sourcePairPrefixConfiguration 1
        input first second output) := by
  sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_first_missing
    (first second output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 0 [] first second output) =
      some (sourcePairPrefixConfiguration 5 [] first second output) := by
  sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_second_true
    (input first second output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 1
        (true :: input) first second output) =
      some (sourcePairPrefixConfiguration 1
        input first (true :: second) output) := by
  sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_second_false
    (input first second output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 1
        (false :: input) first second output) =
      some (sourcePairPrefixConfiguration 2
        input first second (false :: output)) := by
  sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_second_missing
    (first second output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 1 [] first second output) =
      some (sourcePairPrefixConfiguration 5 [] first second output) := by
  sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_suffix_step
    (bit : Bool) (input first second output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 2
        (bit :: input) first second output) =
      some (sourcePairPrefixConfiguration 2
        input first second output) := by
  cases bit <;> sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_suffix_finish
    (first second output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 2 [] first second output) =
      some (sourcePairPrefixConfiguration 3
        [] first second output) := by
  sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_secondRestore_step
    (first second output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 3
        [] first (true :: second) output) =
      some (sourcePairPrefixConfiguration 3
        [] first second (true :: output)) := by
  sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_secondRestore_finish
    (first output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 3 [] first [] output) =
      some (sourcePairPrefixConfiguration 4
        [] first [] (false :: output)) := by
  sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_firstRestore_step
    (first output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 4
        [] (true :: first) [] output) =
      some (sourcePairPrefixConfiguration 4
        [] first [] (true :: output)) := by
  sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_firstRestore_finish
    (output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 4 [] [] [] output) =
      some (Turing.haltList actualSourcePairPrefixMachine output) := by
  sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_failure_input_step
    (bit : Bool) (input first second output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 5
        (bit :: input) first second output) =
      some (sourcePairPrefixConfiguration 5
        input first second output) := by
  cases bit <;> sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_failure_first_step
    (bit : Bool) (first second output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 5
        [] (bit :: first) second output) =
      some (sourcePairPrefixConfiguration 5
        [] first second output) := by
  cases bit <;> sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_failure_second_step
    (bit : Bool) (second output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 5
        [] [] (bit :: second) output) =
      some (sourcePairPrefixConfiguration 5
        [] [] second output) := by
  cases bit <;> sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_failure_output_step
    (bit : Bool) (output : List Bool) :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 5 [] [] [] (bit :: output)) =
      some (sourcePairPrefixConfiguration 5 [] [] [] output) := by
  cases bit <;> sourcePairPrefixStepTac

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourcePairPrefix_failure_finish :
    actualSourcePairPrefixMachine.step
      (sourcePairPrefixConfiguration 5 [] [] [] []) =
      some (Turing.haltList actualSourcePairPrefixMachine []) := by
  sourcePairPrefixStepTac

end CNFSourcePairPrefixWorkerTM

end GapCVP

end
