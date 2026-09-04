/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part03B

/-! # GapCVP proof, part 03, continuation 03 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace SourceFormulaStructuralDecoder

open Turing GapCVP.SourceTotalStructuralDecoder

private def suffix_prefixTrace
    (count : ℕ) (tail counter reversed output : List Bool) :
    EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 0
        (List.replicate count true ++ false :: tail)
        counter reversed output)
      (some (suffixConfiguration 1 tail
        (List.replicate count true ++ counter) reversed output))
      (count + 1) := by
  induction count generalizing counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (suffix_prefix_delimiter tail counter reversed output)
  | succ count ih =>
      have hfirst := oneStep _ _ (suffix_prefix_true
          (List.replicate count true ++ false :: tail)
          counter reversed output)
      have hrest := ih (true :: counter)
      have hboth := EvalsToInTime.trans suffixDecoderMachine.step 1 (count + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hboth

private def suffix_copyTrace
    (payload suffix reversed output : List Bool) :
    EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 1 (payload ++ suffix)
        (List.replicate payload.length true) reversed output)
      (some (suffixConfiguration 1 suffix []
        (payload.reverse ++ reversed) output))
      payload.length := by
  induction payload generalizing reversed with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.nil_append, List.length_nil, List.replicate_zero,
          List.reverse_nil] using
          EvalsToInTime.refl suffixDecoderMachine.step (suffixConfiguration 1 suffix [] reversed
              output)
  | cons bit payload ih =>
      have hfirst := oneStep _ _ (suffix_copy_step bit (payload ++ suffix)
          (List.replicate payload.length true) reversed output)
      have hrest := ih (bit :: reversed)
      have hboth := EvalsToInTime.trans suffixDecoderMachine.step 1 payload.length
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.cons_append, List.length_cons,
          List.replicate_succ,
          List.reverse_cons, List.append_assoc, List.nil_append] using hboth

private def suffix_discardTrace
    (input reversed output : List Bool) :
    EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 2 input [] reversed output)
      (some (suffixConfiguration 3 input [] [] output))
      (reversed.length + 1) := by
  induction reversed with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, zero_add] using
          oneStep _ _ (suffix_discard_complete input output)
  | cons bit reversed ih =>
      have hfirst := oneStep _ _ (suffix_discard_step bit input reversed output)
      have hboth := EvalsToInTime.trans suffixDecoderMachine.step 1 (reversed.length + 1)
        _ _ _ hfirst ih
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, Nat.add_assoc, Nat.reduceAdd]
          using hboth

private def suffix_collectTrace
    (input reversed output : List Bool) :
    EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 3 input [] reversed output)
      (some (suffixConfiguration 4 [] []
        (input.reverse ++ reversed) output))
      (input.length + 1) := by
  induction input generalizing reversed with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (suffix_collect_complete reversed output)
  | cons bit input ih =>
      have hfirst := oneStep _ _ (suffix_collect_step bit input reversed output)
      have hrest := ih (bit :: reversed)
      have hboth := EvalsToInTime.trans suffixDecoderMachine.step 1 (input.length + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hboth

private def suffix_restoreTrace
    (reversed output : List Bool) :
    EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 4 [] [] reversed output)
      (some (Turing.haltList suffixDecoderMachine
        (reversed.reverse ++ output)))
      (reversed.length + 1) := by
  induction reversed generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (suffix_restore_finish output)
  | cons bit reversed ih =>
      have hfirst := oneStep _ _ (suffix_restore_step bit reversed output)
      have hrest := ih (bit :: output)
      have hboth := EvalsToInTime.trans suffixDecoderMachine.step 1 (reversed.length + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hboth

private def suffix_validTrace
    (payload suffix : List Bool) :
    EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 0
        (BinaryEncoding.lengthPrefixedWord payload ++ suffix)
        [] [] [])
      (some (Turing.haltList suffixDecoderMachine suffix))
      (3 * payload.length + 2 * suffix.length + 5) := by
  have hprefix :
      EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 0
          (BinaryEncoding.lengthPrefixedWord payload ++ suffix)
          [] [] [])
        (some (suffixConfiguration 1 (payload ++ suffix)
          (List.replicate payload.length true) [] []))
        (payload.length + 1) := by
    simpa only [FinTM2.step, Fin.isValue, BinaryEncoding.lengthPrefixedWord, List.append_assoc,
        List.cons_append,
        List.append_nil] using suffix_prefixTrace payload.length (payload ++ suffix) [] [] []
  have hcopy :
      EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 1 (payload ++ suffix)
          (List.replicate payload.length true) [] [])
        (some (suffixConfiguration 1 suffix [] payload.reverse []))
        payload.length := by
    simpa only [FinTM2.step, Fin.isValue, List.append_nil] using suffix_copyTrace payload suffix []
        []
  have hcounter := oneStep _ _ (suffix_counter_complete suffix payload.reverse [])
  have hdiscard := suffix_discardTrace suffix payload.reverse []
  have hcollect :
      EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 3 suffix [] [] [])
        (some (suffixConfiguration 4 [] [] suffix.reverse []))
        (suffix.length + 1) := by
    simpa only [FinTM2.step, Fin.isValue, List.append_nil] using suffix_collectTrace suffix [] []
  have hrestore :
      EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 4 [] [] suffix.reverse [])
        (some (Turing.haltList suffixDecoderMachine suffix))
        (suffix.length + 1) := by
    simpa only [FinTM2.step, Fin.isValue, List.reverse_reverse, List.append_nil,
        List.length_reverse] using
        suffix_restoreTrace suffix.reverse []
  have h01 := EvalsToInTime.trans suffixDecoderMachine.step _ _ _ _ _ hprefix hcopy
  have h012 := EvalsToInTime.trans suffixDecoderMachine.step _ _ _ _ _ h01 hcounter
  have h0123 := EvalsToInTime.trans suffixDecoderMachine.step _ _ _ _ _ h012 hdiscard
  have h01234 := EvalsToInTime.trans suffixDecoderMachine.step _ _ _ _ _ h0123 hcollect
  have hfull := EvalsToInTime.trans suffixDecoderMachine.step _ _ _ _ _ h01234 hrestore
  exact {
    steps := hfull.steps
    evals_in_steps := hfull.evals_in_steps
    steps_le_m := by
      have hsteps := hfull.steps_le_m
      simp only [List.length_reverse] at hsteps
      omega
  }

private def suffix_failureTrace
    (input counter reversed output : List Bool) :
    EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 5 input counter reversed output)
      (some (Turing.haltList suffixDecoderMachine output))
      (input.length + counter.length + reversed.length + 1) := by
  induction input generalizing counter reversed output with
  | cons bit input ih =>
      have hfirst := oneStep _ _ (suffix_failure_drop_input bit input counter reversed output)
      have hrest := ih counter reversed output
      have hboth := EvalsToInTime.trans suffixDecoderMachine.step 1
        (input.length + counter.length + reversed.length + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, Nat.add_comm, Nat.add_left_comm,
          Nat.reduceAdd,
          Nat.add_assoc] using hboth
  | nil =>
      induction counter generalizing reversed output with
      | cons bit counter ih =>
          have hfirst := oneStep _ _ (suffix_failure_drop_counter bit counter reversed output)
          have hrest :
              EvalsToInTime suffixDecoderMachine.step
                (suffixConfiguration 5 [] counter reversed output)
                (some (Turing.haltList suffixDecoderMachine output))
                (counter.length + reversed.length + 1) := by
            simpa only [FinTM2.step, Fin.isValue, List.length_nil, zero_add] using ih reversed
                output
          have hboth := EvalsToInTime.trans suffixDecoderMachine.step 1
            (counter.length + reversed.length + 1)
            _ _ _ hfirst hrest
          simpa only [FinTM2.step, Fin.isValue, List.length_nil, List.length_cons, zero_add,
              Nat.add_comm,
              Nat.add_left_comm, Nat.reduceAdd, Nat.add_assoc] using hboth
      | nil =>
          induction reversed generalizing output with
          | cons bit reversed ih =>
              have hfirst := oneStep _ _ (suffix_failure_drop_reversed bit reversed output)
              have hrest :
                  EvalsToInTime suffixDecoderMachine.step
                    (suffixConfiguration 5 [] [] reversed output)
                    (some (Turing.haltList suffixDecoderMachine output))
                    (reversed.length + 1) := by
                simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero, zero_add] using ih
                    output
              have hboth := EvalsToInTime.trans suffixDecoderMachine.step 1 (reversed.length + 1)
                _ _ _ hfirst hrest
              simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero, List.length_cons,
                  zero_add, Nat.add_comm,
                  Nat.add_left_comm, Nat.reduceAdd] using hboth
          | nil =>
              simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero, zero_add] using
                  oneStep _ _ (suffix_failure_finish output)

private def suffix_missingPrefixTrace
    (count : ℕ) (counter reversed output : List Bool) :
    EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 0 (List.replicate count true)
        counter reversed output)
      (some (suffixConfiguration 5 []
        (List.replicate count true ++ counter) reversed output))
      (count + 1) := by
  induction count generalizing counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (suffix_prefix_missing_delimiter counter reversed output)
  | succ count ih =>
      have hfirst := oneStep _ _ (suffix_prefix_true (List.replicate count true)
          counter reversed output)
      have hrest := ih (true :: counter)
      have hboth := EvalsToInTime.trans suffixDecoderMachine.step 1 (count + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hboth

private def suffix_missingTrace (count : ℕ) :
    EvalsToInTime suffixDecoderMachine.step
      (suffixConfiguration 0 (List.replicate count true) [] [] [])
      (some (Turing.haltList suffixDecoderMachine []))
      (2 * count + 2) := by
  have hprefix :
      EvalsToInTime suffixDecoderMachine.step
        (suffixConfiguration 0 (List.replicate count true) [] [] [])
        (some (suffixConfiguration 5 []
          (List.replicate count true) [] []))
        (count + 1) := by
    simpa only [FinTM2.step, Fin.isValue, List.append_nil] using suffix_missingPrefixTrace count []
        [] []
  have hcleanup := suffix_failureTrace []
    (List.replicate count true) [] []
  have hfull := EvalsToInTime.trans suffixDecoderMachine.step _ _ _ _ _ hprefix hcleanup
  exact {
    steps := hfull.steps
    evals_in_steps := hfull.evals_in_steps
    steps_le_m := by
      have hsteps := hfull.steps_le_m
      simp only [List.length_replicate, List.length_nil] at hsteps
      omega
  }

private def suffix_partialCopyTrace
    (payload remaining reversed output : List Bool) :
    EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 1 payload
        (List.replicate payload.length true ++ remaining)
        reversed output)
      (some (suffixConfiguration 1 [] remaining
        (payload.reverse ++ reversed) output))
      payload.length := by
  induction payload generalizing reversed with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, List.replicate_zero, List.nil_append,
          List.reverse_nil] using
          EvalsToInTime.refl suffixDecoderMachine.step (suffixConfiguration 1 [] remaining reversed
              output)
  | cons bit payload ih =>
      have hfirst := oneStep _ _ (suffix_copy_step bit payload
          (List.replicate payload.length true ++ remaining)
          reversed output)
      have hrest := ih (bit :: reversed)
      have hboth := EvalsToInTime.trans suffixDecoderMachine.step 1 payload.length
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, List.replicate_succ,
          List.cons_append,
          List.reverse_cons, List.append_assoc, List.nil_append] using hboth

private def suffix_truncatedTrace
    (payload : List Bool) (extra : ℕ) :
    EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 0
        (List.replicate (payload.length + extra + 1) true ++
          false :: payload)
        [] [] [])
      (some (Turing.haltList suffixDecoderMachine []))
      (3 * payload.length + 2 * extra + 6) := by
  have hprefix :
      EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 0
          (List.replicate (payload.length + extra + 1) true ++
            false :: payload)
          [] [] [])
        (some (suffixConfiguration 1 payload
          (List.replicate (payload.length + extra + 1) true) [] []))
        (payload.length + extra + 1 + 1) := by
    simpa only [FinTM2.step, Fin.isValue, List.append_nil] using
        suffix_prefixTrace (payload.length + extra + 1) payload [] [] []
  have hcopy :
      EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 1 payload
          (List.replicate (payload.length + extra + 1) true) [] [])
        (some (suffixConfiguration 1 []
          (List.replicate (extra + 1) true) payload.reverse []))
        payload.length := by
    have hcounter :
        List.replicate (payload.length + extra + 1) true =
          List.replicate payload.length true ++
            List.replicate (extra + 1) true := by
      rw [show payload.length + extra + 1 =
        payload.length + (extra + 1) by omega, List.replicate_add]
    rw [hcounter]
    simpa only [FinTM2.step, Fin.isValue, List.replicate_append_replicate, List.append_nil] using
        suffix_partialCopyTrace payload (List.replicate (extra + 1) true) [] []
  have hinsufficient :
      EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 1 []
          (List.replicate (extra + 1) true) payload.reverse [])
        (some (suffixConfiguration 5 []
          (List.replicate (extra + 1) true) payload.reverse []))
        1 := by
    simpa only [FinTM2.step, Fin.isValue, List.replicate_succ] using
        oneStep _ _ (suffix_insufficient (List.replicate extra true) payload.reverse [])
  have hcleanup := suffix_failureTrace []
    (List.replicate (extra + 1) true) payload.reverse []
  have h01 := EvalsToInTime.trans suffixDecoderMachine.step _ _ _ _ _ hprefix hcopy
  have h012 := EvalsToInTime.trans suffixDecoderMachine.step _ _ _ _ _ h01 hinsufficient
  have hfull := EvalsToInTime.trans suffixDecoderMachine.step _ _ _ _ _ h012 hcleanup
  exact {
    steps := hfull.steps
    evals_in_steps := hfull.evals_in_steps
    steps_le_m := by
      have hsteps := hfull.steps_le_m
      simp only [List.length_nil, List.length_replicate,
        List.length_reverse] at hsteps
      omega
  }

/-- GapCVP reduction support. -/
def firstFieldSuffix (input : List Bool) : List Bool :=
  match BinaryEncoding.readLengthPrefixedWord input with
  | some (_, suffix) => suffix
  | none => []

@[simp] theorem firstFieldSuffix_valid
    (payload suffix : List Bool) :
    firstFieldSuffix
      (BinaryEncoding.lengthPrefixedWord payload ++ suffix) =
        suffix := by
  simp only [firstFieldSuffix, BinaryEncoding.readLengthPrefixedWord_append]

@[simp] private theorem firstFieldSuffix_missing (count : ℕ) :
    firstFieldSuffix (List.replicate count true) = [] := by
  simp only [firstFieldSuffix, BinaryEncoding.readLengthPrefixedWord, readUnaryPrefix_missing]

@[simp] private theorem firstFieldSuffix_truncated
    (payload : List Bool) (extra : ℕ) :
    firstFieldSuffix
      (List.replicate (payload.length + extra + 1) true ++
        false :: payload) = [] := by
  have hshort : ¬ payload.length + extra + 1 ≤ payload.length := by
    omega
  simp only [firstFieldSuffix, BinaryEncoding.readLengthPrefixedWord,
      BinaryEncoding.readUnaryPrefix_replicate,
      hshort, ↓reduceIte]

private theorem suffixDecoderMachine_init (input : List Bool) :
    Turing.initList suffixDecoderMachine input =
      suffixConfiguration 0 input [] [] [] := by
  simp only [suffixDecoderMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq, dite_eq_ite,
      suffixConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

private def suffix_totalTrace (input : List Bool) :
    EvalsToInTime suffixDecoderMachine.step (suffixConfiguration 0 input [] [] [])
      (some (Turing.haltList suffixDecoderMachine
        (firstFieldSuffix input)))
      (3 * input.length + 6) := by
  cases unaryInputSplit input with
  | inl witness =>
      obtain ⟨count, hinput⟩ := witness
      subst input
      have htrace := suffix_missingTrace count
      exact {
        steps := htrace.steps
        evals_in_steps := by
          simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, firstFieldSuffix_missing]
              using
              htrace.evals_in_steps
        steps_le_m := by
          have hsteps := htrace.steps_le_m
          simp only [List.length_replicate]
          omega
      }
  | inr witness =>
      obtain ⟨count, tail, hinput⟩ := witness
      subst input
      by_cases hlen : count ≤ tail.length
      · have hreconstruct := validInput_reconstruct count tail hlen
        rw [hreconstruct]
        have htrace := suffix_validTrace
          (tail.take count) (tail.drop count)
        exact {
          steps := htrace.steps
          evals_in_steps := by
            simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, firstFieldSuffix_valid]
                using htrace.evals_in_steps
          steps_le_m := by
            have hsteps := htrace.steps_le_m
            simp only [List.length_append,
              BinaryEncoding.lengthPrefixedWord_length]
            omega
        }
      · have hshort : tail.length < count := Nat.lt_of_not_ge hlen
        let extra := count - tail.length - 1
        have hcount : count = tail.length + extra + 1 := by
          dsimp [extra]
          omega
        rw [hcount]
        have htrace := suffix_truncatedTrace tail extra
        exact {
          steps := htrace.steps
          evals_in_steps := by
            simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, firstFieldSuffix_truncated]
                using
                htrace.evals_in_steps
          steps_le_m := by
            have hsteps := htrace.steps_le_m
            simp only [List.length_append, List.length_replicate,
              List.length_cons]
            omega
        }

/-- GapCVP reduction support. -/
noncomputable def firstFieldSuffixComputable :
    BitTM
      firstFieldSuffix where
  tm := suffixDecoderMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 3 * Polynomial.X + 6
  outputsFun input := {
    steps := (suffix_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, suffixDecoderMachine_init,
              Option.map_some] using
          (suffix_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (suffix_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq, Polynomial.eval_add,
          Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X, ge_iff_le] using hsteps
  }

/-- GapCVP reduction support. -/
def literalSuffix : List Bool → List Bool :=
  List.tail ∘ firstFieldSuffix

/-- GapCVP reduction support. -/
noncomputable def literalSuffixComputable :
    BitTM
      literalSuffix := by
  exact TMComposition.computableInPolyTime
    firstFieldSuffixComputable dropHeadComputable

@[simp] theorem literalSuffix_valid
    (literal : Literal) (suffix : List Bool) :
    literalSuffix
      (BinaryEncoding.encodeLiteral literal ++ suffix) =
        suffix := by
  rcases literal with ⟨index, sign⟩
  simp only [literalSuffix, BinaryEncoding.encodeLiteral, List.append_assoc, List.cons_append,
      List.nil_append,
      Function.comp_apply, firstFieldSuffix_valid, List.tail_cons]

/-- GapCVP reduction support. -/
def clauseSuffix : List Bool → List Bool :=
  literalSuffix ∘ literalSuffix ∘ literalSuffix

/-- GapCVP reduction support. -/
noncomputable def clauseSuffixComputable :
    BitTM
      clauseSuffix := by
  exact TMComposition.computableInPolyTime
    (TMComposition.computableInPolyTime
      literalSuffixComputable literalSuffixComputable)
    literalSuffixComputable

@[simp] theorem clauseSuffix_valid
    (clause : ThreeClause) (suffix : List Bool) :
    clauseSuffix
      (BinaryEncoding.encodeThreeClause clause ++ suffix) =
        suffix := by
  simp only [clauseSuffix, Function.comp_def, BinaryEncoding.encodeThreeClause, Fin.isValue,
      List.append_assoc,
      Function.comp_apply, literalSuffix_valid]

@[simp] theorem firstFieldSuffix_encodeThreeCNF
    (clauses : ThreeCNF) :
    firstFieldSuffix
      (BinaryEncoding.encodeThreeCNF clauses) =
        clauses.flatMap BinaryEncoding.encodeThreeClause := by
  simp only [BinaryEncoding.encodeThreeCNF, firstFieldSuffix_valid]

end SourceFormulaStructuralDecoder

namespace SourceVariableFormulaDecoder

open Turing GapCVP.SourceFormulaStructuralDecoder

private def variablePrefixLabel (position : Fin 3) : Fin 7 :=
  ⟨position.val, by omega⟩

private def variablePayloadLabel (position : Fin 3) : Fin 7 :=
  ⟨position.val + 3, by omega⟩

/-- Internal support shared across GapCVP continuation modules. -/
def nextLiteralPosition (position : Fin 3) : Fin 3 :=
  if position = 0 then 1 else if position = 1 then 2 else 0

private def variablePrefixStatement (position : Fin 3) :
    Turing.TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 7) (Option Bool) :=
  .peek 0 (fun _ symbol => symbol)
    (.branch (fun symbol => symbol == some true)
      (.pop 0 (fun _ _ => none)
        (.push 1 (fun _ => true)
          (.goto (fun _ => variablePrefixLabel position))))
      (.branch (fun symbol => symbol.isSome)
        (.pop 0 (fun _ _ => none)
          (.goto (fun _ => variablePayloadLabel position)))
        (.peek 1 (fun _ symbol => symbol)
          (.branch (fun symbol => symbol.isSome)
            (.load (fun _ => none) (.goto (fun _ => (6 : Fin 7))))
            (if position = 0 then
              .push 2 (fun _ => true) .halt
            else
              .goto (fun _ => (6 : Fin 7)))))))

private def variablePayloadStatement (position : Fin 3) :
    Turing.TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 7) (Option Bool) :=
  .peek 1 (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome)
      (.peek 0 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.pop 1 (fun _ _ => none)
            (.pop 0 (fun _ _ => none)
              (.goto (fun _ => variablePayloadLabel position))))
          (.goto (fun _ => (6 : Fin 7)))))
      (.peek 0 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.pop 0 (fun _ _ => none)
            (if position = 2 then
              .push 2 (fun _ => true)
                (.goto (fun _ => variablePrefixLabel 0))
            else
              .goto (fun _ => variablePrefixLabel
                (nextLiteralPosition position))))
          (.goto (fun _ => (6 : Fin 7))))))

private abbrev variableClauseMachine : Turing.FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Fin 7
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 7) then variablePrefixStatement 0
    else if phase = (1 : Fin 7) then variablePrefixStatement 1
    else if phase = (2 : Fin 7) then variablePrefixStatement 2
    else if phase = (3 : Fin 7) then variablePayloadStatement 0
    else if phase = (4 : Fin 7) then variablePayloadStatement 1
    else if phase = (5 : Fin 7) then variablePayloadStatement 2
    else
      .peek 0 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.pop 0 (fun _ _ => none) (.goto (fun _ => 6)))
          (.peek 1 (fun _ symbol => symbol)
            (.branch (fun symbol => symbol.isSome)
              (.pop 1 (fun _ _ => none) (.goto (fun _ => 6)))
              (.push 2 (fun _ => false) .halt))))

private def variableConfiguration
    (phase : Fin 7) (input counter : List Bool) (count : ℕ) :
    variableClauseMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, counter, List.replicate count true]

private theorem variable_prefix_true
    (position : Fin 3) (input counter : List Bool) (count : ℕ) :
    variableClauseMachine.step
      (variableConfiguration (variablePrefixLabel position)
        (true :: input) counter count) =
      some (variableConfiguration (variablePrefixLabel position)
        input (true :: counter) count) := by
  fin_cases position <;>
    compactMachineStepTac [variableClauseMachine, variableConfiguration, variablePrefixLabel,
      variablePrefixStatement]

private theorem variable_prefix_delimiter
    (position : Fin 3) (input counter : List Bool) (count : ℕ) :
    variableClauseMachine.step
      (variableConfiguration (variablePrefixLabel position)
        (false :: input) counter count) =
      some (variableConfiguration (variablePayloadLabel position)
        input counter count) := by
  fin_cases position <;>
    compactMachineStepTac [variableClauseMachine, variableConfiguration, variablePrefixLabel,
      variablePayloadLabel, variablePrefixStatement]

private theorem variable_payload_step
    (position : Fin 3) (bit counterBit : Bool)
    (input counter : List Bool) (count : ℕ) :
    variableClauseMachine.step
      (variableConfiguration (variablePayloadLabel position)
        (bit :: input) (counterBit :: counter) count) =
      some (variableConfiguration (variablePayloadLabel position)
        input counter count) := by
  fin_cases position <;> cases bit <;> cases counterBit <;>
    compactMachineStepTac [variableClauseMachine, variableConfiguration, variablePayloadLabel,
      variablePayloadStatement]

private theorem variable_sign_step
    (position : Fin 3) (hposition : position ≠ 2)
    (sign : Bool) (input : List Bool) (count : ℕ) :
    variableClauseMachine.step
      (variableConfiguration (variablePayloadLabel position)
        (sign :: input) [] count) =
      some (variableConfiguration
        (variablePrefixLabel (nextLiteralPosition position))
        input [] count) := by
  fin_cases position <;> cases sign <;>
    first
    | exact (hposition rfl).elim
    | compactMachineStepTac [variableClauseMachine, variableConfiguration,
        variablePrefixLabel, variablePayloadLabel, nextLiteralPosition,
        variablePayloadStatement]

private theorem variable_completeClause_step
    (sign : Bool) (input : List Bool) (count : ℕ) :
    variableClauseMachine.step
      (variableConfiguration (variablePayloadLabel 2)
        (sign :: input) [] count) =
      some (variableConfiguration (variablePrefixLabel 0)
        input [] (count + 1)) := by
  cases sign <;>
    compactMachineStepTac [variableClauseMachine, variableConfiguration,
      variablePrefixLabel, variablePayloadLabel, variablePayloadStatement,
      List.replicate_succ]

private theorem variable_finish_valid (count : ℕ) :
    variableClauseMachine.step
      (variableConfiguration (variablePrefixLabel 0) [] [] count) =
      some (Turing.haltList variableClauseMachine
        (true :: List.replicate count true)) := by
  compactMachineStepTac [variableClauseMachine, variableConfiguration, variablePrefixLabel,
    variablePrefixStatement]

private theorem variable_prefix_unfinished
    (position : Fin 3) (bit : Bool)
    (counter : List Bool) (count : ℕ) :
    variableClauseMachine.step
      (variableConfiguration (variablePrefixLabel position)
        [] (bit :: counter) count) =
      some (variableConfiguration 6 [] (bit :: counter) count) := by
  fin_cases position <;> cases bit <;>
    compactMachineStepTac [variableClauseMachine, variableConfiguration, variablePrefixLabel,
      variablePrefixStatement]

private theorem variable_prefix_incompleteClause
    (position : Fin 3) (hposition : position ≠ 0) (count : ℕ) :
    variableClauseMachine.step
      (variableConfiguration (variablePrefixLabel position)
        [] [] count) =
      some (variableConfiguration 6 [] [] count) := by
  fin_cases position <;>
    simp_all [variableClauseMachine, variableConfiguration,
      variablePrefixLabel, variablePrefixStatement,
      Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
    rfl

private theorem variable_payload_missing
    (position : Fin 3) (counter : List Bool) (count : ℕ) :
    variableClauseMachine.step
      (variableConfiguration (variablePayloadLabel position)
        [] counter count) =
      some (variableConfiguration 6 [] counter count) := by
  fin_cases position <;> cases counter <;>
    compactMachineStepTac [variableClauseMachine, variableConfiguration, variablePayloadLabel,
      variablePayloadStatement]

private theorem variable_failure_drop_input
    (bit : Bool) (input counter : List Bool) (count : ℕ) :
    variableClauseMachine.step
      (variableConfiguration 6 (bit :: input) counter count) =
      some (variableConfiguration 6 input counter count) := by
  cases bit <;> compactMachineStepTac [variableClauseMachine, variableConfiguration]

private theorem variable_failure_drop_counter
    (bit : Bool) (counter : List Bool) (count : ℕ) :
    variableClauseMachine.step
      (variableConfiguration 6 [] (bit :: counter) count) =
      some (variableConfiguration 6 [] counter count) := by
  cases bit <;> compactMachineStepTac [variableClauseMachine, variableConfiguration]

private theorem variable_failure_finish (count : ℕ) :
    variableClauseMachine.step
      (variableConfiguration 6 [] [] count) =
      some (Turing.haltList variableClauseMachine
        (false :: List.replicate count true)) := by
  compactMachineStepTac [variableClauseMachine, variableConfiguration]

private def variable_failureTrace
    (input counter : List Bool) (count : ℕ) :
    EvalsToInTime variableClauseMachine.step (variableConfiguration 6 input counter count)
      (some (Turing.haltList variableClauseMachine
        (false :: List.replicate count true)))
      (input.length + counter.length + 1) := by
  induction input generalizing counter count with
  | cons bit input ih =>
      have hfirst := oneStep _ _ (variable_failure_drop_input bit input counter count)
      have hrest := ih counter count
      have hboth := EvalsToInTime.trans variableClauseMachine.step 1
        (input.length + counter.length + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, Nat.add_comm, Nat.add_left_comm,
          Nat.reduceAdd,
          Nat.add_assoc] using hboth
  | nil =>
      induction counter generalizing count with
      | cons bit counter ih =>
          have hfirst := oneStep _ _ (variable_failure_drop_counter bit counter count)
          have hrest :
              EvalsToInTime variableClauseMachine.step (variableConfiguration 6 [] counter count)
                (some (Turing.haltList variableClauseMachine
                  (false :: List.replicate count true)))
                (counter.length + 1) := by
            simpa only [FinTM2.step, Fin.isValue, List.length_nil, zero_add] using ih count
          have hboth := EvalsToInTime.trans variableClauseMachine.step 1 (counter.length + 1)
            _ _ _ hfirst hrest
          simpa only [FinTM2.step, Fin.isValue, List.length_nil, List.length_cons, zero_add,
              Nat.add_comm,
              Nat.add_left_comm, Nat.reduceAdd] using hboth
      | nil =>
          simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero, zero_add] using
              oneStep _ _ (variable_failure_finish count)

private def variableScanPhase (payload : Bool) (position : Fin 3) : Fin 7 :=
  if payload then variablePayloadLabel position
  else variablePrefixLabel position

private def variableScanOutput :
    List Bool → Bool → Fin 3 → List Bool → ℕ → List Bool
  | [], true, _, _, count => false :: List.replicate count true
  | [], false, position, [], count =>
      if position = 0 then true :: List.replicate count true
      else false :: List.replicate count true
  | [], false, _, _ :: _, count =>
      false :: List.replicate count true
  | bit :: rest, false, position, counter, count =>
      if bit then
        variableScanOutput rest false position (true :: counter) count
      else
        variableScanOutput rest true position counter count
  | _ :: rest, true, position, [], count =>
      variableScanOutput rest false (nextLiteralPosition position) []
        (if position = 2 then count + 1 else count)
  | _ :: rest, true, position, _ :: counter, count =>
      variableScanOutput rest true position counter count

private def variableScanTrace
    (input : List Bool) (payload : Bool) (position : Fin 3)
    (counter : List Bool) (count : ℕ) :
    EvalsToInTime variableClauseMachine.step
      (variableConfiguration (variableScanPhase payload position)
        input counter count)
      (some (Turing.haltList variableClauseMachine
        (variableScanOutput input payload position counter count)))
      (2 * input.length + counter.length + 2) := by
  induction input generalizing payload position counter count with
  | nil =>
      cases payload with
      | false =>
          cases counter with
          | nil =>
              by_cases hposition : position = 0
              · subst position
                have htrace := oneStep _ _ (variable_finish_valid count)
                simpa only [FinTM2.step, Fin.isValue, variableScanPhase, Bool.false_eq_true,
                    ↓reduceIte, variableScanOutput,
                    List.length_nil, mul_zero, add_zero, zero_add] using rebound (newBudget := 2)
                        htrace (by omega)
              · have hfirst := oneStep _ _ (variable_prefix_incompleteClause
                    position hposition count)
                have hcleanup := variable_failureTrace [] [] count
                have hfull := EvalsToInTime.trans
                  variableClauseMachine.step _ _ _ _ _ hfirst hcleanup
                simpa only [FinTM2.step, Fin.isValue, variableScanPhase, Bool.false_eq_true,
                    ↓reduceIte, variableScanOutput,
                    hposition, List.length_nil, mul_zero, add_zero, zero_add] using
                    rebound (newBudget := 2) hfull
                      (by
                        simp only [List.length_nil]
                        omega)
          | cons counterBit counter =>
              have hfirst := oneStep _ _ (variable_prefix_unfinished position
                  counterBit counter count)
              have hcleanup := variable_failureTrace []
                (counterBit :: counter) count
              have hfull := EvalsToInTime.trans variableClauseMachine.step _ _ _ _ _ hfirst
                  hcleanup
              simpa only [FinTM2.step, Fin.isValue, variableScanPhase, Bool.false_eq_true,
                  ↓reduceIte, variableScanOutput,
                  List.length_nil, mul_zero, List.length_cons, zero_add] using
                  rebound (newBudget := counter.length + 3) hfull
                    (by
                      simp only [List.length_nil, List.length_cons]
                      omega)
      | true =>
          have hfirst := oneStep _ _ (variable_payload_missing position counter count)
          have hcleanup := variable_failureTrace [] counter count
          have hfull := EvalsToInTime.trans variableClauseMachine.step _ _ _ _ _ hfirst hcleanup
          simpa only [FinTM2.step, Fin.isValue, variableScanPhase, ↓reduceIte, variableScanOutput,
              List.length_nil,
              mul_zero, zero_add] using
              rebound (newBudget := counter.length + 2) hfull
                (by
                  simp only [List.length_nil]
                  omega)
  | cons bit input ih =>
      cases payload with
      | false =>
          cases bit with
          | false =>
              have hfirst := oneStep _ _ (variable_prefix_delimiter position input counter count)
              have hrest := ih true position counter count
              have hfull := EvalsToInTime.trans variableClauseMachine.step _ _ _ _ _ hfirst hrest
              simpa only [FinTM2.step, Fin.isValue, variableScanPhase, Bool.false_eq_true,
                  ↓reduceIte, variableScanOutput,
                  List.length_cons] using rebound (newBudget := 2 * (input.length + 1) +
                      counter.length + 2) hfull (by omega)
          | true =>
              have hfirst := oneStep _ _ (variable_prefix_true position input counter count)
              have hrest := ih false position (true :: counter) count
              have hfull := EvalsToInTime.trans variableClauseMachine.step _ _ _ _ _ hfirst hrest
              simpa only [FinTM2.step, Fin.isValue, variableScanPhase, Bool.false_eq_true,
                  ↓reduceIte, variableScanOutput,
                  List.length_cons] using
                  rebound (newBudget := 2 * (input.length + 1) + counter.length + 2) hfull
                    (by
                      simp only [List.length_cons]
                      omega)
      | true =>
          cases counter with
          | nil =>
              by_cases hcomplete : position = 2
              · subst position
                have hfirst := oneStep _ _ (variable_completeClause_step bit input count)
                have hrest := ih false 0 [] (count + 1)
                have hfull := EvalsToInTime.trans variableClauseMachine.step _ _ _ _ _ hfirst hrest
                simpa only [FinTM2.step, Fin.isValue, variableScanPhase, ↓reduceIte,
                    variableScanOutput, nextLiteralPosition,
                    Fin.reduceEq, List.length_cons, List.length_nil, add_zero] using
                    rebound (newBudget := 2 * (input.length + 1) + 2) hfull
                      (by
                        simp only [List.length_nil]
                        omega)
              · have hfirst := oneStep _ _ (variable_sign_step position hcomplete
                    bit input count)
                have hrest := ih false
                  (nextLiteralPosition position) [] count
                have hfull := EvalsToInTime.trans variableClauseMachine.step _ _ _ _ _ hfirst hrest
                simpa only [FinTM2.step, Fin.isValue, variableScanPhase, ↓reduceIte,
                    variableScanOutput, hcomplete,
                    List.length_cons, List.length_nil, add_zero] using
                    rebound (newBudget := 2 * (input.length + 1) + 2) hfull
                      (by
                        simp only [List.length_nil]
                        omega)
          | cons counterBit counter =>
              have hfirst := oneStep _ _ (variable_payload_step position bit counterBit
                  input counter count)
              have hrest := ih true position counter count
              have hfull := EvalsToInTime.trans variableClauseMachine.step _ _ _ _ _ hfirst hrest
              simpa only [FinTM2.step, Fin.isValue, variableScanPhase, ↓reduceIte,
                  variableScanOutput,
                  List.length_cons] using rebound (newBudget := 2 * (input.length + 1) +
                      (counter.length + 1) + 2) hfull (by omega)

private theorem variableClauseMachine_init (input : List Bool) :
    Turing.initList variableClauseMachine input =
      variableConfiguration (variablePrefixLabel 0) input [] 0 := by
  simp only [variableClauseMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq, dite_eq_ite,
      variableConfiguration, variablePrefixLabel, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.zero_eta,
          List.replicate_zero]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- GapCVP reduction support. -/
def variableClauseBodyOutput (input : List Bool) : List Bool :=
  variableScanOutput input false 0 [] 0

/-- GapCVP reduction support. -/
noncomputable def variableClauseBodyComputable :
    BitTM
      variableClauseBodyOutput where
  tm := variableClauseMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 2
  outputsFun input := {
    steps := (variableScanTrace input false 0 [] 0).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, variableScanPhase,
          Bool.false_eq_true, ↓dreduceIte,
          List.length_nil, Nat.add_zero, Equiv.invFun_as_coe, Equiv.refl_symm, Equiv.coe_refl,
              bitEncoding, id_eq,
          List.map_id_fun, variableClauseMachine_init, variableClauseBodyOutput, Option.map_some,
              ↓reduceIte] using
          (variableScanTrace input false 0 [] 0).evals_in_steps
    steps_le_m := by
      have hsteps := (variableScanTrace input false 0 [] 0).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, Nat.add_zero, bitEncoding, id_eq,
          Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, ge_iff_le, add_zero]
              using hsteps
  }

private theorem variableScanOutput_prefix
    (length : ℕ) (tail counter : List Bool)
    (position : Fin 3) (count : ℕ) :
    variableScanOutput
      (List.replicate length true ++ false :: tail)
      false position counter count =
      variableScanOutput tail true position
        (List.replicate length true ++ counter) count := by
  induction length generalizing counter with
  | zero =>
      simp only [List.replicate_zero, List.nil_append, variableScanOutput, Bool.false_eq_true,
          ↓reduceIte]
  | succ length ih =>
      simp only [List.replicate_succ, List.cons_append, variableScanOutput, ↓reduceIte, ih,
          SourceStructuralDecoder.replicate_true_append_cons]

private theorem variableScanOutput_payload
    (payload tail counter : List Bool)
    (position : Fin 3) (count : ℕ) :
    variableScanOutput (payload ++ tail) true position
      (List.replicate payload.length true ++ counter) count =
      variableScanOutput tail true position counter count := by
  induction payload generalizing counter with
  | nil =>
      simp only [List.nil_append, List.length_nil, List.replicate_zero]
  | cons bit payload ih =>
      simp only [List.cons_append, List.length_cons, List.replicate_succ, variableScanOutput, ih]

private theorem variableScanOutput_literal
    (literal : Literal) (suffix : List Bool)
    (position : Fin 3) (count : ℕ) :
    variableScanOutput
      (BinaryEncoding.encodeLiteral literal ++ suffix)
      false position [] count =
      variableScanOutput suffix false
        (nextLiteralPosition position) []
        (if position = 2 then count + 1 else count) := by
  rcases literal with ⟨index, sign⟩
  unfold BinaryEncoding.encodeLiteral
  rw [BinaryEncoding.lengthPrefixedWord]
  simp only [List.append_assoc, List.cons_append]
  rw [variableScanOutput_prefix]
  rw [variableScanOutput_payload]
  simp only [variableScanOutput, List.nil_append, Fin.isValue]

private theorem variableScanOutput_clause
    (clause : ThreeClause) (suffix : List Bool) (count : ℕ) :
    variableScanOutput
      (BinaryEncoding.encodeThreeClause clause ++ suffix)
      false 0 [] count =
      variableScanOutput suffix false 0 [] (count + 1) := by
  unfold BinaryEncoding.encodeThreeClause
  simp only [List.append_assoc]
  rw [variableScanOutput_literal,
    variableScanOutput_literal, variableScanOutput_literal]
  simp only [nextLiteralPosition, Fin.isValue, ↓reduceIte, one_ne_zero, Fin.reduceEq]

private theorem variableScanOutput_clauses
    (clauses : ThreeCNF) (suffix : List Bool) (count : ℕ) :
    variableScanOutput
      (clauses.flatMap BinaryEncoding.encodeThreeClause ++
        suffix)
      false 0 [] count =
      variableScanOutput suffix false 0 []
        (count + clauses.length) := by
  induction clauses generalizing count with
  | nil =>
      simp only [List.flatMap_nil, List.nil_append, Fin.isValue, List.length_nil, add_zero]
  | cons clause clauses ih =>
      simp only [List.flatMap_cons, List.length_cons]
      rw [List.append_assoc, variableScanOutput_clause, ih]
      congr 1
      omega

@[simp] theorem variableClauseBodyOutput_valid
    (clauses : ThreeCNF) :
    variableClauseBodyOutput
      (clauses.flatMap BinaryEncoding.encodeThreeClause) =
        true :: List.replicate clauses.length true := by
  unfold variableClauseBodyOutput
  have hscan := variableScanOutput_clauses clauses [] 0
  simpa only [Fin.isValue, List.append_nil, variableScanOutput, ↓reduceIte, zero_add] using hscan

/-- GapCVP reduction support. -/
noncomputable def variableFormulaBodyComputable :
    BitTM
      (variableClauseBodyOutput ∘ firstFieldSuffix) :=
  TMComposition.computableInPolyTime
    firstFieldSuffixComputable variableClauseBodyComputable

end SourceVariableFormulaDecoder

namespace FormulaTuringTM

open Turing GapCVP.SourceVariableFormulaDecoder

/-- Internal support shared across GapCVP continuation modules. -/
def binaryStackValue : List Bool → ℕ
  | [] => 0
  | bit :: rest => (if bit then 1 else 0) + 2 * binaryStackValue rest

private theorem binaryStackValue_encodePosNum (value : PosNum) :
    binaryStackValue (Computability.encodePosNum value) =
      (value : ℕ) := by
  induction value with
  | one =>
      simp only [Computability.encodePosNum, binaryStackValue, ↓reduceIte, mul_zero, add_zero,
          PosNum.cast_one']
  | bit0 value ih =>
      simp only [Computability.encodePosNum, binaryStackValue, Bool.false_eq_true, ↓reduceIte, ih,
          zero_add,
          PosNum.cast_bit0]
      omega
  | bit1 value ih =>
      simp only [Computability.encodePosNum, binaryStackValue, ↓reduceIte, ih, PosNum.cast_bit1]
      omega

private theorem binaryStackValue_encodeNum (value : Num) :
    binaryStackValue (Computability.encodeNum value) =
      (value : ℕ) := by
  cases value with
  | zero =>
      rfl
  | pos value =>
      simpa only [Computability.encodeNum, Num.cast_pos] using binaryStackValue_encodePosNum value

/-- Internal support shared across GapCVP continuation modules. -/
theorem binaryStackValue_encodeNat (value : ℕ) :
    binaryStackValue (Computability.encodeNat value) = value := by
  change binaryStackValue (Computability.encodeNum (value : Num)) =
    value
  rw [binaryStackValue_encodeNum]
  exact Num.to_of_nat value

/-- Internal support shared across GapCVP continuation modules. -/
def binaryStackDecrement : List Bool → Option (List Bool)
  | [] => none
  | true :: rest => some (false :: rest)
  | false :: rest =>
      match binaryStackDecrement rest with
      | none => none
      | some remaining => some (true :: remaining)

/-- Internal support shared across GapCVP continuation modules. -/
theorem binaryStackDecrement_value
    (bits remaining : List Bool)
    (hdecrement : binaryStackDecrement bits = some remaining) :
    binaryStackValue remaining + 1 = binaryStackValue bits := by
  induction bits generalizing remaining with
  | nil =>
      simp only [binaryStackDecrement, reduceCtorEq] at hdecrement
  | cons bit bits ih =>
      cases bit with
      | true =>
          simp only [binaryStackDecrement, Option.some.injEq] at hdecrement
          subst remaining
          simp only [binaryStackValue, Bool.false_eq_true, ↓reduceIte, zero_add]
          omega
      | false =>
          cases hrest : binaryStackDecrement bits with
          | none =>
              simp only [binaryStackDecrement, hrest, reduceCtorEq] at hdecrement
          | some rest =>
              simp only [binaryStackDecrement, hrest, Option.some.injEq] at hdecrement
              subst remaining
              have hvalue := ih rest hrest
              simp only [binaryStackValue, ↓reduceIte, Bool.false_eq_true, zero_add]
              omega

/-- Internal support shared across GapCVP continuation modules. -/
theorem binaryStackValue_eq_zero_iff
    (bits : List Bool) :
    binaryStackValue bits = 0 ↔ ∀ bit ∈ bits, bit = false := by
  induction bits with
  | nil =>
      simp only [binaryStackValue, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | cons bit bits ih =>
      cases bit <;>
        simp [binaryStackValue, ih]

/-- GapCVP reduction support. -/
def canonicalPrefixLabel (position : Fin 3) : Fin 17 :=
  ⟨position.val + 4, by omega⟩

/-- Internal support shared across GapCVP continuation modules. -/
def canonicalPayloadLabel (position : Fin 3) : Fin 17 :=
  ⟨position.val + 7, by omega⟩

/-- Internal support shared across GapCVP continuation modules. -/
def canonicalClearLabel (position : Fin 3) : Fin 17 :=
  ⟨position.val + 10, by omega⟩

private def canonicalSignStatement (position : Fin 3) :
    Turing.TM2.Stmt (fun _ : Fin 6 => Bool) (Fin 17) (Option Bool) :=
  .peek 0 (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome)
      (.pop 0 (fun _ _ => none)
        (if position = 2 then
          .goto (fun _ => (13 : Fin 17))
        else
          .goto (fun _ => canonicalPrefixLabel
            (nextLiteralPosition position))))
      (.goto (fun _ => (15 : Fin 17))))

/-- GapCVP reduction support. -/
def canonicalPrefixStatement (position : Fin 3) :
    Turing.TM2.Stmt (fun _ : Fin 6 => Bool) (Fin 17) (Option Bool) :=
  .peek 0 (fun _ symbol => symbol)
    (.branch (fun symbol => symbol == some true)
      (.pop 0 (fun _ _ => none)
        (.push 1 (fun _ => true)
          (.goto (fun _ => canonicalPrefixLabel position))))
      (.branch (fun symbol => symbol.isSome)
        (.pop 0 (fun _ _ => none)
          (.goto (fun _ => canonicalPayloadLabel position)))
        (.peek 1 (fun _ symbol => symbol)
          (.branch (fun symbol => symbol.isSome)
            (.load (fun _ => none) (.goto (fun _ => (15 : Fin 17))))
            (if position = 0 then
              .goto (fun _ => (16 : Fin 17))
            else
              .goto (fun _ => (15 : Fin 17)))))))

/-- GapCVP reduction support. -/
def canonicalPayloadStatement (position : Fin 3) :
    Turing.TM2.Stmt (fun _ : Fin 6 => Bool) (Fin 17) (Option Bool) :=
  .peek 1 (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome)
      (.peek 0 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.pop 1 (fun state _ => state)
            (.pop 0 (fun state _ => state)
              (.push 2 (fun state => state.getD false)
                (.load (fun _ => none)
                  (.goto (fun _ => canonicalPayloadLabel position))))))
          (.goto (fun _ => (15 : Fin 17)))))
      (.peek 2 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol == some true)
          (.load (fun _ => none)
            (.goto (fun _ => canonicalClearLabel position)))
          (.branch (fun symbol => symbol.isSome)
            (.load (fun _ => none)
              (.goto (fun _ => (15 : Fin 17))))
            (canonicalSignStatement position)))))

/-- GapCVP reduction support. -/
def canonicalClearStatement (position : Fin 3) :
    Turing.TM2.Stmt (fun _ : Fin 6 => Bool) (Fin 17) (Option Bool) :=
  .peek 2 (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome)
      (.pop 2 (fun _ _ => none)
        (.goto (fun _ => canonicalClearLabel position)))
      (canonicalSignStatement position))

/-- GapCVP reduction support. -/
abbrev canonicalFormulaMachine : Turing.FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 5
  Γ _ := Bool
  Λ := Fin 17
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 17) then
      .peek 0 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol == some true)
          (.pop 0 (fun _ _ => none)
            (.push 1 (fun _ => true) (.goto (fun _ => 0))))
          (.branch (fun symbol => symbol.isSome)
            (.pop 0 (fun _ _ => none) (.goto (fun _ => 1)))
            (.goto (fun _ => 15))))
    else if phase = (1 : Fin 17) then
      .peek 1 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.peek 0 (fun _ symbol => symbol)
            (.branch (fun symbol => symbol.isSome)
              (.pop 1 (fun state _ => state)
                (.pop 0 (fun state _ => state)
                  (.push 2 (fun state => state.getD false)
                    (.load (fun _ => none) (.goto (fun _ => 1))))))
              (.goto (fun _ => 15))))
          (.goto (fun _ => 2)))
    else if phase = (2 : Fin 17) then
      .peek 2 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol == some true)
          (.load (fun _ => none) (.goto (fun _ => 3)))
          (.branch (fun symbol => symbol.isSome)
            (.load (fun _ => none) (.goto (fun _ => 15)))
            (.goto (fun _ => canonicalPrefixLabel 0))))
    else if phase = (3 : Fin 17) then
      .peek 2 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.pop 2 (fun state _ => state)
            (.push 3 (fun state => state.getD false)
              (.load (fun _ => none) (.goto (fun _ => 3)))))
          (.goto (fun _ => canonicalPrefixLabel 0)))
    else if phase = (4 : Fin 17) then canonicalPrefixStatement 0
    else if phase = (5 : Fin 17) then canonicalPrefixStatement 1
    else if phase = (6 : Fin 17) then canonicalPrefixStatement 2
    else if phase = (7 : Fin 17) then canonicalPayloadStatement 0
    else if phase = (8 : Fin 17) then canonicalPayloadStatement 1
    else if phase = (9 : Fin 17) then canonicalPayloadStatement 2
    else if phase = (10 : Fin 17) then canonicalClearStatement 0
    else if phase = (11 : Fin 17) then canonicalClearStatement 1
    else if phase = (12 : Fin 17) then canonicalClearStatement 2
    else if phase = (13 : Fin 17) then
      .peek 3 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol == some true)
          (.pop 3 (fun _ _ => none)
            (.push 3 (fun _ => false) (.goto (fun _ => 14))))
          (.branch (fun symbol => symbol.isSome)
            (.pop 3 (fun _ _ => none)
              (.push 4 (fun _ => true) (.goto (fun _ => 13))))
            (.goto (fun _ => 15))))
    else if phase = (14 : Fin 17) then
      .peek 4 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.pop 4 (fun _ _ => none)
            (.push 3 (fun _ => true) (.goto (fun _ => 14))))
          (.goto (fun _ => canonicalPrefixLabel 0)))
    else if phase = (15 : Fin 17) then
      .peek 0 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.pop 0 (fun _ _ => none) (.goto (fun _ => 15)))
          (.peek 1 (fun _ symbol => symbol)
            (.branch (fun symbol => symbol.isSome)
              (.pop 1 (fun _ _ => none) (.goto (fun _ => 15)))
              (.peek 2 (fun _ symbol => symbol)
                (.branch (fun symbol => symbol.isSome)
                  (.pop 2 (fun _ _ => none) (.goto (fun _ => 15)))
                  (.peek 3 (fun _ symbol => symbol)
                    (.branch (fun symbol => symbol.isSome)
                      (.pop 3 (fun _ _ => none) (.goto (fun _ => 15)))
                      (.peek 4 (fun _ symbol => symbol)
                        (.branch (fun symbol => symbol.isSome)
                          (.pop 4 (fun _ _ => none)
                            (.goto (fun _ => 15)))
                          (.push 5 (fun _ => false) .halt))))))))))
    else
      .peek 3 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol == some true)
          (.load (fun _ => none) (.goto (fun _ => 15)))
          (.branch (fun symbol => symbol.isSome)
            (.pop 3 (fun _ _ => none) (.goto (fun _ => 16)))
            (.push 5 (fun _ => true) .halt)))

/-- GapCVP reduction support. -/
def canonicalConfiguration
    (phase : Fin 17)
    (input counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, counter, field, binary, borrow, output]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_header_prefix_true
    (input counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 0 (true :: input)
        counter field binary borrow output) =
      some (canonicalConfiguration 0 input
        (true :: counter) field binary borrow output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

private theorem canonical_header_prefix_delimiter
    (input counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 0 (false :: input)
        counter field binary borrow output) =
      some (canonicalConfiguration 1 input
        counter field binary borrow output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_header_prefix_missing
    (counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 0 []
        counter field binary borrow output) =
      some (canonicalConfiguration 15 []
        counter field binary borrow output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_header_payload_step
    (bit : Bool) (input counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 1 (bit :: input)
        (true :: counter) field binary borrow output) =
      some (canonicalConfiguration 1 input
        counter (bit :: field) binary borrow output) := by
  cases bit <;> compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_header_payload_missing
    (counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 1 [] (true :: counter)
        field binary borrow output) =
      some (canonicalConfiguration 15 [] (true :: counter)
        field binary borrow output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_header_payload_complete
    (input field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 1 input []
        field binary borrow output) =
      some (canonicalConfiguration 2 input []
        field binary borrow output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_header_check_true
    (input field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 2 input []
        (true :: field) binary borrow output) =
      some (canonicalConfiguration 3 input []
        (true :: field) binary borrow output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_header_check_false
    (input field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 2 input []
        (false :: field) binary borrow output) =
      some (canonicalConfiguration 15 input []
        (false :: field) binary borrow output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_header_check_zero
    (input binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 2 input []
        [] binary borrow output) =
      some (canonicalConfiguration (canonicalPrefixLabel 0) input []
        [] binary borrow output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration, canonicalPrefixLabel]

private theorem canonical_header_reverse_step
    (bit : Bool) (input field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 3 input []
        (bit :: field) binary borrow output) =
      some (canonicalConfiguration 3 input []
        field (bit :: binary) borrow output) := by
  cases bit <;> compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

private theorem canonical_header_reverse_complete
    (input binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 3 input []
        [] binary borrow output) =
      some (canonicalConfiguration (canonicalPrefixLabel 0) input []
        [] binary borrow output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration, canonicalPrefixLabel]

private theorem canonical_borrow_zero
    (input counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 13 input counter field
        (false :: binary) borrow output) =
      some (canonicalConfiguration 13 input counter field
        binary (true :: borrow) output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

private theorem canonical_borrow_one
    (input counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 13 input counter field
        (true :: binary) borrow output) =
      some (canonicalConfiguration 14 input counter field
        (false :: binary) borrow output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

private theorem canonical_borrow_exhausted
    (input counter field borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 13 input counter field
        [] borrow output) =
      some (canonicalConfiguration 15 input counter field
        [] borrow output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

private theorem canonical_borrow_restore_step
    (bit : Bool) (input counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 14 input counter field
        binary (bit :: borrow) output) =
      some (canonicalConfiguration 14 input counter field
        (true :: binary) borrow output) := by
  cases bit <;> compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

private theorem canonical_borrow_restore_complete
    (input counter field binary output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 14 input counter field
        binary [] output) =
      some (canonicalConfiguration (canonicalPrefixLabel 0)
        input counter field binary [] output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration, canonicalPrefixLabel]

private theorem canonical_zeroCheck_false
    (input counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 16 input counter field
        (false :: binary) borrow output) =
      some (canonicalConfiguration 16 input counter field
        binary borrow output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

private theorem canonical_zeroCheck_true
    (input counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 16 input counter field
        (true :: binary) borrow output) =
      some (canonicalConfiguration 15 input counter field
        (true :: binary) borrow output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

private theorem canonical_zeroCheck_finish :
    canonicalFormulaMachine.step
      (canonicalConfiguration 16 [] [] [] [] [] []) =
      some (Turing.haltList canonicalFormulaMachine [true]) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_literal_prefix_true
    (position : Fin 3)
    (input counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalPrefixLabel position)
        (true :: input) counter field binary borrow output) =
      some (canonicalConfiguration (canonicalPrefixLabel position)
        input (true :: counter) field binary borrow output) := by
  fin_cases position <;>
    compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration,
        canonicalPrefixLabel,
      canonicalPrefixStatement]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_literal_prefix_delimiter
    (position : Fin 3)
    (input counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalPrefixLabel position)
        (false :: input) counter field binary borrow output) =
      some (canonicalConfiguration (canonicalPayloadLabel position)
        input counter field binary borrow output) := by
  fin_cases position <;>
    compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration,
        canonicalPrefixLabel,
      canonicalPayloadLabel, canonicalPrefixStatement]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_literal_payload_step
    (position : Fin 3) (bit : Bool)
    (input counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalPayloadLabel position)
        (bit :: input) (true :: counter)
        field binary borrow output) =
      some (canonicalConfiguration (canonicalPayloadLabel position)
        input counter (bit :: field) binary borrow output) := by
  fin_cases position <;> cases bit <;>
    compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration,
      canonicalPayloadLabel, canonicalPayloadStatement]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_literal_payload_missing
    (position : Fin 3)
    (counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalPayloadLabel position)
        [] (true :: counter) field binary borrow output) =
      some (canonicalConfiguration 15 []
        (true :: counter) field binary borrow output) := by
  fin_cases position <;>
    compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration,
      canonicalPayloadLabel, canonicalPayloadStatement]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_literal_field_true
    (position : Fin 3)
    (input field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalPayloadLabel position)
        input [] (true :: field) binary borrow output) =
      some (canonicalConfiguration (canonicalClearLabel position)
        input [] (true :: field) binary borrow output) := by
  fin_cases position <;>
    compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration,
      canonicalPayloadLabel, canonicalClearLabel, canonicalPayloadStatement]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_literal_field_false
    (position : Fin 3)
    (input field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalPayloadLabel position)
        input [] (false :: field) binary borrow output) =
      some (canonicalConfiguration 15
        input [] (false :: field) binary borrow output) := by
  fin_cases position <;>
    compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration,
      canonicalPayloadLabel, canonicalPayloadStatement]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_literal_clear_step
    (position : Fin 3) (bit : Bool)
    (input field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalClearLabel position)
        input [] (bit :: field) binary borrow output) =
      some (canonicalConfiguration (canonicalClearLabel position)
        input [] field binary borrow output) := by
  fin_cases position <;> cases bit <;>
    compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration, canonicalClearLabel,
      canonicalClearStatement]

private theorem canonical_clear_sign_step
    (position : Fin 3) (hposition : position ≠ 2)
    (sign : Bool) (input binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalClearLabel position)
        (sign :: input) [] [] binary borrow output) =
      some (canonicalConfiguration
        (canonicalPrefixLabel (nextLiteralPosition position))
        input [] [] binary borrow output) := by
  fin_cases position <;> cases sign <;>
    first
    | exact (hposition rfl).elim
    | compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration,
        canonicalClearLabel, canonicalPrefixLabel, canonicalClearStatement,
        canonicalSignStatement, nextLiteralPosition]

private theorem canonical_clear_completeClause
    (sign : Bool) (input binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalClearLabel 2)
        (sign :: input) [] [] binary borrow output) =
      some (canonicalConfiguration 13
        input [] [] binary borrow output) := by
  cases sign <;>
    compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration, canonicalClearLabel,
      canonicalClearStatement, canonicalSignStatement]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_zero_field_sign_step
    (position : Fin 3) (hposition : position ≠ 2)
    (sign : Bool) (input binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalPayloadLabel position)
        (sign :: input) [] [] binary borrow output) =
      some (canonicalConfiguration
        (canonicalPrefixLabel (nextLiteralPosition position))
        input [] [] binary borrow output) := by
  fin_cases position <;> cases sign <;>
    first
    | exact (hposition rfl).elim
    | compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration,
        canonicalPayloadLabel, canonicalPrefixLabel, canonicalPayloadStatement,
        canonicalSignStatement, nextLiteralPosition]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_zero_field_completeClause
    (sign : Bool) (input binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalPayloadLabel 2)
        (sign :: input) [] [] binary borrow output) =
      some (canonicalConfiguration 13
        input [] [] binary borrow output) := by
  cases sign <;>
    compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration,
      canonicalPayloadLabel, canonicalPayloadStatement, canonicalSignStatement]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_body_finish
    (binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalPrefixLabel 0)
        [] [] [] binary borrow output) =
      some (canonicalConfiguration 16 [] [] []
        binary borrow output) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration, canonicalPrefixLabel,
    canonicalPrefixStatement]

private def canonical_borrowZerosTrace
    (zeros : ℕ) (tail input counter field borrow output : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 13 input counter field
        (List.replicate zeros false ++ true :: tail) borrow output)
      (some (canonicalConfiguration 14 input counter field
        (false :: tail) (List.replicate zeros true ++ borrow) output))
      (zeros + 1) := by
  induction zeros generalizing borrow with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (canonical_borrow_one input counter field tail borrow output)
  | succ zeros ih =>
      have hfirst := oneStep _ _ (canonical_borrow_zero input counter field
          (List.replicate zeros false ++ true :: tail)
          borrow output)
      have hrest := ih (true :: borrow)
      have hboth := EvalsToInTime.trans canonicalFormulaMachine.step 1 (zeros + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hboth

private def canonical_restoreTrace
    (zeros : ℕ)
    (input counter field binary output : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 14 input counter field
        binary (List.replicate zeros true) output)
      (some (canonicalConfiguration (canonicalPrefixLabel 0)
        input counter field
        (List.replicate zeros true ++ binary) [] output))
      (zeros + 1) := by
  induction zeros generalizing binary with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (canonical_borrow_restore_complete input counter field binary output)
  | succ zeros ih =>
      have hfirst := oneStep _ _ (canonical_borrow_restore_step true input counter field
          binary (List.replicate zeros true) output)
      have hrest := ih (true :: binary)
      have hboth := EvalsToInTime.trans canonicalFormulaMachine.step 1 (zeros + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hboth

private def canonical_decrementTrace
    (zeros : ℕ)
    (tail input counter field output : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 13 input counter field
        (List.replicate zeros false ++ true :: tail) [] output)
      (some (canonicalConfiguration (canonicalPrefixLabel 0)
        input counter field
        (List.replicate zeros true ++ false :: tail) [] output))
      (2 * zeros + 2) := by
  have hborrow :
      EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 13 input counter field
          (List.replicate zeros false ++ true :: tail) [] output)
        (some (canonicalConfiguration 14 input counter field
          (false :: tail) (List.replicate zeros true) output))
        (zeros + 1) := by
    simpa only [FinTM2.step, Fin.isValue, List.append_nil] using
        canonical_borrowZerosTrace zeros tail input counter field [] output
  have hrestore := canonical_restoreTrace zeros
    input counter field (false :: tail) output
  have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hborrow hrestore
  exact {
    steps := hfull.steps
    evals_in_steps := hfull.evals_in_steps
    steps_le_m := by
      have hsteps := hfull.steps_le_m
      omega
  }

/-- Internal support shared across GapCVP continuation modules. -/
theorem binaryStackDecrement_replicate
    (zeros : ℕ) (tail : List Bool) :
    binaryStackDecrement
      (List.replicate zeros false ++ true :: tail) =
        some (List.replicate zeros true ++ false :: tail) := by
  induction zeros with
  | zero =>
      rfl
  | succ zeros ih =>
      simp only [List.replicate_succ, List.cons_append, binaryStackDecrement, ih]

private theorem canonical_failure_drop_input
    (bit : Bool)
    (input counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 15 (bit :: input)
        counter field binary borrow output) =
      some (canonicalConfiguration 15 input
        counter field binary borrow output) := by
  cases bit <;> compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

private theorem canonical_failure_drop_counter
    (bit : Bool)
    (counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 15 []
        (bit :: counter) field binary borrow output) =
      some (canonicalConfiguration 15 []
        counter field binary borrow output) := by
  cases bit <;> compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

private theorem canonical_failure_drop_field
    (bit : Bool) (field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 15 [] []
        (bit :: field) binary borrow output) =
      some (canonicalConfiguration 15 [] []
        field binary borrow output) := by
  cases bit <;> compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

private theorem canonical_failure_drop_binary
    (bit : Bool) (binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 15 [] [] []
        (bit :: binary) borrow output) =
      some (canonicalConfiguration 15 [] [] []
        binary borrow output) := by
  cases bit <;> compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

private theorem canonical_failure_drop_borrow
    (bit : Bool) (borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 15 [] [] [] []
        (bit :: borrow) output) =
      some (canonicalConfiguration 15 [] [] [] []
        borrow output) := by
  cases bit <;> compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

private theorem canonical_failure_finish (output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration 15 [] [] [] [] [] output) =
      some (Turing.haltList canonicalFormulaMachine
        (false :: output)) := by
  compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
def canonicalFailureTrace
    (input counter field binary borrow output : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 15 input
        counter field binary borrow output)
      (some (Turing.haltList canonicalFormulaMachine
        (false :: output)))
      (input.length + counter.length + field.length +
        binary.length + borrow.length + 1) := by
  induction input generalizing counter field binary borrow output with
  | cons bit input ih =>
      have hfirst := oneStep _ _ (canonical_failure_drop_input
          bit input counter field binary borrow output)
      have hrest := ih counter field binary borrow output
      have hboth := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, Nat.add_comm, Nat.add_left_comm,
          Nat.reduceAdd,
          Nat.add_assoc] using hboth
  | nil =>
      induction counter generalizing field binary borrow output with
      | cons bit counter ih =>
          have hfirst := oneStep _ _ (canonical_failure_drop_counter
              bit counter field binary borrow output)
          have hrest := ih field binary borrow output
          have hboth := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hfirst hrest
          simpa only [FinTM2.step, Fin.isValue, List.length_nil, List.length_cons, zero_add,
              Nat.add_comm,
              Nat.add_left_comm, Nat.reduceAdd, Nat.add_assoc] using hboth
      | nil =>
          induction field generalizing binary borrow output with
          | cons bit field ih =>
              have hfirst := oneStep _ _ (canonical_failure_drop_field
                  bit field binary borrow output)
              have hrest := ih binary borrow output
              have hboth := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hfirst hrest
              simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero, List.length_cons,
                  zero_add, Nat.add_comm,
                  Nat.add_left_comm, Nat.reduceAdd, Nat.add_assoc] using hboth
          | nil =>
              induction binary generalizing borrow output with
              | cons bit binary ih =>
                  have hfirst := oneStep _ _
                    (canonical_failure_drop_binary bit binary borrow output)
                  have hrest := ih borrow output
                  have hboth := EvalsToInTime.trans
                    canonicalFormulaMachine.step _ _ _ _ _ hfirst hrest
                  simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero,
                      List.length_cons, zero_add, Nat.add_comm,
                      Nat.add_left_comm, Nat.reduceAdd, Nat.add_assoc] using hboth
              | nil =>
                  induction borrow generalizing output with
                  | cons bit borrow ih =>
                      have hfirst := oneStep _ _ (canonical_failure_drop_borrow bit borrow output)
                      have hrest := ih output
                      have hboth := EvalsToInTime.trans
                        canonicalFormulaMachine.step _ _ _ _ _ hfirst hrest
                      simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero,
                          List.length_cons, zero_add, Nat.add_comm,
                          Nat.add_left_comm, Nat.reduceAdd] using hboth
                  | nil =>
                      simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero, zero_add]
                          using
                          oneStep _ _ (canonical_failure_finish output)

/-- Internal support shared across GapCVP continuation modules. -/
def canonicalZeroTrace (zeros : ℕ) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 16 [] [] []
        (List.replicate zeros false) [] [])
      (some (Turing.haltList canonicalFormulaMachine [true]))
      (zeros + 1) := by
  induction zeros with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, zero_add] using
          oneStep _ _ canonical_zeroCheck_finish
  | succ zeros ih =>
      have hfirst := oneStep _ _ (canonical_zeroCheck_false [] [] []
          (List.replicate zeros false) [] [])
      have hboth := EvalsToInTime.trans canonicalFormulaMachine.step 1 (zeros + 1)
        _ _ _ hfirst ih
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, Nat.add_assoc, Nat.reduceAdd]
          using hboth

end FormulaTuringTM

namespace FormulaCert

open Turing GapCVP.SourceVariableFormulaDecoder GapCVP.FormulaTuringTM

/-- Internal support shared across GapCVP continuation modules. -/
def isCanonicalBinaryWord (word : List Bool) : Bool :=
  match word.reverse with
  | [] => true
  | true :: _ => true
  | false :: _ => false

private theorem encodePosNum_canonical (number : PosNum) :
    isCanonicalBinaryWord
      (Computability.encodePosNum number) = true := by
  induction number with
  | one =>
      rfl
  | bit0 number ih =>
      unfold isCanonicalBinaryWord at ih ⊢
      simp only [Computability.encodePosNum, List.reverse_cons]
      cases hreverse :
        (Computability.encodePosNum number).reverse with
      | nil =>
          have hnonempty := Computability.encodePosNum_nonempty number
          have hempty : Computability.encodePosNum number = [] := by
            simpa only [List.reverse_reverse, List.reverse_nil] using congrArg List.reverse
                hreverse
          exact (hnonempty hempty).elim
      | cons head tail =>
          cases head with
          | false =>
              simp only [hreverse, Bool.false_eq_true] at ih
          | true =>
              simp only [List.cons_append]
  | bit1 number ih =>
      unfold isCanonicalBinaryWord at ih ⊢
      simp only [Computability.encodePosNum, List.reverse_cons]
      cases hreverse :
        (Computability.encodePosNum number).reverse with
      | nil =>
          have hnonempty := Computability.encodePosNum_nonempty number
          have hempty : Computability.encodePosNum number = [] := by
            simpa only [List.reverse_reverse, List.reverse_nil] using congrArg List.reverse
                hreverse
          exact (hnonempty hempty).elim
      | cons head tail =>
          cases head with
          | false =>
              simp only [hreverse, Bool.false_eq_true] at ih
          | true =>
              simp only [List.cons_append]

/-- Internal support shared across GapCVP continuation modules. -/
theorem encodeNat_canonical (number : ℕ) :
    isCanonicalBinaryWord (Computability.encodeNat number) = true := by
  change isCanonicalBinaryWord
    (Computability.encodeNum (number : Num)) = true
  cases hnum : (number : Num) with
  | zero =>
      simp only [isCanonicalBinaryWord, Computability.encodeNum, List.reverse_nil]
  | pos positive =>
      simpa only [Computability.encodeNum] using encodePosNum_canonical positive

/-- Internal support shared across GapCVP continuation modules. -/
def canonicalHeaderPrefixTrace
    (length : ℕ)
    (tail counter field binary borrow output : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 0
        (List.replicate length true ++ false :: tail)
        counter field binary borrow output)
      (some (canonicalConfiguration 1 tail
        (List.replicate length true ++ counter)
        field binary borrow output))
      (length + 1) := by
  induction length generalizing counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (canonical_header_prefix_delimiter tail counter field binary borrow output)
  | succ length ih =>
      have hfirst := oneStep _ _ (canonical_header_prefix_true
          (List.replicate length true ++ false :: tail)
          counter field binary borrow output)
      have hrest := ih (true :: counter)
      have hboth := EvalsToInTime.trans canonicalFormulaMachine.step 1 (length + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hboth

/-- Internal support shared across GapCVP continuation modules. -/
def canonicalHeaderCopyTrace
    (header suffix field binary borrow output : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 1 (header ++ suffix)
        (List.replicate header.length true)
        field binary borrow output)
      (some (canonicalConfiguration 1 suffix []
        (header.reverse ++ field) binary borrow output))
      header.length := by
  induction header generalizing field with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.nil_append, List.length_nil, List.replicate_zero,
          List.reverse_nil] using
          EvalsToInTime.refl canonicalFormulaMachine.step (canonicalConfiguration 1 suffix [] field
              binary borrow output)
  | cons bit header ih =>
      have hfirst := oneStep _ _ (canonical_header_payload_step bit
          (header ++ suffix)
          (List.replicate header.length true)
          field binary borrow output)
      have hrest := ih (bit :: field)
      have hboth := EvalsToInTime.trans canonicalFormulaMachine.step 1 header.length
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.cons_append, List.length_cons,
          List.replicate_succ,
          List.reverse_cons, List.append_assoc, List.nil_append] using hboth

/-- Internal support shared across GapCVP continuation modules. -/
def canonicalHeaderReverseTrace
    (field input binary borrow output : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 3 input []
        field binary borrow output)
      (some (canonicalConfiguration (canonicalPrefixLabel 0)
        input [] [] (field.reverse ++ binary) borrow output))
      (field.length + 1) := by
  induction field generalizing binary with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (canonical_header_reverse_complete input binary borrow output)
  | cons bit field ih =>
      have hfirst := oneStep _ _ (canonical_header_reverse_step bit
          input field binary borrow output)
      have hrest := ih (bit :: binary)
      have hboth := EvalsToInTime.trans canonicalFormulaMachine.step 1 (field.length + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hboth

/-- Internal support shared across GapCVP continuation modules. -/
structure PositiveBinarySplit (bits : List Bool) where
  /-- Number of leading zero bits. -/
  zeros : ℕ
  /-- Bits following the first positive bit. -/
  tail : List Bool
  /-- Decomposition of the positive binary word. -/
  shape : bits = List.replicate zeros false ++ true :: tail

/-- Internal support shared across GapCVP continuation modules. -/
def positiveBinarySplit
    (bits : List Bool) (hpositive : 0 < binaryStackValue bits) :
    PositiveBinarySplit bits := by
  induction bits with
  | nil =>
      simp only [binaryStackValue, lt_self_iff_false] at hpositive
  | cons bit bits ih =>
      cases bit with
      | true =>
          exact ⟨0, bits, rfl⟩
      | false =>
          have hrest : 0 < binaryStackValue bits := by
            simpa only [binaryStackValue, Bool.false_eq_true, ↓reduceIte, zero_add,
                Order.lt_two_iff, zero_le,
                mul_pos_iff_of_pos_left] using hpositive
          obtain ⟨zeros, tail, hshape⟩ := ih hrest
          exact ⟨zeros + 1, tail, by
            simp only [hshape, List.replicate_succ, List.cons_append]⟩

/-- Internal support shared across GapCVP continuation modules. -/
theorem binaryStackDecrement_none_shape
    (bits : List Bool)
    (hdecrement : binaryStackDecrement bits = none) :
    bits = List.replicate bits.length false := by
  induction bits with
  | nil =>
      rfl
  | cons bit bits ih =>
      cases bit with
      | true =>
          simp only [binaryStackDecrement, reduceCtorEq] at hdecrement
      | false =>
          cases hrest : binaryStackDecrement bits with
          | none =>
              have hshape := ih hrest
              change false :: bits =
                List.replicate (bits.length + 1) false
              rw [List.replicate_succ, ← hshape]
          | some remaining =>
              simp only [binaryStackDecrement, hrest, reduceCtorEq] at hdecrement

/-- Internal support shared across GapCVP continuation modules. -/
theorem binaryStackValue_zero_shape
    (bits : List Bool) (hzero : binaryStackValue bits = 0) :
    bits = List.replicate bits.length false := by
  apply List.eq_replicate_of_mem
  exact (binaryStackValue_eq_zero_iff bits).mp hzero

/-- Internal support shared across GapCVP continuation modules. -/
def canonicalBorrowFailureTrace
    (zeros : ℕ)
    (input counter field borrow output : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 13 input counter field
        (List.replicate zeros false) borrow output)
      (some (canonicalConfiguration 15 input counter field
        [] (List.replicate zeros true ++ borrow) output))
      (zeros + 1) := by
  induction zeros generalizing borrow with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (canonical_borrow_exhausted input counter field borrow output)
  | succ zeros ih =>
      have hfirst := oneStep _ _ (canonical_borrow_zero input counter field
          (List.replicate zeros false) borrow output)
      have hrest := ih (true :: borrow)
      have hboth := EvalsToInTime.trans canonicalFormulaMachine.step 1 (zeros + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hboth

/-- Internal support shared across GapCVP continuation modules. -/
def canonicalClearFieldTrace
    (position : Fin 3) (hposition : position ≠ 2)
    (field : List Bool) (sign : Bool)
    (input binary borrow output : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalClearLabel position)
        (sign :: input) [] field binary borrow output)
      (some (canonicalConfiguration
        (canonicalPrefixLabel (nextLiteralPosition position))
        input [] [] binary borrow output))
      (field.length + 1) := by
  induction field with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, zero_add] using
          oneStep _ _ (canonical_clear_sign_step position hposition sign input binary borrow
              output)
  | cons bit field ih =>
      have hfirst := oneStep _ _ (canonical_literal_clear_step position bit
          (sign :: input) field binary borrow output)
      have hboth := EvalsToInTime.trans canonicalFormulaMachine.step 1 (field.length + 1)
        _ _ _ hfirst ih
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, Nat.add_assoc, Nat.reduceAdd]
          using hboth

/-- Internal support shared across GapCVP continuation modules. -/
def canonicalClearThirdFieldTrace
    (field : List Bool) (sign : Bool)
    (input binary borrow output : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration (canonicalClearLabel 2)
        (sign :: input) [] field binary borrow output)
      (some (canonicalConfiguration 13
        input [] [] binary borrow output))
      (field.length + 1) := by
  induction field with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, zero_add] using
          oneStep _ _ (canonical_clear_completeClause sign input binary borrow output)
  | cons bit field ih =>
      have hfirst := oneStep _ _ (canonical_literal_clear_step 2 bit
          (sign :: input) field binary borrow output)
      have hboth := EvalsToInTime.trans canonicalFormulaMachine.step 1 (field.length + 1)
        _ _ _ hfirst ih
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, Nat.add_assoc, Nat.reduceAdd]
          using hboth

end FormulaCert

namespace FormulaTotalCert

open Turing GapCVP.SourceTotalStructuralDecoder GapCVP.SourceVariableFormulaDecoder
open GapCVP.FormulaTuringTM GapCVP.FormulaCert

/-- GapCVP reduction support. -/
def canonicalFormulaExpected (input : List Bool) : List Bool :=
  match BinaryEncoding.decodeThreeCNF input with
  | none => [false]
  | some formula =>
      if BinaryEncoding.encodeThreeCNF formula = input
      then [true] else [false]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonicalFormulaExpected_eq_true_iff (input : List Bool) :
    canonicalFormulaExpected input = [true] ↔
      ∃ formula : ThreeCNF,
        BinaryEncoding.encodeThreeCNF formula = input := by
  constructor
  · intro haccept
    cases hdecode : BinaryEncoding.decodeThreeCNF input with
    | none =>
        simp only [canonicalFormulaExpected, hdecode, List.cons.injEq, Bool.false_eq_true,
            and_true] at haccept
    | some formula =>
        have hcanonical :
            BinaryEncoding.encodeThreeCNF formula = input := by
          simpa only [canonicalFormulaExpected, hdecode, ite_eq_left_iff, List.cons.injEq,
              Bool.false_eq_true, and_true,
              imp_false, Decidable.not_not] using haccept
        exact ⟨formula, hcanonical⟩
  · rintro ⟨formula, rfl⟩
    simp only [canonicalFormulaExpected, BinaryEncoding.decodeThreeCNF_encode, ↓reduceIte]

/-- Internal support shared across GapCVP continuation modules. -/
theorem binaryStackDecrement_length
    (bits remaining : List Bool)
    (hdecrement : binaryStackDecrement bits = some remaining) :
    remaining.length = bits.length := by
  induction bits generalizing remaining with
  | nil =>
      simp only [binaryStackDecrement, reduceCtorEq] at hdecrement
  | cons bit bits ih =>
      cases bit with
      | true =>
          simp only [binaryStackDecrement, Option.some.injEq] at hdecrement
          subst remaining
          rfl
      | false =>
          cases hrest : binaryStackDecrement bits with
          | none =>
              simp only [binaryStackDecrement, hrest, reduceCtorEq] at hdecrement
          | some tail =>
              simp only [binaryStackDecrement, hrest, Option.some.injEq] at hdecrement
              subst remaining
              simp only [List.length_cons, ih tail hrest]

/-- Internal support shared across GapCVP continuation modules. -/
def canonicalDecrementSomeTrace
    (bits remaining : List Bool)
    (hdecrement : binaryStackDecrement bits = some remaining)
    (input counter field output : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step
      (canonicalConfiguration 13 input counter field bits [] output)
      (some (canonicalConfiguration (canonicalPrefixLabel 0)
        input counter field remaining [] output))
      (2 * bits.length + 2) := by
  have hpositive : 0 < binaryStackValue bits := by
    have hvalue := binaryStackDecrement_value bits remaining hdecrement
    omega
  obtain ⟨zeros, tail, hshape⟩ := positiveBinarySplit bits hpositive
  subst bits
  rw [binaryStackDecrement_replicate] at hdecrement
  cases Option.some.inj hdecrement
  apply rebound (canonical_decrementTrace zeros tail input counter field output)
  simp only [List.length_append, List.length_replicate,
    List.length_cons]
  omega

private def canonical_zeroPrefixTrace
    (zeros : ℕ) (tail : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 16 [] [] []
        (List.replicate zeros false ++ tail) [] [])
      (some (canonicalConfiguration 16 [] [] [] tail [] []))
      zeros := by
  induction zeros with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append] using
          EvalsToInTime.refl canonicalFormulaMachine.step (canonicalConfiguration 16 [] [] [] tail
              [] [])
  | succ zeros ih =>
      have hfirst := oneStep _ _ (canonical_zeroCheck_false [] [] []
          (List.replicate zeros false ++ tail) [] [])
      have hboth := EvalsToInTime.trans canonicalFormulaMachine.step 1 zeros _ _ _ hfirst ih
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append] using hboth

/-- Internal support shared across GapCVP continuation modules. -/
def canonicalZeroFailureTrace
    (bits : List Bool) (hpositive : 0 < binaryStackValue bits) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 16 [] [] [] bits [] [])
      (some (Turing.haltList canonicalFormulaMachine [false]))
      (2 * bits.length + 3) := by
  obtain ⟨zeros, tail, hshape⟩ := positiveBinarySplit bits hpositive
  subst bits
  have hprefix := canonical_zeroPrefixTrace zeros (true :: tail)
  have hreject := oneStep _ _ (canonical_zeroCheck_true [] [] [] tail [] [])
  have hcleanup := canonicalFailureTrace [] [] [] (true :: tail) [] []
  have hfirst := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hprefix hreject
  have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hfirst hcleanup
  apply rebound hfull
  simp only [List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_literal_prefix_missing_counter
    (position : Fin 3) (counterBit : Bool)
    (counter field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalPrefixLabel position)
        [] (counterBit :: counter) field binary borrow output) =
      some (canonicalConfiguration 15
        [] (counterBit :: counter) field binary borrow output) := by
  fin_cases position <;> cases counterBit <;>
    compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration,
        canonicalPrefixLabel,
      canonicalPrefixStatement]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_literal_prefix_incomplete
    (position : Fin 3) (hposition : position ≠ 0)
    (field binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalPrefixLabel position)
        [] [] field binary borrow output) =
      some (canonicalConfiguration 15
        [] [] field binary borrow output) := by
  fin_cases position <;>
    simp_all [canonicalFormulaMachine, canonicalConfiguration,
      canonicalPrefixLabel, canonicalPrefixStatement,
      Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
    rfl

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_zero_field_missing_sign
    (position : Fin 3) (binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalPayloadLabel position)
        [] [] [] binary borrow output) =
      some (canonicalConfiguration 15
        [] [] [] binary borrow output) := by
  fin_cases position <;>
    compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration,
      canonicalPayloadLabel, canonicalPayloadStatement, canonicalSignStatement]

/-- Internal support shared across GapCVP continuation modules. -/
theorem canonical_clear_missing_sign
    (position : Fin 3) (binary borrow output : List Bool) :
    canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalClearLabel position)
        [] [] [] binary borrow output) =
      some (canonicalConfiguration 15
        [] [] [] binary borrow output) := by
  fin_cases position <;>
    compactMachineStepTac [canonicalFormulaMachine, canonicalConfiguration, canonicalClearLabel,
      canonicalClearStatement, canonicalSignStatement]

end FormulaTotalCert

end GapCVP

end
