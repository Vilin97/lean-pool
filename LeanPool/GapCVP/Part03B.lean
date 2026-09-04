/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part03A

/-! # GapCVP proof, part 03, continuation 02 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace SourceStructuralDecoder

open Turing

private def payload_validTrace
    (payload suffix : List Bool) :
    EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 0
        (BinaryEncoding.lengthPrefixedWord payload ++ suffix)
        [] [] [])
      (some (Turing.haltList payloadDecoderMachine
        (true :: payload)))
      (3 * payload.length + suffix.length + 4) := by
  have hprefix :
      EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 0
          (BinaryEncoding.lengthPrefixedWord payload ++ suffix)
          [] [] [])
        (some (payloadConfiguration 1 (payload ++ suffix)
          (List.replicate payload.length true) [] []))
        (payload.length + 1) := by
    simpa only [FinTM2.step, Fin.isValue, BinaryEncoding.lengthPrefixedWord, List.append_assoc,
        List.cons_append,
        List.append_nil] using payloadPrefixTrace payload.length (payload ++ suffix) [] [] []
  have hcopy :
      EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 1 (payload ++ suffix)
          (List.replicate payload.length true) [] [])
        (some (payloadConfiguration 1 suffix [] payload.reverse []))
        payload.length := by
    simpa only [FinTM2.step, Fin.isValue, List.append_nil] using payloadCopyTrace payload suffix
        [] []
  have hcounter := oneStep _ _ (payload_counter_complete suffix payload.reverse [])
  have hreverse :
      EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 2 suffix [] payload.reverse
          [])
        (some (payloadConfiguration 2 suffix [] [] payload))
        payload.length := by
    simpa only [FinTM2.step, Fin.isValue, List.reverse_reverse, List.append_nil,
        List.length_reverse] using
        payloadReverseTrace suffix payload.reverse []
  have hreverseDone := oneStep _ _ (payload_reverse_complete suffix payload)
  have hdrain := payloadDrainTrace suffix payload
  have h01 := EvalsToInTime.trans payloadDecoderMachine.step _ _ _ _ _ hprefix hcopy
  have h012 := EvalsToInTime.trans payloadDecoderMachine.step _ _ _ _ _ h01 hcounter
  have h0123 := EvalsToInTime.trans payloadDecoderMachine.step _ _ _ _ _ h012 hreverse
  have h01234 := EvalsToInTime.trans payloadDecoderMachine.step _ _ _ _ _ h0123 hreverseDone
  have hfull := EvalsToInTime.trans payloadDecoderMachine.step _ _ _ _ _ h01234 hdrain
  exact {
    steps := hfull.steps
    evals_in_steps := hfull.evals_in_steps
    steps_le_m := by
      have hsteps := hfull.steps_le_m
      omega
  }

end SourceStructuralDecoder

namespace SourceTotalStructuralDecoder

open Turing GapCVP.SourceStructuralDecoder

private def payload_failureTrace
    (input counter reversed output : List Bool) :
    EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 4 input counter reversed output)
      (some (Turing.haltList payloadDecoderMachine (false :: output)))
      (input.length + counter.length + reversed.length + 1) := by
  induction input generalizing counter reversed output with
  | cons bit input ih =>
      have hfirst := oneStep _ _ (payload_failure_drop_input bit input counter reversed output)
      have hrest := ih counter reversed output
      have hboth := EvalsToInTime.trans payloadDecoderMachine.step 1
        (input.length + counter.length + reversed.length + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, Nat.add_comm, Nat.add_left_comm,
          Nat.reduceAdd,
          Nat.add_assoc] using hboth
  | nil =>
      induction counter generalizing reversed output with
      | cons bit counter ih =>
          have hfirst := oneStep _ _ (payload_failure_drop_counter bit counter reversed output)
          have hrest :
              EvalsToInTime payloadDecoderMachine.step
                (payloadConfiguration 4 [] counter reversed output)
                (some (Turing.haltList payloadDecoderMachine
                  (false :: output)))
                (counter.length + reversed.length + 1) := by
            simpa only [FinTM2.step, Fin.isValue, List.length_nil, zero_add] using ih reversed
                output
          have hboth := EvalsToInTime.trans payloadDecoderMachine.step 1
            (counter.length + reversed.length + 1)
            _ _ _ hfirst hrest
          simpa only [FinTM2.step, Fin.isValue, List.length_nil, List.length_cons, zero_add,
              Nat.add_comm,
              Nat.add_left_comm, Nat.reduceAdd, Nat.add_assoc] using hboth
      | nil =>
          induction reversed generalizing output with
          | cons bit reversed ih =>
              have hfirst := oneStep _ _ (payload_failure_drop_reversed bit reversed output)
              have hrest :
                  EvalsToInTime payloadDecoderMachine.step
                    (payloadConfiguration 4 [] [] reversed output)
                    (some (Turing.haltList payloadDecoderMachine
                      (false :: output)))
                    (reversed.length + 1) := by
                simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero, zero_add] using ih
                    output
              have hboth := EvalsToInTime.trans payloadDecoderMachine.step 1 (reversed.length + 1)
                _ _ _ hfirst hrest
              simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero, List.length_cons,
                  zero_add, Nat.add_comm,
                  Nat.add_left_comm, Nat.reduceAdd] using hboth
          | nil =>
              simpa only [FinTM2.step, Fin.isValue, List.length_nil, add_zero, zero_add] using
                  oneStep _ _ (payload_failure_finish output)

private def payload_missingPrefixTrace
    (count : ℕ) (counter reversed output : List Bool) :
    EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 0 (List.replicate count true)
        counter reversed output)
      (some (payloadConfiguration 4 []
        (List.replicate count true ++ counter) reversed output))
      (count + 1) := by
  induction count generalizing counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (payload_prefix_missing_delimiter counter reversed output)
  | succ count ih =>
      have hfirst := oneStep _ _ (payload_prefix_true (List.replicate count true)
          counter reversed output)
      have hrest := ih (true :: counter)
      have hboth := EvalsToInTime.trans payloadDecoderMachine.step 1 (count + 1)
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          replicate_true_append_cons] using hboth

private def payload_missingTrace (count : ℕ) :
    EvalsToInTime payloadDecoderMachine.step
      (payloadConfiguration 0 (List.replicate count true) [] [] [])
      (some (Turing.haltList payloadDecoderMachine [false]))
      (2 * count + 2) := by
  have hprefix :
      EvalsToInTime payloadDecoderMachine.step
        (payloadConfiguration 0 (List.replicate count true) [] [] [])
        (some (payloadConfiguration 4 []
          (List.replicate count true) [] []))
        (count + 1) := by
    simpa only [FinTM2.step, Fin.isValue, List.append_nil] using payload_missingPrefixTrace count
        [] [] []
  have hcleanup := payload_failureTrace [] (List.replicate count true) [] []
  have hfull := EvalsToInTime.trans payloadDecoderMachine.step _ _ _ _ _ hprefix hcleanup
  exact {
    steps := hfull.steps
    evals_in_steps := hfull.evals_in_steps
    steps_le_m := by
      have hsteps := hfull.steps_le_m
      simp only [List.length_replicate, List.length_nil] at hsteps
      omega
  }

private def payload_partialCopyTrace
    (payload remaining reversed output : List Bool) :
    EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 1 payload
        (List.replicate payload.length true ++ remaining)
        reversed output)
      (some (payloadConfiguration 1 [] remaining
        (payload.reverse ++ reversed) output))
      payload.length := by
  induction payload generalizing reversed with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, List.replicate_zero, List.nil_append,
          List.reverse_nil] using
          EvalsToInTime.refl payloadDecoderMachine.step (payloadConfiguration 1 [] remaining
              reversed output)
  | cons bit payload ih =>
      have hfirst := oneStep _ _ (payload_copy_step bit payload
          (List.replicate payload.length true ++ remaining)
          reversed output)
      have hrest := ih (bit :: reversed)
      have hboth := EvalsToInTime.trans payloadDecoderMachine.step 1 payload.length
        _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, List.replicate_succ,
          List.cons_append,
          List.reverse_cons, List.append_assoc, List.nil_append] using hboth

private def payload_truncatedTrace
    (payload : List Bool) (extra : ℕ) :
    EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 0
        (List.replicate (payload.length + extra + 1) true ++
          false :: payload)
        [] [] [])
      (some (Turing.haltList payloadDecoderMachine [false]))
      (3 * payload.length + 2 * extra + 6) := by
  have hprefix :
      EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 0
          (List.replicate (payload.length + extra + 1) true ++
            false :: payload)
          [] [] [])
        (some (payloadConfiguration 1 payload
          (List.replicate (payload.length + extra + 1) true) [] []))
        (payload.length + extra + 1 + 1) := by
    simpa only [FinTM2.step, Fin.isValue, List.append_nil] using
        payloadPrefixTrace (payload.length + extra + 1) payload [] [] []
  have hcopy :
      EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 1 payload
          (List.replicate (payload.length + extra + 1) true) [] [])
        (some (payloadConfiguration 1 []
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
        payload_partialCopyTrace payload (List.replicate (extra + 1) true) [] []
  have hinsufficient :
      EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 1 []
          (List.replicate (extra + 1) true) payload.reverse [])
        (some (payloadConfiguration 4 []
          (List.replicate (extra + 1) true) payload.reverse []))
        1 := by
    simpa only [FinTM2.step, Fin.isValue, List.replicate_succ] using
        oneStep _ _ (payload_insufficient (List.replicate extra true) payload.reverse [])
  have hcleanup := payload_failureTrace []
    (List.replicate (extra + 1) true) payload.reverse []
  have h01 := EvalsToInTime.trans payloadDecoderMachine.step _ _ _ _ _ hprefix hcopy
  have h012 := EvalsToInTime.trans payloadDecoderMachine.step _ _ _ _ _ h01 hinsufficient
  have hfull := EvalsToInTime.trans payloadDecoderMachine.step _ _ _ _ _ h012 hcleanup
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
def payloadDecodeOutput (input : List Bool) : List Bool :=
  match BinaryEncoding.readLengthPrefixedWord input with
  | some (payload, _) => true :: payload
  | none => [false]

@[simp] theorem payloadDecodeOutput_valid
    (payload suffix : List Bool) :
    payloadDecodeOutput
        (BinaryEncoding.lengthPrefixedWord payload ++ suffix) =
      true :: payload := by
  simp only [payloadDecodeOutput, BinaryEncoding.readLengthPrefixedWord_append]

@[simp] theorem readUnaryPrefix_missing (count : ℕ) :
    BinaryEncoding.readUnaryPrefix
      (List.replicate count true) = none := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, BinaryEncoding.readUnaryPrefix, ih]

@[simp] private theorem payloadDecodeOutput_missing (count : ℕ) :
    payloadDecodeOutput (List.replicate count true) = [false] := by
  simp only [payloadDecodeOutput, BinaryEncoding.readLengthPrefixedWord, readUnaryPrefix_missing]

@[simp] private theorem payloadDecodeOutput_truncated
    (payload : List Bool) (extra : ℕ) :
    payloadDecodeOutput
      (List.replicate (payload.length + extra + 1) true ++
        false :: payload) = [false] := by
  have hshort : ¬ payload.length + extra + 1 ≤ payload.length := by
    omega
  simp only [payloadDecodeOutput, BinaryEncoding.readLengthPrefixedWord,
      BinaryEncoding.readUnaryPrefix_replicate, hshort, ↓reduceIte]

/-- GapCVP reduction support. -/
structure MissingUnaryInput (input : List Bool) where
  /-- GapCVP reduction support. -/
  count : ℕ
  shape : input = List.replicate count true

/-- GapCVP reduction support. -/
structure DelimitedUnaryInput (input : List Bool) where
  /-- GapCVP reduction support. -/
  count : ℕ
  /-- GapCVP reduction support. -/
  tail : List Bool
  shape : input = List.replicate count true ++ false :: tail

/-- GapCVP reduction support. -/
def unaryInputSplit (input : List Bool) :
    MissingUnaryInput input ⊕ DelimitedUnaryInput input := by
  induction input with
  | nil =>
      exact Sum.inl ⟨0, rfl⟩
  | cons bit input ih =>
      cases bit with
      | false =>
          exact Sum.inr ⟨0, input, rfl⟩
      | true =>
          cases ih with
          | inl witness =>
              obtain ⟨count, h⟩ := witness
              exact Sum.inl ⟨count + 1, by
                simp only [h, List.replicate_succ]⟩
          | inr witness =>
              obtain ⟨count, tail, h⟩ := witness
              exact Sum.inr ⟨count + 1, tail, by
                simp only [h, List.replicate_succ, List.cons_append]⟩

theorem validInput_reconstruct
    (count : ℕ) (tail : List Bool) (hlen : count ≤ tail.length) :
    List.replicate count true ++ false :: tail =
      BinaryEncoding.lengthPrefixedWord (tail.take count) ++
        tail.drop count := by
  have htake : (tail.take count).length = count := by
    simp only [List.length_take, min_eq_left hlen]
  simp only [BinaryEncoding.lengthPrefixedWord, htake, List.append_assoc, List.cons_append,
      List.take_append_drop]

private def payload_totalTrace (input : List Bool) :
    EvalsToInTime payloadDecoderMachine.step (payloadConfiguration 0 input [] [] [])
      (some (Turing.haltList payloadDecoderMachine
        (payloadDecodeOutput input)))
      (3 * input.length + 6) := by
  cases unaryInputSplit input with
  | inl witness =>
    obtain ⟨count, hinput⟩ := witness
    subst input
    have htrace := payload_missingTrace count
    exact {
      steps := htrace.steps
      evals_in_steps := by
        simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, payloadDecodeOutput_missing]
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
      have htrace := payload_validTrace (tail.take count) (tail.drop count)
      exact {
        steps := htrace.steps
        evals_in_steps := by
          simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, payloadDecodeOutput_valid]
              using
              htrace.evals_in_steps
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
      have htrace := payload_truncatedTrace tail extra
      exact {
        steps := htrace.steps
        evals_in_steps := by
          simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, payloadDecodeOutput_truncated]
              using
              htrace.evals_in_steps
        steps_le_m := by
          have hsteps := htrace.steps_le_m
          simp only [List.length_append, List.length_replicate,
            List.length_cons]
          omega
      }

/-- GapCVP reduction support. -/
noncomputable def payloadDecoderComputable :
    BitTM
      payloadDecodeOutput where
  tm := payloadDecoderMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 3 * Polynomial.X + 6
  outputsFun input := {
    steps := (payload_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, payloadDecoderMachine_init,
              Option.map_some] using
          (payload_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (payload_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq, Polynomial.eval_add,
          Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X, ge_iff_le] using hsteps
  }

end SourceTotalStructuralDecoder

namespace SourceFormulaStructuralDecoder

open Turing GapCVP.SourceTotalStructuralDecoder

private abbrev dropHeadMachine : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .pop () (fun _ _ => ()) .halt

private theorem dropHeadMachine_step (input : List Bool) :
    dropHeadMachine.step (Turing.initList dropHeadMachine input) =
      some (Turing.haltList dropHeadMachine input.tail) := by
  compactMachineStepTac [dropHeadMachine, Turing.initList]

/-- GapCVP reduction support. -/
noncomputable def dropHeadComputable :
    BitTM
      List.tail where
  tm := dropHeadMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun input := {
    steps := 1
    evals_in_steps := by
      have hinput :
          List.map (Equiv.refl Bool).invFun
            (bitEncoding input) = input := by
        change List.map (fun bit : Bool => bit) input = input
        simp only [List.map_id_fun', id_eq]
      have houtput :
          List.map (Equiv.refl Bool).invFun
            (bitEncoding input.tail) = input.tail := by
        change List.map (fun bit : Bool => bit) input.tail = input.tail
        simp only [List.map_tail, List.map_id_fun', id_eq]
      rw [hinput, houtput]
      change dropHeadMachine.step
        (Turing.initList dropHeadMachine input) =
          some (Turing.haltList dropHeadMachine input.tail)
      exact dropHeadMachine_step input
    steps_le_m := by simp only [id_eq, Polynomial.eval_one, Std.le_refl]
  }

/-- GapCVP reduction support. -/
def firstFieldContents (input : List Bool) : List Bool :=
  (payloadDecodeOutput input).tail

/-- GapCVP reduction support. -/
noncomputable def firstFieldContentsComputable :
    BitTM
      firstFieldContents := by
  exact TMComposition.computableInPolyTime
    payloadDecoderComputable dropHeadComputable

@[simp] theorem firstFieldContents_valid
    (payload suffix : List Bool) :
    firstFieldContents
      (BinaryEncoding.lengthPrefixedWord payload ++ suffix) =
        payload := by
  simp only [firstFieldContents, payloadDecodeOutput_valid, List.tail_cons]

/-- Internal support shared across GapCVP continuation modules. -/
abbrev suffixDecoderMachine : Turing.FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Fin 6
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 6) then
      .peek 0 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol == some true)
          (.pop 0 (fun _ _ => none)
            (.push 1 (fun _ => true)
              (.goto (fun _ => 0))))
          (.branch (fun symbol => symbol.isSome)
            (.pop 0 (fun _ _ => none)
              (.goto (fun _ => 1)))
            (.goto (fun _ => 5))))
    else if phase = (1 : Fin 6) then
      .peek 1 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.peek 0 (fun _ symbol => symbol)
            (.branch (fun symbol => symbol.isSome)
              (.pop 1 (fun state _ => state)
                (.pop 0 (fun state _ => state)
                  (.push 2 (fun state => state.getD false)
                    (.load (fun _ => none) (.goto (fun _ => 1))))))
              (.goto (fun _ => 5))))
          (.goto (fun _ => 2)))
    else if phase = (2 : Fin 6) then
      .peek 2 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.pop 2 (fun _ _ => none) (.goto (fun _ => 2)))
          (.goto (fun _ => 3)))
    else if phase = (3 : Fin 6) then
      .peek 0 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.pop 0 (fun state _ => state)
            (.push 2 (fun state => state.getD false)
              (.load (fun _ => none) (.goto (fun _ => 3)))))
          (.goto (fun _ => 4)))
    else if phase = (4 : Fin 6) then
      .peek 2 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.pop 2 (fun state _ => state)
            (.push 3 (fun state => state.getD false)
              (.load (fun _ => none) (.goto (fun _ => 4)))))
          .halt)
    else
      .peek 0 (fun _ symbol => symbol)
        (.branch (fun symbol => symbol.isSome)
          (.pop 0 (fun _ _ => none) (.goto (fun _ => 5)))
          (.peek 1 (fun _ symbol => symbol)
            (.branch (fun symbol => symbol.isSome)
              (.pop 1 (fun _ _ => none) (.goto (fun _ => 5)))
              (.peek 2 (fun _ symbol => symbol)
                (.branch (fun symbol => symbol.isSome)
                  (.pop 2 (fun _ _ => none) (.goto (fun _ => 5)))
                  .halt)))))

/-- Internal support shared across GapCVP continuation modules. -/
def suffixConfiguration
    (phase : Fin 6)
    (input counter reversed output : List Bool) :
    suffixDecoderMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, counter, reversed, output]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_prefix_true
    (input counter reversed output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 0 (true :: input) counter reversed output) =
      some (suffixConfiguration 0 input (true :: counter)
        reversed output) := by
  compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_prefix_delimiter
    (input counter reversed output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 0 (false :: input) counter reversed output) =
      some (suffixConfiguration 1 input counter reversed output) := by
  compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_prefix_missing_delimiter
    (counter reversed output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 0 [] counter reversed output) =
      some (suffixConfiguration 5 [] counter reversed output) := by
  compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_copy_step
    (bit : Bool) (input counter reversed output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 1 (bit :: input)
        (true :: counter) reversed output) =
      some (suffixConfiguration 1 input counter
        (bit :: reversed) output) := by
  cases bit <;> compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_insufficient
    (counter reversed output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 1 [] (true :: counter) reversed output) =
      some (suffixConfiguration 5 []
        (true :: counter) reversed output) := by
  compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_counter_complete
    (input reversed output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 1 input [] reversed output) =
      some (suffixConfiguration 2 input [] reversed output) := by
  compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_discard_step
    (bit : Bool) (input reversed output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 2 input [] (bit :: reversed) output) =
      some (suffixConfiguration 2 input [] reversed output) := by
  cases bit <;> compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_discard_complete
    (input output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 2 input [] [] output) =
      some (suffixConfiguration 3 input [] [] output) := by
  compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_collect_step
    (bit : Bool) (input reversed output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 3 (bit :: input) [] reversed output) =
      some (suffixConfiguration 3 input []
        (bit :: reversed) output) := by
  cases bit <;> compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_collect_complete
    (reversed output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 3 [] [] reversed output) =
      some (suffixConfiguration 4 [] [] reversed output) := by
  compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_restore_step
    (bit : Bool) (reversed output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 4 [] [] (bit :: reversed) output) =
      some (suffixConfiguration 4 [] [] reversed (bit :: output)) := by
  cases bit <;> compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_restore_finish
    (output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 4 [] [] [] output) =
      some (Turing.haltList suffixDecoderMachine output) := by
  compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_failure_drop_input
    (bit : Bool) (input counter reversed output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 5 (bit :: input) counter reversed output) =
      some (suffixConfiguration 5 input counter reversed output) := by
  cases bit <;> compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_failure_drop_counter
    (bit : Bool) (counter reversed output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 5 [] (bit :: counter) reversed output) =
      some (suffixConfiguration 5 [] counter reversed output) := by
  cases bit <;> compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_failure_drop_reversed
    (bit : Bool) (reversed output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 5 [] [] (bit :: reversed) output) =
      some (suffixConfiguration 5 [] [] reversed output) := by
  cases bit <;> compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

/-- Internal support shared across GapCVP continuation modules. -/
theorem suffix_failure_finish
    (output : List Bool) :
    suffixDecoderMachine.step
      (suffixConfiguration 5 [] [] [] output) =
      some (Turing.haltList suffixDecoderMachine output) := by
  compactMachineStepTac [suffixDecoderMachine, suffixConfiguration]

end SourceFormulaStructuralDecoder

end GapCVP

end
