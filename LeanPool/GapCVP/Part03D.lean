/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part03C

/-! # GapCVP proof, part 03, continuation 04 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace FormulaTotalCert

open Turing GapCVP.SourceTotalStructuralDecoder GapCVP.SourceVariableFormulaDecoder

open GapCVP.FormulaTuringTM GapCVP.FormulaCert

private def canonical_clearMissingTrace
    (position : Fin 3) (field binary : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalClearLabel position)
        [] [] field binary [] [])
      (some (Turing.haltList canonicalFormulaMachine [false]))
      (field.length + binary.length + 2) := by
  induction field with
  | nil =>
      have hfirst := oneStep _ _ (canonical_clear_missing_sign position binary [] [])
      have hcleanup := canonicalFailureTrace [] [] [] binary [] []
      have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hfirst hcleanup
      exact rebound hfull (by
        simp only [List.length_nil]
        omega)
  | cons bit field ih =>
      have hfirst := oneStep _ _ (canonical_literal_clear_step position bit
          [] field binary [] [])
      have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hfirst ih
      exact rebound hfull (by
        simp only [List.length_cons]
        omega)

private def canonical_decrementNoneFailureTrace
    (bits : List Bool)
    (hdecrement : binaryStackDecrement bits = none)
    (input : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 13 input [] [] bits [] [])
      (some (Turing.haltList canonicalFormulaMachine [false]))
      (input.length + 2 * bits.length + 2) := by
  have hshape := binaryStackDecrement_none_shape bits hdecrement
  have hborrow := canonicalBorrowFailureTrace bits.length
    input [] [] [] []
  simp only [List.append_nil] at hborrow
  rw [← hshape] at hborrow
  have hcleanup := canonicalFailureTrace input [] [] []
    (List.replicate bits.length true) []
  have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hborrow hcleanup
  apply rebound hfull
  simp only [List.length_replicate, List.length_nil]
  omega

private def canonicalBodyOutput :
    List Bool → Bool → Fin 3 → ℕ → List Bool → List Bool → Bool
  | [], true, _, _, _, _ => false
  | [], false, position, 0, [], binary =>
      if position = 0 then decide (binaryStackValue binary = 0)
      else false
  | [], false, _, _, _, _ => false
  | bit :: rest, false, position, count, field, binary =>
      if bit then
        canonicalBodyOutput rest false position (count + 1) field binary
      else
        canonicalBodyOutput rest true position count field binary
  | bit :: rest, true, position, count + 1, field, binary =>
      canonicalBodyOutput rest true position count (bit :: field) binary
  | _ :: rest, true, position, 0, field, binary =>
      match field with
      | false :: _ => false
      | _ =>
          if position = 2 then
            match binaryStackDecrement binary with
            | none => false
            | some remaining =>
                canonicalBodyOutput rest false 0 0 [] remaining
          else
            canonicalBodyOutput rest false
              (nextLiteralPosition position) 0 [] binary

private def canonicalBodyPhase (payload : Bool) (position : Fin 3) : Fin 17 :=
  if payload then canonicalPayloadLabel position
  else canonicalPrefixLabel position

private def canonicalBodyBudget
    (binaryBound : ℕ) (input : List Bool)
    (counterLength : ℕ) (field : List Bool) : ℕ :=
  (2 * binaryBound + 10) *
    (2 * input.length + counterLength + field.length + 1) +
    binaryBound + 4

private def canonical_failFromStep
    (source : canonicalFormulaMachine.Cfg)
    (input counter field binary borrow : List Bool)
    (hstep : canonicalFormulaMachine.step source =
      some (canonicalConfiguration 15
        input counter field binary borrow [])) :
    EvalsToInTime canonicalFormulaMachine.step
      source (some (Turing.haltList canonicalFormulaMachine [false]))
      (input.length + counter.length + field.length +
        binary.length + borrow.length + 2) := by
  have hfirst := oneStep _ _ hstep
  have hcleanup := canonicalFailureTrace
    input counter field binary borrow []
  have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hfirst hcleanup
  exact rebound hfull (by omega)

private def canonical_finalCountTrace (binary : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration (canonicalPrefixLabel 0)
        [] [] [] binary [] [])
      (some (Turing.haltList canonicalFormulaMachine
        [decide (binaryStackValue binary = 0)]))
      (2 * binary.length + 4) := by
  have henter := oneStep _ _ (canonical_body_finish binary [] [])
  by_cases hzero : binaryStackValue binary = 0
  · have hshape := binaryStackValue_zero_shape binary hzero
    have hzeroTrace := canonicalZeroTrace binary.length
    rw [← hshape] at hzeroTrace
    have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ henter hzeroTrace
    have hbounded := rebound (newBudget := 2 * binary.length + 4) hfull (by omega)
    simpa only [FinTM2.step, Fin.isValue, hzero, decide_true] using hbounded
  · have hpositive : 0 < binaryStackValue binary := by omega
    have hreject := canonicalZeroFailureTrace binary hpositive
    have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ henter hreject
    have hbounded := rebound (newBudget := 2 * binary.length + 4) hfull (by omega)
    simpa only [FinTM2.step, Fin.isValue, hzero, decide_false] using hbounded

private def canonicalBodyTrace
    (binaryBound : ℕ)
    (input : List Bool) (payload : Bool) (position : Fin 3)
    (counterLength : ℕ) (field binary : List Bool)
    (hbinary : binary.length ≤ binaryBound)
    (hfield : payload = false → field = []) :
    EvalsToInTime canonicalFormulaMachine.step
      (canonicalConfiguration (canonicalBodyPhase payload position)
        input (List.replicate counterLength true)
        field binary [] [])
      (some (Turing.haltList canonicalFormulaMachine
        [canonicalBodyOutput input payload position
          counterLength field binary]))
      (canonicalBodyBudget binaryBound input counterLength field) := by
  induction input generalizing payload position counterLength field binary with
  | nil =>
      cases payload with
      | false =>
          have hempty := hfield rfl
          subst field
          cases counterLength with
          | zero =>
              by_cases hposition : position = 0
              · subst position
                have htrace := canonical_finalCountTrace binary
                have hbounded := rebound (newBudget := canonicalBodyBudget
                    binaryBound [] 0 []) htrace (by
                      simp only [canonicalBodyBudget, List.length_nil, mul_zero, add_zero,
                          zero_add, mul_one, add_le_add_iff_right]
                      omega)
                simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, Bool.false_eq_true,
                    ↓reduceIte, List.replicate_zero,
                    canonicalBodyOutput] using hbounded
              · have hfailure := canonical_failFromStep
                  (canonicalConfiguration
                    (canonicalPrefixLabel position)
                    [] [] [] binary [] [])
                  [] [] [] binary []
                  (canonical_literal_prefix_incomplete
                    position hposition [] binary [] [])
                have hbounded := rebound (newBudget := canonicalBodyBudget
                    binaryBound [] 0 []) hfailure (by
                      simp only [List.length_nil, add_zero, zero_add, canonicalBodyBudget,
                          mul_zero, mul_one, add_le_add_iff_right]
                      omega)
                simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, Bool.false_eq_true,
                    ↓reduceIte, List.replicate_zero,
                    canonicalBodyOutput, hposition] using hbounded
          | succ counterLength =>
              have hfailure := canonical_failFromStep
                (canonicalConfiguration
                  (canonicalPrefixLabel position)
                  [] (true :: List.replicate counterLength true)
                  [] binary [] [])
                [] (true :: List.replicate counterLength true)
                [] binary []
                (canonical_literal_prefix_missing_counter
                  position true (List.replicate counterLength true)
                  [] binary [] [])
              have hbounded := rebound (newBudget := canonicalBodyBudget
                  binaryBound [] (counterLength + 1) [])
                hfailure (by
                  simp only [List.length_nil, List.length_cons, List.length_replicate, zero_add,
                      add_zero, canonicalBodyBudget,
                      mul_zero, add_le_add_iff_right]
                  nlinarith)
              simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, Bool.false_eq_true,
                  ↓reduceIte, List.replicate_succ,
                  canonicalBodyOutput] using hbounded
      | true =>
          cases counterLength with
          | succ counterLength =>
              have hfailure := canonical_failFromStep
                (canonicalConfiguration
                  (canonicalPayloadLabel position)
                  [] (true :: List.replicate counterLength true)
                  field binary [] [])
                [] (true :: List.replicate counterLength true)
                field binary []
                (canonical_literal_payload_missing position
                  (List.replicate counterLength true)
                  field binary [] [])
              have hbounded := rebound (newBudget := canonicalBodyBudget
                  binaryBound [] (counterLength + 1) field)
                hfailure (by
                  simp only [List.length_nil, List.length_cons, List.length_replicate, zero_add,
                      add_zero, canonicalBodyBudget,
                      mul_zero, add_le_add_iff_right]
                  nlinarith)
              simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, ↓reduceIte,
                  List.replicate_succ,
                  canonicalBodyOutput] using hbounded
          | zero =>
              cases field with
              | nil =>
                  have hfailure := canonical_failFromStep
                    (canonicalConfiguration
                      (canonicalPayloadLabel position)
                      [] [] [] binary [] [])
                    [] [] [] binary []
                    (canonical_zero_field_missing_sign
                      position binary [] [])
                  have hbounded := rebound (newBudget := canonicalBodyBudget
                      binaryBound [] 0 []) hfailure (by
                        simp only [List.length_nil, add_zero, zero_add, canonicalBodyBudget,
                            mul_zero, mul_one, add_le_add_iff_right]
                        omega)
                  simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, ↓reduceIte,
                      List.replicate_zero,
                      canonicalBodyOutput] using hbounded
              | cons fieldBit field =>
                  cases fieldBit with
                  | false =>
                      have hfailure := canonical_failFromStep
                        (canonicalConfiguration
                          (canonicalPayloadLabel position)
                          [] [] (false :: field) binary [] [])
                        [] [] (false :: field) binary []
                        (canonical_literal_field_false position []
                          field binary [] [])
                      have hbounded := rebound (newBudget := canonicalBodyBudget
                          binaryBound [] 0 (false :: field))
                        hfailure (by
                          simp only [List.length_nil, add_zero, List.length_cons, zero_add,
                              canonicalBodyBudget, mul_zero,
                              add_le_add_iff_right]
                          nlinarith)
                      simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, ↓reduceIte,
                          List.replicate_zero,
                          canonicalBodyOutput] using hbounded
                  | true =>
                      have hcheck := oneStep _ _ (canonical_literal_field_true position []
                          field binary [] [])
                      have hcleanup := canonical_clearMissingTrace
                        position (true :: field) binary
                      have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _
                        hcheck hcleanup
                      have hbounded := rebound (newBudget := canonicalBodyBudget
                          binaryBound [] 0 (true :: field))
                        hfull (by
                          simp only [List.length_cons, canonicalBodyBudget, List.length_nil,
                              mul_zero, add_zero, zero_add,
                              add_le_add_iff_right]
                          nlinarith)
                      simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, ↓reduceIte,
                          List.replicate_zero,
                          canonicalBodyOutput] using hbounded
  | cons bit input ih =>
      cases payload with
      | false =>
          have hempty := hfield rfl
          subst field
          cases bit with
          | false =>
              have hfirst := oneStep _ _ (canonical_literal_prefix_delimiter
                  position input
                  (List.replicate counterLength true)
                  [] binary [] [])
              have hrest := ih true position counterLength
                [] binary hbinary (by intro _; rfl)
              have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hfirst hrest
              have hbounded := rebound (newBudget := canonicalBodyBudget binaryBound
                  (false :: input) counterLength [])
                hfull (by
                  simp only [canonicalBodyBudget, List.length_nil, add_zero, List.length_cons,
                      add_le_add_iff_right,
                      Nat.reduceLeDiff, Order.add_one_le_iff, add_lt_add_iff_right, add_pos_iff,
                          Order.lt_two_iff, zero_le,
                      mul_pos_iff_of_pos_left, Nat.ofNat_pos, or_true, mul_lt_mul_iff_right₀,
                          Order.lt_add_one_iff, lt_add_iff_pos_right,
                      Order.lt_one_iff])
              simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, Bool.false_eq_true,
                  ↓reduceIte,
                  canonicalBodyOutput] using hbounded
          | true =>
              have hfirst := oneStep _ _ (canonical_literal_prefix_true
                  position input
                  (List.replicate counterLength true)
                  [] binary [] [])
              have hrest := ih false position (counterLength + 1)
                [] binary hbinary (by intro _; rfl)
              have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hfirst hrest
              have hbounded := rebound (newBudget := canonicalBodyBudget binaryBound
                  (true :: input) counterLength [])
                hfull (by
                  simp only [canonicalBodyBudget, List.length_nil, add_zero, List.length_cons,
                      add_le_add_iff_right,
                      Nat.reduceLeDiff, Order.add_one_le_iff, add_lt_add_iff_right, add_pos_iff,
                          Order.lt_two_iff, zero_le,
                      mul_pos_iff_of_pos_left, Nat.ofNat_pos, or_true, mul_lt_mul_iff_right₀,
                          Order.lt_add_one_iff]
                  nlinarith)
              simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, Bool.false_eq_true,
                  ↓reduceIte,
                  canonicalBodyOutput] using hbounded
      | true =>
          cases counterLength with
          | succ counterLength =>
              have hfirst := oneStep _ _ (canonical_literal_payload_step
                  position bit input
                  (List.replicate counterLength true)
                  field binary [] [])
              have hrest := ih true position counterLength
                (bit :: field) binary hbinary (by
                  intro hfalse
                  cases hfalse)
              have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hfirst hrest
              have hbounded := rebound (newBudget := canonicalBodyBudget binaryBound
                  (bit :: input) (counterLength + 1) field)
                hfull (by
                  simp only [canonicalBodyBudget, List.length_cons, add_le_add_iff_right,
                      Nat.reduceLeDiff,
                      Order.add_one_le_iff, add_lt_add_iff_right, add_pos_iff, Order.lt_two_iff,
                          zero_le, mul_pos_iff_of_pos_left,
                      Nat.ofNat_pos, or_true, mul_lt_mul_iff_right₀, Order.lt_add_one_iff]
                  nlinarith)
              simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, ↓reduceIte,
                  List.replicate_succ,
                  canonicalBodyOutput] using hbounded
          | zero =>
              cases field with
              | nil =>
                  by_cases hposition : position = 2
                  · subst position
                    have hfirst := oneStep _ _ (canonical_zero_field_completeClause
                        bit input binary [] [])
                    cases hdecrement :
                        binaryStackDecrement binary with
                    | none =>
                        have hreject :=
                          canonical_decrementNoneFailureTrace
                            binary hdecrement input
                        have hfull :=
                          EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _
                            hfirst hreject
                        have hbounded := rebound (newBudget := canonicalBodyBudget
                            binaryBound (bit :: input) 0 [])
                          hfull (by
                            simp only [canonicalBodyBudget, List.length_cons, add_zero,
                                List.length_nil, add_le_add_iff_right]
                            nlinarith)
                        simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, ↓reduceIte,
                            List.replicate_zero,
                            canonicalBodyOutput, hdecrement] using hbounded
                    | some remaining =>
                        have hremaining :
                            remaining.length ≤ binaryBound := by
                          rw [binaryStackDecrement_length
                            binary remaining hdecrement]
                          exact hbinary
                        have hborrow := canonicalDecrementSomeTrace
                          binary remaining hdecrement
                          input [] [] []
                        have hrest := ih false 0 0 [] remaining
                          hremaining (by intro _; rfl)
                        have hstart :=
                          EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _
                            hfirst hborrow
                        have hfull :=
                          EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _
                            hstart hrest
                        have hbounded := rebound (newBudget := canonicalBodyBudget
                            binaryBound (bit :: input) 0 [])
                          hfull (by
                            simp only [canonicalBodyBudget, add_zero, List.length_nil,
                                List.length_cons]
                            nlinarith)
                        simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, ↓reduceIte,
                            List.replicate_zero,
                            canonicalBodyOutput, hdecrement] using hbounded
                  · have hfirst := oneStep _ _ (canonical_zero_field_sign_step position
                        hposition bit input binary [] [])
                    have hrest := ih false
                      (nextLiteralPosition position) 0 [] binary
                      hbinary (by intro _; rfl)
                    have hfull :=
                      EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _
                        hfirst hrest
                    have hbounded := rebound (newBudget := canonicalBodyBudget
                        binaryBound (bit :: input) 0 [])
                      hfull (by
                        simp only [canonicalBodyBudget, add_zero, List.length_nil,
                            List.length_cons, add_le_add_iff_right,
                            Nat.reduceLeDiff, Order.add_one_le_iff, add_lt_add_iff_right,
                                add_pos_iff, Order.lt_two_iff, zero_le,
                            mul_pos_iff_of_pos_left, Nat.ofNat_pos, or_true, mul_lt_mul_iff_right₀,
                                Order.lt_add_one_iff, lt_add_iff_pos_right,
                            Order.lt_one_iff])
                    simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, ↓reduceIte,
                        List.replicate_zero,
                        canonicalBodyOutput, hposition] using hbounded
              | cons fieldBit field =>
                  cases fieldBit with
                  | false =>
                      have hfailure := canonical_failFromStep
                        (canonicalConfiguration
                          (canonicalPayloadLabel position)
                          (bit :: input) []
                          (false :: field) binary [] [])
                        (bit :: input) []
                        (false :: field) binary []
                        (canonical_literal_field_false position
                          (bit :: input) field binary [] [])
                      have hbounded := rebound (newBudget := canonicalBodyBudget
                          binaryBound (bit :: input)
                          0 (false :: field))
                        hfailure (by
                          simp only [List.length_cons, List.length_nil, add_zero,
                              canonicalBodyBudget, add_le_add_iff_right]
                          nlinarith)
                      simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, ↓reduceIte,
                          List.replicate_zero,
                          canonicalBodyOutput] using hbounded
                  | true =>
                      have hcheck := oneStep _ _ (canonical_literal_field_true position
                          (bit :: input) field binary [] [])
                      by_cases hposition : position = 2
                      · subst position
                        have hclear := canonicalClearThirdFieldTrace
                          (true :: field) bit input binary [] []
                        have hchecked :=
                          EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _
                            hcheck hclear
                        cases hdecrement :
                            binaryStackDecrement binary with
                        | none =>
                            have hreject :=
                              canonical_decrementNoneFailureTrace
                                binary hdecrement input
                            have hfull :=
                              EvalsToInTime.trans canonicalFormulaMachine.step
                                _ _ _ _ _ hchecked hreject
                            have hbounded := rebound (newBudget := canonicalBodyBudget
                                binaryBound (bit :: input)
                                0 (true :: field))
                              hfull (by
                                simp only [List.length_cons, canonicalBodyBudget, add_zero]
                                nlinarith)
                            simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, ↓reduceIte,
                                List.replicate_zero,
                                canonicalBodyOutput, hdecrement] using hbounded
                        | some remaining =>
                            have hremaining :
                                remaining.length ≤ binaryBound := by
                              rw [binaryStackDecrement_length
                                binary remaining hdecrement]
                              exact hbinary
                            have hborrow :=
                              canonicalDecrementSomeTrace
                                binary remaining hdecrement
                                input [] [] []
                            have hrest := ih false 0 0 [] remaining
                              hremaining (by intro _; rfl)
                            have hborrowed :=
                              EvalsToInTime.trans canonicalFormulaMachine.step
                                _ _ _ _ _ hchecked hborrow
                            have hfull :=
                              EvalsToInTime.trans canonicalFormulaMachine.step
                                _ _ _ _ _ hborrowed hrest
                            have hbounded := rebound (newBudget := canonicalBodyBudget
                                binaryBound (bit :: input)
                                0 (true :: field))
                              hfull (by
                                simp only [canonicalBodyBudget, add_zero, List.length_nil,
                                    List.length_cons]
                                nlinarith)
                            simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, ↓reduceIte,
                                List.replicate_zero,
                                canonicalBodyOutput, hdecrement] using hbounded
                      · have hclear := canonicalClearFieldTrace
                          position hposition (true :: field)
                          bit input binary [] []
                        have hchecked :=
                          EvalsToInTime.trans canonicalFormulaMachine.step
                            _ _ _ _ _ hcheck hclear
                        have hrest := ih false
                          (nextLiteralPosition position) 0 [] binary
                          hbinary (by intro _; rfl)
                        have hfull :=
                          EvalsToInTime.trans canonicalFormulaMachine.step
                            _ _ _ _ _ hchecked hrest
                        have hbounded := rebound (newBudget := canonicalBodyBudget
                            binaryBound (bit :: input)
                            0 (true :: field))
                          hfull (by
                            simp only [canonicalBodyBudget, add_zero, List.length_nil,
                                List.length_cons]
                            nlinarith)
                        simpa only [FinTM2.step, Fin.isValue, canonicalBodyPhase, ↓reduceIte,
                            List.replicate_zero,
                            canonicalBodyOutput, hposition] using hbounded

private def canonical_headerMissingPrefixTrace
    (count : ℕ)
    (counter field binary borrow output : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 0 (List.replicate count
        true)
        counter field binary borrow output)
      (some (canonicalConfiguration 15 []
        (List.replicate count true ++ counter)
        field binary borrow output))
      (count + 1) := by
  induction count generalizing counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (canonical_header_prefix_missing counter field binary borrow output)
  | succ count ih =>
      have hfirst := oneStep _ _ (canonical_header_prefix_true
          (List.replicate count true)
          counter field binary borrow output)
      have hrest := ih (true :: counter)
      have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

private def canonical_headerMissingTrace (count : ℕ) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 0
        (List.replicate count true) [] [] [] [] [])
      (some (Turing.haltList canonicalFormulaMachine [false]))
      (2 * count + 2) := by
  have hprefix := canonical_headerMissingPrefixTrace
    count [] [] [] [] []
  simp only [List.append_nil] at hprefix
  have hcleanup := canonicalFailureTrace []
    (List.replicate count true) [] [] [] []
  have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hprefix hcleanup
  apply rebound hfull
  simp only [List.length_nil, List.length_replicate]
  omega

private def canonical_headerPartialCopyTrace
    (payload remaining field binary borrow output : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 1 payload
        (List.replicate payload.length true ++ remaining)
        field binary borrow output)
      (some (canonicalConfiguration 1 [] remaining
        (payload.reverse ++ field) binary borrow output))
      payload.length := by
  induction payload generalizing field with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, List.replicate_zero, List.nil_append,
          List.reverse_nil] using
          EvalsToInTime.refl canonicalFormulaMachine.step (canonicalConfiguration 1 [] remaining
              field binary borrow output)
  | cons bit payload ih =>
      have hfirst := oneStep _ _ (canonical_header_payload_step bit payload
          (List.replicate payload.length true ++ remaining)
          field binary borrow output)
      have hrest := ih (bit :: field)
      have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, List.replicate_succ,
          List.cons_append,
          List.reverse_cons, List.append_assoc, List.nil_append] using hfull

private def canonical_headerTruncatedTrace
    (payload : List Bool) (extra : ℕ) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 0
        (List.replicate (payload.length + extra + 1) true ++
          false :: payload)
        [] [] [] [] [])
      (some (Turing.haltList canonicalFormulaMachine [false]))
      (3 * payload.length + 2 * extra + 6) := by
  have hprefix := canonicalHeaderPrefixTrace
    (payload.length + extra + 1) payload [] [] [] [] []
  simp only [List.append_nil] at hprefix
  have hcounter :
      List.replicate (payload.length + extra + 1) true =
        List.replicate payload.length true ++
          List.replicate (extra + 1) true := by
    rw [show payload.length + extra + 1 =
      payload.length + (extra + 1) by omega,
      List.replicate_add]
  have hcopy := canonical_headerPartialCopyTrace payload
    (List.replicate (extra + 1) true) [] [] [] []
  simp only [List.append_nil] at hcopy
  rw [← hcounter] at hcopy
  have hmissing :
      EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 1 []
          (List.replicate (extra + 1) true)
          payload.reverse [] [] [])
        (some (canonicalConfiguration 15 []
          (List.replicate (extra + 1) true)
          payload.reverse [] [] [])) 1 := by
    simpa only [FinTM2.step, Fin.isValue, List.replicate_succ] using
        oneStep _ _ (canonical_header_payload_missing (List.replicate extra true) payload.reverse
            [] [] [])
  have hcleanup := canonicalFailureTrace []
    (List.replicate (extra + 1) true)
    payload.reverse [] [] []
  have hstart := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hprefix hcopy
  have hdetect := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hstart hmissing
  have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hdetect hcleanup
  apply rebound hfull
  simp only [List.length_nil, List.length_replicate,
    List.length_reverse]
  omega

/-- GapCVP reduction support. -/
def canonicalMachineOutput (input : List Bool) : List Bool :=
  match BinaryEncoding.readLengthPrefixedWord input with
  | none => [false]
  | some (header, body) =>
      if isCanonicalBinaryWord header then
        [canonicalBodyOutput body false 0 0 [] header]
      else
        [false]

@[simp] private theorem canonicalMachineOutput_lengthPrefixed
    (header body : List Bool) :
    canonicalMachineOutput
        (BinaryEncoding.lengthPrefixedWord header ++ body) =
      if isCanonicalBinaryWord header then
        [canonicalBodyOutput body false 0 0 [] header]
      else [false] := by
  simp only [canonicalMachineOutput, BinaryEncoding.readLengthPrefixedWord_append, Fin.isValue]

/-- GapCVP reduction support. -/
def canonicalInputBudget (input : List Bool) : ℕ :=
  64 * (input.length + 1) * (input.length + 1) + 64

private def canonical_headerValidTrace (header body : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 0
        (BinaryEncoding.lengthPrefixedWord header ++ body)
        [] [] [] [] [])
      (some (Turing.haltList canonicalFormulaMachine
        (canonicalMachineOutput
          (BinaryEncoding.lengthPrefixedWord header ++ body))))
      (canonicalInputBudget
        (BinaryEncoding.lengthPrefixedWord header ++ body)) := by
  have hprefix := canonicalHeaderPrefixTrace
    header.length (header ++ body) [] [] [] [] []
  simp only [List.append_nil] at hprefix
  have hcopy := canonicalHeaderCopyTrace
    header body [] [] [] []
  simp only [List.append_nil] at hcopy
  have hcomplete := oneStep _ _ (canonical_header_payload_complete
      body header.reverse [] [] [])
  have hfirst := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hprefix hcopy
  have hchecked := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hfirst hcomplete
  cases hreverse : header.reverse with
  | nil =>
      have hempty : header = [] := by
        simpa only [List.reverse_reverse, List.reverse_nil] using congrArg List.reverse hreverse
      subst header
      have hzero := oneStep _ _ (canonical_header_check_zero body [] [] [])
      have hbody := canonicalBodyTrace
        0 body false 0 0 [] [] (by simp only [List.length_nil, Std.le_refl]) (by intro _; rfl)
      have hstart := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hchecked hzero
      have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _ hstart hbody
      have hbounded := rebound (newBudget := canonicalInputBudget
          (BinaryEncoding.lengthPrefixedWord [] ++ body))
        hfull (by
          simp only [canonicalBodyBudget, mul_zero, zero_add, add_zero, List.length_nil,
              Nat.reduceAdd,
              canonicalInputBudget, BinaryEncoding.lengthPrefixedWord, List.replicate_zero,
                  List.nil_append, List.cons_append,
              List.length_cons, add_le_add_iff_right]
          nlinarith)
      rw [canonicalMachineOutput_lengthPrefixed]
      simp only [isCanonicalBinaryWord, List.reverse_nil, ↓reduceIte]
      simpa only [BinaryEncoding.lengthPrefixedWord,
        List.length_nil, List.replicate_zero, List.nil_append,
        List.append_assoc, List.cons_append] using hbounded
  | cons highBit reversedTail =>
      cases highBit with
      | false =>
          rw [hreverse] at hchecked
          have hreject := oneStep _ _ (canonical_header_check_false
              body reversedTail [] [] [])
          have hcleanup := canonicalFailureTrace
            body [] (false :: reversedTail) [] [] []
          have hstart := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _
            hchecked hreject
          have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _
            hstart hcleanup
          have hlength :
              reversedTail.length + 1 = header.length := by
            have heq := congrArg List.length hreverse
            simpa only [List.length_cons, List.length_reverse] using heq.symm
          have hcanonical :
              isCanonicalBinaryWord header = false := by
            simp only [isCanonicalBinaryWord, hreverse]
          have hbounded := rebound (newBudget := canonicalInputBudget
              (BinaryEncoding.lengthPrefixedWord
                header ++ body))
            hfull (by
              simp only [List.length_nil, add_zero, List.length_cons, canonicalInputBudget,
                  BinaryEncoding.lengthPrefixedWord, List.append_assoc, List.cons_append,
                      List.length_append, List.length_replicate]
              nlinarith only [hlength,
                Nat.zero_le header.length,
                Nat.zero_le body.length,
                Nat.zero_le reversedTail.length])
          rw [canonicalMachineOutput_lengthPrefixed, hcanonical]
          simp only [Bool.false_eq_true, ↓reduceIte]
          simpa only [BinaryEncoding.lengthPrefixedWord,
            List.append_assoc, List.cons_append] using hbounded
      | true =>
          rw [hreverse] at hchecked
          have hcanonical :
              isCanonicalBinaryWord header = true := by
            simp only [isCanonicalBinaryWord, hreverse]
          have hbits :
              (true :: reversedTail).reverse = header := by
            simpa only [List.reverse_cons, List.reverse_reverse] using (congrArg List.reverse
                hreverse).symm
          have hpositive := oneStep _ _ (canonical_header_check_true
              body reversedTail [] [] [])
          have hrestore := canonicalHeaderReverseTrace
            (true :: reversedTail) body [] [] []
          simp only [List.append_nil] at hrestore
          rw [hbits] at hrestore
          have hbody := canonicalBodyTrace
            header.length body false 0 0 [] header
            (Nat.le_refl _) (by intro _; rfl)
          have hstart := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _
            hchecked hpositive
          have hrestored := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _
            hstart hrestore
          have hfull := EvalsToInTime.trans canonicalFormulaMachine.step _ _ _ _ _
            hrestored hbody
          have hlength :
              reversedTail.length + 1 = header.length := by
            have heq := congrArg List.length hreverse
            simpa only [List.length_cons, List.length_reverse] using heq.symm
          have hbounded := rebound (newBudget := canonicalInputBudget
              (BinaryEncoding.lengthPrefixedWord
                header ++ body))
            hfull (by
              simp only [canonicalBodyBudget, add_zero, List.length_nil, List.length_cons,
                  canonicalInputBudget,
                  BinaryEncoding.lengthPrefixedWord, List.append_assoc, List.cons_append,
                      List.length_append, List.length_replicate]
              nlinarith only [hlength,
                Nat.zero_le header.length,
                Nat.zero_le body.length,
                Nat.zero_le reversedTail.length])
          rw [canonicalMachineOutput_lengthPrefixed, hcanonical]
          simp only [↓reduceIte]
          simpa only [BinaryEncoding.lengthPrefixedWord,
            List.append_assoc, List.cons_append] using hbounded

@[simp] private theorem canonicalMachineOutput_missing (count : ℕ) :
    canonicalMachineOutput (List.replicate count true) = [false] := by
  simp only [canonicalMachineOutput, BinaryEncoding.readLengthPrefixedWord,
      readUnaryPrefix_missing]

@[simp] private theorem canonicalMachineOutput_truncated
    (payload : List Bool) (extra : ℕ) :
    canonicalMachineOutput
      (List.replicate (payload.length + extra + 1) true ++
        false :: payload) = [false] := by
  have hshort : ¬ payload.length + extra + 1 ≤ payload.length := by
    omega
  simp only [canonicalMachineOutput, BinaryEncoding.readLengthPrefixedWord,
      BinaryEncoding.readUnaryPrefix_replicate, hshort, ↓reduceIte]

/-- GapCVP reduction support. -/
def canonicalTotalTrace (input : List Bool) :
    EvalsToInTime canonicalFormulaMachine.step (canonicalConfiguration 0 input [] [] [] [] [])
      (some (Turing.haltList canonicalFormulaMachine
        (canonicalMachineOutput input)))
      (canonicalInputBudget input) := by
  cases unaryInputSplit input with
  | inl witness =>
      obtain ⟨count, hinput⟩ := witness
      subst input
      have htrace := canonical_headerMissingTrace count
      have hbounded := rebound (newBudget := canonicalInputBudget
          (List.replicate count true))
        htrace (by
          simp only [canonicalInputBudget, List.length_replicate, add_le_add_iff_right]
          nlinarith)
      simpa only [canonicalMachineOutput_missing] using hbounded
  | inr witness =>
      obtain ⟨count, tail, hinput⟩ := witness
      subst input
      by_cases hlength : count ≤ tail.length
      · have hreconstruct := validInput_reconstruct count tail hlength
        rw [hreconstruct]
        exact canonical_headerValidTrace
          (tail.take count) (tail.drop count)
      · have hshort : tail.length < count :=
          Nat.lt_of_not_ge hlength
        let extra := count - tail.length - 1
        have hcount : count = tail.length + extra + 1 := by
          dsimp [extra]
          omega
        rw [hcount]
        have htrace := canonical_headerTruncatedTrace tail extra
        have hbounded := rebound (newBudget := canonicalInputBudget
            (List.replicate (tail.length + extra + 1) true ++
              false :: tail))
          htrace (by
            simp only [canonicalInputBudget, List.length_append, List.length_replicate,
                List.length_cons,
                add_le_add_iff_right]
            nlinarith)
        simpa only [canonicalMachineOutput_truncated]
          using hbounded

end FormulaTotalCert

namespace FormulaSemanticCert

open Turing GapCVP.SourceTotalStructuralDecoder GapCVP.SourceVariableFormulaDecoder
open GapCVP.FormulaTuringTM GapCVP.FormulaCert GapCVP.FormulaTotalCert

private theorem canonicalBinaryWord_tail
    (bit : Bool) (tail : List Bool)
    (hcanonical : isCanonicalBinaryWord (bit :: tail) = true) :
    isCanonicalBinaryWord tail = true := by
  cases hreverse : tail.reverse with
  | nil =>
      simp only [isCanonicalBinaryWord, hreverse]
  | cons high remaining =>
      cases high with
      | false =>
          simp only [isCanonicalBinaryWord, List.reverse_cons, hreverse, List.cons_append,
              Bool.false_eq_true] at hcanonical
      | true =>
          simp only [isCanonicalBinaryWord, hreverse]

private theorem canonicalBinaryWord_zero
    (word : List Bool)
    (hcanonical : isCanonicalBinaryWord word = true)
    (hzero : binaryStackValue word = 0) :
    word = [] := by
  cases word with
  | nil =>
      rfl
  | cons bit tail =>
      cases hreverse : (bit :: tail).reverse with
      | nil =>
          have hlength := congrArg List.length hreverse
          simp only [List.reverse_cons, List.length_append, List.length_reverse, List.length_cons,
              List.length_nil,
              zero_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false]
                  at hlength
      | cons high remaining =>
          have hmember : high ∈ bit :: tail := by
            have hreversed : high ∈ (bit :: tail).reverse := by
              rw [hreverse]
              simp only [List.mem_cons, true_or]
            simpa only [List.mem_cons, List.reverse_cons, List.mem_append, List.mem_reverse,
                List.not_mem_nil, or_comm,
                false_or] using hreversed
          have hfalse :=
            (binaryStackValue_eq_zero_iff (bit :: tail)).mp
              hzero high hmember
          cases high with
          | false =>
              simp only [isCanonicalBinaryWord, hreverse, Bool.false_eq_true] at hcanonical
          | true =>
              cases hfalse

private theorem canonicalBinaryWord_injective
    (first second : List Bool)
    (hfirst : isCanonicalBinaryWord first = true)
    (hsecond : isCanonicalBinaryWord second = true)
    (hvalue : binaryStackValue first = binaryStackValue second) :
    first = second := by
  induction first generalizing second with
  | nil =>
      have hzero : binaryStackValue second = 0 := by
        simpa only [binaryStackValue] using hvalue.symm
      exact (canonicalBinaryWord_zero second hsecond hzero).symm
  | cons firstBit firstTail ih =>
      cases second with
      | nil =>
          have hzero :
              binaryStackValue (firstBit :: firstTail) = 0 := by
            simpa only [binaryStackValue, Nat.add_eq_zero_iff, ite_eq_right_iff, one_ne_zero,
                imp_false, Bool.not_eq_true,
                mul_eq_zero, OfNat.ofNat_ne_zero, false_or] using hvalue
          have hempty := canonicalBinaryWord_zero
            (firstBit :: firstTail) hfirst hzero
          cases hempty
      | cons secondBit secondTail =>
          have hfirstTail := canonicalBinaryWord_tail
            firstBit firstTail hfirst
          have hsecondTail := canonicalBinaryWord_tail
            secondBit secondTail hsecond
          cases firstBit <;> cases secondBit
          · have htail :
              binaryStackValue firstTail =
                  binaryStackValue secondTail := by
              simp only [binaryStackValue] at hvalue
              omega
            exact congrArg (List.cons false)
              (ih secondTail hfirstTail hsecondTail htail)
          · simp only [binaryStackValue, Bool.false_eq_true,
              ↓reduceIte, Nat.zero_add] at hvalue
            omega
          · simp only [binaryStackValue, Bool.false_eq_true,
              ↓reduceIte, Nat.zero_add] at hvalue
            omega
          · have htail :
                binaryStackValue firstTail =
                  binaryStackValue secondTail := by
              simp only [binaryStackValue,
                ↓reduceIte] at hvalue
              omega
            exact congrArg (List.cons true)
              (ih secondTail hfirstTail hsecondTail htail)

private theorem canonicalBinaryWord_encodeNat
    (word : List Bool)
    (hcanonical : isCanonicalBinaryWord word = true) :
    Computability.encodeNat (binaryStackValue word) = word := by
  apply canonicalBinaryWord_injective
    (Computability.encodeNat (binaryStackValue word)) word
    (encodeNat_canonical (binaryStackValue word)) hcanonical
  exact binaryStackValue_encodeNat (binaryStackValue word)

private theorem canonicalBinaryWord_decodeNat
    (word : List Bool)
    (hcanonical : isCanonicalBinaryWord word = true) :
    binaryStackValue word = Computability.decodeNat word := by
  have hword := canonicalBinaryWord_encodeNat word hcanonical
  have hdecoded := congrArg Computability.decodeNat hword
  simpa only [Computability.decode_encodeNat] using hdecoded

private theorem canonicalBodyOutput_prefix
    (length : ℕ) (tail : List Bool)
    (position : Fin 3) (counter : ℕ)
    (field binary : List Bool) :
    canonicalBodyOutput
      (List.replicate length true ++ false :: tail)
      false position counter field binary =
    canonicalBodyOutput tail true position
      (counter + length) field binary := by
  induction length generalizing counter with
  | zero =>
      simp only [List.replicate_zero, List.nil_append, canonicalBodyOutput, Bool.false_eq_true,
          ↓reduceIte,
          add_zero]
  | succ length ih =>
      simp only [List.replicate_succ, List.cons_append, canonicalBodyOutput, ↓reduceIte, ih,
          Nat.add_comm,
          Nat.add_left_comm]

private theorem canonicalBodyOutput_missingPrefix
    (length : ℕ) (position : Fin 3) (counter : ℕ)
    (field binary : List Bool) :
    canonicalBodyOutput (List.replicate length true)
      false position counter field binary =
      canonicalBodyOutput [] false position
        (counter + length) field binary := by
  induction length generalizing counter with
  | zero =>
      simp only [List.replicate_zero, add_zero]
  | succ length ih =>
      simp only [List.replicate_succ, canonicalBodyOutput, ↓reduceIte, ih, Nat.add_comm,
          Nat.add_left_comm]

private theorem canonicalBodyOutput_payload
    (payload tail : List Bool)
    (position : Fin 3) (counter : ℕ)
    (field binary : List Bool) :
    canonicalBodyOutput (payload ++ tail)
      true position (payload.length + counter) field binary =
    canonicalBodyOutput tail true position counter
      (payload.reverse ++ field) binary := by
  induction payload generalizing counter field with
  | nil =>
      simp only [List.nil_append, List.length_nil, zero_add, List.reverse_nil]
  | cons bit payload ih =>
      simpa only [List.cons_append, List.length_cons, Nat.add_comm, canonicalBodyOutput,
          Nat.add_eq,
          List.reverse_cons, List.append_assoc, List.nil_append] using ih counter (bit :: field)

private theorem canonicalBodyOutput_canonicalSign
    (sign : Bool) (suffix : List Bool) (position : Fin 3)
    (word binary : List Bool)
    (hcanonical : isCanonicalBinaryWord word = true) :
    canonicalBodyOutput (sign :: suffix)
      true position 0 word.reverse binary =
      if position = 2 then
        match binaryStackDecrement binary with
        | none => false
        | some remaining =>
            canonicalBodyOutput suffix false 0 0 [] remaining
      else
        canonicalBodyOutput suffix false
          (nextLiteralPosition position) 0 [] binary := by
  cases hreverse : word.reverse with
  | nil =>
      simp only [canonicalBodyOutput]
  | cons high remaining =>
      cases high with
      | false =>
          simp only [isCanonicalBinaryWord, hreverse, Bool.false_eq_true] at hcanonical
      | true =>
          simp only [canonicalBodyOutput]

private theorem canonicalBodyOutput_literal_extract
    (input : List Bool) (position : Fin 3) (binary : List Bool)
    (hnonempty : input ≠ [])
    (haccept : canonicalBodyOutput input
      false position 0 [] binary = true) :
    ∃ (literal : Literal) (suffix : List Bool),
      input = BinaryEncoding.encodeLiteral literal ++ suffix ∧
        (if position = 2 then
          match binaryStackDecrement binary with
          | none => false
          | some remaining =>
              canonicalBodyOutput suffix false 0 0 [] remaining
         else
          canonicalBodyOutput suffix false
            (nextLiteralPosition position) 0 [] binary) = true := by
  cases unaryInputSplit input with
  | inl witness =>
      obtain ⟨count, hshape⟩ := witness
      subst input
      cases count with
      | zero =>
          exact (hnonempty rfl).elim
      | succ count =>
          rw [canonicalBodyOutput_missingPrefix] at haccept
          simp only [zero_add, canonicalBodyOutput, Bool.false_eq_true] at haccept
  | inr witness =>
      obtain ⟨count, tail, hshape⟩ := witness
      subst input
      have hprefix := canonicalBodyOutput_prefix
        count tail position 0 [] binary
      simp only [Nat.zero_add] at hprefix
      rw [hprefix] at haccept
      by_cases hlength : count ≤ tail.length
      · let word := tail.take count
        let remaining := tail.drop count
        have hsplit : tail = word ++ remaining := by
          dsimp [word, remaining]
          exact (List.take_append_drop count tail).symm
        have hwordlength : word.length = count := by
          simp only [List.length_take, min_eq_left hlength, word]
        rw [hsplit, ← hwordlength] at haccept
        have hpayload := canonicalBodyOutput_payload
          word remaining position 0 [] binary
        simp only [Nat.add_zero, List.append_nil] at hpayload
        rw [hpayload] at haccept
        cases hremaining : remaining with
        | nil =>
            simp only [hremaining, canonicalBodyOutput, Bool.false_eq_true] at haccept
        | cons sign suffix =>
            have hcanonical : isCanonicalBinaryWord word = true := by
              cases hreverse : word.reverse with
              | nil =>
                  simp only [isCanonicalBinaryWord, hreverse]
              | cons high reverseTail =>
                  cases high with
                  | false =>
                      simp only [hremaining, hreverse, canonicalBodyOutput, Bool.false_eq_true]
                          at haccept
                  | true =>
                      simp only [isCanonicalBinaryWord, hreverse]
            have hword :
                Computability.encodeNat
                  (Computability.decodeNat word) = word := by
              rw [← canonicalBinaryWord_decodeNat word hcanonical]
              exact canonicalBinaryWord_encodeNat word hcanonical
            refine ⟨(Computability.decodeNat word, sign),
              suffix, ?_, ?_⟩
            · have htail : tail = word ++ sign :: suffix := by
                simpa only [hremaining] using hsplit
              simp only [htail, BinaryEncoding.encodeLiteral, BinaryEncoding.lengthPrefixedWord,
                  hword, hwordlength,
                  List.append_assoc, List.cons_append, List.nil_append]
            · have hsign := canonicalBodyOutput_canonicalSign
                sign suffix position word binary hcanonical
              rw [hremaining] at haccept
              rw [hsign] at haccept
              exact haccept
      · have hshort : tail.length < count :=
          Nat.lt_of_not_ge hlength
        let extra := count - tail.length
        have hcount : count = tail.length + extra := by
          dsimp [extra]
          omega
        rw [hcount] at haccept
        have hpayload := canonicalBodyOutput_payload
          tail [] position extra [] binary
        simp only [List.append_nil] at hpayload
        rw [hpayload] at haccept
        simp only [canonicalBodyOutput, Bool.false_eq_true] at haccept

private theorem canonicalBodyOutput_literal
    (literal : Literal) (suffix : List Bool)
    (position : Fin 3) (binary : List Bool) :
    canonicalBodyOutput
      (BinaryEncoding.encodeLiteral literal ++ suffix)
      false position 0 [] binary =
      if position = 2 then
        match binaryStackDecrement binary with
        | none => false
        | some remaining =>
            canonicalBodyOutput suffix false 0 0 [] remaining
      else
        canonicalBodyOutput suffix false
          (nextLiteralPosition position) 0 [] binary := by
  rcases literal with ⟨index, sign⟩
  let word := Computability.encodeNat index
  have hprefix := canonicalBodyOutput_prefix word.length
    (word ++ sign :: suffix) position 0 [] binary
  simp only [Nat.zero_add] at hprefix
  have hpayload := canonicalBodyOutput_payload
    word (sign :: suffix) position 0 [] binary
  simp only [List.append_nil] at hpayload
  have hsign := canonicalBodyOutput_canonicalSign
    sign suffix position word binary (encodeNat_canonical index)
  dsimp [word] at hprefix hpayload hsign ⊢
  simpa only [BinaryEncoding.encodeLiteral, BinaryEncoding.lengthPrefixedWord, List.append_assoc,
      List.cons_append, List.nil_append, Fin.isValue] using hprefix.trans (hpayload.trans hsign)

private theorem canonicalBodyOutput_clause
    (clause : ThreeClause) (suffix binary : List Bool) :
    canonicalBodyOutput
      (BinaryEncoding.encodeThreeClause clause ++ suffix)
      false 0 0 [] binary =
      match binaryStackDecrement binary with
      | none => false
      | some remaining =>
          canonicalBodyOutput suffix false 0 0 [] remaining := by
  simp only [BinaryEncoding.encodeThreeClause, Fin.isValue, List.append_assoc,
      canonicalBodyOutput_literal,
      Fin.reduceEq, ↓reduceIte, nextLiteralPosition, one_ne_zero]

private theorem canonicalBodyOutput_clause_extract
    (input binary : List Bool)
    (hnonempty : input ≠ [])
    (haccept : canonicalBodyOutput
      input false 0 0 [] binary = true) :
    ∃ (clause : ThreeClause) (suffix remaining : List Bool),
      input = BinaryEncoding.encodeThreeClause clause ++ suffix ∧
      binaryStackDecrement binary = some remaining ∧
      canonicalBodyOutput suffix false 0 0 [] remaining = true := by
  obtain ⟨first, firstRest, hfirst, hfirstAccept⟩ :=
    canonicalBodyOutput_literal_extract
      input 0 binary hnonempty haccept
  have hfirstPhase :
      canonicalBodyOutput firstRest false 1 0 [] binary = true := by
    simpa only [Fin.isValue, Fin.reduceEq, ↓reduceIte, nextLiteralPosition] using hfirstAccept
  have hfirstNonempty : firstRest ≠ [] := by
    intro hempty
    subst firstRest
    simp only [Fin.isValue, canonicalBodyOutput, one_ne_zero, ↓reduceIte, Bool.false_eq_true]
        at hfirstPhase
  obtain ⟨second, secondRest, hsecond, hsecondAccept⟩ :=
    canonicalBodyOutput_literal_extract
      firstRest 1 binary hfirstNonempty hfirstPhase
  have hsecondPhase :
      canonicalBodyOutput secondRest false 2 0 [] binary = true := by
    simpa only [Fin.isValue, Fin.reduceEq, ↓reduceIte, nextLiteralPosition, one_ne_zero]
        using hsecondAccept
  have hsecondNonempty : secondRest ≠ [] := by
    intro hempty
    subst secondRest
    simp only [Fin.isValue, canonicalBodyOutput, Fin.reduceEq, ↓reduceIte, Bool.false_eq_true]
        at hsecondPhase
  obtain ⟨third, suffix, hthird, hthirdAccept⟩ :=
    canonicalBodyOutput_literal_extract
      secondRest 2 binary hsecondNonempty hsecondPhase
  simp only [↓reduceIte] at hthirdAccept
  cases hdecrement : binaryStackDecrement binary with
  | none =>
      simp only [hdecrement, Bool.false_eq_true] at hthirdAccept
  | some remaining =>
      have hremaining :
          canonicalBodyOutput suffix false 0 0 [] remaining = true := by
        simpa only [Fin.isValue, hdecrement] using hthirdAccept
      refine ⟨![first, second, third], suffix, remaining,
        ?_, rfl, hremaining⟩
      calc
        input = BinaryEncoding.encodeLiteral first ++
            firstRest := hfirst
        _ = BinaryEncoding.encodeLiteral first ++
            (BinaryEncoding.encodeLiteral second ++
              secondRest) := by rw [hsecond]
        _ = BinaryEncoding.encodeLiteral first ++
            (BinaryEncoding.encodeLiteral second ++
              (BinaryEncoding.encodeLiteral third ++
                suffix)) := by rw [hthird]
        _ = BinaryEncoding.encodeThreeClause
              ![first, second, third] ++ suffix := by
              simp only [BinaryEncoding.encodeThreeClause, Fin.isValue, Matrix.cons_val_zero,
                  Matrix.cons_val_one,
                  Matrix.cons_val, List.append_assoc]

theorem readLengthPrefixedWord_some_reconstruct
    (input word suffix : List Bool)
    (hread : BinaryEncoding.readLengthPrefixedWord input =
      some (word, suffix)) :
    input = BinaryEncoding.lengthPrefixedWord word ++ suffix := by
  cases unaryInputSplit input with
  | inl witness =>
      obtain ⟨count, hshape⟩ := witness
      subst input
      simp only [BinaryEncoding.readLengthPrefixedWord, readUnaryPrefix_missing, reduceCtorEq]
          at hread
  | inr witness =>
      obtain ⟨count, tail, hshape⟩ := witness
      subst input
      by_cases hlength : count ≤ tail.length
      · have hpair :
            (tail.take count, tail.drop count) =
              (word, suffix) := by
          simpa only [Prod.mk.injEq, BinaryEncoding.readLengthPrefixedWord,
              BinaryEncoding.readUnaryPrefix_replicate,
              hlength, ↓reduceIte, Option.some.injEq] using hread
        cases hpair
        exact validInput_reconstruct count tail hlength
      · simp only [BinaryEncoding.readLengthPrefixedWord, BinaryEncoding.readUnaryPrefix_replicate,
          hlength,
            ↓reduceIte, reduceCtorEq] at hread

private theorem canonicalBodyOutput_accepted_extract
    (fuel : ℕ) (input binary : List Bool)
    (hlength : input.length ≤ fuel)
    (haccept : canonicalBodyOutput
      input false 0 0 [] binary = true) :
    ∃ clauses : ThreeCNF,
      input = clauses.flatMap
        BinaryEncoding.encodeThreeClause ∧
      clauses.length = binaryStackValue binary := by
  induction fuel using Nat.strong_induction_on
      generalizing input binary with
  | h fuel ih =>
      by_cases hempty : input = []
      · subst input
        have hzero : binaryStackValue binary = 0 := by
          simpa only [Fin.isValue, canonicalBodyOutput, ↓reduceIte, decide_eq_true_eq]
              using haccept
        exact ⟨[], rfl, hzero.symm⟩
      · obtain ⟨clause, suffix, remaining,
          hshape, hdecrement, hrest⟩ :=
          canonicalBodyOutput_clause_extract
            input binary hempty haccept
        have hclause :
            0 < (BinaryEncoding.encodeThreeClause
              clause).length := by
          simp only [BinaryEncoding.encodeThreeClause, BinaryEncoding.encodeLiteral,
              BinaryEncoding.lengthPrefixedWord,
              Fin.isValue, List.append_assoc, List.cons_append, List.nil_append,
                  List.length_append, List.length_replicate,
              List.length_cons, List.length_nil, zero_add, add_pos_iff, Order.lt_add_one_iff,
                  zero_le, or_true]
        have hshort : suffix.length < fuel := by
          have hinputlength :
              input.length =
                (BinaryEncoding.encodeThreeClause
                  clause).length + suffix.length := by
            rw [hshape, List.length_append]
          omega
        obtain ⟨clauses, hsuffix, hcount⟩ :=
          ih suffix.length hshort suffix remaining
            (Nat.le_refl _) hrest
        refine ⟨clause :: clauses, ?_, ?_⟩
        · simpa only [List.flatMap_cons, hsuffix] using hshape
        · have hvalue := binaryStackDecrement_value
            binary remaining hdecrement
          simp only [List.length_cons]
          omega

private theorem canonicalBodyOutput_clauses_valid
    (clauses : ThreeCNF) (binary : List Bool)
    (hcount : binaryStackValue binary = clauses.length) :
    canonicalBodyOutput
      (clauses.flatMap BinaryEncoding.encodeThreeClause)
      false 0 0 [] binary = true := by
  induction clauses generalizing binary with
  | nil =>
      simp only [List.flatMap_nil, Fin.isValue, canonicalBodyOutput, ↓reduceIte, hcount,
          List.length_nil,
          decide_true]
  | cons clause clauses ih =>
      have hpositive : 0 < binaryStackValue binary := by
        simp only [List.length_cons] at hcount
        omega
      cases hdecrement : binaryStackDecrement binary with
      | none =>
          obtain ⟨zeros, tail, hshape⟩ :=
            positiveBinarySplit binary hpositive
          rw [hshape, binaryStackDecrement_replicate] at hdecrement
          simp only [reduceCtorEq] at hdecrement
      | some remaining =>
          have hremaining :
              binaryStackValue remaining = clauses.length := by
            have hvalue := binaryStackDecrement_value
              binary remaining hdecrement
            simp only [List.length_cons] at hcount
            omega
          simp only [List.flatMap_cons, Fin.isValue, canonicalBodyOutput_clause, hdecrement, ih
              remaining hremaining]

private theorem canonicalBodyOutput_eq_true_iff
    (input binary : List Bool) :
    canonicalBodyOutput input false 0 0 [] binary = true ↔
      ∃ clauses : ThreeCNF,
        input = clauses.flatMap
          BinaryEncoding.encodeThreeClause ∧
        clauses.length = binaryStackValue binary := by
  constructor
  · intro haccept
    exact canonicalBodyOutput_accepted_extract
      input.length input binary (Nat.le_refl _) haccept
  · rintro ⟨clauses, hshape, hcount⟩
    subst input
    exact canonicalBodyOutput_clauses_valid
      clauses binary hcount.symm

@[simp] private theorem canonicalMachineOutput_encodeThreeCNF
    (clauses : ThreeCNF) :
    canonicalMachineOutput
      (BinaryEncoding.encodeThreeCNF clauses) = [true] := by
  rw [BinaryEncoding.encodeThreeCNF]
  rw [canonicalMachineOutput_lengthPrefixed]
  rw [encodeNat_canonical]
  simp only [↓reduceIte]
  congr 1
  apply canonicalBodyOutput_clauses_valid
  exact binaryStackValue_encodeNat clauses.length

private theorem canonicalMachineOutput_eq_true_iff (input : List Bool) :
    canonicalMachineOutput input = [true] ↔
      ∃ clauses : ThreeCNF,
        BinaryEncoding.encodeThreeCNF clauses = input := by
  constructor
  · intro haccept
    cases hread :
        BinaryEncoding.readLengthPrefixedWord input with
    | none =>
        simp only [canonicalMachineOutput, hread, List.cons.injEq, Bool.false_eq_true, and_true]
            at haccept
    | some parsed =>
        obtain ⟨header, body⟩ := parsed
        cases hcanonical : isCanonicalBinaryWord header with
        | false =>
            simp only [canonicalMachineOutput, hread, hcanonical, Bool.false_eq_true, ↓reduceIte,
                List.cons.injEq,
                and_true] at haccept
        | true =>
            have hbody :
                canonicalBodyOutput body
                  false 0 0 [] header = true := by
              simpa only [Fin.isValue, canonicalMachineOutput, hread, hcanonical, ↓reduceIte,
                  List.cons.injEq,
                  and_true] using haccept
            obtain ⟨clauses, hshape, hcount⟩ :=
              (canonicalBodyOutput_eq_true_iff body header).mp hbody
            have hheader :
                Computability.encodeNat clauses.length = header := by
              rw [hcount]
              exact canonicalBinaryWord_encodeNat header hcanonical
            have hinput := readLengthPrefixedWord_some_reconstruct
              input header body hread
            refine ⟨clauses, ?_⟩
            calc
              BinaryEncoding.encodeThreeCNF clauses =
                  BinaryEncoding.lengthPrefixedWord
                    header ++ clauses.flatMap
                      BinaryEncoding.encodeThreeClause := by
                    simp only [BinaryEncoding.encodeThreeCNF, hheader]
              _ = BinaryEncoding.lengthPrefixedWord
                    header ++ body := by rw [← hshape]
              _ = input := hinput.symm
  · rintro ⟨clauses, rfl⟩
    exact canonicalMachineOutput_encodeThreeCNF clauses

private theorem canonicalMachineOutput_boolean (input : List Bool) :
    canonicalMachineOutput input = [true] ∨
      canonicalMachineOutput input = [false] := by
  cases hread :
      BinaryEncoding.readLengthPrefixedWord input with
  | none =>
      exact Or.inr (by simp only [canonicalMachineOutput, hread])
  | some parsed =>
      obtain ⟨header, body⟩ := parsed
      cases hcanonical : isCanonicalBinaryWord header with
      | false =>
          exact Or.inr (by
            simp only [canonicalMachineOutput, hread, hcanonical, Bool.false_eq_true, ↓reduceIte])
      | true =>
          cases hbody : canonicalBodyOutput
              body false 0 0 [] header with
          | false =>
              exact Or.inr (by
                simp only [canonicalMachineOutput, hread, hcanonical, ↓reduceIte, Fin.isValue,
                    hbody])
          | true =>
              exact Or.inl (by
                simp only [canonicalMachineOutput, hread, hcanonical, ↓reduceIte, Fin.isValue,
                    hbody])

private theorem canonicalFormulaExpected_boolean (input : List Bool) :
    canonicalFormulaExpected input = [true] ∨
      canonicalFormulaExpected input = [false] := by
  cases hdecode : BinaryEncoding.decodeThreeCNF input with
  | none =>
      exact Or.inr (by
        simp only [canonicalFormulaExpected, hdecode])
  | some clauses =>
      by_cases hcanonical :
          BinaryEncoding.encodeThreeCNF clauses = input
      · exact Or.inl (by
          simp only [canonicalFormulaExpected, hdecode, hcanonical, ↓reduceIte])
      · exact Or.inr (by
          simp only [canonicalFormulaExpected, hdecode, hcanonical, ↓reduceIte])

theorem canonicalMachineOutput_eq_expected (input : List Bool) :
    canonicalMachineOutput input = canonicalFormulaExpected input := by
  rcases canonicalMachineOutput_boolean input with hmachine | hmachine
  · have himage :=
      (canonicalMachineOutput_eq_true_iff input).mp hmachine
    have hexpected :=
      (canonicalFormulaExpected_eq_true_iff input).mpr himage
    exact hmachine.trans hexpected.symm
  · rcases canonicalFormulaExpected_boolean input with
      hexpected | hexpected
    · have himage :=
        (canonicalFormulaExpected_eq_true_iff input).mp hexpected
      have haccept :=
        (canonicalMachineOutput_eq_true_iff input).mpr himage
      rw [hmachine] at haccept
      simp only [List.cons.injEq, Bool.false_eq_true, and_true] at haccept
    · exact hmachine.trans hexpected.symm

end FormulaSemanticCert

namespace CLStructuralNaturalBinaryWriter

open Turing

private def structuralBinaryIncrement : List Bool → List Bool
  | [] => [true]
  | false :: digits => true :: digits
  | true :: digits => false :: structuralBinaryIncrement digits

private theorem structuralBinaryIncrement_encodePosNum
    (number : PosNum) :
    structuralBinaryIncrement
        (Computability.encodePosNum number) =
      Computability.encodePosNum (PosNum.succ number) := by
  induction number with
  | one =>
      rfl
  | bit0 number ih =>
      rfl
  | bit1 number ih =>
      simp only [Computability.encodePosNum, structuralBinaryIncrement, ih, PosNum.succ]

private theorem structuralBinaryIncrement_encodeNat (number : ℕ) :
    structuralBinaryIncrement (Computability.encodeNat number) =
      Computability.encodeNat (number + 1) := by
  have hsucc :
      ((number + 1 : ℕ) : Num) =
        Num.succ (number : Num) := by
    apply Num.to_nat_inj.mp
    rw [Num.to_of_nat, Num.succ_to_nat, Num.to_of_nat]
  change structuralBinaryIncrement
      (Computability.encodeNum (number : Num)) =
    Computability.encodeNum ((number + 1 : ℕ) : Num)
  rw [hsucc]
  generalize (number : Num) = encoded
  cases encoded with
  | zero =>
      rfl
  | pos positive =>
      simpa only [Computability.encodeNum, Num.succ, Num.succ'] using
          structuralBinaryIncrement_encodePosNum positive

private def structuralBinaryCarrySplit : List Bool → ℕ × List Bool
  | [] => (0, [true])
  | false :: digits => (0, true :: digits)
  | true :: digits =>
      let result := structuralBinaryCarrySplit digits
      (result.1 + 1, result.2)

private theorem structuralBinaryIncrement_eq_carrySplit
    (digits : List Bool) :
    structuralBinaryIncrement digits =
      List.replicate (structuralBinaryCarrySplit digits).1 false ++
        (structuralBinaryCarrySplit digits).2 := by
  induction digits with
  | nil =>
      simp only [structuralBinaryIncrement, structuralBinaryCarrySplit, List.replicate_zero,
          List.nil_append]
  | cons bit digits ih =>
      cases bit with
      | false =>
          simp only [structuralBinaryIncrement, structuralBinaryCarrySplit, List.replicate_zero,
              List.nil_append]
      | true =>
          simp only [structuralBinaryIncrement, ih, structuralBinaryCarrySplit,
              List.replicate_succ, List.cons_append]

private theorem structuralBinaryCarrySplit_count_le
    (digits : List Bool) :
    (structuralBinaryCarrySplit digits).1 ≤ digits.length := by
  induction digits with
  | nil =>
      simp only [structuralBinaryCarrySplit, List.length_nil, Std.le_refl]
  | cons bit digits ih =>
      cases bit <;> simp [structuralBinaryCarrySplit, ih]

private theorem structuralBinaryIncrement_length_le
    (digits : List Bool) :
    (structuralBinaryIncrement digits).length ≤ digits.length + 1 := by
  induction digits with
  | nil =>
      simp only [structuralBinaryIncrement, List.length_cons, List.length_nil, zero_add,
          Std.le_refl]
  | cons bit digits ih =>
      cases bit with
      | false =>
          simp only [structuralBinaryIncrement, List.length_cons, le_add_iff_nonneg_right, zero_le]
      | true =>
          simpa only [structuralBinaryIncrement, List.length_cons, Nat.add_assoc, Nat.reduceAdd,
              add_le_add_iff_right] using Nat.add_le_add_right ih 1

private def structuralBinaryIncrementN : ℕ → List Bool → List Bool
  | 0, digits => digits
  | count + 1, digits =>
      structuralBinaryIncrementN count
        (structuralBinaryIncrement digits)

private theorem structuralBinaryIncrementN_encodeNat
    (count number : ℕ) :
    structuralBinaryIncrementN count
        (Computability.encodeNat number) =
      Computability.encodeNat (number + count) := by
  induction count generalizing number with
  | zero =>
      simp only [structuralBinaryIncrementN, add_zero]
  | succ count ih =>
      rw [structuralBinaryIncrementN,
        structuralBinaryIncrement_encodeNat, ih]
      congr 1
      omega

private theorem structuralBinaryIncrementN_length_le
    (count : ℕ) (digits : List Bool) :
    (structuralBinaryIncrementN count digits).length ≤
      digits.length + count := by
  induction count generalizing digits with
  | zero =>
      simp only [structuralBinaryIncrementN, add_zero, Std.le_refl]
  | succ count ih =>
      have hcarry := structuralBinaryIncrement_length_le digits
      have hrest := ih (structuralBinaryIncrement digits)
      simp only [structuralBinaryIncrementN]
      omega

private def naturalBinaryWriterPeek (stack : Fin 4)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool) :=
  .peek stack (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome) present absent)

private def naturalBinaryWriterPop (stack : Fin 4)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool) :=
  .pop stack (fun symbol _ => symbol) continuation

private def naturalBinaryWriterPushBit (stack : Fin 4)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool) :=
  .push stack (fun symbol => symbol.getD false) continuation

private def naturalBinaryWriterPushConstant (stack : Fin 4) (bit : Bool)
    (continuation : Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool) :=
  .push stack (fun _ => bit) continuation

private def naturalBinaryWriterGoto (phase : Fin 5) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => phase))

private def naturalBinaryWriterInputStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool) :=
  naturalBinaryWriterPeek 0
    (naturalBinaryWriterPop 0 (naturalBinaryWriterGoto 1))
    (naturalBinaryWriterGoto 3)

private def naturalBinaryWriterCarryStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool) :=
  naturalBinaryWriterPeek 1
    (.branch (fun symbol => symbol == some true)
      (naturalBinaryWriterPop 1
        (naturalBinaryWriterPushConstant 2 false
          (naturalBinaryWriterGoto 1)))
      (naturalBinaryWriterPop 1
        (naturalBinaryWriterPushConstant 1 true
          (naturalBinaryWriterGoto 2))))
    (naturalBinaryWriterPushConstant 1 true
      (naturalBinaryWriterGoto 2))

private def naturalBinaryWriterRestoreStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool) :=
  naturalBinaryWriterPeek 2
    (naturalBinaryWriterPop 2
      (naturalBinaryWriterPushBit 1
        (naturalBinaryWriterGoto 2)))
    (naturalBinaryWriterGoto 0)

private def naturalBinaryWriterPrepareStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool) :=
  naturalBinaryWriterPeek 1
    (naturalBinaryWriterPop 1
      (naturalBinaryWriterPushBit 2
        (naturalBinaryWriterGoto 3)))
    (naturalBinaryWriterGoto 4)

private def naturalBinaryWriterOutputStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool) :=
  naturalBinaryWriterPeek 2
    (naturalBinaryWriterPop 2
      (naturalBinaryWriterPushBit 3
        (naturalBinaryWriterGoto 4)))
    .halt

private abbrev structuralNaturalBinaryWriter : Turing.FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Fin 5
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 5) then
      naturalBinaryWriterInputStatement
    else if phase = (1 : Fin 5) then
      naturalBinaryWriterCarryStatement
    else if phase = (2 : Fin 5) then
      naturalBinaryWriterRestoreStatement
    else if phase = (3 : Fin 5) then
      naturalBinaryWriterPrepareStatement
    else
      naturalBinaryWriterOutputStatement

private def naturalBinaryWriterConfiguration (phase : Fin 5)
    (input digits carry output : List Bool) :
    structuralNaturalBinaryWriter.Cfg where
  l := some phase
  var := none
  stk := ![input, digits, carry, output]

private theorem structuralNaturalBinaryWriter_init (input : List Bool) :
    Turing.initList structuralNaturalBinaryWriter input =
      naturalBinaryWriterConfiguration 0 input [] [] [] := by
  simp only [structuralNaturalBinaryWriter, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq,
      dite_eq_ite,
      naturalBinaryWriterConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `naturalBinaryWriterStepTac` machine-step simplifier. -/
macro "naturalBinaryWriterStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [structuralNaturalBinaryWriter,
          naturalBinaryWriterConfiguration, naturalBinaryWriterPeek,
          naturalBinaryWriterPop, naturalBinaryWriterPushBit,
          naturalBinaryWriterPushConstant, naturalBinaryWriterGoto,
          naturalBinaryWriterInputStatement,
          naturalBinaryWriterCarryStatement,
          naturalBinaryWriterRestoreStatement,
          naturalBinaryWriterPrepareStatement,
          naturalBinaryWriterOutputStatement,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

private theorem naturalBinaryWriter_input_step (bit : Bool)
    (input digits carry output : List Bool) :
    structuralNaturalBinaryWriter.step
      (naturalBinaryWriterConfiguration 0
        (bit :: input) digits carry output) =
      some (naturalBinaryWriterConfiguration 1
        input digits carry output) := by
  cases bit <;> naturalBinaryWriterStepTac

private theorem naturalBinaryWriter_input_finish
    (digits carry output : List Bool) :
    structuralNaturalBinaryWriter.step
      (naturalBinaryWriterConfiguration 0 [] digits carry output) =
      some (naturalBinaryWriterConfiguration 3
        [] digits carry output) := by
  naturalBinaryWriterStepTac

private theorem naturalBinaryWriter_carry_true_step
    (input digits carry output : List Bool) :
    structuralNaturalBinaryWriter.step
      (naturalBinaryWriterConfiguration 1
        input (true :: digits) carry output) =
      some (naturalBinaryWriterConfiguration 1
        input digits (false :: carry) output) := by
  naturalBinaryWriterStepTac

private theorem naturalBinaryWriter_carry_false_step
    (input digits carry output : List Bool) :
    structuralNaturalBinaryWriter.step
      (naturalBinaryWriterConfiguration 1
        input (false :: digits) carry output) =
      some (naturalBinaryWriterConfiguration 2
        input (true :: digits) carry output) := by
  naturalBinaryWriterStepTac

private theorem naturalBinaryWriter_carry_empty_step
    (input carry output : List Bool) :
    structuralNaturalBinaryWriter.step
      (naturalBinaryWriterConfiguration 1
        input [] carry output) =
      some (naturalBinaryWriterConfiguration 2
        input [true] carry output) := by
  naturalBinaryWriterStepTac

private theorem naturalBinaryWriter_restore_step (bit : Bool)
    (input digits carry output : List Bool) :
    structuralNaturalBinaryWriter.step
      (naturalBinaryWriterConfiguration 2
        input digits (bit :: carry) output) =
      some (naturalBinaryWriterConfiguration 2
        input (bit :: digits) carry output) := by
  cases bit <;> naturalBinaryWriterStepTac

private theorem naturalBinaryWriter_restore_finish
    (input digits output : List Bool) :
    structuralNaturalBinaryWriter.step
      (naturalBinaryWriterConfiguration 2
        input digits [] output) =
      some (naturalBinaryWriterConfiguration 0
        input digits [] output) := by
  naturalBinaryWriterStepTac

private theorem naturalBinaryWriter_prepare_step (bit : Bool)
    (digits carry output : List Bool) :
    structuralNaturalBinaryWriter.step
      (naturalBinaryWriterConfiguration 3
        [] (bit :: digits) carry output) =
      some (naturalBinaryWriterConfiguration 3
        [] digits (bit :: carry) output) := by
  cases bit <;> naturalBinaryWriterStepTac

private theorem naturalBinaryWriter_prepare_finish
    (carry output : List Bool) :
    structuralNaturalBinaryWriter.step
      (naturalBinaryWriterConfiguration 3 [] [] carry output) =
      some (naturalBinaryWriterConfiguration 4
        [] [] carry output) := by
  naturalBinaryWriterStepTac

private theorem naturalBinaryWriter_output_step (bit : Bool)
    (carry output : List Bool) :
    structuralNaturalBinaryWriter.step
      (naturalBinaryWriterConfiguration 4
        [] [] (bit :: carry) output) =
      some (naturalBinaryWriterConfiguration 4
        [] [] carry (bit :: output)) := by
  cases bit <;> naturalBinaryWriterStepTac

private theorem naturalBinaryWriter_output_finish (output : List Bool) :
    structuralNaturalBinaryWriter.step
      (naturalBinaryWriterConfiguration 4 [] [] [] output) =
      some (Turing.haltList structuralNaturalBinaryWriter output) := by
  naturalBinaryWriterStepTac

private def naturalBinaryWriter_carrySearchTrace
    (input digits carry output : List Bool) :
    EvalsToInTime structuralNaturalBinaryWriter.step (naturalBinaryWriterConfiguration 1
        input digits carry output)
      (some (naturalBinaryWriterConfiguration 2
        input (structuralBinaryCarrySplit digits).2
        (List.replicate (structuralBinaryCarrySplit digits).1 false ++
          carry)
        output))
      (digits.length + 1) := by
  induction digits generalizing carry with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, structuralBinaryCarrySplit, List.replicate_zero,
          List.nil_append,
          List.length_nil, zero_add] using oneStep _ _ (naturalBinaryWriter_carry_empty_step input
              carry output)
  | cons bit digits ih =>
      cases bit with
      | false =>
          have hstep := oneStep _ _ (naturalBinaryWriter_carry_false_step
              input digits carry output)
          have hbounded := rebound (newBudget := (false :: digits).length + 1)
            hstep (by simp only [List.length_cons, le_add_iff_nonneg_left, zero_le])
          simpa only [FinTM2.step, Fin.isValue, structuralBinaryCarrySplit, List.replicate_zero,
              List.nil_append,
              List.length_cons] using hbounded
      | true =>
          have hfirst := oneStep _ _ (naturalBinaryWriter_carry_true_step
              input digits carry output)
          have hrest := ih (false :: carry)
          have hfull := EvalsToInTime.trans structuralNaturalBinaryWriter.step
              _ _ _ _ _ hfirst hrest
          simpa only [FinTM2.step, Fin.isValue, structuralBinaryCarrySplit, List.replicate_succ',
              List.append_assoc,
              List.cons_append, List.nil_append, List.length_cons, Nat.add_assoc, Nat.reduceAdd]
                  using hfull

private def naturalBinaryWriter_carryRestoreTrace
    (input digits carry output : List Bool) :
    EvalsToInTime structuralNaturalBinaryWriter.step (naturalBinaryWriterConfiguration 2
        input digits carry output)
      (some (naturalBinaryWriterConfiguration 0
        input (carry.reverse ++ digits) [] output))
      (carry.length + 1) := by
  induction carry generalizing digits with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (naturalBinaryWriter_restore_finish input digits output)
  | cons bit carry ih =>
      have hfirst := oneStep _ _ (naturalBinaryWriter_restore_step bit
          input digits carry output)
      have hrest := ih (bit :: digits)
      have hfull := EvalsToInTime.trans structuralNaturalBinaryWriter.step _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hfull

private def naturalBinaryWriter_carryTrace
    (input digits output : List Bool) :
    EvalsToInTime structuralNaturalBinaryWriter.step (naturalBinaryWriterConfiguration 1
        input digits [] output)
      (some (naturalBinaryWriterConfiguration 0
        input (structuralBinaryIncrement digits) [] output))
      (2 * digits.length + 2) := by
  have hsearch := naturalBinaryWriter_carrySearchTrace
    input digits [] output
  simp only [List.append_nil] at hsearch
  have hrestore := naturalBinaryWriter_carryRestoreTrace
    input (structuralBinaryCarrySplit digits).2
    (List.replicate (structuralBinaryCarrySplit digits).1 false)
    output
  simp only [List.reverse_replicate, List.length_replicate] at hrestore
  have hfull := EvalsToInTime.trans structuralNaturalBinaryWriter.step _ _ _ _ _ hsearch hrestore
  rw [← structuralBinaryIncrement_eq_carrySplit digits] at hfull
  have hcount := structuralBinaryCarrySplit_count_le digits
  exact rebound hfull (by omega)

private def naturalBinaryWriterScanBudget : List Bool → List Bool → ℕ
  | [], _ => 1
  | _ :: input, digits =>
      1 + (2 * digits.length + 2) +
        naturalBinaryWriterScanBudget input
          (structuralBinaryIncrement digits)

private def naturalBinaryWriter_scanTrace
    (input digits output : List Bool) :
    EvalsToInTime structuralNaturalBinaryWriter.step (naturalBinaryWriterConfiguration 0
        input digits [] output)
      (some (naturalBinaryWriterConfiguration 3 []
        (structuralBinaryIncrementN input.length digits)
        [] output))
      (naturalBinaryWriterScanBudget input digits) := by
  induction input generalizing digits with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, structuralBinaryIncrementN,
          naturalBinaryWriterScanBudget] using oneStep _ _ (naturalBinaryWriter_input_finish digits
              [] output)
  | cons bit input ih =>
      have hfirst := oneStep _ _ (naturalBinaryWriter_input_step bit
          input digits [] output)
      have hcarry := naturalBinaryWriter_carryTrace
        input digits output
      have hrest := ih (structuralBinaryIncrement digits)
      have hfirstCarry := EvalsToInTime.trans structuralNaturalBinaryWriter.step
          _ _ _ _ _ hfirst hcarry
      have hfull := EvalsToInTime.trans structuralNaturalBinaryWriter.step
          _ _ _ _ _ hfirstCarry hrest
      have hbounded := rebound (newBudget :=
          naturalBinaryWriterScanBudget (bit :: input) digits)
        hfull (by
          simp only [naturalBinaryWriterScanBudget]
          omega)
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, structuralBinaryIncrementN]
          using hbounded

private theorem naturalBinaryWriterScanBudget_le
    (input digits : List Bool) :
    naturalBinaryWriterScanBudget input digits ≤
      2 * input.length * (digits.length + input.length + 1) + 1 := by
  induction input generalizing digits with
  | nil =>
      simp only [naturalBinaryWriterScanBudget, List.length_nil, mul_zero, add_zero, zero_mul,
          zero_add,
          Std.le_refl]
  | cons bit input ih =>
      have hrecursive := ih (structuralBinaryIncrement digits)
      have hlength := structuralBinaryIncrement_length_le digits
      have hmonotone :
          2 * input.length *
              ((structuralBinaryIncrement digits).length +
                input.length + 1) ≤
            2 * input.length *
              (digits.length + input.length + 2) := by
        apply Nat.mul_le_mul_left
        omega
      calc
        naturalBinaryWriterScanBudget (bit :: input) digits =
            1 + (2 * digits.length + 2) +
              naturalBinaryWriterScanBudget input
                (structuralBinaryIncrement digits) := rfl
        _ ≤ 1 + (2 * digits.length + 2) +
              (2 * input.length *
                (digits.length + input.length + 2) + 1) := by
              omega
        _ ≤ 2 * (bit :: input).length *
              (digits.length + (bit :: input).length + 1) + 1 := by
              simp only [List.length_cons]
              linarith

private def naturalBinaryWriter_prepareTrace
    (digits carry output : List Bool) :
    EvalsToInTime structuralNaturalBinaryWriter.step (naturalBinaryWriterConfiguration 3
        [] digits carry output)
      (some (naturalBinaryWriterConfiguration 4
        [] [] (digits.reverse ++ carry) output))
      (digits.length + 1) := by
  induction digits generalizing carry with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (naturalBinaryWriter_prepare_finish carry output)
  | cons bit digits ih =>
      have hfirst := oneStep _ _ (naturalBinaryWriter_prepare_step bit digits carry output)
      have hrest := ih (bit :: carry)
      have hfull := EvalsToInTime.trans structuralNaturalBinaryWriter.step _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hfull

private def naturalBinaryWriter_outputTrace
    (carry output : List Bool) :
    EvalsToInTime structuralNaturalBinaryWriter.step (naturalBinaryWriterConfiguration 4
        [] [] carry output)
      (some (Turing.haltList structuralNaturalBinaryWriter
        (carry.reverse ++ output)))
      (carry.length + 1) := by
  induction carry generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (naturalBinaryWriter_output_finish output)
  | cons bit carry ih =>
      have hfirst := oneStep _ _ (naturalBinaryWriter_output_step bit carry output)
      have hrest := ih (bit :: output)
      have hfull := EvalsToInTime.trans structuralNaturalBinaryWriter.step _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hfull

private def naturalBinaryWriter_totalTrace (input : List Bool) :
    EvalsToInTime structuralNaturalBinaryWriter.step
      (naturalBinaryWriterConfiguration 0 input [] [] [])
      (some (Turing.haltList structuralNaturalBinaryWriter
        (Computability.encodeNat input.length)))
      (8 * (input.length + 1) ^ 2 + 8) := by
  have hdigits :
      structuralBinaryIncrementN input.length [] =
        Computability.encodeNat input.length := by
    simpa only [Computability.encodeNat, Computability.encodeNum, CharP.cast_eq_zero, zero_add]
        using
        structuralBinaryIncrementN_encodeNat input.length 0
  have hscan := naturalBinaryWriter_scanTrace input [] []
  rw [hdigits] at hscan
  have hprepare := naturalBinaryWriter_prepareTrace
    (Computability.encodeNat input.length) [] []
  simp only [List.append_nil] at hprepare
  have houtput := naturalBinaryWriter_outputTrace
    (Computability.encodeNat input.length).reverse []
  simp only [List.reverse_reverse, List.append_nil] at houtput
  have hfirst := EvalsToInTime.trans structuralNaturalBinaryWriter.step _ _ _ _ _ hscan hprepare
  have hfull := EvalsToInTime.trans structuralNaturalBinaryWriter.step _ _ _ _ _ hfirst houtput
  have hscanBound := naturalBinaryWriterScanBudget_le input []
  simp only [List.length_nil, Nat.zero_add] at hscanBound
  have hdigitBound := structuralBinaryIncrementN_length_le
    input.length []
  rw [hdigits] at hdigitBound
  simp only [List.length_nil, Nat.zero_add] at hdigitBound
  have htotal :
      (Computability.encodeNat input.length).length + 1 +
        ((Computability.encodeNat input.length).length + 1 +
          naturalBinaryWriterScanBudget input []) ≤
        8 * (input.length + 1) ^ 2 + 8 := by
    linarith [sq_nonneg (input.length + 1)]
  exact rebound hfull (by
    simpa only [List.length_reverse] using htotal)

/-- GapCVP reduction support. -/
noncomputable def structuralNaturalBinaryWriterComputable :
    Turing.TM2ComputableInPolyTime GapCVP.bitEncoding
      GapCVP.bitEncoding
      (fun input : List Bool =>
        Computability.encodeNat input.length) where
  tm := structuralNaturalBinaryWriter
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 8 * (Polynomial.X + 1) ^ 2 + 8
  outputsFun input := {
    steps := (naturalBinaryWriter_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, structuralNaturalBinaryWriter_init,
              Option.map_some] using
          (naturalBinaryWriter_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (naturalBinaryWriter_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq, Polynomial.eval_add,
          Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
              ge_iff_le] using hsteps
  }

end CLStructuralNaturalBinaryWriter

namespace CLStructuralAtomicNaturalWriter

open GapCVP.BinaryEncoding GapCVP.CLStructuralPrefixWriter
open GapCVP.CLStructuralNaturalBinaryWriter

/-- GapCVP reduction support. -/
def structuralAtomicNaturalWord (input : List Bool) : List Bool :=
  encodeAtomic input.length

theorem structuralAtomicNaturalWord_eq_prefix (input : List Bool) :
    structuralAtomicNaturalWord input =
      lengthPrefixedWord (Computability.encodeNat input.length) := by
  rfl

/-- GapCVP reduction support. -/
noncomputable def structuralAtomicNaturalWriterComputable :
    Turing.TM2ComputableInPolyTime GapCVP.bitEncoding
      GapCVP.bitEncoding structuralAtomicNaturalWord := by
  have hcomposite :=
    GapCVP.TMComposition.computableInPolyTime
      structuralNaturalBinaryWriterComputable
      structuralPrefixWriterComputable
  change Turing.TM2ComputableInPolyTime GapCVP.bitEncoding
    GapCVP.bitEncoding
    (fun input : List Bool =>
      lengthPrefixedWord (Computability.encodeNat input.length))
  simpa only [Function.comp_def] using hcomposite

end CLStructuralAtomicNaturalWriter

namespace CLStructuralWholeCNFOutputTM

open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLCellRowBounds GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction

/-- GapCVP reduction support. -/
def paddedStructuralTableauSimulation
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    TableauSimulation bound machine :=
  tableauSimulationOfLocalCompiler bound machine
    (paddedAcceptanceLocalTableauCompiler bound machine)

/-- GapCVP reduction support. -/
def structuralWholeSourceClauses
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    List (Clause (rowWidth bound machine x)
      (completePhaseSymbolCount machine.tm)) :=
  sortedElements
    (tableauFormula (paddedAcceptancePhaseSpecification
      bound machine x))

/-- GapCVP reduction support. -/
def structuralWholeThreeCNF
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) : GapCVP.ThreeCNF :=
  encodeFormulaFrom 0
    (structuralWholeSourceClauses bound machine x)

/-- GapCVP reduction support. -/
def structuralWholeCNFWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) : List Bool :=
  encodeThreeCNF (structuralWholeThreeCNF bound machine x)

private theorem structuralWholeThreeCNF_eq_encodeTableau
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    structuralWholeThreeCNF bound machine x =
      ThreeCNFReduction.encodeTableau
        (paddedAcceptancePhaseSpecification bound machine x) := by
  rfl

private theorem structuralWholeCNFWord_eq_encodedTableau
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    structuralWholeCNFWord bound machine x =
      encodedTableau (paddedStructuralTableauSimulation
        bound machine) x := by
  rfl

theorem structuralWholeCNFWord_mem_threeSAT_iff
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    threeSATLanguage (structuralWholeCNFWord bound machine x) ↔
      ∃ certificate : List Bool,
        certificate.length ≤ bound.eval x.length ∧
          verifier (x, certificate) = true := by
  rw [structuralWholeCNFWord_eq_encodedTableau]
  exact compiledTableau_iff_verifier bound machine
    (paddedAcceptanceLocalTableauCompiler bound machine) x

theorem structuralWholeThreeCNF_allDistinct
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    allDistinct (structuralWholeThreeCNF bound machine x) := by
  rw [structuralWholeThreeCNF_eq_encodeTableau]
  exact encodeFormula_allDistinct
    (tableauFormula
      (paddedAcceptancePhaseSpecification bound machine x))

theorem structuralNatSize_le_self (value : ℕ) :
    Nat.size value ≤ value := by
  exact Nat.size_le.mpr Nat.lt_two_pow_self

end CLStructuralWholeCNFOutputTM

namespace CNFClauseLoop

open Computability Turing

/-- GapCVP reduction support. -/
def clauseLoopFiniteElements (α : Type) [Fintype α] : List α :=
  List.ofFn (Fintype.equivFin α).symm

theorem mem_clauseLoopFiniteElements
    (α : Type) [Fintype α] (value : α) :
    value ∈ clauseLoopFiniteElements α := by
  simp only [clauseLoopFiniteElements, List.mem_ofFn]
  exact ⟨(Fintype.equivFin α) value, by simp only [Equiv.symm_apply_apply]⟩

end CNFClauseLoop

namespace CNFSortingDedup

open Computability Turing

theorem replicate_append_bit_cons
    (bit : Bool) (count : ℕ) (tail : List Bool) :
    List.replicate count bit ++ bit :: tail =
      bit :: (List.replicate count bit ++ tail) := by
  induction count with
  | zero => simp only [List.replicate_zero, List.nil_append]
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, ih]

end CNFSortingDedup

namespace CNFEncodedClauseSort

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.CNFSortingDedup

/-- GapCVP reduction support. -/
inductive EncodedWordOrdering where
  | invalid
  | less
  | equal
  | greater
  deriving DecidableEq

noncomputable instance : Fintype EncodedWordOrdering where
  elems := {.invalid, .less, .equal, .greater}
  complete ordering := by cases ordering <;> simp

/-- GapCVP reduction support. -/
def encodedWordOrderingFirst : EncodedWordOrdering → Bool
  | .invalid => false
  | .less => false
  | .equal => true
  | .greater => true

/-- GapCVP reduction support. -/
def encodedWordOrderingSecond : EncodedWordOrdering → Bool
  | .invalid => false
  | .less => true
  | .equal => false
  | .greater => true

/-- GapCVP reduction support. -/
def encodedWordOrderingWord (outcome : EncodedWordOrdering) : List Bool :=
  [encodedWordOrderingFirst outcome, encodedWordOrderingSecond outcome]

/-- GapCVP reduction support. -/
def lexicographicEncodedWordOrdering :
    List Bool → List Bool → EncodedWordOrdering
  | [], [] => .equal
  | [], _ :: _ => .less
  | _ :: _, [] => .greater
  | false :: _, true :: _ => .less
  | true :: _, false :: _ => .greater
  | false :: left, false :: right =>
      lexicographicEncodedWordOrdering left right
  | true :: left, true :: right =>
      lexicographicEncodedWordOrdering left right

/-- GapCVP reduction support. -/
def delimitedPairWordOrdering (input : List Bool) : EncodedWordOrdering :=
  match readLengthPrefixedWord input with
  | none => .invalid
  | some (first, suffix) =>
      match readLengthPrefixedWord suffix with
      | none => .invalid
      | some (second, _) =>
          lexicographicEncodedWordOrdering first second

/-- GapCVP reduction support. -/
def sourcePreservingDelimitedPairComparisonWord
    (input : List Bool) : List Bool :=
  lengthPrefixedWord input ++
    encodedWordOrderingWord (delimitedPairWordOrdering input)

theorem delimitedPairWordOrdering_valid
    (first second suffix : List Bool) :
    delimitedPairWordOrdering
      (lengthPrefixedWord first ++
        lengthPrefixedWord second ++ suffix) =
      lexicographicEncodedWordOrdering first second := by
  simp only [delimitedPairWordOrdering, List.append_assoc, readLengthPrefixedWord_append]

end CNFEncodedClauseSort

end GapCVP

end
