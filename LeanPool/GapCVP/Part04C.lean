/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part04B

/-! # GapCVP proof, part 04, continuation 03 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CLStructuralCNFOutputMachinesUnconditional

open Computability Turing GapCVP.BinaryEncoding GapCVP.CNFSortingDedup
open GapCVP.CNFPolynomialRowMarkerTM

private def polynomialRowMarker_scanTrace
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (input source base baseScratch accumulator product output : List Bool) :
    EvalsToInTime (polynomialRowMarkerMachine polynomial).step
      (polynomialRowMarkerConfiguration polynomial 0 stage
        input source base baseScratch accumulator product output)
      (some (polynomialRowMarkerConfiguration polynomial 1 stage
        [] (input.reverse ++ source)
        (List.replicate input.length true ++ base)
        baseScratch accumulator product output))
      (input.length + 1) := by
  induction input generalizing source base with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          List.replicate_zero,
          zero_add] using
          oneStep _ _ (polynomialRowMarker_scan_finish polynomial stage source base baseScratch
              accumulator product output)
  | cons bit remaining ih =>
      have hfirst := oneStep _ _ (polynomialRowMarker_scan_step polynomial stage bit remaining
          source base baseScratch accumulator product output)
      have hrest := ih (source := bit :: source) (base := true :: base)
      have hfull := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step
        _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, List.replicate_succ, Nat.add_assoc, Nat.reduceAdd,
              replicate_append_bit_cons] using hfull

private def polynomialRowMarker_baseTrace
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (baseCount : ℕ)
    (source baseScratch accumulator product output : List Bool) :
    EvalsToInTime (polynomialRowMarkerMachine polynomial).step
      (polynomialRowMarkerConfiguration polynomial 2 stage
        [] source (List.replicate baseCount true) baseScratch
        accumulator product output)
      (some (polynomialRowMarkerConfiguration polynomial 3 stage
        [] source [] (List.replicate baseCount true ++ baseScratch)
        accumulator (List.replicate baseCount true ++ product) output))
      (baseCount + 1) := by
  induction baseCount generalizing baseScratch product with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (polynomialRowMarker_base_finish polynomial stage source baseScratch
              accumulator product output)
  | succ count ih =>
      have hfirst := oneStep _ _ (polynomialRowMarker_base_step polynomial stage source
          (List.replicate count true) baseScratch accumulator product output)
      have hrest := ih (baseScratch := true :: baseScratch)
        (product := true :: product)
      have hfull := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step
        _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          replicate_append_bit_cons] using hfull

private def polynomialRowMarker_restoreBaseTrace
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (scratchCount : ℕ)
    (source base accumulator product output : List Bool) :
    EvalsToInTime (polynomialRowMarkerMachine polynomial).step
      (polynomialRowMarkerConfiguration polynomial 3 stage
        [] source base (List.replicate scratchCount true)
        accumulator product output)
      (some (polynomialRowMarkerConfiguration polynomial 1 stage
        [] source (List.replicate scratchCount true ++ base) []
        accumulator product output))
      (scratchCount + 1) := by
  induction scratchCount generalizing base with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (polynomialRowMarker_restoreBase_finish polynomial stage source base
              accumulator product output)
  | succ count ih =>
      have hfirst := oneStep _ _ (polynomialRowMarker_restoreBase_step polynomial stage source
          base (List.replicate count true) accumulator product output)
      have hrest := ih (base := true :: base)
      have hfull := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step
        _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          replicate_append_bit_cons] using hfull

private def polynomialRowMarker_multiplyTrace
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (baseCount accumulatorCount productCount : ℕ)
    (source output : List Bool) :
    EvalsToInTime (polynomialRowMarkerMachine polynomial).step
      (polynomialRowMarkerConfiguration polynomial 1 stage
        [] source (List.replicate baseCount true) []
        (List.replicate accumulatorCount true)
        (List.replicate productCount true) output)
      (some (polynomialRowMarkerConfiguration polynomial 4 stage
        [] source (List.replicate baseCount true) [] []
        (List.replicate
          (baseCount * accumulatorCount + productCount) true)
        output))
      (accumulatorCount * (2 * baseCount + 3) + 1) := by
  induction accumulatorCount generalizing productCount with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, mul_zero, zero_add, zero_mul]
          using
          oneStep _ _
            (polynomialRowMarker_multiply_finish polynomial stage source (List.replicate baseCount
                true) []
              (List.replicate productCount true) output)
  | succ count ih =>
      have hfirst := oneStep _ _ (polynomialRowMarker_multiply_step polynomial stage source
          (List.replicate baseCount true) []
          (List.replicate count true)
          (List.replicate productCount true) output)
      have hbase := polynomialRowMarker_baseTrace polynomial stage
        baseCount source [] (List.replicate count true)
        (List.replicate productCount true) output
      have hrestore := polynomialRowMarker_restoreBaseTrace
        polynomial stage baseCount source []
        (List.replicate count true)
        (List.replicate baseCount true ++
          List.replicate productCount true) output
      simp only [List.append_nil] at hbase hrestore
      have hprefix := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step
        _ _ _ _ _ hfirst hbase
      have hcycle := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step
        _ _ _ _ _ hprefix hrestore
      have hremaining := ih (productCount := baseCount + productCount)
      have hproduct :
          List.replicate (baseCount + productCount) true =
            List.replicate baseCount true ++
              List.replicate productCount true :=
        List.replicate_add baseCount productCount true
      have hremaining' :
          EvalsToInTime (polynomialRowMarkerMachine polynomial).step
            (polynomialRowMarkerConfiguration polynomial 1 stage
              [] source (List.replicate baseCount true) []
              (List.replicate count true)
              (List.replicate baseCount true ++
                List.replicate productCount true) output)
            (some (polynomialRowMarkerConfiguration polynomial 4 stage
              [] source (List.replicate baseCount true) [] []
              (List.replicate
                (baseCount * count + (baseCount + productCount)) true)
              output))
            (count * (2 * baseCount + 3) + 1) := by
        simpa only [hproduct] using hremaining
      have hfull := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step
        _ _ _ _ _ hcycle hremaining'
      have hproductCount :
          baseCount * count + (baseCount + productCount) =
            baseCount * (count + 1) + productCount := by
        ring
      have hbudget :
          (count * (2 * baseCount + 3) + 1) +
              ((baseCount + 1) + ((baseCount + 1) + 1)) =
            (count + 1) * (2 * baseCount + 3) + 1 := by
        ring
      rw [hproductCount, hbudget] at hfull
      simpa only [List.replicate_succ, Nat.succ_eq_add_one] using hfull

private def polynomialRowMarker_productTrace
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (productCount : ℕ)
    (source base accumulator output : List Bool) :
    EvalsToInTime (polynomialRowMarkerMachine polynomial).step
      (polynomialRowMarkerConfiguration polynomial 4 stage
        [] source base [] accumulator
        (List.replicate productCount true) output)
      (some (polynomialRowMarkerConfiguration polynomial 4 stage
        [] source base []
        (List.replicate productCount true ++ accumulator)
        [] output))
      productCount := by
  induction productCount generalizing accumulator with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append] using
          EvalsToInTime.refl (polynomialRowMarkerMachine polynomial).step
            (polynomialRowMarkerConfiguration polynomial 4 stage [] source base [] accumulator []
                output)
  | succ count ih =>
      have hfirst := oneStep _ _ (polynomialRowMarker_product_step polynomial stage source base
          accumulator (List.replicate count true) output)
      have hrest := ih (accumulator := true :: accumulator)
      have hfull := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step
        _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append,
          replicate_append_bit_cons] using
          hfull

private def polynomialRowMarkerHornerCostPolynomial
    (polynomial : Polynomial ℕ) : ℕ → Polynomial ℕ → Polynomial ℕ
  | 0, _ => 0
  | remaining + 1, accumulator =>
      accumulator * (2 * Polynomial.X + 3) + 1 +
        Polynomial.X * accumulator + 1 +
        polynomialRowMarkerHornerCostPolynomial polynomial remaining
          (Polynomial.X * accumulator +
            Polynomial.C (polynomial.coeff remaining))

private def polynomialRowMarker_hornerTrace
    (polynomial : Polynomial ℕ)
    (baseCount stages : ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (hstage : stage.val + 1 = stages)
    (accumulatorPolynomial : Polynomial ℕ)
    (source output : List Bool) :
    EvalsToInTime (polynomialRowMarkerMachine polynomial).step
      (polynomialRowMarkerConfiguration polynomial 1 stage
        [] source (List.replicate baseCount true) []
        (List.replicate (accumulatorPolynomial.eval baseCount) true)
        [] output)
      (some (polynomialRowMarkerConfiguration polynomial 5 0
        [] source (List.replicate baseCount true) []
        (List.replicate
          (polynomialRowMarkerHorner polynomial baseCount stages
            (accumulatorPolynomial.eval baseCount)) true)
        [] output))
      ((polynomialRowMarkerHornerCostPolynomial
        polynomial stages accumulatorPolynomial).eval baseCount) := by
  induction stages generalizing stage accumulatorPolynomial with
  | zero =>
      omega
  | succ remaining ih =>
      have hindex : stage.val = remaining := by omega
      let accumulator := accumulatorPolynomial.eval baseCount
      have hmul := polynomialRowMarker_multiplyTrace
        polynomial stage baseCount accumulator 0 source output
      have hproduct := polynomialRowMarker_productTrace
        polynomial stage (baseCount * accumulator) source
        (List.replicate baseCount true) [] output
      simp only [Nat.add_zero, List.replicate_zero,
        List.append_nil] at hmul hproduct
      have hfirst := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step
        _ _ _ _ _ hmul hproduct
      by_cases hremaining : remaining = 0
      · have hzero : stage.val = 0 := by omega
        have hstageZero :
            stage = (0 : PolynomialRowMarkerStage polynomial) :=
          Fin.ext hzero
        have hcoefficient := oneStep _ _ (polynomialRowMarker_coefficient_zero_step polynomial
            stage
            hzero source (List.replicate baseCount true)
            (List.replicate (baseCount * accumulator) true) output)
        have hfull := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step
          _ _ _ _ _ hfirst hcoefficient
        have hvalue :
            polynomial.coeff stage.val + baseCount * accumulator =
              polynomialRowMarkerHorner polynomial baseCount
                (remaining + 1) accumulator := by
          simp only [hindex, hremaining, polynomialRowMarkerHorner]
          ring
        have hmarkers :
            List.replicate (polynomial.coeff stage.val) true ++
                List.replicate (baseCount * accumulator) true =
              List.replicate
                (polynomialRowMarkerHorner polynomial baseCount
                  (remaining + 1) accumulator) true := by
          rw [← List.replicate_add, hvalue]
        have hbudget :
            1 + (baseCount * accumulator +
                (accumulator * (2 * baseCount + 3) + 1)) =
              (polynomialRowMarkerHornerCostPolynomial polynomial
                (remaining + 1) accumulatorPolynomial).eval baseCount := by
          simp only [polynomialRowMarkerHornerCostPolynomial, hremaining, eq_natCast, add_zero,
              Polynomial.eval_add,
              Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one,
                  accumulator]
          ring
        rw [hmarkers, hbudget] at hfull
        simpa only [hstageZero, Nat.succ_eq_add_one] using hfull
      · have hnot : stage.val ≠ 0 := by omega
        let nextAccumulator : Polynomial ℕ :=
          Polynomial.X * accumulatorPolynomial +
            Polynomial.C (polynomial.coeff remaining)
        have hnext :
            nextAccumulator.eval baseCount =
              polynomial.coeff stage.val + baseCount * accumulator := by
          simp only [eq_natCast, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
              Polynomial.eval_natCast,
              Nat.cast_id, hindex, nextAccumulator, accumulator]
          ring
        have hmarkers :
            List.replicate (polynomial.coeff stage.val) true ++
                List.replicate (baseCount * accumulator) true =
              List.replicate
                (nextAccumulator.eval baseCount) true := by
          rw [← List.replicate_add, ← hnext]
        have hcoefficient := oneStep _ _ (polynomialRowMarker_coefficient_succ_step polynomial
            stage
            hnot source (List.replicate baseCount true)
            (List.replicate (baseCount * accumulator) true) output)
        rw [hmarkers] at hcoefficient
        have hprefix := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step
          _ _ _ _ _ hfirst hcoefficient
        have hpred :
            (polynomialRowMarkerPredStage polynomial stage hnot).val + 1 =
              remaining := by
          simp only [polynomialRowMarkerPredStage]
          omega
        have hrest := ih
          (stage := polynomialRowMarkerPredStage polynomial stage hnot)
          hpred (accumulatorPolynomial := nextAccumulator)
        have hfull := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step
          _ _ _ _ _ hprefix hrest
        have hvalue :
            polynomialRowMarkerHorner polynomial baseCount remaining
                (nextAccumulator.eval baseCount) =
              polynomialRowMarkerHorner polynomial baseCount
                (remaining + 1) accumulator := by
          rw [polynomialRowMarkerHorner, hnext, hindex]
          congr 1
          ring
        have hbudget :
            (polynomialRowMarkerHornerCostPolynomial polynomial
                remaining nextAccumulator).eval baseCount +
                (1 + (baseCount * accumulator +
                  (accumulator * (2 * baseCount + 3) + 1))) =
              (polynomialRowMarkerHornerCostPolynomial polynomial
                (remaining + 1) accumulatorPolynomial).eval baseCount := by
          simp only [eq_natCast, polynomialRowMarkerHornerCostPolynomial, Polynomial.eval_add,
              Polynomial.eval_mul,
              Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one, nextAccumulator,
                  accumulator]
          ring
        rw [hvalue, hbudget] at hfull
        simpa only [Nat.succ_eq_add_one] using hfull

private def polynomialRowMarker_payloadTrace
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (markerCount : ℕ)
    (source base product output : List Bool) :
    EvalsToInTime (polynomialRowMarkerMachine polynomial).step
      (polynomialRowMarkerConfiguration polynomial 5 stage
        [] source base [] (List.replicate markerCount true)
        product output)
      (some (polynomialRowMarkerConfiguration polynomial 6 stage
        [] source base [] []
        (List.replicate markerCount true ++ product)
        (false :: (List.replicate markerCount true ++ output))))
      (markerCount + 1) := by
  induction markerCount generalizing product output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (polynomialRowMarker_payload_finish polynomial stage source base product
              output)
  | succ count ih =>
      have hfirst := oneStep _ _ (polynomialRowMarker_payload_step polynomial stage source base
          (List.replicate count true) product output)
      have hrest := ih (product := true :: product)
        (output := true :: output)
      have hfull := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step
        _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          replicate_append_bit_cons] using hfull

private def polynomialRowMarker_headerTrace
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (markerCount : ℕ)
    (source base output : List Bool) :
    EvalsToInTime (polynomialRowMarkerMachine polynomial).step
      (polynomialRowMarkerConfiguration polynomial 6 stage
        [] source base [] [] (List.replicate markerCount true) output)
      (some (polynomialRowMarkerConfiguration polynomial 7 stage
        [] source base [] [] []
        (List.replicate markerCount true ++ output)))
      (markerCount + 1) := by
  induction markerCount generalizing output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (polynomialRowMarker_header_finish polynomial stage source base output)
  | succ count ih =>
      have hfirst := oneStep _ _ (polynomialRowMarker_header_step polynomial stage source base
          (List.replicate count true) output)
      have hrest := ih (output := true :: output)
      have hfull := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step
        _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          replicate_append_bit_cons] using hfull

private def polynomialRowMarker_sourceTrace
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (source base output : List Bool) :
    EvalsToInTime (polynomialRowMarkerMachine polynomial).step
      (polynomialRowMarkerConfiguration polynomial 7 stage
        [] source base [] [] [] output)
      (some (polynomialRowMarkerConfiguration polynomial 8 stage
        [] [] base [] [] []
        (false :: (source.reverse ++ output))))
      (source.length + 1) := by
  induction source generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (polynomialRowMarker_source_finish polynomial stage base output)
  | cons bit remaining ih =>
      have hfirst := oneStep _ _ (polynomialRowMarker_source_step polynomial stage bit
          remaining base output)
      have hrest := ih (output := bit :: output)
      have hfull := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step
        _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hfull

private def polynomialRowMarker_prefixTrace
    (polynomial : Polynomial ℕ)
    (stage : PolynomialRowMarkerStage polynomial)
    (baseCount : ℕ)
    (output : List Bool) :
    EvalsToInTime (polynomialRowMarkerMachine polynomial).step
      (polynomialRowMarkerConfiguration polynomial 8 stage
        [] [] (List.replicate baseCount true) [] [] [] output)
      (some (Turing.haltList (polynomialRowMarkerMachine polynomial)
        (List.replicate baseCount true ++ output)))
      (baseCount + 1) := by
  induction baseCount generalizing output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (polynomialRowMarker_finish polynomial stage output)
  | succ count ih =>
      have hfirst := oneStep _ _ (polynomialRowMarker_prefix_step polynomial stage
          (List.replicate count true) output)
      have hrest := ih (output := true :: output)
      have hfull := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step
        _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          replicate_append_bit_cons] using hfull

private def polynomialRowMarkerTotalTimePolynomial
    (polynomial : Polynomial ℕ) : Polynomial ℕ :=
  polynomialRowMarkerHornerCostPolynomial
      polynomial (polynomial.natDegree + 1) 0 +
    3 * Polynomial.X + 2 * polynomial + 5

private def polynomialRowMarker_totalTrace
    (polynomial : Polynomial ℕ)
    (input : List Bool) :
    EvalsToInTime (polynomialRowMarkerMachine polynomial).step
      (polynomialRowMarkerConfiguration polynomial 0
        (polynomialRowMarkerTopStage polynomial)
        input [] [] [] [] [] [])
      (some (Turing.haltList
        (polynomialRowMarkerMachine polynomial)
        (sourcePreservingPolynomialMarkerWord polynomial input)))
      ((polynomialRowMarkerTotalTimePolynomial polynomial).eval
        input.length) := by
  let sourcePrefix := List.replicate input.length true
  let markerCount := polynomial.eval input.length
  let markerPayload := List.replicate markerCount true
  let markerField := lengthPrefixedWord markerPayload
  have htop :
      (polynomialRowMarkerTopStage polynomial).val + 1 =
        polynomial.natDegree + 1 := by
    rfl
  have hscan :
      EvalsToInTime (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 0
          (polynomialRowMarkerTopStage polynomial)
          input [] [] [] [] [] [])
        (some (polynomialRowMarkerConfiguration polynomial 1
          (polynomialRowMarkerTopStage polynomial)
          [] input.reverse sourcePrefix [] [] [] []))
        (input.length + 1) := by
    simpa [sourcePrefix] using polynomialRowMarker_scanTrace
      polynomial (polynomialRowMarkerTopStage polynomial)
      input [] [] [] [] [] []
  have hhorner :
      EvalsToInTime (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 1
          (polynomialRowMarkerTopStage polynomial)
          [] input.reverse sourcePrefix [] [] [] [])
        (some (polynomialRowMarkerConfiguration polynomial 5 0
          [] input.reverse sourcePrefix [] markerPayload [] []))
        ((polynomialRowMarkerHornerCostPolynomial polynomial
          (polynomial.natDegree + 1) 0).eval input.length) := by
    have h := polynomialRowMarker_hornerTrace polynomial
      input.length (polynomial.natDegree + 1)
      (polynomialRowMarkerTopStage polynomial) htop 0
      input.reverse []
    simpa [sourcePrefix, markerPayload, markerCount,
      polynomialRowMarkerHorner_eval] using h
  have hpayload :
      EvalsToInTime (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 5 0
          [] input.reverse sourcePrefix [] markerPayload [] [])
        (some (polynomialRowMarkerConfiguration polynomial 6 0
          [] input.reverse sourcePrefix [] [] markerPayload
          (false :: markerPayload)))
        (markerCount + 1) := by
    simpa [markerPayload] using polynomialRowMarker_payloadTrace
      polynomial 0 markerCount input.reverse sourcePrefix [] []
  have hheader :
      EvalsToInTime (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 6 0
          [] input.reverse sourcePrefix [] [] markerPayload
          (false :: markerPayload))
        (some (polynomialRowMarkerConfiguration polynomial 7 0
          [] input.reverse sourcePrefix [] [] [] markerField))
        (markerCount + 1) := by
    simpa [markerField, markerPayload, lengthPrefixedWord] using
      polynomialRowMarker_headerTrace polynomial 0 markerCount
        input.reverse sourcePrefix (false :: markerPayload)
  have hsource :
      EvalsToInTime (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 7 0
          [] input.reverse sourcePrefix [] [] [] markerField)
        (some (polynomialRowMarkerConfiguration polynomial 8 0
          [] [] sourcePrefix [] [] []
          (false :: (input ++ markerField))))
        (input.length + 1) := by
    simpa using polynomialRowMarker_sourceTrace
      polynomial 0 input.reverse sourcePrefix markerField
  have hprefix :
      EvalsToInTime (polynomialRowMarkerMachine polynomial).step
        (polynomialRowMarkerConfiguration polynomial 8 0
          [] [] sourcePrefix [] [] []
          (false :: (input ++ markerField)))
        (some (Turing.haltList (polynomialRowMarkerMachine polynomial)
          (sourcePreservingPolynomialMarkerWord polynomial input)))
        (input.length + 1) := by
    simpa [sourcePrefix, sourcePreservingPolynomialMarkerWord,
      markerField, markerPayload, markerCount,
      lengthPrefixedWord, List.append_assoc] using
      polynomialRowMarker_prefixTrace polynomial 0 input.length
        (false :: (input ++ markerField))
  have hfirst := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step _ _ _ _ _
    hscan hhorner
  have hsecond := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step _ _ _ _ _
    hfirst hpayload
  have hthird := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step _ _ _ _ _
    hsecond hheader
  have hfourth := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step _ _ _ _ _
    hthird hsource
  have hfull := EvalsToInTime.trans (polynomialRowMarkerMachine polynomial).step _ _ _ _ _
    hfourth hprefix
  apply rebound hfull
  simp [polynomialRowMarkerTotalTimePolynomial, markerCount,
    Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

/-- GapCVP reduction support. -/
def sourcePreservingPolynomialMarkerComputable
    (polynomial : Polynomial ℕ) :
    BitTM
      (sourcePreservingPolynomialMarkerWord polynomial) where
  tm := polynomialRowMarkerMachine polynomial
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := polynomialRowMarkerTotalTimePolynomial polynomial
  outputsFun input := {
    steps := (polynomialRowMarker_totalTrace polynomial input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, polynomialRowMarkerMachine_init,
              Option.map_some] using
          (polynomialRowMarker_totalTrace polynomial input).evals_in_steps
    steps_le_m := by
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq] using
          (polynomialRowMarker_totalTrace polynomial input).steps_le_m
  }

end CLStructuralCNFOutputMachinesUnconditional

namespace CNFDependentFiveFamilyRecordTM

open Computability Turing GapCVP.CL GapCVP.CNFClauseLoop

@[simp] private theorem mem_executableFiveFamilyFiniteElements
    (α : Type) [Fintype α] (value : α) :
    value ∈ clauseLoopFiniteElements α :=
  mem_clauseLoopFiniteElements α value

/-- GapCVP reduction support. -/
def executableAtLeastOneFamilyClauses (T S : ℕ) :
    List (Clause T S) :=
  (clauseLoopFiniteElements (Time T × Position T)).map
    (fun position => atLeastOneClause (S := S)
      position.1 position.2)

/-- Internal support shared across GapCVP continuation modules. -/
def executableAtMostOneFamilyClauses (T S : ℕ) :
    List (Clause T S) :=
  (clauseLoopFiniteElements
    ((Time T × Position T) × (Symbol S × Symbol S))).filterMap
      (fun position =>
        if position.2.1 < position.2.2 then
          some (atMostOneClause position.1.1 position.1.2
            position.2.1 position.2.2)
        else
          none)

/-- GapCVP reduction support. -/
def executableInitialFamilyClauses {T S : ℕ}
    (specification : Specification T S) : List (Clause T S) :=
  (clauseLoopFiniteElements (Position T)).map
    (initialClause specification.input)

/-- GapCVP reduction support. -/
def executableAcceptanceFamilyClauses {T S : ℕ}
    (specification : Specification T S) : List (Clause T S) :=
  [acceptanceClause specification.accept]

/-- Internal support shared across GapCVP continuation modules. -/
def executableForbiddenTransitionFamilyClauses {T S : ℕ}
    (specification : Specification T S) : List (Clause T S) :=
  (clauseLoopFiniteElements (Window T × WindowSymbols S)).filterMap
    (fun window =>
      if specification.allowed window.2 = false then
        some (transitionClause window.1 window.2)
      else
        none)

/-- Internal support shared across GapCVP continuation modules. -/
def executableFiveFamilySourceClauseCandidates {T S : ℕ}
    (specification : Specification T S) : List (Clause T S) :=
  executableAtLeastOneFamilyClauses T S ++
    executableAtMostOneFamilyClauses T S ++
    executableInitialFamilyClauses specification ++
    executableAcceptanceFamilyClauses specification ++
    executableForbiddenTransitionFamilyClauses specification

private theorem executableAtLeastOneFamilyClauses_toFinset
    (T S : ℕ) :
    (executableAtLeastOneFamilyClauses T S).toFinset =
      Finset.univ.image
        (fun position : Time T × Position T =>
          atLeastOneClause (S := S) position.1 position.2) := by
  ext clause
  simp only [executableAtLeastOneFamilyClauses, List.mem_toFinset, List.mem_map,
      mem_executableFiveFamilyFiniteElements, true_and, Prod.exists, Finset.mem_image,
          Finset.mem_univ]

private theorem executableAtMostOneFamilyClauses_toFinset
    (T S : ℕ) :
    (executableAtMostOneFamilyClauses T S).toFinset =
      (Finset.univ.filter
        (fun position :
          (Time T × Position T) × (Symbol S × Symbol S) =>
            position.2.1 < position.2.2)).image
              (fun position => atMostOneClause position.1.1
                position.1.2 position.2.1 position.2.2) := by
  ext clause
  simp only [executableAtMostOneFamilyClauses, List.mem_toFinset, List.mem_filterMap,
      mem_executableFiveFamilyFiniteElements, Option.ite_none_right_eq_some, Option.some.injEq,
          true_and, Prod.exists,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ]

private theorem executableInitialFamilyClauses_toFinset
    {T S : ℕ} (specification : Specification T S) :
    (executableInitialFamilyClauses specification).toFinset =
      initialClauses specification := by
  ext clause
  simp only [executableInitialFamilyClauses, List.mem_toFinset, List.mem_map,
      mem_executableFiveFamilyFiniteElements, true_and, initialClauses, Finset.mem_image,
          Finset.mem_univ]

private theorem executableForbiddenTransitionFamilyClauses_toFinset
    {T S : ℕ} (specification : Specification T S) :
    (executableForbiddenTransitionFamilyClauses specification).toFinset =
      transitionClauses specification := by
  ext clause
  simp only [executableForbiddenTransitionFamilyClauses, List.mem_toFinset, List.mem_filterMap,
      mem_executableFiveFamilyFiniteElements, Option.ite_none_right_eq_some, Option.some.injEq,
          true_and, Prod.exists,
      Subtype.exists, Order.lt_add_one_iff, Order.add_one_le_iff, transitionClauses,
          Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ]

/-- Internal support shared across GapCVP continuation modules. -/
theorem executableFiveFamilySourceClauseCandidates_toFinset
    {T S : ℕ} (specification : Specification T S) :
    (executableFiveFamilySourceClauseCandidates specification).toFinset =
      tableauFormula specification := by
  simp only [executableFiveFamilySourceClauseCandidates, List.append_assoc,
      executableAcceptanceFamilyClauses,
      List.cons_append, List.nil_append, List.toFinset_append,
          executableAtLeastOneFamilyClauses_toFinset,
      executableAtMostOneFamilyClauses_toFinset, executableInitialFamilyClauses_toFinset,
          List.toFinset_cons,
      executableForbiddenTransitionFamilyClauses_toFinset, Finset.union_insert, tableauFormula,
          structuralClauses,
      Finset.union_assoc, Finset.union_singleton, Finset.insert_union]

end CNFDependentFiveFamilyRecordTM

namespace OutputPolynomialCompositionClosure

open Turing

/-- GapCVP reduction support. -/
def markerConditionalOutput
    (valid : List Bool → List Bool) (fallback : List Bool) :
    List Bool → List Bool
  | true :: input => valid input
  | _ => fallback

/-- GapCVP reduction support. -/
abbrev ConditionalLabel (tm : Turing.FinTM2) := tm.Λ ⊕ Bool

/-- GapCVP reduction support. -/
abbrev ConditionalState (tm : Turing.FinTM2) := Option Bool × tm.σ

/-- GapCVP reduction support. -/
def liftValidStatement (tm : Turing.FinTM2) :
    Turing.TM2.Stmt tm.Γ tm.Λ tm.σ →
      Turing.TM2.Stmt tm.Γ (ConditionalLabel tm)
        (ConditionalState tm)
  | .push k f q =>
      .push k (fun state => f state.2) (liftValidStatement tm q)
  | .peek k f q =>
      .peek k (fun state symbol => (state.1, f state.2 symbol))
        (liftValidStatement tm q)
  | .pop k f q =>
      .pop k (fun state symbol => (state.1, f state.2 symbol))
        (liftValidStatement tm q)
  | .load f q =>
      .load (fun state => (state.1, f state.2))
        (liftValidStatement tm q)
  | .branch test yes no =>
      .branch (fun state => test state.2)
        (liftValidStatement tm yes) (liftValidStatement tm no)
  | .goto next => .goto (fun state => .inl (next state.2))
  | .halt => .load (fun state => (none, state.2)) .halt

private def fixedOutputStatement
    {valid : List Bool → List Bool}
    (computer : BitTM valid) :
    List Bool →
      Turing.TM2.Stmt computer.tm.Γ (ConditionalLabel computer.tm)
        (ConditionalState computer.tm)
  | [] => .halt
  | bit :: remaining =>
      .push computer.tm.k₁
        (fun _ => computer.outputAlphabet.invFun bit)
        (fixedOutputStatement computer remaining)

/-- GapCVP reduction support. -/
noncomputable abbrev markerConditionalMachine
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback : List Bool) : Turing.FinTM2 := by
  classical
  letI : DecidableEq computer.tm.K := computer.tm.kDecidableEq
  letI : Fintype computer.tm.K := computer.tm.kFin
  letI : Fintype computer.tm.Λ := computer.tm.ΛFin
  letI : Fintype computer.tm.σ := computer.tm.σFin
  letI : Fintype (computer.tm.Γ computer.tm.k₀) :=
    computer.tm.Γk₀Fin
  exact {
    K := computer.tm.K
    kDecidableEq := computer.tm.kDecidableEq
    k₀ := computer.tm.k₀
    k₁ := computer.tm.k₁
    Γ := computer.tm.Γ
    Λ := ConditionalLabel computer.tm
    main := .inr false
    σ := ConditionalState computer.tm
    initialState := (none, computer.tm.initialState)
    m := fun
      | .inl label => liftValidStatement computer.tm (computer.tm.m label)
      | .inr false =>
          .pop computer.tm.k₀
            (fun state symbol =>
              (symbol.map computer.inputAlphabet, state.2))
            (.branch (fun state => state.1.getD false)
              (.goto (fun _ => .inl computer.tm.main))
              (.load (fun state => (none, state.2))
                (.goto (fun _ => .inr true))))
      | .inr true =>
          .peek computer.tm.k₀
            (fun state symbol =>
              (symbol.map computer.inputAlphabet, state.2))
            (.branch (fun state => state.1.isSome)
              (.pop computer.tm.k₀
                (fun state _ => (none, state.2))
                (.goto (fun _ => .inr true)))
              (fixedOutputStatement computer fallback.reverse))
  }

/-- GapCVP reduction support. -/
noncomputable def validConfiguration
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback : List Bool)
    (configuration : computer.tm.Cfg) :
    (markerConditionalMachine computer fallback).Cfg where
  l := configuration.l.map Sum.inl
  var :=
    (if configuration.l.isSome then some true else none,
      configuration.var)
  stk := configuration.stk

theorem liftValidStatement_stepAux
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback : List Bool)
    (statement : Turing.TM2.Stmt
      computer.tm.Γ computer.tm.Λ computer.tm.σ)
    (state : computer.tm.σ)
    (sourceStacks : ∀ k, List (computer.tm.Γ k)) :
    Turing.TM2.stepAux (liftValidStatement computer.tm statement)
        (some true, state) sourceStacks =
      validConfiguration computer fallback
        (Turing.TM2.stepAux statement state sourceStacks) := by
  classical
  induction statement generalizing state sourceStacks with
  | push k f q ih =>
      exact ih (state := state)
        (sourceStacks := Function.update sourceStacks k
          (f state :: sourceStacks k))
  | peek k f q ih =>
      exact ih (state := f state (sourceStacks k).head?)
        (sourceStacks := sourceStacks)
  | pop k f q ih =>
      exact ih (state := f state (sourceStacks k).head?)
        (sourceStacks := Function.update sourceStacks k
          (sourceStacks k).tail)
  | load f q ih =>
      exact ih (state := f state) (sourceStacks := sourceStacks)
  | branch test yes no ihYes ihNo =>
      cases htest : test state with
      | false =>
          simpa only [liftValidStatement, TM2.stepAux, htest, Bool.cond_false] using
              ihNo (state := state) (sourceStacks := sourceStacks)
      | true =>
          simpa only [liftValidStatement, TM2.stepAux, htest, Bool.cond_true] using
              ihYes (state := state) (sourceStacks := sourceStacks)
  | goto next => rfl
  | halt => rfl

/-- Internal support shared across GapCVP continuation modules. -/
theorem validConfiguration_step
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback : List Bool)
    (configuration next : computer.tm.Cfg)
    (hstep : computer.tm.step configuration = some next) :
    (markerConditionalMachine computer fallback).step
        (validConfiguration computer fallback configuration) =
      some (validConfiguration computer fallback next) := by
  rcases configuration with ⟨label, state, sourceStacks⟩
  cases label with
  | none =>
      simp only [FinTM2.step, TM2.step, reduceCtorEq] at hstep
  | some label =>
      change some (Turing.TM2.stepAux (computer.tm.m label)
        state sourceStacks) = some next at hstep
      have hnext := Option.some.inj hstep
      subst next
      change some (Turing.TM2.stepAux
        (liftValidStatement computer.tm (computer.tm.m label))
        (some true, state) sourceStacks) =
          some (validConfiguration computer fallback
            (Turing.TM2.stepAux (computer.tm.m label)
              state sourceStacks))
      rw [liftValidStatement_stepAux computer fallback]
      rfl

@[simp] theorem initialStack_input
    (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) :
    (Turing.initList tm input).stk tm.k₀ = input := by
  classical
  simp only [initList, eq_mpr_eq_cast, ↓reduceDIte, cast_eq]

private theorem initialStack_of_ne
    (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀))
    (k : tm.K) (hk : k ≠ tm.k₀) :
    (Turing.initList tm input).stk k = [] := by
  classical
  simp only [initList, eq_mpr_eq_cast, hk, ↓reduceDIte]

@[simp] theorem initialStack_empty
    (tm : Turing.FinTM2) (k : tm.K) :
    (Turing.initList tm []).stk k = [] := by
  classical
  unfold Turing.initList
  dsimp
  split
  next h =>
    subst k
    rfl
  next h => rfl

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def fallbackConfiguration
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback : List Bool)
    (remaining : List (computer.tm.Γ computer.tm.k₀)) :
    (markerConditionalMachine computer fallback).Cfg where
  l := some (.inr true)
  var := (none, computer.tm.initialState)
  stk := (Turing.initList computer.tm remaining).stk

private theorem fixedOutputStatement_stepAux
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (bits : List Bool)
    (marker : Option Bool)
    (state : computer.tm.σ)
    (sourceStacks : ∀ k, List (computer.tm.Γ k)) :
    @Turing.TM2.stepAux computer.tm.K computer.tm.Γ
        (ConditionalLabel computer.tm) (ConditionalState computer.tm)
        computer.tm.kDecidableEq
        (fixedOutputStatement computer bits)
        (marker, state) sourceStacks =
      ⟨none, (marker, state),
        Function.update sourceStacks computer.tm.k₁
          (List.map computer.outputAlphabet.invFun bits.reverse ++
            sourceStacks computer.tm.k₁)⟩ := by
  classical
  let : DecidableEq computer.tm.K := computer.tm.kDecidableEq
  induction bits generalizing sourceStacks with
  | nil =>
      simp only [fixedOutputStatement, TM2.stepAux, Equiv.invFun_as_coe, List.reverse_nil,
          List.map_nil,
          List.nil_append, Function.update_eq_self]
  | cons bit remaining ih =>
      change Turing.TM2.stepAux
        (fixedOutputStatement computer remaining) (marker, state)
        (Function.update sourceStacks computer.tm.k₁
          (computer.outputAlphabet.invFun bit ::
            sourceStacks computer.tm.k₁)) = _
      rw [ih]
      congr 1
      funext k
      by_cases hk : k = computer.tm.k₁
      · subst k
        simp only [Equiv.invFun_as_coe, List.map_reverse, Function.update_self, List.reverse_cons,
            List.map_append,
            List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
      · simp only [Function.update, hk, ↓reduceDIte]

private theorem fallbackConfiguration_step
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback : List Bool)
    (symbol : computer.tm.Γ computer.tm.k₀)
    (remaining : List (computer.tm.Γ computer.tm.k₀)) :
    (markerConditionalMachine computer fallback).step
        (fallbackConfiguration computer fallback
          (symbol :: remaining)) =
      some (fallbackConfiguration computer fallback remaining) := by
  classical
  let : DecidableEq computer.tm.K := computer.tm.kDecidableEq
  simp only [markerConditionalMachine, FinTM2.step, TM2.step, fallbackConfiguration, TM2.stepAux,
      initialStack_input, List.head?_cons, Option.map_some, Option.isSome_some, List.tail_cons,
          Bool.cond_true]
  congr 2
  funext k
  by_cases hk : k = computer.tm.k₀
  · subst k
    rw [Function.update_self]
    exact (initialStack_input computer.tm remaining).symm
  · simp only [Function.update, hk, ↓reduceDIte, ne_eq, not_false_eq_true, initialStack_of_ne]

private theorem fallbackConfiguration_finish
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback : List Bool) :
    (markerConditionalMachine computer fallback).step
        (fallbackConfiguration computer fallback []) =
      some (Turing.haltList
        (markerConditionalMachine computer fallback)
        (List.map computer.outputAlphabet.invFun fallback)) := by
  classical
  let : DecidableEq computer.tm.K := computer.tm.kDecidableEq
  simp only [markerConditionalMachine, fallbackConfiguration,
    Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux,
    initialStack_input, List.head?_nil, Option.map_none,
    Option.isSome_none, Bool.cond_false]
  change some
    (@Turing.TM2.stepAux computer.tm.K computer.tm.Γ
      (ConditionalLabel computer.tm) (ConditionalState computer.tm)
      computer.tm.kDecidableEq
      (fixedOutputStatement computer fallback.reverse)
      (none, computer.tm.initialState)
      (Turing.initList computer.tm []).stk) = _
  rw [fixedOutputStatement_stepAux computer]
  simp only [List.reverse_reverse]
  congr 2
  funext k
  by_cases hk : k = computer.tm.k₁
  · subst k
    simp only [Equiv.invFun_as_coe, initialStack_empty, List.append_nil, Function.update_self,
        ↓reduceDIte,
        eq_mpr_eq_cast, cast_eq]
  · simp only [Function.update, hk, ↓reduceDIte, initialStack_empty]

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def fallbackTrace
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback : List Bool)
    (remaining : List (computer.tm.Γ computer.tm.k₀)) :
    EvalsToInTime (markerConditionalMachine computer fallback).step
      (fallbackConfiguration computer fallback remaining)
      (some (Turing.haltList
        (markerConditionalMachine computer fallback)
        (List.map computer.outputAlphabet.invFun fallback)))
      (remaining.length + 1) := by
  induction remaining with
  | nil =>
      exact oneStep _ _ (fallbackConfiguration_finish computer fallback)
  | cons symbol remaining ih =>
      have hfirst := oneStep _ _ (fallbackConfiguration_step computer fallback
          symbol remaining)
      have hfull := EvalsToInTime.trans (markerConditionalMachine computer fallback).step
        1 (remaining.length + 1) _ _ _ hfirst ih
      simpa only [FinTM2.step, Equiv.invFun_as_coe, List.length_cons, Nat.add_comm] using hfull

/-- Internal support shared across GapCVP continuation modules. -/
theorem markerConditional_start_true
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback : List Bool)
    (remaining : List (computer.tm.Γ computer.tm.k₀)) :
    (markerConditionalMachine computer fallback).step
      (Turing.initList (markerConditionalMachine computer fallback)
        (computer.inputAlphabet.invFun true :: remaining)) =
      some (validConfiguration computer fallback
        (Turing.initList computer.tm remaining)) := by
  classical
  let : DecidableEq computer.tm.K := computer.tm.kDecidableEq
  simp only [markerConditionalMachine, FinTM2.step, TM2.step, initList,
      Equiv.invFun_as_coe, eq_mpr_eq_cast,
      TM2.stepAux, ↓reduceDIte, cast_eq, List.head?_cons, Option.map_some, Equiv.apply_symm_apply,
          Option.getD_some,
      List.tail_cons, Bool.cond_true, validConfiguration, Option.isSome_some, ↓reduceIte]
  congr 2
  funext k
  by_cases hk : k = computer.tm.k₀
  · subst k
    simp only [Function.update_self, ↓reduceDIte, cast_eq]
  · simp only [Function.update, hk, ↓reduceDIte]

/-- Internal support shared across GapCVP continuation modules. -/
theorem markerConditional_start_false
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback : List Bool)
    (remaining : List (computer.tm.Γ computer.tm.k₀)) :
    (markerConditionalMachine computer fallback).step
      (Turing.initList (markerConditionalMachine computer fallback)
        (computer.inputAlphabet.invFun false :: remaining)) =
      some (fallbackConfiguration computer fallback remaining) := by
  classical
  let : DecidableEq computer.tm.K := computer.tm.kDecidableEq
  simp only [markerConditionalMachine, FinTM2.step, TM2.step, initList,
      Equiv.invFun_as_coe, eq_mpr_eq_cast,
      TM2.stepAux, ↓reduceDIte, cast_eq, List.head?_cons, Option.map_some, Equiv.apply_symm_apply,
          Option.getD_some,
      List.tail_cons, Bool.cond_false, fallbackConfiguration]
  congr 2
  funext k
  by_cases hk : k = computer.tm.k₀
  · subst k
    simp only [Function.update_self, ↓reduceDIte, cast_eq]
  · simp only [Function.update, hk, ↓reduceDIte]

/-- Internal support shared across GapCVP continuation modules. -/
theorem markerConditional_start_missing
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback : List Bool) :
    (markerConditionalMachine computer fallback).step
      (Turing.initList (markerConditionalMachine computer fallback) []) =
      some (fallbackConfiguration computer fallback []) := by
  classical
  let : DecidableEq computer.tm.K := computer.tm.kDecidableEq
  simp only [markerConditionalMachine, FinTM2.step, TM2.step, initList,
      eq_mpr_eq_cast, TM2.stepAux,
      ↓reduceDIte, cast_eq, List.head?_nil, Option.map_none, Option.getD_none, List.tail_nil,
          Bool.cond_false,
      fallbackConfiguration]
  congr 2
  funext k
  by_cases hk : k = computer.tm.k₀
  · subst k
    simp only [Function.update, ↓reduceDIte, cast_eq]
  · simp only [Function.update, hk, ↓reduceDIte]

/-- Internal support shared across GapCVP continuation modules. -/
theorem validConfiguration_halt
    {valid : List Bool → List Bool}
    (computer : BitTM valid)
    (fallback : List Bool)
    (output : List (computer.tm.Γ computer.tm.k₁)) :
    validConfiguration computer fallback
        (Turing.haltList computer.tm output) =
      Turing.haltList (markerConditionalMachine computer fallback)
        output := by
  rfl

end OutputPolynomialCompositionClosure

end GapCVP

end
