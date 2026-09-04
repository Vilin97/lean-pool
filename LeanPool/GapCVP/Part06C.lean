/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part06B

/-! # GapCVP proof, part 06, continuation 03 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace SourceMixedRadixUnaryQuotientRemainderTM

section

open Turing GapCVP.BinaryEncoding

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionDividendPrefixTrace
    (count : ℕ) (valid : Bool)
    (remaining archive dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 0 valid
        (List.replicate count true ++ false :: remaining)
        archive dividend modulus modulusScratch
        quotient residueStack output)
      (some (sourceUnaryDivisionConfiguration 1 valid
        remaining (false :: (List.replicate count true ++ archive))
        (List.replicate count true ++ dividend) modulus
        modulusScratch quotient residueStack output))
      (count + 1) := by
  induction count generalizing archive dividend with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _
            (sourceUnaryDivision_dividend_false valid remaining archive dividend modulus
                modulusScratch quotient residueStack
              output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceUnaryDivision_dividend_true valid
          (List.replicate count true ++ false :: remaining)
          archive dividend modulus modulusScratch
          quotient residueStack output)
      have hremaining := ih (true :: archive) (true :: dividend)
      have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hremaining
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionDividendMissingTrace
    (count : ℕ) (valid : Bool)
    (archive dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 0 valid
        (List.replicate count true)
        archive dividend modulus modulusScratch
        quotient residueStack output)
      (some (sourceUnaryDivisionConfiguration 2 false
        [] (List.replicate count true ++ archive)
        (List.replicate count true ++ dividend)
        modulus modulusScratch quotient residueStack output))
      (count + 1) := by
  induction count generalizing archive dividend with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _
            (sourceUnaryDivision_dividend_missing valid archive dividend modulus modulusScratch
                quotient residueStack output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceUnaryDivision_dividend_true valid
          (List.replicate count true) archive dividend modulus
          modulusScratch quotient residueStack output)
      have hremaining := ih (true :: archive) (true :: dividend)
      have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hremaining
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionModulusPrefixTrace
    (count : ℕ) (valid : Bool)
    (remaining archive dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 1 valid
        (List.replicate count true ++ false :: remaining)
        archive dividend modulus modulusScratch
        quotient residueStack output)
      (some (sourceUnaryDivisionConfiguration 2 valid
        remaining (false :: (List.replicate count true ++ archive))
        dividend (List.replicate count true ++ modulus)
        modulusScratch quotient residueStack output))
      (count + 1) := by
  induction count generalizing archive modulus with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _
            (sourceUnaryDivision_modulus_false valid remaining archive dividend modulus
                modulusScratch quotient residueStack
              output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceUnaryDivision_modulus_true valid
          (List.replicate count true ++ false :: remaining)
          archive dividend modulus modulusScratch
          quotient residueStack output)
      have hremaining := ih (true :: archive) (true :: modulus)
      have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hremaining
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionModulusMissingTrace
    (count : ℕ) (valid : Bool)
    (archive dividend modulus modulusScratch
      quotient residueStack output : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 1 valid
        (List.replicate count true)
        archive dividend modulus modulusScratch
        quotient residueStack output)
      (some (sourceUnaryDivisionConfiguration 2 false
        [] (List.replicate count true ++ archive)
        dividend (List.replicate count true ++ modulus)
        modulusScratch quotient residueStack output))
      (count + 1) := by
  induction count generalizing archive modulus with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _
            (sourceUnaryDivision_modulus_missing valid archive dividend modulus modulusScratch
                quotient residueStack output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceUnaryDivision_modulus_true valid
          (List.replicate count true) archive dividend modulus
          modulusScratch quotient residueStack output)
      have hremaining := ih (true :: archive) (true :: modulus)
      have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hremaining
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionSuffixTrace
    (source archive dividend modulus modulusScratch
      quotient residueStack output : List Bool)
    (valid : Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 2 valid
        source archive dividend modulus
        modulusScratch quotient residueStack output)
      (some (sourceUnaryDivisionConfiguration 3 valid
        [] (source.reverse ++ archive) dividend modulus
        modulusScratch quotient residueStack output))
      (source.length + 1) := by
  induction source generalizing archive with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _
            (sourceUnaryDivision_suffix_finish valid archive dividend modulus modulusScratch
                quotient residueStack output)
  | cons bit source ih =>
      have hfirst := oneStep _ _ (sourceUnaryDivision_suffix_step valid bit source archive
          dividend modulus modulusScratch quotient residueStack output)
      have hremaining := ih (bit :: archive)
      have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hremaining
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hfull

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionRestoreSourceTrace
    (archive dividend modulus modulusScratch
      quotient residueStack output : List Bool)
    (valid : Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 3 valid
        [] archive dividend modulus
        modulusScratch quotient residueStack output)
      (some (sourceUnaryDivisionConfiguration 4 valid
        [] [] dividend modulus
        modulusScratch quotient residueStack
        (false :: (archive.reverse ++ output))))
      (archive.length + 1) := by
  induction archive generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _
            (sourceUnaryDivision_restoreSource_finish valid dividend modulus modulusScratch
                quotient residueStack output)
  | cons bit archive ih =>
      have hfirst := oneStep _ _ (sourceUnaryDivision_restoreSource_step valid bit archive
          dividend modulus modulusScratch quotient residueStack output)
      have hremaining := ih (bit :: output)
      have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hremaining
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hfull

private def sourceUnaryDivision_cleanupModulusTrace
    (count : ℕ) (valid : Bool)
    (modulusScratch dividend quotient residueStack output : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 9 valid
        [] [] dividend (List.replicate count true)
        modulusScratch quotient residueStack output)
      (some (sourceUnaryDivisionConfiguration 10 valid
        [] [] dividend []
        modulusScratch quotient residueStack output))
      (count + 1) := by
  induction count with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, zero_add] using
          oneStep _ _ (sourceUnaryDivision_cleanupModulus_finish valid modulusScratch dividend
              quotient residueStack output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceUnaryDivision_cleanupModulus_step valid
          (List.replicate count true) modulusScratch dividend
          quotient residueStack output)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, Nat.add_assoc, Nat.reduceAdd]
          using
          EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst ih

private def sourceUnaryDivision_cleanupScratchTrace
    (count : ℕ) (valid : Bool)
    (dividend quotient residueStack output : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 10 valid
        [] [] dividend [] (List.replicate count true)
        quotient residueStack output)
      (some (sourceUnaryDivisionConfiguration 11 valid
        [] [] dividend [] [] quotient residueStack output))
      (count + 1) := by
  induction count with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, zero_add] using
          oneStep _ _ (sourceUnaryDivision_cleanupScratch_finish valid dividend quotient
              residueStack output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceUnaryDivision_cleanupScratch_step valid
          (List.replicate count true) dividend
          quotient residueStack output)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, Nat.add_assoc, Nat.reduceAdd]
          using
          EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst ih

private def sourceUnaryDivision_cleanupDividendTrace
    (count : ℕ) (valid : Bool)
    (quotient residueStack output : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 11 valid
        [] [] (List.replicate count true) [] []
        quotient residueStack output)
      (some (sourceUnaryDivisionConfiguration 12 valid
        [] [] [] [] [] quotient residueStack output))
      (count + 1) := by
  induction count with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, zero_add] using
          oneStep _ _ (sourceUnaryDivision_cleanupDividend_finish valid quotient residueStack
              output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceUnaryDivision_cleanupDividend_step valid
          (List.replicate count true) quotient residueStack output)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, Nat.add_assoc, Nat.reduceAdd]
          using
          EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst ih

private def sourceUnaryDivision_cleanupPartialTrace
    (count : ℕ) (valid : Bool) (output : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 12 valid
        [] [] [] [] [] [] (List.replicate count true) output)
      (some (Turing.haltList sourceUnaryDivisionMachine output))
      (count + 1) := by
  induction count with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, zero_add] using
          oneStep _ _ (sourceUnaryDivision_cleanupPartial_finish valid output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceUnaryDivision_cleanupPartial_step valid []
          (List.replicate count true) output)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, Nat.add_assoc, Nat.reduceAdd]
          using
          EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst ih

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionCleanupTrace
    (modulusCount scratchCount dividendCount residueCount : ℕ)
    (valid : Bool) (output : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 9 valid
        [] [] (List.replicate dividendCount true)
        (List.replicate modulusCount true)
        (List.replicate scratchCount true) []
        (List.replicate residueCount true) output)
      (some (Turing.haltList sourceUnaryDivisionMachine output))
      (modulusCount + scratchCount + dividendCount + residueCount + 4) := by
  have hmodulus := sourceUnaryDivision_cleanupModulusTrace
    modulusCount valid (List.replicate scratchCount true)
    (List.replicate dividendCount true) []
    (List.replicate residueCount true) output
  have hscratch := sourceUnaryDivision_cleanupScratchTrace
    scratchCount valid (List.replicate dividendCount true) []
    (List.replicate residueCount true) output
  have hdividend := sourceUnaryDivision_cleanupDividendTrace
    dividendCount valid [] (List.replicate residueCount true) output
  have hresidue := sourceUnaryDivision_cleanupPartialTrace
    residueCount valid output
  have hfirst := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hmodulus hscratch
  have hsecond := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hdividend
  have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hsecond hresidue
  exact rebound hfull (by omega)

private def sourceUnaryDivision_matchFullTrace
    (count : ℕ) (valid : Bool)
    (remaining modulusScratch quotient residueStack output : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 5 valid
        [] [] (List.replicate count true ++ remaining)
        (List.replicate count true)
        modulusScratch quotient residueStack output)
      (some (sourceUnaryDivisionConfiguration 6 valid
        [] [] remaining []
        (List.replicate count true ++ modulusScratch)
        quotient
        (List.replicate count true ++ residueStack) output))
      (count + 1) := by
  induction count generalizing modulusScratch residueStack with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceUnaryDivision_match_full valid remaining modulusScratch quotient
              residueStack output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceUnaryDivision_match_step valid
          (List.replicate count true ++ remaining)
          (List.replicate count true)
          modulusScratch quotient residueStack output)
      have hremaining := ih
        (true :: modulusScratch) (true :: residueStack)
      have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hremaining
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

private def sourceUnaryDivision_matchPartialTrace
    (count : ℕ) (valid : Bool)
    (modulusTail modulusScratch quotient residueStack output : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 5 valid
        [] [] (List.replicate count true)
        (List.replicate count true ++ true :: modulusTail)
        modulusScratch quotient residueStack output)
      (some (sourceUnaryDivisionConfiguration 7 valid
        [] [] [] (true :: modulusTail)
        (List.replicate count true ++ modulusScratch)
        quotient
        (List.replicate count true ++ residueStack) output))
      (count + 1) := by
  induction count generalizing modulusScratch residueStack with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceUnaryDivision_match_partial valid modulusTail modulusScratch quotient
              residueStack output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceUnaryDivision_match_step valid
          (List.replicate count true)
          (List.replicate count true ++ true :: modulusTail)
          modulusScratch quotient residueStack output)
      have hremaining := ih
        (true :: modulusScratch) (true :: residueStack)
      have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hremaining
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append,
          SourceStructuralDecoder.replicate_true_append_cons, Nat.add_assoc, Nat.reduceAdd]
              using hfull

private def sourceUnaryDivision_restoreModulusTrace
    (count : ℕ) (valid : Bool)
    (dividend modulus quotient output : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 6 valid
        [] [] dividend modulus
        (List.replicate count true)
        quotient (List.replicate count true) output)
      (some (sourceUnaryDivisionConfiguration 5 valid
        [] [] dividend (List.replicate count true ++ modulus)
        [] (true :: quotient) [] output))
      (count + 1) := by
  induction count generalizing modulus with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceUnaryDivision_restoreModulus_finish valid dividend modulus quotient
              output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceUnaryDivision_restoreModulus_step valid dividend modulus
          (List.replicate count true) quotient
          (List.replicate count true) output)
      have hremaining := ih (true :: modulus)
      have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hremaining
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

private def sourceUnaryDivision_emitRemainderTrace
    (count : ℕ) (valid : Bool)
    (modulus modulusScratch quotient output : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 7 valid
        [] [] [] modulus modulusScratch
        quotient (List.replicate count true) output)
      (some (sourceUnaryDivisionConfiguration 8 valid
        [] [] [] modulus modulusScratch
        quotient []
        (false :: (List.replicate count true ++ output))))
      (count + 1) := by
  induction count generalizing output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceUnaryDivision_emitRemainder_finish valid modulus modulusScratch
              quotient output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceUnaryDivision_emitRemainder_step valid modulus
          modulusScratch quotient (List.replicate count true) output)
      have hremaining := ih (true :: output)
      have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hremaining
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

private def sourceUnaryDivision_emitQuotientTrace
    (count : ℕ) (valid : Bool)
    (modulus modulusScratch output : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 8 valid
        [] [] [] modulus modulusScratch
        (List.replicate count true) [] output)
      (some (sourceUnaryDivisionConfiguration 9 valid
        [] [] [] modulus modulusScratch [] []
        (List.replicate count true ++ output)))
      (count + 1) := by
  induction count generalizing output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceUnaryDivision_emitQuotient_finish valid modulus modulusScratch output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceUnaryDivision_emitQuotient_step valid modulus
          modulusScratch (List.replicate count true) output)
      have hremaining := ih (true :: output)
      have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hremaining
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_assoc,
          Nat.reduceAdd,
          SourceStructuralDecoder.replicate_true_append_cons] using hfull

/-- Internal support shared across GapCVP continuation modules. -/
def sourceUnaryDivisionModuloTrace
    (modulus quotientCount remainder previous : ℕ)
    (hremainder : remainder < modulus)
    (output : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (sourceUnaryDivisionConfiguration 5 true
        [] []
        (List.replicate (modulus * quotientCount + remainder) true)
        (List.replicate modulus true) []
        (List.replicate previous true) [] output)
      (some (Turing.haltList sourceUnaryDivisionMachine
        (List.replicate (quotientCount + previous) true ++
          false :: (List.replicate remainder true ++ output))))
      (quotientCount * (2 * modulus + 3) +
        4 * modulus + previous + 12) := by
  induction quotientCount generalizing previous with
  | zero =>
      have hsplit :
          modulus = remainder +
            ((modulus - remainder - 1) + 1) := by omega
      have hmodulus :
          List.replicate modulus true =
            List.replicate remainder true ++
              true :: List.replicate
                (modulus - remainder - 1) true := by
        conv_lhs =>
          rw [hsplit, List.replicate_add, List.replicate_succ]
      have htail :
          true :: List.replicate (modulus - remainder - 1) true =
            List.replicate (modulus - remainder) true := by
        have hdifference :
            modulus - remainder =
              (modulus - remainder - 1) + 1 := by omega
        conv_rhs =>
          rw [hdifference, List.replicate_succ]
      have hpartial := sourceUnaryDivision_matchPartialTrace
        remainder true
        (List.replicate (modulus - remainder - 1) true)
        [] (List.replicate previous true) [] output
      simp only [List.append_nil] at hpartial
      rw [← hmodulus] at hpartial
      have hemitRemainder := sourceUnaryDivision_emitRemainderTrace
        remainder true
        (true :: List.replicate (modulus - remainder - 1) true)
        (List.replicate remainder true)
        (List.replicate previous true) output
      have hemitQuotient := sourceUnaryDivision_emitQuotientTrace
        previous true
        (true :: List.replicate (modulus - remainder - 1) true)
        (List.replicate remainder true)
        (false :: (List.replicate remainder true ++ output))
      have hcleanup := sourceUnaryDivisionCleanupTrace
        (modulus - remainder) remainder 0 0 true
        (List.replicate previous true ++
          false :: (List.replicate remainder true ++ output))
      rw [← htail] at hcleanup
      have hfirst := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _
        hpartial hemitRemainder
      have hsecond := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _
        hfirst hemitQuotient
      have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hsecond hcleanup
      have hbounded := rebound (newBudget := 0 * (2 * modulus + 3) +
          4 * modulus + previous + 12)
        hfull (by omega)
      simpa only [FinTM2.step, Fin.isValue, mul_zero, zero_add, zero_mul] using hbounded
  | succ quotientCount ih =>
      have hmatch := sourceUnaryDivision_matchFullTrace
        modulus true
        (List.replicate
          (modulus * quotientCount + remainder) true)
        [] (List.replicate previous true) [] output
      simp only [List.append_nil] at hmatch
      have hrestore := sourceUnaryDivision_restoreModulusTrace
        modulus true
        (List.replicate
          (modulus * quotientCount + remainder) true)
        [] (List.replicate previous true) output
      simp only [List.append_nil] at hrestore
      have hremaining := ih (previous + 1)
      have hquotient :
          List.replicate (previous + 1) true =
            true :: List.replicate previous true := by
        simp only [List.replicate_succ]
      rw [hquotient] at hremaining
      have hfirst := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hmatch hrestore
      have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hremaining
      have hbudget :
          (quotientCount * (2 * modulus + 3) +
            4 * modulus + (previous + 1) + 12) +
            ((modulus + 1) + (modulus + 1)) ≤
              (quotientCount + 1) * (2 * modulus + 3) +
                4 * modulus + previous + 12 := by
        simp only [Nat.add_mul, one_mul]
        omega
      have hbounded := rebound (newBudget :=
          (quotientCount + 1) * (2 * modulus + 3) +
            4 * modulus + previous + 12)
        hfull hbudget
      have hdividend :
          modulus * (quotientCount + 1) + remainder =
            modulus + (modulus * quotientCount + remainder) := by
        simp only [Nat.mul_add, mul_one]
        omega
      have hresult :
          quotientCount + (previous + 1) =
            (quotientCount + 1) + previous := by omega
      simpa only [Nat.succ_eq_add_one, hdividend,
        List.replicate_add, hresult] using hbounded

end

section

open Turing GapCVP.BinaryEncoding GapCVP.SourceInterpolationRowTM

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceUnaryDivisionQuery_reverse
    (dividend modulus : ℕ) (source : List Bool) :
    (sourceUnaryDivisionQuery dividend modulus source).reverse =
      source.reverse ++
        false :: (List.replicate modulus true ++
          false :: List.replicate dividend true) := by
  simp only [sourceUnaryDivisionQuery, List.reverse_append, List.reverse_cons,
      List.reverse_replicate,
      List.append_assoc, List.cons_append, List.nil_append]

end

end SourceMixedRadixUnaryQuotientRemainderTM

end GapCVP

end
