/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part06C

/-! # GapCVP proof, part 06, continuation 04 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace SourceMixedRadixUnaryQuotientRemainderTM

section

open Turing GapCVP.BinaryEncoding GapCVP.SourceInterpolationRowTM

private def sourceUnaryDivision_delimitedPrefixTrace
    (dividend modulus : ℕ) (source : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (Turing.initList sourceUnaryDivisionMachine
        (sourceUnaryDivisionQuery dividend modulus source))
      (some (sourceUnaryDivisionConfiguration 4 true
        [] [] (List.replicate dividend true)
        (List.replicate modulus true) [] [] []
        (false :: sourceUnaryDivisionQuery dividend modulus source)))
      (2 * (sourceUnaryDivisionQuery dividend modulus source).length + 2) := by
  rw [sourceUnaryDivisionMachine_init]
  have hfirst := sourceUnaryDivisionDividendPrefixTrace
    dividend true
    (List.replicate modulus true ++ false :: source)
    [] [] [] [] [] [] []
  have hsecond := sourceUnaryDivisionModulusPrefixTrace
    modulus true source
    (false :: List.replicate dividend true)
    (List.replicate dividend true) [] [] [] [] []
  have hsuffix := sourceUnaryDivisionSuffixTrace
    source
    (false :: (List.replicate modulus true ++
      false :: List.replicate dividend true))
    (List.replicate dividend true)
    (List.replicate modulus true) [] [] [] [] true
  have harchive :
      source.reverse ++
        (false :: (List.replicate modulus true ++
          false :: List.replicate dividend true)) =
      (sourceUnaryDivisionQuery dividend modulus source).reverse := by
    symm
    exact sourceUnaryDivisionQuery_reverse dividend modulus source
  rw [harchive] at hsuffix
  have hrestore := sourceUnaryDivisionRestoreSourceTrace
    (sourceUnaryDivisionQuery dividend modulus source).reverse
    (List.replicate dividend true)
    (List.replicate modulus true) [] [] [] [] true
  simp only [List.append_nil] at hfirst hsecond hsuffix
  simp only [List.append_nil, List.reverse_reverse,
    List.length_reverse] at hrestore
  have hparsed := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hsecond
  have harchived := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hparsed hsuffix
  have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ harchived hrestore
  have hlength :
      (sourceUnaryDivisionQuery dividend modulus source).length =
        dividend + modulus + source.length + 2 := by
    simp only [sourceUnaryDivisionQuery, List.length_append, List.length_replicate,
        List.length_cons]
    omega
  have hbounded := rebound (newBudget :=
      2 * (sourceUnaryDivisionQuery dividend modulus source).length + 2)
    hfull (by
      simp only [hlength]
      omega)
  simpa only [sourceUnaryDivisionQuery] using hbounded

private noncomputable def sourceUnaryDivisionTimePolynomial : Polynomial ℕ :=
  4 * Polynomial.X ^ 2 + 20 * Polynomial.X + 30

private noncomputable def sourceUnaryDivision_validOriginalTrace
    (dividend modulus : ℕ) (source : List Bool)
    (hmodulus : 0 < modulus) :
    EvalsToInTime sourceUnaryDivisionMachine.step (Turing.initList sourceUnaryDivisionMachine
        (sourceUnaryDivisionQuery dividend modulus source))
      (some (Turing.haltList sourceUnaryDivisionMachine
        (sourceUnaryDivisionOutput
          (sourceUnaryDivisionQuery dividend modulus source))))
      (sourceUnaryDivisionTimePolynomial.eval
        (sourceUnaryDivisionQuery dividend modulus source).length) := by
  let input := sourceUnaryDivisionQuery dividend modulus source
  have hprefix := sourceUnaryDivision_delimitedPrefixTrace
    dividend modulus source
  have hmodulusWord :
      List.replicate modulus true =
        true :: List.replicate (modulus - 1) true := by
    have hdecompose : modulus = (modulus - 1) + 1 := by omega
    conv_lhs => rw [hdecompose, List.replicate_succ]
  have hdispatch := oneStep _ _ (sourceUnaryDivision_dispatch_valid
      (List.replicate (modulus - 1) true)
      (List.replicate dividend true) [] [] []
      (false :: input))
  rw [← hmodulusWord] at hdispatch
  have hremaining : dividend % modulus < modulus :=
    Nat.mod_lt dividend hmodulus
  have harithmetic :
      modulus * (dividend / modulus) + dividend % modulus =
        dividend := by
    have h := Nat.mod_add_div dividend modulus
    omega
  have hmodulo := sourceUnaryDivisionModuloTrace
    modulus (dividend / modulus) (dividend % modulus)
    0 hremaining (false :: input)
  simp only [Nat.add_zero, List.replicate_zero] at hmodulo
  rw [harithmetic] at hmodulo
  change EvalsToInTime sourceUnaryDivisionMachine.step
    (Turing.initList sourceUnaryDivisionMachine input)
    (some (Turing.haltList sourceUnaryDivisionMachine
      (sourceUnaryDivisionOutput input)))
    (sourceUnaryDivisionTimePolynomial.eval input.length)
  have hfirst := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hprefix hdispatch
  have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hmodulo
  have hinputLength :
      input.length = dividend + modulus + source.length + 2 := by
    simp only [sourceUnaryDivisionQuery, List.length_append, List.length_replicate,
        List.length_cons, input]
    omega
  have hdividend : dividend ≤ input.length := by
    rw [hinputLength]
    omega
  have hwidth : modulus ≤ input.length := by
    rw [hinputLength]
    omega
  have hquotient : dividend / modulus ≤ input.length :=
    (Nat.div_le_self dividend modulus).trans hdividend
  have hproduct :
      (dividend / modulus) * (2 * modulus + 3) ≤
        input.length * (2 * input.length + 3) :=
    Nat.mul_le_mul hquotient (by omega)
  have hbound :
      ((dividend / modulus) * (2 * modulus + 3) +
        4 * modulus + 0 + 12) +
        (1 + (2 * input.length + 2)) ≤
          sourceUnaryDivisionTimePolynomial.eval input.length := by
    simp only [add_zero, sourceUnaryDivisionTimePolynomial, Polynomial.eval_add,
        Polynomial.eval_mul,
        Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_X]
    nlinarith
  have hbounded := rebound hfull hbound
  have houtput := sourceUnaryDivisionOutput_valid
    dividend modulus source hmodulus
  change sourceUnaryDivisionOutput input = _ at houtput
  rw [houtput]
  exact hbounded

private noncomputable def sourceUnaryDivision_zeroModulusTrace
    (dividend : ℕ) (source : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (Turing.initList sourceUnaryDivisionMachine
        (sourceUnaryDivisionQuery dividend 0 source))
      (some (Turing.haltList sourceUnaryDivisionMachine
        (sourceUnaryDivisionOutput
          (sourceUnaryDivisionQuery dividend 0 source))))
      (sourceUnaryDivisionTimePolynomial.eval
        (sourceUnaryDivisionQuery dividend 0 source).length) := by
  let input := sourceUnaryDivisionQuery dividend 0 source
  have hprefix := sourceUnaryDivision_delimitedPrefixTrace
    dividend 0 source
  have hdispatch := oneStep _ _ (sourceUnaryDivision_dispatch_zero
      (List.replicate dividend true) [] [] []
      (false :: input))
  have hcleanup := sourceUnaryDivisionCleanupTrace
    0 0 dividend 0 true (false :: false :: input)
  have hfirst := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hprefix hdispatch
  have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hcleanup
  have hlength : dividend ≤ input.length := by
    simp only [sourceUnaryDivisionQuery, List.replicate_zero, List.nil_append, List.length_append,
        List.length_replicate, List.length_cons, le_add_iff_nonneg_right, zero_le, input]
  have hbound :
      (0 + 0 + dividend + 0 + 4) +
        (1 + (2 * input.length + 2)) ≤
      sourceUnaryDivisionTimePolynomial.eval input.length := by
    simp only [add_zero, zero_add, sourceUnaryDivisionTimePolynomial, Polynomial.eval_add,
        Polynomial.eval_mul,
        Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_X]
    nlinarith
  have hbounded := rebound hfull hbound
  change EvalsToInTime sourceUnaryDivisionMachine.step
    (Turing.initList sourceUnaryDivisionMachine input)
    (some (Turing.haltList sourceUnaryDivisionMachine
      (sourceUnaryDivisionOutput input)))
    (sourceUnaryDivisionTimePolynomial.eval input.length)
  have houtput : sourceUnaryDivisionOutput input =
      false :: false :: input := by
    simp only [sourceUnaryDivisionOutput, sourceUnaryDivisionQuery, List.replicate_zero,
        List.nil_append,
        readUnaryPrefix_replicate, readUnaryPrefix, ↓reduceIte, input]
  rw [houtput]
  exact hbounded

private noncomputable def sourceUnaryDivision_missingFirstTrace
    (count : ℕ) :
    EvalsToInTime sourceUnaryDivisionMachine.step (Turing.initList sourceUnaryDivisionMachine
        (List.replicate count true))
      (some (Turing.haltList sourceUnaryDivisionMachine
        (sourceUnaryDivisionOutput
          (List.replicate count true))))
      (sourceUnaryDivisionTimePolynomial.eval count) := by
  rw [sourceUnaryDivisionMachine_init]
  let input := List.replicate count true
  have hfirst := sourceUnaryDivisionDividendMissingTrace
    count true [] [] [] [] [] [] []
  simp only [List.append_nil] at hfirst
  have hsuffix := sourceUnaryDivisionSuffixTrace
    [] (List.replicate count true)
    (List.replicate count true) [] [] [] [] [] false
  simp only [List.reverse_nil, List.nil_append] at hsuffix
  have hrestore := sourceUnaryDivisionRestoreSourceTrace
    (List.replicate count true)
    (List.replicate count true) [] [] [] [] [] false
  simp only [List.reverse_replicate, List.append_nil] at hrestore
  have hdispatch := oneStep _ _ (sourceUnaryDivision_dispatch_invalid
      (List.replicate count true) [] [] [] []
      (false :: input))
  have hcleanup := sourceUnaryDivisionCleanupTrace
    0 0 count 0 false (false :: false :: input)
  have harchived := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hsuffix
  have hrestored := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ harchived
      hrestore
  have hfailed := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hrestored hdispatch
  have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfailed hcleanup
  simp only [List.length_replicate, List.length_nil] at hfull
  have hbound :
      (0 + 0 + count + 0 + 4) +
        (1 + ((count + 1) + (1 + (count + 1)))) ≤
          sourceUnaryDivisionTimePolynomial.eval count := by
    simp only [add_zero, zero_add, sourceUnaryDivisionTimePolynomial, Polynomial.eval_add,
        Polynomial.eval_mul,
        Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_X]
    nlinarith
  have hbounded := rebound hfull hbound
  have houtput : sourceUnaryDivisionOutput input =
      false :: false :: input := by
    simp only [sourceUnaryDivisionOutput, SourceTotalStructuralDecoder.readUnaryPrefix_missing,
        input]
  change EvalsToInTime sourceUnaryDivisionMachine.step
    (sourceUnaryDivisionConfiguration 0 true
      input [] [] [] [] [] [] [])
    (some (Turing.haltList sourceUnaryDivisionMachine
      (sourceUnaryDivisionOutput input)))
    (sourceUnaryDivisionTimePolynomial.eval count)
  rw [houtput]
  exact hbounded

private def sourceUnaryDivisionMissingModulusQuery
    (dividend markerCount : ℕ) : List Bool :=
  List.replicate dividend true ++
    false :: List.replicate markerCount true

private theorem sourceUnaryDivisionMissingModulusQuery_reverse
    (dividend markerCount : ℕ) :
    (sourceUnaryDivisionMissingModulusQuery
      dividend markerCount).reverse =
      List.replicate markerCount true ++
        false :: List.replicate dividend true := by
  simp only [sourceUnaryDivisionMissingModulusQuery, List.reverse_append, List.reverse_cons,
      List.reverse_replicate, List.append_assoc, List.cons_append, List.nil_append]

private noncomputable def sourceUnaryDivision_missingSecondTrace
    (dividend markerCount : ℕ) :
    EvalsToInTime sourceUnaryDivisionMachine.step (Turing.initList sourceUnaryDivisionMachine
        (sourceUnaryDivisionMissingModulusQuery
          dividend markerCount))
      (some (Turing.haltList sourceUnaryDivisionMachine
        (sourceUnaryDivisionOutput
          (sourceUnaryDivisionMissingModulusQuery
            dividend markerCount))))
      (sourceUnaryDivisionTimePolynomial.eval
        (sourceUnaryDivisionMissingModulusQuery
          dividend markerCount).length) := by
  rw [sourceUnaryDivisionMachine_init]
  let input := sourceUnaryDivisionMissingModulusQuery
    dividend markerCount
  have hfirst := sourceUnaryDivisionDividendPrefixTrace
    dividend true (List.replicate markerCount true)
    [] [] [] [] [] [] []
  have hsecond := sourceUnaryDivisionModulusMissingTrace
    markerCount true
    (false :: List.replicate dividend true)
    (List.replicate dividend true) [] [] [] [] []
  simp only [List.append_nil] at hfirst hsecond
  have hreverse :
      List.replicate markerCount true ++
        false :: List.replicate dividend true = input.reverse := by
    simpa only using (sourceUnaryDivisionMissingModulusQuery_reverse dividend markerCount).symm
  rw [hreverse] at hsecond
  have hsuffix := sourceUnaryDivisionSuffixTrace
    [] input.reverse
    (List.replicate dividend true)
    (List.replicate markerCount true) [] [] [] [] false
  simp only [List.reverse_nil, List.nil_append] at hsuffix
  have hrestore := sourceUnaryDivisionRestoreSourceTrace
    input.reverse (List.replicate dividend true)
    (List.replicate markerCount true) [] [] [] [] false
  simp only [List.reverse_reverse, List.append_nil,
    List.length_reverse] at hrestore
  have hdispatch := oneStep _ _ (sourceUnaryDivision_dispatch_invalid
      (List.replicate dividend true)
      (List.replicate markerCount true) [] [] []
      (false :: input))
  have hcleanup := sourceUnaryDivisionCleanupTrace
    markerCount 0 dividend 0 false
    (false :: false :: input)
  have hfirstPair := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirst hsecond
  have harchived := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfirstPair
      hsuffix
  have hrestored := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ harchived
      hrestore
  have hfailed := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hrestored hdispatch
  have hfull := EvalsToInTime.trans sourceUnaryDivisionMachine.step _ _ _ _ _ hfailed hcleanup
  have hlength : input.length = dividend + markerCount + 1 := by
    simp only [sourceUnaryDivisionMissingModulusQuery, List.length_append, List.length_replicate,
        List.length_cons, input]
    omega
  have hbound :
      (markerCount + 0 + dividend + 0 + 4) +
        (1 + ((input.length + 1) +
          (1 + ((markerCount + 1) + (dividend + 1))))) ≤
          sourceUnaryDivisionTimePolynomial.eval input.length := by
    simp only [add_zero, sourceUnaryDivisionTimePolynomial, Polynomial.eval_add,
        Polynomial.eval_mul,
        Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_X]
    nlinarith
  have hbounded := rebound hfull hbound
  have houtput : sourceUnaryDivisionOutput input =
      false :: false :: input := by
    simp only [sourceUnaryDivisionOutput, sourceUnaryDivisionMissingModulusQuery,
        readUnaryPrefix_replicate,
        SourceTotalStructuralDecoder.readUnaryPrefix_missing, input]
  change EvalsToInTime sourceUnaryDivisionMachine.step
    (sourceUnaryDivisionConfiguration 0 true
      input [] [] [] [] [] [] [])
    (some (Turing.haltList sourceUnaryDivisionMachine
      (sourceUnaryDivisionOutput input)))
    (sourceUnaryDivisionTimePolynomial.eval input.length)
  rw [houtput]
  exact hbounded

private noncomputable def sourceUnaryDivision_totalTrace
    (input : List Bool) :
    EvalsToInTime sourceUnaryDivisionMachine.step (Turing.initList sourceUnaryDivisionMachine
        input)
      (some (Turing.haltList sourceUnaryDivisionMachine
        (sourceUnaryDivisionOutput input)))
      (sourceUnaryDivisionTimePolynomial.eval input.length) := by
  cases hfirst : readUnaryPrefix input with
  | none =>
      have hshape := readUnaryPrefix_none_eq_replicate input hfirst
      have htrace := sourceUnaryDivision_missingFirstTrace input.length
      rw [← hshape] at htrace
      exact htrace
  | some first =>
      obtain ⟨dividend, remaining⟩ := first
      have hinput := readUnaryPrefix_some_decompose
        input dividend remaining hfirst
      cases hsecond : readUnaryPrefix remaining with
      | none =>
          have hremaining :=
            readUnaryPrefix_none_eq_replicate remaining hsecond
          have hquery :
              input = sourceUnaryDivisionMissingModulusQuery
                dividend remaining.length := by
            calc
              input =
                  List.replicate dividend true ++ false :: remaining :=
                hinput
              _ = List.replicate dividend true ++
                  false :: List.replicate remaining.length true :=
                congrArg
                  (fun tail : List Bool =>
                    List.replicate dividend true ++ false :: tail)
                  hremaining
              _ = sourceUnaryDivisionMissingModulusQuery
                  dividend remaining.length := rfl
          simpa only [hquery] using
            sourceUnaryDivision_missingSecondTrace
              dividend remaining.length
      | some second =>
          obtain ⟨modulus, source⟩ := second
          have hremaining := readUnaryPrefix_some_decompose
            remaining modulus source hsecond
          have hquery :
              input = sourceUnaryDivisionQuery
                dividend modulus source := by
            rw [hinput, hremaining]
            rfl
          cases modulus with
          | zero =>
              simpa only [hquery] using
                sourceUnaryDivision_zeroModulusTrace dividend source
          | succ modulus =>
              simpa only [hquery] using
                sourceUnaryDivision_validOriginalTrace
                  dividend (modulus + 1) source
                  (Nat.zero_lt_succ modulus)

/-- GapCVP reduction support. -/
noncomputable def sourceUnaryDivisionComputable :
    BitTM sourceUnaryDivisionOutput where
  tm := sourceUnaryDivisionMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := sourceUnaryDivisionTimePolynomial
  outputsFun input := {
    steps := (sourceUnaryDivision_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, Option.map_some] using
          (sourceUnaryDivision_totalTrace input).evals_in_steps
    steps_le_m := by
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq] using
          (sourceUnaryDivision_totalTrace input).steps_le_m
  }

end

end SourceMixedRadixUnaryQuotientRemainderTM

namespace SourceMixedRadixDimensionRowMajorIndexTM

open Turing GapCVP.SourceStructuralTuringTM GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceMixedRadixUnaryQuotientRemainderTM

private def sourceMixedRadixBlockDimensionPrefixOutput
    (input : List Bool) : List Bool :=
  (unaryPrefixOutput input).tail

private noncomputable def sourceMixedRadixBlockDimensionPrefixComputable :
    BitTM
      sourceMixedRadixBlockDimensionPrefixOutput := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    unaryPrefixComputable dropHeadComputable
  change BitTM
    (fun input => (unaryPrefixOutput input).tail)
  simpa only [Function.comp_def] using hphysical

@[simp] private theorem sourceMixedRadixBlockDimensionPrefixOutput_valid
    (dimension : ℕ) (source : List Bool) :
    sourceMixedRadixBlockDimensionPrefixOutput
        (List.replicate dimension true ++ false :: source) =
      List.replicate dimension true := by
  unfold sourceMixedRadixBlockDimensionPrefixOutput
  rw [unaryPrefixOutput_replicate_delimiter]
  rfl

/-- GapCVP reduction support. -/
def sourceMixedRadixRowMajorPairOutput : List Bool → List Bool :=
  sourceUnaryDivisionOutput

/-- GapCVP reduction support. -/
noncomputable def sourceMixedRadixRowMajorPairComputable :
    BitTM
      sourceMixedRadixRowMajorPairOutput :=
  sourceUnaryDivisionComputable

@[simp] theorem sourceMixedRadixRowMajorPairOutput_valid
    (rank dimension : ℕ) (source : List Bool)
    (hdimension : 0 < dimension) :
    sourceMixedRadixRowMajorPairOutput
        (sourceUnaryDivisionQuery rank dimension source) =
      List.replicate (rank / dimension) true ++
        false :: (List.replicate (rank % dimension) true ++
          false :: sourceUnaryDivisionQuery rank dimension source) := by
  exact sourceUnaryDivisionOutput_valid
    rank dimension source hdimension

end SourceMixedRadixDimensionRowMajorIndexTM

namespace SourceMixedRadixOriginalSourceDescriptorRotationTM

open Turing GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder

/-- GapCVP reduction support. -/
def sourceMixedRadixGuardedOriginalAtomOutput
    (atom : List Bool → List Bool) : List Bool → List Bool :=
  atom ∘ firstFieldContents

/-- GapCVP reduction support. -/
noncomputable def sourceMixedRadixGuardedOriginalAtomComputable
    {atom : List Bool → List Bool}
    (computer : BitTM atom) :
    BitTM
      (sourceMixedRadixGuardedOriginalAtomOutput atom) :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable computer

/-- GapCVP reduction support. -/
def sourceMixedRadixOriginalSourceQueryStream
    (queries : List (List Bool)) : List Bool :=
  queries.flatMap lengthPrefixedWord

end SourceMixedRadixOriginalSourceDescriptorRotationTM

namespace SourceMixedRadixPolynomialPaddedDescriptorFoldTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.FormulaSemanticCert
open GapCVP.SourceTotalStructuralDecoder GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceWholeOutputAssemblyTM

theorem sourceMixedRadixPhysicalFirstFieldContents_length_le
    (input : List Bool) :
    (firstFieldContents input).length ≤ input.length := by
  cases hread : readLengthPrefixedWord input with
  | none =>
      simp only [firstFieldContents, payloadDecodeOutput, hread, List.tail_cons, List.length_nil,
          zero_le]
  | some parsed =>
      obtain ⟨payload, suffix⟩ := parsed
      have hreconstruct := readLengthPrefixedWord_some_reconstruct
        input payload suffix hread
      simp only [firstFieldContents, payloadDecodeOutput, hread,
        List.tail_cons]
      rw [hreconstruct]
      simp only [List.length_append, lengthPrefixedWord_length]
      omega

theorem sourceMixedRadixPhysicalFirstFieldSuffix_length_le
    (input : List Bool) :
    (firstFieldSuffix input).length ≤ input.length := by
  cases hread : readLengthPrefixedWord input with
  | none =>
      simp only [firstFieldSuffix, hread, List.length_nil, zero_le]
  | some parsed =>
      obtain ⟨payload, suffix⟩ := parsed
      have hreconstruct := readLengthPrefixedWord_some_reconstruct
        input payload suffix hread
      simp only [firstFieldSuffix, hread]
      rw [hreconstruct]
      simp only [List.length_append, lengthPrefixedWord_length]
      omega

end SourceMixedRadixPolynomialPaddedDescriptorFoldTM

namespace SourceIndexedClauseLookupTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceMixedRadixDimensionRowMajorIndexTM
open GapCVP.SourceMixedRadixPolynomialPaddedDescriptorFoldTM
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFCappedUnaryPairArithmeticTM GapCVP.CNFFlatPhysicalBinaryAppendTM

/-- GapCVP reduction support. -/
def sourceOriginalIndexedClauseQuery
    (index : ℕ) (formula : ThreeCNF) : List Bool :=
  List.replicate index true ++ false :: encodeThreeCNF formula

private def sourceOriginalIndexedClauseCounterWord
    (input : List Bool) : List Bool :=
  sourceMixedRadixBlockDimensionPrefixOutput input ++ [false]

private noncomputable def sourceOriginalIndexedClauseCounterComputable :
    BitTM
      sourceOriginalIndexedClauseCounterWord := by
  have hphysical := pointwiseAppendComputable
    sourceMixedRadixBlockDimensionPrefixComputable
    (sourceFixedWordComputable [false])
  exact hphysical

private def sourceOriginalIndexedClauseBodyWord
    (input : List Bool) : List Bool :=
  firstFieldSuffix (unaryPrefixSuffixOutput input)

private noncomputable def sourceOriginalIndexedClauseBodyComputable :
    BitTM
      sourceOriginalIndexedClauseBodyWord := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    actualUnaryPrefixSuffixComputable firstFieldSuffixComputable
  change BitTM
    (fun input => firstFieldSuffix (unaryPrefixSuffixOutput input))
  simpa only [Function.comp_def] using hphysical

private def sourceOriginalIndexedClauseSkipPreparation
    (input : List Bool) : List Bool :=
  sourceOriginalIndexedClauseCounterWord input ++
    sourceOriginalIndexedClauseBodyWord input

private noncomputable def sourceOriginalIndexedClauseSkipPreparationComputable :
    BitTM
      sourceOriginalIndexedClauseSkipPreparation :=
  pointwiseAppendComputable
    sourceOriginalIndexedClauseCounterComputable
    sourceOriginalIndexedClauseBodyComputable

@[simp] private theorem sourceOriginalIndexedClauseSkipPreparation_valid
    (index : ℕ) (formula : ThreeCNF) :
    sourceOriginalIndexedClauseSkipPreparation
        (sourceOriginalIndexedClauseQuery index formula) =
      unaryBoundedFoldWord index
        (formula.flatMap encodeThreeClause) := by
  simp only [sourceOriginalIndexedClauseSkipPreparation, sourceOriginalIndexedClauseCounterWord,
      sourceOriginalIndexedClauseQuery, sourceMixedRadixBlockDimensionPrefixOutput_valid,
      sourceOriginalIndexedClauseBodyWord, unaryPrefixSuffixOutput_valid,
          firstFieldSuffix_encodeThreeCNF,
      List.append_assoc, List.cons_append, List.nil_append, unaryBoundedFoldWord]

theorem sourceOriginalIndexedLiteralSuffix_length_le
    (input : List Bool) :
    (literalSuffix input).length ≤ input.length := by
  have hsuffix := sourceMixedRadixPhysicalFirstFieldSuffix_length_le input
  unfold literalSuffix
  change (firstFieldSuffix input).tail.length ≤ input.length
  cases hfield : firstFieldSuffix input with
  | nil => simp only [List.tail_nil, List.length_nil, zero_le]
  | cons bit remaining =>
      simp only [hfield, List.tail_cons] at hsuffix ⊢
      simp only [List.length_cons] at hsuffix
      omega

theorem sourceOriginalIndexedClauseSuffix_length_le
    (input : List Bool) :
    (clauseSuffix input).length ≤ input.length := by
  change
    (literalSuffix (literalSuffix (literalSuffix input))).length ≤
      input.length
  exact
    (sourceOriginalIndexedLiteralSuffix_length_le _).trans
      ((sourceOriginalIndexedLiteralSuffix_length_le _).trans
        (sourceOriginalIndexedLiteralSuffix_length_le input))

private theorem sourceOriginalIndexedClauseSuffix_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates clauseSuffix Polynomial.X := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage _
  have hseed := GapCVP.CNFTypedRecordWorkerTM.parsedUnaryFold_seed_length_le
    input count seed hparse
  have hiterate : ∀ number : ℕ,
      ((clauseSuffix^[number]) seed).length ≤ seed.length := by
    intro number
    induction number with
    | zero => simp only [Function.iterate_zero, id_eq, Std.le_refl]
    | succ number ih =>
        rw [Function.iterate_succ_apply']
        exact (sourceOriginalIndexedClauseSuffix_length_le _).trans ih
  simpa only [Polynomial.eval_X, ge_iff_le] using (hiterate stage).trans hseed

private noncomputable def sourceOriginalIndexedClauseSkipFoldComputable :
    BitTM
      (boundedRecordFoldOutput clauseSuffix) :=
  boundedDependentRecordFoldComputable clauseSuffixComputable
    Polynomial.X
    sourceOriginalIndexedClauseSuffix_polynomiallyBoundedFoldStates

private def sourceOriginalIndexedClauseTailOutput : List Bool → List Bool :=
  boundedRecordFoldOutput clauseSuffix ∘
    sourceOriginalIndexedClauseSkipPreparation

private noncomputable def sourceOriginalIndexedClauseTailComputable :
    BitTM
      sourceOriginalIndexedClauseTailOutput :=
  GapCVP.TMComposition.computableInPolyTime
    sourceOriginalIndexedClauseSkipPreparationComputable
    sourceOriginalIndexedClauseSkipFoldComputable

private theorem sourceOriginalIndexedClauseSuffix_iterate_body
    (formula : ThreeCNF) (index : ℕ) :
    ((clauseSuffix^[index])
      (formula.flatMap encodeThreeClause)) =
        (formula.drop index).flatMap encodeThreeClause := by
  induction index generalizing formula with
  | zero => simp only [Function.iterate_zero, id_eq, List.drop_zero]
  | succ index ih =>
      cases formula with
      | nil =>
          rw [Function.iterate_succ_apply]
          change ((clauseSuffix^[index]) []) = []
          simpa only [List.flatMap_nil, List.drop_nil] using ih []
      | cons clause remaining =>
          rw [Function.iterate_succ_apply]
          simp only [List.flatMap_cons]
          rw [clauseSuffix_valid]
          simpa only [List.drop_succ_cons] using ih remaining

@[simp] private theorem sourceOriginalIndexedClauseTailOutput_valid
    (index : ℕ) (formula : ThreeCNF) :
    sourceOriginalIndexedClauseTailOutput
        (sourceOriginalIndexedClauseQuery index formula) =
      (formula.drop index).flatMap encodeThreeClause := by
  unfold sourceOriginalIndexedClauseTailOutput
  rw [Function.comp_apply,
    sourceOriginalIndexedClauseSkipPreparation_valid]
  simp only [boundedRecordFoldOutput,
    parseUnaryBoundedFold_word]
  exact sourceOriginalIndexedClauseSuffix_iterate_body
    formula index

/-- GapCVP reduction support. -/
def sourceOriginalIndexedLiteralSignOutput
    (input : List Bool) : List Bool :=
  markerConditionalOutput
    (fun _ : List Bool => [true]) [false]
    (firstFieldSuffix input)

/-- GapCVP reduction support. -/
noncomputable def sourceOriginalIndexedLiteralSignComputable :
    BitTM
      sourceOriginalIndexedLiteralSignOutput := by
  have hsign := markerConditionalComputable
    (sourceFixedWordComputable [true]) [false]
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable hsign
  change BitTM
    (fun input => markerConditionalOutput
      (fun _ : List Bool => [true]) [false]
      (firstFieldSuffix input))
  simpa only [Function.comp_def] using hphysical

/-- GapCVP reduction support. -/
def sourceOriginalIndexedLiteralVariableOutput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (firstFieldContents input)

private noncomputable def sourceOriginalIndexedLiteralVariableComputable :
    BitTM
      sourceOriginalIndexedLiteralVariableOutput := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable structuralPrefixWriterComputable
  change BitTM
    (fun input => lengthPrefixedWord (firstFieldContents input))
  simpa only [Function.comp_def] using hphysical

/-- GapCVP reduction support. -/
def sourceOriginalIndexedPhysicalLiteralOutput
    (input : List Bool) : List Bool :=
  sourceOriginalIndexedLiteralVariableOutput input ++
    sourceOriginalIndexedLiteralSignOutput input

/-- GapCVP reduction support. -/
noncomputable def sourceOriginalIndexedPhysicalLiteralComputable :
    BitTM
      sourceOriginalIndexedPhysicalLiteralOutput :=
  pointwiseAppendComputable
    sourceOriginalIndexedLiteralVariableComputable
    sourceOriginalIndexedLiteralSignComputable

@[simp] theorem sourceOriginalIndexedPhysicalLiteralOutput_valid
    (literal : Literal) (suffix : List Bool) :
    sourceOriginalIndexedPhysicalLiteralOutput
        (encodeLiteral literal ++ suffix) =
      encodeLiteral literal := by
  rcases literal with ⟨variableIndex, sign⟩
  cases sign <;>
    simp [sourceOriginalIndexedPhysicalLiteralOutput,
      sourceOriginalIndexedLiteralVariableOutput,
      sourceOriginalIndexedLiteralSignOutput,
      encodeLiteral, markerConditionalOutput,
      firstFieldContents_valid, firstFieldSuffix_valid,
      List.append_assoc]

/-- GapCVP reduction support. -/
def sourceOriginalIndexedSecondLiteralOutput : List Bool → List Bool :=
  sourceOriginalIndexedPhysicalLiteralOutput ∘ literalSuffix

private noncomputable def sourceOriginalIndexedSecondLiteralComputable :
    BitTM
      sourceOriginalIndexedSecondLiteralOutput :=
  GapCVP.TMComposition.computableInPolyTime
    literalSuffixComputable
    sourceOriginalIndexedPhysicalLiteralComputable

/-- GapCVP reduction support. -/
def sourceOriginalIndexedThirdLiteralOutput : List Bool → List Bool :=
  sourceOriginalIndexedPhysicalLiteralOutput ∘
    (literalSuffix ∘ literalSuffix)

private noncomputable def sourceOriginalIndexedThirdLiteralComputable :
    BitTM
      sourceOriginalIndexedThirdLiteralOutput :=
  GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      literalSuffixComputable literalSuffixComputable)
    sourceOriginalIndexedPhysicalLiteralComputable

/-- GapCVP reduction support. -/
def sourceOriginalIndexedPhysicalThreeClauseOutput
    (input : List Bool) : List Bool :=
  sourceOriginalIndexedPhysicalLiteralOutput input ++
    (sourceOriginalIndexedSecondLiteralOutput input ++
      sourceOriginalIndexedThirdLiteralOutput input)

/-- GapCVP reduction support. -/
noncomputable def sourceOriginalIndexedPhysicalThreeClauseComputable :
    BitTM
      sourceOriginalIndexedPhysicalThreeClauseOutput :=
  pointwiseAppendComputable
    sourceOriginalIndexedPhysicalLiteralComputable
    (pointwiseAppendComputable
      sourceOriginalIndexedSecondLiteralComputable
      sourceOriginalIndexedThirdLiteralComputable)

@[simp] theorem sourceOriginalIndexedPhysicalThreeClauseOutput_valid
    (clause : ThreeClause) (suffix : List Bool) :
    sourceOriginalIndexedPhysicalThreeClauseOutput
        (encodeThreeClause clause ++ suffix) =
      encodeThreeClause clause := by
  simp only [sourceOriginalIndexedPhysicalThreeClauseOutput, encodeThreeClause, Fin.isValue,
      List.append_assoc,
      sourceOriginalIndexedPhysicalLiteralOutput_valid, sourceOriginalIndexedSecondLiteralOutput,
          Function.comp_apply,
      literalSuffix_valid, sourceOriginalIndexedThirdLiteralOutput]

/-- GapCVP reduction support. -/
def sourceOriginalIndexedClauseOutput : List Bool → List Bool :=
  sourceOriginalIndexedPhysicalThreeClauseOutput ∘
    sourceOriginalIndexedClauseTailOutput

/-- GapCVP reduction support. -/
noncomputable def sourceOriginalIndexedClauseComputable :
    BitTM
      sourceOriginalIndexedClauseOutput :=
  GapCVP.TMComposition.computableInPolyTime
    sourceOriginalIndexedClauseTailComputable
    sourceOriginalIndexedPhysicalThreeClauseComputable

theorem sourceOriginalIndexedClauseOutput_valid
    (index : ℕ) (formula : ThreeCNF)
    (hindex : index < formula.length) :
    sourceOriginalIndexedClauseOutput
        (sourceOriginalIndexedClauseQuery index formula) =
      encodeThreeClause (formula.get ⟨index, hindex⟩) := by
  unfold sourceOriginalIndexedClauseOutput
  rw [Function.comp_apply,
    sourceOriginalIndexedClauseTailOutput_valid]
  have hdrop := List.drop_eq_getElem_cons hindex
  rw [hdrop]
  simp only [List.flatMap_cons]
  rw [sourceOriginalIndexedPhysicalThreeClauseOutput_valid]
  simp only [List.get_eq_getElem]

end SourceIndexedClauseLookupTM

namespace SourceIndexedClauseSignTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceIndexedClauseLookupTM

@[simp] theorem sourceOriginalIndexedLiteralSignOutput_valid
    (literal : Literal) (suffix : List Bool) :
    sourceOriginalIndexedLiteralSignOutput
        (encodeLiteral literal ++ suffix) = [literal.2] := by
  rcases literal with ⟨variableIndex, sign⟩
  cases sign <;>
    simp [sourceOriginalIndexedLiteralSignOutput,
      encodeLiteral, markerConditionalOutput,
      firstFieldSuffix_valid, List.append_assoc]

/-- GapCVP reduction support. -/
def sourceOriginalClauseBooleanUnaryOutput : List Bool → List Bool :=
  markerConditionalOutput
    (fun _ : List Bool => [true]) []

/-- GapCVP reduction support. -/
noncomputable def sourceOriginalClauseBooleanUnaryComputable :
    BitTM
      sourceOriginalClauseBooleanUnaryOutput :=
  markerConditionalComputable
    (sourceFixedWordComputable [true]) []

@[simp] theorem sourceOriginalClauseBooleanUnaryOutput_bit
    (sign : Bool) :
    sourceOriginalClauseBooleanUnaryOutput [sign] =
      List.replicate (if sign then 1 else 0) true := by
  cases sign <;> rfl

end SourceIndexedClauseSignTM

namespace SourceAnchoredGridRecordFoldTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.FormulaSemanticCert
open GapCVP.SourceFormulaStructuralDecoder GapCVP.OutputPolynomialCompositionClosure
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceOriginalSourcePreservingTM
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceMixedRadixPolynomialPaddedDescriptorFoldTM
open GapCVP.CLStructuralAtomicNaturalWriter GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFEncodedClauseSort GapCVP.CNFNaturalOrderComparator
open GapCVP.CNFNaturalOrderCertifiedComparator GapCVP.CNFGuardedFiveFamilyTagDispatchTM
open GapCVP.CNFFlatAdjacentRecordSwapTM GapCVP.CNFFlatAdjacentRecordSwapTotalCert
open GapCVP.CNFFlatPhysicalBinaryAppendTM

/-- GapCVP reduction support. -/
def sourceAnchoredGridRankSourcePair (input : List Bool) : List Bool :=
  lengthPrefixedWord (firstFieldContents (firstFieldSuffix input)) ++
    firstFieldContents input

private noncomputable def sourceAnchoredGridRankSourcePairComputable :
    BitTM
      sourceAnchoredGridRankSourcePair := by
  have hrank := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    hrank structuralPrefixWriterComputable
  exact pointwiseAppendComputable hprefix firstFieldContentsComputable

/-- GapCVP reduction support. -/
def sourceAnchoredGridRawCandidate
    (candidate : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  candidate (sourceAnchoredGridRankSourcePair input)

private noncomputable def sourceAnchoredGridRawCandidateComputable
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (sourceAnchoredGridRawCandidate candidate) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    sourceAnchoredGridRankSourcePairComputable computer
  change BitTM
    (fun input => candidate (sourceAnchoredGridRankSourcePair input))
  simpa only [Function.comp_def] using hphysical

private def sourceAnchoredGridAvailableRecord (input : List Bool) : List Bool :=
  structuralAtomicNaturalWord (firstFieldContents input)

private noncomputable def sourceAnchoredGridAvailableRecordComputable :
    BitTM
      sourceAnchoredGridAvailableRecord := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable structuralAtomicNaturalWriterComputable
  change BitTM
    (fun input => structuralAtomicNaturalWord (firstFieldContents input))
  simpa only [Function.comp_def] using hphysical

private def sourceAnchoredGridRequiredRecord
    (candidate : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  structuralAtomicNaturalWord (sourceAnchoredGridRawCandidate candidate input)

private noncomputable def sourceAnchoredGridRequiredRecordComputable
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (sourceAnchoredGridRequiredRecord candidate) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (sourceAnchoredGridRawCandidateComputable computer)
    structuralAtomicNaturalWriterComputable
  change BitTM
    (fun input => structuralAtomicNaturalWord
      (sourceAnchoredGridRawCandidate candidate input))
  simpa only [Function.comp_def] using hphysical

private def sourceAnchoredGridComparisonInput
    (candidate : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  sourceAnchoredGridAvailableRecord input ++
    sourceAnchoredGridRequiredRecord candidate input

private noncomputable def sourceAnchoredGridComparisonInputComputable
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (sourceAnchoredGridComparisonInput candidate) :=
  pointwiseAppendComputable
    sourceAnchoredGridAvailableRecordComputable
    (sourceAnchoredGridRequiredRecordComputable computer)

/-- GapCVP reduction support. -/
def sourceAnchoredGridCandidateSelector
    (candidate : List Bool → List Bool)
    (input : List Bool) : Bool :=
  encodedWordOrderingFirst
    (delimitedNaturalPairOrdering
      (sourceAnchoredGridComparisonInput candidate input))

theorem sourceAnchoredGridCandidateSelector_eq
    (candidate : List Bool → List Bool)
    (input : List Bool) :
    sourceAnchoredGridCandidateSelector candidate input =
      decide ((sourceAnchoredGridRawCandidate candidate input).length ≤
        (firstFieldContents input).length) := by
  unfold sourceAnchoredGridCandidateSelector
    sourceAnchoredGridComparisonInput sourceAnchoredGridAvailableRecord
    sourceAnchoredGridRequiredRecord
  rw [structuralAtomicNaturalWord_eq_prefix,
    structuralAtomicNaturalWord_eq_prefix]
  rw [show
    lengthPrefixedWord
        (Computability.encodeNat (firstFieldContents input).length) ++
      lengthPrefixedWord
        (Computability.encodeNat
          (sourceAnchoredGridRawCandidate candidate input).length) =
      lengthPrefixedWord
        (Computability.encodeNat (firstFieldContents input).length) ++
      lengthPrefixedWord
        (Computability.encodeNat
          (sourceAnchoredGridRawCandidate candidate input).length) ++ [] by
        simp only [List.append_nil]]
  rw [delimitedNaturalPairOrdering_encodeNat]
  split <;> rename_i hfirst
  · simp only [encodedWordOrderingFirst, false_eq_decide_iff, not_le]
    omega
  · split <;> rename_i hsecond
    · simp only [encodedWordOrderingFirst, true_eq_decide_iff]
      omega
    · simp only [encodedWordOrderingFirst, true_eq_decide_iff]
      omega

private def sourceAnchoredGridCandidateMarkerWord
    (candidate : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  keepFirstDropSecondWord
    (firstFieldSuffix
      (sourcePreservingDelimitedNaturalComparisonWord
        (sourceAnchoredGridComparisonInput candidate input)))

private noncomputable def sourceAnchoredGridCandidateMarkerComputable
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (sourceAnchoredGridCandidateMarkerWord candidate) := by
  have hcomparison := GapCVP.TMComposition.computableInPolyTime
    (sourceAnchoredGridComparisonInputComputable computer)
    sourcePreservingDelimitedNaturalComparisonComputable
  have hsuffix := GapCVP.TMComposition.computableInPolyTime
    hcomparison firstFieldSuffixComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hsuffix keepFirstDropSecondComputable
  change BitTM
    (fun input => keepFirstDropSecondWord
      (firstFieldSuffix
        (sourcePreservingDelimitedNaturalComparisonWord
          (sourceAnchoredGridComparisonInput candidate input))))
  simpa only [Function.comp_def] using hphysical

@[simp] private theorem sourceAnchoredGridCandidateMarkerWord_eq
    (candidate : List Bool → List Bool)
    (input : List Bool) :
    sourceAnchoredGridCandidateMarkerWord candidate input =
      [sourceAnchoredGridCandidateSelector candidate input] := by
  simp only [sourceAnchoredGridCandidateMarkerWord, keepFirstDropSecondWord,
      sourcePreservingDelimitedNaturalComparisonWord, encodedWordOrderingWord,
          firstFieldSuffix_valid, List.tail_cons,
      sourceAnchoredGridCandidateSelector]

private def sourceAnchoredGridCandidateSelectionWord
    (candidate : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  sourceAnchoredGridCandidateSelector candidate input :: input

private noncomputable def sourceAnchoredGridCandidateSelectionComputable
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (sourceAnchoredGridCandidateSelectionWord candidate) := by
  have hpreserved := originalSourcePreservingComputable
    (sourceAnchoredGridCandidateMarkerComputable computer)
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hpreserved keepFirstDropSecondComputable
  have heq :
      (fun input => keepFirstDropSecondWord
        (originalSourcePreservingOutput
          (sourceAnchoredGridCandidateMarkerWord candidate) input)) =
        sourceAnchoredGridCandidateSelectionWord candidate := by
    funext input
    simp only [keepFirstDropSecondWord, originalSourcePreservingOutput,
        sourceAnchoredGridCandidateMarkerWord_eq,
        List.cons_append, List.nil_append, List.tail_cons,
            sourceAnchoredGridCandidateSelectionWord]
  rw [← heq]
  simpa only [Function.comp_def] using hphysical

/-- GapCVP reduction support. -/
def sourceAnchoredGridGuardedCandidate
    (candidate : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  if sourceAnchoredGridCandidateSelector candidate input
  then sourceAnchoredGridRawCandidate candidate input
  else []

private noncomputable def sourceAnchoredGridGuardedCandidateComputable
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (sourceAnchoredGridGuardedCandidate candidate) := by
  have hconditional := sourcePreservingConditionalComputable
    (sourceAnchoredGridCandidateSelectionComputable computer)
    (sourceAnchoredGridRawCandidateComputable computer) []
  change BitTM
    (fun input => if sourceAnchoredGridCandidateSelector candidate input
      then sourceAnchoredGridRawCandidate candidate input else [])
  simpa only using hconditional

private theorem sourceAnchoredGridGuardedCandidate_length_le
    (candidate : List Bool → List Bool)
    (input : List Bool) :
    (sourceAnchoredGridGuardedCandidate candidate input).length ≤
      (firstFieldContents input).length := by
  unfold sourceAnchoredGridGuardedCandidate
  split <;> rename_i hselection
  · have hbit := sourceAnchoredGridCandidateSelector_eq candidate input
    rw [hselection] at hbit
    exact of_decide_eq_true hbit.symm
  · simp only [List.length_nil, zero_le]

/-- GapCVP reduction support. -/
def sourceAnchoredGridRecordRotationOutput
    (candidate : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  firstFieldSuffix
    (flatAdjacentRecordSwapOutput input ++
      lengthPrefixedWord (sourceAnchoredGridGuardedCandidate
        candidate input))

private noncomputable def sourceAnchoredGridRecordRotationComputable
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (sourceAnchoredGridRecordRotationOutput candidate) := by
  have hrecord := GapCVP.TMComposition.computableInPolyTime
    (sourceAnchoredGridGuardedCandidateComputable computer)
    structuralPrefixWriterComputable
  have hboth := pointwiseAppendComputable
    flatAdjacentRecordSwapComputable hrecord
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hboth firstFieldSuffixComputable
  change BitTM
    (fun input => firstFieldSuffix
      (flatAdjacentRecordSwapOutput input ++
        lengthPrefixedWord
          (sourceAnchoredGridGuardedCandidate candidate input)))
  simpa only [Function.comp_apply, Function.comp_def] using hphysical

theorem sourceAnchoredGridRecordRotationOutput_records
    (candidate : List Bool → List Bool)
    (anchor rank pending : List Bool) :
    sourceAnchoredGridRecordRotationOutput candidate
        (lengthPrefixedWord anchor ++
          lengthPrefixedWord rank ++ pending) =
      lengthPrefixedWord anchor ++ pending ++
        lengthPrefixedWord
          (sourceAnchoredGridGuardedCandidate candidate
            (lengthPrefixedWord anchor ++
              lengthPrefixedWord rank ++ pending)) := by
  unfold sourceAnchoredGridRecordRotationOutput
  rw [flatAdjacentRecordSwapOutput_records anchor rank pending]
  simp only [List.append_assoc, firstFieldSuffix_valid]

private theorem sourceAnchoredGridRecordRotation_anchor_length_le
    (candidate : List Bool → List Bool)
    (input : List Bool) :
    (firstFieldContents
      (sourceAnchoredGridRecordRotationOutput
        candidate input)).length ≤
      (firstFieldContents input).length := by
  cases hfirst : readLengthPrefixedWord input with
  | none =>
      have hswap : flatAdjacentRecordSwapOutput input = [] := by
        simp only [flatAdjacentRecordSwapOutput, hfirst]
      have hdrop : firstFieldSuffix
          (lengthPrefixedWord
            (sourceAnchoredGridGuardedCandidate candidate input)) = [] := by
        simpa only [List.append_nil] using
            firstFieldSuffix_valid (sourceAnchoredGridGuardedCandidate candidate input) []
      rw [sourceAnchoredGridRecordRotationOutput, hswap,
        List.nil_append, hdrop]
      change 0 ≤ (firstFieldContents input).length
      exact Nat.zero_le _
  | some parsed =>
      obtain ⟨anchor, rest⟩ := parsed
      cases hsecond : readLengthPrefixedWord rest with
      | none =>
          have hswap : flatAdjacentRecordSwapOutput input = [] := by
            simp only [flatAdjacentRecordSwapOutput, hfirst, hsecond]
          have hdrop : firstFieldSuffix
              (lengthPrefixedWord
                (sourceAnchoredGridGuardedCandidate candidate input)) = [] := by
            simpa only [List.append_nil] using
                firstFieldSuffix_valid (sourceAnchoredGridGuardedCandidate candidate input) []
          rw [sourceAnchoredGridRecordRotationOutput, hswap,
            List.nil_append, hdrop]
          change 0 ≤ (firstFieldContents input).length
          exact Nat.zero_le _
      | some parsed =>
          obtain ⟨rank, pending⟩ := parsed
          have hinput := readLengthPrefixedWord_some_reconstruct
            input anchor rest hfirst
          have hrest := readLengthPrefixedWord_some_reconstruct
            rest rank pending hsecond
          subst rest
          subst input
          have hrotation :=
            sourceAnchoredGridRecordRotationOutput_records
              candidate anchor rank pending
          simp only [List.append_assoc] at hrotation
          rw [hrotation]
          simp only [firstFieldContents_valid, Std.le_refl]

private theorem sourceAnchoredGridRecordRotation_length_le
    (candidate : List Bool → List Bool)
    (input : List Bool) :
    (sourceAnchoredGridRecordRotationOutput
      candidate input).length ≤
      input.length + (2 * (firstFieldContents input).length + 1) := by
  have hsuffix := sourceMixedRadixPhysicalFirstFieldSuffix_length_le
    (flatAdjacentRecordSwapOutput input ++
      lengthPrefixedWord
        (sourceAnchoredGridGuardedCandidate candidate input))
  have hswap := flatAdjacentRecordSwapOutput_length_le input
  have hguard := sourceAnchoredGridGuardedCandidate_length_le
    candidate input
  simp only [List.length_append, lengthPrefixedWord_length] at hsuffix
  unfold sourceAnchoredGridRecordRotationOutput
  omega

private theorem sourceAnchoredGridRecordRotation_iterate_anchor_length_le
    (candidate : List Bool → List Bool)
    (seed : List Bool) (stage : ℕ) :
    (firstFieldContents
      (((sourceAnchoredGridRecordRotationOutput candidate)^[stage])
        seed)).length ≤ (firstFieldContents seed).length := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      exact (sourceAnchoredGridRecordRotation_anchor_length_le
        candidate _).trans ih

private theorem sourceAnchoredGridRecordRotation_iterate_length_le
    (candidate : List Bool → List Bool)
    (seed : List Bool) (stage : ℕ) :
    (((sourceAnchoredGridRecordRotationOutput
      candidate)^[stage]) seed).length ≤
      seed.length + stage * (2 * seed.length + 1) := by
  have hanchor := sourceMixedRadixPhysicalFirstFieldContents_length_le seed
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, zero_mul, add_zero, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      have hstep := sourceAnchoredGridRecordRotation_length_le
        candidate
          (((sourceAnchoredGridRecordRotationOutput
            candidate)^[stage]) seed)
      have hfixed := sourceAnchoredGridRecordRotation_iterate_anchor_length_le
        candidate seed stage
      calc
        (sourceAnchoredGridRecordRotationOutput candidate
          (((sourceAnchoredGridRecordRotationOutput
            candidate)^[stage]) seed)).length
            ≤ (((sourceAnchoredGridRecordRotationOutput
              candidate)^[stage]) seed).length +
                (2 * (firstFieldContents
                  (((sourceAnchoredGridRecordRotationOutput
                    candidate)^[stage]) seed)).length + 1) := hstep
        _ ≤ seed.length + stage * (2 * seed.length + 1) +
              (2 * seed.length + 1) := by omega
        _ = seed.length + (stage + 1) *
              (2 * seed.length + 1) := by
                simp only [Nat.succ_mul, one_mul, Nat.add_assoc]

private def sourceAnchoredGridRecordStatePolynomial : Polynomial ℕ :=
  Polynomial.X + Polynomial.X *
    (2 * Polynomial.X + 1)

private theorem sourceAnchoredGridRecord_polynomiallyBoundedFoldStates
    (candidate : List Bool → List Bool) :
    PolynomiallyBoundedFoldStates
      (sourceAnchoredGridRecordRotationOutput candidate)
      sourceAnchoredGridRecordStatePolynomial := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage hstage
  have hseed := GapCVP.CNFTypedRecordWorkerTM.parsedUnaryFold_seed_length_le
    input count seed hparse
  have hcount := parsedUnaryFold_count_le_length
    input count seed hparse
  have hiterate := sourceAnchoredGridRecordRotation_iterate_length_le
    candidate seed stage
  simp only [sourceAnchoredGridRecordStatePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  have hstageInput : stage ≤ input.length := hstage.trans hcount
  have hfactor : 2 * seed.length + 1 ≤ 2 * input.length + 1 := by
    omega
  have hmul : stage * (2 * seed.length + 1) ≤
      input.length * (2 * input.length + 1) :=
    Nat.mul_le_mul hstageInput hfactor
  omega

/-- GapCVP reduction support. -/
noncomputable def sourceAnchoredGridRecordFoldComputable
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (boundedRecordFoldOutput
        (sourceAnchoredGridRecordRotationOutput candidate)) :=
  boundedDependentRecordFoldComputable
    (sourceAnchoredGridRecordRotationComputable computer)
    sourceAnchoredGridRecordStatePolynomial
    (sourceAnchoredGridRecord_polynomiallyBoundedFoldStates candidate)

private theorem sourceAnchoredGridGuardedCandidate_records
    (candidate : List Bool → List Bool)
    (anchor rank pending : List Bool)
    (hfit : (candidate
      (lengthPrefixedWord rank ++ anchor)).length ≤ anchor.length) :
    sourceAnchoredGridGuardedCandidate candidate
        (lengthPrefixedWord anchor ++
          lengthPrefixedWord rank ++ pending) =
      candidate (lengthPrefixedWord rank ++ anchor) := by
  unfold sourceAnchoredGridGuardedCandidate
  have hselector : sourceAnchoredGridCandidateSelector candidate
      (lengthPrefixedWord anchor ++
        lengthPrefixedWord rank ++ pending) = true := by
    rw [sourceAnchoredGridCandidateSelector_eq]
    simp only [sourceAnchoredGridRawCandidate, sourceAnchoredGridRankSourcePair, List.append_assoc,
        firstFieldSuffix_valid, firstFieldContents_valid, hfit, decide_true]
  rw [hselector]
  simp only [↓reduceIte, sourceAnchoredGridRawCandidate, sourceAnchoredGridRankSourcePair,
      List.append_assoc,
      firstFieldSuffix_valid, firstFieldContents_valid]

private theorem sourceAnchoredGridRecordRotation_iterate_ranks
    (candidate : List Bool → List Bool)
    (anchor : List Bool) (ranks : List (List Bool))
    (suffix : List Bool)
    (hfit : ∀ rank ∈ ranks,
      (candidate (lengthPrefixedWord rank ++ anchor)).length ≤
        anchor.length) :
    ((sourceAnchoredGridRecordRotationOutput candidate)^[ranks.length])
      (lengthPrefixedWord anchor ++
        ranks.flatMap lengthPrefixedWord ++ suffix) =
      lengthPrefixedWord anchor ++ suffix ++
        ranks.flatMap
          (fun rank => lengthPrefixedWord
            (candidate (lengthPrefixedWord rank ++ anchor))) := by
  induction ranks generalizing suffix with
  | nil =>
      simp only [List.length_nil, List.flatMap_nil, List.append_nil, Function.iterate_zero, id_eq]
  | cons rank remaining ih =>
      have hhead :
          (candidate (lengthPrefixedWord rank ++ anchor)).length ≤
            anchor.length := hfit rank (by simp only [List.mem_cons, true_or])
      have htail : ∀ item ∈ remaining,
          (candidate (lengthPrefixedWord item ++ anchor)).length ≤
            anchor.length := by
        intro item hitem
        exact hfit item (by simp only [List.mem_cons, hitem, or_true])
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [List.flatMap_cons, List.append_assoc]
      have hrotation := sourceAnchoredGridRecordRotationOutput_records
        candidate anchor rank
          (remaining.flatMap lengthPrefixedWord ++ suffix)
      simp only [List.append_assoc] at hrotation
      rw [hrotation]
      have hguard := sourceAnchoredGridGuardedCandidate_records
        candidate anchor rank
          (remaining.flatMap lengthPrefixedWord ++ suffix) hhead
      simp only [List.append_assoc] at hguard
      rw [hguard]
      simpa only [List.append_assoc] using
          ih (suffix ++ lengthPrefixedWord (candidate (lengthPrefixedWord rank ++ anchor))) htail

theorem boundedRecordFoldOutput_sourceAnchoredGridRecordRanks
    (candidate : List Bool → List Bool)
    (anchor : List Bool) (ranks : List (List Bool))
    (suffix : List Bool)
    (hfit : ∀ rank ∈ ranks,
      (candidate (lengthPrefixedWord rank ++ anchor)).length ≤
        anchor.length) :
    boundedRecordFoldOutput
      (sourceAnchoredGridRecordRotationOutput candidate)
      (unaryBoundedFoldWord ranks.length
        (lengthPrefixedWord anchor ++
          ranks.flatMap lengthPrefixedWord ++ suffix)) =
      lengthPrefixedWord anchor ++ suffix ++
        ranks.flatMap
          (fun rank => lengthPrefixedWord
            (candidate (lengthPrefixedWord rank ++ anchor))) := by
  simp only [boundedRecordFoldOutput,
    parseUnaryBoundedFold_word]
  exact sourceAnchoredGridRecordRotation_iterate_ranks
    candidate anchor ranks suffix hfit

end SourceAnchoredGridRecordFoldTM

namespace CNFFiveFamilyFlatIndexedCatalogueTM

open Computability Turing GapCVP.CLNondeterminism GapCVP.CLCompleteVerifierSimulation
open GapCVP.BinaryEncoding GapCVP.CLStructuralPrefixWriter GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFiveFamilyFlatCandidateGenerationTM

/-- GapCVP reduction support. -/
def fiveFlatOriginalSourceAnchorWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord input ++
    List.replicate
      ((flatSourceAnnotatedClauseLengthPolynomial
        (nondeterministicTableauDimensionPolynomial bound machine)
        (completePhaseSymbolCount machine.tm)).eval input.length) true

/-- GapCVP reduction support. -/
noncomputable def fiveFamilyFlatOriginalSourceAnchorComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveFlatOriginalSourceAnchorWord bound machine) := by
  exact pointwiseAppendComputable
    structuralPrefixWriterComputable
    (polynomialValueUnaryComputable
      (flatSourceAnnotatedClauseLengthPolynomial
        (nondeterministicTableauDimensionPolynomial bound machine)
        (completePhaseSymbolCount machine.tm)))

end CNFFiveFamilyFlatIndexedCatalogueTM

namespace CNFFiveFamilyFlatIndexedRankArithmeticTM

open Computability Turing GapCVP.CLNondeterminism GapCVP.CLCellRowBounds GapCVP.BinaryEncoding
open GapCVP.SourceMachineCert GapCVP.SourceUniformTuringTM GapCVP.SourceStructuralTuringTM
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFUnaryPairIndexTM
open GapCVP.CNFUnaryPairIndexTotalRuntimeCert GapCVP.CNFCappedUnaryPairArithmeticTM
open GapCVP.SourceMixedRadixUnaryQuotientRemainderTM

/-- GapCVP reduction support. -/
def fiveFamilyFlatIndexedPhysicalRank (input : List Bool) : List Bool :=
  firstFieldContents input

/-- GapCVP reduction support. -/
noncomputable def fiveFlatIndexedPhysicalRankComputable :
    BitTM
      fiveFamilyFlatIndexedPhysicalRank :=
  firstFieldContentsComputable

/-- GapCVP reduction support. -/
def fiveFlatIndexedPhysicalOriginal (input : List Bool) : List Bool :=
  firstFieldContents (firstFieldSuffix input)

/-- GapCVP reduction support. -/
noncomputable def fiveFamilyFlatIndexedPhysicalOriginalComputable :
    BitTM
      fiveFlatIndexedPhysicalOriginal := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable
  change BitTM
    (fun input => firstFieldContents (firstFieldSuffix input))
  simpa only [Function.comp_def] using physical

theorem fiveFamilyFlatIndexedPhysicalRank_valid
    (rank : ℕ) (original suffix : List Bool) :
    fiveFamilyFlatIndexedPhysicalRank
      (lengthPrefixedWord (List.replicate rank true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate rank true := by
  simp only [fiveFamilyFlatIndexedPhysicalRank, List.append_assoc, firstFieldContents_valid]

theorem fiveFamilyFlatIndexedPhysicalOriginal_valid
    (rank : ℕ) (original suffix : List Bool) :
    fiveFlatIndexedPhysicalOriginal
      (lengthPrefixedWord (List.replicate rank true) ++
        lengthPrefixedWord original ++ suffix) = original := by
  simp only [fiveFlatIndexedPhysicalOriginal, List.append_assoc, firstFieldSuffix_valid,
      firstFieldContents_valid]

/-- GapCVP reduction support. -/
def fiveFlatIndexedOriginalPolynomialUnary
    (polynomial : Polynomial ℕ) (input : List Bool) : List Bool :=
  List.replicate
    (polynomial.eval
      (fiveFlatIndexedPhysicalOriginal input).length) true

/-- GapCVP reduction support. -/
noncomputable def fiveFlatIndexedOriginalPolynomialUnaryComputable
    (polynomial : Polynomial ℕ) :
    BitTM
      (fiveFlatIndexedOriginalPolynomialUnary polynomial) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    fiveFamilyFlatIndexedPhysicalOriginalComputable
    (polynomialValueUnaryComputable polynomial)
  change BitTM
    (fun input => List.replicate
      (polynomial.eval
        (fiveFlatIndexedPhysicalOriginal input).length) true)
  simpa only [Function.comp_def] using physical

theorem fiveFamilyFlatIndexedOriginalPolynomialUnary_valid
    (polynomial : Polynomial ℕ)
    (rank : ℕ) (original suffix : List Bool) :
    fiveFlatIndexedOriginalPolynomialUnary polynomial
      (lengthPrefixedWord (List.replicate rank true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate (polynomial.eval original.length) true := by
  simp only [fiveFlatIndexedOriginalPolynomialUnary, fiveFlatIndexedPhysicalOriginal,
      List.append_assoc,
      firstFieldSuffix_valid, firstFieldContents_valid]

/-- GapCVP reduction support. -/
def fiveFamilyFlatIndexedGridPolynomial
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    Polynomial ℕ :=
  nondeterministicTableauDimensionPolynomial bound machine + 1

@[simp] theorem fiveFamilyFlatIndexedGridPolynomial_eval
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    (fiveFamilyFlatIndexedGridPolynomial bound machine).eval
      original.length = rowWidth bound machine original + 1 := by
  simp only [fiveFamilyFlatIndexedGridPolynomial, Polynomial.eval_add, Polynomial.eval_one,
      rowWidth]

private def fiveFlatIndexedOriginalDivisionQuery
    (polynomial : Polynomial ℕ) (input : List Bool) : List Bool :=
  fiveFamilyFlatIndexedPhysicalRank input ++ false ::
    (fiveFlatIndexedOriginalPolynomialUnary polynomial input ++
      false :: fiveFlatIndexedPhysicalOriginal input)

private noncomputable def fiveFamilyFlatIndexedOriginalDivisionQueryComputable
    (polynomial : Polynomial ℕ) :
    BitTM
      (fiveFlatIndexedOriginalDivisionQuery polynomial) := by
  have sourceDelimiter :=
    GapCVP.TMComposition.computableInPolyTime
      fiveFamilyFlatIndexedPhysicalOriginalComputable
      (prependBitComputable false)
  have modulusAndSource := pointwiseAppendComputable
    (fiveFlatIndexedOriginalPolynomialUnaryComputable polynomial)
    sourceDelimiter
  have modulusDelimiter :=
    GapCVP.TMComposition.computableInPolyTime
      modulusAndSource (prependBitComputable false)
  have physical := pointwiseAppendComputable
    fiveFlatIndexedPhysicalRankComputable modulusDelimiter
  change BitTM
    (fun input =>
      fiveFamilyFlatIndexedPhysicalRank input ++ false ::
        (fiveFlatIndexedOriginalPolynomialUnary polynomial input ++
          false :: fiveFlatIndexedPhysicalOriginal input))
  simpa only [Function.comp_apply] using physical

private theorem fiveFamilyFlatIndexedOriginalDivisionQuery_valid
    (polynomial : Polynomial ℕ)
    (rank : ℕ) (original suffix : List Bool) :
    fiveFlatIndexedOriginalDivisionQuery polynomial
      (lengthPrefixedWord (List.replicate rank true) ++
        lengthPrefixedWord original ++ suffix) =
      sourceUnaryDivisionQuery rank
        (polynomial.eval original.length) original := by
  simp only [fiveFlatIndexedOriginalDivisionQuery, fiveFamilyFlatIndexedPhysicalRank,
      List.append_assoc,
      firstFieldContents_valid, fiveFlatIndexedOriginalPolynomialUnary,
          fiveFlatIndexedPhysicalOriginal,
      firstFieldSuffix_valid, sourceUnaryDivisionQuery]

private def fiveFlatIndexedOriginalDivisionOutput
    (polynomial : Polynomial ℕ) (input : List Bool) : List Bool :=
  sourceUnaryDivisionOutput
    (fiveFlatIndexedOriginalDivisionQuery polynomial input)

private noncomputable def fiveFamilyFlatIndexedOriginalDivisionComputable
    (polynomial : Polynomial ℕ) :
    BitTM
      (fiveFlatIndexedOriginalDivisionOutput polynomial) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatIndexedOriginalDivisionQueryComputable polynomial)
    sourceUnaryDivisionComputable
  change BitTM
    (fun input => sourceUnaryDivisionOutput
      (fiveFlatIndexedOriginalDivisionQuery polynomial input))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyFlatIndexedOriginalDivisionOutput_valid
    (polynomial : Polynomial ℕ)
    (rank : ℕ) (original suffix : List Bool)
    (hpositive : 0 < polynomial.eval original.length) :
    fiveFlatIndexedOriginalDivisionOutput polynomial
      (lengthPrefixedWord (List.replicate rank true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate (rank / polynomial.eval original.length) true ++
        false ::
          (List.replicate (rank % polynomial.eval original.length) true ++
            false :: sourceUnaryDivisionQuery rank
              (polynomial.eval original.length) original) := by
  unfold fiveFlatIndexedOriginalDivisionOutput
  rw [fiveFamilyFlatIndexedOriginalDivisionQuery_valid]
  exact sourceUnaryDivisionOutput_valid
    rank (polynomial.eval original.length) original hpositive

/-- GapCVP reduction support. -/
def fiveFlatIndexedOriginalQuotientUnary
    (polynomial : Polynomial ℕ) (input : List Bool) : List Bool :=
  (unaryPrefixOutput
    (fiveFlatIndexedOriginalDivisionOutput polynomial input)).tail

/-- GapCVP reduction support. -/
noncomputable def fiveFamilyFlatIndexedOriginalQuotientUnaryComputable
    (polynomial : Polynomial ℕ) :
    BitTM
      (fiveFlatIndexedOriginalQuotientUnary polynomial) := by
  have scanned := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatIndexedOriginalDivisionComputable polynomial)
    unaryPrefixComputable
  have physical := GapCVP.TMComposition.computableInPolyTime
    scanned dropHeadComputable
  change BitTM
    (fun input => (unaryPrefixOutput
      (fiveFlatIndexedOriginalDivisionOutput
        polynomial input)).tail)
  simpa only [Function.comp_def] using physical

/-- GapCVP reduction support. -/
def fiveFlatIndexedOriginalRemainderUnary
    (polynomial : Polynomial ℕ) (input : List Bool) : List Bool :=
  (unaryPrefixOutput
    (unaryPrefixSuffixOutput
      (fiveFlatIndexedOriginalDivisionOutput
        polynomial input))).tail

/-- GapCVP reduction support. -/
noncomputable def fiveFamilyFlatIndexedOriginalRemainderUnaryComputable
    (polynomial : Polynomial ℕ) :
    BitTM
      (fiveFlatIndexedOriginalRemainderUnary polynomial) := by
  have suffix := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatIndexedOriginalDivisionComputable polynomial)
    actualUnaryPrefixSuffixComputable
  have scanned := GapCVP.TMComposition.computableInPolyTime
    suffix unaryPrefixComputable
  have physical := GapCVP.TMComposition.computableInPolyTime
    scanned dropHeadComputable
  change BitTM
    (fun input => (unaryPrefixOutput
      (unaryPrefixSuffixOutput
        (fiveFlatIndexedOriginalDivisionOutput
          polynomial input))).tail)
  simpa only [Function.comp_def] using physical

theorem fiveFamilyFlatIndexedOriginalQuotientUnary_valid
    (polynomial : Polynomial ℕ)
    (rank : ℕ) (original suffix : List Bool)
    (hpositive : 0 < polynomial.eval original.length) :
    fiveFlatIndexedOriginalQuotientUnary polynomial
      (lengthPrefixedWord (List.replicate rank true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate (rank / polynomial.eval original.length) true := by
  unfold fiveFlatIndexedOriginalQuotientUnary
  rw [fiveFamilyFlatIndexedOriginalDivisionOutput_valid
    polynomial rank original suffix hpositive,
    unaryPrefixOutput_replicate_delimiter]
  rfl

theorem fiveFamilyFlatIndexedOriginalRemainderUnary_valid
    (polynomial : Polynomial ℕ)
    (rank : ℕ) (original suffix : List Bool)
    (hpositive : 0 < polynomial.eval original.length) :
    fiveFlatIndexedOriginalRemainderUnary polynomial
      (lengthPrefixedWord (List.replicate rank true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate (rank % polynomial.eval original.length) true := by
  unfold fiveFlatIndexedOriginalRemainderUnary
  rw [fiveFamilyFlatIndexedOriginalDivisionOutput_valid
    polynomial rank original suffix hpositive,
    unaryPrefixSuffixOutput_valid,
    unaryPrefixOutput_replicate_delimiter]
  rfl

private def fiveFlatIndexedPositionSymbolPairInput
    (polynomial : Polynomial ℕ) (symbol : ℕ)
    (input : List Bool) : List Bool :=
  fiveFlatIndexedOriginalRemainderUnary polynomial input ++
    false :: (List.replicate symbol true ++ [false])

private noncomputable def fiveFamilyFlatIndexedPositionSymbolPairInputComputable
    (polynomial : Polynomial ℕ) (symbol : ℕ) :
    BitTM
      (fiveFlatIndexedPositionSymbolPairInput
        polynomial symbol) := by
  have physical := pointwiseAppendComputable
    (fiveFamilyFlatIndexedOriginalRemainderUnaryComputable polynomial)
    (constantWordComputable
      (false :: (List.replicate symbol true ++ [false])))
  change BitTM
    (fun input =>
      fiveFlatIndexedOriginalRemainderUnary polynomial input ++
        false :: (List.replicate symbol true ++ [false]))
  exact physical

private def fiveFlatIndexedPositionSymbolCode
    (polynomial : Polynomial ℕ) (symbol : ℕ)
    (input : List Bool) : List Bool :=
  unarySourcePairOutput
    (fiveFlatIndexedPositionSymbolPairInput
      polynomial symbol input)

private noncomputable def fiveFamilyFlatIndexedPositionSymbolCodeComputable
    (polynomial : Polynomial ℕ) (symbol : ℕ) :
    BitTM
      (fiveFlatIndexedPositionSymbolCode polynomial symbol) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatIndexedPositionSymbolPairInputComputable
      polynomial symbol)
    actualUnaryPairIndexComputable
  change BitTM
    (fun input => unarySourcePairOutput
      (fiveFlatIndexedPositionSymbolPairInput
        polynomial symbol input))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyFlatIndexedPositionSymbolCode_valid
    (polynomial : Polynomial ℕ) (symbol rank : ℕ)
    (original suffix : List Bool)
    (hpositive : 0 < polynomial.eval original.length) :
    fiveFlatIndexedPositionSymbolCode polynomial symbol
      (lengthPrefixedWord (List.replicate rank true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate
        (Nat.pair (rank % polynomial.eval original.length) symbol)
        true := by
  unfold fiveFlatIndexedPositionSymbolCode
    fiveFlatIndexedPositionSymbolPairInput
  rw [fiveFamilyFlatIndexedOriginalRemainderUnary_valid
    polynomial rank original suffix hpositive]
  change unarySourcePairOutput
    (unarySourcePairWord
      (rank % polynomial.eval original.length) symbol) = _
  exact unarySourcePairOutput_word
    (rank % polynomial.eval original.length) symbol

private def fiveFlatIndexedVariablePairInput
    (polynomial : Polynomial ℕ) (symbol : ℕ)
    (input : List Bool) : List Bool :=
  fiveFlatIndexedOriginalQuotientUnary polynomial input ++
    false :: (fiveFlatIndexedPositionSymbolCode
      polynomial symbol input ++ [false])

private noncomputable def fiveFamilyFlatIndexedVariablePairInputComputable
    (polynomial : Polynomial ℕ) (symbol : ℕ) :
    BitTM
      (fiveFlatIndexedVariablePairInput polynomial symbol) := by
  have inner := pointwiseAppendComputable
    (fiveFamilyFlatIndexedPositionSymbolCodeComputable
      polynomial symbol)
    (constantWordComputable [false])
  have delimiter := GapCVP.TMComposition.computableInPolyTime
    inner (prependBitComputable false)
  have physical := pointwiseAppendComputable
    (fiveFamilyFlatIndexedOriginalQuotientUnaryComputable polynomial)
    delimiter
  change BitTM
    (fun input =>
      fiveFlatIndexedOriginalQuotientUnary polynomial input ++
        false :: (fiveFlatIndexedPositionSymbolCode
          polynomial symbol input ++ [false]))
  simpa only [Function.comp_apply] using physical

/-- GapCVP reduction support. -/
def fiveFamilyFlatIndexedVariableCode
    (polynomial : Polynomial ℕ) (symbol : ℕ)
    (input : List Bool) : List Bool :=
  unarySourcePairOutput
    (fiveFlatIndexedVariablePairInput polynomial symbol input)

private noncomputable def fiveFamilyFlatIndexedVariableCodeComputable
    (polynomial : Polynomial ℕ) (symbol : ℕ) :
    BitTM
      (fiveFamilyFlatIndexedVariableCode polynomial symbol) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatIndexedVariablePairInputComputable
      polynomial symbol)
    actualUnaryPairIndexComputable
  change BitTM
    (fun input => unarySourcePairOutput
      (fiveFlatIndexedVariablePairInput
        polynomial symbol input))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyFlatIndexedVariableCode_valid
    (polynomial : Polynomial ℕ) (symbol rank : ℕ)
    (original suffix : List Bool)
    (hpositive : 0 < polynomial.eval original.length) :
    fiveFamilyFlatIndexedVariableCode polynomial symbol
      (lengthPrefixedWord (List.replicate rank true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate
        (Nat.pair
          (rank / polynomial.eval original.length)
          (Nat.pair (rank % polynomial.eval original.length) symbol))
        true := by
  unfold fiveFamilyFlatIndexedVariableCode
    fiveFlatIndexedVariablePairInput
  rw [fiveFamilyFlatIndexedOriginalQuotientUnary_valid
    polynomial rank original suffix hpositive,
    fiveFamilyFlatIndexedPositionSymbolCode_valid
      polynomial symbol rank original suffix hpositive]
  change unarySourcePairOutput
    (unarySourcePairWord
      (rank / polynomial.eval original.length)
      (Nat.pair (rank % polynomial.eval original.length) symbol)) = _
  exact unarySourcePairOutput_word
    (rank / polynomial.eval original.length)
    (Nat.pair (rank % polynomial.eval original.length) symbol)

theorem fiveFamilyFlatIndexedGridQuotient_lt
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) (rank : ℕ)
    (hrank : rank < (rowWidth bound machine original + 1) ^ 2) :
    rank / (rowWidth bound machine original + 1) <
      rowWidth bound machine original + 1 := by
  apply (Nat.div_lt_iff_lt_mul (by omega)).2
  simpa only [pow_two] using hrank

theorem fiveFamilyFlatIndexedGridRemainder_lt
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) (rank : ℕ) :
    rank % (rowWidth bound machine original + 1) <
      rowWidth bound machine original + 1 := by
  apply Nat.mod_lt
  omega

end CNFFiveFamilyFlatIndexedRankArithmeticTM

namespace CNFFiveFamilyFlatRowMajorCatalogueTM

open Computability Turing GapCVP.CL GapCVP.CNFDependentFiveFamilyRecordTM
open GapCVP.CNFBoundedRecordFoldTM

private def fiveFamilyRowMajorFinitePairs (first second : ℕ) :
    List (Fin first × Fin second) :=
  (List.finRange first).flatMap fun row =>
    (List.finRange second).map fun column => (row, column)

@[simp] private theorem mem_fiveFamilyRowMajorFinitePairs
    (first second : ℕ) (row : Fin first) (column : Fin second) :
    (row, column) ∈ fiveFamilyRowMajorFinitePairs first second := by
  simp only [fiveFamilyRowMajorFinitePairs, List.mem_flatMap, List.mem_finRange, List.mem_map,
      Prod.mk.injEq,
      true_and, exists_eq_right, exists_eq]

@[simp] private theorem fiveFamilyRowMajorFinitePairs_length
    (first second : ℕ) :
    (fiveFamilyRowMajorFinitePairs first second).length =
      first * second := by
  simp only [fiveFamilyRowMajorFinitePairs, List.length_flatMap, List.length_map,
      List.length_finRange,
      List.map_const', List.sum_replicate, smul_eq_mul]

/-- GapCVP reduction support. -/
def fiveFamilyRowMajorTimePositionSlots (T : ℕ) :
    List (Time T × Position T) :=
  fiveFamilyRowMajorFinitePairs (T + 1) (T + 1)

@[simp] theorem mem_fiveFamilyRowMajorTimePositionSlots
    {T : ℕ} (time : Time T) (position : Position T) :
    (time, position) ∈ fiveFamilyRowMajorTimePositionSlots T := by
  exact mem_fiveFamilyRowMajorFinitePairs
    (T + 1) (T + 1) time position

/-- GapCVP reduction support. -/
def fiveFamilyRowMajorSymbolPairs (S : ℕ) :
    List (Symbol S × Symbol S) :=
  fiveFamilyRowMajorFinitePairs (S + 1) (S + 1)

@[simp] private theorem mem_fiveFamilyRowMajorSymbolPairs
    {S : ℕ} (first second : Symbol S) :
    (first, second) ∈ fiveFamilyRowMajorSymbolPairs S := by
  exact mem_fiveFamilyRowMajorFinitePairs
    (S + 1) (S + 1) first second

@[simp] theorem fiveFamilyRowMajorSymbolPairs_length (S : ℕ) :
    (fiveFamilyRowMajorSymbolPairs S).length = (S + 1) ^ 2 := by
  simp only [fiveFamilyRowMajorSymbolPairs, fiveFamilyRowMajorFinitePairs_length, pow_two]

/-- GapCVP reduction support. -/
def fiveFamilyRowMajorWindowSymbols (S : ℕ) :
    List (WindowSymbols S) :=
  (List.finRange (S + 1)).flatMap fun first =>
    (List.finRange (S + 1)).flatMap fun second =>
      (List.finRange (S + 1)).flatMap fun third =>
        (List.finRange (S + 1)).map fun fourth =>
          (first, second, third, fourth)

@[simp] private theorem mem_fiveFamilyRowMajorWindowSymbols
    {S : ℕ} (symbols : WindowSymbols S) :
    symbols ∈ fiveFamilyRowMajorWindowSymbols S := by
  rcases symbols with ⟨first, second, third, fourth⟩
  simp only [fiveFamilyRowMajorWindowSymbols, List.mem_flatMap, List.mem_finRange, List.mem_map,
    Prod.mk.injEq, true_and, exists_and_left, ↓existsAndEq, and_true, exists_eq]

@[simp] theorem fiveFamilyRowMajorWindowSymbols_length (S : ℕ) :
    (fiveFamilyRowMajorWindowSymbols S).length = (S + 1) ^ 4 := by
  simp only [fiveFamilyRowMajorWindowSymbols, List.length_flatMap, List.length_map,
      List.length_finRange,
      List.map_const', List.sum_replicate, smul_eq_mul]
  ring

/-- GapCVP reduction support. -/
def fiveFamilyRowMajorWindows (T : ℕ) : List (Window T) :=
  (List.finRange T).flatMap fun time =>
    (List.finRange (T + 1)).map fun position =>
      windowAt time position

@[simp] theorem mem_fiveFamilyRowMajorWindows
    {T : ℕ} (window : Window T) :
    window ∈ fiveFamilyRowMajorWindows T := by
  let index := actualWindowIndexEquiv T window
  have reconstruct : windowAt index.1 index.2 = window :=
    (actualWindowIndexEquiv T).left_inv window
  unfold fiveFamilyRowMajorWindows
  apply List.mem_flatMap.mpr
  refine ⟨index.1, by simp only [List.mem_finRange], ?_⟩
  apply List.mem_map.mpr
  exact ⟨index.2, by simp only [List.mem_finRange], reconstruct⟩

/-- GapCVP reduction support. -/
def fiveFamilyRowMajorAtLeastClauses (T S : ℕ) :
    List (Clause T S) :=
  (fiveFamilyRowMajorTimePositionSlots T).map fun position =>
    atLeastOneClause (S := S) position.1 position.2

/-- GapCVP reduction support. -/
def fiveFamilyRowMajorAtMostClauses (T S : ℕ) :
    List (Clause T S) :=
  (fiveFamilyRowMajorTimePositionSlots T).flatMap fun position =>
    (fiveFamilyRowMajorSymbolPairs S).map fun symbols =>
      if symbols.1 < symbols.2 then
        atMostOneClause position.1 position.2 symbols.1 symbols.2
      else
        atLeastOneClause position.1 position.2

/-- GapCVP reduction support. -/
def fiveFamilyRowMajorInitialClauses {T S : ℕ}
    (specification : Specification T S) : List (Clause T S) :=
  (List.finRange (T + 1)).map
    (initialClause specification.input)

/-- GapCVP reduction support. -/
def fiveFamilyRowMajorAcceptanceClauses {T S : ℕ}
    (specification : Specification T S) : List (Clause T S) :=
  [acceptanceClause specification.accept]

/-- GapCVP reduction support. -/
def fiveFamilyRowMajorForbiddenClauses {T S : ℕ}
    (specification : Specification T S) : List (Clause T S) :=
  (fiveFamilyRowMajorWindows T).flatMap fun window =>
    (fiveFamilyRowMajorWindowSymbols S).map fun symbols =>
      if specification.allowed symbols = false then
        transitionClause window symbols
      else
        atLeastOneClause window.1.1 window.1.2

/-- GapCVP reduction support. -/
def fiveFamilyRowMajorSourceClauses {T S : ℕ}
    (specification : Specification T S) : List (Clause T S) :=
  fiveFamilyRowMajorAtLeastClauses T S ++
    fiveFamilyRowMajorAtMostClauses T S ++
    fiveFamilyRowMajorInitialClauses specification ++
    fiveFamilyRowMajorAcceptanceClauses specification ++
    fiveFamilyRowMajorForbiddenClauses specification

private theorem fiveFamilyRowMajorAtLeast_mem_tableauFormula
    {T S : ℕ} (specification : Specification T S)
    (clause : Clause T S)
    (hclause : clause ∈ fiveFamilyRowMajorAtLeastClauses T S) :
    clause ∈ tableauFormula specification := by
  obtain ⟨position, _, rfl⟩ := List.mem_map.mp hclause
  exact atLeastOneClause_mem_tableauFormula
    specification position.1 position.2

private theorem fiveFamilyRowMajorAtMost_mem_tableauFormula
    {T S : ℕ} (specification : Specification T S)
    (clause : Clause T S)
    (hclause : clause ∈ fiveFamilyRowMajorAtMostClauses T S) :
    clause ∈ tableauFormula specification := by
  obtain ⟨position, _, hslot⟩ := List.mem_flatMap.mp hclause
  obtain ⟨symbols, _, hvalue⟩ := List.mem_map.mp hslot
  by_cases hvalid : symbols.1 < symbols.2
  · simp only [hvalid, ↓reduceIte] at hvalue
    subst clause
    exact atMostOneClause_mem_tableauFormula specification
      position.1 position.2 symbols.1 symbols.2 hvalid
  · simp only [hvalid, ↓reduceIte] at hvalue
    subst clause
    exact atLeastOneClause_mem_tableauFormula specification
      position.1 position.2

private theorem fiveFamilyRowMajorForbidden_mem_tableauFormula
    {T S : ℕ} (specification : Specification T S)
    (clause : Clause T S)
    (hclause : clause ∈
      fiveFamilyRowMajorForbiddenClauses specification) :
    clause ∈ tableauFormula specification := by
  obtain ⟨window, _, hslot⟩ := List.mem_flatMap.mp hclause
  obtain ⟨symbols, _, hvalue⟩ := List.mem_map.mp hslot
  by_cases hvalid : specification.allowed symbols = false
  · simp only [hvalid, ↓reduceIte] at hvalue
    subst clause
    exact transitionClause_mem_tableauFormula
      specification window symbols hvalid
  · simp only [hvalid, Bool.true_eq_false, ↓reduceIte] at hvalue
    subst clause
    exact atLeastOneClause_mem_tableauFormula
      specification window.1.1 window.1.2

theorem fiveFamilyRowMajorSourceClauses_toFinset
    {T S : ℕ} (specification : Specification T S) :
    (fiveFamilyRowMajorSourceClauses specification).toFinset =
      tableauFormula specification := by
  ext clause
  simp only [List.mem_toFinset]
  constructor
  · intro hclause
    simp only [fiveFamilyRowMajorSourceClauses,
      List.mem_append] at hclause
    rcases hclause with hremaining | hforbidden
    · rcases hremaining with hremaining | haccept
      · rcases hremaining with hremaining | hinitial
        · rcases hremaining with hleast | hmost
          · exact fiveFamilyRowMajorAtLeast_mem_tableauFormula
              specification clause hleast
          · exact fiveFamilyRowMajorAtMost_mem_tableauFormula
              specification clause hmost
        · obtain ⟨position, _, rfl⟩ := List.mem_map.mp hinitial
          exact initialClause_mem_tableauFormula
            specification position
      · have haccept' : clause =
            acceptanceClause specification.accept := by
          simpa only [fiveFamilyRowMajorAcceptanceClauses, List.mem_cons, List.not_mem_nil,
              or_false] using haccept
        subst clause
        exact acceptanceClause_mem_tableauFormula specification
    · exact fiveFamilyRowMajorForbidden_mem_tableauFormula
        specification clause hforbidden
  · intro hclause
    have htotalFinset : clause ∈
        (totalFiveFamilySourceClauseCandidates
          specification).toFinset := by
      rw [totalFiveFamilySourceClauseCandidates_toFinset]
      exact hclause
    have htotal : clause ∈
        totalFiveFamilySourceClauseCandidates specification := by
      simpa only [List.mem_toFinset] using htotalFinset
    simp only [totalFiveFamilySourceClauseCandidates,
      List.mem_append] at htotal
    simp only [fiveFamilyRowMajorSourceClauses, List.mem_append]
    rcases htotal with hremaining | hforbidden
    · rcases hremaining with hremaining | haccept
      · rcases hremaining with hremaining | hinitial
        · rcases hremaining with hleast | hmost
          · left
            left
            left
            left
            obtain ⟨position, _, hvalue⟩ := List.mem_map.mp hleast
            apply List.mem_map.mpr
            exact ⟨position,
              mem_fiveFamilyRowMajorTimePositionSlots
                position.1 position.2, hvalue⟩
          · left
            left
            left
            right
            obtain ⟨candidate, _, hvalue⟩ := List.mem_map.mp hmost
            apply List.mem_flatMap.mpr
            refine ⟨candidate.1,
              mem_fiveFamilyRowMajorTimePositionSlots
                candidate.1.1 candidate.1.2, ?_⟩
            apply List.mem_map.mpr
            exact ⟨candidate.2,
              mem_fiveFamilyRowMajorSymbolPairs
                candidate.2.1 candidate.2.2, hvalue⟩
        · left
          left
          right
          obtain ⟨position, _, hvalue⟩ := List.mem_map.mp hinitial
          apply List.mem_map.mpr
          exact ⟨position, by simp only [List.mem_finRange], hvalue⟩
      · left
        right
        simpa only [fiveFamilyRowMajorAcceptanceClauses, List.mem_cons, List.not_mem_nil, or_false,
            executableAcceptanceFamilyClauses] using haccept
    · right
      obtain ⟨candidate, _, hvalue⟩ := List.mem_map.mp hforbidden
      apply List.mem_flatMap.mpr
      refine ⟨candidate.1,
        mem_fiveFamilyRowMajorWindows candidate.1, ?_⟩
      apply List.mem_map.mpr
      exact ⟨candidate.2,
        mem_fiveFamilyRowMajorWindowSymbols candidate.2, hvalue⟩

end CNFFiveFamilyFlatRowMajorCatalogueTM

namespace CNFFiveFamilyOriginalIndexedBitTM

open Computability Turing GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputPolynomialCompositionClosure
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM

private theorem fiveFamilyOriginalBitTail_iterate_length_le
    (source : List Bool) (count : ℕ) :
    (((List.tail : List Bool → List Bool)^[count]) source).length ≤
      source.length := by
  induction count with
  | zero => simp only [Function.iterate_zero, id_eq, Std.le_refl]
  | succ count ih =>
      rw [Function.iterate_succ_apply']
      have htail :
          (((List.tail : List Bool → List Bool)
            (((List.tail : List Bool → List Bool)^[count]) source))).length ≤
            (((List.tail : List Bool → List Bool)^[count]) source).length := by
        cases ((List.tail : List Bool → List Bool)^[count]) source <;> simp
      exact htail.trans ih

private theorem fiveFamilyOriginalBitTail_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates
      (List.tail : List Bool → List Bool) Polynomial.X := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage _
  have hseed := GapCVP.CNFTypedRecordWorkerTM.parsedUnaryFold_seed_length_le
    input count seed hparse
  simpa only [Polynomial.eval_X, ge_iff_le] using
      (fiveFamilyOriginalBitTail_iterate_length_le seed stage).trans hseed

private noncomputable def fiveFamilyOriginalBitTailFoldComputable :
    BitTM
      (boundedRecordFoldOutput (List.tail : List Bool → List Bool)) :=
  boundedDependentRecordFoldComputable dropHeadComputable Polynomial.X
    fiveFamilyOriginalBitTail_polynomiallyBoundedFoldStates

private theorem fiveFamilyOriginalBitTail_iterate_eq_drop
    (source : List Bool) (count : ℕ) :
    ((List.tail : List Bool → List Bool)^[count]) source =
      source.drop count := by
  induction count generalizing source with
  | zero => simp only [Function.iterate_zero, id_eq, List.drop_zero]
  | succ count ih =>
      rw [Function.iterate_succ_apply]
      rw [ih]
      simp only [List.drop_tail]

private def fiveOriginalDynamicBitFoldInput
    (index source : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  index input ++ false :: source input

private noncomputable def fiveFamilyOriginalDynamicBitFoldInputComputable
    {index source : List Bool → List Bool}
    (indexComputer : BitTM index)
    (sourceComputer : BitTM source) :
    BitTM
      (fiveOriginalDynamicBitFoldInput index source) := by
  have sourceDelimiter :=
    GapCVP.TMComposition.computableInPolyTime
      sourceComputer (prependBitComputable false)
  have physical := pointwiseAppendComputable
    indexComputer sourceDelimiter
  change BitTM
    (fun input => index input ++ false :: source input)
  simpa only [Function.comp_apply] using physical

/-- GapCVP reduction support. -/
def fiveFamilyOriginalDynamicBitTail
    (index source : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  boundedRecordFoldOutput (List.tail : List Bool → List Bool)
    (fiveOriginalDynamicBitFoldInput index source input)

private noncomputable def fiveFamilyOriginalDynamicBitTailComputable
    {index source : List Bool → List Bool}
    (indexComputer : BitTM index)
    (sourceComputer : BitTM source) :
    BitTM
      (fiveFamilyOriginalDynamicBitTail index source) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyOriginalDynamicBitFoldInputComputable
      indexComputer sourceComputer)
    fiveFamilyOriginalBitTailFoldComputable
  change BitTM
    (fun input => boundedRecordFoldOutput
      (List.tail : List Bool → List Bool)
      (fiveOriginalDynamicBitFoldInput index source input))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyOriginalDynamicBitTail_valid
    (index source : List Bool → List Bool)
    (input : List Bool) (position : ℕ)
    (hindex : index input = List.replicate position true) :
    fiveFamilyOriginalDynamicBitTail index source input =
      (source input).drop position := by
  unfold fiveFamilyOriginalDynamicBitTail
    fiveOriginalDynamicBitFoldInput
  rw [hindex]
  change boundedRecordFoldOutput
    (List.tail : List Bool → List Bool)
    (unaryBoundedFoldWord position (source input)) = _
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word,
      fiveFamilyOriginalBitTail_iterate_eq_drop]

/-- GapCVP reduction support. -/
def fiveFamilyOriginalHeadBitWord : List Bool → List Bool :=
  markerConditionalOutput (fun _ : List Bool => [true]) [false]

/-- GapCVP reduction support. -/
noncomputable def fiveFamilyOriginalHeadBitComputable :
    BitTM
      fiveFamilyOriginalHeadBitWord :=
  markerConditionalComputable (sourceFixedWordComputable [true]) [false]

@[simp] theorem fiveFamilyOriginalHeadBitWord_eq
    (input : List Bool) :
    fiveFamilyOriginalHeadBitWord input =
      [input.headD false] := by
  cases input with
  | nil => rfl
  | cons head remaining =>
      cases head <;> rfl

/-- GapCVP reduction support. -/
def fiveFamilyOriginalDynamicBitWord
    (index source : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  fiveFamilyOriginalHeadBitWord
    (fiveFamilyOriginalDynamicBitTail index source input)

/-- GapCVP reduction support. -/
noncomputable def fiveOriginalDynamicBitComputable
    {index source : List Bool → List Bool}
    (indexComputer : BitTM index)
    (sourceComputer : BitTM source) :
    BitTM
      (fiveFamilyOriginalDynamicBitWord index source) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyOriginalDynamicBitTailComputable
      indexComputer sourceComputer)
    fiveFamilyOriginalHeadBitComputable
  change BitTM
    (fun input => fiveFamilyOriginalHeadBitWord
      (fiveFamilyOriginalDynamicBitTail index source input))
  simpa only [fiveFamilyOriginalHeadBitWord_eq, List.headD_eq_head?_getD, Function.comp_def]
      using physical

theorem fiveOriginalDynamicBitWord_valid
    (index source : List Bool → List Bool)
    (input : List Bool) (position : ℕ)
    (hindex : index input = List.replicate position true) :
    fiveFamilyOriginalDynamicBitWord index source input =
      [((source input).drop position).headD false] := by
  simp only [fiveFamilyOriginalDynamicBitWord,
      fiveFamilyOriginalDynamicBitTail_valid index source input position hindex,
          fiveFamilyOriginalHeadBitWord_eq,
      List.headD_eq_head?_getD, List.head?_drop]

end CNFFiveFamilyOriginalIndexedBitTM

namespace CNFFiveFamilyFlatSortedLiteralFamilies

open GapCVP.CL GapCVP.ThreeCNFReduction GapCVP.CNFFiniteRecordSort
open GapCVP.CNFInputDependentRecordSort

theorem sortedElements_eq_of_nodup_source_pairwise
    {α : Type} [Encodable α]
    (records : Finset α) (candidate : List α)
    (hmembership : ∀ record : α,
      record ∈ candidate ↔ record ∈ records)
    (hnodup : candidate.Nodup)
    (hpairwise : candidate.Pairwise
      (fun first second =>
        Encodable.encode first ≤ Encodable.encode second)) :
    sortedElements records = candidate := by
  classical
  have hequality := sourceOrderedDistinctRecords_eq_of_nodup_pairwise
    (sortedElements records) candidate
    (fun record => by simpa only [mem_sortedElements] using hmembership record)
    hnodup hpairwise
  simpa only [sourceOrderedDistinctRecords_sortedElements] using hequality

private def fiveSourceCellPositiveLiteralList
    {T S : ℕ} (time : Time T) (position : Position T) :
    List (SignedLiteral T S) :=
  (List.finRange (S + 1)).map fun symbol =>
    positive (time, position, symbol)

@[simp] private theorem mem_fiveFamilySourceCellPositiveLiteralList
    {T S : ℕ} (time : Time T) (position : Position T)
    (literal : SignedLiteral T S) :
    literal ∈ fiveSourceCellPositiveLiteralList time position ↔
      literal ∈ atLeastOneClause time position := by
  simp only [fiveSourceCellPositiveLiteralList, List.mem_map, List.mem_finRange, true_and,
      atLeastOneClause,
      Finset.mem_image, Finset.mem_univ]

private theorem fiveFamilySourceCellPositiveLiteralList_nodup
    {T S : ℕ} (time : Time T) (position : Position T) :
    (fiveSourceCellPositiveLiteralList
      (S := S) time position).Nodup := by
  unfold fiveSourceCellPositiveLiteralList
  apply (List.nodup_finRange (S + 1)).map
  intro first second hequal
  have hsymbol := congrArg
    (fun literal : SignedLiteral T S => literal.1.2.2) hequal
  simpa only [positive] using hsymbol

private theorem fiveFamilySourceCellPositiveLiteralList_pairwise
    {T S : ℕ} (time : Time T) (position : Position T) :
    (fiveSourceCellPositiveLiteralList
      (S := S) time position).Pairwise
        (fun first second =>
          Encodable.encode first ≤ Encodable.encode second) := by
  unfold fiveSourceCellPositiveLiteralList
  rw [List.pairwise_map]
  apply (List.pairwise_lt_finRange (S + 1)).imp
  intro first second hlt
  change
    Nat.pair
        (Nat.pair time.val
          (Nat.pair position.val first.val))
        (Encodable.encode true) ≤
      Nat.pair
        (Nat.pair time.val
          (Nat.pair position.val second.val))
        (Encodable.encode true)
  apply Nat.le_of_lt
  apply Nat.pair_lt_pair_left
  apply Nat.pair_lt_pair_right
  apply Nat.pair_lt_pair_right
  exact hlt

private theorem sortedElements_atLeastOneClause_eq_finRange
    {T S : ℕ} (time : Time T) (position : Position T) :
    sortedElements (atLeastOneClause (S := S) time position) =
      fiveSourceCellPositiveLiteralList time position := by
  apply sortedElements_eq_of_nodup_source_pairwise
  · exact mem_fiveFamilySourceCellPositiveLiteralList time position
  · exact fiveFamilySourceCellPositiveLiteralList_nodup time position
  · exact fiveFamilySourceCellPositiveLiteralList_pairwise
      time position

private def fiveSourceAcceptancePositiveLiteralList
    {T S : ℕ} (accept : Symbol S) :
    List (SignedLiteral T S) :=
  (List.finRange (T + 1)).map fun position =>
    positive ((Fin.last T : Time T), position, accept)

@[simp] private theorem mem_fiveFamilySourceAcceptancePositiveLiteralList
    {T S : ℕ} (accept : Symbol S)
    (literal : SignedLiteral T S) :
    literal ∈ fiveSourceAcceptancePositiveLiteralList
      (T := T) accept ↔
        literal ∈ acceptanceClause (T := T) accept := by
  simp only [fiveSourceAcceptancePositiveLiteralList, List.mem_map, List.mem_finRange, true_and,
      acceptanceClause, Finset.mem_image, Finset.mem_univ]

private theorem fiveFamilySourceAcceptancePositiveLiteralList_nodup
    {T S : ℕ} (accept : Symbol S) :
    (fiveSourceAcceptancePositiveLiteralList
      (T := T) accept).Nodup := by
  unfold fiveSourceAcceptancePositiveLiteralList
  apply (List.nodup_finRange (T + 1)).map
  intro first second hequal
  have hposition := congrArg
    (fun literal : SignedLiteral T S => literal.1.2.1) hequal
  simpa only [positive] using hposition

private theorem fiveFamilySourceAcceptancePositiveLiteralList_pairwise
    {T S : ℕ} (accept : Symbol S) :
    (fiveSourceAcceptancePositiveLiteralList
      (T := T) accept).Pairwise
        (fun first second =>
          Encodable.encode first ≤ Encodable.encode second) := by
  unfold fiveSourceAcceptancePositiveLiteralList
  rw [List.pairwise_map]
  apply (List.pairwise_lt_finRange (T + 1)).imp
  intro first second hlt
  change
    Nat.pair
        (Nat.pair T
          (Nat.pair first.val accept.val))
        (Encodable.encode true) ≤
      Nat.pair
        (Nat.pair T
          (Nat.pair second.val accept.val))
        (Encodable.encode true)
  apply Nat.le_of_lt
  apply Nat.pair_lt_pair_left
  apply Nat.pair_lt_pair_right
  apply Nat.pair_lt_pair_left
  exact hlt

private theorem sortedElements_acceptanceClause_eq_finRange
    {T S : ℕ} (accept : Symbol S) :
    sortedElements (acceptanceClause (T := T) accept) =
      fiveSourceAcceptancePositiveLiteralList
        (T := T) accept := by
  apply sortedElements_eq_of_nodup_source_pairwise
  · exact mem_fiveFamilySourceAcceptancePositiveLiteralList accept
  · exact fiveFamilySourceAcceptancePositiveLiteralList_nodup accept
  · exact fiveFamilySourceAcceptancePositiveLiteralList_pairwise accept

@[simp] private theorem fiveFamilySourceCellPositiveLiteralList_length
    {T S : ℕ} (time : Time T) (position : Position T) :
    (fiveSourceCellPositiveLiteralList
      (S := S) time position).length = S + 1 := by
  simp only [fiveSourceCellPositiveLiteralList, List.length_map, List.length_finRange]

end CNFFiveFamilyFlatSortedLiteralFamilies

namespace CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM

open Computability Turing GapCVP.CL GapCVP.CLCompleteVerifierSimulation GapCVP.CLCellRowBounds
open GapCVP.BinaryEncoding GapCVP.SourceUniformTuringTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatSourceOrder GapCVP.CNFFlatStructuralRecordWorkerTM
open GapCVP.CNFFlatSourceGridDescriptorTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM
open GapCVP.CNFFiveFamilyFlatSortedLiteralFamilies

/-- GapCVP reduction support. -/
def fiveFamilyFlatRankedSourceDescriptorWord
    (grid : Polynomial ℕ) (symbol : ℕ) (sign : Bool)
    (input : List Bool) : List Bool :=
  tableauSourceSignedLiteralDescriptorWord sign
    (fiveFamilyFlatIndexedVariableCode grid symbol input)

private noncomputable def fiveFamilyFlatRankedSourceDescriptorComputable
    (grid : Polynomial ℕ) (symbol : ℕ) (sign : Bool) :
    BitTM
      (fiveFamilyFlatRankedSourceDescriptorWord grid symbol sign) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatIndexedVariableCodeComputable grid symbol)
    (tableauSourceSignedLiteralDescriptorComputable sign)
  change BitTM
    (fun input => tableauSourceSignedLiteralDescriptorWord sign
      (fiveFamilyFlatIndexedVariableCode grid symbol input))
  simpa only [Function.comp_def] using physical

/-- GapCVP reduction support. -/
def fiveFamilyFlatRankedSourceDuplicatedCodeWord
    (grid : Polynomial ℕ) (symbol : ℕ) (sign : Bool)
    (input : List Bool) : List Bool :=
  duplicatedUnarySignedLiteralCodeWord sign
    (fiveFamilyFlatIndexedVariableCode grid symbol input)

private noncomputable def fiveFamilyFlatRankedSourceDuplicatedCodeComputable
    (grid : Polynomial ℕ) (symbol : ℕ) (sign : Bool) :
    BitTM
      (fiveFamilyFlatRankedSourceDuplicatedCodeWord
        grid symbol sign) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatIndexedVariableCodeComputable grid symbol)
    (duplicatedUnarySignedLiteralCodeComputable sign)
  change BitTM
    (fun input => duplicatedUnarySignedLiteralCodeWord sign
      (fiveFamilyFlatIndexedVariableCode grid symbol input))
  simpa only [Function.comp_def] using physical

/-- GapCVP reduction support. -/
def fiveFlatRankedSourceDescriptorStream
    (grid : Polynomial ℕ) (sign : Bool) (symbols : List ℕ)
    (input : List Bool) : List Bool :=
  symbols.flatMap fun symbol =>
    fiveFamilyFlatRankedSourceDescriptorWord grid symbol sign input

/-- GapCVP reduction support. -/
noncomputable def fiveFamilyFlatRankedSourceDescriptorStreamComputable
    (grid : Polynomial ℕ) (sign : Bool) (symbols : List ℕ) :
    BitTM
      (fiveFlatRankedSourceDescriptorStream grid sign symbols) := by
  induction symbols with
  | nil => exact constantWordComputable []
  | cons symbol remaining ih =>
      exact pointwiseAppendComputable
        (fiveFamilyFlatRankedSourceDescriptorComputable
          grid symbol sign) ih

/-- GapCVP reduction support. -/
def fiveFlatRankedSourceDuplicatedCodeStream
    (grid : Polynomial ℕ) (sign : Bool) (symbols : List ℕ)
    (input : List Bool) : List Bool :=
  symbols.flatMap fun symbol =>
    fiveFamilyFlatRankedSourceDuplicatedCodeWord
      grid symbol sign input

/-- GapCVP reduction support. -/
noncomputable def fiveFamilyFlatRankedSourceDuplicatedCodeStreamComputable
    (grid : Polynomial ℕ) (sign : Bool) (symbols : List ℕ) :
    BitTM
      (fiveFlatRankedSourceDuplicatedCodeStream
        grid sign symbols) := by
  induction symbols with
  | nil => exact constantWordComputable []
  | cons symbol remaining ih =>
      exact pointwiseAppendComputable
        (fiveFamilyFlatRankedSourceDuplicatedCodeComputable
          grid symbol sign) ih

private def fiveFlatRankedAtLeastDescriptorPayload
    (grid : Polynomial ℕ) (alphabet : ℕ)
    (input : List Bool) : List Bool :=
  fiveFlatRankedSourceDescriptorStream grid true
    ((List.finRange alphabet).map Fin.val) input

private noncomputable def fiveFamilyFlatRankedAtLeastDescriptorPayloadComputable
    (grid : Polynomial ℕ) (alphabet : ℕ) :
    BitTM
      (fiveFlatRankedAtLeastDescriptorPayload grid alphabet) :=
  fiveFamilyFlatRankedSourceDescriptorStreamComputable grid true
    ((List.finRange alphabet).map Fin.val)

private def fiveFlatRankedAtLeastDuplicatedCodePayload
    (grid : Polynomial ℕ) (alphabet : ℕ)
    (input : List Bool) : List Bool :=
  fiveFlatRankedSourceDuplicatedCodeStream grid true
    ((List.finRange alphabet).map Fin.val) input

private noncomputable def fiveFamilyFlatRankedAtLeastDuplicatedCodePayloadComputable
    (grid : Polynomial ℕ) (alphabet : ℕ) :
    BitTM
      (fiveFlatRankedAtLeastDuplicatedCodePayload grid alphabet) :=
  fiveFamilyFlatRankedSourceDuplicatedCodeStreamComputable
    grid true ((List.finRange alphabet).map Fin.val)

/-- GapCVP reduction support. -/
def fiveFlatRowMajorAtLeastClauseRecordWord
    (grid : Polynomial ℕ) (alphabet : ℕ)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (fiveFlatRankedAtLeastDescriptorPayload
        grid alphabet input) ++
    lengthPrefixedWord
      (fiveFlatRankedAtLeastDuplicatedCodePayload
        grid alphabet input) ++
      lengthPrefixedWord (List.replicate alphabet true)

/-- GapCVP reduction support. -/
noncomputable def fiveFamilyFlatRowMajorAtLeastClauseRecordComputable
    (grid : Polynomial ℕ) (alphabet : ℕ) :
    BitTM
      (fiveFlatRowMajorAtLeastClauseRecordWord grid alphabet) := by
  have descriptor := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatRankedAtLeastDescriptorPayloadComputable
      grid alphabet)
    structuralPrefixWriterComputable
  have duplicate := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatRankedAtLeastDuplicatedCodePayloadComputable
      grid alphabet)
    structuralPrefixWriterComputable
  have counter := constantWordComputable
    (lengthPrefixedWord (List.replicate alphabet true))
  have ending := pointwiseAppendComputable duplicate counter
  have physical := pointwiseAppendComputable descriptor ending
  have hequality :
      (fun input : List Bool =>
        lengthPrefixedWord
            (fiveFlatRankedAtLeastDescriptorPayload
              grid alphabet input) ++
          (lengthPrefixedWord
            (fiveFlatRankedAtLeastDuplicatedCodePayload
              grid alphabet input) ++
            lengthPrefixedWord (List.replicate alphabet true))) =
        fiveFlatRowMajorAtLeastClauseRecordWord
          grid alphabet := by
    funext input
    simp only [fiveFlatRowMajorAtLeastClauseRecordWord, List.append_assoc]
  rw [← hequality]
  exact physical

/-- GapCVP reduction support. -/
def fiveFamilyFlatSourceRowMajorIndex
    {T : ℕ} (time : Time T) (position : Position T) : ℕ :=
  time.val * (T + 1) + position.val

@[simp] theorem fiveFamilyFlatSourceRowMajorIndex_div
    {T : ℕ} (time : Time T) (position : Position T) :
    fiveFamilyFlatSourceRowMajorIndex time position / (T + 1) =
      time.val := by
  unfold fiveFamilyFlatSourceRowMajorIndex
  have hgrid : 0 < T + 1 := by omega
  have hposition : position.val < T + 1 := position.isLt
  simpa only [Nat.mul_comm, Nat.div_eq_of_lt hposition, add_zero] using
      (Nat.mul_add_div hgrid time.val position.val)

@[simp] theorem fiveFamilyFlatSourceRowMajorIndex_mod
    {T : ℕ} (time : Time T) (position : Position T) :
    fiveFamilyFlatSourceRowMajorIndex time position % (T + 1) =
      position.val := by
  unfold fiveFamilyFlatSourceRowMajorIndex
  simp only [Nat.mul_add_mod_of_lt position.isLt]

theorem fiveFlatIndexedVariableCode_rowMajor
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (time : Time (rowWidth bound machine original))
    (position : Position (rowWidth bound machine original))
    (symbol : Symbol (completePhaseSymbolCount machine.tm)) :
    fiveFamilyFlatIndexedVariableCode
      (fiveFamilyFlatIndexedGridPolynomial bound machine) symbol.val
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyFlatSourceRowMajorIndex time position) true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate
        (Encodable.encode
          ((time, position, symbol) : Variable
            (rowWidth bound machine original)
            (completePhaseSymbolCount machine.tm))) true := by
  have hpositive :
      0 < (fiveFamilyFlatIndexedGridPolynomial
        bound machine).eval original.length := by
    simp only [fiveFamilyFlatIndexedGridPolynomial_eval, lt_add_iff_pos_left, Order.lt_add_one_iff,
        zero_le]
  rw [fiveFamilyFlatIndexedVariableCode_valid
    (fiveFamilyFlatIndexedGridPolynomial bound machine)
    symbol.val (fiveFamilyFlatSourceRowMajorIndex time position)
    original suffix hpositive,
    fiveFamilyFlatIndexedGridPolynomial_eval,
    fiveFamilyFlatSourceRowMajorIndex_div,
    fiveFamilyFlatSourceRowMajorIndex_mod]
  rfl

private theorem fiveFamilyFlatRankedAtLeastDescriptorPayload_rowMajor
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (time : Time (rowWidth bound machine original))
    (position : Position (rowWidth bound machine original)) :
    fiveFlatRankedAtLeastDescriptorPayload
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (completePhaseSymbolCount machine.tm + 1)
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyFlatSourceRowMajorIndex time position) true) ++
        lengthPrefixedWord original ++ suffix) =
      flatSourceClauseDescriptorPayload
        (atLeastOneClause
          (S := completePhaseSymbolCount machine.tm)
          time position) := by
  unfold fiveFlatRankedAtLeastDescriptorPayload
    fiveFlatRankedSourceDescriptorStream
  rw [List.flatMap_map]
  unfold flatSourceClauseDescriptorPayload
  rw [sortedElements_atLeastOneClause_eq_finRange]
  simp only [fiveSourceCellPositiveLiteralList,
    List.map_map, flatSignedLiteralDescriptorStream,
    List.flatMap_map, Function.comp_def]
  apply List.flatMap_congr
  intro symbol _
  change
    tableauSourceSignedLiteralDescriptorWord true
      (fiveFamilyFlatIndexedVariableCode
        (fiveFamilyFlatIndexedGridPolynomial bound machine)
        symbol.val
        (lengthPrefixedWord
          (List.replicate
            (fiveFamilyFlatSourceRowMajorIndex time position) true) ++
          lengthPrefixedWord original ++ suffix)) = _
  rw [fiveFlatIndexedVariableCode_rowMajor
    bound machine original suffix time position symbol]
  rw [tableauSourceSignedLiteralDescriptorWord_variable]
  rfl

private theorem fiveFamilyFlatRankedAtLeastDuplicatedCodePayload_rowMajor
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (time : Time (rowWidth bound machine original))
    (position : Position (rowWidth bound machine original)) :
    fiveFlatRankedAtLeastDuplicatedCodePayload
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (completePhaseSymbolCount machine.tm + 1)
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyFlatSourceRowMajorIndex time position) true) ++
        lengthPrefixedWord original ++ suffix) =
      flatSourceClauseDuplicatedCodePayload
        (atLeastOneClause
          (S := completePhaseSymbolCount machine.tm)
          time position) := by
  unfold fiveFlatRankedAtLeastDuplicatedCodePayload
    fiveFlatRankedSourceDuplicatedCodeStream
  rw [List.flatMap_map]
  unfold flatSourceClauseDuplicatedCodePayload
    flatSourceFinsetCodes
  rw [sortedElements_atLeastOneClause_eq_finRange]
  simp only [fiveSourceCellPositiveLiteralList,
    List.map_map, flatDuplicatedUnarySourceStream,
    List.flatMap_map, Function.comp_def]
  apply List.flatMap_congr
  intro symbol _
  change
    duplicatedUnarySignedLiteralCodeWord true
      (fiveFamilyFlatIndexedVariableCode
        (fiveFamilyFlatIndexedGridPolynomial bound machine)
        symbol.val
        (lengthPrefixedWord
          (List.replicate
            (fiveFamilyFlatSourceRowMajorIndex time position) true) ++
          lengthPrefixedWord original ++ suffix)) = _
  rw [fiveFlatIndexedVariableCode_rowMajor
    bound machine original suffix time position symbol]
  rw [duplicatedUnarySignedLiteralCodeWord_sourceVariable]
  rfl

private theorem fiveFamilyFlatAtLeastClause_exact_card
    {T S : ℕ} (time : Time T) (position : Position T) :
    (atLeastOneClause (S := S) time position).card = S + 1 := by
  have hsort := congrArg List.length
    (sortedElements_atLeastOneClause_eq_finRange
      (S := S) time position)
  simpa only [ThreeCNFReduction.sortedElements_length,
      fiveFamilySourceCellPositiveLiteralList_length] using
      hsort

theorem fiveFamilyFlatRowMajorAtLeastClauseRecordWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (time : Time (rowWidth bound machine original))
    (position : Position (rowWidth bound machine original)) :
    fiveFlatRowMajorAtLeastClauseRecordWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (completePhaseSymbolCount machine.tm + 1)
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyFlatSourceRowMajorIndex time position) true) ++
        lengthPrefixedWord original ++ suffix) =
      flatSourceClauseAnnotatedRecord
        (atLeastOneClause
          (S := completePhaseSymbolCount machine.tm)
          time position) := by
  unfold fiveFlatRowMajorAtLeastClauseRecordWord
    flatSourceClauseAnnotatedRecord
  rw [fiveFamilyFlatRankedAtLeastDescriptorPayload_rowMajor
    bound machine original suffix time position,
    fiveFamilyFlatRankedAtLeastDuplicatedCodePayload_rowMajor
      bound machine original suffix time position]
  unfold flatSourceClauseUnaryCountPayload
  rw [fiveFamilyFlatAtLeastClause_exact_card]

end CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM

namespace CNFFiveFamilyFlatAcceptanceVariableTM

open Computability Turing GapCVP.CL GapCVP.CLCompleteVerifierSimulation GapCVP.CLCellRowBounds
open GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceUniformTuringTM
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CNFFlatSourceGridDescriptorTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFUnaryPairIndexTM
open GapCVP.CNFUnaryPairIndexTotalRuntimeCert GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM

/-- GapCVP reduction support. -/
def fiveFamilyVerifierAcceptingSymbol
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    Symbol (completePhaseSymbolCount machine.tm) :=
  completePhaseSymbolEquiv machine.tm
    (acceptingPhaseCell machine.tm)

private def fiveFamilyAcceptanceFinalTimeUnary
    (grid : Polynomial ℕ) (input : List Bool) : List Bool :=
  (fiveFlatIndexedOriginalPolynomialUnary grid input).tail

private noncomputable def fiveFamilyAcceptanceFinalTimeUnaryComputable
    (grid : Polynomial ℕ) :
    BitTM
      (fiveFamilyAcceptanceFinalTimeUnary grid) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFlatIndexedOriginalPolynomialUnaryComputable grid)
    dropHeadComputable
  change BitTM
    (fun input =>
      (fiveFlatIndexedOriginalPolynomialUnary grid input).tail)
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyAcceptanceFinalTimeUnary_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (position : ℕ) (original suffix : List Bool) :
    fiveFamilyAcceptanceFinalTimeUnary
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (lengthPrefixedWord (List.replicate position true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate (rowWidth bound machine original) true := by
  unfold fiveFamilyAcceptanceFinalTimeUnary
  rw [fiveFamilyFlatIndexedOriginalPolynomialUnary_valid
    (fiveFamilyFlatIndexedGridPolynomial bound machine)
    position original suffix,
    fiveFamilyFlatIndexedGridPolynomial_eval]
  simp only [List.replicate_succ, List.tail_cons]

private def fiveAcceptancePositionSymbolPairInput
    (symbol : ℕ) (input : List Bool) : List Bool :=
  fiveFamilyFlatIndexedPhysicalRank input ++
    false :: (List.replicate symbol true ++ [false])

private noncomputable def fiveFamilyAcceptancePositionSymbolPairInputComputable
    (symbol : ℕ) :
    BitTM
      (fiveAcceptancePositionSymbolPairInput symbol) := by
  have physical := pointwiseAppendComputable
    fiveFlatIndexedPhysicalRankComputable
    (constantWordComputable
      (false :: (List.replicate symbol true ++ [false])))
  exact physical

private def fiveAcceptancePositionSymbolCode
    (symbol : ℕ) (input : List Bool) : List Bool :=
  unarySourcePairOutput
    (fiveAcceptancePositionSymbolPairInput symbol input)

private noncomputable def fiveFamilyAcceptancePositionSymbolCodeComputable
    (symbol : ℕ) :
    BitTM
      (fiveAcceptancePositionSymbolCode symbol) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyAcceptancePositionSymbolPairInputComputable symbol)
    actualUnaryPairIndexComputable
  change BitTM
    (fun input => unarySourcePairOutput
      (fiveAcceptancePositionSymbolPairInput symbol input))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyAcceptancePositionSymbolCode_valid
    (symbol position : ℕ) (original suffix : List Bool) :
    fiveAcceptancePositionSymbolCode symbol
      (lengthPrefixedWord (List.replicate position true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate (Nat.pair position symbol) true := by
  unfold fiveAcceptancePositionSymbolCode
    fiveAcceptancePositionSymbolPairInput
  rw [fiveFamilyFlatIndexedPhysicalRank_valid]
  change unarySourcePairOutput
    (unarySourcePairWord position symbol) = _
  exact unarySourcePairOutput_word position symbol

private def fiveAcceptanceVariablePairInput
    (grid : Polynomial ℕ) (symbol : ℕ)
    (input : List Bool) : List Bool :=
  fiveFamilyAcceptanceFinalTimeUnary grid input ++
    false :: (fiveAcceptancePositionSymbolCode
      symbol input ++ [false])

private noncomputable def fiveFamilyAcceptanceVariablePairInputComputable
    (grid : Polynomial ℕ) (symbol : ℕ) :
    BitTM
      (fiveAcceptanceVariablePairInput grid symbol) := by
  have inner := pointwiseAppendComputable
    (fiveFamilyAcceptancePositionSymbolCodeComputable symbol)
    (constantWordComputable [false])
  have separator := GapCVP.TMComposition.computableInPolyTime
    inner (prependBitComputable false)
  have physical := pointwiseAppendComputable
    (fiveFamilyAcceptanceFinalTimeUnaryComputable grid) separator
  change BitTM
    (fun input => fiveFamilyAcceptanceFinalTimeUnary grid input ++
      false :: (fiveAcceptancePositionSymbolCode
        symbol input ++ [false]))
  simpa only [Function.comp_apply] using physical

private def fiveFamilyAcceptanceVariableCode
    (grid : Polynomial ℕ) (symbol : ℕ)
    (input : List Bool) : List Bool :=
  unarySourcePairOutput
    (fiveAcceptanceVariablePairInput grid symbol input)

private noncomputable def fiveFamilyAcceptanceVariableCodeComputable
    (grid : Polynomial ℕ) (symbol : ℕ) :
    BitTM
      (fiveFamilyAcceptanceVariableCode grid symbol) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyAcceptanceVariablePairInputComputable grid symbol)
    actualUnaryPairIndexComputable
  change BitTM
    (fun input => unarySourcePairOutput
      (fiveAcceptanceVariablePairInput grid symbol input))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyAcceptanceVariableCode_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (position : Position (rowWidth bound machine original)) :
    fiveFamilyAcceptanceVariableCode
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (fiveFamilyVerifierAcceptingSymbol machine).val
      (lengthPrefixedWord
        (List.replicate position.val true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate
        (Encodable.encode
          (((Fin.last (rowWidth bound machine original) :
              Time (rowWidth bound machine original)),
            position, fiveFamilyVerifierAcceptingSymbol machine) :
            Variable (rowWidth bound machine original)
              (completePhaseSymbolCount machine.tm))) true := by
  unfold fiveFamilyAcceptanceVariableCode
    fiveAcceptanceVariablePairInput
  rw [fiveFamilyAcceptanceFinalTimeUnary_valid
    bound machine position.val original suffix,
    fiveFamilyAcceptancePositionSymbolCode_valid
      (fiveFamilyVerifierAcceptingSymbol machine).val
      position.val original suffix]
  change unarySourcePairOutput
    (unarySourcePairWord
      (rowWidth bound machine original)
      (Nat.pair position.val
        (fiveFamilyVerifierAcceptingSymbol machine).val)) = _
  rw [unarySourcePairOutput_word]
  rfl

private def fiveAcceptanceSourceDescriptorWord
    (grid : Polynomial ℕ) (symbol : ℕ)
    (input : List Bool) : List Bool :=
  tableauSourceSignedLiteralDescriptorWord true
    (fiveFamilyAcceptanceVariableCode grid symbol input)

private noncomputable def fiveFamilyAcceptanceSourceDescriptorComputable
    (grid : Polynomial ℕ) (symbol : ℕ) :
    BitTM
      (fiveAcceptanceSourceDescriptorWord grid symbol) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyAcceptanceVariableCodeComputable grid symbol)
    (tableauSourceSignedLiteralDescriptorComputable true)
  change BitTM
    (fun input => tableauSourceSignedLiteralDescriptorWord true
      (fiveFamilyAcceptanceVariableCode grid symbol input))
  simpa only [Function.comp_def] using physical

private def fiveAcceptanceSourceDuplicatedCodeWord
    (grid : Polynomial ℕ) (symbol : ℕ)
    (input : List Bool) : List Bool :=
  duplicatedUnarySignedLiteralCodeWord true
    (fiveFamilyAcceptanceVariableCode grid symbol input)

private noncomputable def fiveFamilyAcceptanceSourceDuplicatedCodeComputable
    (grid : Polynomial ℕ) (symbol : ℕ) :
    BitTM
      (fiveAcceptanceSourceDuplicatedCodeWord grid symbol) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyAcceptanceVariableCodeComputable grid symbol)
    (duplicatedUnarySignedLiteralCodeComputable true)
  change BitTM
    (fun input => duplicatedUnarySignedLiteralCodeWord true
      (fiveFamilyAcceptanceVariableCode grid symbol input))
  simpa only [Function.comp_def] using physical

end CNFFiveFamilyFlatAcceptanceVariableTM

namespace CNFFiveFamilyFlatAcceptanceClauseFoldTM

open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLCellRowBounds GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.SourceMachineCert GapCVP.SourceUniformTuringTM GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceWholeOutputValidBranchRecordTM
open GapCVP.SourceCanonicalUnaryGridIndexTM GapCVP.SourceAnchoredGridRecordFoldTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFBoundedRecordFoldTM GapCVP.CNFFlatSourceOrder
open GapCVP.CNFFlatStructuralRecordWorkerTM GapCVP.CNFFlatSourceGridDescriptorTM
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM GapCVP.CNFFiveFamilyFlatIndexedCatalogueTM
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM GapCVP.CNFTypedRecordWorkerTM
open GapCVP.CNFFiveFamilyFlatSortedLiteralFamilies GapCVP.CNFFiveFamilyFlatAcceptanceVariableTM

private def fiveAcceptancePositionCountWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  List.replicate
    ((fiveFamilyFlatIndexedGridPolynomial
      bound machine).eval original.length) true

private noncomputable def fiveAcceptancePositionCountComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveAcceptancePositionCountWord bound machine) :=
  polynomialValueUnaryComputable
    (fiveFamilyFlatIndexedGridPolynomial bound machine)

private def fiveAcceptancePositionEnumerationInput
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  fiveAcceptancePositionCountWord bound machine original ++
    [false]

private noncomputable def fiveFamilyAcceptancePositionEnumerationInputComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveAcceptancePositionEnumerationInput bound machine) :=
  pointwiseAppendComputable
    (fiveAcceptancePositionCountComputable bound machine)
    (constantWordComputable [false])

private def fiveAcceptancePositionDescriptorWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  sourceCanonicalUnaryGridIndexOutput
    (fiveAcceptancePositionEnumerationInput
      bound machine original)

private noncomputable def fiveFamilyAcceptancePositionDescriptorComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveAcceptancePositionDescriptorWord bound machine) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyAcceptancePositionEnumerationInputComputable
      bound machine)
    sourceCanonicalUnaryGridIndexComputable
  change BitTM
    (fun original => sourceCanonicalUnaryGridIndexOutput
      (fiveAcceptancePositionEnumerationInput
        bound machine original))
  simpa only [Function.comp_def] using physical

@[simp] private theorem fiveFamilyAcceptancePositionDescriptorWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    fiveAcceptancePositionDescriptorWord
      bound machine original =
      sourceCanonicalUnaryGridIndexDescriptors
        (rowWidth bound machine original + 1) := by
  simp only [fiveAcceptancePositionDescriptorWord, fiveAcceptancePositionEnumerationInput,
      fiveAcceptancePositionCountWord, fiveFamilyFlatIndexedGridPolynomial_eval,
      sourceCanonicalUnaryGridIndexOutput_valid, List.append_nil]

private def fiveAcceptancePositionAnchoredFoldInput
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  fiveAcceptancePositionCountWord bound machine original ++
    false ::
      (lengthPrefixedWord
        (fiveFlatOriginalSourceAnchorWord
          bound machine original) ++
        fiveAcceptancePositionDescriptorWord
          bound machine original)

private noncomputable def fiveFamilyAcceptancePositionAnchoredFoldInputComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveAcceptancePositionAnchoredFoldInput bound machine) := by
  have anchor := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatOriginalSourceAnchorComputable bound machine)
    structuralPrefixWriterComputable
  have seed := pointwiseAppendComputable anchor
    (fiveFamilyAcceptancePositionDescriptorComputable bound machine)
  have delimiter := GapCVP.TMComposition.computableInPolyTime
    seed (prependBitComputable false)
  have physical := pointwiseAppendComputable
    (fiveAcceptancePositionCountComputable bound machine)
    delimiter
  change BitTM
    (fun original =>
      fiveAcceptancePositionCountWord bound machine original ++
        false ::
          (lengthPrefixedWord
            (fiveFlatOriginalSourceAnchorWord
              bound machine original) ++
            fiveAcceptancePositionDescriptorWord
              bound machine original))
  simpa only [fiveFamilyAcceptancePositionDescriptorWord_valid, Function.comp_apply] using physical

private noncomputable def fiveFamilyAcceptancePositionAnchoredCatalogueComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (fun original =>
        boundedRecordFoldOutput
          (sourceAnchoredGridRecordRotationOutput candidate)
          (fiveAcceptancePositionAnchoredFoldInput
            bound machine original)) := by
  have fold := sourceAnchoredGridRecordFoldComputable computer
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyAcceptancePositionAnchoredFoldInputComputable
      bound machine) fold
  simpa only [Function.comp_def] using physical

private def fiveAcceptancePositionRankWords
    (count : ℕ) : List (List Bool) :=
  (List.range count).map fun position =>
    List.replicate position true

@[simp] private theorem fiveFamilyAcceptancePositionRankWords_descriptors
    (count : ℕ) :
    (fiveAcceptancePositionRankWords count).flatMap
      lengthPrefixedWord =
      sourceCanonicalUnaryGridIndexDescriptors count := by
  simp only [fiveAcceptancePositionRankWords,
    sourceCanonicalUnaryGridIndexDescriptors, List.flatMap_map]
  rfl

private theorem fiveFamilyAcceptancePositionAnchoredCatalogueOutput_eq
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (candidate : List Bool → List Bool)
    (original : List Bool)
    (hfit : ∀ position : Fin (rowWidth bound machine original + 1),
      (candidate
        (lengthPrefixedWord (List.replicate position.val true) ++
          fiveFlatOriginalSourceAnchorWord
            bound machine original)).length ≤
        (fiveFlatOriginalSourceAnchorWord
          bound machine original).length) :
    boundedRecordFoldOutput
      (sourceAnchoredGridRecordRotationOutput candidate)
      (fiveAcceptancePositionAnchoredFoldInput
        bound machine original) =
      lengthPrefixedWord
        (fiveFlatOriginalSourceAnchorWord
          bound machine original) ++
        (fiveAcceptancePositionRankWords
          (rowWidth bound machine original + 1)).flatMap
            (fun rank => lengthPrefixedWord
              (candidate (lengthPrefixedWord rank ++
                fiveFlatOriginalSourceAnchorWord
                  bound machine original))) := by
  let count := rowWidth bound machine original + 1
  let ranks := fiveAcceptancePositionRankWords count
  have hranks : ranks.length = count := by
    simp only [fiveAcceptancePositionRankWords, List.length_map, List.length_range, ranks]
  have hfit' : ∀ rank ∈ ranks,
      (candidate
        (lengthPrefixedWord rank ++
          fiveFlatOriginalSourceAnchorWord
            bound machine original)).length ≤
        (fiveFlatOriginalSourceAnchorWord
          bound machine original).length := by
    intro rank hrank
    obtain ⟨position, hposition, rfl⟩ := List.mem_map.mp hrank
    have hp : position < count := by
      simpa only [List.mem_range] using hposition
    exact hfit ⟨position, hp⟩
  have hseed :
      fiveAcceptancePositionAnchoredFoldInput
        bound machine original =
        unaryBoundedFoldWord ranks.length
          (lengthPrefixedWord
              (fiveFlatOriginalSourceAnchorWord
                bound machine original) ++
            ranks.flatMap lengthPrefixedWord ++ []) := by
    simp only [fiveAcceptancePositionAnchoredFoldInput, fiveAcceptancePositionCountWord,
        fiveFamilyFlatIndexedGridPolynomial_eval, fiveFamilyAcceptancePositionDescriptorWord_valid,
            unaryBoundedFoldWord,
        hranks, fiveFamilyAcceptancePositionRankWords_descriptors, List.append_nil, ranks, count]
  rw [hseed,
    boundedRecordFoldOutput_sourceAnchoredGridRecordRanks
      candidate
      (fiveFlatOriginalSourceAnchorWord
        bound machine original)
      ranks [] hfit']
  simp only [List.append_nil, ranks, count]

@[simp] theorem fiveFamilyFlatSingletonDescriptorPayload
    {T S : ℕ} (literal : SignedLiteral T S) :
    flatSourceClauseDescriptorPayload ({literal} : Clause T S) =
      flatSignedLiteralDescriptor (sourceLiteral literal) := by
  simp only [flatSourceClauseDescriptorPayload, flatSignedLiteralDescriptorStream, sortedElements,
      Finset.sort_singleton, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]

@[simp] theorem fiveFamilyFlatSingletonDuplicatedCodePayload
    {T S : ℕ} (literal : SignedLiteral T S) :
    flatSourceClauseDuplicatedCodePayload ({literal} : Clause T S) =
      flatDuplicatedUnaryField (Encodable.encode literal) := by
  simp only [flatSourceClauseDuplicatedCodePayload, flatDuplicatedUnarySourceStream,
      flatSourceFinsetCodes,
      sortedElements, Finset.sort_singleton, List.map_cons, List.map_nil, List.flatMap_cons,
          List.flatMap_nil,
      List.append_nil]

private theorem fiveFamilyFlatSingletonDescriptor_length_le
    {T S : ℕ} (literal : SignedLiteral T S) :
    (flatSignedLiteralDescriptor (sourceLiteral literal)).length ≤
      flatSourceAnnotatedClauseLengthBound T S := by
  have hrecord := flatSourceClauseAnnotatedRecord_length_le
    ({literal} : Clause T S)
  have hcontained :
      (flatSignedLiteralDescriptor (sourceLiteral literal)).length ≤
        (flatSourceClauseAnnotatedRecord
          ({literal} : Clause T S)).length := by
    unfold flatSourceClauseAnnotatedRecord
    simp only [List.length_append, lengthPrefixedWord_length,
      fiveFamilyFlatSingletonDescriptorPayload]
    omega
  exact hcontained.trans hrecord

private theorem fiveFamilyFlatSingletonDuplicatedCode_length_le
    {T S : ℕ} (literal : SignedLiteral T S) :
    (flatDuplicatedUnaryField (Encodable.encode literal)).length ≤
      flatSourceAnnotatedClauseLengthBound T S := by
  have hrecord := flatSourceClauseAnnotatedRecord_length_le
    ({literal} : Clause T S)
  have hcontained :
      (flatDuplicatedUnaryField (Encodable.encode literal)).length ≤
        (flatSourceClauseAnnotatedRecord
          ({literal} : Clause T S)).length := by
    unfold flatSourceClauseAnnotatedRecord
    simp only [List.length_append, lengthPrefixedWord_length,
      fiveFamilyFlatSingletonDuplicatedCodePayload]
    omega
  exact hcontained.trans hrecord

private theorem fiveFamilyAcceptanceSourceDescriptorWord_anchor
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (position : Position (rowWidth bound machine original)) :
    fiveAcceptanceSourceDescriptorWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (fiveFamilyVerifierAcceptingSymbol machine).val
      (lengthPrefixedWord (List.replicate position.val true) ++
        fiveFlatOriginalSourceAnchorWord
          bound machine original) =
      flatSignedLiteralDescriptor
        (sourceLiteral
          (positive
            ((Fin.last (rowWidth bound machine original) :
                Time (rowWidth bound machine original)),
              position, fiveFamilyVerifierAcceptingSymbol machine))) := by
  unfold fiveAcceptanceSourceDescriptorWord
  unfold fiveFlatOriginalSourceAnchorWord
  simp only [← List.append_assoc]
  rw [fiveFamilyAcceptanceVariableCode_valid
    bound machine original
    (List.replicate
      ((flatSourceAnnotatedClauseLengthPolynomial
        (nondeterministicTableauDimensionPolynomial bound machine)
        (completePhaseSymbolCount machine.tm)).eval
        original.length) true)
    position]
  rw [tableauSourceSignedLiteralDescriptorWord_variable]
  rfl

private theorem fiveFamilyAcceptanceSourceDuplicatedCodeWord_anchor
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (position : Position (rowWidth bound machine original)) :
    fiveAcceptanceSourceDuplicatedCodeWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (fiveFamilyVerifierAcceptingSymbol machine).val
      (lengthPrefixedWord (List.replicate position.val true) ++
        fiveFlatOriginalSourceAnchorWord
          bound machine original) =
      flatDuplicatedUnaryField
        (Encodable.encode
          (positive
            ((Fin.last (rowWidth bound machine original) :
                Time (rowWidth bound machine original)),
              position, fiveFamilyVerifierAcceptingSymbol machine))) := by
  unfold fiveAcceptanceSourceDuplicatedCodeWord
  unfold fiveFlatOriginalSourceAnchorWord
  simp only [← List.append_assoc]
  rw [fiveFamilyAcceptanceVariableCode_valid
    bound machine original
    (List.replicate
      ((flatSourceAnnotatedClauseLengthPolynomial
        (nondeterministicTableauDimensionPolynomial bound machine)
        (completePhaseSymbolCount machine.tm)).eval
        original.length) true)
    position]
  rw [duplicatedUnarySignedLiteralCodeWord_sourceVariable]
  rfl

private theorem fiveFamilyAcceptanceSourceDescriptor_fits_anchor
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (position : Position (rowWidth bound machine original)) :
    (fiveAcceptanceSourceDescriptorWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (fiveFamilyVerifierAcceptingSymbol machine).val
      (lengthPrefixedWord (List.replicate position.val true) ++
        fiveFlatOriginalSourceAnchorWord
          bound machine original)).length ≤
      (fiveFlatOriginalSourceAnchorWord
        bound machine original).length := by
  rw [fiveFamilyAcceptanceSourceDescriptorWord_anchor]
  have hbound := fiveFamilyFlatSingletonDescriptor_length_le
    (positive
      ((Fin.last (rowWidth bound machine original) :
          Time (rowWidth bound machine original)),
        position, fiveFamilyVerifierAcceptingSymbol machine))
  rw [flatSourceAnnotatedClauseLengthBound_eq_polynomial
    bound machine original] at hbound
  simp only [fiveFlatOriginalSourceAnchorWord,
    List.length_append, List.length_replicate]
  omega

private theorem fiveFamilyAcceptanceSourceDuplicatedCode_fits_anchor
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (position : Position (rowWidth bound machine original)) :
    (fiveAcceptanceSourceDuplicatedCodeWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (fiveFamilyVerifierAcceptingSymbol machine).val
      (lengthPrefixedWord (List.replicate position.val true) ++
        fiveFlatOriginalSourceAnchorWord
          bound machine original)).length ≤
      (fiveFlatOriginalSourceAnchorWord
        bound machine original).length := by
  rw [fiveFamilyAcceptanceSourceDuplicatedCodeWord_anchor]
  have hbound := fiveFamilyFlatSingletonDuplicatedCode_length_le
    (positive
      ((Fin.last (rowWidth bound machine original) :
          Time (rowWidth bound machine original)),
        position, fiveFamilyVerifierAcceptingSymbol machine))
  rw [flatSourceAnnotatedClauseLengthBound_eq_polynomial
    bound machine original] at hbound
  simp only [fiveFlatOriginalSourceAnchorWord,
    List.length_append, List.length_replicate]
  omega

private theorem fiveFamilyAcceptancePositionRankWords_eq_finRange
    (count : ℕ) :
    fiveAcceptancePositionRankWords count =
      (List.finRange count).map fun position =>
        List.replicate position.val true := by
  unfold fiveAcceptancePositionRankWords
  rw [← List.map_coe_finRange_eq_range (n := count)]
  simp only [List.map_map, Function.comp_def]

private def fiveAcceptanceDescriptorRecords
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List (List Bool) :=
  (List.finRange (rowWidth bound machine original + 1)).map
    fun position =>
      flatSignedLiteralDescriptor
        (sourceLiteral
          (positive
            ((Fin.last (rowWidth bound machine original) :
                Time (rowWidth bound machine original)),
              position, fiveFamilyVerifierAcceptingSymbol machine)))

private def fiveAcceptanceDuplicatedCodeRecords
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List (List Bool) :=
  (List.finRange (rowWidth bound machine original + 1)).map
    fun position =>
      flatDuplicatedUnaryField
        (Encodable.encode
          (positive
            ((Fin.last (rowWidth bound machine original) :
                Time (rowWidth bound machine original)),
              position, fiveFamilyVerifierAcceptingSymbol machine)))

private def fiveAcceptanceBundledDescriptorWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  firstFieldSuffix
    (boundedRecordFoldOutput
      (sourceAnchoredGridRecordRotationOutput
        (fiveAcceptanceSourceDescriptorWord
          (fiveFamilyFlatIndexedGridPolynomial bound machine)
          (fiveFamilyVerifierAcceptingSymbol machine).val))
      (fiveAcceptancePositionAnchoredFoldInput
        bound machine original))

private noncomputable def fiveFamilyAcceptanceBundledDescriptorComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveAcceptanceBundledDescriptorWord bound machine) := by
  have catalogue :=
    fiveFamilyAcceptancePositionAnchoredCatalogueComputable
      bound machine
      (fiveFamilyAcceptanceSourceDescriptorComputable
        (fiveFamilyFlatIndexedGridPolynomial bound machine)
        (fiveFamilyVerifierAcceptingSymbol machine).val)
  have physical := GapCVP.TMComposition.computableInPolyTime
    catalogue firstFieldSuffixComputable
  change BitTM
    (fun original => firstFieldSuffix
      (boundedRecordFoldOutput
        (sourceAnchoredGridRecordRotationOutput
          (fiveAcceptanceSourceDescriptorWord
            (fiveFamilyFlatIndexedGridPolynomial bound machine)
            (fiveFamilyVerifierAcceptingSymbol machine).val))
        (fiveAcceptancePositionAnchoredFoldInput
          bound machine original)))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyAcceptanceBundledDescriptorWord_eq
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    fiveAcceptanceBundledDescriptorWord
      bound machine original =
      sourceFlatAtomicDescriptorStream
        (fiveAcceptanceDescriptorRecords
          bound machine original) := by
  unfold fiveAcceptanceBundledDescriptorWord
  rw [fiveFamilyAcceptancePositionAnchoredCatalogueOutput_eq
    bound machine
    (fiveAcceptanceSourceDescriptorWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (fiveFamilyVerifierAcceptingSymbol machine).val)
    original
    (fiveFamilyAcceptanceSourceDescriptor_fits_anchor
      bound machine original)]
  simp only [firstFieldSuffix_valid]
  rw [fiveFamilyAcceptancePositionRankWords_eq_finRange]
  unfold fiveAcceptanceDescriptorRecords
    sourceFlatAtomicDescriptorStream
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro position _
  rw [fiveFamilyAcceptanceSourceDescriptorWord_anchor
    bound machine original position]
  rfl

private def fiveAcceptanceBundledDuplicatedCodeWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  firstFieldSuffix
    (boundedRecordFoldOutput
      (sourceAnchoredGridRecordRotationOutput
        (fiveAcceptanceSourceDuplicatedCodeWord
          (fiveFamilyFlatIndexedGridPolynomial bound machine)
          (fiveFamilyVerifierAcceptingSymbol machine).val))
      (fiveAcceptancePositionAnchoredFoldInput
        bound machine original))

private noncomputable def fiveFamilyAcceptanceBundledDuplicatedCodeComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveAcceptanceBundledDuplicatedCodeWord bound machine) := by
  have catalogue :=
    fiveFamilyAcceptancePositionAnchoredCatalogueComputable
      bound machine
      (fiveFamilyAcceptanceSourceDuplicatedCodeComputable
        (fiveFamilyFlatIndexedGridPolynomial bound machine)
        (fiveFamilyVerifierAcceptingSymbol machine).val)
  have physical := GapCVP.TMComposition.computableInPolyTime
    catalogue firstFieldSuffixComputable
  change BitTM
    (fun original => firstFieldSuffix
      (boundedRecordFoldOutput
        (sourceAnchoredGridRecordRotationOutput
          (fiveAcceptanceSourceDuplicatedCodeWord
            (fiveFamilyFlatIndexedGridPolynomial bound machine)
            (fiveFamilyVerifierAcceptingSymbol machine).val))
        (fiveAcceptancePositionAnchoredFoldInput
          bound machine original)))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyAcceptanceBundledDuplicatedCodeWord_eq
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    fiveAcceptanceBundledDuplicatedCodeWord
      bound machine original =
      sourceFlatAtomicDescriptorStream
        (fiveAcceptanceDuplicatedCodeRecords
          bound machine original) := by
  unfold fiveAcceptanceBundledDuplicatedCodeWord
  rw [fiveFamilyAcceptancePositionAnchoredCatalogueOutput_eq
    bound machine
    (fiveAcceptanceSourceDuplicatedCodeWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (fiveFamilyVerifierAcceptingSymbol machine).val)
    original
    (fiveFamilyAcceptanceSourceDuplicatedCode_fits_anchor
      bound machine original)]
  simp only [firstFieldSuffix_valid]
  rw [fiveFamilyAcceptancePositionRankWords_eq_finRange]
  unfold fiveAcceptanceDuplicatedCodeRecords
    sourceFlatAtomicDescriptorStream
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro position _
  rw [fiveFamilyAcceptanceSourceDuplicatedCodeWord_anchor
    bound machine original position]
  rfl

private def fiveAcceptanceDescriptorUnwrappingInput
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  fiveAcceptancePositionCountWord bound machine original ++
    false :: fiveAcceptanceBundledDescriptorWord
      bound machine original

private noncomputable def fiveFamilyAcceptanceDescriptorUnwrappingInputComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveAcceptanceDescriptorUnwrappingInput bound machine) := by
  have delimited := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyAcceptanceBundledDescriptorComputable bound machine)
    (prependBitComputable false)
  have physical := pointwiseAppendComputable
    (fiveAcceptancePositionCountComputable bound machine)
    delimited
  change BitTM
    (fun original =>
      fiveAcceptancePositionCountWord bound machine original ++
        false :: fiveAcceptanceBundledDescriptorWord
          bound machine original)
  simpa only [Function.comp_apply] using physical

private def fiveAcceptanceDescriptorPayloadWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  boundedRecordFoldOutput sourceFlatAtomicRecordStep
    (fiveAcceptanceDescriptorUnwrappingInput
      bound machine original)

private noncomputable def fiveFamilyAcceptanceDescriptorPayloadComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveAcceptanceDescriptorPayloadWord bound machine) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyAcceptanceDescriptorUnwrappingInputComputable
      bound machine)
    sourceFlatAtomicRecordFoldComputable
  change BitTM
    (fun original => boundedRecordFoldOutput
      sourceFlatAtomicRecordStep
        (fiveAcceptanceDescriptorUnwrappingInput
          bound machine original))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyAcceptanceDescriptorPayloadWord_eq
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    fiveAcceptanceDescriptorPayloadWord
      bound machine original =
      flatSourceClauseDescriptorPayload
        (acceptanceClause
          (T := rowWidth bound machine original)
          (fiveFamilyVerifierAcceptingSymbol machine)) := by
  unfold fiveAcceptanceDescriptorPayloadWord
    fiveAcceptanceDescriptorUnwrappingInput
  rw [fiveFamilyAcceptanceBundledDescriptorWord_eq]
  have hlength :
      (fiveAcceptanceDescriptorRecords
        bound machine original).length =
          rowWidth bound machine original + 1 := by
    simp only [fiveAcceptanceDescriptorRecords, List.length_map, List.length_finRange]
  simp only [fiveAcceptancePositionCountWord,
    fiveFamilyFlatIndexedGridPolynomial_eval]
  rw [← hlength]
  change
    boundedRecordFoldOutput sourceFlatAtomicRecordStep
      (unaryBoundedFoldWord
        (fiveAcceptanceDescriptorRecords
          bound machine original).length
        (sourceFlatAtomicDescriptorStream
          (fiveAcceptanceDescriptorRecords
            bound machine original))) = _
  rw [boundedRecordFoldOutput_sourceFlatAtomicDescriptors]
  unfold fiveAcceptanceDescriptorRecords
    flatSourceClauseDescriptorPayload
  rw [sortedElements_acceptanceClause_eq_finRange]
  simp only [fiveSourceAcceptancePositiveLiteralList,
    flatSignedLiteralDescriptorStream, List.flatten_eq_flatMap,
    List.flatMap_map, List.map_map, Function.comp_def, id_eq]

private def fiveAcceptanceDuplicatedCodeUnwrappingInput
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  fiveAcceptancePositionCountWord bound machine original ++
    false :: fiveAcceptanceBundledDuplicatedCodeWord
      bound machine original

private noncomputable def fiveFamilyAcceptanceDuplicatedCodeUnwrappingInputComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveAcceptanceDuplicatedCodeUnwrappingInput
        bound machine) := by
  have delimited := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyAcceptanceBundledDuplicatedCodeComputable
      bound machine)
    (prependBitComputable false)
  have physical := pointwiseAppendComputable
    (fiveAcceptancePositionCountComputable bound machine)
    delimited
  change BitTM
    (fun original =>
      fiveAcceptancePositionCountWord bound machine original ++
        false :: fiveAcceptanceBundledDuplicatedCodeWord
          bound machine original)
  simpa only [Function.comp_apply] using physical

private def fiveAcceptanceDuplicatedCodePayloadWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  boundedRecordFoldOutput sourceFlatAtomicRecordStep
    (fiveAcceptanceDuplicatedCodeUnwrappingInput
      bound machine original)

private noncomputable def fiveFamilyAcceptanceDuplicatedCodePayloadComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveAcceptanceDuplicatedCodePayloadWord
        bound machine) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyAcceptanceDuplicatedCodeUnwrappingInputComputable
      bound machine)
    sourceFlatAtomicRecordFoldComputable
  change BitTM
    (fun original => boundedRecordFoldOutput
      sourceFlatAtomicRecordStep
        (fiveAcceptanceDuplicatedCodeUnwrappingInput
          bound machine original))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyAcceptanceDuplicatedCodePayloadWord_eq
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    fiveAcceptanceDuplicatedCodePayloadWord
      bound machine original =
      flatSourceClauseDuplicatedCodePayload
        (acceptanceClause
          (T := rowWidth bound machine original)
          (fiveFamilyVerifierAcceptingSymbol machine)) := by
  unfold fiveAcceptanceDuplicatedCodePayloadWord
    fiveAcceptanceDuplicatedCodeUnwrappingInput
  rw [fiveFamilyAcceptanceBundledDuplicatedCodeWord_eq]
  have hlength :
      (fiveAcceptanceDuplicatedCodeRecords
        bound machine original).length =
          rowWidth bound machine original + 1 := by
    simp only [fiveAcceptanceDuplicatedCodeRecords, List.length_map, List.length_finRange]
  simp only [fiveAcceptancePositionCountWord,
    fiveFamilyFlatIndexedGridPolynomial_eval]
  rw [← hlength]
  change
    boundedRecordFoldOutput sourceFlatAtomicRecordStep
      (unaryBoundedFoldWord
        (fiveAcceptanceDuplicatedCodeRecords
          bound machine original).length
        (sourceFlatAtomicDescriptorStream
          (fiveAcceptanceDuplicatedCodeRecords
            bound machine original))) = _
  rw [boundedRecordFoldOutput_sourceFlatAtomicDescriptors]
  unfold fiveAcceptanceDuplicatedCodeRecords
    flatSourceClauseDuplicatedCodePayload flatSourceFinsetCodes
  rw [sortedElements_acceptanceClause_eq_finRange]
  simp only [fiveSourceAcceptancePositiveLiteralList,
    flatDuplicatedUnarySourceStream, List.flatten_eq_flatMap,
    List.flatMap_map, List.map_map, Function.comp_def, id_eq]

/-- GapCVP reduction support. -/
def fiveFlatWholeAcceptanceClauseRecordWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  lengthPrefixedWord
      (fiveAcceptanceDescriptorPayloadWord
        bound machine original) ++
    lengthPrefixedWord
      (fiveAcceptanceDuplicatedCodePayloadWord
        bound machine original) ++
      lengthPrefixedWord
        (fiveAcceptancePositionCountWord
          bound machine original)

/-- GapCVP reduction support. -/
noncomputable def fiveFamilyFlatWholeAcceptanceClauseRecordComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveFlatWholeAcceptanceClauseRecordWord
        bound machine) := by
  have descriptors := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyAcceptanceDescriptorPayloadComputable
      bound machine)
    structuralPrefixWriterComputable
  have codes := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyAcceptanceDuplicatedCodePayloadComputable
      bound machine)
    structuralPrefixWriterComputable
  have count := GapCVP.TMComposition.computableInPolyTime
    (fiveAcceptancePositionCountComputable
      bound machine)
    structuralPrefixWriterComputable
  have physical := pointwiseAppendComputable
    descriptors (pointwiseAppendComputable codes count)
  change BitTM
    (fun original =>
      lengthPrefixedWord
          (fiveAcceptanceDescriptorPayloadWord
            bound machine original) ++
        lengthPrefixedWord
          (fiveAcceptanceDuplicatedCodePayloadWord
            bound machine original) ++
          lengthPrefixedWord
            (fiveAcceptancePositionCountWord
              bound machine original))
  simpa only [List.append_assoc, Function.comp_apply] using physical

theorem fiveFamilyFlatWholeAcceptanceClauseRecordWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    fiveFlatWholeAcceptanceClauseRecordWord
      bound machine original =
      flatSourceClauseAnnotatedRecord
        (acceptanceClause
          (T := rowWidth bound machine original)
          (fiveFamilyVerifierAcceptingSymbol machine)) := by
  unfold fiveFlatWholeAcceptanceClauseRecordWord
    flatSourceClauseAnnotatedRecord
  rw [fiveFamilyAcceptanceDescriptorPayloadWord_eq,
    fiveFamilyAcceptanceDuplicatedCodePayloadWord_eq]
  congr 2
  unfold flatSourceClauseUnaryCountPayload
    fiveAcceptancePositionCountWord
  rw [acceptanceClause_exact_card,
    fiveFamilyFlatIndexedGridPolynomial_eval]

end CNFFiveFamilyFlatAcceptanceClauseFoldTM


end GapCVP

end
