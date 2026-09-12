/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part07B

/-! # GapCVP proof, part 07, continuation 03 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFFiveFamilyForbiddenWindowCoordinateTM

open Computability Turing GapCVP.CL GapCVP.CLCompleteVerifierSimulation GapCVP.CLCellRowBounds

open GapCVP.BinaryEncoding GapCVP.SourceUniformTuringTM GapCVP.SourceMachineCert

open GapCVP.SourceFormulaStructuralDecoder GapCVP.CNFFlatPhysicalBinaryAppendTM

open GapCVP.CNFUnaryPairIndexTM GapCVP.CNFUnaryPairIndexTotalRuntimeCert

open GapCVP.CNFCappedUnaryMinimumTM GapCVP.CNFCappedUnaryMinimumTotalCert

open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM

open GapCVP.CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM

end CNFFiveFamilyForbiddenWindowCoordinateTM

namespace CNFAnnotatedSourceClausePairZipTM

open Turing GapCVP.CNFSourcePairPrefixWorkerTM GapCVP.CNFSourcePairPrefixWorkerTotalCert
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM

/-- Internal support shared across GapCVP continuation modules. -/
def flatAnnotatedSourceZipArchivedPair
    (pair : ℕ × ℕ) : List Bool :=
  flatDuplicatedUnaryField pair.1 ++
    flatDuplicatedUnaryField pair.2

/-- Internal support shared across GapCVP continuation modules. -/
def flatAnnotatedSourceZipHeadPair
    (offset : ℕ) (input : List Bool) : List Bool :=
  sourcePairPrefixOutput (flatAnnotatedSourceFieldAt offset input)

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def annotatedSourceZipHeadPairComputable
    (offset : ℕ) :
    BitTM
      (flatAnnotatedSourceZipHeadPair offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable offset)
    actualSourcePairPrefixComputable
  change BitTM
    (fun input : List Bool =>
      sourcePairPrefixOutput (flatAnnotatedSourceFieldAt offset input))
  exact physical

private def flatAnnotatedSourceZipPendingTail
    (offset : ℕ) (input : List Bool) : List Bool :=
  flatUnaryDropFields 2 (flatAnnotatedSourceFieldAt offset input)

private noncomputable def flatAnnotatedSourceZipPendingTailComputable
    (offset : ℕ) :
    BitTM
      (flatAnnotatedSourceZipPendingTail offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable offset)
    (flatUnaryDropFieldsComputable 2)
  change BitTM
    (fun input : List Bool =>
      flatUnaryDropFields 2
        (flatAnnotatedSourceFieldAt offset input))
  exact physical

private def flatAnnotatedSourceZipNextArchive
    (input : List Bool) : List Bool :=
  flatAnnotatedSourceZipHeadPair 0 input ++
    flatAnnotatedSourceZipHeadPair 1 input ++
      flatAnnotatedSourceFieldAt 2 input

private noncomputable def flatAnnotatedSourceZipNextArchiveComputable :
    BitTM
      flatAnnotatedSourceZipNextArchive := by
  have htail := pointwiseAppendComputable
    (annotatedSourceZipHeadPairComputable 1)
    (annotatedSourceFieldAtComputable 2)
  have physical := pointwiseAppendComputable
    (annotatedSourceZipHeadPairComputable 0) htail
  have hequality :
      (fun input : List Bool =>
        flatAnnotatedSourceZipHeadPair 0 input ++
          (flatAnnotatedSourceZipHeadPair 1 input ++
            flatAnnotatedSourceFieldAt 2 input)) =
        flatAnnotatedSourceZipNextArchive := by
    funext input
    simp only [flatAnnotatedSourceZipNextArchive, List.append_assoc]
  rw [← hequality]
  exact physical

end CNFAnnotatedSourceClausePairZipTM

namespace CNFAnnotatedSourceCountedClausePairZipTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFSourcePairPrefixWorkerTM
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFCappedFlatSourceListFoldTotalCert
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFTypedRecordWorkerTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM GapCVP.CNFAnnotatedSourceClausePairZipTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM

/-- Internal support shared across GapCVP continuation modules. -/
def flatAnnotatedCountedSourceZipState
    (first second : List ℕ)
    (archive suffix : List Bool) : List Bool :=
  lengthPrefixedWord (flatDuplicatedUnarySourceStream first) ++
    lengthPrefixedWord (flatDuplicatedUnarySourceStream second) ++
      lengthPrefixedWord archive ++
        lengthPrefixedWord (List.replicate first.length true) ++
          lengthPrefixedWord (List.replicate second.length true) ++
            suffix

private def countedZipNextCount
    (offset : ℕ) (input : List Bool) : List Bool :=
  List.tail (flatAnnotatedSourceFieldAt offset input)

private noncomputable def flatAnnotatedCountedSourceZipNextCountComputable
    (offset : ℕ) :
    BitTM
      (countedZipNextCount offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable offset)
    dropHeadComputable
  change BitTM
    (fun input : List Bool =>
      List.tail (flatAnnotatedSourceFieldAt offset input))
  exact physical

/-- Internal support shared across GapCVP continuation modules. -/
def flatAnnotatedCountedSourceZipStep
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (flatAnnotatedSourceZipPendingTail 0 input) ++
    lengthPrefixedWord (flatAnnotatedSourceZipPendingTail 1 input) ++
      lengthPrefixedWord (flatAnnotatedSourceZipNextArchive input) ++
        lengthPrefixedWord
            (countedZipNextCount 3 input) ++
          lengthPrefixedWord
              (countedZipNextCount 4 input) ++
            flatAnnotatedSourceFieldTail 5 input

private noncomputable def countedZipPrefixedComputable
    {worker : List Bool → List Bool}
    (computer : BitTM worker) :
    BitTM
      (fun input => lengthPrefixedWord (worker input)) :=
  GapCVP.TMComposition.computableInPolyTime
    computer structuralPrefixWriterComputable

private noncomputable def flatAnnotatedCountedSourceZipStepComputable :
    BitTM
      flatAnnotatedCountedSourceZipStep := by
  have htail := pointwiseAppendComputable
    (countedZipPrefixedComputable
      (flatAnnotatedCountedSourceZipNextCountComputable 4))
    (annotatedSourceFieldTailComputable 5)
  have hsecondCount := pointwiseAppendComputable
    (countedZipPrefixedComputable
      (flatAnnotatedCountedSourceZipNextCountComputable 3))
    htail
  have harchive := pointwiseAppendComputable
    (countedZipPrefixedComputable
      flatAnnotatedSourceZipNextArchiveComputable)
    hsecondCount
  have hsecond := pointwiseAppendComputable
    (countedZipPrefixedComputable
      (flatAnnotatedSourceZipPendingTailComputable 1))
    harchive
  have physical := pointwiseAppendComputable
    (countedZipPrefixedComputable
      (flatAnnotatedSourceZipPendingTailComputable 0))
    hsecond
  have hequality :
      (fun input : List Bool =>
        lengthPrefixedWord
            (flatAnnotatedSourceZipPendingTail 0 input) ++
          (lengthPrefixedWord
              (flatAnnotatedSourceZipPendingTail 1 input) ++
            (lengthPrefixedWord
                (flatAnnotatedSourceZipNextArchive input) ++
              (lengthPrefixedWord
                  (countedZipNextCount 3 input) ++
                (lengthPrefixedWord
                    (countedZipNextCount 4 input) ++
                  flatAnnotatedSourceFieldTail 5 input))))) =
        flatAnnotatedCountedSourceZipStep := by
    funext input
    simp only [flatAnnotatedCountedSourceZipStep, List.append_assoc]
  rw [← hequality]
  exact physical

private theorem flatAnnotatedCountedSourceZipStep_outer
    (first second archive firstCount secondCount suffix : List Bool) :
    flatAnnotatedCountedSourceZipStep
        (lengthPrefixedWord first ++
          lengthPrefixedWord second ++
            lengthPrefixedWord archive ++
              lengthPrefixedWord firstCount ++
                lengthPrefixedWord secondCount ++ suffix) =
      lengthPrefixedWord (flatUnaryDropFields 2 first) ++
        lengthPrefixedWord (flatUnaryDropFields 2 second) ++
          lengthPrefixedWord
              (sourcePairPrefixOutput first ++
                sourcePairPrefixOutput second ++ archive) ++
            lengthPrefixedWord firstCount.tail ++
              lengthPrefixedWord secondCount.tail ++ suffix := by
  simp only [flatAnnotatedCountedSourceZipStep, flatAnnotatedSourceZipPendingTail,
    flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail, List.append_assoc,
        Function.iterate_zero,
    id_eq, firstFieldContents_valid, firstFieldSuffix_valid, flatAnnotatedSourceZipNextArchive,
    flatAnnotatedSourceZipHeadPair, Function.iterate_succ_apply', countedZipNextCount]

@[simp] private theorem flatAnnotatedCountedSourceZipStep_state
    (firstHead secondHead : ℕ)
    (firstTail secondTail : List ℕ)
    (archive suffix : List Bool) :
    flatAnnotatedCountedSourceZipStep
        (flatAnnotatedCountedSourceZipState
          (firstHead :: firstTail)
          (secondHead :: secondTail) archive suffix) =
      flatAnnotatedCountedSourceZipState firstTail secondTail
        (flatAnnotatedSourceZipArchivedPair
          (firstHead, secondHead) ++ archive)
        suffix := by
  unfold flatAnnotatedCountedSourceZipState
  rw [flatAnnotatedCountedSourceZipStep_outer]
  simp only [flatDuplicatedUnarySourceStream, List.flatMap_cons, flatDuplicatedUnaryField,
      flatUnaryDropFields_two_unaryPair, sourcePairPrefixOutput_pair, List.append_assoc,
          List.length_cons,
      List.replicate_succ, List.tail_cons, flatAnnotatedSourceZipArchivedPair]

private theorem flatAnnotatedCountedSourceZipStep_iterate_pairs
    (pairs : List (ℕ × ℕ))
    (firstRemaining secondRemaining : List ℕ)
    (archive suffix : List Bool) :
    ((flatAnnotatedCountedSourceZipStep^[pairs.length])
      (flatAnnotatedCountedSourceZipState
        (pairs.map Prod.fst ++ firstRemaining)
        (pairs.map Prod.snd ++ secondRemaining)
        archive suffix)) =
      flatAnnotatedCountedSourceZipState firstRemaining secondRemaining
        (pairs.reverse.flatMap flatAnnotatedSourceZipArchivedPair ++
          archive)
        suffix := by
  induction pairs generalizing archive with
  | nil => simp only [List.length_nil, List.map_nil, List.nil_append, Function.iterate_zero, id_eq,
      List.reverse_nil,
               List.flatMap_nil]
  | cons pair remaining ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [List.map_cons, List.cons_append]
      rw [flatAnnotatedCountedSourceZipStep_state]
      rw [ih]
      simp only [Prod.mk.eta, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil,
          List.append_nil, List.append_assoc]

private theorem flatAnnotatedCountedSourceZipStep_outer_length_le
    (first second archive firstCount secondCount suffix : List Bool) :
    (flatAnnotatedCountedSourceZipStep
      (lengthPrefixedWord first ++
        lengthPrefixedWord second ++
          lengthPrefixedWord archive ++
            lengthPrefixedWord firstCount ++
              lengthPrefixedWord secondCount ++ suffix)).length ≤
      (lengthPrefixedWord first ++
        lengthPrefixedWord second ++
          lengthPrefixedWord archive ++
            lengthPrefixedWord firstCount ++
              lengthPrefixedWord secondCount ++ suffix).length := by
  rw [flatAnnotatedCountedSourceZipStep_outer]
  have hfirst := sourcePairPrefixOutput_drop_length_le first
  have hsecond := sourcePairPrefixOutput_drop_length_le second
  have hfirstCount : firstCount.tail.length ≤ firstCount.length := by
    simp only [List.length_tail, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
  have hsecondCount : secondCount.tail.length ≤ secondCount.length := by
    simp only [List.length_tail, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
  simp only [List.length_append, lengthPrefixedWord_length] at *
  omega

private theorem flatAnnotatedCountedSourceFieldTail_length_le
    (offset : ℕ) (input : List Bool) :
    (flatAnnotatedSourceFieldTail offset input).length ≤ input.length := by
  induction offset with
  | zero => simp only [flatAnnotatedSourceFieldTail, Function.iterate_zero, id_eq, Std.le_refl]
  | succ offset ih =>
      unfold flatAnnotatedSourceFieldTail
      rw [Function.iterate_succ_apply']
      have hfield := annotatedStructuralFieldAccounting
        ((firstFieldSuffix^[offset]) input)
      change
        (firstFieldSuffix ((firstFieldSuffix^[offset]) input)).length ≤
          input.length
      have hprevious :
          (((firstFieldSuffix^[offset]) input)).length ≤ input.length := by
        simpa only [flatAnnotatedSourceFieldTail] using ih
      omega

private theorem countedFieldAt_length_le
    (offset : ℕ) (input : List Bool) :
    (flatAnnotatedSourceFieldAt offset input).length ≤ input.length := by
  have hfield := annotatedStructuralFieldAccounting
    (flatAnnotatedSourceFieldTail offset input)
  have htail := flatAnnotatedCountedSourceFieldTail_length_le
    offset input
  change
    (firstFieldContents
      (flatAnnotatedSourceFieldTail offset input)).length ≤
      input.length
  omega

private theorem flatAnnotatedCountedSourceZipStep_length_le
    (input : List Bool) :
    (flatAnnotatedCountedSourceZipStep input).length ≤
      15 * input.length + 5 := by
  have hfirst := countedFieldAt_length_le 0 input
  have hsecond := countedFieldAt_length_le 1 input
  have harchive := countedFieldAt_length_le 2 input
  have hfirstCount := countedFieldAt_length_le 3 input
  have hsecondCount := countedFieldAt_length_le 4 input
  have hsuffix := flatAnnotatedCountedSourceFieldTail_length_le 5 input
  have hfirstPair := sourcePairPrefixOutput_drop_length_le
    (flatAnnotatedSourceFieldAt 0 input)
  have hsecondPair := sourcePairPrefixOutput_drop_length_le
    (flatAnnotatedSourceFieldAt 1 input)
  have hfirstTail :
      (List.tail (flatAnnotatedSourceFieldAt 3 input)).length ≤
        (flatAnnotatedSourceFieldAt 3 input).length := by
    simp only [List.length_tail, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
  have hsecondTail :
      (List.tail (flatAnnotatedSourceFieldAt 4 input)).length ≤
        (flatAnnotatedSourceFieldAt 4 input).length := by
    simp only [List.length_tail, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
  simp only [flatAnnotatedCountedSourceZipStep,
    flatAnnotatedSourceZipPendingTail,
    flatAnnotatedSourceZipNextArchive,
    flatAnnotatedSourceZipHeadPair,
    countedZipNextCount,
    List.length_append, lengthPrefixedWord_length]
  omega

private theorem flatAnnotatedCountedSourceZipStep_output_length_le
    (input : List Bool) :
    (flatAnnotatedCountedSourceZipStep
      (flatAnnotatedCountedSourceZipStep input)).length ≤
      (flatAnnotatedCountedSourceZipStep input).length := by
  unfold flatAnnotatedCountedSourceZipStep at ⊢
  exact flatAnnotatedCountedSourceZipStep_outer_length_le
    (flatAnnotatedSourceZipPendingTail 0 input)
    (flatAnnotatedSourceZipPendingTail 1 input)
    (flatAnnotatedSourceZipNextArchive input)
    (countedZipNextCount 3 input)
    (countedZipNextCount 4 input)
    (flatAnnotatedSourceFieldTail 5 input)

private theorem flatAnnotatedCountedSourceZipStep_iterate_length_le
    (input : List Bool) (stage : ℕ) :
    (((flatAnnotatedCountedSourceZipStep^[stage]) input).length) ≤
      15 * input.length + 5 := by
  induction stage with
  | zero =>
      simp only [Function.iterate_zero, id_eq]
      omega
  | succ stage ih =>
      cases stage with
      | zero =>
          simpa only [zero_add, Function.iterate_one]
              using flatAnnotatedCountedSourceZipStep_length_le input
      | succ previous =>
          rw [Function.iterate_succ_apply']
          have hstep := flatAnnotatedCountedSourceZipStep_output_length_le
            ((flatAnnotatedCountedSourceZipStep^[previous]) input)
          have hbounded :
              (flatAnnotatedCountedSourceZipStep
                ((flatAnnotatedCountedSourceZipStep^[previous + 1])
                  input)).length ≤
                (((flatAnnotatedCountedSourceZipStep^[previous + 1])
                  input).length) := by
            simpa only [Function.iterate_succ_apply'] using hstep
          exact hbounded.trans ih

private theorem flatAnnotatedCountedSourceZip_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates
      flatAnnotatedCountedSourceZipStep
      (15 * Polynomial.X + 5) := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage _
  have hseed := parsedUnaryFold_seed_length_le
    input count seed hparse
  have hstage := flatAnnotatedCountedSourceZipStep_iterate_length_le
    seed stage
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      ge_iff_le]
  omega

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def flatAnnotatedCountedSourceZipFoldComputable :
    BitTM
      (boundedRecordFoldOutput flatAnnotatedCountedSourceZipStep) :=
  boundedDependentRecordFoldComputable
    flatAnnotatedCountedSourceZipStepComputable
    (15 * Polynomial.X + 5)
    flatAnnotatedCountedSourceZip_polynomiallyBoundedFoldStates

/-- Internal support shared across GapCVP continuation modules. -/
theorem boundedRecordFoldOutput_flatAnnotatedCountedSourceZipPairs
    (pairs : List (ℕ × ℕ))
    (firstRemaining secondRemaining : List ℕ)
    (archive suffix : List Bool) :
    boundedRecordFoldOutput flatAnnotatedCountedSourceZipStep
        (unaryBoundedFoldWord pairs.length
          (flatAnnotatedCountedSourceZipState
            (pairs.map Prod.fst ++ firstRemaining)
            (pairs.map Prod.snd ++ secondRemaining)
            archive suffix)) =
      flatAnnotatedCountedSourceZipState
        firstRemaining secondRemaining
        (pairs.reverse.flatMap flatAnnotatedSourceZipArchivedPair ++
          archive)
        suffix := by
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word,
      flatAnnotatedCountedSourceZipStep_iterate_pairs]

private def countedPairZipSeed
    (input : List Bool) : List Bool :=
  flatAnnotatedSourcePrefixedField 1 input ++
    flatAnnotatedSourcePrefixedField 4 input ++
      lengthPrefixedWord [] ++
        flatAnnotatedSourcePrefixedField 2 input ++
          flatAnnotatedSourcePrefixedField 5 input ++ input

private noncomputable def flatAnnotatedCountedSourcePairZipSeedComputable :
    BitTM
      countedPairZipSeed := by
  have hsource := Turing.idComputableInPolyTime bitEncoding
  have hsecondCount := pointwiseAppendComputable
    (annotatedSourcePrefixedFieldComputable 5) hsource
  have hfirstCount := pointwiseAppendComputable
    (annotatedSourcePrefixedFieldComputable 2) hsecondCount
  have hempty := pointwiseAppendComputable
    (sourceFixedWordComputable (lengthPrefixedWord [])) hfirstCount
  have hsecond := pointwiseAppendComputable
    (annotatedSourcePrefixedFieldComputable 4) hempty
  have physical := pointwiseAppendComputable
    (annotatedSourcePrefixedFieldComputable 1) hsecond
  have hequality :
      (fun input : List Bool =>
        flatAnnotatedSourcePrefixedField 1 input ++
          (flatAnnotatedSourcePrefixedField 4 input ++
            (lengthPrefixedWord [] ++
              (flatAnnotatedSourcePrefixedField 2 input ++
                (flatAnnotatedSourcePrefixedField 5 input ++ input))))) =
        countedPairZipSeed := by
    funext input
    simp only [countedPairZipSeed, List.append_assoc]
  rw [← hequality]
  exact physical

/-- Internal support shared across GapCVP continuation modules. -/
def countedPairZipPreparationWord
    (input : List Bool) : List Bool :=
  flatAnnotatedSourceZipCountWord input ++
    false :: countedPairZipSeed input

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def flatAnnotatedCountedSourcePairZipPreparationComputable :
    BitTM
      countedPairZipPreparationWord := by
  have hdelimiter := pointwiseAppendComputable
    (sourceFixedWordComputable [false])
    flatAnnotatedCountedSourcePairZipSeedComputable
  have physical := pointwiseAppendComputable
    flatAnnotatedSourceZipCountComputable hdelimiter
  have hequality :
      (fun input : List Bool =>
        flatAnnotatedSourceZipCountWord input ++
          ([false] ++ countedPairZipSeed input)) =
        countedPairZipPreparationWord := by
    funext input
    simp only [List.cons_append, List.nil_append, countedPairZipPreparationWord]
  rw [← hequality]
  exact physical

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem flatAnnotatedCountedSourcePairZipPreparationWord_valid
    (firstClause firstCodes : List Bool) (firstCount : ℕ)
    (secondClause secondCodes : List Bool) (secondCount : ℕ)
    (suffix : List Bool) :
    countedPairZipPreparationWord
        (annotatedSourceAdjacentClauseWord firstClause firstCodes
          firstCount secondClause secondCodes secondCount suffix) =
      unaryBoundedFoldWord (min firstCount secondCount - 1)
        (lengthPrefixedWord firstCodes ++
          lengthPrefixedWord secondCodes ++
            lengthPrefixedWord [] ++
              lengthPrefixedWord (List.replicate firstCount true) ++
                lengthPrefixedWord (List.replicate secondCount true) ++
                  annotatedSourceAdjacentClauseWord
                    firstClause firstCodes firstCount
                    secondClause secondCodes secondCount suffix) := by
  simp only [countedPairZipPreparationWord, flatAnnotatedSourceZipCountWord_valid,
      countedPairZipSeed,
      flatAnnotatedSourcePrefixedField, flatAnnotatedSourceFieldAt_firstCodes,
          flatAnnotatedSourceFieldAt_secondCodes,
      List.append_assoc, flatAnnotatedSourceFieldAt_firstCount,
          flatAnnotatedSourceFieldAt_secondCount,
      unaryBoundedFoldWord]

end CNFAnnotatedSourceCountedClausePairZipTM

namespace CNFAnnotatedSourceUnaryTailReversalTM

open Turing GapCVP.BinaryEncoding GapCVP.FormulaSemanticCert
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceTotalStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFSourcePairPrefixWorkerTM GapCVP.CNFSourcePairPrefixWorkerTotalCert
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFCappedFlatSourceListFoldTotalCert
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFTypedRecordWorkerTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM

private def annotatedUnarySourceReverseState
    (records : List ℕ) (archive suffix : List Bool) : List Bool :=
  lengthPrefixedWord (flatDuplicatedUnarySourceStream records) ++
    lengthPrefixedWord archive ++ suffix

private def annotatedUnarySourceReversePending
    (input : List Bool) : List Bool :=
  flatUnaryDropFields 2 (flatAnnotatedSourceFieldAt 0 input)

private noncomputable def flatAnnotatedUnarySourceReversePendingComputable :
    BitTM
      annotatedUnarySourceReversePending := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable 0)
    (flatUnaryDropFieldsComputable 2)
  change BitTM
    (fun input : List Bool =>
      flatUnaryDropFields 2 (flatAnnotatedSourceFieldAt 0 input))
  exact physical

private def flatAnnotatedUnarySourceReverseHead
    (input : List Bool) : List Bool :=
  sourcePairPrefixOutput (flatAnnotatedSourceFieldAt 0 input)

private noncomputable def flatAnnotatedUnarySourceReverseHeadComputable :
    BitTM
      flatAnnotatedUnarySourceReverseHead := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable 0)
    actualSourcePairPrefixComputable
  change BitTM
    (fun input : List Bool =>
      sourcePairPrefixOutput (flatAnnotatedSourceFieldAt 0 input))
  exact physical

private def annotatedUnarySourceReverseNextArchive
    (input : List Bool) : List Bool :=
  flatAnnotatedUnarySourceReverseHead input ++
    flatAnnotatedSourceFieldAt 1 input

private noncomputable def flatAnnotatedUnarySourceReverseNextArchiveComputable :
    BitTM
      annotatedUnarySourceReverseNextArchive := by
  have physical := pointwiseAppendComputable
    flatAnnotatedUnarySourceReverseHeadComputable
    (annotatedSourceFieldAtComputable 1)
  change BitTM
    (fun input : List Bool =>
      flatAnnotatedUnarySourceReverseHead input ++
        flatAnnotatedSourceFieldAt 1 input)
  exact physical

private def flatAnnotatedUnarySourceReverseStep
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (annotatedUnarySourceReversePending input) ++
    lengthPrefixedWord
      (annotatedUnarySourceReverseNextArchive input) ++
        flatAnnotatedSourceFieldTail 2 input

private noncomputable def flatAnnotatedUnarySourceReverseStepComputable :
    BitTM
      flatAnnotatedUnarySourceReverseStep := by
  have hpending := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedUnarySourceReversePendingComputable
    structuralPrefixWriterComputable
  have harchive := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedUnarySourceReverseNextArchiveComputable
    structuralPrefixWriterComputable
  have hrest := pointwiseAppendComputable harchive
    (annotatedSourceFieldTailComputable 2)
  have physical := pointwiseAppendComputable hpending hrest
  have hequality :
      (fun input : List Bool =>
        lengthPrefixedWord
            (annotatedUnarySourceReversePending input) ++
          (lengthPrefixedWord
              (annotatedUnarySourceReverseNextArchive input) ++
            flatAnnotatedSourceFieldTail 2 input)) =
        flatAnnotatedUnarySourceReverseStep := by
    funext input
    simp only [flatAnnotatedUnarySourceReverseStep, List.append_assoc]
  rw [← hequality]
  exact physical

private theorem flatAnnotatedUnarySourceReverseStep_outer
    (pending archive suffix : List Bool) :
    flatAnnotatedUnarySourceReverseStep
        (lengthPrefixedWord pending ++
          lengthPrefixedWord archive ++ suffix) =
      lengthPrefixedWord (flatUnaryDropFields 2 pending) ++
        lengthPrefixedWord (sourcePairPrefixOutput pending ++ archive) ++
          suffix := by
  simp only [flatAnnotatedUnarySourceReverseStep, annotatedUnarySourceReversePending,
    flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail, List.append_assoc,
        Function.iterate_zero,
    id_eq, firstFieldContents_valid, annotatedUnarySourceReverseNextArchive,
    flatAnnotatedUnarySourceReverseHead, firstFieldSuffix_valid, Function.iterate_succ_apply']

@[simp] private theorem flatAnnotatedUnarySourceReverseStep_state
    (head : ℕ) (remaining : List ℕ)
    (archive suffix : List Bool) :
    flatAnnotatedUnarySourceReverseStep
        (annotatedUnarySourceReverseState
          (head :: remaining) archive suffix) =
      annotatedUnarySourceReverseState remaining
        (flatDuplicatedUnaryField head ++ archive) suffix := by
  unfold annotatedUnarySourceReverseState
  rw [flatAnnotatedUnarySourceReverseStep_outer]
  simp only [flatDuplicatedUnarySourceStream, List.flatMap_cons, flatDuplicatedUnaryField,
      flatUnaryDropFields_two_unaryPair, sourcePairPrefixOutput_pair, List.append_assoc]

private theorem flatAnnotatedUnarySourceReverseStep_iterate_records
    (records : List ℕ) (archive suffix : List Bool) :
    ((flatAnnotatedUnarySourceReverseStep^[records.length])
      (annotatedUnarySourceReverseState records archive suffix)) =
      annotatedUnarySourceReverseState []
        (flatDuplicatedUnarySourceStream records.reverse ++ archive)
        suffix := by
  induction records generalizing archive with
  | nil =>
      simp only [List.length_nil, Function.iterate_zero, id_eq, flatDuplicatedUnarySourceStream,
          List.reverse_nil,
          List.flatMap_nil, List.nil_append]
  | cons head remaining ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      rw [flatAnnotatedUnarySourceReverseStep_state]
      rw [ih]
      simp only [flatDuplicatedUnarySourceStream, List.reverse_cons, List.flatMap_append,
          List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.append_assoc]

private theorem flatAnnotatedUnarySourceReverseStep_outer_length_le
    (pending archive suffix : List Bool) :
    (flatAnnotatedUnarySourceReverseStep
      (lengthPrefixedWord pending ++
        lengthPrefixedWord archive ++ suffix)).length ≤
      (lengthPrefixedWord pending ++
        lengthPrefixedWord archive ++ suffix).length := by
  rw [flatAnnotatedUnarySourceReverseStep_outer]
  have hpending := sourcePairPrefixOutput_drop_length_le pending
  simp only [List.length_append, lengthPrefixedWord_length] at *
  omega

private theorem flatAnnotatedUnarySourceReverseStep_length_le
    (input : List Bool) :
    (flatAnnotatedUnarySourceReverseStep input).length ≤
      input.length + 2 := by
  have hemptyContents : firstFieldContents [] = [] := by rfl
  have hemptySuffix : firstFieldSuffix [] = [] := by rfl
  have hemptyDrop : flatUnaryDropFields 2 [] = [] := by rfl
  have hemptyPair : sourcePairPrefixOutput [] = [] := by rfl
  cases hfirst : readLengthPrefixedWord input with
  | none =>
      have hcontents : firstFieldContents input = [] := by
        simp only [firstFieldContents, payloadDecodeOutput, hfirst, List.tail_cons]
      have hsuffix : firstFieldSuffix input = [] := by
        simp only [firstFieldSuffix, hfirst]
      simp only [flatAnnotatedUnarySourceReverseStep, annotatedUnarySourceReversePending,
        flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail, Function.iterate_zero, id_eq,
        hcontents, hemptyDrop, annotatedUnarySourceReverseNextArchive,
        flatAnnotatedUnarySourceReverseHead, hemptyPair, hsuffix, hemptyContents, List.append_nil,
        Function.iterate_succ_apply', hemptySuffix, List.length_append, lengthPrefixedWord_length,
        List.length_nil, mul_zero, zero_add, Nat.reduceAdd, le_add_iff_nonneg_left, zero_le]
  | some firstParsed =>
      obtain ⟨pending, firstSuffix⟩ := firstParsed
      have hfirstShape := readLengthPrefixedWord_some_reconstruct
        input pending firstSuffix hfirst
      cases hsecond : readLengthPrefixedWord firstSuffix with
      | none =>
          have hcontents : firstFieldContents firstSuffix = [] := by
            simp only [firstFieldContents, payloadDecodeOutput, hsecond, List.tail_cons]
          have hsuffix : firstFieldSuffix firstSuffix = [] := by
            simp only [firstFieldSuffix, hsecond]
          have hpending := sourcePairPrefixOutput_drop_length_le pending
          rw [hfirstShape]
          simp only [hemptyContents, hemptySuffix, hemptyDrop, hemptyPair, hcontents, hsuffix,
            flatAnnotatedUnarySourceReverseStep, annotatedUnarySourceReversePending,
            flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail, Function.iterate_zero, id_eq,
            firstFieldContents_valid, annotatedUnarySourceReverseNextArchive,
            flatAnnotatedUnarySourceReverseHead, firstFieldSuffix_valid, List.append_nil,
            Function.iterate_succ_apply', List.length_append, lengthPrefixedWord_length, ge_iff_le]
                at *
          omega
      | some secondParsed =>
          obtain ⟨archive, suffix⟩ := secondParsed
          have hsecondShape := readLengthPrefixedWord_some_reconstruct
            firstSuffix archive suffix hsecond
          rw [hfirstShape, hsecondShape]
          have hvalid :=
            flatAnnotatedUnarySourceReverseStep_outer_length_le
              pending archive suffix
          simp only [List.append_assoc] at hvalid ⊢
          omega

private theorem flatAnnotatedUnarySourceReverseStep_iterate_length_le
    (input : List Bool) (stage : ℕ) :
    (((flatAnnotatedUnarySourceReverseStep^[stage]) input).length) ≤
      input.length + 2 * stage := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, mul_zero, add_zero, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      have hstep := flatAnnotatedUnarySourceReverseStep_length_le
        ((flatAnnotatedUnarySourceReverseStep^[stage]) input)
      omega

private theorem flatAnnotatedUnarySourceReverse_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates
      flatAnnotatedUnarySourceReverseStep
      (3 * Polynomial.X + 2) := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage hstage
  have hseed := parsedUnaryFold_seed_length_le
    input count seed hparse
  have hcount := parsedUnaryFold_count_le_length
    input count seed hparse
  have hiterate := flatAnnotatedUnarySourceReverseStep_iterate_length_le
    seed stage
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      ge_iff_le]
  omega

private noncomputable def flatAnnotatedUnarySourceReverseFoldComputable :
    BitTM
      (boundedRecordFoldOutput flatAnnotatedUnarySourceReverseStep) :=
  boundedDependentRecordFoldComputable
    flatAnnotatedUnarySourceReverseStepComputable
    (3 * Polynomial.X + 2)
    flatAnnotatedUnarySourceReverse_polynomiallyBoundedFoldStates

private theorem boundedRecordFoldOutput_flatAnnotatedUnarySourceReverse
    (records : List ℕ) (archive suffix : List Bool) :
    boundedRecordFoldOutput flatAnnotatedUnarySourceReverseStep
        (unaryBoundedFoldWord records.length
          (annotatedUnarySourceReverseState records archive suffix)) =
      annotatedUnarySourceReverseState []
        (flatDuplicatedUnarySourceStream records.reverse ++ archive)
        suffix := by
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word,
      flatAnnotatedUnarySourceReverseStep_iterate_records]

end CNFAnnotatedSourceUnaryTailReversalTM

namespace CNFAnnotatedSourceCountedResidualTailTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFUnaryPairIndexTM GapCVP.CNFCappedUnaryMinimumTM
open GapCVP.CNFCappedUnaryPairArithmeticTM GapCVP.CNFFlatSourceOrder
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFCappedFlatSourceListComparatorTM
open GapCVP.CNFSourcePairPrefixWorkerTM GapCVP.CNFSourcePairPrefixWorkerTotalCert
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFAnnotatedSourceCountedClausePairZipTM
open GapCVP.CNFAnnotatedSourceUnaryTailReversalTM

/-- Internal support shared across GapCVP continuation modules. -/
def annotatedCountedResidualTailCount
    (offset : ℕ) (input : List Bool) : List Bool :=
  List.tail (flatAnnotatedSourceFieldAt (offset + 3) input)

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def flatAnnotatedCountedResidualTailCountComputable
    (offset : ℕ) :
    BitTM
      (annotatedCountedResidualTailCount offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable (offset + 3))
    dropHeadComputable
  change BitTM
    (fun input : List Bool =>
      List.tail (flatAnnotatedSourceFieldAt (offset + 3) input))
  exact physical

private def annotatedCountedResidualTailStream
    (offset : ℕ) (input : List Bool) : List Bool :=
  flatUnaryDropFields 2 (flatAnnotatedSourceFieldAt offset input)

private noncomputable def flatAnnotatedCountedResidualTailStreamComputable
    (offset : ℕ) :
    BitTM
      (annotatedCountedResidualTailStream offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable offset)
    (flatUnaryDropFieldsComputable 2)
  change BitTM
    (fun input : List Bool =>
      flatUnaryDropFields 2 (flatAnnotatedSourceFieldAt offset input))
  exact physical

private def annotatedCountedResidualTailReversePreparation
    (offset : ℕ) (input : List Bool) : List Bool :=
  annotatedCountedResidualTailCount offset input ++
    false ::
      (lengthPrefixedWord
        (annotatedCountedResidualTailStream offset input) ++
        lengthPrefixedWord [] ++ input)

private noncomputable def flatAnnotatedCountedResidualTailReversePreparationComputable
    (offset : ℕ) :
    BitTM
      (annotatedCountedResidualTailReversePreparation offset) := by
  have hpending := GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedCountedResidualTailStreamComputable offset)
    structuralPrefixWriterComputable
  have hsource := pointwiseAppendComputable
    (sourceFixedWordComputable (lengthPrefixedWord []))
    (Turing.idComputableInPolyTime bitEncoding)
  have hseed := pointwiseAppendComputable hpending hsource
  have hdelimiter := pointwiseAppendComputable
    (sourceFixedWordComputable [false]) hseed
  have physical := pointwiseAppendComputable
    (flatAnnotatedCountedResidualTailCountComputable offset)
    hdelimiter
  have hequality :
      (fun input : List Bool =>
        annotatedCountedResidualTailCount offset input ++
          ([false] ++
            (lengthPrefixedWord
              (annotatedCountedResidualTailStream offset input) ++
              (lengthPrefixedWord [] ++ input)))) =
        annotatedCountedResidualTailReversePreparation offset := by
    funext input
    simp only [List.cons_append, List.nil_append, annotatedCountedResidualTailReversePreparation,
        List.append_assoc]
  rw [← hequality]
  exact physical

private def annotatedCountedResidualTailReverseOutput
    (offset : ℕ) : List Bool → List Bool :=
  boundedRecordFoldOutput flatAnnotatedUnarySourceReverseStep ∘
    annotatedCountedResidualTailReversePreparation offset

private noncomputable def flatAnnotatedCountedResidualTailReverseComputable
    (offset : ℕ) :
    BitTM
      (annotatedCountedResidualTailReverseOutput offset) :=
  GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedCountedResidualTailReversePreparationComputable offset)
    flatAnnotatedUnarySourceReverseFoldComputable

private def annotatedCountedResidualTailReversedStream
    (offset : ℕ) (input : List Bool) : List Bool :=
  flatAnnotatedSourceFieldAt 1
    (annotatedCountedResidualTailReverseOutput offset input)

private noncomputable def flatAnnotatedCountedResidualTailReversedStreamComputable
    (offset : ℕ) :
    BitTM
      (annotatedCountedResidualTailReversedStream offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedCountedResidualTailReverseComputable offset)
    (annotatedSourceFieldAtComputable 1)
  change BitTM
    (fun input : List Bool =>
      flatAnnotatedSourceFieldAt 1
        (annotatedCountedResidualTailReverseOutput offset input))
  exact physical

@[simp] private theorem flatAnnotatedCountedResidualTailReverseOutput_first
    (head : ℕ) (remaining second : List ℕ)
    (archive suffix : List Bool) :
    annotatedCountedResidualTailReverseOutput 0
        (flatAnnotatedCountedSourceZipState
          (head :: remaining) second archive suffix) =
      annotatedUnarySourceReverseState []
        (flatDuplicatedUnarySourceStream remaining.reverse)
        (flatAnnotatedCountedSourceZipState
          (head :: remaining) second archive suffix) := by
  unfold annotatedCountedResidualTailReverseOutput
  rw [Function.comp_apply]
  have hpreparation :
      annotatedCountedResidualTailReversePreparation 0
          (flatAnnotatedCountedSourceZipState
            (head :: remaining) second archive suffix) =
        unaryBoundedFoldWord remaining.length
          (annotatedUnarySourceReverseState remaining []
            (flatAnnotatedCountedSourceZipState
              (head :: remaining) second archive suffix)) := by
    simp only [annotatedCountedResidualTailReversePreparation, annotatedCountedResidualTailCount,
      flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail, zero_add,
      flatAnnotatedCountedSourceZipState, flatDuplicatedUnarySourceStream, List.flatMap_cons,
      flatDuplicatedUnaryField, List.append_assoc, List.length_cons, List.replicate_succ,
      Function.iterate_succ_apply', firstFieldSuffix_valid, firstFieldContents_valid,
          List.tail_cons,
      annotatedCountedResidualTailStream, Function.iterate_zero, id_eq,
      flatUnaryDropFields_two_unaryPair, unaryBoundedFoldWord, annotatedUnarySourceReverseState]
  rw [hpreparation]
  simpa only [List.append_nil] using
      boundedRecordFoldOutput_flatAnnotatedUnarySourceReverse remaining []
        (flatAnnotatedCountedSourceZipState (head :: remaining) second archive suffix)

@[simp] private theorem flatAnnotatedCountedResidualTailReverseOutput_second
    (first : List ℕ) (head : ℕ) (remaining : List ℕ)
    (archive suffix : List Bool) :
    annotatedCountedResidualTailReverseOutput 1
        (flatAnnotatedCountedSourceZipState
          first (head :: remaining) archive suffix) =
      annotatedUnarySourceReverseState []
        (flatDuplicatedUnarySourceStream remaining.reverse)
        (flatAnnotatedCountedSourceZipState
          first (head :: remaining) archive suffix) := by
  unfold annotatedCountedResidualTailReverseOutput
  rw [Function.comp_apply]
  have hpreparation :
      annotatedCountedResidualTailReversePreparation 1
          (flatAnnotatedCountedSourceZipState
            first (head :: remaining) archive suffix) =
        unaryBoundedFoldWord remaining.length
          (annotatedUnarySourceReverseState remaining []
            (flatAnnotatedCountedSourceZipState
              first (head :: remaining) archive suffix)) := by
    simp [annotatedCountedResidualTailReversePreparation,
      annotatedCountedResidualTailCount,
      annotatedCountedResidualTailStream,
      flatAnnotatedCountedSourceZipState,
      flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
      flatDuplicatedUnarySourceStream, flatDuplicatedUnaryField,
      annotatedUnarySourceReverseState,
      unaryBoundedFoldWord,
      Function.iterate_succ_apply',
      List.replicate_succ, List.append_assoc]
  rw [hpreparation]
  simpa using boundedRecordFoldOutput_flatAnnotatedUnarySourceReverse
    remaining []
      (flatAnnotatedCountedSourceZipState
        first (head :: remaining) archive suffix)

@[simp] private theorem flatAnnotatedCountedResidualTailReversedStream_first
    (head : ℕ) (remaining second : List ℕ)
    (archive suffix : List Bool) :
    annotatedCountedResidualTailReversedStream 0
        (flatAnnotatedCountedSourceZipState
          (head :: remaining) second archive suffix) =
      flatDuplicatedUnarySourceStream remaining.reverse := by
  unfold annotatedCountedResidualTailReversedStream
  rw [flatAnnotatedCountedResidualTailReverseOutput_first]
  simp only [flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
      annotatedUnarySourceReverseState,
      flatDuplicatedUnarySourceStream, List.flatMap_nil, List.append_assoc, Function.iterate_one,
          firstFieldSuffix_valid,
      firstFieldContents_valid]

@[simp] private theorem flatAnnotatedCountedResidualTailReversedStream_second
    (first : List ℕ) (head : ℕ) (remaining : List ℕ)
    (archive suffix : List Bool) :
    annotatedCountedResidualTailReversedStream 1
        (flatAnnotatedCountedSourceZipState
          first (head :: remaining) archive suffix) =
      flatDuplicatedUnarySourceStream remaining.reverse := by
  unfold annotatedCountedResidualTailReversedStream
  rw [flatAnnotatedCountedResidualTailReverseOutput_second]
  simp only [flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
      annotatedUnarySourceReverseState,
      flatDuplicatedUnarySourceStream, List.flatMap_nil, List.append_assoc, Function.iterate_one,
          firstFieldSuffix_valid,
      firstFieldContents_valid]

/-- Internal support shared across GapCVP continuation modules. -/
def annotatedCountedResidualHeadUnary
    (offset : ℕ) (input : List Bool) : List Bool :=
  flatDuplicatedUnaryValueWord (flatAnnotatedSourceFieldAt offset input)

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def flatAnnotatedCountedResidualHeadUnaryComputable
    (offset : ℕ) :
    BitTM
      (annotatedCountedResidualHeadUnary offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable offset)
    flatDuplicatedUnaryValueComputable
  change BitTM
    (fun input : List Bool =>
      flatDuplicatedUnaryValueWord
        (flatAnnotatedSourceFieldAt offset input))
  exact physical

private def annotatedCountedResidualCapUnary
    (offset : ℕ) (input : List Bool) : List Bool :=
  true :: annotatedCountedResidualHeadUnary offset input

private noncomputable def flatAnnotatedCountedResidualCapUnaryComputable
    (offset : ℕ) :
    BitTM
      (annotatedCountedResidualCapUnary offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedCountedResidualHeadUnaryComputable offset)
    (prependBitComputable true)
  change BitTM
    (fun input : List Bool =>
      true :: annotatedCountedResidualHeadUnary offset input)
  exact physical

private def annotatedCountedResidualCapField
    (offset : ℕ) (input : List Bool) : List Bool :=
  annotatedCountedResidualCapUnary offset input ++ [false]

private noncomputable def flatAnnotatedCountedResidualCapFieldComputable
    (offset : ℕ) :
    BitTM
      (annotatedCountedResidualCapField offset) :=
  pointwiseAppendComputable
    (flatAnnotatedCountedResidualCapUnaryComputable offset)
    (sourceFixedWordComputable [false])

private def flatAnnotatedCountedResidualCapPair
    (offset : ℕ) (input : List Bool) : List Bool :=
  annotatedCountedResidualCapField offset input ++
    annotatedCountedResidualCapField offset input

private noncomputable def flatAnnotatedCountedResidualCapPairComputable
    (offset : ℕ) :
    BitTM
      (flatAnnotatedCountedResidualCapPair offset) :=
  pointwiseAppendComputable
    (flatAnnotatedCountedResidualCapFieldComputable offset)
    (flatAnnotatedCountedResidualCapFieldComputable offset)

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem flatAnnotatedCountedResidualHeadUnary_first
    (head : ℕ) (remaining second : List ℕ)
    (archive suffix : List Bool) :
    annotatedCountedResidualHeadUnary 0
        (flatAnnotatedCountedSourceZipState
          (head :: remaining) second archive suffix) =
      List.replicate head true := by
  simp only [annotatedCountedResidualHeadUnary, flatDuplicatedUnaryValueWord,
      flatAnnotatedSourceFieldAt,
      flatAnnotatedSourceFieldTail, flatAnnotatedCountedSourceZipState,
          flatDuplicatedUnarySourceStream,
      List.flatMap_cons, flatDuplicatedUnaryField, List.append_assoc, List.length_cons,
          Function.iterate_zero, id_eq,
      firstFieldContents_valid, cappedUnaryMinimumOutput_pair, min_self]

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem flatAnnotatedCountedResidualHeadUnary_second
    (first : List ℕ) (head : ℕ) (remaining : List ℕ)
    (archive suffix : List Bool) :
    annotatedCountedResidualHeadUnary 1
        (flatAnnotatedCountedSourceZipState
          first (head :: remaining) archive suffix) =
      List.replicate head true := by
  simp only [annotatedCountedResidualHeadUnary, flatDuplicatedUnaryValueWord,
      flatAnnotatedSourceFieldAt,
      flatAnnotatedSourceFieldTail, flatAnnotatedCountedSourceZipState,
          flatDuplicatedUnarySourceStream,
      List.flatMap_cons, flatDuplicatedUnaryField, List.append_assoc, List.length_cons,
          Function.iterate_one,
      firstFieldSuffix_valid, firstFieldContents_valid, cappedUnaryMinimumOutput_pair, min_self]

@[simp] private theorem flatAnnotatedCountedResidualCapPair_first
    (head : ℕ) (remaining second : List ℕ)
    (archive suffix : List Bool) :
    flatAnnotatedCountedResidualCapPair 0
        (flatAnnotatedCountedSourceZipState
          (head :: remaining) second archive suffix) =
      flatDuplicatedUnaryField (head + 1) := by
  simp only [flatAnnotatedCountedResidualCapPair, annotatedCountedResidualCapField,
      annotatedCountedResidualCapUnary, flatAnnotatedCountedResidualHeadUnary_first,
          List.cons_append, List.append_assoc,
      List.nil_append, flatDuplicatedUnaryField, unarySourcePairWord, List.replicate_succ]

@[simp] private theorem flatAnnotatedCountedResidualCapPair_second
    (first : List ℕ) (head : ℕ) (remaining : List ℕ)
    (archive suffix : List Bool) :
    flatAnnotatedCountedResidualCapPair 1
        (flatAnnotatedCountedSourceZipState
          first (head :: remaining) archive suffix) =
      flatDuplicatedUnaryField (head + 1) := by
  simp only [flatAnnotatedCountedResidualCapPair, annotatedCountedResidualCapField,
      annotatedCountedResidualCapUnary, flatAnnotatedCountedResidualHeadUnary_second,
          List.cons_append, List.append_assoc,
      List.nil_append, flatDuplicatedUnaryField, unarySourcePairWord, List.replicate_succ]

private theorem flatAnnotatedCountedResidualCappedStateAssembly
    (cap : ℕ) (records : List ℕ) :
    flatDuplicatedUnaryField cap ++
        sourcePairPrefixOutput
          (flatDuplicatedUnarySourceStream records) ++
          flatDuplicatedUnaryField 0 ++
            flatUnaryDropFields 2
              (flatDuplicatedUnarySourceStream records) =
      flatCappedUnarySourceListState cap 0 records := by
  cases records with
  | nil =>
      simp [flatDuplicatedUnarySourceStream,
        flatCappedUnarySourceListState,
        flatDuplicatedUnaryField,
        sourcePairPrefixOutput, flatUnaryDropFields,
        unaryPrefixSuffixOutput, readUnaryPrefix]
  | cons head remaining =>
      simp [flatDuplicatedUnarySourceStream,
        flatDuplicatedUnaryField,
        flatCappedUnarySourceListState,
        sourcePairPrefixOutput_pair,
        flatUnaryDropFields_two_unaryPair,
        List.append_assoc]

private def annotatedCountedResidualReverseHeadPair
    (offset : ℕ) (input : List Bool) : List Bool :=
  sourcePairPrefixOutput
    (annotatedCountedResidualTailReversedStream offset input)

private noncomputable def flatAnnotatedCountedResidualReverseHeadPairComputable
    (offset : ℕ) :
    BitTM
      (annotatedCountedResidualReverseHeadPair offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedCountedResidualTailReversedStreamComputable offset)
    actualSourcePairPrefixComputable
  change BitTM
    (fun input : List Bool =>
      sourcePairPrefixOutput
        (annotatedCountedResidualTailReversedStream offset input))
  exact physical

private def annotatedCountedResidualReversePending
    (offset : ℕ) (input : List Bool) : List Bool :=
  flatUnaryDropFields 2
    (annotatedCountedResidualTailReversedStream offset input)

private noncomputable def flatAnnotatedCountedResidualReversePendingComputable
    (offset : ℕ) :
    BitTM
      (annotatedCountedResidualReversePending offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedCountedResidualTailReversedStreamComputable offset)
    (flatUnaryDropFieldsComputable 2)
  change BitTM
    (fun input : List Bool =>
      flatUnaryDropFields 2
        (annotatedCountedResidualTailReversedStream offset input))
  exact physical

private def annotatedCountedResidualCappedStateWord
    (offset capOffset : ℕ) (input : List Bool) : List Bool :=
  flatAnnotatedCountedResidualCapPair capOffset input ++
    annotatedCountedResidualReverseHeadPair offset input ++
      flatDuplicatedUnaryField 0 ++
        annotatedCountedResidualReversePending offset input

private noncomputable def flatAnnotatedCountedResidualCappedStateComputable
    (offset capOffset : ℕ) :
    BitTM
      (annotatedCountedResidualCappedStateWord offset capOffset) := by
  have htail := pointwiseAppendComputable
    (sourceFixedWordComputable (flatDuplicatedUnaryField 0))
    (flatAnnotatedCountedResidualReversePendingComputable offset)
  have hhead := pointwiseAppendComputable
    (flatAnnotatedCountedResidualReverseHeadPairComputable offset)
    htail
  have physical := pointwiseAppendComputable
    (flatAnnotatedCountedResidualCapPairComputable capOffset)
    hhead
  have hequality :
      (fun input : List Bool =>
        flatAnnotatedCountedResidualCapPair capOffset input ++
          (annotatedCountedResidualReverseHeadPair offset input ++
            (flatDuplicatedUnaryField 0 ++
              annotatedCountedResidualReversePending offset input))) =
        annotatedCountedResidualCappedStateWord offset capOffset := by
    funext input
    simp only [annotatedCountedResidualCappedStateWord, List.append_assoc]
  rw [← hequality]
  exact physical

@[simp] private theorem flatAnnotatedCountedResidualCappedStateWord_first
    (head : ℕ) (remaining : List ℕ)
    (opposite : ℕ) (secondRemaining : List ℕ)
    (archive suffix : List Bool) :
    annotatedCountedResidualCappedStateWord 0 1
        (flatAnnotatedCountedSourceZipState
          (head :: remaining) (opposite :: secondRemaining)
          archive suffix) =
      flatCappedUnarySourceListState
        (opposite + 1) 0 remaining.reverse := by
  unfold annotatedCountedResidualCappedStateWord
    annotatedCountedResidualReverseHeadPair
    annotatedCountedResidualReversePending
  rw [flatAnnotatedCountedResidualCapPair_second,
    flatAnnotatedCountedResidualTailReversedStream_first]
  exact flatAnnotatedCountedResidualCappedStateAssembly
    (opposite + 1) remaining.reverse

@[simp] private theorem flatAnnotatedCountedResidualCappedStateWord_second
    (opposite : ℕ) (firstRemaining : List ℕ)
    (head : ℕ) (remaining : List ℕ)
    (archive suffix : List Bool) :
    annotatedCountedResidualCappedStateWord 1 0
        (flatAnnotatedCountedSourceZipState
          (opposite :: firstRemaining) (head :: remaining)
          archive suffix) =
      flatCappedUnarySourceListState
        (opposite + 1) 0 remaining.reverse := by
  unfold annotatedCountedResidualCappedStateWord
    annotatedCountedResidualReverseHeadPair
    annotatedCountedResidualReversePending
  rw [flatAnnotatedCountedResidualCapPair_first,
    flatAnnotatedCountedResidualTailReversedStream_second]
  exact flatAnnotatedCountedResidualCappedStateAssembly
    (opposite + 1) remaining.reverse

private def annotatedCountedResidualCappedFoldPreparation
    (offset capOffset : ℕ) (input : List Bool) : List Bool :=
  annotatedCountedResidualTailCount offset input ++
    false :: annotatedCountedResidualCappedStateWord
      offset capOffset input

private noncomputable def flatAnnotatedCountedResidualCappedFoldPreparationComputable
    (offset capOffset : ℕ) :
    BitTM
      (annotatedCountedResidualCappedFoldPreparation
        offset capOffset) := by
  have htail := pointwiseAppendComputable
    (sourceFixedWordComputable [false])
    (flatAnnotatedCountedResidualCappedStateComputable
      offset capOffset)
  have physical := pointwiseAppendComputable
    (flatAnnotatedCountedResidualTailCountComputable offset)
    htail
  have hequality :
      (fun input : List Bool =>
        annotatedCountedResidualTailCount offset input ++
          ([false] ++
            annotatedCountedResidualCappedStateWord
              offset capOffset input)) =
        annotatedCountedResidualCappedFoldPreparation
          offset capOffset := by
    funext input
    simp only [List.cons_append, List.nil_append, annotatedCountedResidualCappedFoldPreparation]
  rw [← hequality]
  exact physical

/-- Internal support shared across GapCVP continuation modules. -/
def annotatedCountedResidualCappedBinaryWord
    (offset capOffset : ℕ) : List Bool → List Bool :=
  fullCappedFlatSourceListBinaryWord ∘
    annotatedCountedResidualCappedFoldPreparation offset capOffset

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def flatAnnotatedCountedResidualCappedBinaryComputable
    (offset capOffset : ℕ) :
    BitTM
      (annotatedCountedResidualCappedBinaryWord offset capOffset) :=
  GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedCountedResidualCappedFoldPreparationComputable
      offset capOffset)
    fullCappedFlatSourceListBinaryComputable

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem flatAnnotatedCountedResidualCappedBinaryWord_first
    (head : ℕ) (remaining : List ℕ)
    (opposite : ℕ) (secondRemaining : List ℕ)
    (archive suffix : List Bool) :
    annotatedCountedResidualCappedBinaryWord 0 1
        (flatAnnotatedCountedSourceZipState
          (head :: remaining) (opposite :: secondRemaining)
          archive suffix) =
      Computability.encodeNat
        (cappedFlatSourceListValue (opposite + 1) remaining) := by
  unfold annotatedCountedResidualCappedBinaryWord
  rw [Function.comp_apply]
  have hprepare :
      annotatedCountedResidualCappedFoldPreparation 0 1
          (flatAnnotatedCountedSourceZipState
            (head :: remaining) (opposite :: secondRemaining)
            archive suffix) =
        unaryBoundedFoldWord remaining.length
          (flatCappedUnarySourceListState
            (opposite + 1) 0 remaining.reverse) := by
    unfold annotatedCountedResidualCappedFoldPreparation
    rw [flatAnnotatedCountedResidualCappedStateWord_first]
    simp [
      annotatedCountedResidualTailCount,
      flatAnnotatedCountedSourceZipState,
      flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
      Function.iterate_succ_apply', List.replicate_succ,
      unaryBoundedFoldWord, List.append_assoc]
  rw [hprepare]
  exact fullCappedFlatSourceListBinaryWord_valid
    (opposite + 1) remaining

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem flatAnnotatedCountedResidualCappedBinaryWord_second
    (opposite : ℕ) (firstRemaining : List ℕ)
    (head : ℕ) (remaining : List ℕ)
    (archive suffix : List Bool) :
    annotatedCountedResidualCappedBinaryWord 1 0
        (flatAnnotatedCountedSourceZipState
          (opposite :: firstRemaining) (head :: remaining)
          archive suffix) =
      Computability.encodeNat
        (cappedFlatSourceListValue (opposite + 1) remaining) := by
  unfold annotatedCountedResidualCappedBinaryWord
  rw [Function.comp_apply]
  have hprepare :
      annotatedCountedResidualCappedFoldPreparation 1 0
          (flatAnnotatedCountedSourceZipState
            (opposite :: firstRemaining) (head :: remaining)
            archive suffix) =
        unaryBoundedFoldWord remaining.length
          (flatCappedUnarySourceListState
            (opposite + 1) 0 remaining.reverse) := by
    unfold annotatedCountedResidualCappedFoldPreparation
    rw [flatAnnotatedCountedResidualCappedStateWord_second]
    simp [
      annotatedCountedResidualTailCount,
      flatAnnotatedCountedSourceZipState,
      flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
      Function.iterate_succ_apply', List.replicate_succ,
      unaryBoundedFoldWord, List.append_assoc]
  rw [hprepare]
  exact fullCappedFlatSourceListBinaryWord_valid
    (opposite + 1) remaining

end CNFAnnotatedSourceCountedResidualTailTM

namespace SourceFourFamilyTaggedPredicateDispatchTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CNFGuardedFiveFamilyTagDispatchTM GapCVP.CNFFlatPhysicalBinaryAppendTM

private def sourceFourFamilyTagStrippedWorkerWord
    (worker : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  worker (firstFieldSuffix input)

private noncomputable def sourceFourFamilyTagStrippedWorkerComputable
    {worker : List Bool → List Bool}
    (computer : BitTM worker) :
    BitTM
      (sourceFourFamilyTagStrippedWorkerWord worker) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable computer
  change BitTM
    (fun input => worker (firstFieldSuffix input))
  exact physical

/-- GapCVP reduction support. -/
def fourFamilyTaggedGuardedWorkerWord
    (tag : List Bool) (worker : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  fixedDelimitedGuardedWorkerWord tag
    (sourceFourFamilyTagStrippedWorkerWord worker) input

/-- GapCVP reduction support. -/
noncomputable def fourFamilyTaggedGuardedWorkerComputable
    (tag : List Bool)
    {worker : List Bool → List Bool}
    (computer : BitTM worker) :
    BitTM
      (fourFamilyTaggedGuardedWorkerWord tag worker) := by
  exact fixedDelimitedGuardedWorkerComputable tag
    (sourceFourFamilyTagStrippedWorkerComputable computer)

@[simp] theorem sourceFourFamilyTaggedGuardedWorkerWord_valid
    (expected actual payload : List Bool)
    (worker : List Bool → List Bool) :
    fourFamilyTaggedGuardedWorkerWord expected worker
        (lengthPrefixedWord actual ++ payload) =
      if expected = actual then worker payload else [] := by
  simp only [fourFamilyTaggedGuardedWorkerWord, fixedDelimitedGuardedWorkerWord,
      fixedDelimitedWordEqualitySelector_valid, decide_eq_true_eq,
          sourceFourFamilyTagStrippedWorkerWord,
      firstFieldSuffix_valid]

/-- GapCVP reduction support. -/
def fourFamilyTaggedPredicateMarker
    (interpolation normalization diagonal clause :
      List Bool → List Bool)
    (input : List Bool) : List Bool :=
  fourFamilyTaggedGuardedWorkerWord
      [false, false] interpolation input ++
    fourFamilyTaggedGuardedWorkerWord
        [false, true] normalization input ++
      fourFamilyTaggedGuardedWorkerWord
          [true, false] diagonal input ++
        fourFamilyTaggedGuardedWorkerWord
          [true, true] clause input

/-- GapCVP reduction support. -/
noncomputable def fourFamilyTaggedPredicateMarkerComputable
    {interpolation normalization diagonal clause :
      List Bool → List Bool}
    (hinterpolation : BitTM interpolation)
    (hnormalization : BitTM normalization)
    (hdiagonal : BitTM diagonal)
    (hclause : BitTM clause) :
    BitTM
      (fourFamilyTaggedPredicateMarker
        interpolation normalization diagonal clause) := by
  have hlast := pointwiseAppendComputable
    (fourFamilyTaggedGuardedWorkerComputable
      [true, false] hdiagonal)
    (fourFamilyTaggedGuardedWorkerComputable
      [true, true] hclause)
  have htail := pointwiseAppendComputable
    (fourFamilyTaggedGuardedWorkerComputable
      [false, true] hnormalization)
    hlast
  have physical := pointwiseAppendComputable
    (fourFamilyTaggedGuardedWorkerComputable
      [false, false] hinterpolation)
    htail
  have hequality :
      (fun input =>
        fourFamilyTaggedGuardedWorkerWord
            [false, false] interpolation input ++
          (fourFamilyTaggedGuardedWorkerWord
              [false, true] normalization input ++
            (fourFamilyTaggedGuardedWorkerWord
                [true, false] diagonal input ++
              fourFamilyTaggedGuardedWorkerWord
                [true, true] clause input))) =
        fourFamilyTaggedPredicateMarker
          interpolation normalization diagonal clause := by
    funext input
    simp only [fourFamilyTaggedPredicateMarker, List.append_assoc]
  rw [← hequality]
  exact physical

@[simp] theorem sourceFourFamilyTaggedPredicateMarker_interpolation
    (interpolation normalization diagonal clause :
      List Bool → List Bool)
    (payload : List Bool) :
    fourFamilyTaggedPredicateMarker
        interpolation normalization diagonal clause
        (lengthPrefixedWord [false, false] ++ payload) =
      interpolation payload := by
  simp only [fourFamilyTaggedPredicateMarker,
      sourceFourFamilyTaggedGuardedWorkerWord_valid, ↓reduceIte, List.cons.injEq,
      Bool.true_eq_false, and_true, and_false, List.append_nil,
      and_self]

@[simp] theorem sourceFourFamilyTaggedPredicateMarker_normalization
    (interpolation normalization diagonal clause :
      List Bool → List Bool)
    (payload : List Bool) :
    fourFamilyTaggedPredicateMarker
        interpolation normalization diagonal clause
        (lengthPrefixedWord [false, true] ++ payload) =
      normalization payload := by
  simp only [fourFamilyTaggedPredicateMarker,
      sourceFourFamilyTaggedGuardedWorkerWord_valid, List.cons.injEq,
      Bool.false_eq_true, and_true, and_false, ↓reduceIte, List.nil_append,
      Bool.true_eq_false, and_self, List.append_nil]

@[simp] theorem sourceFourFamilyTaggedPredicateMarker_diagonal
    (interpolation normalization diagonal clause :
      List Bool → List Bool)
    (payload : List Bool) :
    fourFamilyTaggedPredicateMarker
        interpolation normalization diagonal clause
        (lengthPrefixedWord [true, false] ++ payload) =
      diagonal payload := by
  simp only [fourFamilyTaggedPredicateMarker,
      sourceFourFamilyTaggedGuardedWorkerWord_valid, List.cons.injEq, Bool.false_eq_true, and_true,
          ↓reduceIte,
      Bool.true_eq_false, and_self, List.append_nil, List.nil_append,
      and_false]

@[simp] theorem sourceFourFamilyTaggedPredicateMarker_clause
    (interpolation normalization diagonal clause :
      List Bool → List Bool)
    (payload : List Bool) :
    fourFamilyTaggedPredicateMarker
        interpolation normalization diagonal clause
        (lengthPrefixedWord [true, true] ++ payload) =
      clause payload := by
  simp only [fourFamilyTaggedPredicateMarker,
      sourceFourFamilyTaggedGuardedWorkerWord_valid, List.cons.injEq, Bool.false_eq_true, and_true,
          and_self, ↓reduceIte,
      List.append_nil, and_false, List.nil_append]

end SourceFourFamilyTaggedPredicateDispatchTM

namespace CNFAnnotatedSourceSquareMajorResolutionTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.FormulaSemanticCert
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceTotalStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralPrefixWriter GapCVP.CLStructuralNaturalBinaryWriter
open GapCVP.CNFEncodedClauseSort GapCVP.CNFNaturalOrderComparator
open GapCVP.CNFNaturalOrderCertifiedComparator GapCVP.CNFCappedUnaryMinimumTM
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFCappedFlatSourceListFoldTotalCert
open GapCVP.CNFFlatSourceOrder GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFGuardedFiveFamilyTagDispatchTM GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFAnnotatedSourceClausePairZipTM GapCVP.CNFTypedRecordWorkerTM
open GapCVP.SourceFourFamilyTaggedPredicateDispatchTM

private def flatAnnotatedSquareHeadUnaryWord
    (offset : ℕ) (input : List Bool) : List Bool :=
  flatDuplicatedUnaryValueWord
    (flatUnaryDropFields offset (firstFieldContents input))

private noncomputable def flatAnnotatedSquareHeadUnaryComputable
    (offset : ℕ) :
    BitTM
      (flatAnnotatedSquareHeadUnaryWord offset) := by
  have htail := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable
    (flatUnaryDropFieldsComputable offset)
  have physical := GapCVP.TMComposition.computableInPolyTime
    htail flatDuplicatedUnaryValueComputable
  change BitTM
    (fun input : List Bool =>
      flatDuplicatedUnaryValueWord
        (flatUnaryDropFields offset (firstFieldContents input)))
  simpa only [Function.comp_def] using physical

@[simp] private theorem flatAnnotatedSquareHeadUnaryWord_first
    (first second : ℕ) (archive suffix : List Bool) :
    flatAnnotatedSquareHeadUnaryWord 0
        (lengthPrefixedWord
          (flatAnnotatedSourceZipArchivedPair (first, second) ++
            archive) ++ suffix) =
      List.replicate first true := by
  simp only [flatAnnotatedSquareHeadUnaryWord, flatDuplicatedUnaryValueWord, flatUnaryDropFields,
      flatAnnotatedSourceZipArchivedPair, flatDuplicatedUnaryField, List.append_assoc,
          firstFieldContents_valid,
      Function.iterate_zero, id_eq, cappedUnaryMinimumOutput_pair, min_self]

@[simp] private theorem flatAnnotatedSquareHeadUnaryWord_second
    (first second : ℕ) (archive suffix : List Bool) :
    flatAnnotatedSquareHeadUnaryWord 2
        (lengthPrefixedWord
          (flatAnnotatedSourceZipArchivedPair (first, second) ++
            archive) ++ suffix) =
      List.replicate second true := by
  simp only [flatAnnotatedSquareHeadUnaryWord, flatDuplicatedUnaryValueWord,
      flatAnnotatedSourceZipArchivedPair,
      flatDuplicatedUnaryField, List.append_assoc, firstFieldContents_valid,
          flatUnaryDropFields_two_unaryPair,
      cappedUnaryMinimumOutput_pair, min_self]

private def flatAnnotatedSquareHeadBinaryWord
    (offset : ℕ) (input : List Bool) : List Bool :=
  Computability.encodeNat
    (flatAnnotatedSquareHeadUnaryWord offset input).length

private noncomputable def flatAnnotatedSquareHeadBinaryComputable
    (offset : ℕ) :
    BitTM
      (flatAnnotatedSquareHeadBinaryWord offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedSquareHeadUnaryComputable offset)
    structuralNaturalBinaryWriterComputable
  change BitTM
    (fun input : List Bool =>
      Computability.encodeNat
        (flatAnnotatedSquareHeadUnaryWord offset input).length)
  simpa only [Function.comp_def] using physical

private def annotatedSquareHeadComparisonInput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (flatAnnotatedSquareHeadBinaryWord 0 input) ++
    lengthPrefixedWord (flatAnnotatedSquareHeadBinaryWord 2 input) ++
      input

private noncomputable def flatAnnotatedSquareHeadComparisonInputComputable :
    BitTM
      annotatedSquareHeadComparisonInput := by
  have hfirst := GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedSquareHeadBinaryComputable 0)
    structuralPrefixWriterComputable
  have hsecond := GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedSquareHeadBinaryComputable 2)
    structuralPrefixWriterComputable
  have htail := pointwiseAppendComputable hsecond
    (Turing.idComputableInPolyTime bitEncoding)
  have physical := pointwiseAppendComputable hfirst htail
  have hequality :
      (fun input : List Bool =>
        lengthPrefixedWord
          (flatAnnotatedSquareHeadBinaryWord 0 input) ++
          (lengthPrefixedWord
            (flatAnnotatedSquareHeadBinaryWord 2 input) ++ input)) =
        annotatedSquareHeadComparisonInput := by
    funext input
    simp only [annotatedSquareHeadComparisonInput, List.append_assoc]
  rw [← hequality]
  exact physical

private def flatAnnotatedSquareHeadOrderingWord
    (input : List Bool) : List Bool :=
  firstFieldSuffix
    (sourcePreservingDelimitedNaturalComparisonWord
      (annotatedSquareHeadComparisonInput input))

private noncomputable def flatAnnotatedSquareHeadOrderingComputable :
    BitTM
      flatAnnotatedSquareHeadOrderingWord := by
  have hcomparison := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedSquareHeadComparisonInputComputable
    sourcePreservingDelimitedNaturalComparisonComputable
  have physical := GapCVP.TMComposition.computableInPolyTime
    hcomparison firstFieldSuffixComputable
  change BitTM
    (fun input : List Bool =>
      firstFieldSuffix
        (sourcePreservingDelimitedNaturalComparisonWord
          (annotatedSquareHeadComparisonInput input)))
  simpa only [Function.comp_def] using physical

@[simp] private theorem flatAnnotatedSquareHeadOrderingWord_valid
    (first second : ℕ) (archive suffix : List Bool) :
    flatAnnotatedSquareHeadOrderingWord
        (lengthPrefixedWord
          (flatAnnotatedSourceZipArchivedPair (first, second) ++
            archive) ++ suffix) =
      encodedWordOrderingWord
        (flatSourceNaturalOrdering first second) := by
  simp only [flatAnnotatedSquareHeadOrderingWord, sourcePreservingDelimitedNaturalComparisonWord,
      annotatedSquareHeadComparisonInput, flatAnnotatedSquareHeadBinaryWord,
          flatAnnotatedSquareHeadUnaryWord_first,
      List.length_replicate, flatAnnotatedSquareHeadUnaryWord_second, List.append_assoc,
          firstFieldSuffix_valid,
      flatSourceNaturalOrdering]
  simpa only [List.append_assoc] using
    congrArg encodedWordOrderingWord
      (delimitedNaturalPairOrdering_encodeNat first second
        (lengthPrefixedWord
          (flatAnnotatedSourceZipArchivedPair (first, second) ++
            archive) ++ suffix))

private theorem flatAnnotatedSquareHeadOrderingWord_length
    (input : List Bool) :
    (flatAnnotatedSquareHeadOrderingWord input).length = 2 := by
  simp only [flatAnnotatedSquareHeadOrderingWord, sourcePreservingDelimitedNaturalComparisonWord,
      encodedWordOrderingWord, firstFieldSuffix_valid, List.length_cons, List.length_nil, zero_add,
          Nat.reduceAdd]

/-- Internal support shared across GapCVP continuation modules. -/
def annotatedSquareResolvedOrderingWord
    (input : List Bool) : List Bool :=
  fourFamilyTaggedPredicateMarker
    (fun _ : List Bool => encodedWordOrderingWord .invalid)
    (fun _ : List Bool => encodedWordOrderingWord .less)
    flatAnnotatedSquareHeadOrderingWord
    (fun _ : List Bool => encodedWordOrderingWord .greater)
    input

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def flatAnnotatedSquareResolvedOrderingComputable :
    BitTM
      annotatedSquareResolvedOrderingWord :=
  fourFamilyTaggedPredicateMarkerComputable
    (sourceFixedWordComputable (encodedWordOrderingWord .invalid))
    (sourceFixedWordComputable (encodedWordOrderingWord .less))
    flatAnnotatedSquareHeadOrderingComputable
    (sourceFixedWordComputable (encodedWordOrderingWord .greater))

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAnnotatedSquareResolvedOrderingWord_valid
    (major : EncodedWordOrdering)
    (first second : ℕ) (archive suffix : List Bool) :
    annotatedSquareResolvedOrderingWord
        (lengthPrefixedWord (encodedWordOrderingWord major) ++
          lengthPrefixedWord
            (flatAnnotatedSourceZipArchivedPair (first, second) ++
              archive) ++ suffix) =
      encodedWordOrderingWord
        (resolveFlatSourceOrder major first second) := by
  let payload := lengthPrefixedWord
    (flatAnnotatedSourceZipArchivedPair (first, second) ++ archive) ++
      suffix
  cases major with
  | invalid =>
      simpa only [annotatedSquareResolvedOrderingWord, encodedWordOrderingWord,
          encodedWordOrderingFirst,
          encodedWordOrderingSecond, List.append_assoc, resolveFlatSourceOrder,
          payload] using
          (sourceFourFamilyTaggedPredicateMarker_interpolation (fun _ : List Bool
              => encodedWordOrderingWord .invalid)
            (fun _ : List Bool => encodedWordOrderingWord .less)
                flatAnnotatedSquareHeadOrderingWord
            (fun _ : List Bool => encodedWordOrderingWord .greater) payload)
  | less =>
      simpa only [annotatedSquareResolvedOrderingWord, encodedWordOrderingWord,
          encodedWordOrderingFirst,
          encodedWordOrderingSecond, List.append_assoc, resolveFlatSourceOrder,
          payload] using
          (sourceFourFamilyTaggedPredicateMarker_normalization (fun _ : List Bool
              => encodedWordOrderingWord .invalid)
            (fun _ : List Bool => encodedWordOrderingWord .less)
                flatAnnotatedSquareHeadOrderingWord
            (fun _ : List Bool => encodedWordOrderingWord .greater) payload)
  | equal =>
      have hdispatch :=
        sourceFourFamilyTaggedPredicateMarker_diagonal
          (fun _ : List Bool => encodedWordOrderingWord .invalid)
          (fun _ : List Bool => encodedWordOrderingWord .less)
          flatAnnotatedSquareHeadOrderingWord
          (fun _ : List Bool => encodedWordOrderingWord .greater)
          payload
      have hhead := flatAnnotatedSquareHeadOrderingWord_valid
        first second archive suffix
      simpa only [annotatedSquareResolvedOrderingWord, encodedWordOrderingWord,
          encodedWordOrderingFirst,
          encodedWordOrderingSecond, List.append_assoc, resolveFlatSourceOrder, payload] using
          hdispatch.trans hhead
  | greater =>
      simpa only [annotatedSquareResolvedOrderingWord, encodedWordOrderingWord,
          encodedWordOrderingFirst,
          encodedWordOrderingSecond, List.append_assoc, resolveFlatSourceOrder, payload] using
          (sourceFourFamilyTaggedPredicateMarker_clause (fun _ : List Bool
              => encodedWordOrderingWord .invalid)
            (fun _ : List Bool => encodedWordOrderingWord .less)
                flatAnnotatedSquareHeadOrderingWord
            (fun _ : List Bool => encodedWordOrderingWord .greater) payload)

private theorem flatAnnotatedSquareResolvedOrderingWord_length_le
    (input : List Bool) :
    (annotatedSquareResolvedOrderingWord input).length ≤ 2 := by
  let invalid : List Bool → List Bool :=
    fun _ => encodedWordOrderingWord .invalid
  let less : List Bool → List Bool :=
    fun _ => encodedWordOrderingWord .less
  let greater : List Bool → List Bool :=
    fun _ => encodedWordOrderingWord .greater
  cases hread : readLengthPrefixedWord input with
  | none =>
      simp only [annotatedSquareResolvedOrderingWord, fourFamilyTaggedPredicateMarker,
          fourFamilyTaggedGuardedWorkerWord, fixedDelimitedGuardedWorkerWord,
              fixedDelimitedWordEqualitySelector,
          delimitedPairWordOrdering, readLengthPrefixedWord_append, hread, reduceCtorEq,
          decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil,
          List.length_nil, zero_le]
  | some parsed =>
      obtain ⟨tag, suffix⟩ := parsed
      have hshape := readLengthPrefixedWord_some_reconstruct
        input tag suffix hread
      rw [hshape]
      change
        (fourFamilyTaggedPredicateMarker
          invalid less flatAnnotatedSquareHeadOrderingWord greater
          (lengthPrefixedWord tag ++ suffix)).length ≤ 2
      by_cases hfirst : tag = [false, false]
      · subst tag
        rw [sourceFourFamilyTaggedPredicateMarker_interpolation]
        simp only [encodedWordOrderingWord, List.length_cons, List.length_nil, zero_add,
            Nat.reduceAdd, Std.le_refl,
            invalid]
      · by_cases hsecond : tag = [false, true]
        · subst tag
          rw [sourceFourFamilyTaggedPredicateMarker_normalization]
          simp only [encodedWordOrderingWord, List.length_cons, List.length_nil, zero_add,
              Nat.reduceAdd, Std.le_refl,
              less]
        · by_cases hthird : tag = [true, false]
          · subst tag
            rw [sourceFourFamilyTaggedPredicateMarker_diagonal]
            simp only [flatAnnotatedSquareHeadOrderingWord_length, Std.le_refl]
          · by_cases hfourth : tag = [true, true]
            · subst tag
              rw [sourceFourFamilyTaggedPredicateMarker_clause]
              simp only [encodedWordOrderingWord, List.length_cons, List.length_nil, zero_add,
                  Nat.reduceAdd, Std.le_refl,
                  greater]
            · simp only [fourFamilyTaggedPredicateMarker, fourFamilyTaggedGuardedWorkerWord,
                  fixedDelimitedGuardedWorkerWord, fixedDelimitedWordEqualitySelector_valid,
                  eq_comm, hfirst, decide_false, Bool.false_eq_true, ↓reduceIte, hsecond,
                  List.append_nil, hthird, hfourth, List.length_nil, zero_le]

/-- Internal support shared across GapCVP continuation modules. -/
def flatAnnotatedSquareResolutionState
    (major : EncodedWordOrdering)
    (archive suffix : List Bool) : List Bool :=
  lengthPrefixedWord (encodedWordOrderingWord major) ++
    lengthPrefixedWord archive ++ suffix

private def annotatedSquareResolutionPending
    (input : List Bool) : List Bool :=
  flatUnaryDropFields 4 (flatAnnotatedSourceFieldAt 1 input)

private noncomputable def flatAnnotatedSquareResolutionPendingComputable :
    BitTM
      annotatedSquareResolutionPending := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable 1)
    (flatUnaryDropFieldsComputable 4)
  change BitTM
    (fun input : List Bool =>
      flatUnaryDropFields 4
        (flatAnnotatedSourceFieldAt 1 input))
  exact physical

/-- Internal support shared across GapCVP continuation modules. -/
def flatAnnotatedSquareResolutionStep
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (annotatedSquareResolvedOrderingWord input) ++
    lengthPrefixedWord (annotatedSquareResolutionPending input) ++
      flatAnnotatedSourceFieldTail 2 input

private noncomputable def flatAnnotatedSquareResolutionStepComputable :
    BitTM
      flatAnnotatedSquareResolutionStep := by
  have hmajor := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedSquareResolvedOrderingComputable
    structuralPrefixWriterComputable
  have hpending := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedSquareResolutionPendingComputable
    structuralPrefixWriterComputable
  have htail := pointwiseAppendComputable hpending
    (annotatedSourceFieldTailComputable 2)
  have physical := pointwiseAppendComputable hmajor htail
  have hequality :
      (fun input : List Bool =>
        lengthPrefixedWord
            (annotatedSquareResolvedOrderingWord input) ++
          (lengthPrefixedWord
              (annotatedSquareResolutionPending input) ++
            flatAnnotatedSourceFieldTail 2 input)) =
        flatAnnotatedSquareResolutionStep := by
    funext input
    simp only [flatAnnotatedSquareResolutionStep, List.append_assoc]
  rw [← hequality]
  exact physical

@[simp] private theorem flatAnnotatedSquareResolutionStep_state
    (major : EncodedWordOrdering)
    (first second : ℕ) (archive suffix : List Bool) :
    flatAnnotatedSquareResolutionStep
        (flatAnnotatedSquareResolutionState major
          (flatAnnotatedSourceZipArchivedPair (first, second) ++ archive)
          suffix) =
      flatAnnotatedSquareResolutionState
        (resolveFlatSourceOrder major first second)
        archive suffix := by
  unfold flatAnnotatedSquareResolutionState
    flatAnnotatedSquareResolutionStep
  rw [flatAnnotatedSquareResolvedOrderingWord_valid]
  simp [annotatedSquareResolutionPending,
    flatAnnotatedSourceFieldAt,
    flatAnnotatedSourceFieldTail,
    flatAnnotatedSourceZipArchivedPair,
    flatDuplicatedUnaryField,
    Function.iterate_succ_apply', List.append_assoc]
  simpa only [List.append_assoc] using
    congrArg lengthPrefixedWord
      (flatUnaryDropFields_four_unaryPairs
        first first second second archive)

private theorem flatAnnotatedSquareResolutionStep_iterate_pairs
    (major : EncodedWordOrdering)
    (pairs : List (ℕ × ℕ))
    (archive suffix : List Bool) :
    ((flatAnnotatedSquareResolutionStep^[pairs.length])
      (flatAnnotatedSquareResolutionState major
        (pairs.flatMap flatAnnotatedSourceZipArchivedPair ++ archive)
        suffix)) =
      flatAnnotatedSquareResolutionState
        (pairs.foldl
          (fun current pair =>
            resolveFlatSourceOrder current pair.1 pair.2)
          major)
        archive suffix := by
  induction pairs generalizing major with
  | nil => simp only [List.length_nil, List.flatMap_nil, List.nil_append, Function.iterate_zero,
      id_eq, List.foldl_nil]
  | cons pair remaining ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [List.flatMap_cons, List.append_assoc]
      rw [flatAnnotatedSquareResolutionStep_state]
      simpa only [List.foldl_cons] using ih (resolveFlatSourceOrder major pair.1 pair.2)

private theorem flatAnnotatedSquareResolutionStep_outer
    (major archive suffix : List Bool) :
    flatAnnotatedSquareResolutionStep
        (lengthPrefixedWord major ++
          lengthPrefixedWord archive ++ suffix) =
      lengthPrefixedWord
        (annotatedSquareResolvedOrderingWord
          (lengthPrefixedWord major ++
            lengthPrefixedWord archive ++ suffix)) ++
        lengthPrefixedWord
          (flatUnaryDropFields 4 archive) ++ suffix := by
  simp [flatAnnotatedSquareResolutionStep,
    annotatedSquareResolutionPending,
    flatAnnotatedSourceFieldAt,
    flatAnnotatedSourceFieldTail,
    Function.iterate_succ_apply', List.append_assoc]

private theorem flatAnnotatedSquareResolutionStep_outer_length_le
    (major archive suffix : List Bool) :
    (flatAnnotatedSquareResolutionStep
      (lengthPrefixedWord major ++
        lengthPrefixedWord archive ++ suffix)).length ≤
      (lengthPrefixedWord major ++
        lengthPrefixedWord archive ++ suffix).length + 4 := by
  rw [flatAnnotatedSquareResolutionStep_outer]
  have houtcome := flatAnnotatedSquareResolvedOrderingWord_length_le
    (lengthPrefixedWord major ++
      lengthPrefixedWord archive ++ suffix)
  have hpending := flatUnaryDropFields_length_le 4 archive
  simp only [List.length_append, lengthPrefixedWord_length] at *
  omega

private theorem flatAnnotatedSquareResolutionStep_length_le
    (input : List Bool) :
    (flatAnnotatedSquareResolutionStep input).length ≤
      input.length + 6 := by
  have hemptyContents : firstFieldContents [] = [] := by rfl
  have hemptySuffix : firstFieldSuffix [] = [] := by rfl
  have hemptyDrop : flatUnaryDropFields 4 [] = [] := by rfl
  cases hfirst : readLengthPrefixedWord input with
  | none =>
      have hcontents : firstFieldContents input = [] := by
        simp [firstFieldContents, payloadDecodeOutput, hfirst]
      have hsuffix : firstFieldSuffix input = [] := by
        simp [firstFieldSuffix, hfirst]
      have houtcome :=
        flatAnnotatedSquareResolvedOrderingWord_length_le input
      simp [flatAnnotatedSquareResolutionStep,
        annotatedSquareResolutionPending,
        flatAnnotatedSourceFieldAt,
        flatAnnotatedSourceFieldTail,
        hcontents, hsuffix, hemptyContents, hemptySuffix,
        hemptyDrop, Function.iterate_succ_apply',
        lengthPrefixedWord_length, List.length_append] at *
      omega
  | some firstParsed =>
      obtain ⟨major, firstSuffix⟩ := firstParsed
      have hfirstShape := readLengthPrefixedWord_some_reconstruct
        input major firstSuffix hfirst
      cases hsecond : readLengthPrefixedWord firstSuffix with
      | none =>
          have hcontents : firstFieldContents firstSuffix = [] := by
            simp [firstFieldContents, payloadDecodeOutput, hsecond]
          have hsuffix : firstFieldSuffix firstSuffix = [] := by
            simp [firstFieldSuffix, hsecond]
          have houtcome :=
            flatAnnotatedSquareResolvedOrderingWord_length_le input
          rw [hfirstShape] at houtcome ⊢
          simp [flatAnnotatedSquareResolutionStep,
            annotatedSquareResolutionPending,
            flatAnnotatedSourceFieldAt,
            flatAnnotatedSourceFieldTail,
            hcontents, hsuffix, hemptyContents, hemptySuffix,
            hemptyDrop, Function.iterate_succ_apply',
            lengthPrefixedWord_length, List.length_append] at *
          omega
      | some secondParsed =>
          obtain ⟨archive, suffix⟩ := secondParsed
          have hsecondShape := readLengthPrefixedWord_some_reconstruct
            firstSuffix archive suffix hsecond
          rw [hfirstShape, hsecondShape]
          have hvalid := flatAnnotatedSquareResolutionStep_outer_length_le
            major archive suffix
          simp only [List.append_assoc] at hvalid ⊢
          omega

private theorem flatAnnotatedSquareResolutionStep_iterate_length_le
    (input : List Bool) (stage : ℕ) :
    (((flatAnnotatedSquareResolutionStep^[stage]) input).length) ≤
      input.length + 6 * stage := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, mul_zero, add_zero, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      have hstep := flatAnnotatedSquareResolutionStep_length_le
        ((flatAnnotatedSquareResolutionStep^[stage]) input)
      omega

private theorem flatAnnotatedSquareResolution_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates
      flatAnnotatedSquareResolutionStep
      (7 * Polynomial.X + 6) := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage hstage
  have hseed := parsedUnaryFold_seed_length_le
    input count seed hparse
  have hcount := parsedUnaryFold_count_le_length
    input count seed hparse
  have hiterate := flatAnnotatedSquareResolutionStep_iterate_length_le
    seed stage
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      ge_iff_le]
  omega

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def flatAnnotatedSquareResolutionFoldComputable :
    BitTM
      (boundedRecordFoldOutput flatAnnotatedSquareResolutionStep) :=
  boundedDependentRecordFoldComputable
    flatAnnotatedSquareResolutionStepComputable
    (7 * Polynomial.X + 6)
    flatAnnotatedSquareResolution_polynomiallyBoundedFoldStates

/-- Internal support shared across GapCVP continuation modules. -/
theorem boundedRecordFoldOutput_flatAnnotatedSquareResolution
    (major : EncodedWordOrdering)
    (pairs : List (ℕ × ℕ))
    (archive suffix : List Bool) :
    boundedRecordFoldOutput flatAnnotatedSquareResolutionStep
        (unaryBoundedFoldWord pairs.length
          (flatAnnotatedSquareResolutionState major
            (pairs.flatMap flatAnnotatedSourceZipArchivedPair ++ archive)
            suffix)) =
      flatAnnotatedSquareResolutionState
        (pairs.foldl
          (fun current pair =>
            resolveFlatSourceOrder current pair.1 pair.2)
          major)
        archive suffix := by
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word,
      flatAnnotatedSquareResolutionStep_iterate_pairs]

end CNFAnnotatedSourceSquareMajorResolutionTM

end GapCVP

end
