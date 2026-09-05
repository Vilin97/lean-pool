/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part07C

/-! # GapCVP proof, part 07, continuation 04 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

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

end CNFAnnotatedSourceSquareMajorResolutionTM

namespace CNFAnnotatedSourceCompleteFiniteSetComparatorTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralPrefixWriter GapCVP.CLStructuralNaturalBinaryWriter
open GapCVP.CNFEncodedClauseSort GapCVP.CNFNaturalOrderComparator
open GapCVP.CNFNaturalOrderCertifiedComparator GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM GapCVP.CNFAnnotatedSourceClausePairZipTM
open GapCVP.CNFAnnotatedSourceCountedClausePairZipTM
open GapCVP.CNFAnnotatedSourceCountedResidualTailTM
open GapCVP.CNFAnnotatedSourceSquareMajorResolutionTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.SourceFourFamilyTaggedPredicateDispatchTM

private def annotatedCompleteSourceZippedWord : List Bool → List Bool :=
  boundedRecordFoldOutput flatAnnotatedCountedSourceZipStep ∘
    countedPairZipPreparationWord

private noncomputable def flatAnnotatedCompleteSourceZippedComputable :
    BitTM
      annotatedCompleteSourceZippedWord :=
  GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCountedSourcePairZipPreparationComputable
    flatAnnotatedCountedSourceZipFoldComputable

private def annotatedCompleteResidualHeadBinary
    (offset : ℕ) (input : List Bool) : List Bool :=
  Computability.encodeNat
    (annotatedCountedResidualHeadUnary offset input).length

private noncomputable def annotatedCompleteResidualHeadBinaryComputable
    (offset : ℕ) :
    BitTM
      (annotatedCompleteResidualHeadBinary offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedCountedResidualHeadUnaryComputable offset)
    structuralNaturalBinaryWriterComputable
  change BitTM
    (fun input : List Bool =>
      Computability.encodeNat
        (annotatedCountedResidualHeadUnary offset input).length)
  exact physical

private def annotatedCompleteNaturalComparisonInput
    (first second : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (first input) ++
    lengthPrefixedWord (second input) ++ input

private noncomputable def flatAnnotatedCompleteNaturalComparisonInputComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (annotatedCompleteNaturalComparisonInput first second) := by
  have hleft := GapCVP.TMComposition.computableInPolyTime
    hfirst structuralPrefixWriterComputable
  have hright := GapCVP.TMComposition.computableInPolyTime
    hsecond structuralPrefixWriterComputable
  have htail := pointwiseAppendComputable hright
    (Turing.idComputableInPolyTime bitEncoding)
  have physical := pointwiseAppendComputable hleft htail
  have hequality :
      (fun input : List Bool =>
        lengthPrefixedWord (first input) ++
          (lengthPrefixedWord (second input) ++ input)) =
        annotatedCompleteNaturalComparisonInput first second := by
    funext input
    simp only [annotatedCompleteNaturalComparisonInput, List.append_assoc]
  rw [← hequality]
  exact physical

private def annotatedCompleteNaturalOrderingWord
    (first second : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  firstFieldSuffix
    (sourcePreservingDelimitedNaturalComparisonWord
      (annotatedCompleteNaturalComparisonInput
        first second input))

private noncomputable def flatAnnotatedCompleteNaturalOrderingComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (annotatedCompleteNaturalOrderingWord first second) := by
  have hcomparison := GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedCompleteNaturalComparisonInputComputable
      hfirst hsecond)
    sourcePreservingDelimitedNaturalComparisonComputable
  have physical := GapCVP.TMComposition.computableInPolyTime
    hcomparison firstFieldSuffixComputable
  change BitTM
    (fun input : List Bool =>
      firstFieldSuffix
        (sourcePreservingDelimitedNaturalComparisonWord
          (annotatedCompleteNaturalComparisonInput
            first second input)))
  exact physical

private def annotatedCompleteResidualHeadPair
    (input : List Bool) : List Bool :=
  flatAnnotatedSourceZipHeadPair 0 input ++
    flatAnnotatedSourceZipHeadPair 1 input

private noncomputable def flatAnnotatedCompleteResidualHeadPairComputable :
    BitTM
      annotatedCompleteResidualHeadPair :=
  pointwiseAppendComputable
    (annotatedSourceZipHeadPairComputable 0)
    (annotatedSourceZipHeadPairComputable 1)

private def annotatedCompleteResidualResolutionInput
    (major : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (major input) ++
    lengthPrefixedWord (annotatedCompleteResidualHeadPair input) ++
      input

private noncomputable def flatAnnotatedCompleteResidualResolutionInputComputable
    {major : List Bool → List Bool}
    (computer : BitTM major) :
    BitTM
      (annotatedCompleteResidualResolutionInput major) := by
  have hmajor := GapCVP.TMComposition.computableInPolyTime
    computer structuralPrefixWriterComputable
  have hpair := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteResidualHeadPairComputable
    structuralPrefixWriterComputable
  have hrest := pointwiseAppendComputable hpair
    (Turing.idComputableInPolyTime bitEncoding)
  have physical := pointwiseAppendComputable hmajor hrest
  have hequality :
      (fun input : List Bool =>
        lengthPrefixedWord (major input) ++
          (lengthPrefixedWord
            (annotatedCompleteResidualHeadPair input) ++ input)) =
        annotatedCompleteResidualResolutionInput major := by
    funext input
    simp only [annotatedCompleteResidualResolutionInput, List.append_assoc]
  rw [← hequality]
  exact physical

private def annotatedCompleteResidualResolvedOrdering
    (major : List Bool → List Bool) : List Bool → List Bool :=
  annotatedSquareResolvedOrderingWord ∘
    annotatedCompleteResidualResolutionInput major

private noncomputable def flatAnnotatedCompleteResidualResolvedOrderingComputable
    {major : List Bool → List Bool}
    (computer : BitTM major) :
    BitTM
      (annotatedCompleteResidualResolvedOrdering major) :=
  GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedCompleteResidualResolutionInputComputable computer)
    flatAnnotatedSquareResolvedOrderingComputable

private def flatAnnotatedCompleteSingletonMajor : List Bool → List Bool :=
  annotatedCompleteNaturalOrderingWord
    (annotatedCompleteResidualHeadBinary 0)
    (annotatedCompleteResidualHeadBinary 1)

private noncomputable def flatAnnotatedCompleteSingletonMajorComputable :
    BitTM
      flatAnnotatedCompleteSingletonMajor :=
  flatAnnotatedCompleteNaturalOrderingComputable
    (annotatedCompleteResidualHeadBinaryComputable 0)
    (annotatedCompleteResidualHeadBinaryComputable 1)

private def flatAnnotatedCompleteRightTailMajor : List Bool → List Bool :=
  annotatedCompleteNaturalOrderingWord
    (annotatedCompleteResidualHeadBinary 0)
    (annotatedCountedResidualCappedBinaryWord 1 0)

private noncomputable def flatAnnotatedCompleteRightTailMajorComputable :
    BitTM
      flatAnnotatedCompleteRightTailMajor :=
  flatAnnotatedCompleteNaturalOrderingComputable
    (annotatedCompleteResidualHeadBinaryComputable 0)
    (flatAnnotatedCountedResidualCappedBinaryComputable 1 0)

private def flatAnnotatedCompleteLeftTailMajor : List Bool → List Bool :=
  annotatedCompleteNaturalOrderingWord
    (annotatedCountedResidualCappedBinaryWord 0 1)
    (annotatedCompleteResidualHeadBinary 1)

private noncomputable def flatAnnotatedCompleteLeftTailMajorComputable :
    BitTM
      flatAnnotatedCompleteLeftTailMajor :=
  flatAnnotatedCompleteNaturalOrderingComputable
    (flatAnnotatedCountedResidualCappedBinaryComputable 0 1)
    (annotatedCompleteResidualHeadBinaryComputable 1)

private def annotatedCompleteResidualTailPresence
    (offset : ℕ) (input : List Bool) : List Bool :=
  fiveFamilyOriginalHeadBitWord
    (annotatedCountedResidualTailCount offset input)

private noncomputable def flatAnnotatedCompleteResidualTailPresenceComputable
    (offset : ℕ) :
    BitTM
      (annotatedCompleteResidualTailPresence offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (flatAnnotatedCountedResidualTailCountComputable offset)
    fiveFamilyOriginalHeadBitComputable
  change BitTM
    (fun input : List Bool =>
      fiveFamilyOriginalHeadBitWord
        (annotatedCountedResidualTailCount offset input))
  exact physical

private def annotatedCompleteResidualShapeTag
    (input : List Bool) : List Bool :=
  annotatedCompleteResidualTailPresence 0 input ++
    annotatedCompleteResidualTailPresence 1 input

private noncomputable def flatAnnotatedCompleteResidualShapeTagComputable :
    BitTM
      annotatedCompleteResidualShapeTag :=
  pointwiseAppendComputable
    (flatAnnotatedCompleteResidualTailPresenceComputable 0)
    (flatAnnotatedCompleteResidualTailPresenceComputable 1)

private def annotatedCompleteResidualShapeDispatchInput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
    (annotatedCompleteResidualShapeTag input) ++ input

private noncomputable def flatAnnotatedCompleteResidualShapeDispatchInputComputable :
    BitTM
      annotatedCompleteResidualShapeDispatchInput := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteResidualShapeTagComputable
    structuralPrefixWriterComputable
  exact pointwiseAppendComputable hprefix
    (Turing.idComputableInPolyTime bitEncoding)

private def annotatedCompleteResidualBaseOrdering : List Bool → List Bool :=
  fourFamilyTaggedPredicateMarker
      (annotatedCompleteResidualResolvedOrdering
        flatAnnotatedCompleteSingletonMajor)
      (annotatedCompleteResidualResolvedOrdering
        flatAnnotatedCompleteRightTailMajor)
      (annotatedCompleteResidualResolvedOrdering
        flatAnnotatedCompleteLeftTailMajor)
      (fun _ => encodedWordOrderingWord .invalid) ∘
    annotatedCompleteResidualShapeDispatchInput

private noncomputable def flatAnnotatedCompleteResidualBaseOrderingComputable :
    BitTM
      annotatedCompleteResidualBaseOrdering := by
  have hdispatch := fourFamilyTaggedPredicateMarkerComputable
    (flatAnnotatedCompleteResidualResolvedOrderingComputable
      flatAnnotatedCompleteSingletonMajorComputable)
    (flatAnnotatedCompleteResidualResolvedOrderingComputable
      flatAnnotatedCompleteRightTailMajorComputable)
    (flatAnnotatedCompleteResidualResolvedOrderingComputable
      flatAnnotatedCompleteLeftTailMajorComputable)
    (sourceFixedWordComputable (encodedWordOrderingWord .invalid))
  exact GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteResidualShapeDispatchInputComputable
    hdispatch

private def flatAnnotatedCompleteArchiveCount
    (input : List Bool) : List Bool :=
  flatAnnotatedSourceZipCountWord
    (flatAnnotatedSourceFieldTail 5 input)

private noncomputable def flatAnnotatedCompleteArchiveCountComputable :
    BitTM
      flatAnnotatedCompleteArchiveCount := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldTailComputable 5)
    flatAnnotatedSourceZipCountComputable
  change BitTM
    (fun input : List Bool =>
      flatAnnotatedSourceZipCountWord
        (flatAnnotatedSourceFieldTail 5 input))
  exact physical

private def annotatedCompleteArchiveResolutionPreparation
    (input : List Bool) : List Bool :=
  flatAnnotatedCompleteArchiveCount input ++
    false ::
      (lengthPrefixedWord
          (annotatedCompleteResidualBaseOrdering input) ++
        lengthPrefixedWord (flatAnnotatedSourceFieldAt 2 input) ++ input)

private noncomputable def flatAnnotatedCompleteArchiveResolutionPreparationComputable :
    BitTM
      annotatedCompleteArchiveResolutionPreparation := by
  have hmajor := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteResidualBaseOrderingComputable
    structuralPrefixWriterComputable
  have harchive := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable 2)
    structuralPrefixWriterComputable
  have hstate := pointwiseAppendComputable hmajor
    (pointwiseAppendComputable harchive
      (Turing.idComputableInPolyTime bitEncoding))
  have hdelimited := pointwiseAppendComputable
    (sourceFixedWordComputable [false]) hstate
  have physical := pointwiseAppendComputable
    flatAnnotatedCompleteArchiveCountComputable hdelimited
  have hequality :
      (fun input : List Bool =>
        flatAnnotatedCompleteArchiveCount input ++
          ([false] ++
            (lengthPrefixedWord
              (annotatedCompleteResidualBaseOrdering input) ++
              (lengthPrefixedWord
                (flatAnnotatedSourceFieldAt 2 input) ++ input)))) =
        annotatedCompleteArchiveResolutionPreparation := by
    funext input
    simp only [List.cons_append, List.nil_append, annotatedCompleteArchiveResolutionPreparation,
        List.append_assoc]
  rw [← hequality]
  exact physical

private def annotatedCompleteArchiveResolutionOutput : List Bool → List Bool :=
  boundedRecordFoldOutput flatAnnotatedSquareResolutionStep ∘
    annotatedCompleteArchiveResolutionPreparation

private noncomputable def flatAnnotatedCompleteArchiveResolutionComputable :
    BitTM
      annotatedCompleteArchiveResolutionOutput :=
  GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteArchiveResolutionPreparationComputable
    flatAnnotatedSquareResolutionFoldComputable

private def flatAnnotatedCompleteArchiveAfterZipWord : List Bool → List Bool :=
  annotatedCompleteArchiveResolutionOutput ∘
    annotatedCompleteSourceZippedWord

private noncomputable def flatAnnotatedCompleteArchiveAfterZipComputable :
    BitTM
      flatAnnotatedCompleteArchiveAfterZipWord :=
  GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteSourceZippedComputable
    flatAnnotatedCompleteArchiveResolutionComputable

private def annotatedCompleteFiniteSetOrderingWord : List Bool → List Bool :=
  firstFieldContents ∘ flatAnnotatedCompleteArchiveAfterZipWord

private noncomputable def flatAnnotatedCompleteFiniteSetOrderingComputable :
    BitTM
      annotatedCompleteFiniteSetOrderingWord :=
  GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteArchiveAfterZipComputable
    firstFieldContentsComputable

end CNFAnnotatedSourceCompleteFiniteSetComparatorTM

namespace CNFAnnotatedSourceCompleteFiniteSetComparatorSourceCert

open Turing GapCVP.CL GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFEncodedClauseSort
open GapCVP.CNFNaturalOrderComparator GapCVP.CNFFlatSourceOrder
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFlatCappedComparisonControlledSwapTM
open GapCVP.CNFSourcePairPrefixWorkerTM GapCVP.CNFCappedFlatSourceListFoldTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM GapCVP.CNFAnnotatedSourceClausePairZipTM
open GapCVP.CNFAnnotatedSourceCountedClausePairZipTM
open GapCVP.CNFAnnotatedSourceCountedResidualTailTM
open GapCVP.CNFAnnotatedSourceSquareMajorResolutionTM
open GapCVP.CNFAnnotatedSourceCompleteFiniteSetComparatorTM
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM
open GapCVP.SourceFourFamilyTaggedPredicateDispatchTM

@[simp] private theorem flatAnnotatedCompleteResidualHeadBinary_first
    (head : ℕ) (remaining second : List ℕ)
    (archive suffix : List Bool) :
    annotatedCompleteResidualHeadBinary 0
        (flatAnnotatedCountedSourceZipState
          (head :: remaining) second archive suffix) =
      Computability.encodeNat head := by
  simp only [annotatedCompleteResidualHeadBinary, flatAnnotatedCountedResidualHeadUnary_first,
      List.length_replicate]

@[simp] private theorem flatAnnotatedCompleteResidualHeadBinary_second
    (first : List ℕ) (head : ℕ) (remaining : List ℕ)
    (archive suffix : List Bool) :
    annotatedCompleteResidualHeadBinary 1
        (flatAnnotatedCountedSourceZipState
          first (head :: remaining) archive suffix) =
      Computability.encodeNat head := by
  simp only [annotatedCompleteResidualHeadBinary, flatAnnotatedCountedResidualHeadUnary_second,
      List.length_replicate]

private theorem flatAnnotatedCompleteNaturalOrderingWord_valid
    (first second : List Bool → List Bool)
    (input : List Bool) (firstValue secondValue : ℕ)
    (hfirst : first input = Computability.encodeNat firstValue)
    (hsecond : second input = Computability.encodeNat secondValue) :
    annotatedCompleteNaturalOrderingWord first second input =
      encodedWordOrderingWord
        (flatSourceNaturalOrdering firstValue secondValue) := by
  simp only [annotatedCompleteNaturalOrderingWord,
    annotatedCompleteNaturalComparisonInput,
    sourcePreservingDelimitedNaturalComparisonWord,
    firstFieldSuffix_valid, hfirst, hsecond]
  rw [delimitedNaturalPairOrdering_encodeNat]
  rfl

@[simp] private theorem flatAnnotatedCompleteResidualHeadPair_valid
    (firstHead secondHead : ℕ)
    (firstRemaining secondRemaining : List ℕ)
    (archive suffix : List Bool) :
    annotatedCompleteResidualHeadPair
        (flatAnnotatedCountedSourceZipState
          (firstHead :: firstRemaining)
          (secondHead :: secondRemaining) archive suffix) =
      flatAnnotatedSourceZipArchivedPair (firstHead, secondHead) := by
  simp only [annotatedCompleteResidualHeadPair, flatAnnotatedSourceZipHeadPair,
      flatAnnotatedSourceFieldAt,
      flatAnnotatedSourceFieldTail, flatAnnotatedCountedSourceZipState,
          flatDuplicatedUnarySourceStream,
      List.flatMap_cons, flatDuplicatedUnaryField, List.append_assoc, List.length_cons,
          Function.iterate_zero, id_eq,
      firstFieldContents_valid, sourcePairPrefixOutput_pair, Function.iterate_one,
          firstFieldSuffix_valid,
      flatAnnotatedSourceZipArchivedPair]

private theorem flatAnnotatedCompleteResidualResolvedOrdering_valid
    (major : List Bool → List Bool)
    (outcome : EncodedWordOrdering)
    (firstHead secondHead : ℕ)
    (firstRemaining secondRemaining : List ℕ)
    (archive suffix : List Bool)
    (hmajor :
      major (flatAnnotatedCountedSourceZipState
          (firstHead :: firstRemaining)
          (secondHead :: secondRemaining) archive suffix) =
        encodedWordOrderingWord outcome) :
    annotatedCompleteResidualResolvedOrdering major
        (flatAnnotatedCountedSourceZipState
          (firstHead :: firstRemaining)
          (secondHead :: secondRemaining) archive suffix) =
      encodedWordOrderingWord
        (resolveFlatSourceOrder outcome firstHead secondHead) := by
  unfold annotatedCompleteResidualResolvedOrdering
  rw [Function.comp_apply]
  unfold annotatedCompleteResidualResolutionInput
  rw [hmajor, flatAnnotatedCompleteResidualHeadPair_valid]
  simpa only [List.append_assoc, List.append_nil] using
      flatAnnotatedSquareResolvedOrderingWord_valid outcome firstHead secondHead []
        (flatAnnotatedCountedSourceZipState (firstHead :: firstRemaining) (secondHead ::
            secondRemaining) archive suffix)

@[simp] private theorem flatAnnotatedCompleteResidualTailPresence_first
    (head : ℕ) (remaining second : List ℕ)
    (archive suffix : List Bool) :
    annotatedCompleteResidualTailPresence 0
        (flatAnnotatedCountedSourceZipState
          (head :: remaining) second archive suffix) =
      [decide (0 < remaining.length)] := by
  cases remaining with
  | nil =>
      simp [annotatedCompleteResidualTailPresence,
        annotatedCountedResidualTailCount,
        flatAnnotatedCountedSourceZipState,
        flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
        fiveFamilyOriginalHeadBitWord_eq,
        Function.iterate_succ_apply', List.append_assoc]
  | cons next tail =>
      simp [annotatedCompleteResidualTailPresence,
        annotatedCountedResidualTailCount,
        flatAnnotatedCountedSourceZipState,
        flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
        fiveFamilyOriginalHeadBitWord_eq,
        List.replicate_succ,
        Function.iterate_succ_apply', List.append_assoc]

@[simp] private theorem flatAnnotatedCompleteResidualTailPresence_second
    (first : List ℕ) (head : ℕ) (remaining : List ℕ)
    (archive suffix : List Bool) :
    annotatedCompleteResidualTailPresence 1
        (flatAnnotatedCountedSourceZipState
          first (head :: remaining) archive suffix) =
      [decide (0 < remaining.length)] := by
  cases remaining with
  | nil =>
      simp [annotatedCompleteResidualTailPresence,
        annotatedCountedResidualTailCount,
        flatAnnotatedCountedSourceZipState,
        flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
        fiveFamilyOriginalHeadBitWord_eq,
        Function.iterate_succ_apply', List.append_assoc]
  | cons next tail =>
      simp [annotatedCompleteResidualTailPresence,
        annotatedCountedResidualTailCount,
        flatAnnotatedCountedSourceZipState,
        flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
        fiveFamilyOriginalHeadBitWord_eq,
        List.replicate_succ,
        Function.iterate_succ_apply', List.append_assoc]

private theorem flatAnnotatedCompleteResidualBaseOrdering_valid
    (firstHead secondHead : ℕ)
    (firstRemaining secondRemaining : List ℕ)
    (archive suffix : List Bool)
    (hshort : firstRemaining = [] ∨ secondRemaining = []) :
    annotatedCompleteResidualBaseOrdering
        (flatAnnotatedCountedSourceZipState
          (firstHead :: firstRemaining)
          (secondHead :: secondRemaining) archive suffix) =
      encodedWordOrderingWord
        (flatSortedSourceListOrdering
          (firstHead :: firstRemaining)
          (secondHead :: secondRemaining)) := by
  cases firstRemaining with
  | nil =>
      cases secondRemaining with
      | nil =>
          have hmajor := flatAnnotatedCompleteNaturalOrderingWord_valid
            (annotatedCompleteResidualHeadBinary 0)
            (annotatedCompleteResidualHeadBinary 1)
            (flatAnnotatedCountedSourceZipState
              [firstHead] [secondHead] archive suffix)
            firstHead secondHead
            (flatAnnotatedCompleteResidualHeadBinary_first
              firstHead [] [secondHead] archive suffix)
            (flatAnnotatedCompleteResidualHeadBinary_second
              [firstHead] secondHead [] archive suffix)
          have hresolved :=
            flatAnnotatedCompleteResidualResolvedOrdering_valid
              flatAnnotatedCompleteSingletonMajor
              (flatSourceNaturalOrdering firstHead secondHead)
              firstHead secondHead [] [] archive suffix hmajor
          have htag :
              annotatedCompleteResidualShapeTag
                  (flatAnnotatedCountedSourceZipState
                    [firstHead] [secondHead] archive suffix) =
                [false, false] := by
            unfold annotatedCompleteResidualShapeTag
            rw [flatAnnotatedCompleteResidualTailPresence_first,
              flatAnnotatedCompleteResidualTailPresence_second]
            rfl
          unfold annotatedCompleteResidualBaseOrdering
          rw [Function.comp_apply]
          unfold annotatedCompleteResidualShapeDispatchInput
          rw [htag, sourceFourFamilyTaggedPredicateMarker_interpolation]
          simpa only [flatSortedSourceListOrdering] using hresolved
      | cons next remaining =>
          have hmajor := flatAnnotatedCompleteNaturalOrderingWord_valid
            (annotatedCompleteResidualHeadBinary 0)
            (annotatedCountedResidualCappedBinaryWord 1 0)
            (flatAnnotatedCountedSourceZipState
              [firstHead] (secondHead :: next :: remaining)
              archive suffix)
            firstHead
            (cappedFlatSourceListValue
              (firstHead + 1) (next :: remaining))
            (flatAnnotatedCompleteResidualHeadBinary_first
              firstHead [] (secondHead :: next :: remaining)
              archive suffix)
            (flatAnnotatedCountedResidualCappedBinaryWord_second
              firstHead [] secondHead (next :: remaining)
              archive suffix)
          have hresolved :=
            flatAnnotatedCompleteResidualResolvedOrdering_valid
              flatAnnotatedCompleteRightTailMajor
              (flatSourceNaturalOrdering firstHead
                (cappedFlatSourceListValue
                  (firstHead + 1) (next :: remaining)))
              firstHead secondHead [] (next :: remaining)
              archive suffix hmajor
          have htag :
              annotatedCompleteResidualShapeTag
                  (flatAnnotatedCountedSourceZipState
                    [firstHead] (secondHead :: next :: remaining)
                    archive suffix) =
                [false, true] := by
            unfold annotatedCompleteResidualShapeTag
            rw [flatAnnotatedCompleteResidualTailPresence_first,
              flatAnnotatedCompleteResidualTailPresence_second]
            rfl
          unfold annotatedCompleteResidualBaseOrdering
          rw [Function.comp_apply]
          unfold annotatedCompleteResidualShapeDispatchInput
          rw [htag, sourceFourFamilyTaggedPredicateMarker_normalization]
          simpa only [flatSortedSourceListOrdering] using hresolved
  | cons next remaining =>
      cases secondRemaining with
      | nil =>
          have hmajor := flatAnnotatedCompleteNaturalOrderingWord_valid
            (annotatedCountedResidualCappedBinaryWord 0 1)
            (annotatedCompleteResidualHeadBinary 1)
            (flatAnnotatedCountedSourceZipState
              (firstHead :: next :: remaining) [secondHead]
              archive suffix)
            (cappedFlatSourceListValue
              (secondHead + 1) (next :: remaining))
            secondHead
            (flatAnnotatedCountedResidualCappedBinaryWord_first
              firstHead (next :: remaining)
              secondHead [] archive suffix)
            (flatAnnotatedCompleteResidualHeadBinary_second
              (firstHead :: next :: remaining)
              secondHead [] archive suffix)
          have hresolved :=
            flatAnnotatedCompleteResidualResolvedOrdering_valid
              flatAnnotatedCompleteLeftTailMajor
              (flatSourceNaturalOrdering
                (cappedFlatSourceListValue
                  (secondHead + 1) (next :: remaining))
                secondHead)
              firstHead secondHead (next :: remaining) []
              archive suffix hmajor
          have htag :
              annotatedCompleteResidualShapeTag
                  (flatAnnotatedCountedSourceZipState
                    (firstHead :: next :: remaining) [secondHead]
                    archive suffix) =
                [true, false] := by
            unfold annotatedCompleteResidualShapeTag
            rw [flatAnnotatedCompleteResidualTailPresence_first,
              flatAnnotatedCompleteResidualTailPresence_second]
            rfl
          unfold annotatedCompleteResidualBaseOrdering
          rw [Function.comp_apply]
          unfold annotatedCompleteResidualShapeDispatchInput
          rw [htag, sourceFourFamilyTaggedPredicateMarker_diagonal]
          simpa only [flatSortedSourceListOrdering] using hresolved
      | cons other others =>
          simp only [reduceCtorEq, or_self] at hshort

private theorem flatSortedSourceListOrdering_matchedPrefix
    (pairs : List (ℕ × ℕ))
    (firstHead secondHead : ℕ)
    (firstRemaining secondRemaining : List ℕ) :
    flatSortedSourceListOrdering
        (pairs.map Prod.fst ++ firstHead :: firstRemaining)
        (pairs.map Prod.snd ++ secondHead :: secondRemaining) =
      pairs.reverse.foldl
        (fun major pair =>
          resolveFlatSourceOrder major pair.1 pair.2)
        (flatSortedSourceListOrdering
          (firstHead :: firstRemaining)
          (secondHead :: secondRemaining)) := by
  induction pairs with
  | nil => simp only [List.map_nil, List.nil_append, List.reverse_nil, List.foldl_nil]
  | cons pair remaining ih =>
      cases remaining with
      | nil =>
          simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
              flatSortedSourceListOrdering,
              List.reverse_cons, List.reverse_nil, List.foldl_cons, List.foldl_nil]
      | cons next tail =>
          simp only [List.map_cons, List.cons_append,
            List.reverse_cons, List.foldl_append,
            List.foldl_cons, List.foldl_nil]
          rw [flatSortedSourceListOrdering]
          simpa only [List.map_cons, List.cons_append,
            List.reverse_cons, List.foldl_append,
            List.foldl_cons, List.foldl_nil] using
            congrArg
              (fun outcome =>
                resolveFlatSourceOrder outcome pair.1 pair.2)
              ih

private theorem flatAnnotatedCompleteSourceZippedWord_valid
    (pairs : List (ℕ × ℕ))
    (firstRemaining secondRemaining : List ℕ)
    (firstClause secondClause suffix : List Bool)
    (hcount :
      min (pairs.map Prod.fst ++ firstRemaining).length
          (pairs.map Prod.snd ++ secondRemaining).length - 1 =
        pairs.length) :
    annotatedCompleteSourceZippedWord
        (annotatedSourceAdjacentClauseWord
          firstClause
          (flatDuplicatedUnarySourceStream
            (pairs.map Prod.fst ++ firstRemaining))
          (pairs.map Prod.fst ++ firstRemaining).length
          secondClause
          (flatDuplicatedUnarySourceStream
            (pairs.map Prod.snd ++ secondRemaining))
          (pairs.map Prod.snd ++ secondRemaining).length
          suffix) =
      flatAnnotatedCountedSourceZipState
        firstRemaining secondRemaining
        (pairs.reverse.flatMap flatAnnotatedSourceZipArchivedPair)
        (annotatedSourceAdjacentClauseWord
          firstClause
          (flatDuplicatedUnarySourceStream
            (pairs.map Prod.fst ++ firstRemaining))
          (pairs.map Prod.fst ++ firstRemaining).length
          secondClause
          (flatDuplicatedUnarySourceStream
            (pairs.map Prod.snd ++ secondRemaining))
          (pairs.map Prod.snd ++ secondRemaining).length
          suffix) := by
  unfold annotatedCompleteSourceZippedWord
  rw [Function.comp_apply,
    flatAnnotatedCountedSourcePairZipPreparationWord_valid,
    hcount]
  simpa only [flatAnnotatedCountedSourceZipState,
    List.append_nil, List.append_assoc] using
    (boundedRecordFoldOutput_flatAnnotatedCountedSourceZipPairs
      pairs firstRemaining secondRemaining []
        (annotatedSourceAdjacentClauseWord
          firstClause
          (flatDuplicatedUnarySourceStream
            (pairs.map Prod.fst ++ firstRemaining))
          (pairs.map Prod.fst ++ firstRemaining).length
          secondClause
          (flatDuplicatedUnarySourceStream
            (pairs.map Prod.snd ++ secondRemaining))
          (pairs.map Prod.snd ++ secondRemaining).length
          suffix))

@[simp] private theorem flatAnnotatedCompleteZippedArchiveField_valid
    (first second : List ℕ)
    (archive suffix : List Bool) :
    flatAnnotatedSourceFieldAt 2
        (flatAnnotatedCountedSourceZipState
          first second archive suffix) = archive := by
  simp [flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
    flatAnnotatedCountedSourceZipState,
    Function.iterate_succ_apply', List.append_assoc]

@[simp] private theorem flatAnnotatedCompleteZippedOriginalSource_valid
    (first second : List ℕ)
    (archive suffix : List Bool) :
    flatAnnotatedSourceFieldTail 5
        (flatAnnotatedCountedSourceZipState
          first second archive suffix) = suffix := by
  simp [flatAnnotatedSourceFieldTail,
    flatAnnotatedCountedSourceZipState,
    Function.iterate_succ_apply', List.append_assoc]

@[simp] private theorem flatAnnotatedCompleteArchiveCount_zipState_valid
    (firstRemaining secondRemaining : List ℕ)
    (archive : List Bool)
    (firstClause firstCodes : List Bool) (firstCount : ℕ)
    (secondClause secondCodes : List Bool) (secondCount : ℕ)
    (suffix : List Bool) :
    flatAnnotatedCompleteArchiveCount
        (flatAnnotatedCountedSourceZipState
          firstRemaining secondRemaining archive
          (annotatedSourceAdjacentClauseWord
            firstClause firstCodes firstCount
            secondClause secondCodes secondCount suffix)) =
      List.replicate (min firstCount secondCount - 1) true := by
  unfold flatAnnotatedCompleteArchiveCount
  rw [flatAnnotatedCompleteZippedOriginalSource_valid,
    flatAnnotatedSourceZipCountWord_valid]

private theorem flatAnnotatedCompleteArchiveResolutionOutput_valid
    (pairs : List (ℕ × ℕ))
    (firstHead secondHead : ℕ)
    (firstRemaining secondRemaining : List ℕ)
    (firstClause firstCodes : List Bool) (firstCount : ℕ)
    (secondClause secondCodes : List Bool) (secondCount : ℕ)
    (suffix : List Bool)
    (hcount : min firstCount secondCount - 1 = pairs.length)
    (hshort : firstRemaining = [] ∨ secondRemaining = []) :
    annotatedCompleteArchiveResolutionOutput
        (flatAnnotatedCountedSourceZipState
          (firstHead :: firstRemaining)
          (secondHead :: secondRemaining)
          (pairs.reverse.flatMap flatAnnotatedSourceZipArchivedPair)
          (annotatedSourceAdjacentClauseWord
            firstClause firstCodes firstCount
            secondClause secondCodes secondCount suffix)) =
      flatAnnotatedSquareResolutionState
        (pairs.reverse.foldl
          (fun major pair =>
            resolveFlatSourceOrder major pair.1 pair.2)
          (flatSortedSourceListOrdering
            (firstHead :: firstRemaining)
            (secondHead :: secondRemaining)))
        []
        (flatAnnotatedCountedSourceZipState
          (firstHead :: firstRemaining)
          (secondHead :: secondRemaining)
          (pairs.reverse.flatMap flatAnnotatedSourceZipArchivedPair)
          (annotatedSourceAdjacentClauseWord
            firstClause firstCodes firstCount
            secondClause secondCodes secondCount suffix)) := by
  unfold annotatedCompleteArchiveResolutionOutput
  rw [Function.comp_apply]
  unfold annotatedCompleteArchiveResolutionPreparation
  rw [flatAnnotatedCompleteArchiveCount_zipState_valid, hcount,
    flatAnnotatedCompleteResidualBaseOrdering_valid
      firstHead secondHead firstRemaining secondRemaining
      (pairs.reverse.flatMap flatAnnotatedSourceZipArchivedPair)
      (annotatedSourceAdjacentClauseWord
        firstClause firstCodes firstCount
        secondClause secondCodes secondCount suffix) hshort,
    flatAnnotatedCompleteZippedArchiveField_valid]
  simpa only [unaryBoundedFoldWord,
    flatAnnotatedSquareResolutionState,
    List.length_reverse, List.append_nil, List.append_assoc] using
    (boundedRecordFoldOutput_flatAnnotatedSquareResolution
      (flatSortedSourceListOrdering
        (firstHead :: firstRemaining)
        (secondHead :: secondRemaining))
      pairs.reverse []
      (flatAnnotatedCountedSourceZipState
        (firstHead :: firstRemaining)
        (secondHead :: secondRemaining)
        (pairs.reverse.flatMap flatAnnotatedSourceZipArchivedPair)
        (annotatedSourceAdjacentClauseWord
          firstClause firstCodes firstCount
          secondClause secondCodes secondCount suffix)))

private theorem flatAnnotatedCompleteFiniteSetOrderingWord_matched_valid
    (pairs : List (ℕ × ℕ))
    (firstHead secondHead : ℕ)
    (firstRemaining secondRemaining : List ℕ)
    (firstClause secondClause suffix : List Bool)
    (hcount :
      min (pairs.map Prod.fst ++ firstHead :: firstRemaining).length
          (pairs.map Prod.snd ++ secondHead :: secondRemaining).length - 1 =
        pairs.length)
    (hshort : firstRemaining = [] ∨ secondRemaining = []) :
    annotatedCompleteFiniteSetOrderingWord
        (annotatedSourceAdjacentClauseWord
          firstClause
          (flatDuplicatedUnarySourceStream
            (pairs.map Prod.fst ++ firstHead :: firstRemaining))
          (pairs.map Prod.fst ++ firstHead :: firstRemaining).length
          secondClause
          (flatDuplicatedUnarySourceStream
            (pairs.map Prod.snd ++ secondHead :: secondRemaining))
          (pairs.map Prod.snd ++ secondHead :: secondRemaining).length
          suffix) =
      encodedWordOrderingWord
        (flatSortedSourceListOrdering
          (pairs.map Prod.fst ++ firstHead :: firstRemaining)
          (pairs.map Prod.snd ++ secondHead :: secondRemaining)) := by
  unfold annotatedCompleteFiniteSetOrderingWord
  rw [Function.comp_apply]
  unfold flatAnnotatedCompleteArchiveAfterZipWord
  rw [Function.comp_apply,
    flatAnnotatedCompleteSourceZippedWord_valid
      pairs (firstHead :: firstRemaining)
      (secondHead :: secondRemaining)
      firstClause secondClause suffix hcount,
    flatAnnotatedCompleteArchiveResolutionOutput_valid
      pairs firstHead secondHead firstRemaining secondRemaining
      firstClause
      (flatDuplicatedUnarySourceStream
        (pairs.map Prod.fst ++ firstHead :: firstRemaining))
      (pairs.map Prod.fst ++ firstHead :: firstRemaining).length
      secondClause
      (flatDuplicatedUnarySourceStream
        (pairs.map Prod.snd ++ secondHead :: secondRemaining))
      (pairs.map Prod.snd ++ secondHead :: secondRemaining).length
      suffix hcount hshort]
  simp only [flatAnnotatedSquareResolutionState,
    List.append_assoc, firstFieldContents_valid]
  rw [flatSortedSourceListOrdering_matchedPrefix]

private def annotatedCompleteOriginalCountPresence
    (offset : ℕ) (input : List Bool) : List Bool :=
  fiveFamilyOriginalHeadBitWord (flatAnnotatedSourceFieldAt offset input)

private noncomputable def flatAnnotatedCompleteOriginalCountPresenceComputable
    (offset : ℕ) :
    BitTM
      (annotatedCompleteOriginalCountPresence offset) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable offset)
    fiveFamilyOriginalHeadBitComputable
  change BitTM
    (fun input : List Bool =>
      fiveFamilyOriginalHeadBitWord
        (flatAnnotatedSourceFieldAt offset input))
  exact physical

private def annotatedCompleteOriginalShapeTag (input : List Bool) : List Bool :=
  annotatedCompleteOriginalCountPresence 2 input ++
    annotatedCompleteOriginalCountPresence 5 input

private noncomputable def flatAnnotatedCompleteOriginalShapeTagComputable :
    BitTM
      annotatedCompleteOriginalShapeTag := by
  exact pointwiseAppendComputable
    (flatAnnotatedCompleteOriginalCountPresenceComputable 2)
    (flatAnnotatedCompleteOriginalCountPresenceComputable 5)

private def flatAnnotatedCompleteOriginalShapeDispatchInput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (annotatedCompleteOriginalShapeTag input) ++ input

private noncomputable def flatAnnotatedCompleteOriginalShapeDispatchInputComputable :
    BitTM
      flatAnnotatedCompleteOriginalShapeDispatchInput := by
  have htag := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteOriginalShapeTagComputable
    structuralPrefixWriterComputable
  have physical := pointwiseAppendComputable htag
    (Turing.idComputableInPolyTime bitEncoding)
  change BitTM
    (fun input : List Bool =>
      lengthPrefixedWord (annotatedCompleteOriginalShapeTag input) ++
        input)
  simpa only [Function.comp_def, id_eq] using physical

/-- GapCVP reduction support. -/
def annotatedCompleteTotalOrderingWord : List Bool → List Bool :=
  fourFamilyTaggedPredicateMarker
    (fun _ => encodedWordOrderingWord .equal)
    (fun _ => encodedWordOrderingWord .less)
    (fun _ => encodedWordOrderingWord .greater)
    annotatedCompleteFiniteSetOrderingWord ∘
      flatAnnotatedCompleteOriginalShapeDispatchInput

private noncomputable def flatAnnotatedCompleteTotalOrderingComputable :
    BitTM
      annotatedCompleteTotalOrderingWord := by
  have hdispatch := fourFamilyTaggedPredicateMarkerComputable
    (sourceFixedWordComputable (encodedWordOrderingWord .equal))
    (sourceFixedWordComputable (encodedWordOrderingWord .less))
    (sourceFixedWordComputable (encodedWordOrderingWord .greater))
    flatAnnotatedCompleteFiniteSetOrderingComputable
  exact GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteOriginalShapeDispatchInputComputable hdispatch

/-- GapCVP reduction support. -/
def annotatedCompleteTotalSourceComparison
    (input : List Bool) : List Bool :=
  lengthPrefixedWord input ++ annotatedCompleteTotalOrderingWord input

/-- GapCVP reduction support. -/
noncomputable def flatAnnotatedCompleteTotalSourceComparisonComputable :
    BitTM
      annotatedCompleteTotalSourceComparison := by
  exact pointwiseAppendComputable structuralPrefixWriterComputable
    flatAnnotatedCompleteTotalOrderingComputable

@[simp] private theorem flatAnnotatedCompleteOriginalCountPresence_first
    (firstClause firstCodes : List Bool) (firstCount : ℕ)
    (secondClause secondCodes : List Bool) (secondCount : ℕ)
    (suffix : List Bool) :
    annotatedCompleteOriginalCountPresence 2
        (annotatedSourceAdjacentClauseWord
          firstClause firstCodes firstCount
          secondClause secondCodes secondCount suffix) =
      [decide (0 < firstCount)] := by
  cases firstCount <;>
    simp [annotatedCompleteOriginalCountPresence,
      fiveFamilyOriginalHeadBitWord_eq, List.replicate_succ]

@[simp] private theorem flatAnnotatedCompleteOriginalCountPresence_second
    (firstClause firstCodes : List Bool) (firstCount : ℕ)
    (secondClause secondCodes : List Bool) (secondCount : ℕ)
    (suffix : List Bool) :
    annotatedCompleteOriginalCountPresence 5
        (annotatedSourceAdjacentClauseWord
          firstClause firstCodes firstCount
          secondClause secondCodes secondCount suffix) =
      [decide (0 < secondCount)] := by
  cases secondCount <;>
    simp [annotatedCompleteOriginalCountPresence,
      fiveFamilyOriginalHeadBitWord_eq, List.replicate_succ]

@[simp] private theorem flatAnnotatedCompleteOriginalShapeTag_valid
    (firstClause firstCodes : List Bool) (firstCount : ℕ)
    (secondClause secondCodes : List Bool) (secondCount : ℕ)
    (suffix : List Bool) :
    annotatedCompleteOriginalShapeTag
        (annotatedSourceAdjacentClauseWord
          firstClause firstCodes firstCount
          secondClause secondCodes secondCount suffix) =
      [decide (0 < firstCount), decide (0 < secondCount)] := by
  simp only [annotatedCompleteOriginalShapeTag, flatAnnotatedCompleteOriginalCountPresence_first,
      flatAnnotatedCompleteOriginalCountPresence_second, List.cons_append, List.nil_append]

private theorem flatAnnotatedCompleteTotalOrderingWord_shape_valid
    (firstClause firstCodes : List Bool) (firstCount : ℕ)
    (secondClause secondCodes : List Bool) (secondCount : ℕ)
    (suffix : List Bool) :
    annotatedCompleteTotalOrderingWord
        (annotatedSourceAdjacentClauseWord
          firstClause firstCodes firstCount
          secondClause secondCodes secondCount suffix) =
      if 0 < firstCount then
        if 0 < secondCount then
          annotatedCompleteFiniteSetOrderingWord
            (annotatedSourceAdjacentClauseWord
              firstClause firstCodes firstCount
              secondClause secondCodes secondCount suffix)
        else encodedWordOrderingWord .greater
      else
        if 0 < secondCount then encodedWordOrderingWord .less
        else encodedWordOrderingWord .equal := by
  unfold annotatedCompleteTotalOrderingWord
  rw [Function.comp_apply]
  unfold flatAnnotatedCompleteOriginalShapeDispatchInput
  rw [flatAnnotatedCompleteOriginalShapeTag_valid]
  cases firstCount with
  | zero =>
      cases secondCount with
      | zero =>
          change fourFamilyTaggedPredicateMarker _ _ _ _
            (lengthPrefixedWord [false, false] ++ _) = _
          rw [sourceFourFamilyTaggedPredicateMarker_interpolation]
          simp only [lt_self_iff_false, ↓reduceIte]
      | succ count =>
          change fourFamilyTaggedPredicateMarker _ _ _ _
            (lengthPrefixedWord [false, true] ++ _) = _
          rw [sourceFourFamilyTaggedPredicateMarker_normalization]
          simp only [lt_self_iff_false, ↓reduceIte, lt_add_iff_pos_left, Order.lt_add_one_iff,
              zero_le]
  | succ count =>
      cases secondCount with
      | zero =>
          change fourFamilyTaggedPredicateMarker _ _ _ _
            (lengthPrefixedWord [true, false] ++ _) = _
          rw [sourceFourFamilyTaggedPredicateMarker_diagonal]
          simp only [lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, ↓reduceIte,
              lt_self_iff_false]
      | succ count =>
          change fourFamilyTaggedPredicateMarker _ _ _ _
            (lengthPrefixedWord [true, true] ++ _) = _
          rw [sourceFourFamilyTaggedPredicateMarker_clause]
          simp only [lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, ↓reduceIte]

private theorem flatAnnotatedCompleteNonemptyMatchedDecomposition
    (first second : List ℕ)
    (hfirst : first ≠ []) (hsecond : second ≠ []) :
    ∃ (pairs : List (ℕ × ℕ))
      (firstHead secondHead : ℕ)
      (firstRemaining secondRemaining : List ℕ),
      first = pairs.map Prod.fst ++ firstHead :: firstRemaining ∧
      second = pairs.map Prod.snd ++ secondHead :: secondRemaining ∧
      min first.length second.length - 1 = pairs.length ∧
      (firstRemaining = [] ∨ secondRemaining = []) := by
  induction first generalizing second with
  | nil => exact False.elim (hfirst rfl)
  | cons firstHead firstTail ih =>
      cases second with
      | nil => exact False.elim (hsecond rfl)
      | cons secondHead secondTail =>
          cases firstTail with
          | nil =>
              refine ⟨[], firstHead, secondHead, [], secondTail,
                ?_, ?_, ?_, Or.inl rfl⟩
              · simp only [List.map_nil, List.nil_append]
              · simp only [List.map_nil, List.nil_append]
              · simp only [List.length_cons, List.length_nil, zero_add, le_add_iff_nonneg_left,
                  zero_le, inf_of_le_left,
                    tsub_self]
          | cons firstNext firstRest =>
              cases secondTail with
              | nil =>
                  refine ⟨[], firstHead, secondHead,
                    firstNext :: firstRest, [],
                    ?_, ?_, ?_, Or.inr rfl⟩
                  · simp only [List.map_nil, List.nil_append]
                  · simp only [List.map_nil, List.nil_append]
                  · simp only [List.length_cons, List.length_nil, zero_add, le_add_iff_nonneg_left,
                      zero_le, inf_of_le_right,
                        tsub_self]
              | cons secondNext secondRest =>
                  obtain ⟨pairs, nextFirst, nextSecond,
                    firstRemaining, secondRemaining,
                    hfirstTail, hsecondTail, hcount, hshort⟩ :=
                    ih (secondNext :: secondRest)
                      (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (by simp only [ne_eq,
                          reduceCtorEq, not_false_eq_true])
                  refine ⟨(firstHead, secondHead) :: pairs,
                    nextFirst, nextSecond,
                    firstRemaining, secondRemaining,
                    ?_, ?_, ?_, hshort⟩
                  · simpa only [List.map_cons, List.cons_append]
                      using congrArg
                        (fun source : List ℕ => firstHead :: source)
                        hfirstTail
                  · simpa only [List.map_cons, List.cons_append]
                      using congrArg
                        (fun source : List ℕ => secondHead :: source)
                        hsecondTail
                  · simp only [List.length_cons] at hcount ⊢
                    omega

theorem flatAnnotatedCompleteTotalOrderingWord_valid
    (first second : List ℕ)
    (firstClause secondClause suffix : List Bool) :
    annotatedCompleteTotalOrderingWord
        (annotatedSourceAdjacentClauseWord
          firstClause (flatDuplicatedUnarySourceStream first) first.length
          secondClause (flatDuplicatedUnarySourceStream second) second.length
          suffix) =
      encodedWordOrderingWord
        (flatSortedSourceListOrdering first second) := by
  rw [flatAnnotatedCompleteTotalOrderingWord_shape_valid]
  cases first with
  | nil =>
      cases second with
      | nil => simp only [List.length_nil, lt_self_iff_false, ↓reduceIte,
          flatSortedSourceListOrdering]
      | cons secondHead secondTail =>
          simp only [List.length_nil, lt_self_iff_false, ↓reduceIte, List.length_cons,
              lt_add_iff_pos_left,
              Order.lt_add_one_iff, zero_le, flatSortedSourceListOrdering]
  | cons firstHead firstTail =>
      cases second with
      | nil => simp only [List.length_cons, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le,
          ↓reduceIte, List.length_nil,
                   lt_self_iff_false, flatSortedSourceListOrdering]
      | cons secondHead secondTail =>
          simp only [List.length_cons, Nat.zero_lt_succ,
            ↓reduceIte]
          obtain ⟨pairs, nextFirst, nextSecond,
            firstRemaining, secondRemaining,
            hfirst, hsecond, hcount, hshort⟩ :=
            flatAnnotatedCompleteNonemptyMatchedDecomposition
              (firstHead :: firstTail) (secondHead :: secondTail)
              (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (by simp only [ne_eq,
                  reduceCtorEq, not_false_eq_true])
          have hpaircount :
              min (pairs.map Prod.fst ++
                    nextFirst :: firstRemaining).length
                  (pairs.map Prod.snd ++
                    nextSecond :: secondRemaining).length - 1 =
                pairs.length := by
            rw [← hfirst, ← hsecond]
            exact hcount
          have hmatched :=
            flatAnnotatedCompleteFiniteSetOrderingWord_matched_valid
              pairs nextFirst nextSecond
              firstRemaining secondRemaining
              firstClause secondClause suffix hpaircount hshort
          rw [← hfirst, ← hsecond] at hmatched
          exact hmatched

@[simp] theorem flatAnnotatedCompleteOriginalClausePair_records
    {T S : ℕ} (first second : Clause T S) :
    flatSourceClauseAnnotatedRecord first ++
        flatSourceClauseAnnotatedRecord second =
      annotatedSourceAdjacentClauseWord
        (flatSourceClauseDescriptorPayload first)
        (flatDuplicatedUnarySourceStream
          (flatSourceFinsetCodes first))
        (flatSourceFinsetCodes first).length
        (flatSourceClauseDescriptorPayload second)
        (flatDuplicatedUnarySourceStream
          (flatSourceFinsetCodes second))
        (flatSourceFinsetCodes second).length
        [] := by
  simp only [flatSourceClauseAnnotatedRecord, flatSourceClauseDuplicatedCodePayload,
      flatSourceFinsetCodes,
      flatSourceClauseUnaryCountPayload, List.append_assoc, annotatedSourceAdjacentClauseWord,
          List.length_map,
      ThreeCNFReduction.sortedElements_length, List.append_nil]

theorem flatAnnotatedCompleteTotalSourceComparison_correct :
    CorrectFlatAnnotatedBundledSourceComparison
      annotatedCompleteTotalSourceComparison := by
  simp only [CorrectFlatAnnotatedBundledSourceComparison,
      decide_eq_true_eq]
  intro T S first second suffix
  simp only [flatComparisonGreaterMarker,
    annotatedBundledPairComparisonWord,
    flatAnnotatedBundledPairComparisonInput_records,
    annotatedCompleteTotalSourceComparison,
    firstFieldSuffix_valid]
  rw [flatAnnotatedCompleteOriginalClausePair_records,
    flatAnnotatedCompleteTotalOrderingWord_valid,
    flatSourceFinsetOrdering_eq_godel]
  by_cases hless : Encodable.encode first < Encodable.encode second
  · have hreverse :
        ¬ Encodable.encode second < Encodable.encode first :=
      Nat.not_lt_of_gt hless
    simp only [encodedWordOrderingWord, encodedWordOrderingFirst, flatSourceNaturalOrdering, hless,
        ↓reduceIte,
        encodedWordOrderingSecond, List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
            List.tail_cons,
        Bool.and_true, hreverse, decide_false]
  · by_cases hreverse :
        Encodable.encode second < Encodable.encode first
    · simp only [encodedWordOrderingWord, encodedWordOrderingFirst, flatSourceNaturalOrdering,
        hless, ↓reduceIte,
          hreverse, encodedWordOrderingSecond, List.headD_eq_head?_getD, List.head?_cons,
              Option.getD_some, List.tail_cons,
          Bool.and_self, decide_true]
    · simp only [encodedWordOrderingWord, encodedWordOrderingFirst, flatSourceNaturalOrdering,
        hless, ↓reduceIte,
          hreverse, encodedWordOrderingSecond, List.headD_eq_head?_getD, List.head?_cons,
              Option.getD_some, List.tail_cons,
          Bool.and_false, decide_false]

end CNFAnnotatedSourceCompleteFiniteSetComparatorSourceCert

namespace CNFFiveFamilyForbiddenWholeClauseWorkerTM

open Computability Turing GapCVP.CL GapCVP.ThreeCNFReduction
open GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceOriginalSourcePreservingTM
open GapCVP.CNFGuardedFiveFamilyTagDispatchTM GapCVP.CNFFiveFamilyFlatSortedLiteralFamilies
open GapCVP.CNFFiveFamilyForbiddenWindowCoordinateTM

/-- Internal support shared across GapCVP continuation modules. -/
theorem fiveFamilyForbiddenOneBit_exists
    (marker : List Bool → List Bool)
    (hmarker : ∀ input, (marker input).length = 1)
    (input : List Bool) :
    ∃ bit : Bool, marker input = [bit] := by
  cases hbits : marker input with
  | nil =>
      simpa only [List.ne_cons_self, exists_const, hbits, List.length_nil, zero_ne_one]
          using hmarker input
  | cons bit remaining =>
      have hremaining : remaining = [] := by
        have hlength := hmarker input
        simp only [hbits, List.length_cons, Nat.add_eq_right, List.length_eq_zero_iff] at hlength
        exact hlength
      exact ⟨bit, by simp only [hremaining]⟩

private def fiveFamilyForbiddenOneBitSelectionWord
    (marker : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  (marker input).headD false :: input

private noncomputable def fiveFamilyForbiddenOneBitSelectionComputable
    {marker : List Bool → List Bool}
    (computer : BitTM marker)
    (hmarker : ∀ input, (marker input).length = 1) :
    BitTM
      (fiveFamilyForbiddenOneBitSelectionWord marker) := by
  have preserved := originalSourcePreservingComputable computer
  have physical := GapCVP.TMComposition.computableInPolyTime
    preserved keepFirstDropSecondComputable
  have hequality :
      (fun input : List Bool =>
        keepFirstDropSecondWord
          (originalSourcePreservingOutput marker input)) =
        fiveFamilyForbiddenOneBitSelectionWord marker := by
    funext input
    obtain ⟨bit, hbit⟩ :=
      fiveFamilyForbiddenOneBit_exists marker hmarker input
    simp only [keepFirstDropSecondWord, originalSourcePreservingOutput, hbit, List.cons_append,
        List.nil_append,
        List.tail_cons, fiveFamilyForbiddenOneBitSelectionWord, List.headD_eq_head?_getD,
            List.head?_cons, Option.getD_some]
  rw [← hequality]
  simpa only [Function.comp_def] using physical

/-- Internal support shared across GapCVP continuation modules. -/
def fiveForbiddenOneBitGuardedWord
    (marker worker : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  if (marker input).headD false then worker input else []

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def fiveForbiddenOneBitGuardedComputable
    {marker worker : List Bool → List Bool}
    (hmarker : BitTM marker)
    (hunique : ∀ input, (marker input).length = 1)
    (hworker : BitTM worker) :
    BitTM
      (fiveForbiddenOneBitGuardedWord marker worker) := by
  exact sourcePreservingConditionalComputable
    (fiveFamilyForbiddenOneBitSelectionComputable hmarker hunique)
    hworker []

/-- GapCVP reduction support. -/
def fiveFamilyForbiddenEncodedMinimum
    {α : Type} [Encodable α]
    (first second : α) : α :=
  if Encodable.encode first < Encodable.encode second
    then first else second

/-- GapCVP reduction support. -/
def fiveFamilyForbiddenEncodedMaximum
    {α : Type} [Encodable α]
    (first second : α) : α :=
  if Encodable.encode first < Encodable.encode second
    then second else first

/-- GapCVP reduction support. -/
def fiveForbiddenEncodedSortedAtoms
    {α : Type} [Encodable α]
    (first second third fourth : α) : α × α × α × α :=
  let firstLow := fiveFamilyForbiddenEncodedMinimum first second
  let firstHigh := fiveFamilyForbiddenEncodedMaximum first second
  let secondLow := fiveFamilyForbiddenEncodedMinimum third fourth
  let secondHigh := fiveFamilyForbiddenEncodedMaximum third fourth
  let outerLow :=
    fiveFamilyForbiddenEncodedMinimum firstLow secondLow
  let middleLeft :=
    fiveFamilyForbiddenEncodedMaximum firstLow secondLow
  let middleRight :=
    fiveFamilyForbiddenEncodedMinimum firstHigh secondHigh
  let outerHigh :=
    fiveFamilyForbiddenEncodedMaximum firstHigh secondHigh
  (outerLow,
    fiveFamilyForbiddenEncodedMinimum middleLeft middleRight,
    fiveFamilyForbiddenEncodedMaximum middleLeft middleRight,
    outerHigh)

/-- GapCVP reduction support. -/
def fiveForbiddenEncodedSortedAtomList
    {α : Type} [Encodable α]
    (first second third fourth : α) : List α :=
  let sorted := fiveForbiddenEncodedSortedAtoms
    first second third fourth
  [sorted.1, sorted.2.1, sorted.2.2.1, sorted.2.2.2]

private theorem fiveFamilyForbiddenEncodedSortedAtomList_mem
    {α : Type} [Encodable α]
    (first second third fourth atom : α) :
    atom ∈ fiveForbiddenEncodedSortedAtomList
      first second third fourth ↔
      atom = first ∨ atom = second ∨
        atom = third ∨ atom = fourth := by
  simp only [fiveForbiddenEncodedSortedAtomList,
    fiveForbiddenEncodedSortedAtoms,
    fiveFamilyForbiddenEncodedMinimum,
    fiveFamilyForbiddenEncodedMaximum]
  split_ifs <;> simp_all <;> aesop

theorem fiveFamilyForbiddenEncodedSortedAtomList_pairwise
    {α : Type} [Encodable α]
    (first second third fourth : α) :
    (fiveForbiddenEncodedSortedAtomList
      first second third fourth).Pairwise
        (fun left right =>
          Encodable.encode left ≤ Encodable.encode right) := by
  simp only [fiveForbiddenEncodedSortedAtomList,
    fiveForbiddenEncodedSortedAtoms,
    fiveFamilyForbiddenEncodedMinimum,
    fiveFamilyForbiddenEncodedMaximum]
  split_ifs <;>
    simp_all [List.pairwise_cons] <;>
    omega

/-- GapCVP reduction support. -/
def fiveForbiddenWindowSortedUniqueLiteralList
    {T S : ℕ}
    (window : Window T) (symbols : WindowSymbols S) :
    List (SignedLiteral T S) :=
  (fiveForbiddenEncodedSortedAtomList
    (fiveForbiddenWindowSourceVariable window symbols .left)
    (fiveForbiddenWindowSourceVariable window symbols .center)
    (fiveForbiddenWindowSourceVariable window symbols .right)
    (fiveForbiddenWindowSourceVariable window symbols .next)).dedup.map
      negative

private theorem fiveFamilyForbiddenWindowSortedUniqueLiteralList_mem
    {T S : ℕ}
    (window : Window T) (symbols : WindowSymbols S)
    (literal : SignedLiteral T S) :
    literal ∈
        fiveForbiddenWindowSortedUniqueLiteralList window symbols ↔
      literal ∈ transitionClause window symbols := by
  simp only [fiveForbiddenWindowSortedUniqueLiteralList,
    List.mem_map, List.mem_dedup,
    fiveFamilyForbiddenEncodedSortedAtomList_mem,
    transitionClause, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨atom, hatom, rfl⟩
    rcases hatom with h | h | h | h
    · left
      simpa only [fiveForbiddenWindowSourceVariable] using congrArg negative h
    · right
      left
      simpa only [fiveForbiddenWindowSourceVariable] using congrArg negative h
    · right
      right
      left
      simpa only [fiveForbiddenWindowSourceVariable] using congrArg negative h
    · right
      right
      right
      simpa only [fiveForbiddenWindowSourceVariable] using congrArg negative h
  · intro hmember
    rcases hmember with h | h | h | h
    · refine ⟨fiveForbiddenWindowSourceVariable
        window symbols .left, Or.inl rfl, ?_⟩
      simpa only [fiveForbiddenWindowSourceVariable] using h.symm
    · refine ⟨fiveForbiddenWindowSourceVariable
        window symbols .center, Or.inr (Or.inl rfl), ?_⟩
      simpa only [fiveForbiddenWindowSourceVariable] using h.symm
    · refine ⟨fiveForbiddenWindowSourceVariable
        window symbols .right, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
      simpa only [fiveForbiddenWindowSourceVariable] using h.symm
    · refine ⟨fiveForbiddenWindowSourceVariable
        window symbols .next, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
      simpa only [fiveForbiddenWindowSourceVariable] using h.symm

private theorem fiveFamilyForbiddenWindowSortedUniqueLiteralList_nodup
    {T S : ℕ}
    (window : Window T) (symbols : WindowSymbols S) :
    (fiveForbiddenWindowSortedUniqueLiteralList
      window symbols).Nodup := by
  unfold fiveForbiddenWindowSortedUniqueLiteralList
  apply (List.nodup_dedup _).map
  intro first second hequal
  exact congrArg Prod.fst hequal

private theorem fiveFamilyForbiddenNegativeSourceCode_monotone
    {T S : ℕ} (first second : Variable T S)
    (horder : Encodable.encode first ≤ Encodable.encode second) :
    Encodable.encode (negative first) ≤
      Encodable.encode (negative second) := by
  rcases lt_or_eq_of_le horder with hless | hequal
  · change Nat.pair (Encodable.encode first)
        (Encodable.encode false) ≤
      Nat.pair (Encodable.encode second)
        (Encodable.encode false)
    apply Nat.le_of_lt
    apply Nat.pair_lt_pair_left
    exact hless
  · have hatoms : first = second :=
      Encodable.encode_injective hequal
    subst second
    exact le_rfl

private theorem fiveFamilyForbiddenWindowSortedUniqueLiteralList_pairwise
    {T S : ℕ}
    (window : Window T) (symbols : WindowSymbols S) :
    (fiveForbiddenWindowSortedUniqueLiteralList
      window symbols).Pairwise
        (fun first second =>
          Encodable.encode first ≤ Encodable.encode second) := by
  unfold fiveForbiddenWindowSortedUniqueLiteralList
  rw [List.pairwise_map]
  apply List.Pairwise.imp
    (fun {first second} horder =>
      fiveFamilyForbiddenNegativeSourceCode_monotone
        first second horder)
  apply List.Pairwise.sublist
    (List.dedup_sublist _)
  exact fiveFamilyForbiddenEncodedSortedAtomList_pairwise
    (fiveForbiddenWindowSourceVariable window symbols .left)
    (fiveForbiddenWindowSourceVariable window symbols .center)
    (fiveForbiddenWindowSourceVariable window symbols .right)
    (fiveForbiddenWindowSourceVariable window symbols .next)

theorem sortedElements_transitionClause_eq_sortedNetwork
    {T S : ℕ}
    (window : Window T) (symbols : WindowSymbols S) :
    sortedElements (transitionClause window symbols) =
      fiveForbiddenWindowSortedUniqueLiteralList
        window symbols := by
  apply sortedElements_eq_of_nodup_source_pairwise
  · exact fiveFamilyForbiddenWindowSortedUniqueLiteralList_mem
      window symbols
  · exact fiveFamilyForbiddenWindowSortedUniqueLiteralList_nodup
      window symbols
  · exact fiveFamilyForbiddenWindowSortedUniqueLiteralList_pairwise
      window symbols

end CNFFiveFamilyForbiddenWholeClauseWorkerTM

namespace CNFFiveFamilyForbiddenWholeClauseSourceCert

open Computability Turing GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.CNFFiveFamilyForbiddenWindowCoordinateTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseWorkerTM

/-- Internal support shared across GapCVP continuation modules. -/
def fiveForbiddenRawSourceLessMarker
    (first second : List Bool → List Bool) :
    List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput first second

/-- Internal support shared across GapCVP continuation modules. -/
def fiveForbiddenRawSourceNotLessMarker
    (first second : List Bool → List Bool) :
    List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    (fiveForbiddenRawSourceLessMarker first second)

/-- Internal support shared across GapCVP continuation modules. -/
theorem fiveForbiddenRawSourceLessMarker_length
    (first second : List Bool → List Bool)
    (input : List Bool) :
    (fiveForbiddenRawSourceLessMarker
      first second input).length = 1 :=
  fourFamilyComputedUnaryLessBitOutput_length
    first second input

/-- Internal support shared across GapCVP continuation modules. -/
theorem fiveFamilyForbiddenRawSourceNotLessMarker_length
    (first second : List Bool → List Bool)
    (input : List Bool) :
    (fiveForbiddenRawSourceNotLessMarker
      first second input).length = 1 := by
  obtain ⟨bit, hbit⟩ := fiveFamilyForbiddenOneBit_exists
    (fiveForbiddenRawSourceLessMarker first second)
    (fiveForbiddenRawSourceLessMarker_length
      first second)
    input
  have hnot := fourFamilyBooleanNotOutput_bit
    (fiveForbiddenRawSourceLessMarker first second)
    input bit hbit
  simpa only [fiveForbiddenRawSourceNotLessMarker, List.length_cons, List.length_nil, zero_add]
      using
      congrArg List.length hnot

end CNFFiveFamilyForbiddenWholeClauseSourceCert

end GapCVP

end
