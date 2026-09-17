/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part08B

/-! # GapCVP proof, part 08, continuation 03 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFAnnotatedSourceCompleteBubbleSortSourceCert

open Turing GapCVP.CL GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold

open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFAnnotatedSourceClausePairPreparationTM

open GapCVP.CNFAnnotatedSourceClauseBubblePassTM

open GapCVP.CNFAnnotatedSourceCompleteFiniteSetComparatorSourceCert

open GapCVP.CNFAnnotatedSourceCompleteBubbleSortTM

end CNFAnnotatedSourceCompleteBubbleSortSourceCert

namespace CNFAnnotatedSourceCompleteSortedDedupTM

open Turing GapCVP.CL GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputPolynomialCompositionClosure
open GapCVP.OutputBoundedDependentRecordFold GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFEncodedClauseSort GapCVP.CNFFlatSourceOrder GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFTypedRecordWorkerTM GapCVP.CNFGuardedFiveFamilyTagDispatchTM
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM GapCVP.CNFAnnotatedSourceClauseBubblePassTM
open GapCVP.CNFAnnotatedSourceCompleteFiniteSetComparatorSourceCert
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.SourceFourFamilyTaggedPredicateDispatchTM

private def annotatedSortedDedupSourceOrdering
    (input : List Bool) : List Bool :=
  firstFieldSuffix
    (annotatedBundledPairComparisonWord
      annotatedCompleteTotalSourceComparison
      (firstFieldContents input))

private noncomputable def flatAnnotatedSortedDedupSourceOrderingComputable :
    BitTM
      annotatedSortedDedupSourceOrdering := by
  have hcomparison := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable
    (flatAnnotatedBundledPairComparisonComputable
      flatAnnotatedCompleteTotalSourceComparisonComputable)
  have physical := GapCVP.TMComposition.computableInPolyTime
    hcomparison firstFieldSuffixComputable
  change BitTM
    (fun input : List Bool =>
      firstFieldSuffix
        (annotatedBundledPairComparisonWord
          annotatedCompleteTotalSourceComparison
          (firstFieldContents input)))
  simpa only [Function.comp_def] using physical

private def flatAnnotatedSortedDedupEqualityBit
    (input : List Bool) : List Bool :=
  fiveFamilyOriginalHeadBitWord
    (encodedOrderingEqualityBitWord
      (annotatedSortedDedupSourceOrdering input))

private noncomputable def flatAnnotatedSortedDedupEqualityBitComputable :
    BitTM
      flatAnnotatedSortedDedupEqualityBit := by
  have hequality := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedSortedDedupSourceOrderingComputable
    encodedOrderingEqualityBitComputable
  have physical := GapCVP.TMComposition.computableInPolyTime
    hequality fiveFamilyOriginalHeadBitComputable
  change BitTM
    (fun input : List Bool =>
      fiveFamilyOriginalHeadBitWord
        (encodedOrderingEqualityBitWord
          (annotatedSortedDedupSourceOrdering input)))
  simpa only [Function.comp_def] using physical

private def annotatedSortedDedupSecondPresence
    (input : List Bool) : List Bool :=
  fiveFamilyOriginalHeadBitWord
    (firstFieldSuffix (firstFieldContents input))

private noncomputable def flatAnnotatedSortedDedupSecondPresenceComputable :
    BitTM
      annotatedSortedDedupSecondPresence := by
  have hpending := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable firstFieldSuffixComputable
  have physical := GapCVP.TMComposition.computableInPolyTime
    hpending fiveFamilyOriginalHeadBitComputable
  change BitTM
    (fun input : List Bool =>
      fiveFamilyOriginalHeadBitWord
        (firstFieldSuffix (firstFieldContents input)))
  simpa only [Function.comp_def] using physical

private def annotatedSortedDedupEqualityQuery
    (input : List Bool) : List Bool :=
  flatAnnotatedSortedDedupEqualityBit input ++
    annotatedSortedDedupSecondPresence input

private noncomputable def flatAnnotatedSortedDedupEqualityQueryComputable :
    BitTM
      annotatedSortedDedupEqualityQuery := by
  exact pointwiseAppendComputable
    flatAnnotatedSortedDedupEqualityBitComputable
    flatAnnotatedSortedDedupSecondPresenceComputable

private def annotatedSortedDedupEffectiveMarker : List Bool → List Bool :=
  markerConditionalOutput fiveFamilyOriginalHeadBitWord [false] ∘
    annotatedSortedDedupEqualityQuery

private noncomputable def flatAnnotatedSortedDedupEffectiveMarkerComputable :
    BitTM
      annotatedSortedDedupEffectiveMarker := by
  have hconditional := markerConditionalComputable
    fiveFamilyOriginalHeadBitComputable [false]
  exact GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedSortedDedupEqualityQueryComputable hconditional

private def flatAnnotatedSortedDedupNextPending
    (input : List Bool) : List Bool :=
  firstFieldSuffix (firstFieldContents input)

private noncomputable def flatAnnotatedSortedDedupNextPendingComputable :
    BitTM
      flatAnnotatedSortedDedupNextPending := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable firstFieldSuffixComputable
  change BitTM
    (fun input : List Bool =>
      firstFieldSuffix (firstFieldContents input))
  exact physical

private def flatAnnotatedSortedDedupArchive
    (input : List Bool) : List Bool :=
  firstFieldContents (firstFieldSuffix input)

private noncomputable def flatAnnotatedSortedDedupArchiveComputable :
    BitTM
      flatAnnotatedSortedDedupArchive := by
  have htail := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable
  change BitTM
    (fun input : List Bool =>
      firstFieldContents (firstFieldSuffix input))
  exact htail

private def flatAnnotatedSortedDedupSelected
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
    (firstFieldContents (firstFieldContents input))

private noncomputable def flatAnnotatedSortedDedupSelectedComputable :
    BitTM
      flatAnnotatedSortedDedupSelected := by
  have hinner := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable firstFieldContentsComputable
  have physical := GapCVP.TMComposition.computableInPolyTime
    hinner structuralPrefixWriterComputable
  change BitTM
    (fun input : List Bool =>
      lengthPrefixedWord
        (firstFieldContents (firstFieldContents input)))
  simpa only [Function.comp_def] using physical

private def flatAnnotatedSortedDedupDropStep
    (input : List Bool) : List Bool :=
  flatAnnotatedBubblePassState
    (flatAnnotatedSortedDedupNextPending input)
    (flatAnnotatedSortedDedupArchive input)

private noncomputable def flatAnnotatedSortedDedupDropStepComputable :
    BitTM
      flatAnnotatedSortedDedupDropStep := by
  have hpending := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedSortedDedupNextPendingComputable
    structuralPrefixWriterComputable
  have harchive := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedSortedDedupArchiveComputable
    structuralPrefixWriterComputable
  have physical := pointwiseAppendComputable hpending harchive
  change BitTM
    (fun input : List Bool =>
      lengthPrefixedWord
          (flatAnnotatedSortedDedupNextPending input) ++
        lengthPrefixedWord
          (flatAnnotatedSortedDedupArchive input))
  simpa only [Function.comp_def] using physical

private def flatAnnotatedSortedDedupEmitStep
    (input : List Bool) : List Bool :=
  flatAnnotatedBubblePassState
    (flatAnnotatedSortedDedupNextPending input)
    (flatAnnotatedSortedDedupArchive input ++
      flatAnnotatedSortedDedupSelected input)

private noncomputable def flatAnnotatedSortedDedupEmitStepComputable :
    BitTM
      flatAnnotatedSortedDedupEmitStep := by
  have hpending := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedSortedDedupNextPendingComputable
    structuralPrefixWriterComputable
  have harchive := pointwiseAppendComputable
    flatAnnotatedSortedDedupArchiveComputable
    flatAnnotatedSortedDedupSelectedComputable
  have harchivePrefix := GapCVP.TMComposition.computableInPolyTime
    harchive structuralPrefixWriterComputable
  have physical := pointwiseAppendComputable
    hpending harchivePrefix
  change BitTM
    (fun input : List Bool =>
      lengthPrefixedWord
          (flatAnnotatedSortedDedupNextPending input) ++
        lengthPrefixedWord
          (flatAnnotatedSortedDedupArchive input ++
            flatAnnotatedSortedDedupSelected input))
  simpa only [Function.comp_def] using physical

private def flatAnnotatedSortedDedupShapeTag
    (input : List Bool) : List Bool :=
  annotatedSortedDedupEffectiveMarker input ++ [false]

private noncomputable def flatAnnotatedSortedDedupShapeTagComputable :
    BitTM
      flatAnnotatedSortedDedupShapeTag := by
  exact pointwiseAppendComputable
    flatAnnotatedSortedDedupEffectiveMarkerComputable
    (sourceFixedWordComputable [false])

private def flatAnnotatedSortedDedupDispatchInput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (flatAnnotatedSortedDedupShapeTag input) ++ input

private noncomputable def flatAnnotatedSortedDedupDispatchInputComputable :
    BitTM
      flatAnnotatedSortedDedupDispatchInput := by
  have htag := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedSortedDedupShapeTagComputable
    structuralPrefixWriterComputable
  have physical := pointwiseAppendComputable htag
    (Turing.idComputableInPolyTime bitEncoding)
  change BitTM
    (fun input : List Bool =>
      lengthPrefixedWord (flatAnnotatedSortedDedupShapeTag input) ++ input)
  simpa only [Function.comp_def, id_eq] using physical

private def flatAnnotatedSortedDedupStep : List Bool → List Bool :=
  fourFamilyTaggedPredicateMarker
    flatAnnotatedSortedDedupEmitStep
    (fun _ => [])
    flatAnnotatedSortedDedupDropStep
    (fun _ => []) ∘
      flatAnnotatedSortedDedupDispatchInput

private noncomputable def flatAnnotatedSortedDedupStepComputable :
    BitTM
      flatAnnotatedSortedDedupStep := by
  have hdispatch := fourFamilyTaggedPredicateMarkerComputable
    flatAnnotatedSortedDedupEmitStepComputable
    (sourceFixedWordComputable [])
    flatAnnotatedSortedDedupDropStepComputable
    (sourceFixedWordComputable [])
  exact GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedSortedDedupDispatchInputComputable hdispatch

@[simp] private theorem flatAnnotatedSortedDedupEffectiveMarker_eq
    (input : List Bool) :
    annotatedSortedDedupEffectiveMarker input =
      [((encodedOrderingEqualityBitWord
          (annotatedSortedDedupSourceOrdering input)).headD false &&
        (firstFieldSuffix (firstFieldContents input)).headD false)] := by
  unfold annotatedSortedDedupEffectiveMarker
  rw [Function.comp_apply]
  unfold annotatedSortedDedupEqualityQuery
    flatAnnotatedSortedDedupEqualityBit
    annotatedSortedDedupSecondPresence
  rw [fiveFamilyOriginalHeadBitWord_eq,
    fiveFamilyOriginalHeadBitWord_eq]
  cases (encodedOrderingEqualityBitWord
    (annotatedSortedDedupSourceOrdering input)).headD false <;>
    cases (firstFieldSuffix (firstFieldContents input)).headD false <;>
    rfl

private theorem flatAnnotatedSortedDedupStep_eq
    (input : List Bool) :
    flatAnnotatedSortedDedupStep input =
      if (encodedOrderingEqualityBitWord
            (annotatedSortedDedupSourceOrdering input)).headD false &&
          (firstFieldSuffix (firstFieldContents input)).headD false then
        flatAnnotatedSortedDedupDropStep input
      else flatAnnotatedSortedDedupEmitStep input := by
  unfold flatAnnotatedSortedDedupStep
  rw [Function.comp_apply]
  unfold flatAnnotatedSortedDedupDispatchInput
  unfold flatAnnotatedSortedDedupShapeTag
  rw [flatAnnotatedSortedDedupEffectiveMarker_eq]
  cases hbit :
      (encodedOrderingEqualityBitWord
          (annotatedSortedDedupSourceOrdering input)).headD false &&
        (firstFieldSuffix (firstFieldContents input)).headD false with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      change fourFamilyTaggedPredicateMarker _ _ _ _
        (lengthPrefixedWord [false, false] ++ input) = _
      rw [sourceFourFamilyTaggedPredicateMarker_interpolation]
  | true =>
      simp only [↓reduceIte]
      change fourFamilyTaggedPredicateMarker _ _ _ _
        (lengthPrefixedWord [true, false] ++ input) = _
      rw [sourceFourFamilyTaggedPredicateMarker_diagonal]

private theorem flatAnnotatedSortedDedupDropStep_length_le
    (input : List Bool) :
    (flatAnnotatedSortedDedupDropStep input).length ≤
      input.length + 2 := by
  have hsource := annotatedStructuralTwoFieldAccounting input
  have hpending := annotatedStructuralFieldAccounting
    (firstFieldContents input)
  simp only [flatAnnotatedSortedDedupDropStep,
    flatAnnotatedBubblePassState,
    flatAnnotatedSortedDedupNextPending,
    flatAnnotatedSortedDedupArchive,
    List.length_append, lengthPrefixedWord_length]
  omega

private theorem flatAnnotatedSortedDedupEmitStep_length_le
    (input : List Bool) :
    (flatAnnotatedSortedDedupEmitStep input).length ≤
      input.length + 4 := by
  have hsource := annotatedStructuralTwoFieldAccounting input
  have hpending := annotatedStructuralFieldAccounting
    (firstFieldContents input)
  simp only [flatAnnotatedSortedDedupEmitStep,
    flatAnnotatedBubblePassState,
    flatAnnotatedSortedDedupNextPending,
    flatAnnotatedSortedDedupArchive,
    flatAnnotatedSortedDedupSelected,
    List.length_append, lengthPrefixedWord_length]
  omega

private theorem flatAnnotatedSortedDedupStep_length_le
    (input : List Bool) :
    (flatAnnotatedSortedDedupStep input).length ≤
      input.length + 4 := by
  rw [flatAnnotatedSortedDedupStep_eq]
  split
  · have hdrop := flatAnnotatedSortedDedupDropStep_length_le input
    omega
  · exact flatAnnotatedSortedDedupEmitStep_length_le input

private theorem flatAnnotatedSortedDedupStep_iterate_length_le
    (input : List Bool) (count : ℕ) :
    (((flatAnnotatedSortedDedupStep)^[count]) input).length ≤
      input.length + 4 * count := by
  induction count with
  | zero => simp only [Function.iterate_zero, id_eq, mul_zero, add_zero, Std.le_refl]
  | succ count ih =>
      rw [Function.iterate_succ_apply']
      have hstep := flatAnnotatedSortedDedupStep_length_le
        (((flatAnnotatedSortedDedupStep)^[count]) input)
      omega

private theorem flatAnnotatedSortedDedup_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates
      flatAnnotatedSortedDedupStep
      (5 * Polynomial.X) := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage hstage
  have hseed := parsedUnaryFold_seed_length_le
    input count seed hparse
  have hcount := parsedUnaryFold_count_le_length
    input count seed hparse
  have hiterate := flatAnnotatedSortedDedupStep_iterate_length_le
    seed stage
  simp only [Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

private noncomputable def flatAnnotatedSortedDedupFoldComputable :
    BitTM
      (boundedRecordFoldOutput flatAnnotatedSortedDedupStep) :=
  boundedDependentRecordFoldComputable
    flatAnnotatedSortedDedupStepComputable
    (5 * Polynomial.X)
    flatAnnotatedSortedDedup_polynomiallyBoundedFoldStates

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAnnotatedSortedDedupSourceClauseRecord_ne_nil
    {T S : ℕ} (clause : Clause T S) :
    flatSourceClauseAnnotatedRecord clause ≠ [] := by
  intro hrecord
  have hlength := congrArg List.length hrecord
  simp only [flatSourceClauseAnnotatedRecord, List.append_assoc, List.length_append,
      lengthPrefixedWord_length,
      flatSourceClauseUnaryCountPayload_length, List.length_nil, Nat.add_eq_zero_iff, mul_eq_zero,
          OfNat.ofNat_ne_zero,
      List.length_eq_zero_iff, false_or, one_ne_zero, and_false, and_self] at hlength

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAnnotatedSortedDedupHeadBit_nonemptyPrefix
    (record suffix : List Bool) (hrecord : record ≠ []) :
    fiveFamilyOriginalHeadBitWord
        (lengthPrefixedWord record ++ suffix) = [true] := by
  cases record with
  | nil => exact False.elim (hrecord rfl)
  | cons head tail =>
      simp only [lengthPrefixedWord, List.length_cons, List.replicate_succ, List.cons_append,
          List.append_assoc,
          fiveFamilyOriginalHeadBitWord_eq, List.headD_eq_head?_getD, List.head?_cons,
              Option.getD_some]

private theorem flatAnnotatedSortedDedupSourceOrdering_originalClauseState
    {T S : ℕ} (first second : Clause T S)
    (remaining emitted : List (Clause T S)) :
    annotatedSortedDedupSourceOrdering
        (flatAnnotatedBubbleClauseState
          (first :: second :: remaining) emitted) =
      encodedWordOrderingWord
        (flatSortedSourceListOrdering
          (flatSourceFinsetCodes first)
          (flatSourceFinsetCodes second)) := by
  simp only [annotatedSortedDedupSourceOrdering,
    flatAnnotatedBubbleClauseState,
    flatAnnotatedBubblePassState,
    flatAnnotatedBundledClauseStream,
    List.flatMap_cons,
    firstFieldContents_valid]
  unfold annotatedBundledPairComparisonWord
  rw [← List.append_assoc,
    flatAnnotatedBundledPairComparisonInput_records]
  unfold annotatedCompleteTotalSourceComparison
  rw [firstFieldSuffix_valid,
    flatAnnotatedCompleteOriginalClausePair_records,
    flatAnnotatedCompleteTotalOrderingWord_valid]

@[simp] private theorem flatAnnotatedSortedDedupEqualityBit_originalClauseState
    {T S : ℕ} (first second : Clause T S)
    (remaining emitted : List (Clause T S)) :
    flatAnnotatedSortedDedupEqualityBit
        (flatAnnotatedBubbleClauseState
          (first :: second :: remaining) emitted) =
      [decide (first = second)] := by
  unfold flatAnnotatedSortedDedupEqualityBit
  rw [flatAnnotatedSortedDedupSourceOrdering_originalClauseState,
    encodedOrderingEqualityBitWord_ordering,
    fiveFamilyOriginalHeadBitWord_eq]
  simp only [List.headD_cons]
  simp only [flatSourceFinsetOrdering_equal_iff]

@[simp] private theorem flatAnnotatedSortedDedupSecondPresence_originalClausePair
    {T S : ℕ} (first second : Clause T S)
    (remaining emitted : List (Clause T S)) :
    annotatedSortedDedupSecondPresence
        (flatAnnotatedBubbleClauseState
          (first :: second :: remaining) emitted) = [true] := by
  unfold annotatedSortedDedupSecondPresence
  simp only [flatAnnotatedBubbleClauseState,
    flatAnnotatedBubblePassState,
    flatAnnotatedBundledClauseStream,
    List.flatMap_cons,
    firstFieldContents_valid,
    flatAnnotatedBundledClauseRecord,
    firstFieldSuffix_valid]
  exact flatAnnotatedSortedDedupHeadBit_nonemptyPrefix
    (flatSourceClauseAnnotatedRecord second)
    (remaining.flatMap flatAnnotatedBundledClauseRecord)
    (flatAnnotatedSortedDedupSourceClauseRecord_ne_nil second)

@[simp] private theorem flatAnnotatedSortedDedupSecondPresence_originalSingleton
    {T S : ℕ} (first : Clause T S)
    (emitted : List (Clause T S)) :
    annotatedSortedDedupSecondPresence
        (flatAnnotatedBubbleClauseState [first] emitted) = [false] := by
  have htail :
      firstFieldSuffix
          (lengthPrefixedWord
            (flatSourceClauseAnnotatedRecord first)) = [] := by
    simpa only [List.append_nil] using firstFieldSuffix_valid (flatSourceClauseAnnotatedRecord
        first) []
  simp only [annotatedSortedDedupSecondPresence, flatAnnotatedBubbleClauseState,
      flatAnnotatedBubblePassState,
      flatAnnotatedBundledClauseStream, List.flatMap_cons, flatAnnotatedBundledClauseRecord,
          List.flatMap_nil,
      List.append_nil, firstFieldContents_valid, htail, fiveFamilyOriginalHeadBitWord_eq,
          List.headD_eq_head?_getD,
      List.head?_nil, Option.getD_none]

private theorem flatAnnotatedSortedDedupEffectiveMarker_originalClausePair
    {T S : ℕ} (first second : Clause T S)
    (remaining emitted : List (Clause T S)) :
    annotatedSortedDedupEffectiveMarker
        (flatAnnotatedBubbleClauseState
          (first :: second :: remaining) emitted) =
      [decide (first = second)] := by
  unfold annotatedSortedDedupEffectiveMarker
  rw [Function.comp_apply]
  unfold annotatedSortedDedupEqualityQuery
  rw [flatAnnotatedSortedDedupEqualityBit_originalClauseState,
    flatAnnotatedSortedDedupSecondPresence_originalClausePair]
  by_cases hequal : first = second <;>
    simp [hequal, markerConditionalOutput,
      fiveFamilyOriginalHeadBitWord_eq]

private theorem flatAnnotatedSortedDedupEffectiveMarker_originalSingleton
    {T S : ℕ} (first : Clause T S)
    (emitted : List (Clause T S)) :
    annotatedSortedDedupEffectiveMarker
        (flatAnnotatedBubbleClauseState [first] emitted) = [false] := by
  unfold annotatedSortedDedupEffectiveMarker
  rw [Function.comp_apply]
  unfold annotatedSortedDedupEqualityQuery
  rw [flatAnnotatedSortedDedupSecondPresence_originalSingleton]
  unfold flatAnnotatedSortedDedupEqualityBit
  rw [fiveFamilyOriginalHeadBitWord_eq]
  cases (encodedOrderingEqualityBitWord
    (annotatedSortedDedupSourceOrdering
      (flatAnnotatedBubbleClauseState [first] emitted))).headD false <;>
    rfl

@[simp] private theorem flatAnnotatedSortedDedupDropStep_originalClauseState
    {T S : ℕ} (first : Clause T S)
    (remaining emitted : List (Clause T S)) :
    flatAnnotatedSortedDedupDropStep
        (flatAnnotatedBubbleClauseState
          (first :: remaining) emitted) =
      flatAnnotatedBubbleClauseState remaining emitted := by
  have harchive :
      firstFieldContents
          (lengthPrefixedWord
            (flatAnnotatedBundledClauseStream emitted)) =
        flatAnnotatedBundledClauseStream emitted := by
    simpa only [List.append_nil] using firstFieldContents_valid (flatAnnotatedBundledClauseStream
        emitted) []
  have harchiveFlat :
      firstFieldContents
          (lengthPrefixedWord
            (emitted.flatMap flatAnnotatedBundledClauseRecord)) =
        emitted.flatMap flatAnnotatedBundledClauseRecord := by
    simpa only [flatAnnotatedBundledClauseStream] using harchive
  unfold flatAnnotatedSortedDedupDropStep
    flatAnnotatedSortedDedupNextPending
    flatAnnotatedSortedDedupArchive
  simp only [flatAnnotatedBubbleClauseState,
    flatAnnotatedBubblePassState,
    flatAnnotatedBundledClauseStream,
    List.flatMap_cons,
    firstFieldContents_valid,
    flatAnnotatedBundledClauseRecord,
    firstFieldSuffix_valid]
  simp only [harchiveFlat]

@[simp] private theorem flatAnnotatedSortedDedupEmitStep_originalClauseState
    {T S : ℕ} (first : Clause T S)
    (remaining emitted : List (Clause T S)) :
    flatAnnotatedSortedDedupEmitStep
        (flatAnnotatedBubbleClauseState
          (first :: remaining) emitted) =
      flatAnnotatedBubbleClauseState
        remaining (emitted ++ [first]) := by
  have harchive :
      firstFieldContents
          (lengthPrefixedWord
            (flatAnnotatedBundledClauseStream emitted)) =
        flatAnnotatedBundledClauseStream emitted := by
    simpa only [List.append_nil] using firstFieldContents_valid (flatAnnotatedBundledClauseStream
        emitted) []
  have harchiveFlat :
      firstFieldContents
          (lengthPrefixedWord
            (emitted.flatMap flatAnnotatedBundledClauseRecord)) =
        emitted.flatMap flatAnnotatedBundledClauseRecord := by
    simpa only [flatAnnotatedBundledClauseStream] using harchive
  unfold flatAnnotatedSortedDedupEmitStep
    flatAnnotatedSortedDedupNextPending
    flatAnnotatedSortedDedupArchive
    flatAnnotatedSortedDedupSelected
  simp only [flatAnnotatedBubbleClauseState,
    flatAnnotatedBubblePassState,
    flatAnnotatedBundledClauseStream,
    List.flatMap_cons,
    firstFieldContents_valid,
    flatAnnotatedBundledClauseRecord,
    firstFieldSuffix_valid]
  simp only [harchiveFlat, List.flatMap_append, List.flatMap_cons,
      flatAnnotatedBundledClauseRecord,
      List.flatMap_nil, List.append_nil]

private theorem flatAnnotatedSortedDedupStep_effective
    (input : List Bool) :
    flatAnnotatedSortedDedupStep input =
      if (annotatedSortedDedupEffectiveMarker input).headD false then
        flatAnnotatedSortedDedupDropStep input
      else flatAnnotatedSortedDedupEmitStep input := by
  rw [flatAnnotatedSortedDedupStep_eq,
    flatAnnotatedSortedDedupEffectiveMarker_eq]
  rfl

@[simp] private theorem flatAnnotatedSortedDedupStep_originalClausePair
    {T S : ℕ} (first second : Clause T S)
    (remaining emitted : List (Clause T S)) :
    flatAnnotatedSortedDedupStep
        (flatAnnotatedBubbleClauseState
          (first :: second :: remaining) emitted) =
      if first = second then
        flatAnnotatedBubbleClauseState
          (second :: remaining) emitted
      else
        flatAnnotatedBubbleClauseState
          (second :: remaining) (emitted ++ [first]) := by
  rw [flatAnnotatedSortedDedupStep_effective,
    flatAnnotatedSortedDedupEffectiveMarker_originalClausePair]
  simp only [List.headD_cons]
  by_cases hequal : first = second <;>
    simp [hequal]

@[simp] private theorem flatAnnotatedSortedDedupStep_originalSingleton
    {T S : ℕ} (first : Clause T S)
    (emitted : List (Clause T S)) :
    flatAnnotatedSortedDedupStep
        (flatAnnotatedBubbleClauseState [first] emitted) =
      flatAnnotatedBubbleClauseState [] (emitted ++ [first]) := by
  rw [flatAnnotatedSortedDedupStep_effective,
    flatAnnotatedSortedDedupEffectiveMarker_originalSingleton]
  simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, Bool.false_eq_true,
      ↓reduceIte,
      flatAnnotatedSortedDedupEmitStep_originalClauseState]

private def flatAnnotatedOriginalSortedDedupAux
    {T S : ℕ} (pending emitted : List (Clause T S)) :
    List (Clause T S) :=
  match pending with
  | [] => emitted
  | [first] => emitted ++ [first]
  | first :: second :: remaining =>
      if first = second then
        flatAnnotatedOriginalSortedDedupAux
          (second :: remaining) emitted
      else
        flatAnnotatedOriginalSortedDedupAux
          (second :: remaining) (emitted ++ [first])
termination_by pending.length
decreasing_by
  all_goals
    simp only [List.length_cons]
    omega

private theorem flatAnnotatedSortedDedupStep_iterate_originalClauseState
    {T S : ℕ} (pending emitted : List (Clause T S)) :
    (((flatAnnotatedSortedDedupStep)^[pending.length])
      (flatAnnotatedBubbleClauseState pending emitted)) =
      flatAnnotatedBubbleClauseState []
        (flatAnnotatedOriginalSortedDedupAux pending emitted) := by
  cases pending with
  | nil =>
      simp only [List.length_nil, Function.iterate_zero, id_eq,
          flatAnnotatedOriginalSortedDedupAux]
  | cons first remaining =>
      cases remaining with
      | nil =>
          simp only [List.length_cons, List.length_nil, zero_add, Function.iterate_one,
              flatAnnotatedSortedDedupStep_originalSingleton, flatAnnotatedOriginalSortedDedupAux]
      | cons second tail =>
          rw [List.length_cons, Function.iterate_succ_apply,
            flatAnnotatedSortedDedupStep_originalClausePair]
          by_cases hequal : first = second
          · simp only [hequal, ↓reduceIte,
              flatAnnotatedOriginalSortedDedupAux]
            exact flatAnnotatedSortedDedupStep_iterate_originalClauseState
              (second :: tail) emitted
          · simp only [hequal, ↓reduceIte,
              flatAnnotatedOriginalSortedDedupAux]
            exact flatAnnotatedSortedDedupStep_iterate_originalClauseState
              (second :: tail) (emitted ++ [first])
termination_by pending.length
decreasing_by
  all_goals
    simp only [List.length_cons]
    omega

private theorem boundedRecordFoldOutput_flatAnnotatedSortedDedup
    {T S : ℕ} (pending emitted : List (Clause T S)) :
    boundedRecordFoldOutput flatAnnotatedSortedDedupStep
        (unaryBoundedFoldWord pending.length
          (flatAnnotatedBubbleClauseState pending emitted)) =
      flatAnnotatedBubbleClauseState []
        (flatAnnotatedOriginalSortedDedupAux pending emitted) := by
  simp only [boundedRecordFoldOutput,
    parseUnaryBoundedFold_word]
  exact flatAnnotatedSortedDedupStep_iterate_originalClauseState
    pending emitted

end CNFAnnotatedSourceCompleteSortedDedupTM

namespace CNFAnnotatedSourceCompleteSortedDedupSourceCert

open Turing GapCVP.CL GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFiniteRecordSort
open GapCVP.CNFInputDependentRecordSort GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM GapCVP.CNFAnnotatedSourceCompleteBubbleSortTM
open GapCVP.CNFAnnotatedSourceCompleteBubbleSortSourceCert
open GapCVP.CNFAnnotatedSourceCompleteSortedDedupTM

private theorem flatAnnotatedSortedDistinctHead_not_mem_tail
    {T S : ℕ} {first second : Clause T S}
    {remaining : List (Clause T S)}
    (hordered : (first :: second :: remaining).Pairwise
      (fun left right => Encodable.encode left ≤ Encodable.encode right))
    (hdistinct : first ≠ second) :
    first ∉ second :: remaining := by
  intro hmember
  rcases List.mem_cons.mp hmember with hequal | hremaining
  · exact hdistinct hequal
  · have hforward : Encodable.encode first ≤ Encodable.encode second :=
      (List.pairwise_cons.mp hordered).1 second (by simp only [List.mem_cons, true_or])
    have hbackward : Encodable.encode second ≤ Encodable.encode first :=
      (List.pairwise_cons.mp
        (List.pairwise_cons.mp hordered).2).1 first hremaining
    exact hdistinct
      (Encodable.encode_injective (Nat.le_antisymm hforward hbackward))

private theorem flatAnnotatedOriginalSortedDedupAux_eq_dedup
    {T S : ℕ} (pending emitted : List (Clause T S))
    (hordered : pending.Pairwise
      (fun first second => Encodable.encode first ≤ Encodable.encode second)) :
    flatAnnotatedOriginalSortedDedupAux pending emitted =
      emitted ++ pending.dedup := by
  induction pending using List.twoStepInduction generalizing emitted with
  | nil =>
      simp only [flatAnnotatedOriginalSortedDedupAux, List.dedup_nil, List.append_nil]
  | singleton first =>
      simp only [flatAnnotatedOriginalSortedDedupAux, List.not_mem_nil, not_false_eq_true,
          List.dedup_cons_of_notMem, List.dedup_nil]
  | cons_cons first second remaining _ ih =>
      have htail : (second :: remaining).Pairwise
          (fun left right =>
            Encodable.encode left ≤ Encodable.encode right) :=
        (List.pairwise_cons.mp hordered).2
      by_cases hequal : first = second
      · subst second
        simp only [flatAnnotatedOriginalSortedDedupAux,
          ↓reduceIte]
        have hduplicate :
            (first :: first :: remaining).dedup =
              (first :: remaining).dedup :=
          List.dedup_cons_of_mem (by simp only [List.mem_cons, true_or])
        calc
          flatAnnotatedOriginalSortedDedupAux
              (first :: remaining) emitted =
              emitted ++ (first :: remaining).dedup :=
            ih first emitted htail
          _ = emitted ++ (first :: first :: remaining).dedup :=
            congrArg (fun records => emitted ++ records)
              hduplicate.symm
      · have hnot : first ∉ second :: remaining :=
          flatAnnotatedSortedDistinctHead_not_mem_tail
            hordered hequal
        simp only [flatAnnotatedOriginalSortedDedupAux,
          hequal, ↓reduceIte]
        calc
          flatAnnotatedOriginalSortedDedupAux
              (second :: remaining) (emitted ++ [first]) =
              (emitted ++ [first]) ++
                (second :: remaining).dedup :=
            ih second (emitted ++ [first]) htail
          _ = emitted ++ (first :: second :: remaining).dedup := by
            rw [List.dedup_cons_of_notMem hnot]
            simp only [List.append_assoc, List.cons_append, List.nil_append]

private theorem flatAnnotatedOriginalSortedDedup_eq_sourceOrderedDistinctRecords
    {T S : ℕ} (pending : List (Clause T S)) :
    flatAnnotatedOriginalSortedDedupAux
        (flatAnnotatedOriginalBubbleSortAux pending []) [] =
      sourceOrderedDistinctRecords pending := by
  let ordered := flatAnnotatedOriginalBubbleSortAux pending []
  have hordered : ordered.Pairwise
      (fun first second =>
        Encodable.encode first ≤ Encodable.encode second) :=
    flatAnnotatedOriginalBubbleSort_pairwise pending
  have hpermutation : ordered.Perm pending := by
    simpa only [List.append_nil] using
      flatAnnotatedOriginalBubbleSortAux_perm pending []
  rw [flatAnnotatedOriginalSortedDedupAux_eq_dedup
    ordered [] hordered]
  simp only [List.nil_append]
  symm
  apply sourceOrderedDistinctRecords_eq_of_nodup_pairwise
    pending ordered.dedup
  · intro record
    simpa only [List.mem_dedup] using
      (hpermutation.mem_iff (a := record))
  · exact List.nodup_dedup ordered
  · exact List.Pairwise.sublist
      (List.dedup_sublist ordered) hordered

private def annotatedCompleteSortedDedupPreparedInput
    (input : List Bool) : List Bool :=
  flatAnnotatedCompleteBubbleCount input ++ false ::
    flatAnnotatedBubblePassState
      (annotatedCompleteBubbleSortedSourceOutput input) []

private noncomputable def flatAnnotatedCompleteSortedDedupPreparedInputComputable :
    BitTM
      annotatedCompleteSortedDedupPreparedInput := by
  have hpending := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteBubbleSortedSourceComputable
    structuralPrefixWriterComputable
  have hstate := pointwiseAppendComputable hpending
    (sourceFixedWordComputable (lengthPrefixedWord []))
  have hdelimited := pointwiseAppendComputable
    (sourceFixedWordComputable [false]) hstate
  have physical := pointwiseAppendComputable
    (annotatedSourceFieldAtComputable 1) hdelimited
  change BitTM
    (fun input : List Bool =>
      flatAnnotatedSourceFieldAt 1 input ++
        false ::
          (lengthPrefixedWord
              (annotatedCompleteBubbleSortedSourceOutput input) ++
            lengthPrefixedWord []))
  simpa only [Function.comp_def,
    List.cons_append, List.nil_append] using physical

private def annotatedCompleteSortedDistinctSourceOutput :
    List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix ∘
    boundedRecordFoldOutput flatAnnotatedSortedDedupStep ∘
      annotatedCompleteSortedDedupPreparedInput

private noncomputable def flatAnnotatedCompleteSortedDistinctSourceComputable :
    BitTM
      annotatedCompleteSortedDistinctSourceOutput := by
  have hfold := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteSortedDedupPreparedInputComputable
    flatAnnotatedSortedDedupFoldComputable
  have htail := GapCVP.TMComposition.computableInPolyTime
    hfold firstFieldSuffixComputable
  have physical := GapCVP.TMComposition.computableInPolyTime
    htail firstFieldContentsComputable
  simpa only [annotatedCompleteSortedDistinctSourceOutput,
    Function.comp_def] using physical

@[simp] private theorem flatAnnotatedCompleteSortedDedupPreparedInput_originalClauseState
    {T S : ℕ} (pending : List (Clause T S)) :
    annotatedCompleteSortedDedupPreparedInput
        (annotatedCompleteBubbleSortState
          (flatAnnotatedBundledClauseStream pending)
          (List.replicate pending.length true) []) =
      unaryBoundedFoldWord
        (flatAnnotatedOriginalBubbleSortAux pending []).length
        (flatAnnotatedBubbleClauseState
          (flatAnnotatedOriginalBubbleSortAux pending []) []) := by
  have hlength :
      (flatAnnotatedOriginalBubbleSortAux pending []).length =
        pending.length := by
    simpa only [List.append_nil] using
      (flatAnnotatedOriginalBubbleSortAux_perm pending []).length_eq
  have hsorted :
      annotatedCompleteBubbleSortedSourceOutput
        (annotatedCompleteBubbleSortState
          (flatAnnotatedBundledClauseStream pending)
          (List.replicate pending.length true) []) =
        flatAnnotatedBundledClauseStream
          (flatAnnotatedOriginalBubbleSortAux pending []) := by
    simpa only [flatAnnotatedBundledClauseStream, List.flatMap_nil] using
        flatAnnotatedCompleteBubbleSortedSourceOutput_valid pending []
  simp only [annotatedCompleteSortedDedupPreparedInput,
    flatAnnotatedCompleteBubbleSortState_count,
    hsorted]
  simp only [flatAnnotatedBundledClauseStream, unaryBoundedFoldWord, hlength,
      flatAnnotatedBubbleClauseState,
      List.flatMap_nil]

private theorem flatAnnotatedCompleteSortedDistinctSourceOutput_valid
    {T S : ℕ} (pending : List (Clause T S)) :
    annotatedCompleteSortedDistinctSourceOutput
        (annotatedCompleteBubbleSortState
          (flatAnnotatedBundledClauseStream pending)
          (List.replicate pending.length true) []) =
      flatAnnotatedBundledClauseStream
        (sourceOrderedDistinctRecords pending) := by
  unfold annotatedCompleteSortedDistinctSourceOutput
  rw [Function.comp_apply, Function.comp_apply,
    Function.comp_apply,
    flatAnnotatedCompleteSortedDedupPreparedInput_originalClauseState,
    boundedRecordFoldOutput_flatAnnotatedSortedDedup]
  have hempty :
      flatAnnotatedBundledClauseStream ([] : List (Clause T S)) =
        [] := rfl
  simp only [flatAnnotatedBubbleClauseState,
    flatAnnotatedBubblePassState, hempty,
    firstFieldSuffix_valid,
    flatAnnotatedOriginalSortedDedup_eq_sourceOrderedDistinctRecords]
  simpa only [List.append_nil] using
    firstFieldContents_valid
      (flatAnnotatedBundledClauseStream
        (sourceOrderedDistinctRecords pending)) []

end CNFAnnotatedSourceCompleteSortedDedupSourceCert

namespace CNFFiveFamilyIndependentFiveFamilyPhysicalBundledSourceCert

open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLCellRowBounds GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding
open GapCVP.SourceUniformTuringTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CLStructuralWholeCNFOutputTM GapCVP.CNFFiniteRecordSort
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFAnnotatedSourceClauseBubblePassTM
open GapCVP.CNFAnnotatedSourceCompleteBubbleSortTM
open GapCVP.CNFAnnotatedSourceCompleteSortedDedupSourceCert
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM GapCVP.CNFFiveFamilyFlatIndexedCatalogueTM
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM GapCVP.CNFFiveFamilyFlatRowMajorCatalogueTM
open GapCVP.CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM
open GapCVP.CNFFiveFamilyFlatAcceptanceVariableTM GapCVP.CNFFiveFamilyFlatAcceptanceClauseFoldTM
open GapCVP.CNFFiveFamilyPackedInitialCellDecoderTM
open GapCVP.CNFFiveFamilyIndependentAnchoredFamilyStreamTM
open GapCVP.CNFFiveFamilyIndependentFiveFamilyBundledCatalogueTM
open GapCVP.CNFFiveFamilyIndependentFiveFamilyCatalogueSourceValidity

private theorem fiveIndependentActualRankBundledStream_valid
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (candidate : List Bool → List Bool)
    (clauses : Fin (count.eval original.length) →
      Clause (rowWidth bound machine original)
        (completePhaseSymbolCount machine.tm))
    (hvalid : ∀ rank : Fin (count.eval original.length),
      candidate
        (lengthPrefixedWord (List.replicate rank.val true) ++
          fiveFlatOriginalSourceAnchorWord
            bound machine original) =
        flatSourceClauseAnnotatedRecord (clauses rank)) :
    fiveIndependentAnchoredFamilyBundledStreamWord
        bound count machine candidate original =
      flatAnnotatedBundledClauseStream
        ((List.finRange (count.eval original.length)).map clauses) := by
  have hfit : ∀ rank : Fin (count.eval original.length),
      (candidate
        (lengthPrefixedWord (List.replicate rank.val true) ++
          fiveFlatOriginalSourceAnchorWord
            bound machine original)).length ≤
        (fiveFlatOriginalSourceAnchorWord
          bound machine original).length := by
    intro rank
    rw [hvalid rank]
    exact fiveFamilyActualAnnotatedRecord_fits_originalAnchor
      bound machine original (clauses rank)
  rw [fiveFamilyIndependentAnchoredFamilyBundledStreamWord_valid
    bound count machine candidate original hfit]
  unfold fiveIndependentSourceRankWords
    flatAnnotatedBundledClauseStream
    flatAnnotatedBundledClauseRecord
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map, List.map_map, Function.comp_def,
    hvalid]

private theorem fiveFamilyIndependentAtLeastBundledStreamWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    fiveIndependentAtLeastBundledStreamWord
        bound machine original =
      flatAnnotatedBundledClauseStream
        (fiveIndependentPhysicalAtLeastSourceClauses
          bound machine original) := by
  have hphysical := fiveIndependentActualRankBundledStream_valid
    bound
    (fiveFamilyFlatIndexedGridPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine original
    (fiveFlatRowMajorAtLeastClauseRecordWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (completePhaseSymbolCount machine.tm + 1))
    (fun rank => atLeastOneClause
      (S := completePhaseSymbolCount machine.tm)
      (fiveFamilyIndependentSquareGridTime
        bound machine original rank)
      (fiveIndependentSquareGridPosition
        bound machine original rank))
    (fiveFamilyIndependentAtLeastRankWorker_valid
      bound machine original)
  simpa only [fiveIndependentAtLeastBundledStreamWord,
    fiveIndependentPhysicalAtLeastSourceClauses,
    fiveIndependentSquareGridSlots,
    List.map_map, Function.comp_def] using hphysical

private theorem fiveFamilyIndependentFixedFamilyBundledStream_valid
    {α : Type} {T S : ℕ}
    (indices : List α)
    (stream : α → List Bool → List Bool)
    (clauses : α → List (Clause T S))
    (original : List Bool)
    (hvalid : ∀ index ∈ indices,
      stream index original =
        flatAnnotatedBundledClauseStream (clauses index)) :
    fiveIndependentFixedFamilyStreamWord
        indices stream original =
      flatAnnotatedBundledClauseStream
        (indices.flatMap clauses) := by
  induction indices with
  | nil =>
      rfl
  | cons index remaining ih =>
      have hfirst := hvalid index (by simp only [List.mem_cons, true_or])
      have hremaining := ih (fun next hnext =>
        hvalid next (by simp only [List.mem_cons, hnext, or_true]))
      change stream index original ++
        fiveIndependentFixedFamilyStreamWord
          remaining stream original =
        flatAnnotatedBundledClauseStream
          (clauses index ++ remaining.flatMap clauses)
      rw [hfirst, hremaining]
      simp only [flatAnnotatedBundledClauseStream, List.flatMap_append]

private def fiveIndependentPhysicalAtMostFixedPairSourceClauses
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (pair : Symbol (completePhaseSymbolCount machine.tm) ×
      Symbol (completePhaseSymbolCount machine.tm)) :
    List (Clause (rowWidth bound machine original)
      (completePhaseSymbolCount machine.tm)) :=
  (fiveIndependentSquareGridSlots
    bound machine original).map fun position =>
      if pair.1 < pair.2 then
        atMostOneClause position.1 position.2 pair.1 pair.2
      else
        atLeastOneClause position.1 position.2

private theorem fiveFamilyIndependentAtMostFixedPairBundledStreamWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (pair : Symbol (completePhaseSymbolCount machine.tm) ×
      Symbol (completePhaseSymbolCount machine.tm)) :
    fiveIndependentAtMostFixedPairBundledStreamWord
        bound machine pair original =
      flatAnnotatedBundledClauseStream
        (fiveIndependentPhysicalAtMostFixedPairSourceClauses
          bound machine original pair) := by
  have hphysical := fiveIndependentActualRankBundledStream_valid
    bound
    (fiveFamilyFlatIndexedGridPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine original
    (fiveIndependentAtMostFixedPairWorker
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (completePhaseSymbolCount machine.tm + 1)
      pair.1.val pair.2.val)
    (fun rank =>
      if pair.1 < pair.2 then
        atMostOneClause
          (fiveFamilyIndependentSquareGridTime
            bound machine original rank)
          (fiveIndependentSquareGridPosition
            bound machine original rank)
          pair.1 pair.2
      else
        atLeastOneClause
          (S := completePhaseSymbolCount machine.tm)
          (fiveFamilyIndependentSquareGridTime
            bound machine original rank)
          (fiveIndependentSquareGridPosition
            bound machine original rank))
    (fiveFamilyIndependentAtMostRankWorker_valid
      bound machine original pair)
  simpa only [fiveIndependentAtMostFixedPairBundledStreamWord,
    fiveIndependentPhysicalAtMostFixedPairSourceClauses,
    fiveIndependentSquareGridSlots,
    List.map_map, Function.comp_def] using hphysical

private theorem fiveFamilyIndependentAtMostBundledStreamWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    fiveIndependentAtMostBundledStreamWord
        bound machine original =
      flatAnnotatedBundledClauseStream
        (fiveIndependentPhysicalAtMostSourceClauses
          bound machine original) := by
  have hphysical := fiveFamilyIndependentFixedFamilyBundledStream_valid
    (fiveFamilyRowMajorSymbolPairs
      (completePhaseSymbolCount machine.tm))
    (fiveIndependentAtMostFixedPairBundledStreamWord
      bound machine)
    (fiveIndependentPhysicalAtMostFixedPairSourceClauses
      bound machine original)
    original
    (fun pair _ =>
      fiveFamilyIndependentAtMostFixedPairBundledStreamWord_valid
        bound machine original pair)
  have hclauses :
      (fiveFamilyRowMajorSymbolPairs
        (completePhaseSymbolCount machine.tm)).flatMap
          (fiveIndependentPhysicalAtMostFixedPairSourceClauses
            bound machine original) =
        fiveIndependentPhysicalAtMostSourceClauses
          bound machine original := by
    rfl
  rw [hclauses] at hphysical
  exact hphysical

private theorem fiveFamilyIndependentInitialBundledStreamWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    fiveIndependentInitialBundledStreamWord
        bound machine original =
      flatAnnotatedBundledClauseStream
        (fiveIndependentPhysicalInitialSourceClauses
          bound machine original) := by
  have hphysical := fiveIndependentActualRankBundledStream_valid
    bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine original
    (fiveFlatWholePackedInitialClauseRecordWord
      bound machine)
    (fun rank => initialClause
      (paddedAcceptancePhaseSpecification
        bound machine original).input
      (fiveIndependentInitialGridPosition
        bound machine original rank))
    (fiveFamilyIndependentInitialRankWorker_valid
      bound machine original)
  simpa only [fiveIndependentInitialBundledStreamWord,
    fiveIndependentPhysicalInitialSourceClauses,
    fiveIndependentInitialGridPositions,
    List.map_map, Function.comp_def] using hphysical

private theorem fiveFamilyIndependentAcceptanceBundledStreamWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    fiveIndependentAcceptanceBundledStreamWord
        bound machine original =
      flatAnnotatedBundledClauseStream
        (fiveFamilyRowMajorAcceptanceClauses
          (paddedAcceptancePhaseSpecification
            bound machine original)) := by
  unfold fiveIndependentAcceptanceBundledStreamWord
  rw [fiveFamilyFlatWholeAcceptanceClauseRecordWord_valid
    bound machine original]
  simp only [fiveFamilyVerifierAcceptingSymbol, flatAnnotatedBundledClauseStream,
      fiveFamilyRowMajorAcceptanceClauses, paddedAcceptancePhaseSpecification, List.flatMap_cons,
      flatAnnotatedBundledClauseRecord, List.flatMap_nil, List.append_nil]

private def fiveIndependentPhysicalForbiddenFixedTupleSourceClauses
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    List (Clause (rowWidth bound machine original)
      (completePhaseSymbolCount machine.tm)) :=
  (fiveIndependentForbiddenGridWindows
    bound machine original).map fun window =>
      if paddedAcceptancePhaseSymbolAllowed machine symbols = false
      then transitionClause window symbols
      else atLeastOneClause window.1.1 window.1.2

private theorem fiveFamilyIndependentForbiddenFixedTupleBundledStreamWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    fiveIndependentForbiddenFixedTupleBundledStreamWord
        bound machine symbols original =
      flatAnnotatedBundledClauseStream
        (fiveIndependentPhysicalForbiddenFixedTupleSourceClauses
          bound machine original symbols) := by
  have hphysical := fiveIndependentActualRankBundledStream_valid
    bound
    (nondeterministicTableauDimensionPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine original
    (fiveIndependentForbiddenFixedTupleWorker
      bound machine symbols)
    (fun rank =>
      if paddedAcceptancePhaseSymbolAllowed machine symbols = false
      then transitionClause
        (fiveIndependentForbiddenGridWindow
          bound machine original rank) symbols
      else atLeastOneClause
        (S := completePhaseSymbolCount machine.tm)
        (fiveIndependentForbiddenGridWindow
          bound machine original rank).1.1
        (fiveIndependentForbiddenGridWindow
          bound machine original rank).1.2)
    (fiveFamilyIndependentForbiddenRankWorker_valid
      bound machine original symbols)
  simpa only [fiveIndependentForbiddenFixedTupleBundledStreamWord,
    fiveIndependentPhysicalForbiddenFixedTupleSourceClauses,
    fiveIndependentForbiddenGridWindows,
    List.map_map, Function.comp_def] using hphysical

private theorem fiveFamilyIndependentForbiddenBundledStreamWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    fiveIndependentForbiddenBundledStreamWord
        bound machine original =
      flatAnnotatedBundledClauseStream
        (fiveIndependentPhysicalForbiddenSourceClauses
          bound machine original) := by
  have hphysical := fiveFamilyIndependentFixedFamilyBundledStream_valid
    (fiveFamilyRowMajorWindowSymbols
      (completePhaseSymbolCount machine.tm))
    (fiveIndependentForbiddenFixedTupleBundledStreamWord
      bound machine)
    (fiveIndependentPhysicalForbiddenFixedTupleSourceClauses
      bound machine original)
    original
    (fun symbols _ =>
      fiveFamilyIndependentForbiddenFixedTupleBundledStreamWord_valid
        bound machine original symbols)
  have hclauses :
      (fiveFamilyRowMajorWindowSymbols
        (completePhaseSymbolCount machine.tm)).flatMap
          (fiveIndependentPhysicalForbiddenFixedTupleSourceClauses
            bound machine original) =
        fiveIndependentPhysicalForbiddenSourceClauses
          bound machine original := by
    rfl
  rw [hclauses] at hphysical
  exact hphysical

private theorem fiveFamilyIndependentActualBundledCatalogueWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    fiveIndependentActualBundledCatalogueWord
        bound machine original =
      flatAnnotatedBundledClauseStream
        (fiveIndependentPhysicalSourceClauses
          bound machine original) := by
  unfold fiveIndependentActualBundledCatalogueWord
    fiveIndependentPhysicalSourceClauses
  rw [fiveFamilyIndependentAtLeastBundledStreamWord_valid
      bound machine original,
    fiveFamilyIndependentAtMostBundledStreamWord_valid
      bound machine original,
    fiveFamilyIndependentInitialBundledStreamWord_valid
      bound machine original,
    fiveFamilyIndependentAcceptanceBundledStreamWord_valid
      bound machine original,
    fiveFamilyIndependentForbiddenBundledStreamWord_valid
      bound machine original]
  simp only [flatAnnotatedBundledClauseStream, List.flatMap_append]

private theorem fiveFamilyIndependentPhysicalSourceClauses_length
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    (fiveIndependentPhysicalSourceClauses
      bound machine original).length =
      (fiveIndependentActualSourceClauseCountPolynomial
        bound machine).eval original.length := by
  let grid := fiveFamilyFlatIndexedGridPolynomial bound machine
  let dimension := nondeterministicTableauDimensionPolynomial
    bound machine
  let alphabet := completePhaseSymbolCount machine.tm + 1
  have hleast :
      (fiveIndependentPhysicalAtLeastSourceClauses
        bound machine original).length =
        (grid * grid).eval original.length := by
    simp only [fiveIndependentPhysicalAtLeastSourceClauses, fiveIndependentSquareGridSlots,
        List.map_map,
        List.length_map, List.length_finRange, Polynomial.eval_mul,
            fiveFamilyFlatIndexedGridPolynomial_eval, grid]
  have hmost :
      (fiveIndependentPhysicalAtMostSourceClauses
        bound machine original).length =
        alphabet ^ 2 * (grid * grid).eval original.length := by
    simp only [fiveIndependentPhysicalAtMostSourceClauses, fiveIndependentSquareGridSlots,
        List.map_map,
        List.length_flatMap, List.length_map, List.length_finRange, Polynomial.eval_mul,
        fiveFamilyFlatIndexedGridPolynomial_eval, List.map_const',
            fiveFamilyRowMajorSymbolPairs_length, pow_two,
        List.sum_replicate, smul_eq_mul, alphabet, grid]
  have hinitial :
      (fiveIndependentPhysicalInitialSourceClauses
        bound machine original).length =
        grid.eval original.length := by
    simp only [fiveIndependentPhysicalInitialSourceClauses, fiveIndependentInitialGridPositions,
      List.map_map, List.length_map, List.length_finRange,
          fiveFamilyFlatIndexedGridPolynomial_eval,
      grid]
  have hforbidden :
      (fiveIndependentPhysicalForbiddenSourceClauses
        bound machine original).length =
        alphabet ^ 4 * (dimension * grid).eval original.length := by
    simp only [fiveIndependentPhysicalForbiddenSourceClauses, fiveIndependentForbiddenGridWindows,
        List.map_map,
        List.length_flatMap, List.length_map, List.length_finRange, Polynomial.eval_mul,
        fiveFamilyFlatIndexedGridPolynomial_eval, List.map_const',
            fiveFamilyRowMajorWindowSymbols_length,
        List.sum_replicate, smul_eq_mul, alphabet, dimension, grid]
  change
    (fiveIndependentPhysicalAtLeastSourceClauses
      bound machine original ++
      (fiveIndependentPhysicalAtMostSourceClauses
        bound machine original ++
        (fiveIndependentPhysicalInitialSourceClauses
          bound machine original ++
          ((fiveFamilyRowMajorAcceptanceClauses
            (paddedAcceptancePhaseSpecification
              bound machine original) :
              List (Clause (rowWidth bound machine original)
                (completePhaseSymbolCount machine.tm))) ++
            fiveIndependentPhysicalForbiddenSourceClauses
              bound machine original)))).length = _
  rw [List.length_append, List.length_append,
    List.length_append, List.length_append,
    hleast, hmost, hinitial]
  simp only [fiveFamilyRowMajorAcceptanceClauses,
    List.length_cons, List.length_nil, Nat.zero_add]
  rw [hforbidden]
  simp only [Polynomial.eval_mul, fiveFamilyFlatIndexedGridPolynomial_eval,
      fiveIndependentActualSourceClauseCountPolynomial, eq_natCast, Nat.cast_pow, Nat.cast_add,
          Nat.cast_one,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_natCast, Nat.cast_id,
          Polynomial.eval_one, grid, alphabet,
      dimension]
  ring

private def fiveIndependentActualBubbleSortInputWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  annotatedCompleteBubbleSortState
    (fiveIndependentActualBundledCatalogueWord
      bound machine original)
    (fiveIndependentSourceCountWord
      (fiveIndependentActualSourceClauseCountPolynomial
        bound machine) original)
    []

private noncomputable def fiveFamilyIndependentActualBubbleSortInputComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentActualBubbleSortInputWord
        bound machine) := by
  have hpending := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyIndependentActualBundledCatalogueComputable
      bound machine)
    structuralPrefixWriterComputable
  have hcount := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyIndependentSourceCountComputable
      (fiveIndependentActualSourceClauseCountPolynomial
        bound machine))
    structuralPrefixWriterComputable
  have hsuffix := pointwiseAppendComputable hcount
    (constantWordComputable (lengthPrefixedWord []))
  have physical := pointwiseAppendComputable hpending hsuffix
  have hequality :
      (fun original : List Bool =>
        lengthPrefixedWord
            (fiveIndependentActualBundledCatalogueWord
              bound machine original) ++
          (lengthPrefixedWord
              (fiveIndependentSourceCountWord
                (fiveIndependentActualSourceClauseCountPolynomial
                  bound machine) original) ++
            lengthPrefixedWord [])) =
        fiveIndependentActualBubbleSortInputWord
          bound machine := by
    funext original
    simp only [fiveIndependentActualBubbleSortInputWord, annotatedCompleteBubbleSortState,
        List.append_assoc]
  rw [← hequality]
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyIndependentActualBubbleSortInputWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    fiveIndependentActualBubbleSortInputWord
        bound machine original =
      annotatedCompleteBubbleSortState
        (flatAnnotatedBundledClauseStream
          (fiveIndependentPhysicalSourceClauses
            bound machine original))
        (List.replicate
          (fiveIndependentPhysicalSourceClauses
            bound machine original).length true)
        [] := by
  unfold fiveIndependentActualBubbleSortInputWord
  rw [fiveFamilyIndependentActualBundledCatalogueWord_valid
    bound machine original]
  unfold fiveIndependentSourceCountWord
  rw [fiveFamilyIndependentPhysicalSourceClauses_length]

/-- Internal support shared across GapCVP continuation modules. -/
def fiveIndependentActualSortedDistinctBundledSourceWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  annotatedCompleteSortedDistinctSourceOutput
    (fiveIndependentActualBubbleSortInputWord
      bound machine original)

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def fiveFamilyIndependentActualSortedDistinctBundledSourceComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentActualSortedDistinctBundledSourceWord
        bound machine) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyIndependentActualBubbleSortInputComputable
      bound machine)
    flatAnnotatedCompleteSortedDistinctSourceComputable
  change BitTM
    (fun original => annotatedCompleteSortedDistinctSourceOutput
      (fiveIndependentActualBubbleSortInputWord
        bound machine original))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyIndependentPhysicalSourceClauses_sorted
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    sourceOrderedDistinctRecords
        (fiveIndependentPhysicalSourceClauses
          bound machine original) =
      structuralWholeSourceClauses bound machine original := by
  unfold sourceOrderedDistinctRecords structuralWholeSourceClauses
  rw [fiveFamilyIndependentPhysicalSourceClauses_toFinset
    bound machine original]

/-- Internal support shared across GapCVP continuation modules. -/
theorem fiveFamilyIndependentActualSortedDistinctBundledSourceWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) :
    fiveIndependentActualSortedDistinctBundledSourceWord
        bound machine original =
      flatAnnotatedBundledClauseStream
        (structuralWholeSourceClauses
          bound machine original) := by
  unfold fiveIndependentActualSortedDistinctBundledSourceWord
  rw [fiveFamilyIndependentActualBubbleSortInputWord_valid
    bound machine original]
  rw [flatAnnotatedCompleteSortedDistinctSourceOutput_valid]
  rw [fiveFamilyIndependentPhysicalSourceClauses_sorted
    bound machine original]

end CNFFiveFamilyIndependentFiveFamilyPhysicalBundledSourceCert

namespace CNFFiveFamilySourceIndexedORGadgetRecordWorkerTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceUniformTuringTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatStructuralRecordWorkerTM
open GapCVP.CNFFlatSourceGridDescriptorTM GapCVP.CNFUnaryPairIndexTM
open GapCVP.CNFPairedSourceGridDescriptorTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFAnnotatedSourceClausePairPreparationTM

/-- GapCVP reduction support. -/
def flatAnnotatedIndexedORGadgetState
    (clauseIndex prefixWord pending active emitted count : List Bool) :
    List Bool :=
  lengthPrefixedWord clauseIndex ++
    lengthPrefixedWord prefixWord ++
      lengthPrefixedWord pending ++
        lengthPrefixedWord active ++
          lengthPrefixedWord emitted ++
            lengthPrefixedWord count

/-- Internal support shared across GapCVP continuation modules. -/
def flatIndexedGadgetNegateLeadingBitWord : List Bool → List Bool
  | [] => []
  | bit :: remaining => (!bit) :: remaining

/-- Internal support shared across GapCVP continuation modules. -/
abbrev flatIndexedGadgetNegateLeadingBitMachine : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m _ :=
    .peek () (fun _ inspected => inspected)
      (.pop () (fun state _ => state)
        (.branch (fun state => state.isSome)
          (.push () (fun state => !(state.getD false))
            (.load (fun _ => none) .halt))
          (.load (fun _ => none) .halt)))

/-- Internal support shared across GapCVP continuation modules. -/
theorem flatIndexedGadgetNegateLeadingBitMachine_step
    (input : List Bool) :
    flatIndexedGadgetNegateLeadingBitMachine.step
      (Turing.initList flatIndexedGadgetNegateLeadingBitMachine input) =
      some (Turing.haltList flatIndexedGadgetNegateLeadingBitMachine
        (flatIndexedGadgetNegateLeadingBitWord input)) := by
  cases input with
  | nil =>
      simp only [flatIndexedGadgetNegateLeadingBitMachine, FinTM2.step, TM2.step, initList,
          ↓reduceDIte,
          eq_mpr_eq_cast, cast_eq, TM2.stepAux, List.head?_nil, Option.isSome_none, List.tail_nil,
              Function.update_eq_self,
          Option.getD_none, Bool.not_false, Function.update_self, Bool.cond_false, haltList,
              flatIndexedGadgetNegateLeadingBitWord]
      rfl
  | cons bit remaining =>
      cases bit <;>
        simp [flatIndexedGadgetNegateLeadingBitMachine,
          flatIndexedGadgetNegateLeadingBitWord, Turing.initList,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux]
        <;> congr 2

end CNFFiveFamilySourceIndexedORGadgetRecordWorkerTM

end GapCVP

end
