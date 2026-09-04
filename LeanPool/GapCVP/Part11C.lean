/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part11B

/-! # GapCVP proof, part 11, continuation 03 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace BinarySourceModularDegreeStepTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder

open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM

open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.SourceFourFamilyBooleanPredicateTM

open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryDimensionTM

open GapCVP.BinarySourceConvolutionTM GapCVP.BinaryModularReductionTM

private noncomputable def binarySourceModularCurrentWidth :
    SourceQaryMaskDynamicGridWidth where
  output := binarySourceModularCurrentWidthUnary
  computer := factor400BinarySourceModularCurrentWidthUnaryComputable

private def binarySourceModularCellRankUnary : List Bool → List Bool :=
  firstFieldContents

private noncomputable def binarySourceModularCellRankUnaryComputable :
    BitTM
      binarySourceModularCellRankUnary :=
  firstFieldContentsComputable

private def binarySourceModularCellState : List Bool → List Bool :=
  factor400BinarySourceSkipFields 2

private noncomputable def factor400BinarySourceModularCellStateComputable :
    BitTM
      binarySourceModularCellState :=
  binarySourceSkipFieldsComputable 2

private def binarySourceModularCellLift
    (worker : List Bool → List Bool) : List Bool → List Bool :=
  worker ∘ binarySourceModularCellState

private noncomputable def binarySourceModularCellLiftComputable
    {worker : List Bool → List Bool}
    (computer : BitTM worker) :
    BitTM
      (binarySourceModularCellLift worker) :=
  GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceModularCellStateComputable computer

private def binarySourceModularCellShiftStart : List Bool → List Bool :=
  binarySourceModularCellLift
    binarySourceModularShiftStartUnary

private noncomputable def factor400BinarySourceModularCellShiftStartComputable :
    BitTM
      binarySourceModularCellShiftStart :=
  binarySourceModularCellLiftComputable
    factor400BinarySourceModularShiftStartUnaryComputable

private def binarySourceModularCellLowerIndex : List Bool → List Bool :=
  unarySubtractionOutput
    binarySourceModularCellRankUnary
    binarySourceModularCellShiftStart

private noncomputable def factor400BinarySourceModularCellLowerIndexComputable :
    BitTM
      binarySourceModularCellLowerIndex :=
  unarySubtractionComputable
    binarySourceModularCellRankUnaryComputable
    factor400BinarySourceModularCellShiftStartComputable

private def binarySourceModularCellLowerWord : List Bool → List Bool :=
  binarySourceModularCellLift
    binarySourceModularLowerWord

private noncomputable def factor400BinarySourceModularCellLowerWordComputable :
    BitTM
      binarySourceModularCellLowerWord :=
  binarySourceModularCellLiftComputable
    factor400BinarySourceModularLowerWordComputable

private def binarySourceModularCellLowerBit : List Bool → List Bool :=
  fiveFamilyOriginalDynamicBitWord
    binarySourceModularCellLowerIndex
    binarySourceModularCellLowerWord

private noncomputable def factor400BinarySourceModularCellLowerBitComputable :
    BitTM
      binarySourceModularCellLowerBit :=
  fiveOriginalDynamicBitComputable
    factor400BinarySourceModularCellLowerIndexComputable
    factor400BinarySourceModularCellLowerWordComputable

private def binarySourceModularCellBelowShift : List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    binarySourceModularCellRankUnary
    binarySourceModularCellShiftStart

private noncomputable def factor400BinarySourceModularCellBelowShiftComputable :
    BitTM
      binarySourceModularCellBelowShift :=
  fourFamilyComputedUnaryLessBitComputable
    binarySourceModularCellRankUnaryComputable
    factor400BinarySourceModularCellShiftStartComputable

private def binarySourceModularCellAtOrAboveShift :
    List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    binarySourceModularCellBelowShift

private noncomputable def factor400BinarySourceModularCellAtOrAboveShiftComputable :
    BitTM
      binarySourceModularCellAtOrAboveShift :=
  fourFamilyBooleanNotOutputComputable
    factor400BinarySourceModularCellBelowShiftComputable

private def binarySourceModularCellShiftedLowerBit :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    binarySourceModularCellAtOrAboveShift
    binarySourceModularCellLowerBit

private noncomputable def factor400BinarySourceModularCellShiftedLowerBitComputable :
    BitTM
      binarySourceModularCellShiftedLowerBit :=
  fourFamilyBooleanAndComputable
    factor400BinarySourceModularCellAtOrAboveShiftComputable
    factor400BinarySourceModularCellLowerBitComputable

private def binarySourceModularCellDescendingDegree :
    List Bool → List Bool :=
  binarySourceModularCellLift
    binarySourceModularDescendingDegreeUnary

private noncomputable def factor400BinarySourceModularCellDescendingDegreeComputable :
    BitTM
      binarySourceModularCellDescendingDegree :=
  binarySourceModularCellLiftComputable
    factor400BinarySourceModularDescendingDegreeUnaryComputable

private def binarySourceModularCellRankLessDegree :
    List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    binarySourceModularCellRankUnary
    binarySourceModularCellDescendingDegree

private noncomputable def factor400BinarySourceModularCellRankLessDegreeComputable :
    BitTM
      binarySourceModularCellRankLessDegree :=
  fourFamilyComputedUnaryLessBitComputable
    binarySourceModularCellRankUnaryComputable
    factor400BinarySourceModularCellDescendingDegreeComputable

private def binarySourceModularCellDegreeLessRank :
    List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    binarySourceModularCellDescendingDegree
    binarySourceModularCellRankUnary

private noncomputable def factor400BinarySourceModularCellDegreeLessRankComputable :
    BitTM
      binarySourceModularCellDegreeLessRank :=
  fourFamilyComputedUnaryLessBitComputable
    factor400BinarySourceModularCellDescendingDegreeComputable
    binarySourceModularCellRankUnaryComputable

private def binarySourceModularCellLeadingMask :
    List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    (sourceFourFamilyBooleanOrOutput
      binarySourceModularCellRankLessDegree
      binarySourceModularCellDegreeLessRank)

private noncomputable def factor400BinarySourceModularCellLeadingMaskComputable :
    BitTM
      binarySourceModularCellLeadingMask :=
  fourFamilyBooleanNotOutputComputable
    (sourceFourFamilyBooleanOrComputable
      factor400BinarySourceModularCellRankLessDegreeComputable
      factor400BinarySourceModularCellDegreeLessRankComputable)

private def binarySourceModularCellMask : List Bool → List Bool :=
  sourceFourFamilyBooleanOrOutput
    binarySourceModularCellLeadingMask
    binarySourceModularCellShiftedLowerBit

private noncomputable def factor400BinarySourceModularCellMaskComputable :
    BitTM
      binarySourceModularCellMask :=
  sourceFourFamilyBooleanOrComputable
    factor400BinarySourceModularCellLeadingMaskComputable
    factor400BinarySourceModularCellShiftedLowerBitComputable

private def binarySourceModularCellCurrentWord : List Bool → List Bool :=
  binarySourceModularCellLift
    binarySourceModularCurrentWord

private noncomputable def factor400BinarySourceModularCellCurrentWordComputable :
    BitTM
      binarySourceModularCellCurrentWord :=
  binarySourceModularCellLiftComputable
    factor400BinarySourceModularCurrentWordComputable

private def binarySourceModularCellDestination :
    List Bool → List Bool :=
  fiveFamilyOriginalDynamicBitWord
    binarySourceModularCellRankUnary
    binarySourceModularCellCurrentWord

private noncomputable def factor400BinarySourceModularCellDestinationComputable :
    BitTM
      binarySourceModularCellDestination :=
  fiveOriginalDynamicBitComputable
    binarySourceModularCellRankUnaryComputable
    factor400BinarySourceModularCellCurrentWordComputable

private def binarySourceModularCellLeadingGate :
    List Bool → List Bool :=
  binarySourceModularCellLift
    binarySourceModularLeadingGate

private noncomputable def factor400BinarySourceModularCellLeadingGateComputable :
    BitTM
      binarySourceModularCellLeadingGate :=
  binarySourceModularCellLiftComputable
    factor400BinarySourceModularLeadingGateComputable

private def binarySourceModularPackedCell
    (input : List Bool) : List Bool :=
  binarySourceModularCellLeadingGate input ++
    (binarySourceModularCellMask input ++
      binarySourceModularCellDestination input)

private noncomputable def binarySourceModularPackedCellComputable :
    BitTM
      binarySourceModularPackedCell :=
  pointwiseAppendComputable
    factor400BinarySourceModularCellLeadingGateComputable
    (pointwiseAppendComputable
      factor400BinarySourceModularCellMaskComputable
      factor400BinarySourceModularCellDestinationComputable)

private def binarySourceModularPackedCellCatalogue :
    List Bool → List Bool :=
  maskDynamicGridCandidateCatalogueOutput
    binarySourceModularCurrentWidth
    binarySourceModularPackedCellComputable

private noncomputable def factor400BinarySourceModularPackedCellCatalogueComputable :
    BitTM
      binarySourceModularPackedCellCatalogue :=
  maskDynamicGridCandidateCatalogueComputable
    binarySourceModularCurrentWidth
    binarySourceModularPackedCellComputable

private def binarySourceModularPackedRow
    (input : List Bool) : List Bool :=
  binarySourceModularCurrentWidthUnary input ++ false ::
    binarySourceModularPackedCellCatalogue input

private noncomputable def factor400BinarySourceModularPackedRowComputable :
    BitTM
      binarySourceModularPackedRow := by
  have hcatalogue := GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceModularPackedCellCatalogueComputable
    (prependBitComputable false)
  exact pointwiseAppendComputable
    factor400BinarySourceModularCurrentWidthUnaryComputable hcatalogue

private def binarySourceModularReducedCurrentWord :
    List Bool → List Bool :=
  modularReductionWordRowOutput ∘ binarySourceModularPackedRow

private noncomputable def factor400BinarySourceModularReducedCurrentWordComputable :
    BitTM
      binarySourceModularReducedCurrentWord :=
  GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceModularPackedRowComputable
    modularReductionWordRowComputable

private def binarySourceModularNextOffsetUnary
    (input : List Bool) : List Bool :=
  true :: binarySourceModularOffsetUnary input

private noncomputable def factor400BinarySourceModularNextOffsetUnaryComputable :
    BitTM
      binarySourceModularNextOffsetUnary :=
  GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceModularOffsetUnaryComputable
    (prependBitComputable true)

private noncomputable def factor400BinarySourceModularPrefixComputable
    {worker : List Bool → List Bool}
    (computer : BitTM worker) :
    BitTM
      (fun input => lengthPrefixedWord (worker input)) :=
  GapCVP.TMComposition.computableInPolyTime
    computer structuralPrefixWriterComputable

private def binarySourceModularDegreeStepOutput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (binarySourceModularNextOffsetUnary input) ++
    (lengthPrefixedWord (binarySourceModularLowerWord input) ++
      (lengthPrefixedWord
        (binarySourceModularReducedCurrentWord input) ++
        binarySourceModularOriginalSource input))

private noncomputable def factor400BinarySourceModularDegreeStepComputable :
    BitTM
      binarySourceModularDegreeStepOutput :=
  pointwiseAppendComputable
    (factor400BinarySourceModularPrefixComputable
      factor400BinarySourceModularNextOffsetUnaryComputable)
    (pointwiseAppendComputable
      (factor400BinarySourceModularPrefixComputable
        factor400BinarySourceModularLowerWordComputable)
      (pointwiseAppendComputable
        (factor400BinarySourceModularPrefixComputable
          factor400BinarySourceModularReducedCurrentWordComputable)
        factor400BinarySourceModularOriginalSourceComputable))

end BinarySourceModularDegreeStepTM

namespace BinarySourceModularDegreeStepCorrectness

open Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.SourceFormulaStructuralDecoder GapCVP.FormulaSemanticCert
open GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.SourceFourFamilyMarkerRotationTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryDimensionTM
open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceConvolutionTM
open GapCVP.BinarySourceModularDegreeStepTM

private theorem factor400BinarySourceModularReductionMarkerStream_length
    (queries : List (List Bool)) :
    (fourFamilyOriginalMarkerStream
      modularReductionCellOutput queries).length = queries.length := by
  induction queries with
  | nil =>
      simp only [fourFamilyOriginalMarkerStream, List.flatMap_nil, List.length_nil]
  | cons query remaining ih =>
      change
        (modularReductionCellOutput query ++
          fourFamilyOriginalMarkerStream
            modularReductionCellOutput remaining).length =
          (query :: remaining).length
      rw [List.length_append, modularReductionCellOutput_length,
        ih, List.length_cons]
      omega

private theorem factor400BinarySourceModularReducedCurrentWord_length
    (input : List Bool) :
    (binarySourceModularReducedCurrentWord input).length =
      (binarySourceModularCurrentWord input).length := by
  let count := (binarySourceModularCurrentWord input).length
  let queries : List (List Bool) :=
    (List.range count).map fun rank =>
      binarySourceModularPackedCell
        (lengthPrefixedWord (List.replicate rank true) ++
          sourceQaryMaskDynamicGridBaseSource
            binarySourceModularCurrentWidth input)
  have hwidth :
      binarySourceModularCurrentWidth.output input =
        List.replicate count true := by
    rfl
  have hcatalogue :=
    maskDynamicGridCandidateCatalogueOutput_valid
      binarySourceModularCurrentWidth
      binarySourceModularPackedCellComputable
      input count hwidth
  have hqueries : queries.length = count := by
    simp only [List.length_map, List.length_range, queries]
  have hrow :
      binarySourceModularPackedRow input =
        unaryBoundedFoldWord queries.length
          (sourceMixedRadixOriginalSourceQueryStream queries ++ []) := by
    unfold binarySourceModularPackedRow
      binarySourceModularPackedCellCatalogue
    rw [hcatalogue]
    change
      sourceInputLengthUnary
          (binarySourceModularCurrentWord input) ++
        false ::
          (List.range count).flatMap
            (fun rank => lengthPrefixedWord
              (binarySourceModularPackedCell
                (lengthPrefixedWord (List.replicate rank true) ++
                  sourceQaryMaskDynamicGridBaseSource
                    binarySourceModularCurrentWidth input))) = _
    simp only [sourceInputLengthUnary, unaryBoundedFoldWord, List.length_map, List.length_range,
        sourceMixedRadixOriginalSourceQueryStream, List.flatMap_map, List.append_nil, count,
            queries]
  unfold binarySourceModularReducedCurrentWord
  simp only [Function.comp_apply]
  rw [hrow]
  unfold modularReductionWordRowOutput
  rw [boundedRecordFoldOutput_sourceFourFamilyOriginalMarkerQueries
    modularReductionCellOutput queries []]
  simpa only [List.nil_append, hqueries]
      using factor400BinarySourceModularReductionMarkerStream_length queries

private def binarySourceModularStateFieldValidityAt
    (position : ℕ) : List Bool → List Bool :=
  fiveFamilyOriginalHeadBitWord ∘ payloadDecodeOutput ∘
    factor400BinarySourceSkipFields position

private noncomputable def factor400BinarySourceModularStateFieldValidityAtComputable
    (position : ℕ) :
    BitTM
      (binarySourceModularStateFieldValidityAt position) := by
  exact GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      (binarySourceSkipFieldsComputable position)
      payloadDecoderComputable)
    fiveFamilyOriginalHeadBitComputable

private def binarySourceModularStateValid
    (input : List Bool) : Bool :=
  (payloadDecodeOutput
      (factor400BinarySourceSkipFields 0 input)).headD false &&
    ((payloadDecodeOutput
      (factor400BinarySourceSkipFields 1 input)).headD false &&
      (payloadDecodeOutput
        (factor400BinarySourceSkipFields 2 input)).headD false)

private def factor400BinarySourceModularStateValidityWord :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    (binarySourceModularStateFieldValidityAt 0)
    (sourceFourFamilyBooleanAndOutput
      (binarySourceModularStateFieldValidityAt 1)
      (binarySourceModularStateFieldValidityAt 2))

@[simp] private theorem factor400BinarySourceModularStateValidityWord_eq
    (input : List Bool) :
    factor400BinarySourceModularStateValidityWord input =
      [binarySourceModularStateValid input] := by
  simp only [factor400BinarySourceModularStateValidityWord, sourceFourFamilyBooleanAndOutput,
      binarySourceModularStateFieldValidityAt, Function.comp_apply,
          fiveFamilyOriginalHeadBitWord_eq,
      List.headD_eq_head?_getD, List.cons_append, List.nil_append,
          sourceFourFamilyBooleanAndPairWord_bits,
      binarySourceModularStateValid]

private noncomputable def factor400BinarySourceModularStateValidityWordComputable :
    BitTM
      factor400BinarySourceModularStateValidityWord :=
  fourFamilyBooleanAndComputable
    (factor400BinarySourceModularStateFieldValidityAtComputable 0)
    (fourFamilyBooleanAndComputable
      (factor400BinarySourceModularStateFieldValidityAtComputable 1)
      (factor400BinarySourceModularStateFieldValidityAtComputable 2))

private noncomputable def factor400BinarySourceModularStateSelectionComputable :
    BitTM
      (fun input =>
        binarySourceModularStateValid input :: input) := by
  have hphysical := pointwiseAppendComputable
    factor400BinarySourceModularStateValidityWordComputable
    (Turing.idComputableInPolyTime bitEncoding)
  simpa only [factor400BinarySourceModularStateValidityWord_eq, id_eq, List.cons_append,
      List.nil_append] using
      hphysical

private def binarySourceModularGuardedDegreeStepOutput
    (input : List Bool) : List Bool :=
  if binarySourceModularStateValid input then
    binarySourceModularDegreeStepOutput input
  else
    []

private noncomputable def factor400BinarySourceModularGuardedDegreeStepComputable :
    BitTM
      binarySourceModularGuardedDegreeStepOutput := by
  exact sourcePreservingConditionalComputable
    factor400BinarySourceModularStateSelectionComputable
    factor400BinarySourceModularDegreeStepComputable []

private theorem factor400BinarySourceModularStateValid_reconstruct
    (input : List Bool)
    (hvalid : binarySourceModularStateValid input = true) :
    ∃ (offset lower current source : List Bool),
      input = lengthPrefixedWord offset ++
        (lengthPrefixedWord lower ++
          (lengthPrefixedWord current ++ source)) := by
  cases hfirst : readLengthPrefixedWord input with
  | none =>
      simp only [binarySourceModularStateValid, payloadDecodeOutput,
          factor400BinarySourceSkipFields, id_eq, hfirst,
          List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, Function.comp_apply,
              CompTriple.comp_eq,
          Bool.false_and, Bool.false_eq_true] at hvalid
  | some parsed =>
      obtain ⟨offset, firstSuffix⟩ := parsed
      cases hsecond : readLengthPrefixedWord firstSuffix with
      | none =>
          simp only [binarySourceModularStateValid, payloadDecodeOutput,
              factor400BinarySourceSkipFields, id_eq, hfirst,
              List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, Function.comp_apply,
                  firstFieldSuffix, hsecond,
              CompTriple.comp_eq, Bool.false_and, Bool.and_false, Bool.false_eq_true] at hvalid
      | some parsed =>
          obtain ⟨lower, secondSuffix⟩ := parsed
          cases hthird : readLengthPrefixedWord secondSuffix with
          | none =>
              simp only [binarySourceModularStateValid, payloadDecodeOutput,
                  factor400BinarySourceSkipFields, id_eq, hfirst,
                  List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, Function.comp_apply,
                      firstFieldSuffix, hsecond,
                  CompTriple.comp_eq, hthird, Bool.and_false, Bool.false_eq_true] at hvalid
          | some parsed =>
              obtain ⟨current, source⟩ := parsed
              refine ⟨offset, lower, current, source, ?_⟩
              have hshapeFirst := readLengthPrefixedWord_some_reconstruct
                input offset firstSuffix hfirst
              have hshapeSecond := readLengthPrefixedWord_some_reconstruct
                firstSuffix lower secondSuffix hsecond
              have hshapeThird := readLengthPrefixedWord_some_reconstruct
                secondSuffix current source hthird
              calc
                input = lengthPrefixedWord offset ++ firstSuffix :=
                  hshapeFirst
                _ = lengthPrefixedWord offset ++
                    (lengthPrefixedWord lower ++ secondSuffix) := by
                  rw [hshapeSecond]
                _ = lengthPrefixedWord offset ++
                    (lengthPrefixedWord lower ++
                      (lengthPrefixedWord current ++ source)) := by
                  rw [hshapeThird]

private theorem factor400BinarySourceModularGuardedDegreeStepOutput_length_le
    (input : List Bool) :
    (binarySourceModularGuardedDegreeStepOutput input).length ≤
      input.length + 2 := by
  unfold binarySourceModularGuardedDegreeStepOutput
  split_ifs with hvalid
  · obtain ⟨offset, lower, current, source, hshape⟩ :=
      factor400BinarySourceModularStateValid_reconstruct input hvalid
    subst input
    simp only [binarySourceModularDegreeStepOutput,
      List.length_append, lengthPrefixedWord_length]
    rw [factor400BinarySourceModularReducedCurrentWord_length]
    simp only [binarySourceModularNextOffsetUnary, binarySourceModularOffsetUnary,
        firstFieldContents_valid,
        List.length_cons, binarySourceModularLowerWord, factor400BinarySourceSkipFields,
            CompTriple.comp_eq,
        Function.comp_apply, firstFieldSuffix_valid, binarySourceModularCurrentWord,
            binarySourceModularOriginalSource]
    omega
  · simp only [List.length_nil, le_add_iff_nonneg_left, zero_le]

end BinarySourceModularDegreeStepCorrectness

namespace BinarySourceModularDegreeStepSemanticSourceLemmas

open GapCVP.BinaryEncoding GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryDimensionTM
open GapCVP.BinarySourceConvolutionTM GapCVP.BinarySourceModularDegreeStepTM

private def binarySourceModularPhysicalCellQuery
    (rank : ℕ) (state : List Bool) : List Bool :=
  lengthPrefixedWord (List.replicate rank true) ++
    sourceQaryMaskDynamicGridBaseSource
      binarySourceModularCurrentWidth state

@[simp] private theorem factor400BinarySourceModularCellRankUnary_query
    (rank : ℕ) (state : List Bool) :
    binarySourceModularCellRankUnary
        (binarySourceModularPhysicalCellQuery rank state) =
      List.replicate rank true := by
  simp only [binarySourceModularCellRankUnary, binarySourceModularPhysicalCellQuery,
      SourceFormulaStructuralDecoder.firstFieldContents_valid]

@[simp] private theorem factor400BinarySourceModularCellState_query
    (rank : ℕ) (state : List Bool) :
    binarySourceModularCellState
        (binarySourceModularPhysicalCellQuery rank state) =
      state := by
  simp only [binarySourceModularCellState, factor400BinarySourceSkipFields, CompTriple.comp_eq,
      binarySourceModularPhysicalCellQuery, sourceQaryMaskDynamicGridBaseSource,
          Function.comp_apply,
      SourceFormulaStructuralDecoder.firstFieldSuffix_valid]

@[simp] private theorem factor400BinarySourceModularCellLift_query
    (worker : List Bool → List Bool)
    (rank : ℕ) (state : List Bool) :
    binarySourceModularCellLift worker
        (binarySourceModularPhysicalCellQuery rank state) =
      worker state := by
  simp only [binarySourceModularCellLift, Function.comp_apply,
      factor400BinarySourceModularCellState_query]

@[simp] private theorem factor400BinarySourceModularShiftStartUnary_degreeState
    (offset : ℕ) (lower current source : List Bool) :
    binarySourceModularShiftStartUnary
        (binarySourceModularDegreeState
          offset lower current source) =
      List.replicate
        (current.length - 1 - offset - lower.length) true := by
  unfold binarySourceModularShiftStartUnary
  apply unarySubtractionOutput_valid
    binarySourceModularDescendingDegreeUnary
    binarySourceModularLowerDegreeUnary
    (binarySourceModularDegreeState
      offset lower current source)
    (current.length - 1 - offset) lower.length
  · exact factor400BinarySourceModularDescendingDegreeUnary_state
      offset lower current source
  · exact factor400BinarySourceModularLowerDegreeUnary_state
      offset lower current source

@[simp] private theorem factor400BinarySourceModularCellLowerIndex_query
    (rank offset : ℕ) (lower current source : List Bool) :
    binarySourceModularCellLowerIndex
        (binarySourceModularPhysicalCellQuery rank
          (binarySourceModularDegreeState
            offset lower current source)) =
      List.replicate
        (rank - (current.length - 1 - offset - lower.length)) true := by
  unfold binarySourceModularCellLowerIndex
  apply unarySubtractionOutput_valid
    binarySourceModularCellRankUnary
    binarySourceModularCellShiftStart
    (binarySourceModularPhysicalCellQuery rank
      (binarySourceModularDegreeState
        offset lower current source))
    rank (current.length - 1 - offset - lower.length)
  · exact factor400BinarySourceModularCellRankUnary_query rank _
  · simp only [binarySourceModularCellShiftStart, factor400BinarySourceModularCellLift_query,
        factor400BinarySourceModularShiftStartUnary_degreeState]

private theorem factor400BinarySourceModularLeadingGate_degreeState
    (offset : ℕ) (lower current source : List Bool) :
    binarySourceModularLeadingGate
        (binarySourceModularDegreeState
          offset lower current source) =
      [(current.drop (current.length - 1 - offset)).headD false] := by
  unfold binarySourceModularLeadingGate
  rw [fiveOriginalDynamicBitWord_valid
    binarySourceModularDescendingDegreeUnary
    binarySourceModularCurrentWord
    (binarySourceModularDegreeState
      offset lower current source)
    (current.length - 1 - offset)
    (factor400BinarySourceModularDescendingDegreeUnary_state
      offset lower current source)]
  simp only [factor400BinarySourceModularCurrentWord_state, List.headD_eq_head?_getD,
      List.head?_drop]

private theorem factor400BinarySourceModularCellDestination_query
    (rank offset : ℕ) (lower current source : List Bool) :
    binarySourceModularCellDestination
        (binarySourceModularPhysicalCellQuery rank
          (binarySourceModularDegreeState
            offset lower current source)) =
      [(current.drop rank).headD false] := by
  unfold binarySourceModularCellDestination
  rw [fiveOriginalDynamicBitWord_valid
    binarySourceModularCellRankUnary
    binarySourceModularCellCurrentWord
    (binarySourceModularPhysicalCellQuery rank
      (binarySourceModularDegreeState
        offset lower current source)) rank
    (factor400BinarySourceModularCellRankUnary_query rank _)]
  simp only [binarySourceModularCellCurrentWord, factor400BinarySourceModularCellLift_query,
      factor400BinarySourceModularCurrentWord_state, List.headD_eq_head?_getD, List.head?_drop]

private theorem factor400BinarySourceModularCellLowerBit_query
    (rank offset : ℕ) (lower current source : List Bool) :
    binarySourceModularCellLowerBit
        (binarySourceModularPhysicalCellQuery rank
          (binarySourceModularDegreeState
            offset lower current source)) =
      [(lower.drop
        (rank - (current.length - 1 - offset - lower.length))).headD false] := by
  unfold binarySourceModularCellLowerBit
  rw [fiveOriginalDynamicBitWord_valid
    binarySourceModularCellLowerIndex
    binarySourceModularCellLowerWord
    (binarySourceModularPhysicalCellQuery rank
      (binarySourceModularDegreeState
        offset lower current source))
    (rank - (current.length - 1 - offset - lower.length))
    (factor400BinarySourceModularCellLowerIndex_query
      rank offset lower current source)]
  simp only [binarySourceModularCellLowerWord, factor400BinarySourceModularCellLift_query,
      factor400BinarySourceModularLowerWord_state, List.headD_eq_head?_getD, List.head?_drop]

private theorem factor400BinarySourceModularCellBelowShift_query
    (rank offset : ℕ) (lower current source : List Bool) :
    binarySourceModularCellBelowShift
        (binarySourceModularPhysicalCellQuery rank
          (binarySourceModularDegreeState
            offset lower current source)) =
      [decide (rank < current.length - 1 - offset - lower.length)] := by
  unfold binarySourceModularCellBelowShift
  apply fourFamilyComputedUnaryLessBitOutput_valid
    binarySourceModularCellRankUnary
    binarySourceModularCellShiftStart
    (binarySourceModularPhysicalCellQuery rank
      (binarySourceModularDegreeState
        offset lower current source))
    rank (current.length - 1 - offset - lower.length)
  · exact factor400BinarySourceModularCellRankUnary_query rank _
  · simp only [binarySourceModularCellShiftStart, factor400BinarySourceModularCellLift_query,
        factor400BinarySourceModularShiftStartUnary_degreeState]

private theorem factor400BinarySourceModularCellAtOrAboveShift_query
    (rank offset : ℕ) (lower current source : List Bool) :
    binarySourceModularCellAtOrAboveShift
        (binarySourceModularPhysicalCellQuery rank
          (binarySourceModularDegreeState
            offset lower current source)) =
      [decide (current.length - 1 - offset - lower.length ≤ rank)] := by
  unfold binarySourceModularCellAtOrAboveShift
  rw [fourFamilyBooleanNotOutput_bit
    binarySourceModularCellBelowShift
    (binarySourceModularPhysicalCellQuery rank
      (binarySourceModularDegreeState
        offset lower current source))
    (decide (rank < current.length - 1 - offset - lower.length))
    (factor400BinarySourceModularCellBelowShift_query
      rank offset lower current source)]
  apply congrArg (fun bit : Bool => [bit])
  by_cases hlt : rank < current.length - 1 - offset - lower.length
  · have hnot :
        ¬ current.length - 1 - offset - lower.length ≤ rank := by
      omega
    simp only [hlt, decide_true, Bool.not_true, hnot, decide_false]
  · have hle :
        current.length - 1 - offset - lower.length ≤ rank := by
      omega
    simp only [hlt, decide_false, Bool.not_false, hle, decide_true]

private theorem factor400BinarySourceModularCellShiftedLowerBit_query
    (rank offset : ℕ) (lower current source : List Bool) :
    binarySourceModularCellShiftedLowerBit
        (binarySourceModularPhysicalCellQuery rank
          (binarySourceModularDegreeState
            offset lower current source)) =
      [decide (current.length - 1 - offset - lower.length ≤ rank) &&
        (lower.drop
          (rank - (current.length - 1 - offset - lower.length))).headD false] := by
  unfold binarySourceModularCellShiftedLowerBit
  apply fourFamilyBooleanAndOutput_bits
    binarySourceModularCellAtOrAboveShift
    binarySourceModularCellLowerBit
    (binarySourceModularPhysicalCellQuery rank
      (binarySourceModularDegreeState
        offset lower current source))
    (decide (current.length - 1 - offset - lower.length ≤ rank))
    ((lower.drop
      (rank - (current.length - 1 - offset - lower.length))).headD false)
  · exact factor400BinarySourceModularCellAtOrAboveShift_query
      rank offset lower current source
  · exact factor400BinarySourceModularCellLowerBit_query
      rank offset lower current source

private theorem factor400BinarySourceModularCellRankLessDegree_query
    (rank offset : ℕ) (lower current source : List Bool) :
    binarySourceModularCellRankLessDegree
        (binarySourceModularPhysicalCellQuery rank
          (binarySourceModularDegreeState
            offset lower current source)) =
      [decide (rank < current.length - 1 - offset)] := by
  unfold binarySourceModularCellRankLessDegree
  apply fourFamilyComputedUnaryLessBitOutput_valid
    binarySourceModularCellRankUnary
    binarySourceModularCellDescendingDegree
    (binarySourceModularPhysicalCellQuery rank
      (binarySourceModularDegreeState
        offset lower current source))
    rank (current.length - 1 - offset)
  · exact factor400BinarySourceModularCellRankUnary_query rank _
  · simp only [binarySourceModularCellDescendingDegree, factor400BinarySourceModularCellLift_query,
        factor400BinarySourceModularDescendingDegreeUnary_state]

private theorem factor400BinarySourceModularCellDegreeLessRank_query
    (rank offset : ℕ) (lower current source : List Bool) :
    binarySourceModularCellDegreeLessRank
        (binarySourceModularPhysicalCellQuery rank
          (binarySourceModularDegreeState
            offset lower current source)) =
      [decide (current.length - 1 - offset < rank)] := by
  unfold binarySourceModularCellDegreeLessRank
  apply fourFamilyComputedUnaryLessBitOutput_valid
    binarySourceModularCellDescendingDegree
    binarySourceModularCellRankUnary
    (binarySourceModularPhysicalCellQuery rank
      (binarySourceModularDegreeState
        offset lower current source))
    (current.length - 1 - offset) rank
  · simp only [binarySourceModularCellDescendingDegree, factor400BinarySourceModularCellLift_query,
        factor400BinarySourceModularDescendingDegreeUnary_state]
  · exact factor400BinarySourceModularCellRankUnary_query rank _

private theorem factor400BinarySourceModularCellLeadingMask_query
    (rank offset : ℕ) (lower current source : List Bool) :
    binarySourceModularCellLeadingMask
        (binarySourceModularPhysicalCellQuery rank
          (binarySourceModularDegreeState
            offset lower current source)) =
      [decide (rank = current.length - 1 - offset)] := by
  unfold binarySourceModularCellLeadingMask
  have hor := fourFamilyBooleanOrOutput_bits
    binarySourceModularCellRankLessDegree
    binarySourceModularCellDegreeLessRank
    (binarySourceModularPhysicalCellQuery rank
      (binarySourceModularDegreeState
        offset lower current source))
    (decide (rank < current.length - 1 - offset))
    (decide (current.length - 1 - offset < rank))
    (factor400BinarySourceModularCellRankLessDegree_query
      rank offset lower current source)
    (factor400BinarySourceModularCellDegreeLessRank_query
      rank offset lower current source)
  rw [fourFamilyBooleanNotOutput_bit
    (sourceFourFamilyBooleanOrOutput
      binarySourceModularCellRankLessDegree
      binarySourceModularCellDegreeLessRank)
    (binarySourceModularPhysicalCellQuery rank
      (binarySourceModularDegreeState
        offset lower current source))
    (decide (rank < current.length - 1 - offset) ||
      decide (current.length - 1 - offset < rank)) hor]
  apply congrArg (fun bit : Bool => [bit])
  by_cases heq : rank = current.length - 1 - offset
  · subst rank
    simp only [lt_self_iff_false, decide_false, Bool.or_self, Bool.not_false, decide_true]
  · by_cases hlt : rank < current.length - 1 - offset
    · have hnot : ¬ current.length - 1 - offset < rank := by
        omega
      simp only [hlt, decide_true, hnot, decide_false, Bool.or_false, Bool.not_true, heq]
    · have hgt : current.length - 1 - offset < rank := by
        omega
      simp only [hlt, decide_false, hgt, decide_true, Bool.or_true, Bool.not_true, heq]

private theorem factor400BinarySourceModularCellMask_query
    (rank offset : ℕ) (lower current source : List Bool) :
    binarySourceModularCellMask
        (binarySourceModularPhysicalCellQuery rank
          (binarySourceModularDegreeState
            offset lower current source)) =
      [decide (rank = current.length - 1 - offset) ||
        (decide (current.length - 1 - offset - lower.length ≤ rank) &&
          (lower.drop
            (rank - (current.length - 1 - offset - lower.length))).headD false)] := by
  unfold binarySourceModularCellMask
  apply fourFamilyBooleanOrOutput_bits
    binarySourceModularCellLeadingMask
    binarySourceModularCellShiftedLowerBit
    (binarySourceModularPhysicalCellQuery rank
      (binarySourceModularDegreeState
        offset lower current source))
    (decide (rank = current.length - 1 - offset))
    (decide (current.length - 1 - offset - lower.length ≤ rank) &&
      (lower.drop
        (rank - (current.length - 1 - offset - lower.length))).headD false)
  · exact factor400BinarySourceModularCellLeadingMask_query
      rank offset lower current source
  · exact factor400BinarySourceModularCellShiftedLowerBit_query
      rank offset lower current source

private theorem factor400BinarySourceModularCellLeadingGate_query
    (rank offset : ℕ) (lower current source : List Bool) :
    binarySourceModularCellLeadingGate
        (binarySourceModularPhysicalCellQuery rank
          (binarySourceModularDegreeState
            offset lower current source)) =
      [(current.drop (current.length - 1 - offset)).headD false] := by
  unfold binarySourceModularCellLeadingGate
  rw [factor400BinarySourceModularCellLift_query]
  exact factor400BinarySourceModularLeadingGate_degreeState
    offset lower current source

private theorem factor400BinarySourceModularPackedCell_query
    (rank offset : ℕ) (lower current source : List Bool) :
    binarySourceModularPackedCell
        (binarySourceModularPhysicalCellQuery rank
          (binarySourceModularDegreeState
            offset lower current source)) =
      [(current.drop (current.length - 1 - offset)).headD false,
        decide (rank = current.length - 1 - offset) ||
          (decide (current.length - 1 - offset - lower.length ≤ rank) &&
            (lower.drop
              (rank -
                (current.length - 1 - offset - lower.length))).headD false),
        (current.drop rank).headD false] := by
  unfold binarySourceModularPackedCell
  rw [factor400BinarySourceModularCellLeadingGate_query,
    factor400BinarySourceModularCellMask_query,
    factor400BinarySourceModularCellDestination_query]
  rfl

end BinarySourceModularDegreeStepSemanticSourceLemmas

namespace BinarySourceModularDegreeStepSemanticCoefficientLemmas

open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinarySourceModularDegreeStepTM
open GapCVP.BinarySourceModularDegreeStepSemanticSourceLemmas GapCVP.Core.EffectiveBinaryField

theorem binarySourceModularFiniteWordBits_drop_head
    {degree : ℕ}
    (word : Word degree)
    (rank : ℕ) (hrank : rank < degree) :
    ((finiteWordBits word).drop rank).headD false =
      word ⟨rank, hrank⟩ := by
  exact GapCVP.BinarySourceConvolutionCorrectness.factor400BinaryFiniteWordBits_drop_head
    word rank hrank

private theorem factor400BinarySourceModularShiftXor_coefficient
    {degree : ℕ}
    (lower : Word degree) (position : ℕ)
    (word : Word (2 * degree))
    (hposition : degree ≤ position ∧ position < 2 * degree)
    (rank : Fin (2 * degree)) :
    shiftXor lower position word rank =
      Bool.xor
        (decide (position - degree ≤ rank.val) &&
          ((finiteWordBits lower).drop
            (rank.val - (position - degree))).headD false)
        (word rank) := by
  have hcoefficient :=
    congrArg
      (fun polynomial : Polynomial (ZMod 2) =>
        polynomial.coeff rank.val)
      (wordPolynomial_shiftXor lower position word hposition)
  simp only [Polynomial.coeff_add,
    GapCVP.Core.EffectiveBinaryField.wordPolynomial_coeff_fin,
    Polynomial.coeff_X_pow_mul'] at hcoefficient
  by_cases hshift : position - degree ≤ rank.val
  · by_cases hlower : rank.val - (position - degree) < degree
    · have hlowcoefficient :
          (GapCVP.Core.EffectiveBinaryField.wordPolynomial lower).coeff
              (rank.val - (position - degree)) =
            GapCVP.Core.EffectiveBinaryField.bitValue
              (lower ⟨rank.val - (position - degree), hlower⟩) :=
        GapCVP.Core.EffectiveBinaryField.wordPolynomial_coeff_fin
          lower ⟨rank.val - (position - degree), hlower⟩
      rw [ite_eq_left hshift, hlowcoefficient] at hcoefficient
      rw [binarySourceModularFiniteWordBits_drop_head
        lower _ hlower]
      apply GapCVP.Core.EffectiveBinaryField.bitValue_injective
      simpa only [hshift, decide_true, Bool.true_and, bitValue_xor, add_comm] using hcoefficient
    · have hlarge : degree ≤ rank.val - (position - degree) :=
        Nat.le_of_not_gt hlower
      rw [ite_eq_left hshift,
        GapCVP.Core.EffectiveBinaryField.wordPolynomial_coeff_eq_zero
          lower _ hlarge] at hcoefficient
      have hdrop :
          (finiteWordBits lower).drop
            (rank.val - (position - degree)) = [] := by
        apply List.drop_eq_nil_of_le
        simpa only [finiteWordBits, List.length_map, List.length_finRange] using hlarge
      rw [hdrop]
      apply GapCVP.Core.EffectiveBinaryField.bitValue_injective
      simpa only [hshift, decide_true, List.headD_eq_head?_getD, List.head?_nil, Option.getD_none,
          Bool.and_false,
          Bool.false_bne, add_zero] using hcoefficient
  · rw [ite_eq_right hshift] at hcoefficient
    apply GapCVP.Core.EffectiveBinaryField.bitValue_injective
    simpa only [hshift, decide_false, List.headD_eq_head?_getD, List.head?_drop, Bool.false_and,
        Bool.false_bne,
        add_zero] using hcoefficient

private theorem factor400BinarySourceModularPhysicalCellOutput_query
    {degree : ℕ}
    (lower : Word degree)
    (current : Word (2 * degree))
    (source : List Bool) (offset : ℕ)
    (hoffset : offset < degree)
    (rank : ℕ) (hrank : rank < 2 * degree) :
    modularReductionCellOutput
        (binarySourceModularPackedCell
          (binarySourceModularPhysicalCellQuery rank
            (binarySourceModularDegreeState offset
              (finiteWordBits lower) (finiteWordBits current) source))) =
      [reduceAt lower (2 * degree - 1 - offset)
        current (⟨rank, hrank⟩ : Fin (2 * degree))] := by
  have hposition :
      degree ≤ 2 * degree - 1 - offset ∧
        2 * degree - 1 - offset < 2 * degree := by
    omega
  have hcurrent : (finiteWordBits current).length = 2 * degree := by
    simp only [finiteWordBits, List.length_map, List.length_finRange]
  have hlower : (finiteWordBits lower).length = degree := by
    simp only [finiteWordBits, List.length_map, List.length_finRange]
  rw [factor400BinarySourceModularPackedCell_query,
    modularReductionCellOutput_valid]
  simp only [hcurrent, hlower]
  rw [binarySourceModularFiniteWordBits_drop_head
    current (2 * degree - 1 - offset) hposition.2,
    binarySourceModularFiniteWordBits_drop_head
      current rank hrank]
  apply congrArg (fun bit : Bool => [bit])
  unfold reduceAt
  rw [dite_eq_left hposition]
  let leading : Fin (2 * degree) :=
    ⟨2 * degree - 1 - offset, hposition.2⟩
  change
    Bool.xor
      (current leading &&
        (decide (rank = leading.val) ||
          (decide (leading.val - degree ≤ rank) &&
            ((finiteWordBits lower).drop
              (rank - (leading.val - degree))).headD false)))
      (current (⟨rank, hrank⟩ : Fin (2 * degree))) =
      (if current leading then
        shiftXor lower leading.val
          (xorAt current leading true)
      else
        current) (⟨rank, hrank⟩ : Fin (2 * degree))
  cases hleading : current leading with
  | false =>
      simp only [tsub_le_iff_right, List.headD_eq_head?_getD, List.head?_drop, Bool.false_and,
          Bool.false_bne,
          Bool.false_eq_true, ↓reduceIte]
  | true =>
      simp only [Bool.true_and, ↓reduceIte]
      rw [factor400BinarySourceModularShiftXor_coefficient
        lower leading.val (xorAt current leading true)
        (by simpa only [leading] using hposition)
        (⟨rank, hrank⟩ : Fin (2 * degree))]
      by_cases hrankLeading : rank = leading.val
      · have hindex :
            (⟨rank, hrank⟩ : Fin (2 * degree)) = leading := by
          apply Fin.ext
          exact hrankLeading
        have hshift : leading.val - degree ≤ leading.val := by
          omega
        have hdifference :
            leading.val - (leading.val - degree) = degree := by
          have hbound : degree ≤ leading.val := by
            simpa only [leading] using hposition.1
          omega
        have hdrop :
            (finiteWordBits lower).drop
              (leading.val - (leading.val - degree)) = [] := by
          rw [hdifference]
          apply List.drop_eq_nil_of_le
          simp only [finiteWordBits, List.length_map, List.length_finRange, Std.le_refl]
        simp only [hrankLeading, decide_true, hshift, hdrop, List.headD_eq_head?_getD,
            List.head?_nil,
            Option.getD_none, Bool.and_false, Bool.or_false, Fin.eta, hleading, bne_self_eq_false,
                xorAt, ↓reduceIte]
      · have hindex :
            (⟨rank, hrank⟩ : Fin (2 * degree)) ≠ leading := by
          intro heq
          exact hrankLeading
            (congrArg (fun bit : Fin (2 * degree) => bit.val) heq)
        simp only [hrankLeading, decide_false, tsub_le_iff_right, List.headD_eq_head?_getD,
            List.head?_drop,
            Bool.false_or, xorAt, hindex, ↓reduceIte]

end BinarySourceModularDegreeStepSemanticCoefficientLemmas

namespace BinarySourceModularDegreeStepPhysicalCellCorrectness

open GapCVP.BinaryEncoding GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceFourFamilyMarkerRotationTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM GapCVP.BinaryDimensionTM
open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceModularDegreeStepTM
open GapCVP.BinarySourceModularDegreeStepSemanticSourceLemmas
open GapCVP.BinarySourceModularDegreeStepSemanticCoefficientLemmas

theorem binarySourceModularFiniteWordBits_drop_head
    {degree : ℕ}
    (word : GapCVP.Core.EffectiveBinaryField.Word degree)
    (rank : ℕ) (hrank : rank < degree) :
    ((finiteWordBits word).drop rank).headD false =
      word ⟨rank, hrank⟩ := by
  exact GapCVP.BinarySourceConvolutionCorrectness.factor400BinaryFiniteWordBits_drop_head
    word rank hrank

private theorem factor400BinarySourceModularReducedCurrentWord_markerStream
    (input : List Bool) :
    binarySourceModularReducedCurrentWord input =
      fourFamilyOriginalMarkerStream modularReductionCellOutput
        ((List.range
          (binarySourceModularCurrentWord input).length).map
          fun rank =>
            binarySourceModularPackedCell
              (binarySourceModularPhysicalCellQuery rank input)) := by
  let count := (binarySourceModularCurrentWord input).length
  let queries : List (List Bool) :=
    (List.range count).map fun rank =>
      binarySourceModularPackedCell
        (binarySourceModularPhysicalCellQuery rank input)
  have hwidth :
      binarySourceModularCurrentWidth.output input =
        List.replicate count true := by
    rfl
  have hcatalogue :=
    maskDynamicGridCandidateCatalogueOutput_valid
      binarySourceModularCurrentWidth
      binarySourceModularPackedCellComputable
      input count hwidth
  have hrow :
      binarySourceModularPackedRow input =
        unaryBoundedFoldWord queries.length
          (sourceMixedRadixOriginalSourceQueryStream queries ++ []) := by
    unfold binarySourceModularPackedRow
      binarySourceModularPackedCellCatalogue
    rw [hcatalogue]
    change
      sourceInputLengthUnary
          (binarySourceModularCurrentWord input) ++
        false ::
          (List.range count).flatMap
            (fun rank => lengthPrefixedWord
              (binarySourceModularPackedCell
                (lengthPrefixedWord (List.replicate rank true) ++
                  sourceQaryMaskDynamicGridBaseSource
                    binarySourceModularCurrentWidth input))) = _
    simp only [sourceInputLengthUnary, unaryBoundedFoldWord, binarySourceModularPhysicalCellQuery,
        List.length_map, List.length_range, sourceMixedRadixOriginalSourceQueryStream,
            List.flatMap_map, List.append_nil,
        count, queries]
  unfold binarySourceModularReducedCurrentWord
  simp only [Function.comp_apply]
  rw [hrow]
  unfold modularReductionWordRowOutput
  rw [boundedRecordFoldOutput_sourceFourFamilyOriginalMarkerQueries
    modularReductionCellOutput queries []]
  simp only [List.nil_append, queries, count]

private theorem factor400BinarySourceModular_reconstruct_drop_head_range
    (bits : List Bool) :
    (List.range bits.length).map
      (fun rank => (bits.drop rank).headD false) = bits := by
  apply List.ext_getElem
  · simp only [List.headD_eq_head?_getD, List.head?_drop, List.length_map, List.length_range]
  · intro rank hleft hright
    simp only [List.headD_eq_head?_getD, List.head?_drop, List.getElem_map, List.getElem_range]
    rw [List.getElem?_eq_getElem hright]
    rfl

private theorem factor400BinarySourceModularReducedCurrentWord_state_valid
    {degree : ℕ}
    (lower : GapCVP.Core.EffectiveBinaryField.Word degree)
    (current : GapCVP.Core.EffectiveBinaryField.Word (2 * degree))
    (source : List Bool)
    (offset : ℕ)
    (hoffset : offset < degree) :
    binarySourceModularReducedCurrentWord
        (binarySourceModularDegreeState offset
          (finiteWordBits lower) (finiteWordBits current) source) =
      finiteWordBits
        (GapCVP.Core.EffectiveBinaryField.reduceAt
          lower (2 * degree - 1 - offset) current) := by
  have hcurrent : (finiteWordBits current).length = 2 * degree := by
    simp only [finiteWordBits, List.length_map, List.length_finRange]
  have hreduced :
      (finiteWordBits
        (GapCVP.Core.EffectiveBinaryField.reduceAt
          lower (2 * degree - 1 - offset) current)).length =
        2 * degree := by
    simp only [finiteWordBits, List.length_map, List.length_finRange]
  rw [factor400BinarySourceModularReducedCurrentWord_markerStream,
    factor400BinarySourceModularCurrentWord_state]
  unfold fourFamilyOriginalMarkerStream
  rw [List.flatMap_map, hcurrent,
    ← factor400BinarySourceModular_reconstruct_drop_head_range
      (finiteWordBits
        (GapCVP.Core.EffectiveBinaryField.reduceAt
          lower (2 * degree - 1 - offset) current)),
    hreduced, List.map_eq_flatMap]
  apply List.flatMap_congr
  intro rank hrank
  have hposition : rank < 2 * degree := List.mem_range.mp hrank
  rw [factor400BinarySourceModularPhysicalCellOutput_query
    lower current source offset hoffset rank hposition,
    binarySourceModularFiniteWordBits_drop_head
      (GapCVP.Core.EffectiveBinaryField.reduceAt
        lower (2 * degree - 1 - offset) current) rank hposition]

end BinarySourceModularDegreeStepPhysicalCellCorrectness

namespace BinarySourceModularDegreeStepSemanticCorrectness

open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceConvolutionTM
open GapCVP.BinarySourceModularDegreeStepTM GapCVP.BinarySourceModularDegreeStepCorrectness
open GapCVP.BinarySourceModularDegreeStepPhysicalCellCorrectness

@[simp] private theorem factor400BinarySourceModularStateValid_degreeState
    (offset : ℕ) (lower current source : List Bool) :
    binarySourceModularStateValid
      (binarySourceModularDegreeState
        offset lower current source) = true := by
  simp only [binarySourceModularStateValid, factor400BinarySourceSkipFields,
      binarySourceModularDegreeState,
      List.append_assoc, id_eq, SourceTotalStructuralDecoder.payloadDecodeOutput_valid,
          List.headD_eq_head?_getD,
      List.head?_cons, Option.getD_some, Function.comp_apply,
          SourceFormulaStructuralDecoder.firstFieldSuffix_valid,
      CompTriple.comp_eq, Bool.and_self]

private theorem factor400BinarySourceModularGuardedDegreeStepOutput_valid
    {degree : ℕ}
    (lower : GapCVP.Core.EffectiveBinaryField.Word degree)
    (current : GapCVP.Core.EffectiveBinaryField.Word (2 * degree))
    (source : List Bool) (offset : ℕ)
    (hoffset : offset < degree) :
    binarySourceModularGuardedDegreeStepOutput
        (binarySourceModularDegreeState offset
          (finiteWordBits lower) (finiteWordBits current) source) =
      binarySourceModularDegreeState (offset + 1)
        (finiteWordBits lower)
        (finiteWordBits
          (GapCVP.Core.EffectiveBinaryField.reduceAt lower
            (2 * degree - 1 - offset) current)) source := by
  unfold binarySourceModularGuardedDegreeStepOutput
  rw [factor400BinarySourceModularStateValid_degreeState]
  simp only [ite_true,
    binarySourceModularDegreeStepOutput,
    binarySourceModularNextOffsetUnary,
    factor400BinarySourceModularOffsetUnary_state,
    factor400BinarySourceModularLowerWord_state,
    factor400BinarySourceModularOriginalSource_state]
  rw [factor400BinarySourceModularReducedCurrentWord_state_valid
    lower current source offset hoffset]
  simp only [binarySourceModularDegreeState, List.replicate_succ, List.append_assoc]

end BinarySourceModularDegreeStepSemanticCorrectness

namespace BinarySourceModularReductionFoldTM

open Turing GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceTotalStructuralDecoder GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryModularReductionTM
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinarySourceFieldMultiplicationTM
open GapCVP.BinarySourceModularDegreeStepTM GapCVP.BinarySourceModularDegreeStepCorrectness
open GapCVP.BinarySourceModularDegreeStepSemanticCorrectness

private theorem factor400BinarySourceModularDegree_iterate_length_le
    (state : List Bool) (stage : ℕ) :
    (((binarySourceModularGuardedDegreeStepOutput)^[stage]) state).length ≤
      state.length + 2 * stage := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, mul_zero, add_zero, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      have hstep := factor400BinarySourceModularGuardedDegreeStepOutput_length_le
        (((binarySourceModularGuardedDegreeStepOutput)^[stage]) state)
      omega

private def factor400BinarySourceModularReductionStatePolynomial : Polynomial ℕ :=
  3 * Polynomial.X

private theorem factor400BinarySourceModularReduction_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates
      binarySourceModularGuardedDegreeStepOutput
      factor400BinarySourceModularReductionStatePolynomial := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage hstage
  have hreconstruct := parseUnaryBoundedFold_eq_word
    input count seed hparse
  have hseed : seed.length ≤ input.length := by
    rw [hreconstruct]
    simp only [unaryBoundedFoldWord, List.length_append,
      List.length_replicate, List.length_cons]
    omega
  have hcount := parsedUnaryFold_count_le_length
    input count seed hparse
  have hiterate := factor400BinarySourceModularDegree_iterate_length_le
    seed stage
  simp only [factor400BinarySourceModularReductionStatePolynomial,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

private def factor400BinarySourceModularReductionFoldOutput :
    List Bool → List Bool :=
  boundedRecordFoldOutput binarySourceModularGuardedDegreeStepOutput

private noncomputable def factor400BinarySourceModularReductionFoldComputable :
    BitTM
      factor400BinarySourceModularReductionFoldOutput :=
  boundedDependentRecordFoldComputable
    factor400BinarySourceModularGuardedDegreeStepComputable
    factor400BinarySourceModularReductionStatePolynomial
    factor400BinarySourceModularReduction_polynomiallyBoundedFoldStates

private def factor400BinarySourceModularReductionCurrentOutput :
    List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix ∘ firstFieldSuffix

private noncomputable def factor400BinarySourceModularReductionCurrentComputable :
    BitTM
      factor400BinarySourceModularReductionCurrentOutput :=
  GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      firstFieldSuffixComputable firstFieldSuffixComputable)
    firstFieldContentsComputable

private def binarySourceModularReductionWord :
    List Bool → List Bool :=
  factor400BinarySourceModularReductionCurrentOutput ∘
    factor400BinarySourceModularReductionFoldOutput ∘
    binarySourceModularReductionFoldPreparation

private noncomputable def factor400BinarySourceModularReductionComputable :
    BitTM
      binarySourceModularReductionWord :=
  GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      factor400BinarySourceModularReductionFoldPreparationComputable
      factor400BinarySourceModularReductionFoldComputable)
    factor400BinarySourceModularReductionCurrentComputable

@[simp] private theorem factor400BinarySourceModularReductionInitialState_degreeState
    (lower current source : List Bool) :
    binarySourceModularReductionInitialState
        lower current source =
      binarySourceModularDegreeState 0 lower current source := by
  simp only [binarySourceModularReductionInitialState,
    binarySourceModularDegreeState,
    List.replicate_zero, List.append_assoc]

private theorem factor400BinarySourceModularReduction_iterate_valid
    {degree : ℕ}
    (lower : GapCVP.Core.EffectiveBinaryField.Word degree)
    (product : GapCVP.Core.EffectiveBinaryField.Word (2 * degree))
    (source : List Bool) (stage : ℕ) (hstage : stage ≤ degree) :
    ((binarySourceModularGuardedDegreeStepOutput^[stage])
      (binarySourceModularReductionInitialState
        (finiteWordBits lower) (finiteWordBits product) source)) =
      binarySourceModularDegreeState stage
        (finiteWordBits lower)
        (finiteWordBits (reducePrefix lower stage product)) source := by
  induction stage with
  | zero =>
      simpa only [Function.iterate_zero, id_eq,
        reducePrefix, List.range_zero, List.foldl_nil] using
        factor400BinarySourceModularReductionInitialState_degreeState
          (finiteWordBits lower) (finiteWordBits product) source
  | succ stage ih =>
      have hprevious : stage ≤ degree := by omega
      have hactive : stage < degree := by omega
      rw [Function.iterate_succ_apply', ih hprevious]
      rw [factor400BinarySourceModularGuardedDegreeStepOutput_valid
        lower (reducePrefix lower stage product) source stage hactive]
      rw [← reducePrefix_succ]

@[simp] private theorem factor400BinarySourceModularReductionWord_valid
    {degree : ℕ}
    (lower : GapCVP.Core.EffectiveBinaryField.Word degree)
    (product : GapCVP.Core.EffectiveBinaryField.Word (2 * degree))
    (source : List Bool) :
    binarySourceModularReductionWord
      (binarySourceModularReductionQuery
        (finiteWordBits lower) (finiteWordBits product) source) =
      finiteWordBits
        (GapCVP.Core.EffectiveBinaryField.reduceProduct lower product) := by
  unfold binarySourceModularReductionWord
    factor400BinarySourceModularReductionFoldOutput
    factor400BinarySourceModularReductionCurrentOutput
  simp only [Function.comp_apply,
    factor400BinarySourceModularReductionFoldPreparation_valid,
    boundedRecordFoldOutput, parseUnaryBoundedFold_word]
  rw [factor400BinarySourceModularReduction_iterate_valid
    lower product source degree (le_refl degree)]
  simp only [binarySourceModularDegreeState,
    List.append_assoc, firstFieldSuffix_valid,
    firstFieldContents_valid]
  rfl

private theorem factor400BinarySourceModularReductionFiniteWordBits_take
    {degree : ℕ}
    (word : GapCVP.Core.EffectiveBinaryField.Word (2 * degree)) :
    (finiteWordBits word).take degree =
      finiteWordBits (truncateWord word) := by
  apply List.ext_getElem
  · simp only [finiteWordBits, List.length_take, List.length_map, List.length_finRange,
      inf_eq_left]
    omega
  · intro index hleft hright
    simp only [finiteWordBits, List.getElem_take, List.getElem_map, List.getElem_finRange,
        Fin.cast_mk,
        truncateWord]

private def factor400BinarySourceModularReductionLowPreparation
    (input : List Bool) : List Bool :=
  binarySourceModularReductionDegreeUnary input ++ false ::
    binarySourceModularReductionWord input

private noncomputable def factor400BinarySourceModularReductionLowPreparationComputable :
    BitTM
      factor400BinarySourceModularReductionLowPreparation :=
  pointwiseAppendComputable
    factor400BinarySourceModularReductionDegreeUnaryComputable
    (GapCVP.TMComposition.computableInPolyTime
      factor400BinarySourceModularReductionComputable
      (prependBitComputable false))

private def binarySourceModularReductionLowWord :
    List Bool → List Bool :=
  firstFieldContents ∘
    factor400BinarySourceModularReductionLowPreparation

private noncomputable def factor400BinarySourceModularReductionLowComputable :
    BitTM
      binarySourceModularReductionLowWord :=
  GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceModularReductionLowPreparationComputable
    firstFieldContentsComputable

@[simp] private theorem factor400BinarySourceModularReductionLowWord_valid
    {degree : ℕ}
    (lower : GapCVP.Core.EffectiveBinaryField.Word degree)
    (product : GapCVP.Core.EffectiveBinaryField.Word (2 * degree))
    (source : List Bool) :
    binarySourceModularReductionLowWord
      (binarySourceModularReductionQuery
        (finiteWordBits lower) (finiteWordBits product) source) =
      finiteWordBits
        (truncateWord
          (GapCVP.Core.EffectiveBinaryField.reduceProduct lower product)) := by
  unfold binarySourceModularReductionLowWord
    factor400BinarySourceModularReductionLowPreparation
  simp only [Function.comp_apply,
    factor400BinarySourceModularReductionDegreeUnary_valid,
    factor400BinarySourceModularReductionWord_valid]
  have hlength :
      degree ≤
        (finiteWordBits
          (GapCVP.Core.EffectiveBinaryField.reduceProduct lower product)).length := by
    simp only [factor400BinaryFiniteWordBits_length]
    omega
  rw [validInput_reconstruct degree
    (finiteWordBits
      (GapCVP.Core.EffectiveBinaryField.reduceProduct lower product))
    hlength]
  rw [firstFieldContents_valid]
  exact factor400BinarySourceModularReductionFiniteWordBits_take
    (GapCVP.Core.EffectiveBinaryField.reduceProduct lower product)

end BinarySourceModularReductionFoldTM

namespace BinarySourceFieldMultiplicationTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder
open GapCVP.SourceFormulaStructuralDecoder GapCVP.OutputPolynomialCompositionClosure
open GapCVP.BinarySourceConvolutionTM GapCVP.BinarySourceModularDegreeStepCorrectness
open GapCVP.BinarySourceModularReductionFoldTM GapCVP.BinaryModularReductionTM

private def binarySourceMultiplyModValidBranch :
    List Bool → List Bool :=
  binarySourceModularReductionLowWord ∘
    binarySourceProductReductionQuery

private noncomputable def factor400BinarySourceMultiplyModValidBranchComputable :
    BitTM
      binarySourceMultiplyModValidBranch :=
  GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceProductReductionQueryComputable
    factor400BinarySourceModularReductionLowComputable

private theorem factor400BinarySourceMultiplyModValidBranch_query
    (lower left right source : List Bool) :
    binarySourceMultiplyModValidBranch
      (factor400BinarySourceFieldQuery lower left right source) =
      finiteWordBits
        (GapCVP.Core.EffectiveBinaryField.multiplyMod
          (factor400BinarySourcePaddedWord left.length lower)
          (factor400BinarySourcePaddedWord left.length left)
          (factor400BinarySourcePaddedWord left.length right)) := by
  unfold binarySourceMultiplyModValidBranch
  rw [Function.comp_apply,
    factor400BinarySourceProductReductionQuery_query,
    factor400BinarySourceModularReductionLowWord_valid]
  rfl

private theorem factor400BinarySourceMultiplyModWord_eq_physical
    (input : List Bool) :
    binarySourceMultiplyModWord input =
      if binarySourceModularStateValid input then
        binarySourceMultiplyModValidBranch input
      else
        [] := by
  cases hvalid : binarySourceModularStateValid input with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold binarySourceMultiplyModWord
      cases hfirst : readLengthPrefixedWord input with
      | none => rfl
      | some parsed =>
          obtain ⟨lower, firstSuffix⟩ := parsed
          cases hsecond : readLengthPrefixedWord firstSuffix with
          | none => simp only [hsecond]
          | some parsed =>
              obtain ⟨left, secondSuffix⟩ := parsed
              cases hthird : readLengthPrefixedWord secondSuffix with
              | none => simp only [hsecond, hthird]
              | some parsed =>
                  obtain ⟨right, source⟩ := parsed
                  simp only [binarySourceModularStateValid, payloadDecodeOutput,
                      factor400BinarySourceSkipFields, id_eq, hfirst,
                      List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
                          Function.comp_apply, firstFieldSuffix, hsecond,
                      CompTriple.comp_eq, hthird, Bool.and_self, Bool.true_eq_false] at hvalid
  | true =>
      simp only [↓reduceIte]
      obtain ⟨lower, left, right, source, hshape⟩ :=
        factor400BinarySourceModularStateValid_reconstruct input hvalid
      have hquery :
          input = factor400BinarySourceFieldQuery
            lower left right source := by
        simpa only [factor400BinarySourceFieldQuery, List.append_assoc] using hshape
      rw [hquery, factor400BinarySourceMultiplyModValidBranch_query]
      simp only [binarySourceMultiplyModWord, factor400BinarySourceFieldQuery, List.append_assoc,
          readLengthPrefixedWord_append]

/-- GapCVP reduction support. -/
noncomputable def binarySourceMultiplyModComputable :
    BitTM
      binarySourceMultiplyModWord := by
  have hphysical := sourcePreservingConditionalComputable
    factor400BinarySourceModularStateSelectionComputable
    factor400BinarySourceMultiplyModValidBranchComputable []
  convert hphysical using 1
  funext input
  exact factor400BinarySourceMultiplyModWord_eq_physical input

end BinarySourceFieldMultiplicationTM

namespace BinaryFieldInverseTM

open Turing GapCVP.BinaryFieldInverseAlgebra

theorem sourceWordValue_sourceFieldPowerIterate
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (operand :
      GapCVP.Core.EffectiveBinaryField.Word
        (GapCVP.Core.sourceFieldExponent
          (GapCVP.Core.sourceSizeParameter encodingLength formula)))
    (steps : ℕ) :
    sourceWordValue encodingLength formula
        (sourceFieldPowerIterate
          (GapCVP.Core.EffectiveBinaryField.irreducibleWord
            (GapCVP.Core.sourceFieldExponent
              (GapCVP.Core.sourceSizeParameter encodingLength formula)))
          operand steps) =
      sourceWordValue encodingLength formula operand ^ (steps + 1) := by
  induction steps with
  | zero => simp only [sourceFieldPowerIterate, Function.iterate_zero, id_eq, zero_add, pow_one]
  | succ steps ih =>
      unfold sourceFieldPowerIterate at ih ⊢
      rw [Function.iterate_succ_apply',
        sourceFieldPowerStep, sourceWordValue_multiplyMod, ih]
      rw [pow_succ]
      ring

end BinaryFieldInverseTM

namespace GaussianSourceConsistencyBridge

open Turing GapCVP.Factor400BinaryPhysicalWorkers GapCVP.GaussianRowWorker
open GapCVP.GaussianPivotScheduleTM GapCVP.GaussianPackedPivotColumnTM
open GapCVP.GaussianReducedConsistencyTM GapCVP.SourceOriginalSourcePreservingTM
open GapCVP.SourceFourFamilyBooleanPredicateTM

/-- GapCVP reduction support. -/
def binaryGaussianMalformedReducedState : List Bool :=
  binaryGaussianPackedPivotColumnWord [(true, true)] []

@[simp] private theorem binaryGaussianMalformedReducedState_inconsistent :
    binaryGaussianReducedConsistencyWord
        binaryGaussianMalformedReducedState = [false] := by
  change
    sourceFourFamilyBooleanNotWord
      (binaryGaussianFirstCellWord
        (binaryGaussianPivotWord
          (binaryGaussianPackedPivotCandidateOutput
            (binaryGaussianPackedPivotColumnWord
              [(true, true)] [])))) = [false]
  rw [binaryGaussianPackedPivotCandidateOutput_valid]
  rfl

/-- GapCVP reduction support. -/
def binaryGaussianSourceConsistencyGuard
    (system : List Bool → Option GapCVP.Core.BinaryAffineSystem)
    (input : List Bool) : Bool :=
  match system input with
  | none => false
  | some actual => actual.effectiveReducedConsistent

/-- GapCVP reduction support. -/
def binaryGaussianExpectedReducedSourceState
    (system : List Bool → Option GapCVP.Core.BinaryAffineSystem)
    (input : List Bool) : List Bool :=
  match system input with
  | none => binaryGaussianMalformedReducedState
  | some actual =>
      effectiveGaussianReducedConsistencyQuery actual input

/-- GapCVP reduction support. -/
structure BinaryGaussianExactSourceInitializer
    (system : List Bool → Option GapCVP.Core.BinaryAffineSystem) where
  /-- GapCVP reduction support. -/
  output : List Bool → List Bool
  /-- GapCVP reduction support. -/
  computer : BitTM output
  output_eq : ∀ input : List Bool,
    output input = binaryGaussianExpectedReducedSourceState system input

private def binaryGaussianExactSourceConsistencyWord
    {system : List Bool → Option GapCVP.Core.BinaryAffineSystem}
    (initializer : BinaryGaussianExactSourceInitializer system) :
    List Bool → List Bool :=
  binaryGaussianReducedConsistencyWord ∘ initializer.output

private noncomputable def binaryGaussianExactSourceConsistencyWordComputable
    {system : List Bool → Option GapCVP.Core.BinaryAffineSystem}
    (initializer : BinaryGaussianExactSourceInitializer system) :
    BitTM
      (binaryGaussianExactSourceConsistencyWord initializer) :=
  GapCVP.TMComposition.computableInPolyTime
    initializer.computer binaryGaussianReducedConsistencyComputable

private theorem binaryGaussianExactSourceConsistencyWord_eq
    {system : List Bool → Option GapCVP.Core.BinaryAffineSystem}
    (initializer : BinaryGaussianExactSourceInitializer system)
    (input : List Bool) :
    binaryGaussianExactSourceConsistencyWord initializer input =
      [binaryGaussianSourceConsistencyGuard system input] := by
  simp only [binaryGaussianExactSourceConsistencyWord,
    Function.comp_apply, initializer.output_eq]
  cases hsystem : system input with
  | none =>
      simp only [binaryGaussianExpectedReducedSourceState, hsystem,
          binaryGaussianMalformedReducedState_inconsistent, binaryGaussianSourceConsistencyGuard]
  | some actual =>
      simp only [binaryGaussianExpectedReducedSourceState,
        binaryGaussianSourceConsistencyGuard, hsystem]
      exact binaryGaussianReducedConsistencyWord_effective
        actual input

/-- GapCVP reduction support. -/
noncomputable def binaryGaussianExactSourceConsistencyComputable
    {system : List Bool → Option GapCVP.Core.BinaryAffineSystem}
    (initializer : BinaryGaussianExactSourceInitializer system) :
    BitTM
      (fun input => binaryGaussianSourceConsistencyGuard system input :: input) := by
  have hpreserved := originalSourcePreservingComputable
    (binaryGaussianExactSourceConsistencyWordComputable initializer)
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hpreserved factor400KeepFirstDropSecondComputable
  convert hphysical using 1
  funext input
  change
    binaryGaussianSourceConsistencyGuard system input :: input =
      factor400KeepFirstDropSecondWord
        (originalSourcePreservingOutput
          (binaryGaussianExactSourceConsistencyWord initializer) input)
  rw [originalSourcePreservingOutput,
    binaryGaussianExactSourceConsistencyWord_eq initializer input]
  simp only [factor400KeepFirstDropSecondWord, List.cons_append, List.nil_append, List.tail_cons]

end GaussianSourceConsistencyBridge

namespace BinaryPhysicalWordPackedMatrixTM

open Turing GapCVP.BinaryEncoding GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM

/-- GapCVP reduction support. -/
def sourcePhysicalWordPackedCheckBits
    (system : GapCVP.Core.BinaryAffineSystem) : List Bool :=
  (List.finRange system.rowCount).flatMap fun row =>
    (List.finRange system.dimension).map fun column =>
      decide (system.check row column = (1 : ZMod 2))

/-- GapCVP reduction support. -/
def sourcePhysicalWordPackedRhsBits
    (system : GapCVP.Core.BinaryAffineSystem) : List Bool :=
  (List.finRange system.rowCount).map fun row =>
    decide (system.rightHandSide row = (1 : ZMod 2))

/-- GapCVP reduction support. -/
def sourcePhysicalWordPackedQueryPreparation
    (queries : List (List Bool)) (input : List Bool) : List Bool :=
  unaryBoundedFoldWord queries.length
    (sourceMixedRadixOriginalSourceQueryStream queries ++
      lengthPrefixedWord input)

theorem sourcePhysicalWordPackedFlatMap_singleton
    {α : Type} (values : List α) (bit : α → Bool) :
    values.flatMap (fun value => [bit value]) = values.map bit := by
  calc
    values.flatMap (fun value => [bit value]) =
        (values.map bit).flatMap (fun value => [value]) := by
          simp only [List.flatMap_map]
    _ = values.map bit := List.flatMap_singleton' _

end BinaryPhysicalWordPackedMatrixTM

namespace GaussianAdaptivePackedTraceCorrectness

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.BinaryPhysicalWordPackedMatrixTM
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePivotStepTM

theorem sourcePhysicalWordPackedCheckBits_eq_effective_initial
    (system : BinaryAffineSystem) :
    sourcePhysicalWordPackedCheckBits system =
      effectiveGaussianPackedCheckBits
        (initialState system.effectiveGaussianSystem) := by
  rfl

theorem sourcePhysicalWordPackedRhsBits_eq_effective_initial
    (system : BinaryAffineSystem) :
    sourcePhysicalWordPackedRhsBits system =
      effectiveGaussianPackedRhsBits
        (initialState system.effectiveGaussianSystem) := by
  rfl

/-- GapCVP reduction support. -/
def effectiveGaussianPackedPivotCatalogue
    {m n : ℕ} (state : State m n) : List Bool :=
  binaryGaussianPivotBatchStream
    ((List.finRange n).map
      (effectiveGaussianStatePivotWord state))

/-- GapCVP reduction support. -/
def effectiveGaussianPackedStateWord
    {m n : ℕ} (state : State m n) (source : List Bool) : List Bool :=
  lengthPrefixedWord (effectiveGaussianPackedCheckBits state) ++
    lengthPrefixedWord (effectiveGaussianPackedRhsBits state) ++
    lengthPrefixedWord (List.replicate state.nextPivot true) ++
    lengthPrefixedWord (effectiveGaussianPackedPivotCatalogue state) ++
    source

/-- GapCVP reduction support. -/
def gaussianPackedStateCheckBits : List Bool → List Bool :=
  firstFieldContents

/-- GapCVP reduction support. -/
noncomputable def gaussianPackedStateCheckBitsComputable :
    BitTM
      gaussianPackedStateCheckBits :=
  firstFieldContentsComputable

/-- GapCVP reduction support. -/
def gaussianPackedStateRhsBits : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix

/-- GapCVP reduction support. -/
noncomputable def gaussianPackedStateRhsBitsComputable :
    BitTM
      gaussianPackedStateRhsBits :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable

/-- GapCVP reduction support. -/
def gaussianPackedInitialOriginalSource : List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix

/-- GapCVP reduction support. -/
noncomputable def gaussianPackedInitialOriginalSourceComputable :
    BitTM
      gaussianPackedInitialOriginalSource :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable

theorem gaussianPackedStateCheckBits_matrixWord
    (checks rhs source : List Bool) :
    gaussianPackedStateCheckBits
        (lengthPrefixedWord checks ++
          lengthPrefixedWord rhs ++ source) = checks := by
  simp only [gaussianPackedStateCheckBits, List.append_assoc, firstFieldContents_valid]

theorem gaussianPackedStateRhsBits_matrixWord
    (checks rhs source : List Bool) :
    gaussianPackedStateRhsBits
        (lengthPrefixedWord checks ++
          lengthPrefixedWord rhs ++ source) = rhs := by
  simp only [gaussianPackedStateRhsBits, List.append_assoc, Function.comp_apply,
      firstFieldSuffix_valid,
      firstFieldContents_valid]

theorem gaussianPackedInitialOriginalSource_matrixWord
    (checks rhs source : List Bool) :
    gaussianPackedInitialOriginalSource
        (lengthPrefixedWord checks ++
          lengthPrefixedWord rhs ++ source) = source := by
  simp only [gaussianPackedInitialOriginalSource, List.append_assoc, Function.comp_apply,
      firstFieldSuffix_valid]

@[simp] theorem effectiveGaussianPackedPivotCatalogue_initial
    {m n : ℕ} (system : System m n) :
    effectiveGaussianPackedPivotCatalogue
        (initialState system) =
      binaryGaussianPivotBatchStream
        (List.replicate n [false]) := by
  have hpivot (column : Fin n) :
      effectiveGaussianStatePivotWord
        (initialState system) column = [false] := by
    rfl
  have hmap :
      (List.finRange n).map
          (effectiveGaussianStatePivotWord (initialState system)) =
        List.replicate n [false] := by
    calc
      (List.finRange n).map
          (effectiveGaussianStatePivotWord (initialState system)) =
        (List.finRange n).map
          (fun _ : Fin n => [false]) := by
          exact congrArg (List.map · (List.finRange n))
            (funext hpivot)
      _ = List.replicate n [false] := by
        simp only [List.map_const', List.length_finRange]
  exact congrArg binaryGaussianPivotBatchStream hmap

end GaussianAdaptivePackedTraceCorrectness

namespace GaussianPhysicalWordReducedAtomTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.GaussianAdaptiveEliminationCorrectness
open GapCVP.Factor400BinaryEffectiveBasisSerializerTM GapCVP.SourceWholeOutputAssemblyTM

private def effectiveGaussianStateTargetTag
    {m n : ℕ} (state : State m n) (column : Fin n) : List Bool :=
  match effectiveGaussianStatePivotRowOption state column with
  | none => [false]
  | some row => [decide (state.system.rhs row = (1 : ZMod 2))]

/-- GapCVP reduction support. -/
def effectiveGaussianStateBasisTag
    {m n : ℕ} (state : State m n)
    (row column : Fin n) : List Bool :=
  match effectiveGaussianStatePivotRowOption state row,
      effectiveGaussianStatePivotRowOption state column with
  | some pivot, none =>
      [decide (state.system.check pivot column = (1 : ZMod 2)), false]
  | some _, some _ =>
      if row = column then [true, true] else [false, false]
  | none, none =>
      if row = column then [true, false] else [false, false]
  | none, some _ => [false, false]

private theorem effectiveGaussianStateTargetTag_effective_atom
    (system : BinaryAffineSystem) (column : Fin system.dimension) :
    effectiveTargetPackedAtom
        (effectiveGaussianStateTargetTag
          system.effectiveGaussianState column) =
      encodeAtomic
        ((system.effectiveAffineRepresentative column : ℤ) : ℚ) := by
  unfold effectiveGaussianStateTargetTag
  rw [effectiveGaussianStatePivotRow_effective]
  cases hpivot : system.effectivePivotRowOption column with
  | none =>
      simp only [effectiveTargetPackedAtom_false, BinaryAffineSystem.effectiveAffineRepresentative,
          BinaryAffineSystem.effectiveAffineBits, hpivot, ZMod.val_zero, CharP.cast_eq_zero,
              Int.cast_zero]
  | some row =>
      rcases effectiveBinary_eq_zero_or_one
        (system.effectiveGaussianState.system.rhs row) with hzero | hone
      · simp only [hzero, zero_ne_one, decide_false, effectiveTargetPackedAtom_false,
            BinaryAffineSystem.effectiveAffineRepresentative,
                BinaryAffineSystem.effectiveAffineBits, hpivot, ZMod.val_zero,
            CharP.cast_eq_zero, Int.cast_zero]
      · have hrepresentative :
            system.effectiveAffineRepresentative column = (1 : ℤ) := by
          change ((system.effectiveAffineBits column).val : ℤ) = 1
          simp only [BinaryAffineSystem.effectiveAffineBits,
            hpivot, hone, ZMod.val_one, Nat.cast_one]
        simp only [hone, decide_true, effectiveTargetPackedAtom_true, hrepresentative,
            Int.cast_one]

private theorem effectiveGaussianStateBasisTag_effective_atom
    (system : BinaryAffineSystem)
    (row column : Fin system.dimension) :
    effectiveBasisPackedAtom
        (effectiveGaussianStateBasisTag
          system.effectiveGaussianState row column) =
      encodeAtomic (system.effectiveSquareBasisMatrix row column) := by
  unfold effectiveGaussianStateBasisTag
  rw [effectiveGaussianStatePivotRow_effective,
    effectiveGaussianStatePivotRow_effective]
  cases hrow : system.effectivePivotRowOption row with
  | none =>
      cases hcolumn : system.effectivePivotRowOption column with
      | none =>
          by_cases hdiagonal : row = column
          · simp only [hdiagonal, ↓reduceIte, effectiveBasisPackedAtom_one,
              BinaryAffineSystem.effectiveSquareBasisMatrix,
                hcolumn]
          · simp only [hdiagonal, ↓reduceIte, effectiveBasisPackedAtom_zero,
                BinaryAffineSystem.effectiveSquareBasisMatrix, hrow, hcolumn]
      | some pivot =>
          simp only [effectiveBasisPackedAtom_zero, BinaryAffineSystem.effectiveSquareBasisMatrix,
              hrow, hcolumn]
  | some pivot =>
      cases hcolumn : system.effectivePivotRowOption column with
      | none =>
          rcases effectiveBinary_eq_zero_or_one
            (system.effectiveGaussianState.system.check pivot column)
              with hzero | hone
          · simp only [hzero, zero_ne_one, decide_false, effectiveBasisPackedAtom_zero,
                BinaryAffineSystem.effectiveSquareBasisMatrix, hrow, hcolumn, ZMod.val_zero,
                    CharP.cast_eq_zero]
          · have hentry :
                system.effectiveSquareBasisMatrix row column =
                  (1 : ℤ) := by
              simp only [BinaryAffineSystem.effectiveSquareBasisMatrix,
                hrow, hcolumn, hone, ZMod.val_one, Nat.cast_one]
            simp only [hone, decide_true, effectiveBasisPackedAtom_one, hentry]
      | some other =>
          by_cases hdiagonal : row = column
          · simp only [hdiagonal, ↓reduceIte, effectiveBasisPackedAtom_two,
              BinaryAffineSystem.effectiveSquareBasisMatrix,
                hcolumn]
          · simp only [hdiagonal, ↓reduceIte, effectiveBasisPackedAtom_zero,
                BinaryAffineSystem.effectiveSquareBasisMatrix, hrow, hcolumn]

end GaussianPhysicalWordReducedAtomTM

namespace GaussianPackedStateTargetAtomTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert GapCVP.GaussianRowWorker
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptiveEliminationCorrectness
open GapCVP.GaussianAdaptivePackedTraceCorrectness GapCVP.GaussianPhysicalWordReducedAtomTM
open GapCVP.Factor400BinaryEffectiveBasisSerializerTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceFourFamilyBooleanPredicateTM

/-- GapCVP reduction support. -/
def gaussianPackedIndexedStateWord
    (index : ℕ) (state : List Bool) : List Bool :=
  lengthPrefixedWord (List.replicate index true) ++ state

private def gaussianPackedIndexedColumnUnary : List Bool → List Bool :=
  firstFieldContents

private noncomputable def gaussianPackedIndexedColumnUnaryComputable :
    BitTM
      gaussianPackedIndexedColumnUnary :=
  firstFieldContentsComputable

private def gaussianPackedIndexedState : List Bool → List Bool :=
  firstFieldSuffix

private noncomputable def gaussianPackedIndexedStateComputable :
    BitTM
      gaussianPackedIndexedState :=
  firstFieldSuffixComputable

@[simp] private theorem gaussianPackedIndexedColumnUnary_word
    (index : ℕ) (state : List Bool) :
    gaussianPackedIndexedColumnUnary
        (gaussianPackedIndexedStateWord index state) =
      List.replicate index true := by
  exact firstFieldContents_valid
    (List.replicate index true) state

@[simp] private theorem gaussianPackedIndexedState_word
    (index : ℕ) (state : List Bool) :
    gaussianPackedIndexedState
        (gaussianPackedIndexedStateWord index state) = state := by
  exact firstFieldSuffix_valid
    (List.replicate index true) state

private def gaussianPackedStatePivotRecords : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix ∘
    firstFieldSuffix ∘ firstFieldSuffix

private noncomputable def gaussianPackedStatePivotRecordsComputable :
    BitTM
      gaussianPackedStatePivotRecords := by
  have hone := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable
  have hthree := GapCVP.TMComposition.computableInPolyTime
    hone firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hthree firstFieldContentsComputable

@[simp] private theorem gaussianPackedStatePivotRecords_word
    {m n : ℕ} (state : State m n) (source : List Bool) :
    gaussianPackedStatePivotRecords
        (effectiveGaussianPackedStateWord state source) =
      effectiveGaussianPackedPivotCatalogue state := by
  simp only [gaussianPackedStatePivotRecords, effectiveGaussianPackedStateWord, List.append_assoc,
      Function.comp_apply, firstFieldSuffix_valid, firstFieldContents_valid]

private def gaussianPackedIndexedRhsBits : List Bool → List Bool :=
  gaussianPackedStateRhsBits ∘ gaussianPackedIndexedState

private noncomputable def gaussianPackedIndexedRhsBitsComputable :
    BitTM
      gaussianPackedIndexedRhsBits :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedIndexedStateComputable
    gaussianPackedStateRhsBitsComputable

private def gaussianPackedIndexedPivotQuery
    (input : List Bool) : List Bool :=
  gaussianPackedIndexedColumnUnary input ++
    false :: gaussianPackedStatePivotRecords
      (gaussianPackedIndexedState input)

private noncomputable def gaussianPackedIndexedPivotQueryComputable :
    BitTM
      gaussianPackedIndexedPivotQuery := by
  have hstate := GapCVP.TMComposition.computableInPolyTime
    gaussianPackedIndexedStateComputable
    gaussianPackedStatePivotRecordsComputable
  have hsuffix := GapCVP.TMComposition.computableInPolyTime
    hstate (prependBitComputable false)
  exact pointwiseAppendComputable
    gaussianPackedIndexedColumnUnaryComputable hsuffix

private def gaussianPackedIndexedPivotOutput : List Bool → List Bool :=
  binaryGaussianIndexedBatchOutput ∘ gaussianPackedIndexedPivotQuery

private noncomputable def gaussianPackedIndexedPivotComputable :
    BitTM
      gaussianPackedIndexedPivotOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedIndexedPivotQueryComputable
    binaryGaussianIndexedBatchComputable

private theorem gaussianPackedIndexedPivotOutput_word
    {m n : ℕ} (state : State m n)
    (column : Fin n) (source : List Bool) :
    gaussianPackedIndexedPivotOutput
        (gaussianPackedIndexedStateWord column.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianStatePivotWord state column := by
  let records := (List.finRange n).map
    (effectiveGaussianStatePivotWord state)
  have hindex : column.val < records.length := by
    simp only [List.length_map, List.length_finRange, Fin.is_lt, records]
  unfold gaussianPackedIndexedPivotOutput
  rw [Function.comp_apply]
  unfold gaussianPackedIndexedPivotQuery
  rw [gaussianPackedIndexedColumnUnary_word,
    gaussianPackedIndexedState_word,
    gaussianPackedStatePivotRecords_word]
  change
    binaryGaussianIndexedBatchOutput
        (List.replicate column.val true ++
          false :: binaryGaussianPivotBatchStream records) =
      effectiveGaussianStatePivotWord state column
  have hselect := binaryGaussianIndexedBatchOutput_valid
    records [] column.val hindex
  simp only [List.append_nil] at hselect
  change
    binaryGaussianIndexedBatchOutput
        (List.replicate column.val true ++
          false :: binaryGaussianPivotBatchStream records) =
      records[column.val] at hselect
  rw [hselect]
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta, records]

private def gaussianPackedIndexedPivotRowUnary : List Bool → List Bool :=
  List.tail ∘ gaussianPackedIndexedPivotOutput

private noncomputable def gaussianPackedIndexedPivotRowUnaryComputable :
    BitTM
      gaussianPackedIndexedPivotRowUnary :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedIndexedPivotComputable dropHeadComputable

private def gaussianPackedIndexedPivotPresentWord : List Bool → List Bool :=
  binaryGaussianFirstCellWord ∘ gaussianPackedIndexedPivotOutput

private noncomputable def gaussianPackedIndexedPivotPresentComputable :
    BitTM
      gaussianPackedIndexedPivotPresentWord :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedIndexedPivotComputable
    binaryGaussianFirstCellComputable

private def gaussianPackedIndexedPivotRhsBit : List Bool → List Bool :=
  fiveFamilyOriginalDynamicBitWord
    gaussianPackedIndexedPivotRowUnary gaussianPackedIndexedRhsBits

private noncomputable def gaussianPackedIndexedPivotRhsBitComputable :
    BitTM
      gaussianPackedIndexedPivotRhsBit :=
  fiveOriginalDynamicBitComputable
    gaussianPackedIndexedPivotRowUnaryComputable
    gaussianPackedIndexedRhsBitsComputable

/-- GapCVP reduction support. -/
def gaussianPackedIndexedTargetBit : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    gaussianPackedIndexedPivotPresentWord
    gaussianPackedIndexedPivotRhsBit

/-- GapCVP reduction support. -/
noncomputable def gaussianPackedIndexedTargetBitComputable :
    BitTM
      gaussianPackedIndexedTargetBit :=
  fourFamilyBooleanAndComputable
    gaussianPackedIndexedPivotPresentComputable
    gaussianPackedIndexedPivotRhsBitComputable

/-- GapCVP reduction support. -/
def gaussianPackedIndexedTargetAtom : List Bool → List Bool :=
  effectiveTargetPackedAtom ∘ gaussianPackedIndexedTargetBit

private noncomputable def gaussianPackedIndexedTargetAtomComputable :
    BitTM
      gaussianPackedIndexedTargetAtom :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedIndexedTargetBitComputable
    effectiveTargetPackedAtomComputable

private theorem effectiveGaussianPackedRhsBits_drop_head
    {m n : ℕ} (state : State m n) (row : Fin m) :
    ((effectiveGaussianPackedRhsBits state).drop row.val).headD false =
      decide (state.system.rhs row = (1 : ZMod 2)) := by
  have hindex : row.val < (effectiveGaussianPackedRhsBits state).length := by
    simp only [effectiveGaussianPackedRhsBits, List.length_map, List.length_finRange, Fin.is_lt]
  rw [List.drop_eq_getElem_cons hindex]
  simp only [effectiveGaussianPackedRhsBits, List.getElem_map, List.getElem_finRange, Fin.cast_mk,
      Fin.eta,
      List.headD_eq_head?_getD, List.head?_cons, Option.getD_some]

theorem gaussianPackedIndexedTargetAtom_effective
    (system : BinaryAffineSystem)
    (column : Fin system.dimension) (source : List Bool) :
    gaussianPackedIndexedTargetAtom
        (gaussianPackedIndexedStateWord column.val
          (effectiveGaussianPackedStateWord
            system.effectiveGaussianState source)) =
      encodeAtomic
        ((system.effectiveAffineRepresentative column : ℤ) : ℚ) := by
  let state := system.effectiveGaussianState
  let input := gaussianPackedIndexedStateWord column.val
    (effectiveGaussianPackedStateWord state source)
  have hpivot := gaussianPackedIndexedPivotOutput_word
    state column source
  have hrhsSource : gaussianPackedIndexedRhsBits input =
      effectiveGaussianPackedRhsBits state := by
    unfold gaussianPackedIndexedRhsBits
    rw [Function.comp_apply]
    unfold gaussianPackedStateRhsBits
    rw [Function.comp_apply]
    rw [show gaussianPackedIndexedState input =
      effectiveGaussianPackedStateWord state source by
        exact gaussianPackedIndexedState_word
          column.val (effectiveGaussianPackedStateWord state source)]
    unfold effectiveGaussianPackedStateWord
    simp only [List.append_assoc]
    rw [firstFieldSuffix_valid]
    exact firstFieldContents_valid
      (effectiveGaussianPackedRhsBits state)
      (lengthPrefixedWord (List.replicate state.nextPivot true) ++
        (lengthPrefixedWord (effectiveGaussianPackedPivotCatalogue state) ++
          source))
  unfold gaussianPackedIndexedTargetAtom
  rw [Function.comp_apply]
  change
    effectiveTargetPackedAtom
      (gaussianPackedIndexedTargetBit input) = _
  cases hpivotRow : effectiveGaussianStatePivotRowOption state column with
  | none =>
      have hpivotWord : gaussianPackedIndexedPivotOutput input =
          [false] := by
        simpa only [effectiveGaussianStatePivotWord, hpivotRow, input] using hpivot
      have hrow : gaussianPackedIndexedPivotRowUnary input =
          List.replicate 0 true := by
        simp only [gaussianPackedIndexedPivotRowUnary, Function.comp_apply, hpivotWord,
            List.tail_cons,
            List.replicate_zero]
      have hread := fiveOriginalDynamicBitWord_valid
        gaussianPackedIndexedPivotRowUnary
        gaussianPackedIndexedRhsBits input 0 hrow
      have hpresent : gaussianPackedIndexedPivotPresentWord input =
          [false] := by
        simp only [gaussianPackedIndexedPivotPresentWord, Function.comp_apply, hpivotWord,
            binaryGaussianFirstCellWord_valid]
      have hbit := fourFamilyBooleanAndOutput_bits
        gaussianPackedIndexedPivotPresentWord
        gaussianPackedIndexedPivotRhsBit input false
        ((gaussianPackedIndexedRhsBits input).headD false)
        hpresent hread
      rw [show gaussianPackedIndexedTargetBit input =
        sourceFourFamilyBooleanAndOutput
          gaussianPackedIndexedPivotPresentWord
          gaussianPackedIndexedPivotRhsBit input from rfl, hbit]
      have hpure : system.effectivePivotRowOption column = none := by
        simpa only [state,
          effectiveGaussianStatePivotRow_effective] using hpivotRow
      simp only [List.headD_eq_head?_getD, Bool.false_and, effectiveTargetPackedAtom_false,
          BinaryAffineSystem.effectiveAffineRepresentative, BinaryAffineSystem.effectiveAffineBits,
              hpure, ZMod.val_zero,
          CharP.cast_eq_zero, Int.cast_zero]
  | some row =>
      have hpivotWord : gaussianPackedIndexedPivotOutput input =
          true :: List.replicate row.val true := by
        simpa only [effectiveGaussianStatePivotWord, hpivotRow, input] using hpivot
      have hrow : gaussianPackedIndexedPivotRowUnary input =
          List.replicate row.val true := by
        simp only [gaussianPackedIndexedPivotRowUnary, Function.comp_apply, hpivotWord,
            List.tail_cons]
      have hread := fiveOriginalDynamicBitWord_valid
        gaussianPackedIndexedPivotRowUnary
        gaussianPackedIndexedRhsBits input row.val hrow
      rw [hrhsSource, effectiveGaussianPackedRhsBits_drop_head]
        at hread
      have hpresent : gaussianPackedIndexedPivotPresentWord input =
          [true] := by
        simp only [gaussianPackedIndexedPivotPresentWord, Function.comp_apply, hpivotWord,
            binaryGaussianFirstCellWord_valid]
      have hbit := fourFamilyBooleanAndOutput_bits
        gaussianPackedIndexedPivotPresentWord
        gaussianPackedIndexedPivotRhsBit input true
        (decide (state.system.rhs row = (1 : ZMod 2)))
        hpresent hread
      rw [show gaussianPackedIndexedTargetBit input =
        sourceFourFamilyBooleanAndOutput
          gaussianPackedIndexedPivotPresentWord
          gaussianPackedIndexedPivotRhsBit input from rfl, hbit]
      change
        effectiveTargetPackedAtom
          [decide (state.system.rhs row = (1 : ZMod 2))] = _
      have htag : effectiveGaussianStateTargetTag state column =
          [decide (state.system.rhs row = (1 : ZMod 2))] := by
        simp only [effectiveGaussianStateTargetTag, hpivotRow]
      rw [← htag]
      exact effectiveGaussianStateTargetTag_effective_atom
        system column

end GaussianPackedStateTargetAtomTM

namespace GaussianAdaptivePhysicalStateCellTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.SourceMachineCert
open GapCVP.SourceStructuralTuringTM GapCVP.SourceFormulaStructuralDecoder
open GapCVP.BinaryDimensionTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.SourceMixedRadixUnaryQuotientRemainderTM
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness

/-- GapCVP reduction support. -/
def gaussianDenseStateCheckLengthUnary : List Bool → List Bool :=
  sourceInputLengthUnary ∘ gaussianPackedStateCheckBits

private noncomputable def gaussianDenseStateCheckLengthUnaryComputable :
    BitTM
      gaussianDenseStateCheckLengthUnary :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedStateCheckBitsComputable
    sourceInputLengthUnaryComputable

/-- GapCVP reduction support. -/
def gaussianDenseStateRowCountUnary : List Bool → List Bool :=
  sourceInputLengthUnary ∘ gaussianPackedStateRhsBits

/-- GapCVP reduction support. -/
noncomputable def gaussianDenseStateRowCountUnaryComputable :
    BitTM
      gaussianDenseStateRowCountUnary :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedStateRhsBitsComputable
    sourceInputLengthUnaryComputable

/-- GapCVP reduction support. -/
def gaussianDenseStateDimensionDivisionQuery
    (input : List Bool) : List Bool :=
  gaussianDenseStateCheckLengthUnary input ++
    false :: (gaussianDenseStateRowCountUnary input ++
      false :: input)

private noncomputable def gaussianDenseStateDimensionDivisionQueryComputable :
    BitTM
      gaussianDenseStateDimensionDivisionQuery := by
  have hsource := prependBitComputable false
  have hmodulus := pointwiseAppendComputable
    gaussianDenseStateRowCountUnaryComputable hsource
  have hdelimited := GapCVP.TMComposition.computableInPolyTime
    hmodulus (prependBitComputable false)
  have hphysical := pointwiseAppendComputable
    gaussianDenseStateCheckLengthUnaryComputable hdelimited
  change BitTM
    (fun input => gaussianDenseStateCheckLengthUnary input ++
      false :: (gaussianDenseStateRowCountUnary input ++
        false :: input))
  simpa only [Function.comp_apply] using hphysical

/-- GapCVP reduction support. -/
def gaussianDenseStateDimensionUnary : List Bool → List Bool :=
  List.tail ∘ unaryPrefixOutput ∘ sourceUnaryDivisionOutput ∘
    gaussianDenseStateDimensionDivisionQuery

/-- GapCVP reduction support. -/
noncomputable def gaussianDenseStateDimensionUnaryComputable :
    BitTM
      gaussianDenseStateDimensionUnary := by
  have hdivision := GapCVP.TMComposition.computableInPolyTime
    gaussianDenseStateDimensionDivisionQueryComputable
    sourceUnaryDivisionComputable
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    hdivision unaryPrefixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hprefix dropHeadComputable

@[simp] theorem effectiveGaussianPackedCheckBits_length
    {m n : ℕ} (state : State m n) :
    (effectiveGaussianPackedCheckBits state).length = m * n := by
  simp only [effectiveGaussianPackedCheckBits, List.length_flatMap, List.length_map,
      List.length_finRange,
      List.map_const', List.sum_replicate, smul_eq_mul]

@[simp] theorem effectiveGaussianPackedRhsBits_length
    {m n : ℕ} (state : State m n) :
    (effectiveGaussianPackedRhsBits state).length = m := by
  simp only [effectiveGaussianPackedRhsBits, List.length_map, List.length_finRange]

@[simp] theorem gaussianDenseStateRowCountUnary_effective
    {m n : ℕ} (state : State m n) (source : List Bool) :
    gaussianDenseStateRowCountUnary
        (effectiveGaussianPackedStateWord state source) =
      List.replicate m true := by
  unfold gaussianDenseStateRowCountUnary
    gaussianPackedStateRhsBits
  simp only [effectiveGaussianPackedStateWord, List.append_assoc, Function.comp_apply,
      sourceInputLengthUnary,
      firstFieldSuffix_valid, firstFieldContents_valid, effectiveGaussianPackedRhsBits_length]

@[simp] private theorem gaussianDenseStateCheckLengthUnary_effective
    {m n : ℕ} (state : State m n) (source : List Bool) :
    gaussianDenseStateCheckLengthUnary
        (effectiveGaussianPackedStateWord state source) =
      List.replicate (m * n) true := by
  unfold gaussianDenseStateCheckLengthUnary
    gaussianPackedStateCheckBits
  simp only [effectiveGaussianPackedStateWord, List.append_assoc, Function.comp_apply,
      sourceInputLengthUnary,
      firstFieldContents_valid, effectiveGaussianPackedCheckBits_length]

theorem gaussianDenseStateDimensionUnary_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (hrows : 0 < m) :
    gaussianDenseStateDimensionUnary
        (effectiveGaussianPackedStateWord state source) =
      List.replicate n true := by
  let word := effectiveGaussianPackedStateWord state source
  have hcheck : gaussianDenseStateCheckLengthUnary word =
      List.replicate (m * n) true :=
    gaussianDenseStateCheckLengthUnary_effective state source
  have hrhs : gaussianDenseStateRowCountUnary word =
      List.replicate m true :=
    gaussianDenseStateRowCountUnary_effective state source
  have hquery : gaussianDenseStateDimensionDivisionQuery word =
      sourceUnaryDivisionQuery (m * n) m word := by
    simp only [gaussianDenseStateDimensionDivisionQuery, hcheck, hrhs, sourceUnaryDivisionQuery]
  unfold gaussianDenseStateDimensionUnary
  simp only [Function.comp_apply]
  rw [hquery, sourceUnaryDivisionOutput_valid
    (m * n) m word hrows]
  rw [unaryPrefixOutput_replicate_delimiter]
  simp only [List.tail_cons]
  rw [Nat.mul_div_cancel_left n hrows]

end GaussianAdaptivePhysicalStateCellTM

namespace GaussianAdaptivePackedStateLookupTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian
open GapCVP.SourceFormulaStructuralDecoder GapCVP.OutputBoundedDependentRecordFold
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.BinaryExplicitAffineRows
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePhysicalStateCellTM GapCVP.GaussianAdaptivePivotStepTM

private def gaussianPackedCellDimensionUnary : List Bool → List Bool :=
  gaussianDenseStateDimensionUnary ∘
    sourceExplicitAffineCellOriginalSource

private noncomputable def gaussianPackedCellDimensionUnaryComputable :
    BitTM
      gaussianPackedCellDimensionUnary :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    gaussianDenseStateDimensionUnaryComputable

private def gaussianPackedCellCheckBits : List Bool → List Bool :=
  gaussianPackedStateCheckBits ∘
    sourceExplicitAffineCellOriginalSource

private noncomputable def gaussianPackedCellCheckBitsComputable :
    BitTM
      gaussianPackedCellCheckBits :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    gaussianPackedStateCheckBitsComputable

private def gaussianPackedCellRhsBits : List Bool → List Bool :=
  gaussianPackedStateRhsBits ∘
    sourceExplicitAffineCellOriginalSource

private noncomputable def gaussianPackedCellRhsBitsComputable :
    BitTM
      gaussianPackedCellRhsBits :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    gaussianPackedStateRhsBitsComputable

private def gaussianPackedCellRowOffsetUnary : List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    sourceExplicitAffineCellRow gaussianPackedCellDimensionUnary

private noncomputable def gaussianPackedCellRowOffsetUnaryComputable :
    BitTM
      gaussianPackedCellRowOffsetUnary :=
  fourFamilyComputedUnaryProductComputable
    sourceExplicitAffineCellRowComputable
    gaussianPackedCellDimensionUnaryComputable

private def gaussianPackedCellFlatIndexUnary : List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    gaussianPackedCellRowOffsetUnary sourceExplicitAffineCellColumn

private noncomputable def gaussianPackedCellFlatIndexUnaryComputable :
    BitTM
      gaussianPackedCellFlatIndexUnary :=
  fourFamilyComputedUnarySumComputable
    gaussianPackedCellRowOffsetUnaryComputable
    sourceExplicitAffineCellColumnComputable

/-- GapCVP reduction support. -/
def gaussianPackedStateCheckCellWord : List Bool → List Bool :=
  fiveFamilyOriginalDynamicBitWord
    gaussianPackedCellFlatIndexUnary gaussianPackedCellCheckBits

/-- GapCVP reduction support. -/
noncomputable def gaussianPackedStateCheckCellComputable :
    BitTM
      gaussianPackedStateCheckCellWord :=
  fiveOriginalDynamicBitComputable
    gaussianPackedCellFlatIndexUnaryComputable
    gaussianPackedCellCheckBitsComputable

/-- GapCVP reduction support. -/
def gaussianPackedStateRhsCellWord : List Bool → List Bool :=
  fiveFamilyOriginalDynamicBitWord
    sourceExplicitAffineCellRow gaussianPackedCellRhsBits

/-- GapCVP reduction support. -/
noncomputable def gaussianPackedStateRhsCellComputable :
    BitTM
      gaussianPackedStateRhsCellWord :=
  fiveOriginalDynamicBitComputable
    sourceExplicitAffineCellRowComputable
    gaussianPackedCellRhsBitsComputable

private theorem gaussianPackedCellDimensionUnary_query
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row column : ℕ) (hrows : 0 < m) :
    gaussianPackedCellDimensionUnary
        (affineCellQuery row column
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate n true := by
  unfold gaussianPackedCellDimensionUnary
  simp only [Function.comp_apply,
    sourceExplicitAffineCellOriginalSource_query]
  exact gaussianDenseStateDimensionUnary_effective
    state source hrows

private theorem gaussianPackedCellCheckBits_query
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row column : ℕ) :
    gaussianPackedCellCheckBits
        (affineCellQuery row column
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianPackedCheckBits state := by
  unfold gaussianPackedCellCheckBits gaussianPackedStateCheckBits
  simp only [effectiveGaussianPackedStateWord, List.append_assoc, Function.comp_apply,
      sourceExplicitAffineCellOriginalSource_query, firstFieldContents_valid]

private theorem gaussianPackedCellRhsBits_query
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row column : ℕ) :
    gaussianPackedCellRhsBits
        (affineCellQuery row column
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianPackedRhsBits state := by
  unfold gaussianPackedCellRhsBits gaussianPackedStateRhsBits
  simp only [effectiveGaussianPackedStateWord, List.append_assoc, Function.comp_apply,
      sourceExplicitAffineCellOriginalSource_query, firstFieldSuffix_valid,
          firstFieldContents_valid]

private theorem gaussianPackedCellRowOffsetUnary_query
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row column : ℕ) (hrows : 0 < m) :
    gaussianPackedCellRowOffsetUnary
        (affineCellQuery row column
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate (row * n) true := by
  apply fourFamilyComputedUnaryProductOutput_valid
    sourceExplicitAffineCellRow gaussianPackedCellDimensionUnary
    (affineCellQuery row column
      (effectiveGaussianPackedStateWord state source)) row n
  · exact sourceExplicitAffineCellRow_query
      row column (effectiveGaussianPackedStateWord state source)
  · exact gaussianPackedCellDimensionUnary_query
      state source row column hrows

private theorem gaussianPackedCellFlatIndexUnary_query
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row column : ℕ) (hrows : 0 < m) :
    gaussianPackedCellFlatIndexUnary
        (affineCellQuery row column
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate (row * n + column) true := by
  apply fourFamilyComputedUnarySumOutput_valid
    gaussianPackedCellRowOffsetUnary
    sourceExplicitAffineCellColumn
    (affineCellQuery row column
      (effectiveGaussianPackedStateWord state source))
    (row * n) column
  · exact gaussianPackedCellRowOffsetUnary_query
      state source row column hrows
  · exact sourceExplicitAffineCellColumn_query
      row column (effectiveGaussianPackedStateWord state source)

private theorem gaussianDenseRowMajorBits_getD
    {m n : ℕ} (entry : Fin m → Fin n → Bool)
    (row : Fin m) (column : Fin n) :
    ((List.finRange m).flatMap fun index =>
      (List.finRange n).map (entry index)).getD
        (row.val * n + column.val) false =
      entry row column := by
  induction m with
  | zero => exact Fin.elim0 row
  | succ m ih =>
      have hsplit :
          (List.finRange (m + 1)).flatMap
              (fun index =>
                (List.finRange n).map (entry index)) =
            (List.finRange n).map (entry 0) ++
              (List.finRange m).flatMap
                (fun index =>
                  (List.finRange n).map
                    (entry index.succ)) := by
        rw [List.finRange_succ]
        simp only [List.flatMap_cons, List.flatMap_map]
      refine Fin.cases ?_ (fun previous => ?_) row
      · simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add]
        rw [hsplit]
        have hcolumn :
            column.val <
              ((List.finRange n).map (entry 0)).length := by
          simpa only [List.length_map, List.length_finRange]
            using column.isLt
        rw [List.getD_append
          ((List.finRange n).map (entry 0))
          ((List.finRange m).flatMap
            (fun index =>
              (List.finRange n).map (entry index.succ)))
          false column.val hcolumn]
        rw [List.getD_eq_getElem
          ((List.finRange n).map (entry 0)) false hcolumn]
        simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta]
      · rw [hsplit]
        have hprefix :
            ((List.finRange n).map (entry 0)).length ≤
              previous.succ.val * n + column.val := by
          simp only [List.length_map, List.length_finRange,
            Fin.val_succ, Nat.succ_mul]
          omega
        rw [List.getD_append_right
          ((List.finRange n).map (entry 0))
          ((List.finRange m).flatMap
            (fun index =>
              (List.finRange n).map (entry index.succ)))
          false (previous.succ.val * n + column.val) hprefix]
        simp only [List.length_map, List.length_finRange]
        have hoffset :
            previous.succ.val * n + column.val - n =
              previous.val * n + column.val := by
          simp only [Fin.val_succ, Nat.succ_mul]
          omega
        rw [hoffset]
        exact ih (fun index => entry index.succ) previous

theorem gaussianPackedStateCheckCellWord_query
    {m n : ℕ} (state : State m n)
    (source : List Bool)
    (row : Fin m) (column : Fin n) (hrows : 0 < m) :
    gaussianPackedStateCheckCellWord
        (affineCellQuery row.val column.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide (state.system.check row column = (1 : ZMod 2))] := by
  let query := affineCellQuery
    row.val column.val
      (effectiveGaussianPackedStateWord state source)
  have hindex : gaussianPackedCellFlatIndexUnary query =
      List.replicate (row.val * n + column.val) true :=
    gaussianPackedCellFlatIndexUnary_query
      state source row.val column.val hrows
  have hbits : gaussianPackedCellCheckBits query =
      effectiveGaussianPackedCheckBits state :=
    gaussianPackedCellCheckBits_query
      state source row.val column.val
  have hread := fiveOriginalDynamicBitWord_valid
    gaussianPackedCellFlatIndexUnary gaussianPackedCellCheckBits
    query (row.val * n + column.val) hindex
  change gaussianPackedStateCheckCellWord query = _
  unfold gaussianPackedStateCheckCellWord
  rw [hread, hbits]
  have hlt :
      row.val * n + column.val <
        (effectiveGaussianPackedCheckBits state).length := by
    rw [effectiveGaussianPackedCheckBits_length]
    calc
      row.val * n + column.val < row.val * n + n :=
        Nat.add_lt_add_left column.isLt _
      _ = (row.val + 1) * n := by
        simp only [Nat.add_mul, one_mul]
      _ ≤ m * n :=
        Nat.mul_le_mul_right n
          (Nat.succ_le_of_lt row.isLt)
  rw [List.drop_eq_getElem_cons hlt]
  simp only [List.headD_cons]
  apply congrArg (fun bit : Bool => [bit])
  rw [← List.getD_eq_getElem
    (effectiveGaussianPackedCheckBits state) false hlt]
  exact gaussianDenseRowMajorBits_getD
    (fun current col =>
      decide (state.system.check current col = (1 : ZMod 2)))
    row column

theorem gaussianPackedStateRhsCellWord_query
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row : Fin m) (column : ℕ) :
    gaussianPackedStateRhsCellWord
        (affineCellQuery row.val column
          (effectiveGaussianPackedStateWord state source)) =
      [decide (state.system.rhs row = (1 : ZMod 2))] := by
  let query := affineCellQuery
    row.val column (effectiveGaussianPackedStateWord state source)
  have hindex : sourceExplicitAffineCellRow query =
      List.replicate row.val true :=
    sourceExplicitAffineCellRow_query
      row.val column (effectiveGaussianPackedStateWord state source)
  have hbits : gaussianPackedCellRhsBits query =
      effectiveGaussianPackedRhsBits state :=
    gaussianPackedCellRhsBits_query
      state source row.val column
  have hread := fiveOriginalDynamicBitWord_valid
    sourceExplicitAffineCellRow gaussianPackedCellRhsBits
    query row.val hindex
  change gaussianPackedStateRhsCellWord query = _
  unfold gaussianPackedStateRhsCellWord
  rw [hread, hbits]
  have hlt :
      row.val < (effectiveGaussianPackedRhsBits state).length := by
    simpa only [effectiveGaussianPackedRhsBits_length]
      using row.isLt
  rw [List.drop_eq_getElem_cons hlt]
  simp only [effectiveGaussianPackedRhsBits, List.getElem_map, List.getElem_finRange, Fin.cast_mk,
      Fin.eta,
      List.headD_eq_head?_getD, List.head?_cons, Option.getD_some]

private def gaussianPackedCellPivotCatalogue : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix ∘ firstFieldSuffix ∘
    firstFieldSuffix ∘ sourceExplicitAffineCellOriginalSource

private noncomputable def gaussianPackedCellPivotCatalogueComputable :
    BitTM
      gaussianPackedCellPivotCatalogue := by
  have hfirst := GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    firstFieldSuffixComputable
  have hsecond := GapCVP.TMComposition.computableInPolyTime
    hfirst firstFieldSuffixComputable
  have hthird := GapCVP.TMComposition.computableInPolyTime
    hsecond firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hthird firstFieldContentsComputable

private def gaussianPackedCellPivotSelectionInput
    (input : List Bool) : List Bool :=
  sourceExplicitAffineCellRow input ++
    false :: gaussianPackedCellPivotCatalogue input

private noncomputable def gaussianPackedCellPivotSelectionInputComputable :
    BitTM
      gaussianPackedCellPivotSelectionInput := by
  have htail := GapCVP.TMComposition.computableInPolyTime
    gaussianPackedCellPivotCatalogueComputable
    (SourceMachineCert.prependBitComputable false)
  have hphysical := pointwiseAppendComputable
    sourceExplicitAffineCellRowComputable htail
  change BitTM
    (fun input => sourceExplicitAffineCellRow input ++
      false :: gaussianPackedCellPivotCatalogue input)
  simpa only [Function.comp_apply] using hphysical

/-- GapCVP reduction support. -/
def gaussianPackedStatePivotCellWord : List Bool → List Bool :=
  binaryGaussianIndexedBatchOutput ∘
    gaussianPackedCellPivotSelectionInput

/-- GapCVP reduction support. -/
noncomputable def gaussianPackedStatePivotCellComputable :
    BitTM
      gaussianPackedStatePivotCellWord :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedCellPivotSelectionInputComputable
    binaryGaussianIndexedBatchComputable

@[simp] private theorem gaussianPackedCellPivotCatalogue_query
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row column : ℕ) :
    gaussianPackedCellPivotCatalogue
        (affineCellQuery row column
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianPackedPivotCatalogue state := by
  unfold gaussianPackedCellPivotCatalogue
    effectiveGaussianPackedStateWord
  simp only [List.append_assoc, Function.comp_apply, sourceExplicitAffineCellOriginalSource_query,
      firstFieldSuffix_valid, firstFieldContents_valid]

theorem gaussianPackedStatePivotCellWord_query
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : Fin n) :
    gaussianPackedStatePivotCellWord
        (affineCellQuery column.val 0
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianStatePivotWord state column := by
  let trace :=
    (List.finRange n).map
      (effectiveGaussianStatePivotWord state)
  have hindex : column.val < trace.length := by
    simpa only [trace, List.length_map, List.length_finRange]
      using column.isLt
  unfold gaussianPackedStatePivotCellWord
    gaussianPackedCellPivotSelectionInput
  simp only [Function.comp_apply,
    sourceExplicitAffineCellRow_query,
    gaussianPackedCellPivotCatalogue_query]
  change
    binaryGaussianIndexedBatchOutput
        (unaryBoundedFoldWord column.val
          (binaryGaussianPivotBatchStream trace)) =
      effectiveGaussianStatePivotWord state column
  have hread := binaryGaussianIndexedBatchOutput_valid
    trace [] column.val hindex
  simpa [trace] using hread

end GaussianAdaptivePackedStateLookupTM

namespace GaussianPackedStateBasisAtomTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.BinaryExplicitAffineRows GapCVP.GaussianRowWorker
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePackedStateLookupTM GapCVP.GaussianPackedStateTargetAtomTM
open GapCVP.GaussianPhysicalWordReducedAtomTM GapCVP.Factor400BinaryEffectiveBasisSerializerTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM

/-- GapCVP reduction support. -/
def gaussianPackedIndexedBasisStateWord
    (row column : ℕ) (state : List Bool) : List Bool :=
  affineCellQuery row column state

private def gaussianPackedBasisRowPivotQuery (input : List Bool) : List Bool :=
  lengthPrefixedWord (sourceExplicitAffineCellRow input) ++
    sourceExplicitAffineCellOriginalSource input

private noncomputable def gaussianPackedBasisRowPivotQueryComputable :
    BitTM
      gaussianPackedBasisRowPivotQuery := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellRowComputable structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable
    hprefix sourceExplicitAffineCellOriginalSourceComputable
  change BitTM
    (fun input => lengthPrefixedWord
      (sourceExplicitAffineCellRow input) ++
      sourceExplicitAffineCellOriginalSource input)
  simpa only [Function.comp_apply] using hphysical

private def gaussianPackedBasisColumnPivotQuery (input : List Bool) : List Bool :=
  lengthPrefixedWord (sourceExplicitAffineCellColumn input) ++
    sourceExplicitAffineCellOriginalSource input

private noncomputable def gaussianPackedBasisColumnPivotQueryComputable :
    BitTM
      gaussianPackedBasisColumnPivotQuery := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellColumnComputable structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable
    hprefix sourceExplicitAffineCellOriginalSourceComputable
  change BitTM
    (fun input => lengthPrefixedWord
      (sourceExplicitAffineCellColumn input) ++
      sourceExplicitAffineCellOriginalSource input)
  simpa only [Function.comp_apply] using hphysical

@[simp] private theorem gaussianPackedBasisRowPivotQuery_query
    (row column : ℕ) (state : List Bool) :
    gaussianPackedBasisRowPivotQuery
        (affineCellQuery row column state) =
      gaussianPackedIndexedStateWord row state := by
  simp only [gaussianPackedBasisRowPivotQuery, sourceExplicitAffineCellRow_query,
      sourceExplicitAffineCellOriginalSource_query, gaussianPackedIndexedStateWord]

@[simp] private theorem gaussianPackedBasisColumnPivotQuery_query
    (row column : ℕ) (state : List Bool) :
    gaussianPackedBasisColumnPivotQuery
        (affineCellQuery row column state) =
      gaussianPackedIndexedStateWord column state := by
  simp only [gaussianPackedBasisColumnPivotQuery, sourceExplicitAffineCellColumn_query,
      sourceExplicitAffineCellOriginalSource_query, gaussianPackedIndexedStateWord]

private def gaussianPackedBasisRowPivotWord : List Bool → List Bool :=
  gaussianPackedIndexedPivotOutput ∘ gaussianPackedBasisRowPivotQuery

private noncomputable def gaussianPackedBasisRowPivotComputable :
    BitTM
      gaussianPackedBasisRowPivotWord :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedBasisRowPivotQueryComputable
    gaussianPackedIndexedPivotComputable

private def gaussianPackedBasisColumnPivotWord : List Bool → List Bool :=
  gaussianPackedIndexedPivotOutput ∘ gaussianPackedBasisColumnPivotQuery

private noncomputable def gaussianPackedBasisColumnPivotComputable :
    BitTM
      gaussianPackedBasisColumnPivotWord :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedBasisColumnPivotQueryComputable
    gaussianPackedIndexedPivotComputable

private def gaussianPackedBasisRowPresentWord : List Bool → List Bool :=
  binaryGaussianFirstCellWord ∘ gaussianPackedBasisRowPivotWord

private noncomputable def gaussianPackedBasisRowPresentComputable :
    BitTM
      gaussianPackedBasisRowPresentWord :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedBasisRowPivotComputable binaryGaussianFirstCellComputable

private def gaussianPackedBasisColumnPresentWord : List Bool → List Bool :=
  binaryGaussianFirstCellWord ∘ gaussianPackedBasisColumnPivotWord

private noncomputable def gaussianPackedBasisColumnPresentComputable :
    BitTM
      gaussianPackedBasisColumnPresentWord :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedBasisColumnPivotComputable binaryGaussianFirstCellComputable

private def gaussianPackedBasisPivotRowUnary : List Bool → List Bool :=
  List.tail ∘ gaussianPackedBasisRowPivotWord

private noncomputable def gaussianPackedBasisPivotRowUnaryComputable :
    BitTM
      gaussianPackedBasisPivotRowUnary :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedBasisRowPivotComputable
    dropHeadComputable

private def gaussianPackedBasisDiagonalWord : List Bool → List Bool :=
  fourFamilyComputedUnaryEqBitOutput
    sourceExplicitAffineCellRow sourceExplicitAffineCellColumn

private noncomputable def gaussianPackedBasisDiagonalComputable :
    BitTM
      gaussianPackedBasisDiagonalWord :=
  fourFamilyComputedUnaryEqBitComputable
    sourceExplicitAffineCellRowComputable
    sourceExplicitAffineCellColumnComputable

private def gaussianPackedBasisCoefficientQuery
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (gaussianPackedBasisPivotRowUnary input) ++
    (lengthPrefixedWord (sourceExplicitAffineCellColumn input) ++
      sourceExplicitAffineCellOriginalSource input)

private noncomputable def gaussianPackedBasisCoefficientQueryComputable :
    BitTM
      gaussianPackedBasisCoefficientQuery := by
  have hrow := GapCVP.TMComposition.computableInPolyTime
    gaussianPackedBasisPivotRowUnaryComputable
    structuralPrefixWriterComputable
  have hcolumn := GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellColumnComputable
    structuralPrefixWriterComputable
  have htail := pointwiseAppendComputable
    hcolumn sourceExplicitAffineCellOriginalSourceComputable
  have hphysical := pointwiseAppendComputable hrow htail
  change BitTM
    (fun input =>
      lengthPrefixedWord (gaussianPackedBasisPivotRowUnary input) ++
        (lengthPrefixedWord (sourceExplicitAffineCellColumn input) ++
          sourceExplicitAffineCellOriginalSource input))
  simpa only [Function.comp_apply] using hphysical

private def gaussianPackedBasisCoefficientWord : List Bool → List Bool :=
  gaussianPackedStateCheckCellWord ∘ gaussianPackedBasisCoefficientQuery

private noncomputable def gaussianPackedBasisCoefficientComputable :
    BitTM
      gaussianPackedBasisCoefficientWord :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedBasisCoefficientQueryComputable
    gaussianPackedStateCheckCellComputable

private def gaussianPackedBasisBothPivotWord : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    gaussianPackedBasisRowPresentWord
    gaussianPackedBasisColumnPresentWord

private noncomputable def gaussianPackedBasisBothPivotComputable :
    BitTM
      gaussianPackedBasisBothPivotWord :=
  fourFamilyBooleanAndComputable
    gaussianPackedBasisRowPresentComputable
    gaussianPackedBasisColumnPresentComputable

private def gaussianPackedBasisRowFreeWord : List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput gaussianPackedBasisRowPresentWord

private noncomputable def gaussianPackedBasisRowFreeComputable :
    BitTM
      gaussianPackedBasisRowFreeWord :=
  fourFamilyBooleanNotOutputComputable
    gaussianPackedBasisRowPresentComputable

private def gaussianPackedBasisColumnFreeWord : List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput gaussianPackedBasisColumnPresentWord

private noncomputable def gaussianPackedBasisColumnFreeComputable :
    BitTM
      gaussianPackedBasisColumnFreeWord :=
  fourFamilyBooleanNotOutputComputable
    gaussianPackedBasisColumnPresentComputable

private def gaussianPackedBasisBothFreeWord : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    gaussianPackedBasisRowFreeWord gaussianPackedBasisColumnFreeWord

private noncomputable def gaussianPackedBasisBothFreeComputable :
    BitTM
      gaussianPackedBasisBothFreeWord :=
  fourFamilyBooleanAndComputable
    gaussianPackedBasisRowFreeComputable
    gaussianPackedBasisColumnFreeComputable

private def gaussianPackedBasisMatchingKindWord : List Bool → List Bool :=
  sourceFourFamilyBooleanOrOutput
    gaussianPackedBasisBothPivotWord gaussianPackedBasisBothFreeWord

private noncomputable def gaussianPackedBasisMatchingKindComputable :
    BitTM
      gaussianPackedBasisMatchingKindWord :=
  sourceFourFamilyBooleanOrComputable
    gaussianPackedBasisBothPivotComputable
    gaussianPackedBasisBothFreeComputable

private def gaussianPackedBasisDiagonalNonzeroWord : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    gaussianPackedBasisDiagonalWord gaussianPackedBasisMatchingKindWord

private noncomputable def gaussianPackedBasisDiagonalNonzeroComputable :
    BitTM
      gaussianPackedBasisDiagonalNonzeroWord :=
  fourFamilyBooleanAndComputable
    gaussianPackedBasisDiagonalComputable
    gaussianPackedBasisMatchingKindComputable

private def gaussianPackedBasisPivotFreeCoefficientWord : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput gaussianPackedBasisRowPresentWord
    (sourceFourFamilyBooleanAndOutput
      gaussianPackedBasisColumnFreeWord gaussianPackedBasisCoefficientWord)

private noncomputable def gaussianPackedBasisPivotFreeCoefficientComputable :
    BitTM
      gaussianPackedBasisPivotFreeCoefficientWord :=
  fourFamilyBooleanAndComputable
    gaussianPackedBasisRowPresentComputable
    (fourFamilyBooleanAndComputable
      gaussianPackedBasisColumnFreeComputable
      gaussianPackedBasisCoefficientComputable)

private def gaussianPackedBasisFirstBit : List Bool → List Bool :=
  sourceFourFamilyBooleanOrOutput
    gaussianPackedBasisDiagonalNonzeroWord
    gaussianPackedBasisPivotFreeCoefficientWord

private noncomputable def gaussianPackedBasisFirstBitComputable :
    BitTM
      gaussianPackedBasisFirstBit :=
  sourceFourFamilyBooleanOrComputable
    gaussianPackedBasisDiagonalNonzeroComputable
    gaussianPackedBasisPivotFreeCoefficientComputable

private def gaussianPackedBasisSecondBit : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    gaussianPackedBasisBothPivotWord gaussianPackedBasisDiagonalWord

private noncomputable def gaussianPackedBasisSecondBitComputable :
    BitTM
      gaussianPackedBasisSecondBit :=
  fourFamilyBooleanAndComputable
    gaussianPackedBasisBothPivotComputable
    gaussianPackedBasisDiagonalComputable

/-- GapCVP reduction support. -/
def gaussianPackedIndexedBasisTag
    (input : List Bool) : List Bool :=
  gaussianPackedBasisFirstBit input ++ gaussianPackedBasisSecondBit input

/-- GapCVP reduction support. -/
noncomputable def gaussianPackedIndexedBasisTagComputable :
    BitTM
      gaussianPackedIndexedBasisTag :=
  pointwiseAppendComputable
    gaussianPackedBasisFirstBitComputable
    gaussianPackedBasisSecondBitComputable

/-- GapCVP reduction support. -/
def gaussianPackedIndexedBasisAtom : List Bool → List Bool :=
  effectiveBasisPackedAtom ∘ gaussianPackedIndexedBasisTag

/-- GapCVP reduction support. -/
noncomputable def gaussianPackedIndexedBasisAtomComputable :
    BitTM
      gaussianPackedIndexedBasisAtom :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPackedIndexedBasisTagComputable
    effectiveBasisPackedAtomComputable

private theorem gaussianPackedBasisCoefficientWord_singleton
    (input : List Bool) :
    gaussianPackedBasisCoefficientWord input =
      [(gaussianPackedBasisCoefficientWord input).headD false] := by
  unfold gaussianPackedBasisCoefficientWord
  simp only [Function.comp_apply]
  unfold gaussianPackedStateCheckCellWord
    fiveFamilyOriginalDynamicBitWord
  rw [fiveFamilyOriginalHeadBitWord_eq]
  simp only [List.headD_cons]

private theorem gaussianPackedBasisRowPivotWord_query
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row column : Fin n) :
    gaussianPackedBasisRowPivotWord
        (affineCellQuery row.val column.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianStatePivotWord state row := by
  unfold gaussianPackedBasisRowPivotWord
  rw [Function.comp_apply, gaussianPackedBasisRowPivotQuery_query]
  exact gaussianPackedIndexedPivotOutput_word state row source

private theorem gaussianPackedBasisColumnPivotWord_query
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row column : Fin n) :
    gaussianPackedBasisColumnPivotWord
        (affineCellQuery row.val column.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianStatePivotWord state column := by
  unfold gaussianPackedBasisColumnPivotWord
  rw [Function.comp_apply, gaussianPackedBasisColumnPivotQuery_query]
  exact gaussianPackedIndexedPivotOutput_word state column source

private theorem gaussianPackedBasisRowPresentWord_query
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row column : Fin n) :
    gaussianPackedBasisRowPresentWord
        (affineCellQuery row.val column.val
          (effectiveGaussianPackedStateWord state source)) =
      [(effectiveGaussianStatePivotRowOption state row).isSome] := by
  unfold gaussianPackedBasisRowPresentWord
  rw [Function.comp_apply,
    gaussianPackedBasisRowPivotWord_query state source row column]
  cases hpivot : effectiveGaussianStatePivotRowOption state row <;>
    simp [effectiveGaussianStatePivotWord, hpivot]

private theorem gaussianPackedBasisColumnPresentWord_query
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row column : Fin n) :
    gaussianPackedBasisColumnPresentWord
        (affineCellQuery row.val column.val
          (effectiveGaussianPackedStateWord state source)) =
      [(effectiveGaussianStatePivotRowOption state column).isSome] := by
  unfold gaussianPackedBasisColumnPresentWord
  rw [Function.comp_apply,
    gaussianPackedBasisColumnPivotWord_query state source row column]
  cases hpivot : effectiveGaussianStatePivotRowOption state column <;>
    simp [effectiveGaussianStatePivotWord, hpivot]

private theorem gaussianPackedBasisDiagonalWord_query
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row column : Fin n) :
    gaussianPackedBasisDiagonalWord
        (affineCellQuery row.val column.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide (row.val = column.val)] := by
  exact fourFamilyComputedUnaryEqBitOutput_valid
    sourceExplicitAffineCellRow sourceExplicitAffineCellColumn
    (affineCellQuery row.val column.val
      (effectiveGaussianPackedStateWord state source))
    row.val column.val
    (sourceExplicitAffineCellRow_query row.val column.val
      (effectiveGaussianPackedStateWord state source))
    (sourceExplicitAffineCellColumn_query row.val column.val
      (effectiveGaussianPackedStateWord state source))

private theorem gaussianPackedBasisCoefficientWord_query_pivot
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row column : Fin n) (pivot : Fin m)
    (hpivot : effectiveGaussianStatePivotRowOption state row = some pivot) :
    gaussianPackedBasisCoefficientWord
        (affineCellQuery row.val column.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide (state.system.check pivot column = (1 : ZMod 2))] := by
  let input := affineCellQuery row.val column.val
    (effectiveGaussianPackedStateWord state source)
  have hrow : gaussianPackedBasisPivotRowUnary input =
      List.replicate pivot.val true := by
    unfold gaussianPackedBasisPivotRowUnary
    rw [Function.comp_apply,
      gaussianPackedBasisRowPivotWord_query state source row column]
    simp only [effectiveGaussianStatePivotWord, hpivot, List.tail_cons]
  have hquery : gaussianPackedBasisCoefficientQuery input =
      affineCellQuery pivot.val column.val
        (effectiveGaussianPackedStateWord state source) := by
    unfold gaussianPackedBasisCoefficientQuery
      affineCellQuery
    rw [hrow, sourceExplicitAffineCellColumn_query,
      sourceExplicitAffineCellOriginalSource_query]
    simp only [List.append_assoc]
  have hrows : 0 < m := by
    have hlt := pivot.isLt
    omega
  unfold gaussianPackedBasisCoefficientWord
  rw [Function.comp_apply, hquery]
  exact gaussianPackedStateCheckCellWord_query
    state source pivot column hrows

private theorem gaussianPackedBasisFirstBit_bits
    (input : List Bool) (rowPivot columnPivot diagonal coefficient : Bool)
    (hrow : gaussianPackedBasisRowPresentWord input = [rowPivot])
    (hcolumn : gaussianPackedBasisColumnPresentWord input = [columnPivot])
    (hdiagonal : gaussianPackedBasisDiagonalWord input = [diagonal])
    (hcoefficient : gaussianPackedBasisCoefficientWord input = [coefficient]) :
    gaussianPackedBasisFirstBit input =
      [((diagonal &&
          ((rowPivot && columnPivot) ||
            ((!rowPivot) && (!columnPivot)))) ||
        (rowPivot && ((!columnPivot) && coefficient)))] := by
  have hboth := fourFamilyBooleanAndOutput_bits
    gaussianPackedBasisRowPresentWord gaussianPackedBasisColumnPresentWord
    input rowPivot columnPivot hrow hcolumn
  have hrowFree := fourFamilyBooleanNotOutput_bit
    gaussianPackedBasisRowPresentWord input rowPivot hrow
  have hcolumnFree := fourFamilyBooleanNotOutput_bit
    gaussianPackedBasisColumnPresentWord input columnPivot hcolumn
  have hfree := fourFamilyBooleanAndOutput_bits
    gaussianPackedBasisRowFreeWord gaussianPackedBasisColumnFreeWord
    input (!rowPivot) (!columnPivot) hrowFree hcolumnFree
  have hkind := fourFamilyBooleanOrOutput_bits
    gaussianPackedBasisBothPivotWord gaussianPackedBasisBothFreeWord
    input (rowPivot && columnPivot)
      ((!rowPivot) && (!columnPivot)) hboth hfree
  have hnonzero := fourFamilyBooleanAndOutput_bits
    gaussianPackedBasisDiagonalWord gaussianPackedBasisMatchingKindWord
    input diagonal
      ((rowPivot && columnPivot) ||
        ((!rowPivot) && (!columnPivot))) hdiagonal hkind
  have hcolumnCoefficient := fourFamilyBooleanAndOutput_bits
    gaussianPackedBasisColumnFreeWord gaussianPackedBasisCoefficientWord
    input (!columnPivot) coefficient hcolumnFree hcoefficient
  have hpivotCoefficient := fourFamilyBooleanAndOutput_bits
    gaussianPackedBasisRowPresentWord
    (sourceFourFamilyBooleanAndOutput
      gaussianPackedBasisColumnFreeWord gaussianPackedBasisCoefficientWord)
    input rowPivot ((!columnPivot) && coefficient)
    hrow hcolumnCoefficient
  exact fourFamilyBooleanOrOutput_bits
    gaussianPackedBasisDiagonalNonzeroWord
    gaussianPackedBasisPivotFreeCoefficientWord input
    (diagonal &&
      ((rowPivot && columnPivot) ||
        ((!rowPivot) && (!columnPivot))))
    (rowPivot && ((!columnPivot) && coefficient))
    hnonzero hpivotCoefficient

private theorem gaussianPackedBasisSecondBit_bits
    (input : List Bool) (rowPivot columnPivot diagonal : Bool)
    (hrow : gaussianPackedBasisRowPresentWord input = [rowPivot])
    (hcolumn : gaussianPackedBasisColumnPresentWord input = [columnPivot])
    (hdiagonal : gaussianPackedBasisDiagonalWord input = [diagonal]) :
    gaussianPackedBasisSecondBit input =
      [(rowPivot && columnPivot) && diagonal] := by
  have hboth := fourFamilyBooleanAndOutput_bits
    gaussianPackedBasisRowPresentWord gaussianPackedBasisColumnPresentWord
    input rowPivot columnPivot hrow hcolumn
  exact fourFamilyBooleanAndOutput_bits
    gaussianPackedBasisBothPivotWord gaussianPackedBasisDiagonalWord
    input (rowPivot && columnPivot) diagonal hboth hdiagonal

theorem gaussianPackedIndexedBasisTag_state
    {m n : ℕ} (state : State m n)
    (row column : Fin n) (source : List Bool) :
    gaussianPackedIndexedBasisTag
        (gaussianPackedIndexedBasisStateWord row.val column.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianStateBasisTag state row column := by
  let input := affineCellQuery row.val column.val
    (effectiveGaussianPackedStateWord state source)
  change gaussianPackedBasisFirstBit input ++
    gaussianPackedBasisSecondBit input =
      effectiveGaussianStateBasisTag state row column
  have hrow := gaussianPackedBasisRowPresentWord_query
    state source row column
  have hcolumn := gaussianPackedBasisColumnPresentWord_query
    state source row column
  have hdiagonal := gaussianPackedBasisDiagonalWord_query
    state source row column
  have harbitrary := gaussianPackedBasisCoefficientWord_singleton input
  cases hpivotRow : effectiveGaussianStatePivotRowOption state row with
  | none =>
      cases hpivotColumn : effectiveGaussianStatePivotRowOption state column with
      | none =>
          have hfirst := gaussianPackedBasisFirstBit_bits input
            false false (decide (row.val = column.val))
            ((gaussianPackedBasisCoefficientWord input).headD false)
            (by simpa only [hpivotRow, Option.isSome_none, input] using hrow)
            (by simpa only [hpivotColumn, Option.isSome_none, input] using hcolumn)
            (by simpa only [input] using hdiagonal) harbitrary
          have hsecond := gaussianPackedBasisSecondBit_bits input
            false false (decide (row.val = column.val))
            (by simpa only [hpivotRow, Option.isSome_none, input] using hrow)
            (by simpa only [hpivotColumn, Option.isSome_none, input] using hcolumn)
            (by simpa only [input] using hdiagonal)
          rw [hfirst, hsecond]
          unfold effectiveGaussianStateBasisTag
          rw [hpivotRow, hpivotColumn]
          by_cases hval : row.val = column.val
          · have heq : row = column := Fin.ext hval
            simp only [heq, decide_true, Bool.and_self, Bool.not_false, Bool.or_true,
                List.headD_eq_head?_getD,
                Bool.true_and, Bool.false_and, Bool.or_false, Bool.and_true, List.cons_append,
                    List.nil_append, ↓reduceIte]
          · have heq : row ≠ column := by
              intro h
              exact hval (congrArg Fin.val h)
            simp only [hval, decide_false, Bool.and_self, Bool.not_false, Bool.or_true,
                Bool.and_true,
                List.headD_eq_head?_getD, Bool.true_and, Bool.false_and, Bool.or_self,
                    List.cons_append, List.nil_append, heq,
                ↓reduceIte]
      | some pivot =>
          have hfirst := gaussianPackedBasisFirstBit_bits input
            false true (decide (row.val = column.val))
            ((gaussianPackedBasisCoefficientWord input).headD false)
            (by simpa only [hpivotRow, Option.isSome_none, input] using hrow)
            (by simpa only [hpivotColumn, Option.isSome_some, input] using hcolumn)
            (by simpa only [input] using hdiagonal) harbitrary
          have hsecond := gaussianPackedBasisSecondBit_bits input
            false true (decide (row.val = column.val))
            (by simpa only [hpivotRow, Option.isSome_none, input] using hrow)
            (by simpa only [hpivotColumn, Option.isSome_some, input] using hcolumn)
            (by simpa only [input] using hdiagonal)
          rw [hfirst, hsecond]
          unfold effectiveGaussianStateBasisTag
          rw [hpivotRow, hpivotColumn]
          simp only [Bool.and_true, Bool.not_false, Bool.not_true, Bool.and_false, Bool.or_self,
              List.headD_eq_head?_getD, Bool.false_and, Bool.and_self, List.cons_append,
                  List.nil_append]
  | some pivot =>
      cases hpivotColumn : effectiveGaussianStatePivotRowOption state column with
      | none =>
          have hcoefficient :=
            gaussianPackedBasisCoefficientWord_query_pivot
              state source row column pivot hpivotRow
          have hfirst := gaussianPackedBasisFirstBit_bits input
            true false (decide (row.val = column.val))
            (decide (state.system.check pivot column = (1 : ZMod 2)))
            (by simpa only [hpivotRow, Option.isSome_some, input] using hrow)
            (by simpa only [hpivotColumn, Option.isSome_none, input] using hcolumn)
            (by simpa only [input] using hdiagonal)
            (by simpa only [input] using hcoefficient)
          have hsecond := gaussianPackedBasisSecondBit_bits input
            true false (decide (row.val = column.val))
            (by simpa only [hpivotRow, Option.isSome_some, input] using hrow)
            (by simpa only [hpivotColumn, Option.isSome_none, input] using hcolumn)
            (by simpa only [input] using hdiagonal)
          rw [hfirst, hsecond]
          unfold effectiveGaussianStateBasisTag
          rw [hpivotRow, hpivotColumn]
          simp only [Bool.and_false, Bool.not_true, Bool.not_false, Bool.and_true, Bool.or_self,
              Bool.true_and,
              Bool.false_or, Bool.false_and, List.cons_append, List.nil_append]
      | some other =>
          have hfirst := gaussianPackedBasisFirstBit_bits input
            true true (decide (row.val = column.val))
            ((gaussianPackedBasisCoefficientWord input).headD false)
            (by simpa only [hpivotRow, Option.isSome_some, input] using hrow)
            (by simpa only [hpivotColumn, Option.isSome_some, input] using hcolumn)
            (by simpa only [input] using hdiagonal) harbitrary
          have hsecond := gaussianPackedBasisSecondBit_bits input
            true true (decide (row.val = column.val))
            (by simpa only [hpivotRow, Option.isSome_some, input] using hrow)
            (by simpa only [hpivotColumn, Option.isSome_some, input] using hcolumn)
            (by simpa only [input] using hdiagonal)
          rw [hfirst, hsecond]
          unfold effectiveGaussianStateBasisTag
          rw [hpivotRow, hpivotColumn]
          by_cases hval : row.val = column.val
          · have heq : row = column := Fin.ext hval
            simp only [heq, decide_true, Bool.and_self, Bool.not_true, Bool.or_false,
                List.headD_eq_head?_getD,
                Bool.false_and, Bool.and_false, List.cons_append, List.nil_append, ↓reduceIte]
          · have heq : row ≠ column := by
              intro h
              exact hval (congrArg Fin.val h)
            simp only [hval, decide_false, Bool.and_self, Bool.not_true, Bool.or_false,
                Bool.and_true,
                List.headD_eq_head?_getD, Bool.false_and, Bool.and_false, Bool.or_self,
                    List.cons_append, List.nil_append, heq,
                ↓reduceIte]

theorem gaussianPackedIndexedBasisAtom_effective
    (system : BinaryAffineSystem)
    (row column : Fin system.dimension) (source : List Bool) :
    gaussianPackedIndexedBasisAtom
        (gaussianPackedIndexedBasisStateWord row.val column.val
          (effectiveGaussianPackedStateWord
            system.effectiveGaussianState source)) =
      encodeAtomic (system.effectiveSquareBasisMatrix row column) := by
  unfold gaussianPackedIndexedBasisAtom
  rw [Function.comp_apply,
    gaussianPackedIndexedBasisTag_state]
  exact effectiveGaussianStateBasisTag_effective_atom
    system row column

end GaussianPackedStateBasisAtomTM

namespace Factor400FinitePNormCorollary

open scoped BigOperators ENNReal

/-- GapCVP reduction support. -/
def finitePNorm (p : ℚ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, |x i| ^ (p : ℝ)) ^ ((p : ℝ)⁻¹)

theorem finitePNorm_nonneg (p : ℚ) {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ finitePNorm p x := by
  unfold finitePNorm
  exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ =>
    Real.rpow_nonneg (abs_nonneg _) _) _

theorem finitePNorm_rpow (p : ℚ) (hp : 0 < p)
    {n : ℕ} (x : Fin n → ℝ) :
    finitePNorm p x ^ (p : ℝ) =
      ∑ i : Fin n, |x i| ^ (p : ℝ) := by
  have hp_real : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  unfold finitePNorm
  exact Real.rpow_inv_rpow
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)
    hp_real.ne'

/-- GapCVP reduction support. -/
def finitePLatticeDiscrepancy (I : GapCVPInstance)
    (z : Fin I.dimension → ℤ) : Fin I.dimension → ℝ := fun i =>
  (I.target i : ℝ) -
    ∑ j : Fin I.dimension, (I.basis i j : ℝ) * (z j : ℝ)

/-- GapCVP reduction support. -/
def finitePLatticeDistance (p : ℚ) (I : GapCVPInstance)
    (z : Fin I.dimension → ℤ) : ℝ :=
  finitePNorm p (finitePLatticeDiscrepancy I z)

/-- GapCVP reduction support. -/
def finitePGapFactor (p : ℚ) (I : GapCVPInstance) : ℝ :=
  (I.dimension : ℝ) ^ (((200 : ℝ) * (p : ℝ))⁻¹)

private theorem finitePGapFactor_one_le (p : ℚ) (hp : 1 ≤ p)
    {I : GapCVPInstance} (hdimension : 0 < I.dimension) :
    1 ≤ finitePGapFactor p I := by
  unfold finitePGapFactor
  apply Real.one_le_rpow
  · exact_mod_cast hdimension
  · have hp_real : (0 : ℝ) < (p : ℝ) := by
      have : (0 : ℚ) < p := lt_of_lt_of_le (by norm_num) hp
      exact_mod_cast this
    exact inv_nonneg.mpr (mul_nonneg (by norm_num) hp_real.le)

/-- GapCVP reduction support. -/
def finitePRadiusScale (p : ℚ) : ℕ :=
  Nat.ceil (4 * p)

theorem finitePRadiusScale_pos (p : ℚ) (hp : 1 ≤ p) :
    0 < finitePRadiusScale p := by
  apply Nat.ceil_pos.mpr
  have hp_pos : (0 : ℚ) < p := lt_of_lt_of_le (by norm_num) hp
  exact mul_pos (by norm_num) hp_pos

private def finitePCeilingRoot (a value : ℕ) : ℕ :=
  let root := Nat.nthRoot a value
  if root ^ a = value then root else root + 1

/-- GapCVP reduction support. -/
def finitePRadiusNumerator (p : ℚ) (R : ℕ) : ℕ :=
  finitePCeilingRoot p.num.natAbs
    (finitePRadiusScale p ^ p.num.natAbs * R ^ p.den)

/-- GapCVP reduction support. -/
def finitePRadius (p : ℚ) (R : ℕ) : ℚ :=
  (finitePRadiusNumerator p R : ℚ) / (finitePRadiusScale p : ℚ)

/-- GapCVP reduction support. -/
def finitePSignedBinarySupport {n : ℕ} (z : Fin n → ℤ) : Finset (Fin n) :=
  Finset.univ.filter fun i => (z i : ZMod 2) ≠ 0

theorem finitePSignedBinarySupport_card_le_power_sum
    (p : ℚ) (hp : 1 ≤ p) {n : ℕ} (z : Fin n → ℤ) :
    ((finitePSignedBinarySupport z).card : ℝ) ≤
      ∑ i : Fin n, |(z i : ℝ)| ^ (p : ℝ) := by
  have hp_real : (0 : ℝ) ≤ (p : ℝ) := by
    have : (0 : ℚ) ≤ p := le_trans (by norm_num) hp
    exact_mod_cast this
  calc
    ((finitePSignedBinarySupport z).card : ℝ) =
        ∑ _i ∈ finitePSignedBinarySupport z, (1 : ℝ) := by simp only [Finset.sum_const,
            nsmul_eq_mul, mul_one]
    _ ≤ ∑ i ∈ finitePSignedBinarySupport z,
          |(z i : ℝ)| ^ (p : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hparity : (z i : ZMod 2) ≠ 0 :=
        (Finset.mem_filter.mp hi).2
      have hne : z i ≠ 0 := by
        intro hzero
        apply hparity
        simp only [hzero, Int.cast_zero]
      have hone : (1 : ℝ) ≤ |(z i : ℝ)| := by
        exact_mod_cast Int.one_le_abs hne
      exact Real.one_le_rpow hone hp_real
    _ ≤ ∑ i : Fin n, |(z i : ℝ)| ^ (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro i _ _
        exact Real.rpow_nonneg (abs_nonneg _) _

/-- GapCVP reduction support. -/
def finitePGapCVPPromise (p : ℚ) (hp : 1 ≤ p) : PromiseProblem where
  yes bits :=
    @decide (
 ∃ I : GapCVPInstance,
    (binaryFinEncoding GapCVPInstance).encode I = bits ∧
      gapCVPWellFormed I ∧
      ∃ z : Fin I.dimension → ℤ,
        finitePLatticeDistance p I z ≤ (I.radius : ℝ)
    ) (Classical.propDecidable _)
  no bits :=
    @decide (
 ∃ I : GapCVPInstance,
    (binaryFinEncoding GapCVPInstance).encode I = bits ∧
      gapCVPWellFormed I ∧
      ∀ z : Fin I.dimension → ℤ,
        finitePGapFactor p I * (I.radius : ℝ) <
          finitePLatticeDistance p I z
    ) (Classical.propDecidable _)
  disjoint bits hyes hno := by
    simp only [decide_eq_true_eq] at hyes hno
    obtain ⟨I, hI, hwell, z, hz⟩ := hyes
    have well := hwell
    simp only [GapCVP.gapCVPWellFormed, decide_eq_true_eq] at well
    obtain ⟨J, hJ, _, hfar⟩ := hno
    have heq : I = J :=
      (binaryFinEncoding GapCVPInstance).encode_injective
        (hI.trans hJ.symm)
    subst J
    have hfactor := finitePGapFactor_one_le p hp well.1
    have hradius : 0 < (I.radius : ℝ) := by
      exact_mod_cast well.2.2
    have hscaled :
        (I.radius : ℝ) ≤ finitePGapFactor p I * (I.radius : ℝ) := by
      nlinarith
    exact (not_le_of_gt (hfar z)) (hz.trans hscaled)

end Factor400FinitePNormCorollary

namespace Factor400FinitePRadiusArithmetic

open GapCVP.Factor400FinitePNormCorollary

theorem finitePExponent_num_pos (p : ℚ) (hp : 1 ≤ p) :
    0 < p.num.natAbs := by
  have hp' : 0 < p := lt_of_lt_of_le (by norm_num) hp
  exact Int.natAbs_pos.mpr (Rat.num_pos.mpr hp').ne'

theorem finitePExponent_cast (p : ℚ) (hp : 1 ≤ p) :
    (p : ℝ) = (p.num.natAbs : ℝ) / (p.den : ℝ) := by
  rw [Rat.cast_def]
  have hp' : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hnum : 0 ≤ p.num := (Rat.num_pos.mpr hp').le
  have habs : (p.num.natAbs : ℤ) = p.num :=
    Int.natAbs_of_nonneg hnum
  congr 1
  simpa only [Int.cast_natCast] using
    congrArg (fun value : ℤ => (value : ℝ)) habs.symm

theorem four_mul_le_finitePRadiusScale (p : ℚ) :
    4 * (p : ℝ) ≤ (finitePRadiusScale p : ℝ) := by
  have hceil : 4 * p ≤ (finitePRadiusScale p : ℚ) := by
    exact Nat.le_ceil (4 * p)
  exact_mod_cast hceil

private theorem finitePCeilingRoot_spec (a value : ℕ) (ha : 0 < a) :
    value ≤ finitePCeilingRoot a value ^ a := by
  simp only [finitePCeilingRoot]
  split_ifs with hexact
  · exact hexact.symm.le
  · exact (Nat.lt_pow_nthRoot_add_one ha.ne' value).le

private theorem finitePCeilingRoot_minimal
    (a value candidate : ℕ) (ha : 0 < a)
    (hcandidate : value ≤ candidate ^ a) :
    finitePCeilingRoot a value ≤ candidate := by
  simp only [finitePCeilingRoot]
  split_ifs with hexact
  · apply (Nat.pow_left_strictMono ha.ne').le_iff_le.mp
    exact hexact.le.trans hcandidate
  · have hfloor : Nat.nthRoot a value ^ a ≤ value :=
      Nat.pow_nthRoot_le (Or.inl ha.ne')
    have hstrict : Nat.nthRoot a value ^ a < value :=
      lt_of_le_of_ne hfloor hexact
    have hroot : Nat.nthRoot a value < candidate :=
      (Nat.pow_left_strictMono ha.ne').lt_iff_lt.mp
        (hstrict.trans_le hcandidate)
    omega

theorem finitePCeilingRoot_le_nthRoot_add_one (a value : ℕ) :
    finitePCeilingRoot a value ≤ Nat.nthRoot a value + 1 := by
  simp only [finitePCeilingRoot]
  split_ifs <;> omega

theorem finitePRadiusNumerator_spec (p : ℚ) (hp : 1 ≤ p) (R : ℕ) :
    finitePRadiusScale p ^ p.num.natAbs * R ^ p.den ≤
      finitePRadiusNumerator p R ^ p.num.natAbs := by
  exact finitePCeilingRoot_spec p.num.natAbs
    (finitePRadiusScale p ^ p.num.natAbs * R ^ p.den)
    (finitePExponent_num_pos p hp)

private theorem finitePRadiusNumerator_pos
    (p : ℚ) (hp : 1 ≤ p) (R : ℕ) (hR : 0 < R) :
    0 < finitePRadiusNumerator p R := by
  have hscale := finitePRadiusScale_pos p hp
  have hvalue :
      0 < finitePRadiusScale p ^ p.num.natAbs * R ^ p.den :=
    Nat.mul_pos (pow_pos hscale _) (pow_pos hR _)
  have hpower : 0 < finitePRadiusNumerator p R ^ p.num.natAbs :=
    hvalue.trans_le (finitePRadiusNumerator_spec p hp R)
  exact Nat.pos_of_ne_zero fun hzero => by
    simp only [hzero, ne_eq, (finitePExponent_num_pos p hp).ne', not_false_eq_true, zero_pow,
        lt_self_iff_false] at hpower

theorem finitePRadius_pos
    (p : ℚ) (hp : 1 ≤ p) (R : ℕ) (hR : 0 < R) :
    0 < finitePRadius p R := by
  unfold finitePRadius
  exact div_pos (by exact_mod_cast finitePRadiusNumerator_pos p hp R hR)
    (by exact_mod_cast finitePRadiusScale_pos p hp)

theorem finitePRadius_cast (p : ℚ) (R : ℕ) :
    (finitePRadius p R : ℝ) =
      (finitePRadiusNumerator p R : ℝ) /
        (finitePRadiusScale p : ℝ) := by
  simp only [finitePRadius, Rat.cast_div, Rat.cast_natCast]

end Factor400FinitePRadiusArithmetic

namespace Factor400BinaryCodeDecodingCorollary

open scoped BigOperators

open GapCVP.Factor400BinaryConstructiveSourcePlaces

/-- GapCVP reduction support. -/
def binaryWordLift {n : ℕ} (word : Fin n → ZMod 2) : Fin n → ℤ :=
  fun index => ((word index).val : ℤ)

@[simp] theorem binaryResidue_binaryWordLift
    {n : ℕ} (word : Fin n → ZMod 2) :
    GapCVP.Core.binaryResidue (binaryWordLift word) = word := by
  funext index
  exact_mod_cast ZMod.natCast_zmod_val (word index)

/-- GapCVP reduction support. -/
noncomputable def sourceBinaryDecodingRadius
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula) : ℕ :=
  (formula.clauses.length + 1) *
    (sourceFormulaGrid encodingLength formula).card

theorem sourceBinaryDecodingRadius_pos
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula) :
    0 < sourceBinaryDecodingRadius encodingLength formula := by
  unfold sourceBinaryDecodingRadius
  exact Nat.mul_pos (Nat.zero_lt_succ formula.clauses.length)
    (sourceFormulaGrid_card_pos encodingLength formula)

private theorem sourceBinaryDecodingRadius_le_size_mul_field
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula) :
    sourceBinaryDecodingRadius encodingLength formula ≤
      GapCVP.Core.sourceSizeParameter encodingLength formula *
        Fintype.card (sourceFormulaField encodingLength formula) := by
  unfold sourceBinaryDecodingRadius
  have hclauses : formula.clauses.length + 1 ≤
      GapCVP.Core.sourceSizeParameter encodingLength formula := by
    simp only [GapCVP.Core.sourceSizeParameter]
    omega
  have hgrid :
      (sourceFormulaGrid encodingLength formula).card ≤
        Fintype.card (sourceFormulaField encodingLength formula) :=
    Finset.card_le_card (Finset.subset_univ _)
  exact Nat.mul_le_mul hclauses hgrid

/-- GapCVP reduction support. -/
noncomputable def binaryCodeGapFactor (blockLength : ℕ) : ℝ :=
  (blockLength : ℝ) ^ ((1 : ℝ) / 200)

private theorem binaryCodeGapFactor_eq_factor400_sq (blockLength : ℕ) :
    binaryCodeGapFactor blockLength =
      GapCVP.SourceFactor400BinaryConstructionABounds.gapFactor400
        blockLength ^ 2 := by
  exact
    (GapCVP.SourceFactor400BinaryConstructionABounds.gapFactor400_sq
      blockLength).symm

theorem sourceBinaryDecoding_scaledNorm_support
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (vector : Fin (sourceFormulaDimension encodingLength formula) → ℤ)
    (hshort : (GapCVP.Core.integerSquaredNorm vector : ℝ) ≤
      2 * binaryCodeGapFactor
          (sourceFormulaDimension encodingLength formula) *
        (sourceBinaryDecodingRadius encodingLength formula : ℝ)) :
    10 * GapCVP.Core.integerSquaredNorm vector ≤
      Fintype.card (sourceFormulaField encodingLength formula) *
        GapCVP.Core.sourceSizeParameter encodingLength formula ^ 4 := by
  let N := GapCVP.Core.sourceSizeParameter encodingLength formula
  let q := Fintype.card (sourceFormulaField encodingLength formula)
  let factor := binaryCodeGapFactor
    (sourceFormulaDimension encodingLength formula)
  have hq : 0 < q := by
    dsimp [q]
    exact Fintype.card_pos_iff.mpr ⟨0⟩
  have hqreal : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq
  have hfactor : 0 ≤ factor := by
    dsimp [factor, binaryCodeGapFactor]
    positivity
  have hweight :
      (sourceBinaryDecodingRadius encodingLength formula : ℝ) ≤
        (N : ℝ) * (q : ℝ) := by
    exact_mod_cast
      sourceBinaryDecodingRadius_le_size_mul_field encodingLength formula
  have hmargin : (80 : ℝ) * factor * (N : ℝ) < (N : ℝ) ^ 4 := by
    simpa [N, factor, binaryCodeGapFactor_eq_factor400_sq] using
      sourceFormula_gapFactor400_eighty_mul_size_lt_fourth_power
        encodingLength formula
  have hmarginSmall : (20 : ℝ) * factor * (N : ℝ) <
      (N : ℝ) ^ 4 := by
    have hN : (0 : ℝ) ≤ (N : ℝ) := by positivity
    linarith [mul_nonneg hfactor hN]
  have hstrict :
      ((10 * GapCVP.Core.integerSquaredNorm vector : ℕ) : ℝ) <
        ((q * N ^ 4 : ℕ) : ℝ) := by
    calc
      ((10 * GapCVP.Core.integerSquaredNorm vector : ℕ) : ℝ) =
          10 * (GapCVP.Core.integerSquaredNorm vector : ℝ) := by
            push_cast
            ring
      _ ≤ 10 * (2 * factor *
            (sourceBinaryDecodingRadius encodingLength formula : ℝ)) := by
            gcongr
      _ ≤ 10 * (2 * factor * ((N : ℝ) * (q : ℝ))) := by
            gcongr
      _ = (20 * factor * (N : ℝ)) * (q : ℝ) := by ring
      _ < (N : ℝ) ^ 4 * (q : ℝ) :=
        mul_lt_mul_of_pos_right hmarginSmall hqreal
      _ = ((q * N ^ 4 : ℕ) : ℝ) := by
        push_cast
        ring
  exact Nat.le_of_lt (by exact_mod_cast hstrict)

end Factor400BinaryCodeDecodingCorollary

namespace Factor400FinitePRadiusSourceTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceAnchoredGridRecordFoldTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryRadiusTM
open GapCVP.Factor400FinitePNormCorollary GapCVP.Factor400FinitePRadiusArithmetic

private def finitePNthRootAccumulatorPower (a : ℕ)
    (input : List Bool) : List Bool :=
  List.replicate ((squareRootAccumulator input).length ^ a) true

private noncomputable def finitePNthRootAccumulatorPowerComputable (a : ℕ) :
    BitTM
      (finitePNthRootAccumulatorPower a) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    squareRootAccumulatorComputable
    (polynomialValueUnaryComputable (Polynomial.X ^ a))
  change BitTM
    (fun input : List Bool =>
      List.replicate ((squareRootAccumulator input).length ^ a) true)
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, Function.comp_def] using hphysical

private def finitePNthRootLessMarker (a : ℕ)
    (input : List Bool) : List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    (finitePNthRootAccumulatorPower a) squareRootTarget input

private noncomputable def finitePNthRootLessMarkerComputable (a : ℕ) :
    BitTM
      (finitePNthRootLessMarker a) :=
  fourFamilyComputedUnaryLessBitComputable
    (finitePNthRootAccumulatorPowerComputable a)
    squareRootTargetComputable

private theorem finitePNthRootLessMarker_length (a : ℕ) (input : List Bool) :
    (finitePNthRootLessMarker a input).length = 1 :=
  fourFamilyComputedUnaryLessBitOutput_length
    (finitePNthRootAccumulatorPower a) squareRootTarget input

private def finitePNthRootLessBit (a : ℕ) (input : List Bool) : Bool :=
  (finitePNthRootLessMarker a input).headD false

private theorem finitePNthRootLessMarker_eq (a : ℕ) (input : List Bool) :
    finitePNthRootLessMarker a input =
      [finitePNthRootLessBit a input] := by
  have hlength := finitePNthRootLessMarker_length a input
  cases hword : finitePNthRootLessMarker a input with
  | nil => simp only [hword, List.length_nil, zero_ne_one] at hlength
  | cons bit remaining =>
      cases remaining with
      | nil => simp only [finitePNthRootLessBit, hword, List.headD_eq_head?_getD, List.head?_cons,
          Option.getD_some]
      | cons next tail => simp only [hword, List.length_cons, Nat.add_eq_right,
          Nat.add_eq_zero_iff, List.length_eq_zero_iff,
                              one_ne_zero, and_false] at hlength

private noncomputable def finitePNthRootLessSelectionComputable (a : ℕ) :
    BitTM
      (fun input : List Bool => finitePNthRootLessBit a input :: input) := by
  have hphysical := pointwiseAppendComputable
    (finitePNthRootLessMarkerComputable a)
    (Turing.idComputableInPolyTime bitEncoding)
  have heq :
      (fun input : List Bool =>
        finitePNthRootLessMarker a input ++ input) =
        (fun input : List Bool => finitePNthRootLessBit a input :: input) := by
    funext input
    simp only [finitePNthRootLessMarker_eq, List.cons_append, List.nil_append]
  change BitTM
    (fun input : List Bool =>
      finitePNthRootLessMarker a input ++ input) at hphysical
  rwa [heq] at hphysical

private def finitePNthRootIncrement (a : ℕ) (input : List Bool) : List Bool :=
  if finitePNthRootLessBit a input then [true] else []

private noncomputable def finitePNthRootIncrementComputable (a : ℕ) :
    BitTM
      (finitePNthRootIncrement a) :=
  sourcePreservingConditionalComputable
    (finitePNthRootLessSelectionComputable a)
    (SourceCanonicalFixedWordTuringTM.sourceFixedWordComputable
      [true]) []

private def finitePNthRootCandidate (a : ℕ) (input : List Bool) : List Bool :=
  squareRootAccumulator input ++ finitePNthRootIncrement a input

private noncomputable def finitePNthRootCandidateComputable (a : ℕ) :
    BitTM
      (finitePNthRootCandidate a) :=
  pointwiseAppendComputable squareRootAccumulatorComputable
    (finitePNthRootIncrementComputable a)

private def finitePNthRootStep (a target current : ℕ) : ℕ :=
  if current ^ a < target then current + 1 else current

private theorem finitePNthRootStep_le_target
    (a target current : ℕ) (ha : 0 < a)
    (hcurrent : current ≤ target) :
    finitePNthRootStep a target current ≤ target := by
  unfold finitePNthRootStep
  split
  next hlt =>
    have hself : current ≤ current ^ a :=
      Nat.le_self_pow ha.ne' current
    omega
  next => exact hcurrent

private theorem finitePNthRootCandidate_valid
    (a current target : ℕ) (padding : List Bool) :
    finitePNthRootCandidate a
      (lengthPrefixedWord (List.replicate current true) ++
        lengthPrefixedWord (List.replicate target true) ++ padding) =
      List.replicate (finitePNthRootStep a target current) true := by
  let input :=
    lengthPrefixedWord (List.replicate current true) ++
      lengthPrefixedWord (List.replicate target true) ++ padding
  have hacc : squareRootAccumulator input =
      List.replicate current true := by
    simp only [squareRootAccumulator, List.append_assoc, firstFieldContents_valid, input]
  have htarget : squareRootTarget input =
      List.replicate target true := by
    simp only [squareRootTarget, List.append_assoc, firstFieldSuffix_valid,
        firstFieldContents_valid, input]
  have hpower : finitePNthRootAccumulatorPower a input =
      List.replicate (current ^ a) true := by
    simp only [finitePNthRootAccumulatorPower, hacc, List.length_replicate]
  have hmarker : finitePNthRootLessMarker a input =
      [decide (current ^ a < target)] :=
    fourFamilyComputedUnaryLessBitOutput_valid
      (finitePNthRootAccumulatorPower a) squareRootTarget input
      (current ^ a) target hpower htarget
  have hbit : finitePNthRootLessBit a input =
      decide (current ^ a < target) := by
    simp only [finitePNthRootLessBit, hmarker, List.headD_eq_head?_getD, List.head?_cons,
        Option.getD_some]
  change finitePNthRootCandidate a input = _
  unfold finitePNthRootCandidate finitePNthRootIncrement
  rw [hacc, hbit]
  by_cases hlt : current ^ a < target
  · simp only [hlt, decide_true, ↓reduceIte, SourceStructuralDecoder.replicate_true_append_cons,
      List.append_nil,
        ← List.replicate_succ, finitePNthRootStep]
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil,
      finitePNthRootStep]

private theorem finitePNthRootRotation_step
    (a target current : ℕ) (ha : 0 < a)
    (hcurrent : current ≤ target) :
    sourceAnchoredGridRecordRotationOutput (finitePNthRootCandidate a)
      (lengthPrefixedWord
          (squareRootAnchor (List.replicate target true)) ++
        lengthPrefixedWord (List.replicate current true)) =
      lengthPrefixedWord
          (squareRootAnchor (List.replicate target true)) ++
        lengthPrefixedWord
          (List.replicate (finitePNthRootStep a target current) true) := by
  let anchor := squareRootAnchor (List.replicate target true)
  let state :=
    lengthPrefixedWord anchor ++
      lengthPrefixedWord (List.replicate current true)
  have hraw :
      sourceAnchoredGridRawCandidate
        (finitePNthRootCandidate a) state =
        List.replicate (finitePNthRootStep a target current) true := by
    change finitePNthRootCandidate a
      (sourceAnchoredGridRankSourcePair state) = _
    have hpair :
        sourceAnchoredGridRankSourcePair state =
          lengthPrefixedWord (List.replicate current true) ++ anchor := by
      have hcontents : firstFieldContents
          (lengthPrefixedWord (List.replicate current true)) =
            List.replicate current true := by
        simpa only [List.append_nil] using
          firstFieldContents_valid (List.replicate current true) []
      simp [state, sourceAnchoredGridRankSourcePair, hcontents]
    rw [hpair]
    simpa [anchor, squareRootAnchor, List.append_assoc] using
      finitePNthRootCandidate_valid a current target
        (List.replicate target true)
  have hfit :
      (List.replicate
        (finitePNthRootStep a target current) true).length ≤
          anchor.length := by
    have hstep := finitePNthRootStep_le_target
      a target current ha hcurrent
    simp [anchor, squareRootAnchor, lengthPrefixedWord_length]
    omega
  have hselector :
      sourceAnchoredGridCandidateSelector
        (finitePNthRootCandidate a) state = true := by
    rw [sourceAnchoredGridCandidateSelector_eq, hraw]
    have hcontents : firstFieldContents state = anchor := by
      simp [state]
    rw [hcontents]
    exact decide_eq_true hfit
  have hguard :
      sourceAnchoredGridGuardedCandidate
        (finitePNthRootCandidate a) state =
          List.replicate (finitePNthRootStep a target current) true := by
    simp [sourceAnchoredGridGuardedCandidate, hselector, hraw]
  have hrotation := sourceAnchoredGridRecordRotationOutput_records
    (finitePNthRootCandidate a) anchor
    (List.replicate current true) []
  simpa [state, anchor, hguard] using hrotation

private theorem finitePNthRootRotation_iterate
    (a target current stages : ℕ) (ha : 0 < a)
    (hcurrent : current ≤ target) :
    ((sourceAnchoredGridRecordRotationOutput
      (finitePNthRootCandidate a))^[stages])
        (lengthPrefixedWord
            (squareRootAnchor (List.replicate target true)) ++
          lengthPrefixedWord (List.replicate current true)) =
      lengthPrefixedWord
          (squareRootAnchor (List.replicate target true)) ++
        lengthPrefixedWord
          (List.replicate
            (((finitePNthRootStep a target)^[stages]) current) true) := by
  induction stages generalizing current with
  | zero => simp
  | succ stages ih =>
      rw [Function.iterate_succ_apply,
        finitePNthRootRotation_step a target current ha hcurrent,
        ih (finitePNthRootStep a target current)
          (finitePNthRootStep_le_target a target current ha hcurrent),
        Function.iterate_succ_apply]

private theorem finitePNthRoot_power_lt_iff
    (a target current : ℕ) (ha : 0 < a) :
    current ^ a < target ↔
      current < finitePCeilingRoot a target := by
  constructor
  · intro hpower
    by_contra hnot
    have hroot : finitePCeilingRoot a target ≤ current :=
      Nat.le_of_not_gt hnot
    have hbound : target ≤ current ^ a :=
      (finitePCeilingRoot_spec a target ha).trans
        (Nat.pow_le_pow_left hroot a)
    exact (Nat.not_le_of_gt hpower) hbound
  · intro hroot
    by_contra hnot
    have hbound : target ≤ current ^ a := Nat.le_of_not_gt hnot
    have hminimum := finitePCeilingRoot_minimal
      a target current ha hbound
    exact (Nat.not_le_of_gt hroot) hminimum

private theorem finitePNthRootStep_iterate
    (a target stages : ℕ) (ha : 0 < a) :
    ((finitePNthRootStep a target)^[stages]) 0 =
      min stages (finitePCeilingRoot a target) := by
  induction stages with
  | zero => simp only [Function.iterate_zero, id_eq, zero_le, inf_of_le_left]
  | succ stages ih =>
      rw [Function.iterate_succ_apply', ih]
      by_cases hlt : stages < finitePCeilingRoot a target
      · have hmin :
            min stages (finitePCeilingRoot a target) = stages :=
          Nat.min_eq_left (Nat.le_of_lt hlt)
        have hnext :
            min (stages + 1) (finitePCeilingRoot a target) =
              stages + 1 :=
          Nat.min_eq_left (by omega)
        have hpower : stages ^ a < target :=
          (finitePNthRoot_power_lt_iff a target stages ha).mpr hlt
        simp only [finitePNthRootStep, hmin, hpower, ↓reduceIte, hnext]
      · have hle : finitePCeilingRoot a target ≤ stages := by
          omega
        have hmin :
            min stages (finitePCeilingRoot a target) =
              finitePCeilingRoot a target :=
          Nat.min_eq_right hle
        have hnext :
            min (stages + 1) (finitePCeilingRoot a target) =
              finitePCeilingRoot a target :=
          Nat.min_eq_right (by omega)
        have hpower :
            ¬ finitePCeilingRoot a target ^ a < target := by
          exact Nat.not_lt_of_ge
            (finitePCeilingRoot_spec a target ha)
        simp only [finitePNthRootStep, hmin, hpower, ↓reduceIte, hnext]

private theorem finitePCeilingRoot_le_target
    (a target : ℕ) (ha : 0 < a) :
    finitePCeilingRoot a target ≤ target :=
  finitePCeilingRoot_minimal a target target ha
    (Nat.le_self_pow ha.ne' target)

private theorem finitePNthRootStep_iterate_target
    (a target : ℕ) (ha : 0 < a) :
    ((finitePNthRootStep a target)^[target]) 0 =
      finitePCeilingRoot a target := by
  rw [finitePNthRootStep_iterate a target target ha,
    Nat.min_eq_right (finitePCeilingRoot_le_target a target ha)]

/-- GapCVP reduction support. -/
def finitePNthRootUnaryOutput
    (a : ℕ) (target : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  firstFieldContents
    (firstFieldSuffix
      (boundedRecordFoldOutput
        (sourceAnchoredGridRecordRotationOutput
          (finitePNthRootCandidate a))
        (squareRootFoldPreparation target input)))

/-- GapCVP reduction support. -/
noncomputable def finitePNthRootUnaryComputable
    (a : ℕ) {target : List Bool → List Bool}
    (computer : BitTM target) :
    BitTM
      (finitePNthRootUnaryOutput a target) := by
  have hfold := GapCVP.TMComposition.computableInPolyTime
    (squareRootFoldPreparationComputable computer)
    (sourceAnchoredGridRecordFoldComputable
      (finitePNthRootCandidateComputable a))
  have hsuffix := GapCVP.TMComposition.computableInPolyTime
    hfold firstFieldSuffixComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hsuffix firstFieldContentsComputable
  change BitTM
    (fun input : List Bool =>
      firstFieldContents
        (firstFieldSuffix
          (boundedRecordFoldOutput
            (sourceAnchoredGridRecordRotationOutput
              (finitePNthRootCandidate a))
            (squareRootFoldPreparation target input))))
  exact hphysical

theorem finitePNthRootUnaryOutput_valid
    (a : ℕ) (ha : 0 < a)
    (target : List Bool → List Bool)
    (input : List Bool) (value : ℕ)
    (hvalue : target input = List.replicate value true) :
    finitePNthRootUnaryOutput a target input =
      List.replicate (finitePCeilingRoot a value) true := by
  unfold finitePNthRootUnaryOutput squareRootFoldPreparation
  rw [hvalue]
  change
    firstFieldContents
      (firstFieldSuffix
        (boundedRecordFoldOutput
          (sourceAnchoredGridRecordRotationOutput
            (finitePNthRootCandidate a))
          (unaryBoundedFoldWord value
            (lengthPrefixedWord
                (squareRootAnchor (List.replicate value true)) ++
              lengthPrefixedWord [])))) = _
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word]
  change
    firstFieldContents
      (firstFieldSuffix
        (((sourceAnchoredGridRecordRotationOutput
          (finitePNthRootCandidate a))^[value])
          (lengthPrefixedWord
              (squareRootAnchor (List.replicate value true)) ++
            lengthPrefixedWord (List.replicate 0 true)))) = _
  rw [finitePNthRootRotation_iterate
    a value 0 value ha (Nat.zero_le _),
    finitePNthRootStep_iterate_target a value ha,
    firstFieldSuffix_valid]
  simpa only [List.append_nil] using
    firstFieldContents_valid
      (List.replicate (finitePCeilingRoot a value) true) []

end Factor400FinitePRadiusSourceTM

namespace Factor400FinitePRadiusRationalAtomTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceStructuralTuringTM
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputPolynomialCompositionClosure
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixUnaryQuotientRemainderTM GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFCappedUnaryPairArithmeticTM
open GapCVP.CNFUnaryPairIndexTM GapCVP.CNFUnaryPairIndexTotalRuntimeCert
open GapCVP.CLStructuralAtomicNaturalWriter

private def computedUnaryDivisionQuery
    (dividend modulus : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  dividend input ++ false :: (modulus input ++ false :: input)

private noncomputable def computedUnaryDivisionQueryComputable
    {dividend modulus : List Bool → List Bool}
    (hdividend : BitTM dividend)
    (hmodulus : BitTM modulus) :
    BitTM
      (computedUnaryDivisionQuery dividend modulus) := by
  have hsource := GapCVP.TMComposition.computableInPolyTime
    (Turing.idComputableInPolyTime bitEncoding)
    (prependBitComputable false)
  have hsecond := pointwiseAppendComputable hmodulus hsource
  have hseparator := GapCVP.TMComposition.computableInPolyTime
    hsecond (prependBitComputable false)
  have hphysical := pointwiseAppendComputable
    hdividend hseparator
  change BitTM
    (fun input : List Bool =>
      dividend input ++ false :: (modulus input ++ false :: input))
  simpa only [Function.comp_apply, id_eq] using hphysical

private def computedUnaryDivisionOutput
    (dividend modulus : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  sourceUnaryDivisionOutput
    (computedUnaryDivisionQuery dividend modulus input)

private noncomputable def computedUnaryDivisionComputable
    {dividend modulus : List Bool → List Bool}
    (hdividend : BitTM dividend)
    (hmodulus : BitTM modulus) :
    BitTM
      (computedUnaryDivisionOutput dividend modulus) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (computedUnaryDivisionQueryComputable hdividend hmodulus)
    sourceUnaryDivisionComputable
  change BitTM
    (fun input : List Bool => sourceUnaryDivisionOutput
      (computedUnaryDivisionQuery dividend modulus input))
  simpa only [Function.comp_def] using hphysical

private theorem computedUnaryDivisionOutput_valid
    (dividend modulus : List Bool → List Bool)
    (input : List Bool) (first second : ℕ)
    (hfirst : dividend input = List.replicate first true)
    (hsecond : modulus input = List.replicate second true)
    (hpositive : 0 < second) :
    computedUnaryDivisionOutput dividend modulus input =
      List.replicate (first / second) true ++
        false :: (List.replicate (first % second) true ++
          false :: sourceUnaryDivisionQuery first second input) := by
  unfold computedUnaryDivisionOutput computedUnaryDivisionQuery
  rw [hfirst, hsecond]
  exact sourceUnaryDivisionOutput_valid first second input hpositive

private def computedUnaryQuotient
    (dividend modulus : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  (unaryPrefixOutput
    (computedUnaryDivisionOutput dividend modulus input)).tail

private noncomputable def computedUnaryQuotientComputable
    {dividend modulus : List Bool → List Bool}
    (hdividend : BitTM dividend)
    (hmodulus : BitTM modulus) :
    BitTM
      (computedUnaryQuotient dividend modulus) := by
  have hscan := GapCVP.TMComposition.computableInPolyTime
    (computedUnaryDivisionComputable hdividend hmodulus)
    unaryPrefixComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hscan dropHeadComputable
  change BitTM
    (fun input : List Bool =>
      (unaryPrefixOutput
        (computedUnaryDivisionOutput dividend modulus input)).tail)
  simpa only [Function.comp_def] using hphysical

private theorem computedUnaryQuotient_valid
    (dividend modulus : List Bool → List Bool)
    (input : List Bool) (first second : ℕ)
    (hfirst : dividend input = List.replicate first true)
    (hsecond : modulus input = List.replicate second true)
    (hpositive : 0 < second) :
    computedUnaryQuotient dividend modulus input =
      List.replicate (first / second) true := by
  unfold computedUnaryQuotient
  rw [computedUnaryDivisionOutput_valid
    dividend modulus input first second hfirst hsecond hpositive]
  rw [unaryPrefixOutput_replicate_delimiter]
  rfl

private def computedUnaryRemainder
    (dividend modulus : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  (unaryPrefixOutput
    (unaryPrefixSuffixOutput
      (computedUnaryDivisionOutput dividend modulus input))).tail

private noncomputable def computedUnaryRemainderComputable
    {dividend modulus : List Bool → List Bool}
    (hdividend : BitTM dividend)
    (hmodulus : BitTM modulus) :
    BitTM
      (computedUnaryRemainder dividend modulus) := by
  have hsuffix := GapCVP.TMComposition.computableInPolyTime
    (computedUnaryDivisionComputable hdividend hmodulus)
    actualUnaryPrefixSuffixComputable
  have hscan := GapCVP.TMComposition.computableInPolyTime
    hsuffix unaryPrefixComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hscan dropHeadComputable
  change BitTM
    (fun input : List Bool =>
      (unaryPrefixOutput
        (unaryPrefixSuffixOutput
          (computedUnaryDivisionOutput dividend modulus input))).tail)
  simpa only [Function.comp_def] using hphysical

private theorem computedUnaryRemainder_valid
    (dividend modulus : List Bool → List Bool)
    (input : List Bool) (first second : ℕ)
    (hfirst : dividend input = List.replicate first true)
    (hsecond : modulus input = List.replicate second true)
    (hpositive : 0 < second) :
    computedUnaryRemainder dividend modulus input =
      List.replicate (first % second) true := by
  unfold computedUnaryRemainder
  rw [computedUnaryDivisionOutput_valid
    dividend modulus input first second hfirst hsecond hpositive]
  rw [unaryPrefixSuffixOutput_valid,
    unaryPrefixOutput_replicate_delimiter]
  rfl

private def fixedUnaryLessMarker
    (operand : List Bool → List Bool)
    (cutoff : ℕ) (input : List Bool) : List Bool :=
  fourFamilyComputedUnaryLessBitOutput operand
    (fun _ : List Bool => List.replicate cutoff true) input

private noncomputable def fixedUnaryLessMarkerComputable
    {operand : List Bool → List Bool}
    (computer : BitTM operand)
    (cutoff : ℕ) :
    BitTM
      (fixedUnaryLessMarker operand cutoff) := by
  exact fourFamilyComputedUnaryLessBitComputable
    computer (sourceFixedWordComputable (List.replicate cutoff true))

private def fixedUnaryLessBit
    (operand : List Bool → List Bool)
    (cutoff : ℕ) (input : List Bool) : Bool :=
  (fixedUnaryLessMarker operand cutoff input).headD false

private theorem fixedUnaryLessMarker_eq
    (operand : List Bool → List Bool)
    (cutoff : ℕ) (input : List Bool) :
    fixedUnaryLessMarker operand cutoff input =
      [fixedUnaryLessBit operand cutoff input] := by
  have hlength := fourFamilyComputedUnaryLessBitOutput_length
    operand (fun _ : List Bool => List.replicate cutoff true) input
  change (fixedUnaryLessMarker operand cutoff input).length = 1
    at hlength
  cases hword : fixedUnaryLessMarker operand cutoff input with
  | nil => simp only [hword, List.length_nil, zero_ne_one] at hlength
  | cons bit remaining =>
      cases remaining with
      | nil => simp only [fixedUnaryLessBit, hword, List.headD_eq_head?_getD, List.head?_cons,
          Option.getD_some]
      | cons next tail => simp only [hword, List.length_cons, Nat.add_eq_right,
          Nat.add_eq_zero_iff, List.length_eq_zero_iff,
                              one_ne_zero, and_false] at hlength

private theorem fixedUnaryLessBit_valid
    (operand : List Bool → List Bool)
    (cutoff : ℕ) (input : List Bool) (value : ℕ)
    (hvalue : operand input = List.replicate value true) :
    fixedUnaryLessBit operand cutoff input =
      decide (value < cutoff) := by
  have hmarker := fourFamilyComputedUnaryLessBitOutput_valid
    operand (fun _ : List Bool => List.replicate cutoff true)
    input value cutoff hvalue rfl
  simpa only [fixedUnaryLessBit, fixedUnaryLessMarker, List.headD_eq_head?_getD, List.head?_cons,
      Option.getD_some] using congrArg (fun word : List Bool => word.headD false) hmarker

@[irreducible] private noncomputable def fixedUnaryLessSelectionComputable
    {operand : List Bool → List Bool}
    (computer : BitTM operand)
    (cutoff : ℕ) :
    BitTM
      (fun input : List Bool =>
        fixedUnaryLessBit operand cutoff input :: input) := by
  have hphysical := pointwiseAppendComputable
    (fixedUnaryLessMarkerComputable computer cutoff)
    (Turing.idComputableInPolyTime bitEncoding)
  have heq :
      (fun input : List Bool =>
        fixedUnaryLessMarker operand cutoff input ++ input) =
      (fun input : List Bool =>
        fixedUnaryLessBit operand cutoff input :: input) := by
    funext input
    simp only [fixedUnaryLessMarker_eq, List.cons_append, List.nil_append]
  change BitTM
    (fun input : List Bool =>
      fixedUnaryLessMarker operand cutoff input ++ input) at hphysical
  rwa [heq] at hphysical

private def fixedGcdLookup
    (modulus : ℕ) (residue : List Bool → List Bool) :
    ℕ → List Bool → List Bool
  | 0 => fun _ => List.replicate (Nat.gcd 0 modulus) true
  | stages + 1 => fun input =>
      if fixedUnaryLessBit residue stages.succ input then
        fixedGcdLookup modulus residue stages input
      else
        List.replicate (Nat.gcd stages.succ modulus) true

@[irreducible] private noncomputable def fixedGcdLookupSuccComputable
    (modulus : ℕ) {residue : List Bool → List Bool}
    (computer : BitTM residue)
    (stages : ℕ)
    (previous : BitTM
      (fixedGcdLookup modulus residue stages)) :
    BitTM
      (fixedGcdLookup modulus residue stages.succ) :=
  sourcePreservingConditionalComputable
    (selector := fixedUnaryLessBit residue stages.succ)
    (valid := fixedGcdLookup modulus residue stages)
    (fixedUnaryLessSelectionComputable
      (operand := residue) computer stages.succ)
    previous (List.replicate (Nat.gcd stages.succ modulus) true)

@[irreducible] private noncomputable def fixedGcdLookupComputable
    (modulus : ℕ) {residue : List Bool → List Bool}
    (computer : BitTM residue)
    (stages : ℕ) :
    BitTM
      (fixedGcdLookup modulus residue stages) :=
  match stages with
  | 0 => sourceFixedWordComputable
      (List.replicate (Nat.gcd 0 modulus) true)
  | stages + 1 => fixedGcdLookupSuccComputable
      modulus computer stages
      (fixedGcdLookupComputable
        (residue := residue) modulus computer stages)

private theorem fixedGcdLookup_valid
    (modulus : ℕ) (residue : List Bool → List Bool)
    (input : List Bool) (value stages : ℕ)
    (hvalue : residue input = List.replicate value true)
    (hbound : value ≤ stages) :
    fixedGcdLookup modulus residue stages input =
      List.replicate (Nat.gcd value modulus) true := by
  induction stages generalizing value with
  | zero =>
      have hzero : value = 0 := Nat.eq_zero_of_le_zero hbound
      subst value
      rfl
  | succ stages ih =>
      have hbit := fixedUnaryLessBit_valid
        residue (stages + 1) input value hvalue
      by_cases hlt : value < stages + 1
      · have hle : value ≤ stages := by omega
        simpa only [fixedGcdLookup, Nat.succ_eq_add_one, hbit, hlt, decide_true, ↓reduceIte]
            using ih value hvalue hle
      · have heq : value = stages + 1 := by omega
        subst value
        simp only [fixedGcdLookup, Nat.succ_eq_add_one, hbit, lt_self_iff_false, decide_false,
            Bool.false_eq_true,
            ↓reduceIte]

private def constantScaleUnary (scale : ℕ) : List Bool → List Bool :=
  fun _ => List.replicate scale true

private noncomputable def constantScaleUnaryComputable (scale : ℕ) :
    BitTM
      (constantScaleUnary scale) :=
  sourceFixedWordComputable (List.replicate scale true)

private def sourceReducedGcdUnary
    (scale : ℕ) (numerator : List Bool → List Bool) :
    List Bool → List Bool :=
  fixedGcdLookup scale
    (computedUnaryRemainder numerator (constantScaleUnary scale))
    scale

private noncomputable def sourceReducedGcdUnaryComputable
    (scale : ℕ) {numerator : List Bool → List Bool}
    (computer : BitTM numerator) :
    BitTM
      (sourceReducedGcdUnary scale numerator) := by
  exact fixedGcdLookupComputable scale
    (computedUnaryRemainderComputable
      computer (constantScaleUnaryComputable scale)) scale

private theorem sourceReducedGcdUnary_valid
    (scale : ℕ) (numerator : List Bool → List Bool)
    (input : List Bool) (value : ℕ)
    (hscale : 0 < scale)
    (hvalue : numerator input = List.replicate value true) :
    sourceReducedGcdUnary scale numerator input =
      List.replicate (Nat.gcd value scale) true := by
  have hremainder := computedUnaryRemainder_valid
    numerator (constantScaleUnary scale) input value scale
    hvalue rfl hscale
  have hbound : value % scale ≤ scale :=
    (Nat.mod_lt value hscale).le
  have hgcd := fixedGcdLookup_valid scale
    (computedUnaryRemainder numerator (constantScaleUnary scale))
    input (value % scale) scale hremainder hbound
  have heq : Nat.gcd (value % scale) scale =
      Nat.gcd value scale := by
    calc
      Nat.gcd (value % scale) scale = Nat.gcd scale value :=
        (Nat.gcd_rec scale value).symm
      _ = Nat.gcd value scale := Nat.gcd_comm scale value
  simpa only [sourceReducedGcdUnary, heq] using hgcd

private def sourceReducedNumeratorUnary
    (scale : ℕ) (numerator : List Bool → List Bool) :
    List Bool → List Bool :=
  computedUnaryQuotient numerator
    (sourceReducedGcdUnary scale numerator)

private noncomputable def sourceReducedNumeratorUnaryComputable
    (scale : ℕ) {numerator : List Bool → List Bool}
    (computer : BitTM numerator) :
    BitTM
      (sourceReducedNumeratorUnary scale numerator) :=
  computedUnaryQuotientComputable computer
    (sourceReducedGcdUnaryComputable scale computer)

private theorem sourceReducedNumeratorUnary_valid
    (scale : ℕ) (numerator : List Bool → List Bool)
    (input : List Bool) (value : ℕ)
    (hscale : 0 < scale)
    (hvalue : numerator input = List.replicate value true) :
    sourceReducedNumeratorUnary scale numerator input =
      List.replicate (value / Nat.gcd value scale) true := by
  exact computedUnaryQuotient_valid numerator
    (sourceReducedGcdUnary scale numerator) input
    value (Nat.gcd value scale) hvalue
    (sourceReducedGcdUnary_valid scale numerator input
      value hscale hvalue)
    (Nat.gcd_pos_of_pos_right value hscale)

private def sourceReducedDenominatorUnary
    (scale : ℕ) (numerator : List Bool → List Bool) :
    List Bool → List Bool :=
  computedUnaryQuotient (constantScaleUnary scale)
    (sourceReducedGcdUnary scale numerator)

private noncomputable def sourceReducedDenominatorUnaryComputable
    (scale : ℕ) {numerator : List Bool → List Bool}
    (computer : BitTM numerator) :
    BitTM
      (sourceReducedDenominatorUnary scale numerator) :=
  computedUnaryQuotientComputable
    (constantScaleUnaryComputable scale)
    (sourceReducedGcdUnaryComputable scale computer)

private theorem sourceReducedDenominatorUnary_valid
    (scale : ℕ) (numerator : List Bool → List Bool)
    (input : List Bool) (value : ℕ)
    (hscale : 0 < scale)
    (hvalue : numerator input = List.replicate value true) :
    sourceReducedDenominatorUnary scale numerator input =
      List.replicate (scale / Nat.gcd value scale) true := by
  exact computedUnaryQuotient_valid
    (constantScaleUnary scale)
    (sourceReducedGcdUnary scale numerator) input
    scale (Nat.gcd value scale) rfl
    (sourceReducedGcdUnary_valid scale numerator input
      value hscale hvalue)
    (Nat.gcd_pos_of_pos_right value hscale)

private def sourceReducedSignedNumeratorUnary
    (scale : ℕ) (numerator : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  List.replicate
    (2 * (sourceReducedNumeratorUnary scale numerator input).length)
    true

private noncomputable def sourceReducedSignedNumeratorUnaryComputable
    (scale : ℕ) {numerator : List Bool → List Bool}
    (computer : BitTM numerator) :
    BitTM
      (sourceReducedSignedNumeratorUnary scale numerator) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (sourceReducedNumeratorUnaryComputable scale computer)
    (polynomialValueUnaryComputable
      (Polynomial.C 2 * Polynomial.X))
  change BitTM
    (fun input : List Bool => List.replicate
      (2 * (sourceReducedNumeratorUnary scale numerator input).length)
      true)
  simpa only [eq_natCast, Nat.cast_ofNat, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X,
      Function.comp_def] using hphysical

private theorem sourceReducedSignedNumeratorUnary_valid
    (scale : ℕ) (numerator : List Bool → List Bool)
    (input : List Bool) (value : ℕ)
    (hscale : 0 < scale)
    (hvalue : numerator input = List.replicate value true) :
    sourceReducedSignedNumeratorUnary scale numerator input =
      List.replicate (2 * (value / Nat.gcd value scale)) true := by
  unfold sourceReducedSignedNumeratorUnary
  rw [sourceReducedNumeratorUnary_valid
    scale numerator input value hscale hvalue]
  simp only [List.length_replicate]

private def sourceReducedRationalPairWord
    (scale : ℕ) (numerator : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  sourceReducedSignedNumeratorUnary scale numerator input ++
    false :: (sourceReducedDenominatorUnary scale numerator input ++
      [false])

private noncomputable def sourceReducedRationalPairWordComputable
    (scale : ℕ) {numerator : List Bool → List Bool}
    (computer : BitTM numerator) :
    BitTM
      (sourceReducedRationalPairWord scale numerator) := by
  have hsecond := pointwiseAppendComputable
    (sourceReducedDenominatorUnaryComputable scale computer)
    (sourceFixedWordComputable [false])
  have hdelimiter := GapCVP.TMComposition.computableInPolyTime
    hsecond (prependBitComputable false)
  have hphysical := pointwiseAppendComputable
    (sourceReducedSignedNumeratorUnaryComputable scale computer)
    hdelimiter
  change BitTM
    (fun input : List Bool =>
      sourceReducedSignedNumeratorUnary scale numerator input ++
        false ::
          (sourceReducedDenominatorUnary scale numerator input ++
            [false]))
  simpa only [Function.comp_apply] using hphysical

private def sourceReducedRationalCodeUnary
    (scale : ℕ) (numerator : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  unarySourcePairOutput
    (sourceReducedRationalPairWord scale numerator input)

private noncomputable def sourceReducedRationalCodeUnaryComputable
    (scale : ℕ) {numerator : List Bool → List Bool}
    (computer : BitTM numerator) :
    BitTM
      (sourceReducedRationalCodeUnary scale numerator) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (sourceReducedRationalPairWordComputable scale computer)
    actualUnaryPairIndexComputable
  change BitTM
    (fun input : List Bool => unarySourcePairOutput
      (sourceReducedRationalPairWord scale numerator input))
  simpa only [Function.comp_def] using hphysical

private theorem sourceReducedRationalCodeUnary_valid
    (scale : ℕ) (numerator : List Bool → List Bool)
    (input : List Bool) (value : ℕ)
    (hscale : 0 < scale)
    (hvalue : numerator input = List.replicate value true) :
    sourceReducedRationalCodeUnary scale numerator input =
      List.replicate
        (Nat.pair (2 * (value / Nat.gcd value scale))
          (scale / Nat.gcd value scale)) true := by
  unfold sourceReducedRationalCodeUnary
    sourceReducedRationalPairWord
  rw [sourceReducedSignedNumeratorUnary_valid
    scale numerator input value hscale hvalue]
  rw [sourceReducedDenominatorUnary_valid
    scale numerator input value hscale hvalue]
  exact unarySourcePairOutput_word
    (2 * (value / Nat.gcd value scale))
    (scale / Nat.gcd value scale)

private theorem nonnegativeRational_encode_pair
    (numerator denominator : ℕ)
    (hdenominator : 0 < denominator) :
    Encodable.encode
      ((numerator : ℚ) / (denominator : ℚ)) =
      Nat.pair
        (2 * (numerator / Nat.gcd numerator denominator))
        (denominator / Nat.gcd numerator denominator) := by
  rw [Rat.natCast_div_eq_divInt, Rat.divInt_ofNat]
  change Nat.pair
    (Encodable.encode
      (mkRat (Int.ofNat numerator) denominator).num)
    (mkRat (Int.ofNat numerator) denominator).den = _
  rw [Rat.num_mkRat, Rat.den_mkRat]
  simp only [hdenominator.ne', ↓reduceIte]
  change Nat.pair
    (2 * (numerator / Nat.gcd denominator numerator))
    (denominator / Nat.gcd denominator numerator) = _
  rw [Nat.gcd_comm denominator numerator]

/-- GapCVP reduction support. -/
def sourceReducedRationalAtomicOutput
    (scale : ℕ) (numerator : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  structuralAtomicNaturalWord
    (sourceReducedRationalCodeUnary scale numerator input)

/-- GapCVP reduction support. -/
noncomputable def sourceReducedRationalAtomicComputable
    (scale : ℕ) {numerator : List Bool → List Bool}
    (computer : BitTM numerator) :
    BitTM
      (sourceReducedRationalAtomicOutput scale numerator) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (sourceReducedRationalCodeUnaryComputable scale computer)
    structuralAtomicNaturalWriterComputable
  change BitTM
    (fun input : List Bool => structuralAtomicNaturalWord
      (sourceReducedRationalCodeUnary scale numerator input))
  simpa only [Function.comp_def] using hphysical

theorem sourceReducedRationalAtomicOutput_valid
    (scale : ℕ) (numerator : List Bool → List Bool)
    (input : List Bool) (value : ℕ)
    (hscale : 0 < scale)
    (hvalue : numerator input = List.replicate value true) :
    sourceReducedRationalAtomicOutput scale numerator input =
      encodeAtomic ((value : ℚ) / (scale : ℚ)) := by
  unfold sourceReducedRationalAtomicOutput
  rw [sourceReducedRationalCodeUnary_valid
    scale numerator input value hscale hvalue]
  rw [structuralAtomicNaturalWord_eq_prefix]
  simp only [List.length_replicate, encodeAtomic, nonnegativeRational_encode_pair value scale
      hscale]

end Factor400FinitePRadiusRationalAtomTM

namespace Factor400BinaryCompactPhysicalGaussianOutputSerializerTM

open Turing GapCVP.BinaryEncoding GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryStructuralRecordTM
open GapCVP.BinaryGaussianStructuralAtomTM GapCVP.GaussianPhysicalWordRankIndexTM
open GapCVP.GaussianPackedStateTargetAtomTM GapCVP.SourceWholeOutputAssemblyTM

/-- GapCVP reduction support. -/
def compactPhysicalGaussianRankReducedState
    (reduced : List Bool → List Bool) : List Bool → List Bool :=
  reduced ∘ structuralRankOriginalSource

/-- GapCVP reduction support. -/
noncomputable def compactPhysicalGaussianRankReducedStateComputable
    {reduced : List Bool → List Bool}
    (computer : BitTM reduced) :
    BitTM
      (compactPhysicalGaussianRankReducedState reduced) :=
  GapCVP.TMComposition.computableInPolyTime
    structuralRankOriginalSourceComputable computer

/-- GapCVP reduction support. -/
def compactPhysicalGaussianRankTargetStateQuery
    (reduced : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (factor400PhysicalWordGaussianTargetCoordinateUnary input) ++
    compactPhysicalGaussianRankReducedState reduced input

/-- GapCVP reduction support. -/
noncomputable def compactPhysicalGaussianRankTargetStateQueryComputable
    {reduced : List Bool → List Bool}
    (computer : BitTM reduced) :
    BitTM
      (compactPhysicalGaussianRankTargetStateQuery reduced) := by
  have hindex := GapCVP.TMComposition.computableInPolyTime
    factor400PhysicalWordGaussianTargetCoordinateComputable
    structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable hindex
    (compactPhysicalGaussianRankReducedStateComputable computer)
  change BitTM
    (fun input =>
      lengthPrefixedWord
        (factor400PhysicalWordGaussianTargetCoordinateUnary input) ++
        compactPhysicalGaussianRankReducedState reduced input)
  simpa only [Function.comp_apply] using hphysical

/-- GapCVP reduction support. -/
def compactPhysicalGaussianRankTargetAtom
    (reduced : List Bool → List Bool) : List Bool → List Bool :=
  gaussianPackedIndexedTargetAtom ∘
    compactPhysicalGaussianRankTargetStateQuery reduced

/-- GapCVP reduction support. -/
noncomputable def compactPhysicalGaussianRankTargetAtomComputable
    {reduced : List Bool → List Bool}
    (computer : BitTM reduced) :
    BitTM
      (compactPhysicalGaussianRankTargetAtom reduced) :=
  GapCVP.TMComposition.computableInPolyTime
    (compactPhysicalGaussianRankTargetStateQueryComputable computer)
    gaussianPackedIndexedTargetAtomComputable

/-- GapCVP reduction support. -/
def compactPhysicalGaussianRankRadiusAtom
    (radius : List Bool → List Bool) : List Bool → List Bool :=
  radius ∘ structuralRankOriginalSource

/-- GapCVP reduction support. -/
noncomputable def compactPhysicalGaussianRankRadiusAtomComputable
    {radius : List Bool → List Bool}
    (computer : BitTM radius) :
    BitTM
      (compactPhysicalGaussianRankRadiusAtom radius) :=
  GapCVP.TMComposition.computableInPolyTime
    structuralRankOriginalSourceComputable computer

/-- GapCVP reduction support. -/
def compactPhysicalGaussianStructuralAtomComputerPack
    (output : List Bool → List Bool)
    (computer : BitTM output) :
    ConstructiveStructuralAtomComputer where
  output := output
  computer := computer

@[simp] theorem compactPhysicalGaussianStructuralAtomComputerPack_output
    (output : List Bool → List Bool)
    (computer : BitTM output)
    (input : List Bool) :
    (compactPhysicalGaussianStructuralAtomComputerPack
      output computer).output input = output input := by
  rfl

end Factor400BinaryCompactPhysicalGaussianOutputSerializerTM

namespace OriginalThreeSATNPHardness

open Computability GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.CLStructuralWholeCNFOutputTM GapCVP.CNFFiveFamilySourceIndexedORGadgetFinalCert

/-- GapCVP reduction support. -/
noncomputable def paperOriginalThreeSATLanguage (bits : List Bool) : Bool :=
  @decide
    (∃ formula : ThreeCNF,
      encodeThreeCNF formula = bits ∧
        ∃ assignment : ℕ → Bool,
          ∀ clause ∈ formula, clauseSatisfied assignment clause)
    (Classical.propDecidable _)

theorem paperOriginalThreeSATLanguage_iff (bits : List Bool) :
    paperOriginalThreeSATLanguage bits ↔
      ∃ formula : ThreeCNF,
        encodeThreeCNF formula = bits ∧
          ∃ assignment : ℕ → Bool,
            ∀ clause ∈ formula, clauseSatisfied assignment clause := by
  simp only [GapCVP.OriginalThreeSATNPHardness.paperOriginalThreeSATLanguage, decide_eq_true_eq]

private theorem paperOriginalThreeSATLanguage_encode_iff (formula : ThreeCNF) :
    paperOriginalThreeSATLanguage (encodeThreeCNF formula) ↔
      ∃ assignment : ℕ → Bool,
        ∀ clause ∈ formula, clauseSatisfied assignment clause := by
  rw [paperOriginalThreeSATLanguage_iff]
  constructor
  · rintro ⟨candidate, encoding, assignment, satisfied⟩
    have sameEncoding := congrArg decodeThreeCNF encoding
    have sameFormula : candidate = formula := by
      simpa only [decodeThreeCNF_encode, Option.some.injEq]
        using sameEncoding
    subst candidate
    exact ⟨assignment, satisfied⟩
  · rintro ⟨assignment, satisfied⟩
    exact ⟨formula, rfl, assignment, satisfied⟩

private theorem paperOriginalThreeSATLanguage_encode_iff_threeSAT
    (formula : ThreeCNF)
    (distinct : allDistinct formula) :
    paperOriginalThreeSATLanguage (encodeThreeCNF formula) ↔
      threeSATLanguage (encodeThreeCNF formula) := by
  simp only [GapCVP.ThreeCNFReduction.allDistinct, decide_eq_true_eq] at distinct
  rw [paperOriginalThreeSATLanguage_encode_iff]
  change
    (∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) ↔
      threeSATLanguage ((binaryFinEncoding ThreeCNF).encode formula)
  rw [GapCVP.CLVerifier.threeSATLanguage_encode_iff]
  simp only [GapCVP.threeCNFSatisfiable, decide_eq_true_eq]
  exact ⟨fun satisfaction => ⟨distinct, satisfaction⟩,
    fun satisfaction => satisfaction.2⟩

private theorem structuralWholeCNFWord_mem_paperOriginalThreeSAT_iff
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) :
    paperOriginalThreeSATLanguage
        (structuralWholeCNFWord bound machine input) ↔
      ∃ certificate : List Bool,
        certificate.length ≤ bound.eval input.length ∧
          verifier (input, certificate) = true := by
  exact
    (paperOriginalThreeSATLanguage_encode_iff_threeSAT
      (structuralWholeThreeCNF bound machine input)
      (structuralWholeThreeCNF_allDistinct bound machine input)).trans
        (structuralWholeCNFWord_mem_threeSAT_iff bound machine input)

theorem paperOriginalThreeSATIsNPHard :
    NPHard paperOriginalThreeSATLanguage := by
  simp only [GapCVP.NPHard, decide_eq_true_eq]
  intro language membership
  simp only [GapCVP.IsNP, decide_eq_true_eq] at membership
  obtain ⟨bound, verifier, ⟨machine⟩, correctness⟩ := membership
  refine ⟨{
    map := structuralWholeCNFWord bound machine
    polynomial_time :=
      ⟨actualWholeStructuralCNFOutputComputable bound machine⟩
    correct := ?_
  }⟩
  intro input
  exact (correctness input).trans
    (structuralWholeCNFWord_mem_paperOriginalThreeSAT_iff
      bound machine input).symm

end OriginalThreeSATNPHardness

namespace BinarySourceTautologyNormalizationExact

/-- GapCVP reduction support. -/
def sourceClauseIsTautology (clause : ThreeClause) : Bool :=
  decide (∃ left right : Fin 3,
    (clause left).1 = (clause right).1 ∧
      (clause left).2 ≠ (clause right).2)

theorem sourceClauseIsTautology_iff
    (clause : ThreeClause) :
    sourceClauseIsTautology clause = true ↔
      ∃ left right : Fin 3,
        (clause left).1 = (clause right).1 ∧
          (clause left).2 ≠ (clause right).2 := by
  simp only [sourceClauseIsTautology, ne_eq, decide_eq_true_eq]

private theorem sourceClauseIsTautology_satisfied
    (assignment : ℕ → Bool) (clause : ThreeClause)
    (htautology : sourceClauseIsTautology clause = true) :
    clauseSatisfied assignment clause := by
  simp only [GapCVP.clauseSatisfied, GapCVP.literalSatisfied, decide_eq_true_eq] at *
  obtain ⟨left, right, hname, hsign⟩ :=
    (sourceClauseIsTautology_iff clause).mp htautology
  by_cases hleft : assignment (clause left).1 = (clause left).2
  · exact ⟨left, hleft⟩
  · refine ⟨right, ?_⟩
    rw [← hname]
    cases hvalue : assignment (clause left).1 <;>
      cases hleftSign : (clause left).2 <;>
      cases hrightSign : (clause right).2 <;>
      simp_all

/-- GapCVP reduction support. -/
def noTautClauses (formula : ThreeCNF) : ThreeCNF :=
  formula.filter fun clause => !(sourceClauseIsTautology clause)

theorem mem_sourceClausesWithoutTautologies
    (formula : ThreeCNF) (clause : ThreeClause) :
    clause ∈ noTautClauses formula ↔
      clause ∈ formula ∧ sourceClauseIsTautology clause = false := by
  simp only [noTautClauses, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true]

private theorem sourceClausesWithoutTautologies_satisfied_iff
    (formula : ThreeCNF) (assignment : ℕ → Bool) :
    (∀ clause ∈ noTautClauses formula,
      clauseSatisfied assignment clause) ↔
      (∀ clause ∈ formula, clauseSatisfied assignment clause) := by
  constructor
  · intro hremaining clause hclause
    cases htautology : sourceClauseIsTautology clause with
    | false =>
        exact hremaining clause
          ((mem_sourceClausesWithoutTautologies formula clause).mpr
            ⟨hclause, htautology⟩)
    | true =>
        exact sourceClauseIsTautology_satisfied
          assignment clause htautology
  · intro hall clause hclause
    exact hall clause
      ((mem_sourceClausesWithoutTautologies formula clause).mp
        hclause).1

end BinarySourceTautologyNormalizationExact

namespace SourcePreprocessingSemantics

open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.BinarySourceVariableCompaction

/-- GapCVP reduction support. -/
def paperSourceClauseLiterals (clause : ThreeClause) : List Literal :=
  [clause 0, clause 1, clause 2]

/-- GapCVP reduction support. -/
def paperSourceNormalizedClause (clause : ThreeClause) : List Literal :=
  (paperSourceClauseLiterals clause).eraseDups

/-- GapCVP reduction support. -/
def paperSourceNormalizedClauses (formula : ThreeCNF) :
    List (List Literal) :=
  (noTautClauses formula).map
    paperSourceNormalizedClause

/-- GapCVP reduction support. -/
def paperSourceNormalizedClauseRecord (clause : ThreeClause) : List Bool :=
  List.replicate (paperSourceNormalizedClause clause).length true ++
    false :: (paperSourceNormalizedClause clause).flatMap encodeLiteral

/-- GapCVP reduction support. -/
def paperSourceNormalizedClauseStream (formula : ThreeCNF) : List Bool :=
  (noTautClauses formula).flatMap
    paperSourceNormalizedClauseRecord

/-- GapCVP reduction support. -/
def paperSourceNormalizedVariables (formula : ThreeCNF) : List ℕ :=
  (paperSourceNormalizedClauses formula).flatMap
    (fun clause => clause.map Prod.fst)

/-- GapCVP reduction support. -/
def paperNormalizedOccurringVariables (formula : ThreeCNF) : List ℕ :=
  (paperSourceNormalizedVariables formula).eraseDups

private theorem paperSourceLiteralEraseDups_length_le
    (literals : List Literal) :
    literals.eraseDups.length ≤ literals.length := by
  induction literals using
      (measure fun values : List Literal => values.length).wf.induction with
  | h literals induction =>
      cases literals with
      | nil => simp only [List.eraseDups_nil, List.length_nil, Std.le_refl]
      | cons literal remaining =>
          rw [List.eraseDups_cons]
          simp only [List.length_cons]
          apply Nat.succ_le_succ
          exact Nat.le_trans
            (induction
              (remaining.filter fun candidate => !(candidate == literal))
              (Nat.lt_succ_of_le (List.length_filter_le _ _)))
            (List.length_filter_le _ remaining)

private theorem paperSourceLiteralEraseDups_nodup
    (literals : List Literal) :
    literals.eraseDups.Nodup := by
  induction literals using
      (measure fun values : List Literal => values.length).wf.induction with
  | h literals induction =>
      cases literals with
      | nil => simp only [List.eraseDups_nil, List.nodup_nil]
      | cons literal remaining =>
          rw [List.eraseDups_cons, List.nodup_cons]
          constructor
          · simp only [List.mem_eraseDups, List.mem_filter, BEq.rfl, Bool.not_true,
              Bool.false_eq_true, and_false,
                not_false_eq_true]
          · exact induction
              (remaining.filter fun candidate => !(candidate == literal))
              (Nat.lt_succ_of_le (List.length_filter_le _ _))

theorem paperNormalizedClause_length_le_three
    (clause : ThreeClause) :
    (paperSourceNormalizedClause clause).length ≤ 3 := by
  simpa only [paperSourceNormalizedClause, paperSourceClauseLiterals, Fin.isValue,
      List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd] using
      paperSourceLiteralEraseDups_length_le (paperSourceClauseLiterals clause)

theorem paperSourceNormalizedClause_ne_nil
    (clause : ThreeClause) :
    paperSourceNormalizedClause clause ≠ [] := by
  intro hempty
  have hfirst : clause 0 ∈ paperSourceNormalizedClause clause := by
    simp only [paperSourceNormalizedClause, paperSourceClauseLiterals, Fin.isValue,
        List.mem_eraseDups,
        List.mem_cons, List.not_mem_nil, or_false, true_or]
  simp only [hempty, Fin.isValue, List.not_mem_nil] at hfirst

theorem paperSourceNormalizedClause_nodup
    (clause : ThreeClause) :
    (paperSourceNormalizedClause clause).Nodup := by
  exact paperSourceLiteralEraseDups_nodup
    (paperSourceClauseLiterals clause)

theorem mem_paperSourceNormalizedClause_iff
    (clause : ThreeClause) (literal : Literal) :
    literal ∈ paperSourceNormalizedClause clause ↔
      ∃ index : Fin 3, clause index = literal := by
  simp only [paperSourceNormalizedClause, paperSourceClauseLiterals, Fin.isValue,
      List.mem_eraseDups,
      List.mem_cons, List.not_mem_nil, or_false, eq_comm, Fin.exists_fin_succ,
          Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      IsEmpty.exists_iff]

private theorem paperSourceNormalizedClause_satisfied_iff
    (assignment : ℕ → Bool) (clause : ThreeClause) :
    (∃ literal ∈ paperSourceNormalizedClause clause,
      literalSatisfied assignment literal) ↔
      clauseSatisfied assignment clause := by
  simp only [paperSourceNormalizedClause, paperSourceClauseLiterals, Fin.isValue,
      List.mem_eraseDups,
      List.mem_cons, List.not_mem_nil, or_false, literalSatisfied, decide_eq_true_eq,
          exists_eq_or_imp, ↓existsAndEq,
      true_and, clauseSatisfied, Fin.exists_fin_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
          IsEmpty.exists_iff,
      Bool.decide_or, Bool.or_eq_true]

theorem mem_paperSourceNormalizedClauses_iff
    (formula : ThreeCNF) (normalized : List Literal) :
    normalized ∈ paperSourceNormalizedClauses formula ↔
      ∃ clause ∈ noTautClauses formula,
        paperSourceNormalizedClause clause = normalized := by
  simp only [paperSourceNormalizedClauses, List.mem_map]

theorem paperSourceNormalizedClauses_satisfied_iff
    (formula : ThreeCNF) (assignment : ℕ → Bool) :
    (∀ clause ∈ paperSourceNormalizedClauses formula,
      ∃ literal ∈ clause, literalSatisfied assignment literal) ↔
      (∀ clause ∈ formula, clauseSatisfied assignment clause) := by
  constructor
  · intro hnormalized
    apply (sourceClausesWithoutTautologies_satisfied_iff
      formula assignment).mp
    intro clause hretained
    apply (paperSourceNormalizedClause_satisfied_iff
      assignment clause).mp
    apply hnormalized
    exact (mem_paperSourceNormalizedClauses_iff
      formula (paperSourceNormalizedClause clause)).mpr
      ⟨clause, hretained, rfl⟩
  · intro horiginal normalized hnormalized
    obtain ⟨clause, hretained, rfl⟩ :=
      (mem_paperSourceNormalizedClauses_iff
        formula normalized).mp hnormalized
    apply (paperSourceNormalizedClause_satisfied_iff
      assignment clause).mpr
    exact (sourceClausesWithoutTautologies_satisfied_iff
      formula assignment).mpr horiginal clause hretained

private theorem mem_paperSourceNormalizedVariables_iff
    (formula : ThreeCNF) (name : ℕ) :
    name ∈ paperSourceNormalizedVariables formula ↔
      ∃ clause ∈ noTautClauses formula,
        ∃ index : Fin 3, (clause index).1 = name := by
  constructor
  · intro hname
    obtain ⟨normalized, hnormalized, hmember⟩ :=
      List.mem_flatMap.mp hname
    obtain ⟨clause, hclause, rfl⟩ :=
      (mem_paperSourceNormalizedClauses_iff
        formula normalized).mp hnormalized
    obtain ⟨literal, hliteral, rfl⟩ := List.mem_map.mp hmember
    obtain ⟨index, hindex⟩ :=
      (mem_paperSourceNormalizedClause_iff clause literal).mp hliteral
    exact ⟨clause, hclause, index, congrArg Prod.fst hindex⟩
  · rintro ⟨clause, hclause, index, hindex⟩
    apply List.mem_flatMap.mpr
    refine ⟨paperSourceNormalizedClause clause,
      (mem_paperSourceNormalizedClauses_iff
        formula (paperSourceNormalizedClause clause)).mpr
          ⟨clause, hclause, rfl⟩, ?_⟩
    exact List.mem_map.mpr
      ⟨clause index,
        (mem_paperSourceNormalizedClause_iff
          clause (clause index)).mpr ⟨index, rfl⟩,
        hindex⟩

theorem mem_paperSourceNormalizedOccurringVariables_iff
    (formula : ThreeCNF) (name : ℕ) :
    name ∈ paperNormalizedOccurringVariables formula ↔
      ∃ clause ∈ noTautClauses formula,
        ∃ index : Fin 3, (clause index).1 = name := by
  simp only [paperNormalizedOccurringVariables, List.mem_eraseDups,
      mem_paperSourceNormalizedVariables_iff]

theorem paperSourceNormalizedOccurringVariables_nodup
    (formula : ThreeCNF) :
    (paperNormalizedOccurringVariables formula).Nodup := by
  exact eraseDups_nodup (paperSourceNormalizedVariables formula)

end SourcePreprocessingSemantics

namespace FormulaBridge

open GapCVP.Factor400FormulaBridge GapCVP.SourcePreprocessingSemantics
open GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.BinaryExplicitAffineSystem
open GapCVP.BinaryExplicitSourceSoundness

/-- GapCVP reduction support. -/
def paperVariableArityVariableCount (formula : ThreeCNF) : ℕ :=
  (paperNormalizedOccurringVariables formula).length

/-- GapCVP reduction support. -/
def paperVariableArityVariableRank
    (formula : ThreeCNF) (name : ℕ) : ℕ :=
  (paperNormalizedOccurringVariables formula).idxOf name

theorem paperVariableArityVariableRank_lt
    (formula : ThreeCNF) (clause : List Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula)
    (literal : Literal) (hliteral : literal ∈ clause) :
    paperVariableArityVariableRank formula literal.1 <
      paperVariableArityVariableCount formula := by
  unfold paperVariableArityVariableRank paperVariableArityVariableCount
  apply List.idxOf_lt_length_of_mem
  simp only [paperNormalizedOccurringVariables,
    List.mem_eraseDups]
  unfold paperSourceNormalizedVariables
  apply List.mem_flatMap.mpr
  exact ⟨clause, hclause,
    List.mem_map.mpr ⟨literal, hliteral, rfl⟩⟩

/-- GapCVP reduction support. -/
def paperVariableAritySourceLiteral
    (formula : ThreeCNF) (clause : List Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula)
    (literal : Literal) (hliteral : literal ∈ clause) :
    GapCVP.Core.Literal (paperVariableArityVariableCount formula) where
  variableIndex :=
    ⟨paperVariableArityVariableRank formula literal.1,
      paperVariableArityVariableRank_lt
        formula clause hclause literal hliteral⟩
  satisfyingValue := literal.2

theorem paper_retainedClause_length_le_three
    (formula : ThreeCNF) (clause : List Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula) :
    clause.length ≤ 3 := by
  obtain ⟨original, _, horiginal⟩ :=
    (mem_paperSourceNormalizedClauses_iff formula clause).mp hclause
  rw [← horiginal]
  exact paperNormalizedClause_length_le_three original

/-- GapCVP reduction support. -/
def paperVariableAritySourceClause
    (formula : ThreeCNF) (clause : List Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula) :
    GapCVP.Core.Clause (paperVariableArityVariableCount formula) where
  literals :=
    (clause.attach.map fun item =>
      paperVariableAritySourceLiteral
        formula clause hclause item.val item.property).toFinset
  nonempty := by
    obtain ⟨original, hretained, horiginal⟩ :=
      (mem_paperSourceNormalizedClauses_iff formula clause).mp hclause
    have hfirst : original 0 ∈ clause := by
      rw [← horiginal]
      simp only [paperSourceNormalizedClause, paperSourceClauseLiterals, Fin.isValue,
          List.mem_eraseDups,
          List.mem_cons, List.not_mem_nil, or_false, true_or]
    refine ⟨paperVariableAritySourceLiteral
      formula clause hclause (original 0) hfirst, ?_⟩
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨⟨original 0, hfirst⟩, List.mem_attach _ _, rfl⟩
  size_le_three := by
    calc
      (clause.attach.map fun item =>
        paperVariableAritySourceLiteral
          formula clause hclause item.val item.property).toFinset.card ≤
          (clause.attach.map fun item =>
            paperVariableAritySourceLiteral
              formula clause hclause item.val item.property).length :=
        List.toFinset_card_le _
      _ = clause.length := by simp only [List.length_map, List.length_attach]
      _ ≤ 3 := paper_retainedClause_length_le_three
        formula clause hclause

/-- GapCVP reduction support. -/
abbrev srcFormula (formula : ThreeCNF) :
    GapCVP.Core.Formula where
  variableCount := paperVariableArityVariableCount formula
  clauses :=
    (paperSourceNormalizedClauses formula).attach.map fun item =>
      paperVariableAritySourceClause
        formula item.val item.property

@[simp] theorem paperVariableAritySourceFormula_variableCount
    (formula : ThreeCNF) :
    (srcFormula formula).variableCount =
      paperVariableArityVariableCount formula := by
  rfl

theorem paperVariableAritySourceFormula_clauses_length
    (formula : ThreeCNF) :
    (srcFormula formula).clauses.length =
      (noTautClauses formula).length := by
  simp only [srcFormula, paperSourceNormalizedClauses, List.length_map, List.length_attach]

private theorem paperVariableAritySourceClause_mem
    (formula : ThreeCNF) (clause : List Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula) :
    paperVariableAritySourceClause formula clause hclause ∈
      (srcFormula formula).clauses := by
  change paperVariableAritySourceClause formula clause hclause ∈
    (paperSourceNormalizedClauses formula).attach.map
      (fun item => paperVariableAritySourceClause
        formula item.val item.property)
  exact List.mem_map.mpr
    ⟨⟨clause, hclause⟩, List.mem_attach _ _, rfl⟩

private theorem paperVariableAritySourceClause_satisfied_iff
    (formula : ThreeCNF) (clause : List Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula)
    (assignment : Fin (paperVariableArityVariableCount formula) → Bool) :
    (paperVariableAritySourceClause formula clause hclause).Satisfied
        assignment ↔
      ∃ literal : Literal, ∃ hliteral : literal ∈ clause,
        assignment
            (paperVariableAritySourceLiteral
              formula clause hclause literal hliteral).variableIndex =
          literal.2 := by
  simp only [GapCVP.Core.Clause.Satisfied, decide_eq_true_eq]
  constructor
  · rintro ⟨sourceLiteral, hsource, hsatisfied⟩
    simp only [paperVariableAritySourceClause] at hsource
    have hlist : sourceLiteral ∈
        clause.attach.map (fun item =>
          paperVariableAritySourceLiteral
            formula clause hclause item.val item.property) := by
      exact List.mem_toFinset.mp hsource
    obtain ⟨item, _, rfl⟩ := List.mem_map.mp hlist
    refine ⟨item.val, item.property, ?_⟩
    exact hsatisfied
  · rintro ⟨literal, hliteral, hsatisfied⟩
    refine ⟨paperVariableAritySourceLiteral
      formula clause hclause literal hliteral, ?_, ?_⟩
    · simp only [paperVariableAritySourceClause]
      exact List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨⟨literal, hliteral⟩,
          List.mem_attach _ _, rfl⟩)
    · change
        assignment (paperVariableAritySourceLiteral
          formula clause hclause literal hliteral).variableIndex =
            literal.2
      exact hsatisfied

private def paperVariableArityCompactAssignment
    (formula : ThreeCNF) (assignment : ℕ → Bool)
    (index : Fin (paperVariableArityVariableCount formula)) : Bool :=
  assignment ((paperNormalizedOccurringVariables formula).get index)

private theorem paperVariableArityCompactAssignment_literal
    (formula : ThreeCNF) (clause : List Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula)
    (literal : Literal) (hliteral : literal ∈ clause)
    (assignment : ℕ → Bool) :
    paperVariableArityCompactAssignment formula assignment
        (paperVariableAritySourceLiteral
          formula clause hclause literal hliteral).variableIndex =
      assignment literal.1 := by
  unfold paperVariableArityCompactAssignment
    paperVariableAritySourceLiteral paperVariableArityVariableRank
  congr 1
  exact List.idxOf_get
    (paperVariableArityVariableRank_lt
      formula clause hclause literal hliteral)

private def paperExpandedAssignment
    (formula : ThreeCNF)
    (assignment : Fin (paperVariableArityVariableCount formula) → Bool) :
    ℕ → Bool := fun name =>
      if h : paperVariableArityVariableRank formula name <
          paperVariableArityVariableCount formula then
        assignment ⟨paperVariableArityVariableRank formula name, h⟩
      else
        false

private theorem paperVariableArityExpandedAssignment_literal
    (formula : ThreeCNF) (clause : List Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula)
    (literal : Literal) (hliteral : literal ∈ clause)
    (assignment : Fin (paperVariableArityVariableCount formula) → Bool) :
    paperExpandedAssignment formula assignment literal.1 =
      assignment
        (paperVariableAritySourceLiteral
          formula clause hclause literal hliteral).variableIndex := by
  simp only [paperExpandedAssignment, paperVariableArityVariableRank_lt formula clause hclause
      literal hliteral,
      ↓reduceDIte, paperVariableAritySourceLiteral]

theorem sourceFormula_satisfiable_iff
    (formula : ThreeCNF) :
    (srcFormula formula).Satisfiable ↔
      ∃ assignment : ℕ → Bool,
        ∀ clause ∈ formula, clauseSatisfied assignment clause := by
  simp only [GapCVP.Core.Formula.Satisfiable, decide_eq_true_eq]
  constructor
  · rintro ⟨assignment, hsatisfied⟩
    refine ⟨paperExpandedAssignment formula assignment, ?_⟩
    apply (paperSourceNormalizedClauses_satisfied_iff
      formula (paperExpandedAssignment
        formula assignment)).mp
    intro clause hclause
    have hsource :=
      (formula_satisfied_iff_forall_mem
        (srcFormula formula) assignment).mp
        hsatisfied (paperVariableAritySourceClause
          formula clause hclause)
        (paperVariableAritySourceClause_mem formula clause hclause)
    obtain ⟨literal, hliteral, hliteralSatisfied⟩ :=
      (paperVariableAritySourceClause_satisfied_iff
        formula clause hclause assignment).mp hsource
    refine ⟨literal, hliteral, ?_⟩
    simp only [GapCVP.literalSatisfied, decide_eq_true_eq]
    rw [paperVariableArityExpandedAssignment_literal
      formula clause hclause literal hliteral assignment]
    exact hliteralSatisfied
  · rintro ⟨assignment, hsatisfied⟩
    refine ⟨paperVariableArityCompactAssignment
      formula assignment, ?_⟩
    apply (formula_satisfied_iff_forall_mem
      (srcFormula formula)
        (paperVariableArityCompactAssignment formula assignment)).mpr
    intro sourceClause hsourceClause
    change sourceClause ∈
      (paperSourceNormalizedClauses formula).attach.map
        (fun item => paperVariableAritySourceClause
          formula item.val item.property) at hsourceClause
    obtain ⟨item, _, rfl⟩ := List.mem_map.mp hsourceClause
    apply (paperVariableAritySourceClause_satisfied_iff
      formula item.val item.property
        (paperVariableArityCompactAssignment formula assignment)).mpr
    have hnormalized :=
      (paperSourceNormalizedClauses_satisfied_iff
        formula assignment).mpr hsatisfied
        item.val item.property
    obtain ⟨literal, hliteral, hliteralSatisfied⟩ := hnormalized
    refine ⟨literal, hliteral, ?_⟩
    rw [paperVariableArityCompactAssignment_literal
      formula item.val item.property literal hliteral assignment]
    simp only [GapCVP.literalSatisfied, decide_eq_true_eq] at hliteralSatisfied
    exact hliteralSatisfied

/-- GapCVP reduction support. -/
noncomputable abbrev paperExplicitBinarySystem
    (encodingLength : ℕ) (formula : ThreeCNF) :
    GapCVP.Core.BinaryAffineSystem :=
  sourceFormulaExplicitBinarySystem
    encodingLength (srcFormula formula)

theorem paperVariableArityExplicitBinarySystem_signedSolution_of_satisfiable
    (encodingLength : ℕ) (formula : ThreeCNF)
    (hsatisfiable : ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    ∃ vector : Fin
        (sourceFormulaDimension encodingLength
          (srcFormula formula)) → ℤ,
      (paperExplicitBinarySystem
        encodingLength formula).Solves vector ∧
      (GapCVP.Core.integerSquaredNorm vector : ℝ) ≤
        ((GapCVP.Core.sourceOneHotCompletenessRadius
          (srcFormula formula)
          (sourceFormulaGrid encodingLength
            (srcFormula formula)) : ℚ) : ℝ) ^ 2 := by
  have hformula :=
    (sourceFormula_satisfiable_iff formula).mpr hsatisfiable
  obtain ⟨vector, hsolve, hbound⟩ :=
    sourceFormulaExplicitBinarySystem_signedSolution_of_satisfiable
      encodingLength (srcFormula formula) hformula
  exact ⟨vector, hsolve, hbound⟩

end FormulaBridge

namespace Factor400BinaryDecodingPromiseReduction

open scoped BigOperators

open GapCVP.Factor400BinaryCodeDecodingCorollary GapCVP.BinaryEncoding

theorem binaryField_zero_or_one (value : ZMod 2) :
    value = 0 ∨ value = 1 := by
  exact GapCVP.Core.effectiveBinary_eq_zero_or_one value

theorem integerSquaredNorm_binaryWordLift
    {n : ℕ} (word : Fin n → ZMod 2) :
    GapCVP.Core.integerSquaredNorm (binaryWordLift word) =
      hammingNorm word := by
  classical
  unfold GapCVP.Core.integerSquaredNorm binaryWordLift hammingNorm
  simp_rw [Int.natAbs_natCast]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro index _
  rcases binaryField_zero_or_one (word index) with hzero | hone
  · simp only [hzero, ZMod.val_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      not_true_eq_false,
        ↓reduceIte]
  · simp only [hone, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte, pow_eq_one_iff,
      OfNat.ofNat_ne_zero,
        or_false]
    exact ZMod.val_natCast_of_lt (by norm_num : 1 < (2 : ℕ))

theorem sourceOneHotSignedTable_zero_or_one
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (formula : GapCVP.Core.Formula) (points : Finset K)
    (assignment : Fin formula.variableCount → Bool)
    (hsatisfies : formula.Satisfied assignment)
    (interpolant : Polynomial K)
    (index : Fin (GapCVP.Core.sourceSATTableDimension formula K points)) :
    GapCVP.Core.sourceOneHotSignedTable
      formula points assignment hsatisfies interpolant index = 0 ∨
    GapCVP.Core.sourceOneHotSignedTable
        formula points assignment hsatisfies interpolant index = 1 := by
  classical
  let coordinate :=
    (Fintype.equivFin
      (GapCVP.Core.sourceSATTableCoordinate formula K points)).symm index
  cases htype : coordinate.1 with
  | inl global =>
      by_cases hvalue :
        coordinate.2.2 = interpolant.eval coordinate.2.1.val
      · right
        simp only [Core.sourceOneHotSignedTable, htype, List.get_eq_getElem, hvalue, ↓reduceIte,
            coordinate]
      · left
        simp only [Core.sourceOneHotSignedTable, htype, List.get_eq_getElem, hvalue, ↓reduceIte,
            coordinate]
  | inr subtype =>
      by_cases hactive :
        subtype.2 = GapCVP.Core.sourceActiveLocalTuple
          formula assignment hsatisfies subtype.1
      · by_cases hvalue :
          coordinate.2.2 = interpolant.eval coordinate.2.1.val
        · right
          simp only [Core.sourceOneHotSignedTable, htype, List.get_eq_getElem, hactive, hvalue,
              and_self, ↓reduceIte,
              coordinate]
        · left
          simp only [Core.sourceOneHotSignedTable, htype, List.get_eq_getElem, hactive, hvalue,
              and_false, ↓reduceIte,
              coordinate]
      · left
        simp only [Core.sourceOneHotSignedTable, htype, List.get_eq_getElem, hactive, false_and,
            ↓reduceIte,
            coordinate]

/-- GapCVP reduction support. -/
structure BinaryNearestCodewordInstance where
  /-- GapCVP reduction support. -/
  blockLength : ℕ
  /-- GapCVP reduction support. -/
  generatorRank : ℕ
  /-- GapCVP reduction support. -/
  generator : Fin blockLength → Fin generatorRank → ZMod 2
  /-- GapCVP reduction support. -/
  target : Fin blockLength → ZMod 2
  /-- GapCVP reduction support. -/
  radius : ℕ

/-- GapCVP reduction support. -/
structure BinarySyndromeDecodingInstance where
  /-- GapCVP reduction support. -/
  checkCount : ℕ
  /-- GapCVP reduction support. -/
  blockLength : ℕ
  /-- GapCVP reduction support. -/
  parityCheck : Fin checkCount → Fin blockLength → ZMod 2
  /-- GapCVP reduction support. -/
  syndrome : Fin checkCount → ZMod 2
  /-- GapCVP reduction support. -/
  radius : ℕ

theorem binaryIntegerLift_zero : ((0 : ZMod 2).val : ℤ) = 0 := by
  simp only [ZMod.val_zero, CharP.cast_eq_zero]

theorem binaryIntegerLift_one : ((1 : ZMod 2).val : ℤ) = 1 := by
  rw [ZMod.val_one 2]
  norm_num

theorem binaryIntegerLift_two : ((2 : ZMod 2).val : ℤ) = 0 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, binaryIntegerLift_zero]

private theorem binaryIntegerLift_cast (value : ZMod 2) :
    ((value.val : ℤ) : ZMod 2) = value := by
  rw [Int.cast_natCast]
  exact ZMod.natCast_zmod_val value

private theorem binaryIntegerLift_zero_or_one (value : ZMod 2) :
    (value.val : ℤ) = 0 ∨ (value.val : ℤ) = 1 := by
  rcases binaryField_zero_or_one value with hzero | hone
  · left
    simp only [hzero, ZMod.val_zero, CharP.cast_eq_zero]
  · right
    simp only [hone, binaryIntegerLift_one]

theorem binaryIntegerLift_intCast_of_zero_or_one
    {value : ℤ} (hvalue : value = 0 ∨ value = 1) :
    ((value : ZMod 2).val : ℤ) = value := by
  rcases hvalue with hzero | hone
  · simp only [hzero, Int.cast_zero, binaryIntegerLift_zero]
  · simp only [hone, Int.cast_one, binaryIntegerLift_one]

private def binaryVectorOfIntegers {n : ℕ} (values : Fin n → ℤ) :
    Option (Fin n → ZMod 2) :=
  if ∀ index, values index = 0 ∨ values index = 1 then
    some (fun index => (values index : ZMod 2))
  else
    none

private def binaryMatrixOfIntegers {m n : ℕ}
    (values : Fin m → Fin n → ℤ) :
    Option (Fin m → Fin n → ZMod 2) :=
  if ∀ row column, values row column = 0 ∨ values row column = 1 then
    some (fun row column => (values row column : ZMod 2))
  else
    none

private theorem binaryVectorOfIntegers_lift {n : ℕ}
    (values : Fin n → ZMod 2) :
    binaryVectorOfIntegers (fun index => ((values index).val : ℤ)) =
      some values := by
  simp only [binaryVectorOfIntegers, binaryIntegerLift_zero_or_one, implies_true, ↓reduceIte,
      binaryIntegerLift_cast]

private theorem binaryMatrixOfIntegers_lift {m n : ℕ}
    (values : Fin m → Fin n → ZMod 2) :
    binaryMatrixOfIntegers
        (fun row column => ((values row column).val : ℤ)) =
      some values := by
  simp only [binaryMatrixOfIntegers, binaryIntegerLift_zero_or_one, implies_true, ↓reduceIte,
      binaryIntegerLift_cast]

/-- GapCVP reduction support. -/
def encodeBinaryNearestCodewordInstance
    (record : BinaryNearestCodewordInstance) : List Bool :=
  encodeAtomic record.blockLength ++
    encodeAtomic record.generatorRank ++
    encodeAtomic record.radius ++
    encodeFinValues record.blockLength
      (fun index => ((record.target index).val : ℤ)) ++
    encodeMatrixRows record.blockLength record.generatorRank
      (fun row column => ((record.generator row column).val : ℤ))

/-- GapCVP reduction support. -/
def encodeBinarySyndromeDecodingInstance
    (record : BinarySyndromeDecodingInstance) : List Bool :=
  encodeAtomic record.checkCount ++
    encodeAtomic record.blockLength ++
    encodeAtomic record.radius ++
    encodeFinValues record.checkCount
      (fun row => ((record.syndrome row).val : ℤ)) ++
    encodeMatrixRows record.checkCount record.blockLength
      (fun row column => ((record.parityCheck row column).val : ℤ))

/-- GapCVP reduction support. -/
def decodeBinaryNearestCodewordInstance
    (bits : List Bool) : Option BinaryNearestCodewordInstance :=
  match (readAtomic bits : Option (ℕ × List Bool)) with
  | none => none
  | some (blockLength, tail) =>
    match (readAtomic tail : Option (ℕ × List Bool)) with
    | none => none
    | some (generatorRank, tail) =>
      match (readAtomic tail : Option (ℕ × List Bool)) with
      | none => none
      | some (radius, tail) =>
        match (readFinValues blockLength tail :
          Option ((Fin blockLength → ℤ) × List Bool)) with
        | none => none
        | some (target, tail) =>
          match binaryVectorOfIntegers target with
          | none => none
          | some target =>
            match readMatrixRows blockLength generatorRank tail with
            | some (generator, []) =>
              match binaryMatrixOfIntegers generator with
              | some generator =>
                some ⟨blockLength, generatorRank, generator, target, radius⟩
              | none => none
            | _ => none

/-- GapCVP reduction support. -/
def decodeBinarySyndromeDecodingInstance
    (bits : List Bool) : Option BinarySyndromeDecodingInstance :=
  match (readAtomic bits : Option (ℕ × List Bool)) with
  | none => none
  | some (checkCount, tail) =>
    match (readAtomic tail : Option (ℕ × List Bool)) with
    | none => none
    | some (blockLength, tail) =>
      match (readAtomic tail : Option (ℕ × List Bool)) with
      | none => none
      | some (radius, tail) =>
        match (readFinValues checkCount tail :
          Option ((Fin checkCount → ℤ) × List Bool)) with
        | none => none
        | some (syndrome, tail) =>
          match binaryVectorOfIntegers syndrome with
          | none => none
          | some syndrome =>
            match readMatrixRows checkCount blockLength tail with
            | some (parityCheck, []) =>
              match binaryMatrixOfIntegers parityCheck with
              | some parityCheck =>
                some ⟨checkCount, blockLength, parityCheck, syndrome, radius⟩
              | none => none
            | _ => none

@[simp] theorem decodeBinaryNearestCodewordInstance_encode
    (record : BinaryNearestCodewordInstance) :
    decodeBinaryNearestCodewordInstance
      (encodeBinaryNearestCodewordInstance record) = some record := by
  cases record with
  | mk blockLength generatorRank generator target radius =>
    have hmatrix :
        readMatrixRows blockLength generatorRank
          (encodeMatrixRows blockLength generatorRank
            (fun row column => ((generator row column).val : ℤ))) =
            some ((fun row column => ((generator row column).val : ℤ)), []) := by
      simpa only [List.append_nil] using
          (readMatrixRows_append (fun row column => ((generator row column).val : ℤ)) [])
    simp only [decodeBinaryNearestCodewordInstance, encodeBinaryNearestCodewordInstance,
        List.append_assoc,
        readAtomic_append, readFinValues_append, binaryVectorOfIntegers_lift, hmatrix,
            binaryMatrixOfIntegers_lift]

@[simp] theorem decodeBinarySyndromeDecodingInstance_encode
    (record : BinarySyndromeDecodingInstance) :
    decodeBinarySyndromeDecodingInstance
      (encodeBinarySyndromeDecodingInstance record) = some record := by
  cases record with
  | mk checkCount blockLength parityCheck syndrome radius =>
    have hmatrix :
        readMatrixRows checkCount blockLength
          (encodeMatrixRows checkCount blockLength
            (fun row column => ((parityCheck row column).val : ℤ))) =
            some ((fun row column => ((parityCheck row column).val : ℤ)), []) := by
      simpa only [List.append_nil] using
          (readMatrixRows_append (fun row column => ((parityCheck row column).val : ℤ)) [])
    simp only [decodeBinarySyndromeDecodingInstance, encodeBinarySyndromeDecodingInstance,
        List.append_assoc,
        readAtomic_append, readFinValues_append, binaryVectorOfIntegers_lift, hmatrix,
            binaryMatrixOfIntegers_lift]

/-- GapCVP reduction support. -/
def binaryNearestCodeword
    (record : BinaryNearestCodewordInstance)
    (coefficients : Fin record.generatorRank → ZMod 2) :
    Fin record.blockLength → ZMod 2 :=
  fun index => ∑ column : Fin record.generatorRank,
    record.generator index column * coefficients column

/-- GapCVP reduction support. -/
def binaryNearestTarget (record : BinaryNearestCodewordInstance) :
    Fin record.blockLength → ZMod 2 :=
  record.target

/-- GapCVP reduction support. -/
def binarySyndromeProduct
    (record : BinarySyndromeDecodingInstance)
    (word : Fin record.blockLength → ZMod 2) :
    Fin record.checkCount → ZMod 2 :=
  fun row => ∑ column : Fin record.blockLength,
    record.parityCheck row column * word column

/-- GapCVP reduction support. -/
def binarySyndromeTarget (record : BinarySyndromeDecodingInstance) :
    Fin record.checkCount → ZMod 2 :=
  record.syndrome

end Factor400BinaryDecodingPromiseReduction


end GapCVP

end
