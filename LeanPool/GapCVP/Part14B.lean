/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part14A

/-! # GapCVP proof, part 14, continuation 02 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine

section

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert

open GapCVP.SourceStructuralTuringTM GapCVP.SourceMixedRadixDimensionRowMajorIndexTM

open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.SourceMixedRadixUnaryQuotientRemainderTM

open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM

open GapCVP.CNFCappedUnaryPairArithmeticTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM

open GapCVP.GaussianPivotScheduleTM GapCVP.GaussianRowWorker GapCVP.BinaryFieldBasis

open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceFieldMultiplicationTM

open GapCVP.BinarySourceConvolutionTM GapCVP.BinarySourceConvolutionCorrectness

open GapCVP.BinarySelectedIrreducibleWordTM GapCVP.BinarySelectedIrreducibleWordOrderCorrectness

open GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM GapCVP.Core.EffectiveBinaryField

private def sourceIrreducibleCandidateQuery
    (input : List Bool) (rank : ℕ) : List Bool :=
  lengthPrefixedWord (List.replicate rank true) ++
    sourceQaryMaskDynamicGridBaseSource
      sourceIrreducibleCandidateWidth input

private def sourceIrreducibleCandidateCardinalityUnary :
    List Bool → List Bool :=
  physicalFamilyFieldCardinalityUnary ∘
    binaryIrreducibleRankOriginal

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleCandidateCardinalityComputable :
    BitTM
      sourceIrreducibleCandidateCardinalityUnary :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    factor400BinaryIrreducibleRankOriginalComputable
    paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable

private def paperVariableAritySourceIrreducibleFactorPairWidthOutput :
    List Bool → List Bool :=
  (fun input : List Bool =>
    List.replicate ((Polynomial.X ^ 2).eval input.length) true) ∘
      sourceIrreducibleCandidateCardinalityUnary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorPairWidthComputable :
    BitTM
      paperVariableAritySourceIrreducibleFactorPairWidthOutput :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    paperVariableAritySourceIrreducibleCandidateCardinalityComputable
    factor400BinaryIrreduciblePhysicalSquareComputer

private noncomputable def sourceIrreducibleFactorPairWidth :
    SourceQaryMaskDynamicGridWidth :=
  factor400BinaryIrreduciblePhysicalDynamicWidth
    paperVariableAritySourceIrreducibleFactorPairWidthComputable

private abbrev sourceIrreducibleFactorPairOriginalSource :
    List Bool → List Bool :=
  factor400BinarySourceIrreducibleFactorPairOriginalSource

private def sourceIrreducibleFactorPairCardinalityUnary :
    List Bool → List Bool :=
  physicalFamilyFieldCardinalityUnary ∘
    sourceIrreducibleFactorPairOriginalSource

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorPairCardinalityComputable :
    BitTM
      sourceIrreducibleFactorPairCardinalityUnary :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    factor400BinarySourceIrreducibleFactorPairOriginalSourceComputable
    paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable

private def sourceIrreducibleFactorPairDivisionQuery
    (input : List Bool) : List Bool :=
  firstFieldContents input ++ false ::
    (sourceIrreducibleFactorPairCardinalityUnary input ++
      false :: sourceIrreducibleFactorPairOriginalSource input)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorPairDivisionQueryComputable :
    BitTM
      sourceIrreducibleFactorPairDivisionQuery := by
  have hsource := factor400BinaryIrreduciblePhysicalCompositionComputer
    factor400BinarySourceIrreducibleFactorPairOriginalSourceComputable
    (prependBitComputable false)
  have hcardinality := factor400BinaryIrreduciblePhysicalAppendComputer
    paperVariableAritySourceIrreducibleFactorPairCardinalityComputable hsource
  have hseparator := factor400BinaryIrreduciblePhysicalCompositionComputer
    hcardinality (prependBitComputable false)
  exact factor400BinaryIrreduciblePhysicalAppendComputer
    firstFieldContentsComputable hseparator

private def sourceIrreducibleFactorPairOdometer :
    List Bool → List Bool :=
  sourceMixedRadixRowMajorPairOutput ∘
    sourceIrreducibleFactorPairDivisionQuery

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorPairOdometerComputable :
    BitTM
      sourceIrreducibleFactorPairOdometer :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    paperVariableAritySourceIrreducibleFactorPairDivisionQueryComputable
    sourceMixedRadixRowMajorPairComputable

private def sourceIrreducibleFactorPairFirstRank
    (input : List Bool) : List Bool :=
  (unaryPrefixOutput
    (sourceIrreducibleFactorPairOdometer input)).tail

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorPairFirstRankComputable :
    BitTM
      sourceIrreducibleFactorPairFirstRank := by
  have hprefix := factor400BinaryIrreduciblePhysicalCompositionComputer
    paperVariableAritySourceIrreducibleFactorPairOdometerComputable
    unaryPrefixComputable
  exact factor400BinaryIrreduciblePhysicalCompositionComputer
    hprefix factor400BinaryIrreduciblePhysicalDropHeadComputer

private def sourceIrreducibleFactorPairSecondRank
    (input : List Bool) : List Bool :=
  (unaryPrefixOutput (unaryPrefixSuffixOutput
    (sourceIrreducibleFactorPairOdometer input))).tail

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorPairSecondRankComputable :
    BitTM
      sourceIrreducibleFactorPairSecondRank := by
  have hsuffix := factor400BinaryIrreduciblePhysicalCompositionComputer
    paperVariableAritySourceIrreducibleFactorPairOdometerComputable
    actualUnaryPrefixSuffixComputable
  have hprefix := factor400BinaryIrreduciblePhysicalCompositionComputer
    hsuffix unaryPrefixComputable
  exact factor400BinaryIrreduciblePhysicalCompositionComputer
    hprefix factor400BinaryIrreduciblePhysicalDropHeadComputer

private def sourceIrreducibleFactorRankQuery
    (rank : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  binaryIrreduciblePhysicalComputedPrefixOutput rank input ++
    (binaryIrreduciblePhysicalComputedPrefixOutput
      sourceIrreducibleFactorPairCardinalityUnary input ++
        sourceIrreducibleFactorPairOriginalSource input)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorRankQueryComputable
    {rank : List Bool → List Bool}
    (computer : BitTM rank) :
    BitTM
      (sourceIrreducibleFactorRankQuery rank) :=
  factor400BinaryIrreduciblePhysicalAppendComputer
    (factor400BinaryIrreduciblePhysicalComputedPrefixComputer computer)
    (factor400BinaryIrreduciblePhysicalAppendComputer
      (factor400BinaryIrreduciblePhysicalComputedPrefixComputer
        paperVariableAritySourceIrreducibleFactorPairCardinalityComputable)
      factor400BinarySourceIrreducibleFactorPairOriginalSourceComputable)

private def sourceIrreducibleFactorPairLowerWord :
    List Bool → List Bool :=
  sourceIrreducibleRankCoefficientWord ∘
    binarySourceIrreducibleFactorPairCandidateSource

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorPairLowerWordComputable :
    BitTM
      sourceIrreducibleFactorPairLowerWord :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    factor400BinarySourceIrreducibleFactorPairCandidateSourceComputable
    paperVariableAritySourceIrreducibleRankCoefficientWordComputable

private def sourceIrreducibleFactorPairFirstWord :
    List Bool → List Bool :=
  sourceIrreducibleRankCoefficientWord ∘
    sourceIrreducibleFactorRankQuery
      sourceIrreducibleFactorPairFirstRank

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorPairFirstWordComputable :
    BitTM
      sourceIrreducibleFactorPairFirstWord :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    (paperVariableAritySourceIrreducibleFactorRankQueryComputable
      paperVariableAritySourceIrreducibleFactorPairFirstRankComputable)
    paperVariableAritySourceIrreducibleRankCoefficientWordComputable

private def sourceIrreducibleFactorPairSecondWord :
    List Bool → List Bool :=
  sourceIrreducibleRankCoefficientWord ∘
    sourceIrreducibleFactorRankQuery
      sourceIrreducibleFactorPairSecondRank

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorPairSecondWordComputable :
    BitTM
      sourceIrreducibleFactorPairSecondWord :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    (paperVariableAritySourceIrreducibleFactorRankQueryComputable
      paperVariableAritySourceIrreducibleFactorPairSecondRankComputable)
    paperVariableAritySourceIrreducibleRankCoefficientWordComputable

private def sourceIrreducibleFactorPairProductQuery
    (input : List Bool) : List Bool :=
  binaryIrreduciblePhysicalComputedPrefixOutput
      sourceIrreducibleFactorPairLowerWord input ++
    (binaryIrreduciblePhysicalComputedPrefixOutput
        sourceIrreducibleFactorPairFirstWord input ++
      (binaryIrreduciblePhysicalComputedPrefixOutput
          sourceIrreducibleFactorPairSecondWord input ++
        sourceIrreducibleFactorPairOriginalSource input))

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorPairProductQueryComputable :
    BitTM
      sourceIrreducibleFactorPairProductQuery :=
  factor400BinaryIrreduciblePhysicalAppendComputer
    (factor400BinaryIrreduciblePhysicalComputedPrefixComputer
      paperVariableAritySourceIrreducibleFactorPairLowerWordComputable)
    (factor400BinaryIrreduciblePhysicalAppendComputer
      (factor400BinaryIrreduciblePhysicalComputedPrefixComputer
        paperVariableAritySourceIrreducibleFactorPairFirstWordComputable)
      (factor400BinaryIrreduciblePhysicalAppendComputer
        (factor400BinaryIrreduciblePhysicalComputedPrefixComputer
          paperVariableAritySourceIrreducibleFactorPairSecondWordComputable)
        factor400BinarySourceIrreducibleFactorPairOriginalSourceComputable))

private def sourceIrreducibleFactorPairProductWord :
    List Bool → List Bool :=
  binarySourceRawConvolutionWord ∘
    sourceIrreducibleFactorPairProductQuery

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorPairProductWordComputable :
    BitTM
      sourceIrreducibleFactorPairProductWord :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    paperVariableAritySourceIrreducibleFactorPairProductQueryComputable
    factor400BinaryIrreduciblePhysicalConvolutionComputer

private def sourceIrreducibleFactorPairDegreeUnary :
    List Bool → List Bool :=
  physicalFamilyFieldDegreeUnary ∘
    sourceIrreducibleFactorPairOriginalSource

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorPairDegreeUnaryComputable :
    BitTM
      sourceIrreducibleFactorPairDegreeUnary :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    factor400BinarySourceIrreducibleFactorPairOriginalSourceComputable
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable

private def paperVariableAritySourceIrreducibleMonicZeroWidthOutput
    (input : List Bool) : List Bool :=
  (sourceIrreducibleFactorPairDegreeUnary input).tail

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleMonicZeroWidthComputable :
    BitTM
      paperVariableAritySourceIrreducibleMonicZeroWidthOutput :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    paperVariableAritySourceIrreducibleFactorPairDegreeUnaryComputable
    factor400BinaryIrreduciblePhysicalDropHeadComputer

private noncomputable def sourceIrreducibleMonicZeroWidth :
    SourceQaryMaskDynamicGridWidth :=
  factor400BinaryIrreduciblePhysicalDynamicWidth
    paperVariableAritySourceIrreducibleMonicZeroWidthComputable

private def sourceIrreducibleMonicZeroWord :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    sourceIrreducibleMonicZeroWidth
    factor400BinaryIrreduciblePhysicalFalseComputer

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleMonicZeroWordComputable :
    BitTM
      sourceIrreducibleMonicZeroWord :=
  factor400BinaryIrreduciblePhysicalDynamicCatalogueComputer
    sourceIrreducibleMonicZeroWidth
    factor400BinaryIrreduciblePhysicalFalseComputer

private def sourceIrreducibleFactorPairMonicWord
    (input : List Bool) : List Bool :=
  sourceIrreducibleFactorPairLowerWord input ++
    ([true] ++ sourceIrreducibleMonicZeroWord input)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorPairMonicWordComputable :
    BitTM
      sourceIrreducibleFactorPairMonicWord := by
  have htail := factor400BinaryIrreduciblePhysicalAppendComputer
    factor400BinaryIrreduciblePhysicalTrueComputer
    paperVariableAritySourceIrreducibleMonicZeroWordComputable
  exact factor400BinaryIrreduciblePhysicalAppendComputer
    paperVariableAritySourceIrreducibleFactorPairLowerWordComputable htail

private def sourceIrreducibleFactorPairMarker :
    List Bool → List Bool :=
  maskComputedWordEquality
    sourceIrreducibleFactorPairProductWord
    sourceIrreducibleFactorPairMonicWord

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorPairMarkerComputable :
    BitTM
      sourceIrreducibleFactorPairMarker :=
  maskComputedWordEqualityComputable
    paperVariableAritySourceIrreducibleFactorPairProductWordComputable
    paperVariableAritySourceIrreducibleFactorPairMonicWordComputable

private def sourceIrreducibleFactorPairMarkerStream :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    sourceIrreducibleFactorPairWidth
    paperVariableAritySourceIrreducibleFactorPairMarkerComputable

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleFactorPairMarkerStreamComputable :
    BitTM
      sourceIrreducibleFactorPairMarkerStream :=
  factor400BinaryIrreduciblePhysicalDynamicCatalogueComputer
    sourceIrreducibleFactorPairWidth
    paperVariableAritySourceIrreducibleFactorPairMarkerComputable

private def paperVariableAritySourceIrreducibleProperFactorExistsWord :
    List Bool → List Bool :=
  binaryGaussianFirstCellWord ∘ binaryGaussianPivotWord ∘
    sourceIrreducibleFactorPairMarkerStream

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleProperFactorExistsComputable :
    BitTM
      paperVariableAritySourceIrreducibleProperFactorExistsWord := by
  have hscan := factor400BinaryIrreduciblePhysicalCompositionComputer
    paperVariableAritySourceIrreducibleFactorPairMarkerStreamComputable
    binaryGaussianPivotComputable
  exact factor400BinaryIrreduciblePhysicalCompositionComputer
    hscan binaryGaussianFirstCellComputable

private def sourceIrreducibleNoProperFactorWord :
    List Bool → List Bool :=
  sourceFourFamilyBooleanNotWord ∘
    paperVariableAritySourceIrreducibleProperFactorExistsWord

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleNoProperFactorComputable :
    BitTM
      sourceIrreducibleNoProperFactorWord :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    paperVariableAritySourceIrreducibleProperFactorExistsComputable
    sourceFourFamilyBooleanNotComputable

private def sourceActualIrreducibleCandidateMarkerStream :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    sourceIrreducibleCandidateWidth
    paperVariableAritySourceIrreducibleNoProperFactorComputable

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceActualIrreducibleCandidateMarkerStreamComputable :
    BitTM
      sourceActualIrreducibleCandidateMarkerStream :=
  factor400BinaryIrreduciblePhysicalDynamicCatalogueComputer
    sourceIrreducibleCandidateWidth
    paperVariableAritySourceIrreducibleNoProperFactorComputable

private def sourceActualIrreducibleFirstCandidateWord :
    List Bool → List Bool :=
  binaryGaussianPivotWord ∘
    sourceActualIrreducibleCandidateMarkerStream

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceActualIrreducibleFirstCandidateComputable :
    BitTM
      sourceActualIrreducibleFirstCandidateWord :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    paperVariableAritySourceActualIrreducibleCandidateMarkerStreamComputable
    binaryGaussianPivotComputable

private def sourceActualIrreducibleSelectedRankUnary :
    List Bool → List Bool :=
  List.tail ∘ sourceActualIrreducibleFirstCandidateWord

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceActualIrreducibleSelectedRankComputable :
    BitTM
      sourceActualIrreducibleSelectedRankUnary :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    paperVariableAritySourceActualIrreducibleFirstCandidateComputable
    factor400BinaryIrreduciblePhysicalDropHeadComputer

private def paperVariableAritySourceActualIrreducibleSelectedRankQuery
    (input : List Bool) : List Bool :=
  binaryIrreduciblePhysicalComputedPrefixOutput
      sourceActualIrreducibleSelectedRankUnary input ++
    (binaryIrreduciblePhysicalComputedPrefixOutput
      physicalFamilyFieldCardinalityUnary input ++ input)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceActualIrreducibleSelectedRankQueryComputable :
    BitTM
      paperVariableAritySourceActualIrreducibleSelectedRankQuery :=
  factor400BinaryIrreduciblePhysicalAppendComputer
    (factor400BinaryIrreduciblePhysicalComputedPrefixComputer
      paperVariableAritySourceActualIrreducibleSelectedRankComputable)
    (factor400BinaryIrreduciblePhysicalAppendComputer
      (factor400BinaryIrreduciblePhysicalComputedPrefixComputer
        paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable)
      (Turing.idComputableInPolyTime bitEncoding))

/-- GapCVP reduction support. -/
def sourceSelectedIrreducibleWord :
    List Bool → List Bool :=
  sourceIrreducibleRankCoefficientWord ∘
    paperVariableAritySourceActualIrreducibleSelectedRankQuery

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceSelectedIrreducibleWordComputable :
    BitTM
    sourceSelectedIrreducibleWord :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    paperVariableAritySourceActualIrreducibleSelectedRankQueryComputable
    paperVariableAritySourceIrreducibleRankCoefficientWordComputable

private theorem paperVariableAritySourceIrreducibleCandidateWidth_valid
    (formula : ThreeCNF) :
    sourceIrreducibleCandidateWidth.output
      (encodeThreeCNF formula) =
      List.replicate
        (2 ^ sourceIrreducibleFormulaDegree formula) true := by
  rw [paperVariableAritySourceIrreducibleCandidateWidth_output,
    paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid]

@[simp] private theorem paperVariableAritySourceIrreducibleCandidateOriginalSource_query
    (formula : ThreeCNF) (rank : ℕ) :
    binaryIrreducibleRankOriginal
      (sourceIrreducibleCandidateQuery
        (encodeThreeCNF formula) rank) =
      encodeThreeCNF formula := by
  unfold sourceIrreducibleCandidateQuery
    sourceQaryMaskDynamicGridBaseSource
  simpa only [List.append_assoc] using
    factor400BinaryIrreducibleRankOriginal_valid
      (List.replicate rank true)
      (sourceIrreducibleCandidateWidth.output
        (encodeThreeCNF formula))
      (encodeThreeCNF formula)

@[simp] private theorem paperVariableAritySourceIrreducibleCandidateCardinality_query
    (formula : ThreeCNF) (rank : ℕ) :
    sourceIrreducibleCandidateCardinalityUnary
      (sourceIrreducibleCandidateQuery
        (encodeThreeCNF formula) rank) =
      List.replicate
        (2 ^ sourceIrreducibleFormulaDegree formula) true := by
  unfold sourceIrreducibleCandidateCardinalityUnary
  rw [Function.comp_apply,
    paperVariableAritySourceIrreducibleCandidateOriginalSource_query,
    paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid]

@[simp] private theorem paperVariableAritySourceIrreducibleFactorPairWidth_valid
    (formula : ThreeCNF) (rank : ℕ) :
    sourceIrreducibleFactorPairWidth.output
      (sourceIrreducibleCandidateQuery
        (encodeThreeCNF formula) rank) =
      List.replicate
        ((2 ^ sourceIrreducibleFormulaDegree formula) ^ 2)
        true := by
  unfold sourceIrreducibleFactorPairWidth
  rw [factor400BinaryIrreduciblePhysicalDynamicWidth_output]
  unfold paperVariableAritySourceIrreducibleFactorPairWidthOutput
  rw [Function.comp_apply,
    paperVariableAritySourceIrreducibleCandidateCardinality_query]
  simp only [List.length_replicate, Polynomial.eval_pow,
    Polynomial.eval_X]

private def sourcePhysicalIrreducibleFactorPairQuery
    (candidate : List Bool) (rank : ℕ) : List Bool :=
  lengthPrefixedWord (List.replicate rank true) ++
    sourceQaryMaskDynamicGridBaseSource
      sourceIrreducibleFactorPairWidth candidate

@[simp] private theorem paperVariableAritySourceIrreducibleFactorPairCandidateSource_query
    (candidate : List Bool) (rank : ℕ) :
    binarySourceIrreducibleFactorPairCandidateSource
      (sourcePhysicalIrreducibleFactorPairQuery
        candidate rank) = candidate := by
  simp only [binarySourceIrreducibleFactorPairCandidateSource, factor400BinarySourceSkipFields,
      CompTriple.comp_eq, sourcePhysicalIrreducibleFactorPairQuery,
          sourceQaryMaskDynamicGridBaseSource,
      Function.comp_apply, firstFieldSuffix_valid]

@[simp] private theorem paperVariableAritySourceIrreducibleFactorPairOriginalSource_query
    (formula : ThreeCNF) (candidateRank pairRank : ℕ) :
    sourceIrreducibleFactorPairOriginalSource
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank) pairRank) =
      encodeThreeCNF formula := by
  unfold sourceIrreducibleFactorPairOriginalSource
    factor400BinarySourceIrreducibleFactorPairOriginalSource
  rw [Function.comp_apply,
    paperVariableAritySourceIrreducibleFactorPairCandidateSource_query,
    paperVariableAritySourceIrreducibleCandidateOriginalSource_query]

@[simp] private theorem paperVariableAritySourceIrreducibleFactorPairCardinality_query
    (formula : ThreeCNF) (candidateRank pairRank : ℕ) :
    sourceIrreducibleFactorPairCardinalityUnary
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank) pairRank) =
      List.replicate
        (2 ^ sourceIrreducibleFormulaDegree formula) true := by
  unfold sourceIrreducibleFactorPairCardinalityUnary
  rw [Function.comp_apply,
    paperVariableAritySourceIrreducibleFactorPairOriginalSource_query,
    paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid]

@[simp] private theorem paperVariableAritySourceIrreducibleFactorPairRank_query
    (candidate : List Bool) (rank : ℕ) :
    firstFieldContents
      (sourcePhysicalIrreducibleFactorPairQuery
        candidate rank) = List.replicate rank true := by
  unfold sourcePhysicalIrreducibleFactorPairQuery
  exact firstFieldContents_valid (List.replicate rank true)
    (sourceQaryMaskDynamicGridBaseSource
      sourceIrreducibleFactorPairWidth candidate)

private theorem paperVariableAritySourceIrreducibleFactorPairDivisionQuery_query
    (formula : ThreeCNF) (candidateRank pairRank : ℕ) :
    sourceIrreducibleFactorPairDivisionQuery
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank) pairRank) =
      sourceUnaryDivisionQuery pairRank
        (2 ^ sourceIrreducibleFormulaDegree formula)
        (encodeThreeCNF formula) := by
  unfold sourceIrreducibleFactorPairDivisionQuery
    sourceUnaryDivisionQuery
  rw [paperVariableAritySourceIrreducibleFactorPairRank_query,
    paperVariableAritySourceIrreducibleFactorPairCardinality_query,
    paperVariableAritySourceIrreducibleFactorPairOriginalSource_query]

private theorem paperVariableAritySourceIrreducibleFactorPairOdometer_query
    (formula : ThreeCNF) (candidateRank pairRank : ℕ) :
    sourceIrreducibleFactorPairOdometer
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank) pairRank) =
      List.replicate
          (pairRank /
            (2 ^ sourceIrreducibleFormulaDegree formula)) true ++
        false ::
          (List.replicate
            (pairRank %
              (2 ^ sourceIrreducibleFormulaDegree formula)) true ++
            false :: sourceUnaryDivisionQuery pairRank
              (2 ^ sourceIrreducibleFormulaDegree formula)
              (encodeThreeCNF formula)) := by
  unfold sourceIrreducibleFactorPairOdometer
  rw [Function.comp_apply,
    paperVariableAritySourceIrreducibleFactorPairDivisionQuery_query,
    sourceMixedRadixRowMajorPairOutput_valid]
  positivity

private theorem paperVariableAritySourceIrreducibleFactorPairFirstRank_query
    (formula : ThreeCNF) (candidateRank pairRank : ℕ) :
    sourceIrreducibleFactorPairFirstRank
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank) pairRank) =
      List.replicate
        (pairRank /
          (2 ^ sourceIrreducibleFormulaDegree formula)) true := by
  unfold sourceIrreducibleFactorPairFirstRank
  rw [paperVariableAritySourceIrreducibleFactorPairOdometer_query,
    unaryPrefixOutput_replicate_delimiter]
  rfl

private theorem paperVariableAritySourceIrreducibleFactorPairSecondRank_query
    (formula : ThreeCNF) (candidateRank pairRank : ℕ) :
    sourceIrreducibleFactorPairSecondRank
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank) pairRank) =
      List.replicate
        (pairRank %
          (2 ^ sourceIrreducibleFormulaDegree formula)) true := by
  unfold sourceIrreducibleFactorPairSecondRank
  rw [paperVariableAritySourceIrreducibleFactorPairOdometer_query,
    unaryPrefixSuffixOutput_valid,
    unaryPrefixOutput_replicate_delimiter]
  rfl

private def sourceIrreducibleProperFactorFirstIndex
    (degree pairRank : ℕ)
    (hpair : pairRank < (2 ^ degree) ^ 2) : Fin (2 ^ degree) :=
  ⟨pairRank / (2 ^ degree), by
    have hq : 0 < 2 ^ degree := by positivity
    apply (Nat.div_lt_iff_lt_mul hq).2
    simpa only [pow_two] using hpair⟩

private def sourceIrreducibleProperFactorSecondIndex
    (degree pairRank : ℕ)
    (_hpair : pairRank < (2 ^ degree) ^ 2) : Fin (2 ^ degree) :=
  ⟨pairRank % (2 ^ degree), Nat.mod_lt _ (by positivity)⟩

private theorem paperVariableAritySourceIrreducibleFactorPairLowerWord_query
    (formula : ThreeCNF)
    (candidateRank : Fin
      (2 ^ sourceIrreducibleFormulaDegree formula))
    (pairRank : ℕ) :
    sourceIrreducibleFactorPairLowerWord
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank.val) pairRank) =
      finiteWordBits
        (indexedWord
          (sourceIrreducibleFormulaDegree formula)
          candidateRank) := by
  unfold sourceIrreducibleFactorPairLowerWord
  rw [Function.comp_apply,
    paperVariableAritySourceIrreducibleFactorPairCandidateSource_query]
  unfold sourceIrreducibleCandidateQuery
    sourceQaryMaskDynamicGridBaseSource
  simpa only [List.append_assoc] using
    sourceIrreducibleRankCoefficientWord_eq_indexedWord
      formula candidateRank
      (sourceIrreducibleCandidateWidth.output
        (encodeThreeCNF formula))

private theorem paperVariableAritySourceIrreducibleFactorPairFirstWord_query
    (formula : ThreeCNF)
    (candidateRank : Fin
      (2 ^ sourceIrreducibleFormulaDegree formula))
    (pairRank : ℕ)
    (hpair : pairRank <
      (2 ^ sourceIrreducibleFormulaDegree formula) ^ 2) :
    sourceIrreducibleFactorPairFirstWord
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank.val) pairRank) =
      finiteWordBits
        (indexedWord
          (sourceIrreducibleFormulaDegree formula)
          (sourceIrreducibleProperFactorFirstIndex
            (sourceIrreducibleFormulaDegree formula)
            pairRank hpair)) := by
  unfold sourceIrreducibleFactorPairFirstWord
  rw [Function.comp_apply]
  unfold sourceIrreducibleFactorRankQuery
    binaryIrreduciblePhysicalComputedPrefixOutput
  simp only [Function.comp_apply]
  rw [paperVariableAritySourceIrreducibleFactorPairFirstRank_query,
    paperVariableAritySourceIrreducibleFactorPairCardinality_query,
    paperVariableAritySourceIrreducibleFactorPairOriginalSource_query]
  simpa only [sourceIrreducibleProperFactorFirstIndex,
    List.append_assoc] using
    sourceIrreducibleRankCoefficientWord_eq_indexedWord
      formula
      (sourceIrreducibleProperFactorFirstIndex
        (sourceIrreducibleFormulaDegree formula)
        pairRank hpair)
      (List.replicate
        (2 ^ sourceIrreducibleFormulaDegree formula) true)

private theorem paperVariableAritySourceIrreducibleFactorPairSecondWord_query
    (formula : ThreeCNF)
    (candidateRank : Fin
      (2 ^ sourceIrreducibleFormulaDegree formula))
    (pairRank : ℕ)
    (hpair : pairRank <
      (2 ^ sourceIrreducibleFormulaDegree formula) ^ 2) :
    sourceIrreducibleFactorPairSecondWord
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank.val) pairRank) =
      finiteWordBits
        (indexedWord
          (sourceIrreducibleFormulaDegree formula)
          (sourceIrreducibleProperFactorSecondIndex
            (sourceIrreducibleFormulaDegree formula)
            pairRank hpair)) := by
  unfold sourceIrreducibleFactorPairSecondWord
  rw [Function.comp_apply]
  unfold sourceIrreducibleFactorRankQuery
    binaryIrreduciblePhysicalComputedPrefixOutput
  simp only [Function.comp_apply]
  rw [paperVariableAritySourceIrreducibleFactorPairSecondRank_query,
    paperVariableAritySourceIrreducibleFactorPairCardinality_query,
    paperVariableAritySourceIrreducibleFactorPairOriginalSource_query]
  simpa only [sourceIrreducibleProperFactorSecondIndex,
    List.append_assoc] using
    sourceIrreducibleRankCoefficientWord_eq_indexedWord
      formula
      (sourceIrreducibleProperFactorSecondIndex
        (sourceIrreducibleFormulaDegree formula)
        pairRank hpair)
      (List.replicate
        (2 ^ sourceIrreducibleFormulaDegree formula) true)

private theorem paperVariableAritySourceIrreducibleFactorPairProductQuery_query
    (formula : ThreeCNF)
    (candidateRank : Fin
      (2 ^ sourceIrreducibleFormulaDegree formula))
    (pairRank : ℕ)
    (hpair : pairRank <
      (2 ^ sourceIrreducibleFormulaDegree formula) ^ 2) :
    sourceIrreducibleFactorPairProductQuery
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank.val) pairRank) =
      factor400BinarySourceFieldQuery
        (finiteWordBits
          (indexedWord
            (sourceIrreducibleFormulaDegree formula)
            candidateRank))
        (finiteWordBits
          (indexedWord
            (sourceIrreducibleFormulaDegree formula)
            (sourceIrreducibleProperFactorFirstIndex
              (sourceIrreducibleFormulaDegree formula)
              pairRank hpair)))
        (finiteWordBits
          (indexedWord
            (sourceIrreducibleFormulaDegree formula)
            (sourceIrreducibleProperFactorSecondIndex
              (sourceIrreducibleFormulaDegree formula)
              pairRank hpair)))
        (encodeThreeCNF formula) := by
  unfold sourceIrreducibleFactorPairProductQuery
    binaryIrreduciblePhysicalComputedPrefixOutput
  simp only [Function.comp_apply]
  rw [paperVariableAritySourceIrreducibleFactorPairLowerWord_query,
    paperVariableAritySourceIrreducibleFactorPairFirstWord_query
      formula candidateRank pairRank hpair,
    paperVariableAritySourceIrreducibleFactorPairSecondWord_query
      formula candidateRank pairRank hpair,
    paperVariableAritySourceIrreducibleFactorPairOriginalSource_query]
  simp only [factor400BinarySourceFieldQuery, List.append_assoc]

private theorem paperVariableAritySourceIrreducibleFactorPairProductWord_query
    (formula : ThreeCNF)
    (candidateRank : Fin
      (2 ^ sourceIrreducibleFormulaDegree formula))
    (pairRank : ℕ)
    (hpair : pairRank <
      (2 ^ sourceIrreducibleFormulaDegree formula) ^ 2) :
    sourceIrreducibleFactorPairProductWord
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank.val) pairRank) =
      finiteWordBits
        (multiplyWords
          (indexedWord
            (sourceIrreducibleFormulaDegree formula)
            (sourceIrreducibleProperFactorFirstIndex
              (sourceIrreducibleFormulaDegree formula)
              pairRank hpair))
          (indexedWord
            (sourceIrreducibleFormulaDegree formula)
            (sourceIrreducibleProperFactorSecondIndex
              (sourceIrreducibleFormulaDegree formula)
              pairRank hpair))) := by
  unfold sourceIrreducibleFactorPairProductWord
  rw [Function.comp_apply,
    paperVariableAritySourceIrreducibleFactorPairProductQuery_query
      formula candidateRank pairRank hpair,
    factor400BinarySourceRawConvolutionWord_valid]

@[simp] private theorem paperVariableAritySourceIrreducibleFactorPairDegreeUnary_query
    (formula : ThreeCNF) (candidateRank pairRank : ℕ) :
    sourceIrreducibleFactorPairDegreeUnary
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank) pairRank) =
      List.replicate
        (sourceIrreducibleFormulaDegree formula) true := by
  unfold sourceIrreducibleFactorPairDegreeUnary
  rw [Function.comp_apply,
    paperVariableAritySourceIrreducibleFactorPairOriginalSource_query,
    paperVariableArityPhysicalFamilyFieldDegreeUnary_valid]

@[simp] private theorem paperVariableAritySourceIrreducibleMonicZeroWidth_query
    (formula : ThreeCNF) (candidateRank pairRank : ℕ) :
    sourceIrreducibleMonicZeroWidth.output
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank) pairRank) =
      List.replicate
        (sourceIrreducibleFormulaDegree formula - 1) true := by
  unfold sourceIrreducibleMonicZeroWidth
  rw [factor400BinaryIrreduciblePhysicalDynamicWidth_output]
  unfold paperVariableAritySourceIrreducibleMonicZeroWidthOutput
  rw [paperVariableAritySourceIrreducibleFactorPairDegreeUnary_query]
  simp only [List.tail_replicate]

private theorem paperVariableAritySourceIrreducibleMonicZeroWord_query
    (formula : ThreeCNF) (candidateRank pairRank : ℕ) :
    sourceIrreducibleMonicZeroWord
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank) pairRank) =
      List.replicate
        (sourceIrreducibleFormulaDegree formula - 1) false := by
  unfold sourceIrreducibleMonicZeroWord
  rw [maskDynamicGridRecordCatalogueOutput_valid
    sourceIrreducibleMonicZeroWidth
    factor400BinaryIrreduciblePhysicalFalseComputer
    (sourcePhysicalIrreducibleFactorPairQuery
      (sourceIrreducibleCandidateQuery
        (encodeThreeCNF formula) candidateRank) pairRank)
    (sourceIrreducibleFormulaDegree formula - 1)
    (paperVariableAritySourceIrreducibleMonicZeroWidth_query
      formula candidateRank pairRank)]
  change
    (List.range
      (sourceIrreducibleFormulaDegree formula - 1)).flatMap
        (fun _ => [false]) = _
  rw [← List.map_eq_flatMap]
  simp only [List.map_const', List.length_range]

private theorem paperVariableAritySourceIrreducibleFactorPairMonicWord_query
    (formula : ThreeCNF)
    (candidateRank : Fin
      (2 ^ sourceIrreducibleFormulaDegree formula))
    (pairRank : ℕ) :
    sourceIrreducibleFactorPairMonicWord
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank.val) pairRank) =
      finiteWordBits
        (monicWord
          (indexedWord
            (sourceIrreducibleFormulaDegree formula)
            candidateRank)) := by
  unfold sourceIrreducibleFactorPairMonicWord
  rw [paperVariableAritySourceIrreducibleFactorPairLowerWord_query,
    paperVariableAritySourceIrreducibleMonicZeroWord_query]
  symm
  apply finiteWordBits_monicWord
  exact GapCVP.Core.sourceFieldExponent_pos
    (GapCVP.Core.sourceSizeParameter_ge_one_hundred
      (encodeThreeCNF formula).length
      (srcFormula formula))

end

section

open Turing GapCVP.BinaryEncoding GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.BinaryFieldBasis
open GapCVP.BinaryModularReductionTM GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.BinarySelectedIrreducibleWordTM GapCVP.BinarySelectedIrreducibleWordOrderCorrectness
open GapCVP.BinarySelectedIrreducibleFactorCorrectness GapCVP.BinarySourceFieldMultiplicationTM
open GapCVP.GaussianPivotScheduleTM GapCVP.GaussianRowWorker GapCVP.Core.EffectiveBinaryField

@[simp] private theorem paperVariableAritySourceFiniteWordBits_eq_iff
    {degree : ℕ} (left right : Word degree) :
    finiteWordBits left = finiteWordBits right ↔ left = right := by
  constructor
  · intro heq
    have hwords := congrArg
      (factor400BinarySourcePaddedWord degree) heq
    simpa only [factor400BinarySourcePaddedWord_finiteWordBits]
      using hwords
  · intro heq
    rw [heq]

private theorem paperVariableAritySourceIrreducibleFactorPairMarker_query
    (formula : ThreeCNF)
    (candidateRank : Fin
      (2 ^ sourceIrreducibleFormulaDegree formula))
    (pairRank : ℕ)
    (hpair : pairRank <
      (2 ^ sourceIrreducibleFormulaDegree formula) ^ 2) :
    sourceIrreducibleFactorPairMarker
      (sourcePhysicalIrreducibleFactorPairQuery
        (sourceIrreducibleCandidateQuery
          (encodeThreeCNF formula) candidateRank.val) pairRank) =
      [binaryIndexedProperFactorPairBit
        (sourceIrreducibleFormulaDegree formula)
        (indexedWord
          (sourceIrreducibleFormulaDegree formula)
          candidateRank)
        pairRank] := by
  unfold sourceIrreducibleFactorPairMarker
  rw [sourceQaryMaskSquareComputedWordEquality_valid,
    paperVariableAritySourceIrreducibleFactorPairProductWord_query
      formula candidateRank pairRank hpair,
    paperVariableAritySourceIrreducibleFactorPairMonicWord_query
      formula candidateRank pairRank]
  simp only [paperVariableAritySourceFiniteWordBits_eq_iff]
  simp only [sourceIrreducibleProperFactorFirstIndex, sourceIrreducibleProperFactorSecondIndex,
      binaryIndexedProperFactorPairBit, hpair, ↓reduceDIte,
      List.cons.injEq, and_true]
  rfl

private theorem paperVariableAritySourceIrreducibleFactorPairMarkerStream_valid
    (formula : ThreeCNF)
    (candidateRank : Fin
      (2 ^ sourceIrreducibleFormulaDegree formula)) :
    sourceIrreducibleFactorPairMarkerStream
      (sourceIrreducibleCandidateQuery
        (encodeThreeCNF formula) candidateRank.val) =
      (List.range
        ((2 ^ sourceIrreducibleFormulaDegree formula) ^ 2)).map
        (binaryIndexedProperFactorPairBit
          (sourceIrreducibleFormulaDegree formula)
          (indexedWord
            (sourceIrreducibleFormulaDegree formula)
            candidateRank)) := by
  unfold sourceIrreducibleFactorPairMarkerStream
  rw [maskDynamicGridRecordCatalogueOutput_valid
    sourceIrreducibleFactorPairWidth
    paperVariableAritySourceIrreducibleFactorPairMarkerComputable
    (sourceIrreducibleCandidateQuery
      (encodeThreeCNF formula) candidateRank.val)
    ((2 ^ sourceIrreducibleFormulaDegree formula) ^ 2)
    (paperVariableAritySourceIrreducibleFactorPairWidth_valid
      formula candidateRank.val)]
  change
    (List.range
      ((2 ^ sourceIrreducibleFormulaDegree formula) ^ 2)).flatMap
      (fun pairRank =>
        sourceIrreducibleFactorPairMarker
          (sourcePhysicalIrreducibleFactorPairQuery
            (sourceIrreducibleCandidateQuery
              (encodeThreeCNF formula) candidateRank.val) pairRank)) = _
  calc
    _ = (List.range
      ((2 ^ sourceIrreducibleFormulaDegree formula) ^ 2)).flatMap
        (fun pairRank =>
          [binaryIndexedProperFactorPairBit
            (sourceIrreducibleFormulaDegree formula)
            (indexedWord
              (sourceIrreducibleFormulaDegree formula)
              candidateRank) pairRank]) := by
          apply List.flatMap_congr
          intro pairRank hpair
          exact paperVariableAritySourceIrreducibleFactorPairMarker_query
            formula candidateRank pairRank (List.mem_range.mp hpair)
    _ = _ :=
      (List.map_eq_flatMap
        (f := binaryIndexedProperFactorPairBit
          (sourceIrreducibleFormulaDegree formula)
          (indexedWord
            (sourceIrreducibleFormulaDegree formula)
            candidateRank))
        (l := List.range
          ((2 ^ sourceIrreducibleFormulaDegree formula) ^ 2))).symm

private theorem paperVariableAritySourceIrreducibleFirstPivotMarker
    (markers : List Bool) :
    binaryGaussianFirstCellWord (binaryGaussianPivotWord markers) =
      [decide (markers.findIdx? id ≠ none)] := by
  cases hfind : markers.findIdx? id with
  | none => simp only [binaryGaussianPivotWord, hfind, binaryGaussianFirstCellWord_valid, ne_eq,
      not_true_eq_false,
                decide_false]
  | some rank => simp only [binaryGaussianPivotWord, hfind, binaryGaussianFirstCellWord_valid,
      ne_eq, reduceCtorEq,
                     not_false_eq_true, decide_true]

private theorem paperVariableAritySourceIrreducibleNoProperFactorWord_valid
    (formula : ThreeCNF)
    (candidateRank : Fin
      (2 ^ sourceIrreducibleFormulaDegree formula)) :
    sourceIrreducibleNoProperFactorWord
      (sourceIrreducibleCandidateQuery
        (encodeThreeCNF formula) candidateRank.val) =
      [noProperFactors
        (sourceIrreducibleFormulaDegree formula)
        (indexedWord
          (sourceIrreducibleFormulaDegree formula)
          candidateRank)] := by
  let degree := sourceIrreducibleFormulaDegree formula
  let lower := indexedWord degree candidateRank
  let markers :=
    (List.range ((2 ^ degree) ^ 2)).map
      (binaryIndexedProperFactorPairBit degree lower)
  unfold sourceIrreducibleNoProperFactorWord
    paperVariableAritySourceIrreducibleProperFactorExistsWord
  simp only [Function.comp_apply]
  rw [paperVariableAritySourceIrreducibleFactorPairMarkerStream_valid
    formula candidateRank]
  change
    sourceFourFamilyBooleanNotWord
      (binaryGaussianFirstCellWord (binaryGaussianPivotWord markers)) =
      [noProperFactors degree lower]
  rw [paperVariableAritySourceIrreducibleFirstPivotMarker,
    sourceFourFamilyBooleanNotWord_bit]
  cases hfind : markers.findIdx? id with
  | none =>
      have hgood : noProperFactors degree lower = true :=
        (noProperFactors_eq_true_iff lower).mpr
          ((factor400BinaryIndexedProperFactorPairMarkers_find_none_iff
            degree lower).mp hfind)
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.not_false, hgood]
  | some index =>
      have hbad : noProperFactors degree lower = false := by
        cases hvalue : noProperFactors degree lower with
        | false => rfl
        | true =>
            have hnone : markers.findIdx? id = none :=
              (factor400BinaryIndexedProperFactorPairMarkers_find_none_iff
                degree lower).mpr
                ((noProperFactors_eq_true_iff lower).mp hvalue)
            rw [hfind] at hnone
            cases hnone
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, decide_true, Bool.not_true, hbad]

private theorem paperVariableAritySourceActualIrreducibleCandidateMarkerStream_valid
    (formula : ThreeCNF) :
    sourceActualIrreducibleCandidateMarkerStream
      (encodeThreeCNF formula) =
      binaryIndexedIrreducibleCandidateMarkers
        (sourceIrreducibleFormulaDegree formula) := by
  let degree := sourceIrreducibleFormulaDegree formula
  let input := encodeThreeCNF formula
  unfold sourceActualIrreducibleCandidateMarkerStream
  rw [maskDynamicGridRecordCatalogueOutput_valid
    sourceIrreducibleCandidateWidth
    paperVariableAritySourceIrreducibleNoProperFactorComputable
    input (2 ^ degree)
    (paperVariableAritySourceIrreducibleCandidateWidth_valid formula)]
  change
    (List.range (2 ^ degree)).flatMap
      (fun rank => sourceIrreducibleNoProperFactorWord
        (sourceIrreducibleCandidateQuery input rank)) =
      binaryIndexedIrreducibleCandidateMarkers degree
  unfold binaryIndexedIrreducibleCandidateMarkers
  calc
    _ = (List.range (2 ^ degree)).flatMap
        (fun rank => [binaryIndexedNoProperFactorsBit degree rank]) := by
          apply List.flatMap_congr
          intro rank hrank
          have hlt : rank < 2 ^ degree := List.mem_range.mp hrank
          have hcorrect := paperVariableAritySourceIrreducibleNoProperFactorWord_valid
            formula (⟨rank, hlt⟩ : Fin (2 ^ degree))
          simpa only [input, degree,
            binaryIndexedNoProperFactorsBit,
            dite_eq_left hlt] using hcorrect
    _ = _ :=
      (List.map_eq_flatMap
        (f := binaryIndexedNoProperFactorsBit degree)
        (l := List.range (2 ^ degree))).symm

theorem paperVariableAritySourceSelectedIrreducibleWord_valid
    (formula : ThreeCNF) :
    sourceSelectedIrreducibleWord
      (encodeThreeCNF formula) =
      finiteWordBits
        (irreducibleWord
          (sourceIrreducibleFormulaDegree formula)) := by
  let degree := sourceIrreducibleFormulaDegree formula
  have hdegree : 0 < degree := by
    exact GapCVP.Core.sourceFieldExponent_pos
      (GapCVP.Core.sourceSizeParameter_ge_one_hundred
        (encodeThreeCNF formula).length
        (srcFormula formula))
  obtain ⟨rank, hfirst, hselected⟩ :=
    exists_first_source_irreducible_rank degree hdegree
  have hpivot :
      sourceActualIrreducibleFirstCandidateWord
        (encodeThreeCNF formula) =
        true :: List.replicate rank.val true := by
    unfold sourceActualIrreducibleFirstCandidateWord
    rw [Function.comp_apply,
      paperVariableAritySourceActualIrreducibleCandidateMarkerStream_valid]
    change
      binaryGaussianPivotWord
        (binaryIndexedIrreducibleCandidateMarkers degree) = _
    simp only [binaryGaussianPivotWord, hfirst]
  have hrank :
      sourceActualIrreducibleSelectedRankUnary
        (encodeThreeCNF formula) =
        List.replicate rank.val true := by
    simp only [sourceActualIrreducibleSelectedRankUnary, Function.comp_apply, hpivot,
        List.tail_cons]
  unfold sourceSelectedIrreducibleWord
  rw [Function.comp_apply]
  unfold paperVariableAritySourceActualIrreducibleSelectedRankQuery
    binaryIrreduciblePhysicalComputedPrefixOutput
  simp only [Function.comp_apply, hrank,
    paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid]
  change
    sourceIrreducibleRankCoefficientWord
      (lengthPrefixedWord (List.replicate rank.val true) ++
        (lengthPrefixedWord (List.replicate (2 ^ degree) true) ++
          encodeThreeCNF formula)) =
      finiteWordBits (irreducibleWord degree)
  have hword := sourceIrreducibleRankCoefficientWord_eq_indexedWord
    formula rank
    (List.replicate (2 ^ degree) true)
  calc
    _ = finiteWordBits (indexedWord degree rank) := by
      simpa only [List.append_assoc, degree] using hword
    _ = _ := congrArg finiteWordBits hselected

end

end Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine

namespace PhysicalMatrixCellTM

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryModularReductionTM GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalColumnOrder GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalRightHandSideTM
open GapCVP.SourceOrder GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.BinaryCompactPhysicalFieldCoefficientBitTM
open GapCVP.CanonicalMatrixShape GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

private def paperVariableArityPhysicalMatrixLiftedSourceWord
    (worker : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  worker.output ∘ sourceExplicitAffineCellOriginalSource

private noncomputable def paperVariableArityPhysicalMatrixLiftedSourceWordComputable
    (worker : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (paperVariableArityPhysicalMatrixLiftedSourceWord worker) :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable worker.computer

private noncomputable def paperVariableArityPhysicalMatrixLiftedSourceComputer
    (worker : SourcePhysicalLagrangeWordComputer) :
    SourcePhysicalLagrangeWordComputer where
  output := paperVariableArityPhysicalMatrixLiftedSourceWord worker
  computer := paperVariableArityPhysicalMatrixLiftedSourceWordComputable worker

@[simp] private theorem paperVariableArityPhysicalMatrixLiftedSourceComputer_query
    (worker : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF) :
    (paperVariableArityPhysicalMatrixLiftedSourceComputer worker).output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      worker.output (encodeThreeCNF formula) := by
  change
    worker.output
      (sourceExplicitAffineCellOriginalSource
        (affineCellQuery row column
          (encodeThreeCNF formula))) = _
  rw [sourceExplicitAffineCellOriginalSource_query]

/-- GapCVP reduction support. -/
noncomputable def physicalMatrixBasisRankComputer
    (degree : SourcePhysicalLagrangeWordComputer) :
    SourcePhysicalLagrangeWordComputer where
  output := sourcePhysicalComputedUnaryRemainder
    sourceExplicitAffineCellRow degree.output
  computer := sourcePhysicalComputedUnaryRemainderComputable
    sourceExplicitAffineCellRowComputable degree.computer

theorem paperVariableArityPhysicalMatrixBasisRankComputer_query
    (degree : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (fieldDegree : ℕ) (positive : 0 < fieldDegree)
    (correctDegree : degree.output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate fieldDegree true) :
    (physicalMatrixBasisRankComputer degree).output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate (row % fieldDegree) true := by
  exact sourcePhysicalComputedUnaryRemainder_valid
    sourceExplicitAffineCellRow degree.output
    (affineCellQuery row column
      (encodeThreeCNF formula))
    row fieldDegree positive
    (sourceExplicitAffineCellRow_query
      row column (encodeThreeCNF formula)) correctDegree

private noncomputable def paperVariableArityPhysicalMatrixSourceDegreeComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalFamilyFieldDegreeUnary
  computer := paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable

/-- GapCVP reduction support. -/
noncomputable def physicalMatrixFieldDegreeComputer :
    SourcePhysicalLagrangeWordComputer :=
  paperVariableArityPhysicalMatrixLiftedSourceComputer
    paperVariableArityPhysicalMatrixSourceDegreeComputer

@[simp] theorem paperVariableArityPhysicalMatrixFieldDegreeComputer_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalMatrixFieldDegreeComputer.output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physDegree formula) true := by
  change
    (paperVariableArityPhysicalMatrixLiftedSourceComputer
      paperVariableArityPhysicalMatrixSourceDegreeComputer).output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = _
  rw [paperVariableArityPhysicalMatrixLiftedSourceComputer_query]
  exact paperVariableArityPhysicalFamilyFieldDegreeUnary_valid formula

/-- GapCVP reduction support. -/
noncomputable def physicalMatrixSelectedBasisRankComputer :
    SourcePhysicalLagrangeWordComputer :=
  physicalMatrixBasisRankComputer
    physicalMatrixFieldDegreeComputer

@[simp] theorem
    paperVariableArityPhysicalMatrixSelectedBasisRankComputer_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalMatrixSelectedBasisRankComputer.output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (row % physDegree formula) true := by
  apply paperVariableArityPhysicalMatrixBasisRankComputer_query
    physicalMatrixFieldDegreeComputer
    row column formula
    (physDegree formula)
    (GapCVP.Core.sourceFieldExponent_pos
      (GapCVP.Core.sourceSizeParameter_ge_one_hundred
        (encodeThreeCNF formula).length
        (srcFormula formula)))
  exact paperVariableArityPhysicalMatrixFieldDegreeComputer_query
    row column formula

/-- GapCVP reduction support. -/
def physicalMatrixCoefficientBit
    (basisRank coefficient : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  compactPhysicalFieldCoefficientCellBit basisRank coefficient

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalMatrixCoefficientBitComputable
    (basisRank coefficient : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalMatrixCoefficientBit
        basisRank coefficient) :=
  compactPhysicalFieldCoefficientCellBitComputable
    basisRank coefficient

theorem paperVariableArityPhysicalMatrixCoefficientBit_valid
    {degree : ℕ}
    (basisRank coefficient : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (word : GapCVP.Core.EffectiveBinaryField.Word degree)
    (position : ℕ) (bounded : position < degree)
    (correctRank : basisRank.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
        List.replicate position true)
    (correctCoefficient : coefficient.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits word) :
    physicalMatrixCoefficientBit
        basisRank coefficient
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [word ⟨position, bounded⟩] := by
  exact compactPhysicalFieldCoefficientCellBit_valid
    basisRank coefficient row column formula word position bounded
    correctRank correctCoefficient

/-- GapCVP reduction support. -/
def physicalMatrixGuardedFourFamilyCheck
    (global refinement ordinary shifted : List Bool → List Bool) :
    List Bool → List Bool :=
  sourceFourFamilyBooleanOrOutput global
    (sourceFourFamilyBooleanOrOutput refinement
      (sourceFourFamilyBooleanOrOutput ordinary shifted))

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalMatrixGuardedFourFamilyCheckComputable
    (global refinement ordinary shifted : List Bool → List Bool)
    (globalComputer : BitTM global)
    (refinementComputer : BitTM refinement)
    (ordinaryComputer : BitTM ordinary)
    (shiftedComputer : BitTM shifted) :
    BitTM
      (physicalMatrixGuardedFourFamilyCheck
        global refinement ordinary shifted) :=
  sourceFourFamilyBooleanOrComputable globalComputer
    (sourceFourFamilyBooleanOrComputable refinementComputer
      (sourceFourFamilyBooleanOrComputable
        ordinaryComputer shiftedComputer))

private theorem paperVariableArityPhysicalMatrixFamilyGuardCover
    (row globalBoundary refinementBoundary ordinaryBoundary : ℕ)
    (entry : Bool) :
    ((decide (row < globalBoundary) && entry) ||
      ((decide (globalBoundary ≤ row ∧ row < refinementBoundary) &&
        entry) ||
        ((decide (refinementBoundary ≤ row ∧ row < ordinaryBoundary) &&
          entry) ||
          (decide (ordinaryBoundary ≤ row) && entry)))) = entry := by
  cases entry with
  | false => simp only [Bool.and_false, Bool.decide_and, Bool.or_self]
  | true =>
      by_cases global : row < globalBoundary
      · simp only [global, decide_true, Bool.and_self, Bool.decide_and, Bool.and_true,
          Bool.true_or]
      · have afterGlobal : globalBoundary ≤ row :=
          Nat.le_of_not_gt global
        by_cases refinement : row < refinementBoundary
        · simp only [global, decide_false, Bool.and_true, afterGlobal, refinement, and_self,
            decide_true, Bool.and_self,
              Bool.decide_and, Bool.true_or, Bool.or_true]
        · have afterRefinement : refinementBoundary ≤ row :=
            Nat.le_of_not_gt refinement
          by_cases ordinary : row < ordinaryBoundary
          · simp only [global, decide_false, Bool.and_true, afterGlobal, refinement, and_false,
              afterRefinement, ordinary,
                and_self, decide_true, Bool.and_self, Bool.true_or, Bool.or_true]
          · have afterOrdinary : ordinaryBoundary ≤ row :=
              Nat.le_of_not_gt ordinary
            simp only [global, decide_false, Bool.and_true, afterGlobal, refinement, and_false,
                afterRefinement, ordinary,
                afterOrdinary, decide_true, Bool.and_self, Bool.or_true]

theorem paperVariableArityPhysicalMatrixGuardedFourFamilyCheck_valid
    (global refinement ordinary shifted : List Bool → List Bool)
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (correctGlobal :
      global (affineCellQuery row.val column.val
        (encodeThreeCNF formula)) =
      [decide
        (row.val < physicalFormulaGlobalBoundary formula) &&
       decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).check
            row column = (1 : ZMod 2))])
    (correctRefinement :
      refinement (affineCellQuery row.val column.val
        (encodeThreeCNF formula)) =
      [decide
        (physicalFormulaGlobalBoundary formula ≤ row.val ∧
          row.val <
            physicalFormulaRefinementBoundary formula) &&
       decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).check
            row column = (1 : ZMod 2))])
    (correctOrdinary :
      ordinary (affineCellQuery row.val column.val
        (encodeThreeCNF formula)) =
      [decide
        (physicalFormulaRefinementBoundary formula ≤
            row.val ∧
          row.val <
            physicalFormulaOrdinaryBoundary formula) &&
       decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).check
            row column = (1 : ZMod 2))])
    (correctShifted :
      shifted (affineCellQuery row.val column.val
        (encodeThreeCNF formula)) =
      [decide
        (physicalFormulaOrdinaryBoundary formula ≤
          row.val) &&
       decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).check
            row column = (1 : ZMod 2))]) :
    physicalMatrixGuardedFourFamilyCheck
        global refinement ordinary shifted
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).check
            row column = (1 : ZMod 2))] := by
  let query := affineCellQuery row.val column.val
    (encodeThreeCNF formula)
  let entry := decide
    ((physicalWordBinarySystem
      (encodeThreeCNF formula).length formula).check
        row column = (1 : ZMod 2))
  let globalBit :=
    decide (row.val < physicalFormulaGlobalBoundary formula)
  let refinementBit := decide
    (physicalFormulaGlobalBoundary formula ≤ row.val ∧
      row.val < physicalFormulaRefinementBoundary formula)
  let ordinaryBit := decide
    (physicalFormulaRefinementBoundary formula ≤ row.val ∧
      row.val < physicalFormulaOrdinaryBoundary formula)
  let shiftedBit := decide
    (physicalFormulaOrdinaryBoundary formula ≤ row.val)
  have globalValue : global query = [globalBit && entry] := by
    simpa only [query, globalBit, entry] using correctGlobal
  have refinementValue : refinement query = [refinementBit && entry] := by
    simpa only [query, refinementBit, entry] using correctRefinement
  have ordinaryValue : ordinary query = [ordinaryBit && entry] := by
    simpa only [query, ordinaryBit, entry] using correctOrdinary
  have shiftedValue : shifted query = [shiftedBit && entry] := by
    simpa only [query, shiftedBit, entry] using correctShifted
  have last := fourFamilyBooleanOrOutput_bits
    ordinary shifted query
    (ordinaryBit && entry) (shiftedBit && entry)
    ordinaryValue shiftedValue
  have middle := fourFamilyBooleanOrOutput_bits
    refinement (sourceFourFamilyBooleanOrOutput ordinary shifted) query
    (refinementBit && entry)
    ((ordinaryBit && entry) || (shiftedBit && entry))
    refinementValue last
  have complete := fourFamilyBooleanOrOutput_bits
    global
    (sourceFourFamilyBooleanOrOutput refinement
      (sourceFourFamilyBooleanOrOutput ordinary shifted)) query
    (globalBit && entry)
    ((refinementBit && entry) ||
      ((ordinaryBit && entry) || (shiftedBit && entry)))
    globalValue middle
  have covered := paperVariableArityPhysicalMatrixFamilyGuardCover
    row.val
    (physicalFormulaGlobalBoundary formula)
    (physicalFormulaRefinementBoundary formula)
    (physicalFormulaOrdinaryBoundary formula)
    entry
  change
    physicalMatrixGuardedFourFamilyCheck
      global refinement ordinary shifted query = [entry]
  change
    sourceFourFamilyBooleanOrOutput global
      (sourceFourFamilyBooleanOrOutput refinement
        (sourceFourFamilyBooleanOrOutput ordinary shifted)) query =
      [entry]
  rw [← covered]
  exact complete

private theorem paperVariableArityPhysicalMatrixCheckEntry_transport
    (source target : GapCVP.Core.BinaryAffineSystem)
    (same : source = target)
    (row : Fin source.rowCount)
    (column : Fin source.dimension) :
    target.check
      (Fin.cast (congrArg GapCVP.Core.BinaryAffineSystem.rowCount same) row)
      (Fin.cast (congrArg GapCVP.Core.BinaryAffineSystem.dimension same)
        column) =
      source.check row column := by
  cases same
  rfl

private theorem paperVariableArityPhysicalMatrixRightHandSide_transport
    (source target : GapCVP.Core.BinaryAffineSystem)
    (same : source = target)
    (row : Fin source.rowCount) :
    target.rightHandSide
      (Fin.cast (congrArg GapCVP.Core.BinaryAffineSystem.rowCount same) row) =
      source.rightHandSide row := by
  cases same
  rfl

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityCanonicalPhysicalMatrixCellComputerOfCheck
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (check : List Bool → List Bool)
    (checkComputer : BitTM check)
    (correctCheck : ∀ (formula : ThreeCNF)
      (row : Fin (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
      (column : Fin
        (PaperVariableArityPhysicalWordDimension
          (encodeThreeCNF formula).length formula)),
      check
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
        [decide
          ((physicalWordBinarySystem
            (encodeThreeCNF formula).length formula).check
              row column = (1 : ZMod 2))]) :
    PaperVariableArityCanonicalBinaryMatrixCellComputer shape where
  check := check
  rhs := physicalRightHandSideBit
  checkComputable := checkComputer
  rhsComputable := paperVariableArityPhysicalRightHandSideBitComputable
  checkCorrect formula row column := by
    let source :=
      shape.system (encodeThreeCNF formula).length formula
    let target :=
      physicalWordBinarySystem
        (encodeThreeCNF formula).length formula
    have same : source = target :=
      shape.systemCorrect (encodeThreeCNF formula).length formula
    let physicalRow : Fin target.rowCount :=
      Fin.cast
        (congrArg GapCVP.Core.BinaryAffineSystem.rowCount same) row
    let physicalColumn : Fin target.dimension :=
      Fin.cast
        (congrArg GapCVP.Core.BinaryAffineSystem.dimension same) column
    have transferred :
        target.check physicalRow physicalColumn =
          source.check row column := by
      exact paperVariableArityPhysicalMatrixCheckEntry_transport
        source target same row column
    have correct := correctCheck formula physicalRow physicalColumn
    rw [transferred] at correct
    simpa only [source, target, physicalRow, physicalColumn, Fin.val_cast]
      using correct
  rhsCorrect formula row column := by
    let source :=
      shape.system (encodeThreeCNF formula).length formula
    let target :=
      physicalWordBinarySystem
        (encodeThreeCNF formula).length formula
    have same : source = target :=
      shape.systemCorrect (encodeThreeCNF formula).length formula
    let physicalRow : Fin target.rowCount :=
      Fin.cast
        (congrArg GapCVP.Core.BinaryAffineSystem.rowCount same) row
    let physicalColumn : Fin target.dimension :=
      Fin.cast
        (congrArg GapCVP.Core.BinaryAffineSystem.dimension same) column
    have transferred :
        target.rightHandSide physicalRow =
          source.rightHandSide row := by
      exact paperVariableArityPhysicalMatrixRightHandSide_transport
        source target same row
    have correct := paperVariableArityPhysicalRightHandSide_valid
      formula physicalRow physicalColumn
    rw [transferred] at correct
    simpa only [source, target, physicalRow, physicalColumn, Fin.val_cast]
      using correct

end PhysicalMatrixCellTM

namespace PhysicalGlobalRefinementCoefficientTM

open scoped BigOperators

open Turing GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryExplicitAffineSystem
open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalFamilyMarkerTM GapCVP.PhysicalRowOrderProjection
open GapCVP.PhysicalRightHandSideTM

attribute [local instance] Classical.propDecidable

private def physicalCoefficientFieldCardinalityUnary :
    List Bool → List Bool :=
  physicalCellSourceLift
    physicalFamilyFieldCardinalityUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalCoefficientFieldCardinalityUnaryComputable :
    BitTM
      physicalCoefficientFieldCardinalityUnary :=
  physicalCellSourceLiftComputable
    paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable

@[simp] private theorem paperVariableArityPhysicalCoefficientFieldCardinalityUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalCoefficientFieldCardinalityUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (physFieldCard formula) true := by
  unfold physicalCoefficientFieldCardinalityUnary
  rw [paperVariableArityPhysicalCellSourceLift_query,
    paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid]

private def physicalCoefficientGridCardinalityUnary :
    List Bool → List Bool :=
  physicalCellSourceLift
    physicalFamilyGridCardinalityUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalCoefficientGridCardinalityUnaryComputable :
    BitTM
      physicalCoefficientGridCardinalityUnary :=
  physicalCellSourceLiftComputable
    paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable

@[simp] private theorem paperVariableArityPhysicalCoefficientGridCardinalityUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalCoefficientGridCardinalityUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (physGridCard formula) true := by
  unfold physicalCoefficientGridCardinalityUnary
  rw [paperVariableArityPhysicalCellSourceLift_query,
    paperVariableArityPhysicalFamilyGridCardinalityUnary_valid]

theorem physicalCoefficientFieldCardinality_pos
    (formula : ThreeCNF) :
    0 < physFieldCard formula := by
  exact pow_pos (by decide : 0 < (2 : ℕ)) _

theorem physicalCoefficientGridCardinality_pos
    (formula : ThreeCNF) :
    0 < physGridCard formula := by
  have gridCardinality :
      Fintype.card
        (ExplicitGridPoint (encodeThreeCNF formula).length
          (srcFormula formula)) =
        physGridCard formula := by
    simpa only [Fintype.card_coe, physGridCard, physFieldCard, physDegree, physicalFormulaSize,
        physicalFormulaVariableCount] using physicalSourceGridCardinality_eq (encodeThreeCNF
            formula).length formula
  rw [← gridCardinality]
  simpa only [Fintype.card_coe, Finset.card_pos] using
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid_card_pos (encodeThreeCNF
          formula).length
        (srcFormula formula)

private def physicalColumnGridQuotientUnary :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryQuotient
    sourceExplicitAffineCellColumn
    physicalCoefficientFieldCardinalityUnary

private noncomputable def paperVariableArityPhysicalColumnGridQuotientUnaryComputable :
    BitTM
      physicalColumnGridQuotientUnary :=
  sourcePhysicalComputedUnaryQuotientComputable
    sourceExplicitAffineCellColumnComputable
    paperVariableArityPhysicalCoefficientFieldCardinalityUnaryComputable

@[simp] private theorem paperVariableArityPhysicalColumnGridQuotientUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalColumnGridQuotientUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (column / physFieldCard formula)
        true := by
  unfold physicalColumnGridQuotientUnary
  exact sourcePhysicalComputedUnaryQuotient_valid
    sourceExplicitAffineCellColumn
    physicalCoefficientFieldCardinalityUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    column (physFieldCard formula)
    (physicalCoefficientFieldCardinality_pos formula)
    (sourceExplicitAffineCellColumn_query row column
      (encodeThreeCNF formula))
    (paperVariableArityPhysicalCoefficientFieldCardinalityUnary_query
      row column formula)

/-- GapCVP reduction support. -/
def physicalColumnFieldValueRankUnary :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryRemainder
    sourceExplicitAffineCellColumn
    physicalCoefficientFieldCardinalityUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalColumnFieldValueRankUnaryComputable :
    BitTM
      physicalColumnFieldValueRankUnary :=
  sourcePhysicalComputedUnaryRemainderComputable
    sourceExplicitAffineCellColumnComputable
    paperVariableArityPhysicalCoefficientFieldCardinalityUnaryComputable

@[simp] theorem paperVariableArityPhysicalColumnFieldValueRankUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalColumnFieldValueRankUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (column % physFieldCard formula)
        true := by
  unfold physicalColumnFieldValueRankUnary
  exact sourcePhysicalComputedUnaryRemainder_valid
    sourceExplicitAffineCellColumn
    physicalCoefficientFieldCardinalityUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    column (physFieldCard formula)
    (physicalCoefficientFieldCardinality_pos formula)
    (sourceExplicitAffineCellColumn_query row column
      (encodeThreeCNF formula))
    (paperVariableArityPhysicalCoefficientFieldCardinalityUnary_query
      row column formula)

/-- GapCVP reduction support. -/
def physicalColumnGridRankUnary :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryRemainder
    physicalColumnGridQuotientUnary
    physicalCoefficientGridCardinalityUnary

/-- GapCVP reduction support. -/
noncomputable def physicalColumnGridRankUnaryComputable :
    BitTM
      physicalColumnGridRankUnary :=
  sourcePhysicalComputedUnaryRemainderComputable
    paperVariableArityPhysicalColumnGridQuotientUnaryComputable
    paperVariableArityPhysicalCoefficientGridCardinalityUnaryComputable

@[simp] theorem paperVariableArityPhysicalColumnGridRankUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalColumnGridRankUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        ((column / physFieldCard formula) %
          physGridCard formula)
        true := by
  unfold physicalColumnGridRankUnary
  exact sourcePhysicalComputedUnaryRemainder_valid
    physicalColumnGridQuotientUnary
    physicalCoefficientGridCardinalityUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    (column / physFieldCard formula)
    (physGridCard formula)
    (physicalCoefficientGridCardinality_pos formula)
    (paperVariableArityPhysicalColumnGridQuotientUnary_query
      row column formula)
    (paperVariableArityPhysicalCoefficientGridCardinalityUnary_query
      row column formula)

/-- GapCVP reduction support. -/
def physicalColumnTypeRankUnary :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryQuotient
    physicalColumnGridQuotientUnary
    physicalCoefficientGridCardinalityUnary

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalColumnTypeRankUnaryComputable :
    BitTM
      physicalColumnTypeRankUnary :=
  sourcePhysicalComputedUnaryQuotientComputable
    paperVariableArityPhysicalColumnGridQuotientUnaryComputable
    paperVariableArityPhysicalCoefficientGridCardinalityUnaryComputable

@[simp] theorem paperVariableArityPhysicalColumnTypeRankUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalColumnTypeRankUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        ((column / physFieldCard formula) /
          physGridCard formula)
        true := by
  unfold physicalColumnTypeRankUnary
  exact sourcePhysicalComputedUnaryQuotient_valid
    physicalColumnGridQuotientUnary
    physicalCoefficientGridCardinalityUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    (column / physFieldCard formula)
    (physGridCard formula)
    (physicalCoefficientGridCardinality_pos formula)
    (paperVariableArityPhysicalColumnGridQuotientUnary_query
      row column formula)
    (paperVariableArityPhysicalCoefficientGridCardinalityUnary_query
      row column formula)

private def physicalGlobalRowFieldRankUnary :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryQuotient
    sourceExplicitAffineCellRow
    physicalRightHandSideCellDegreeUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalGlobalRowFieldRankUnaryComputable :
    BitTM
      physicalGlobalRowFieldRankUnary :=
  sourcePhysicalComputedUnaryQuotientComputable
    sourceExplicitAffineCellRowComputable
    paperVariableArityPhysicalRightHandSideCellDegreeUnaryComputable

@[simp] private theorem paperVariableArityPhysicalGlobalRowFieldRankUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalGlobalRowFieldRankUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (row / physDegree formula) true := by
  unfold physicalGlobalRowFieldRankUnary
  exact sourcePhysicalComputedUnaryQuotient_valid
    sourceExplicitAffineCellRow
    physicalRightHandSideCellDegreeUnary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    row (physDegree formula)
    (GapCVP.Core.sourceFieldExponent_pos
      (GapCVP.Core.sourceSizeParameter_ge_one_hundred
        (encodeThreeCNF formula).length
        (srcFormula formula)))
    (sourceExplicitAffineCellRow_query row column
      (encodeThreeCNF formula))
    (paperVariableArityPhysicalRightHandSideCellDegreeUnary_query
      row column formula)

/-- GapCVP reduction support. -/
def physicalCoefficientUnaryEquality
    (first second : List Bool → List Bool) : List Bool → List Bool :=
  maskComputedWordEquality first second

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalCoefficientUnaryEqualityComputable
    {first second : List Bool → List Bool}
    (firstComputer : BitTM first)
    (secondComputer : BitTM second) :
    BitTM
      (physicalCoefficientUnaryEquality first second) :=
  maskComputedWordEqualityComputable
    firstComputer secondComputer

theorem physicalCoefficientUnaryEquality_valid
    (first second : List Bool → List Bool)
    (input : List Bool) (left right : ℕ)
    (firstValid : first input = List.replicate left true)
    (secondValid : second input = List.replicate right true) :
    physicalCoefficientUnaryEquality first second input =
      [decide (left = right)] := by
  unfold physicalCoefficientUnaryEquality
  rw [sourceQaryMaskSquareComputedWordEquality_valid,
    firstValid, secondValid]
  simp only [List.replicate_inj, or_true, and_true]

private def physicalColumnGlobalTypeBit :
    List Bool → List Bool :=
  physicalCoefficientUnaryEquality
    physicalColumnTypeRankUnary (fun _ => [])

private noncomputable def paperVariableArityPhysicalColumnGlobalTypeBitComputable :
    BitTM
      physicalColumnGlobalTypeBit :=
  paperVariableArityPhysicalCoefficientUnaryEqualityComputable
    paperVariableArityPhysicalColumnTypeRankUnaryComputable
    (sourceFixedWordComputable [])

@[simp] private theorem paperVariableArityPhysicalColumnGlobalTypeBit_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalColumnGlobalTypeBit
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      [decide
        (((column / physFieldCard formula) /
          physGridCard formula) = 0)] := by
  unfold physicalColumnGlobalTypeBit
  exact physicalCoefficientUnaryEquality_valid
    physicalColumnTypeRankUnary (fun _ => [])
    (affineCellQuery row column (encodeThreeCNF formula))
    ((column / physFieldCard formula) /
      physGridCard formula)
    0
    (paperVariableArityPhysicalColumnTypeRankUnary_query row column formula)
    rfl

private def physicalGlobalGridMatchBit :
    List Bool → List Bool :=
  physicalCoefficientUnaryEquality
    physicalColumnGridRankUnary
    physicalGlobalRowFieldRankUnary

private noncomputable def paperVariableArityPhysicalGlobalGridMatchBitComputable :
    BitTM
      physicalGlobalGridMatchBit :=
  paperVariableArityPhysicalCoefficientUnaryEqualityComputable
    physicalColumnGridRankUnaryComputable
    paperVariableArityPhysicalGlobalRowFieldRankUnaryComputable

@[simp] private theorem paperVariableArityPhysicalGlobalGridMatchBit_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalGlobalGridMatchBit
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      [decide
        (((column / physFieldCard formula) %
          physGridCard formula) =
          row / physDegree formula)] := by
  unfold physicalGlobalGridMatchBit
  exact physicalCoefficientUnaryEquality_valid
    physicalColumnGridRankUnary
    physicalGlobalRowFieldRankUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    ((column / physFieldCard formula) %
      physGridCard formula)
    (row / physDegree formula)
    (paperVariableArityPhysicalColumnGridRankUnary_query row column formula)
    (paperVariableArityPhysicalGlobalRowFieldRankUnary_query
      row column formula)

private def physicalGlobalFamilyCoefficientWord :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    physicalColumnGlobalTypeBit
    physicalGlobalGridMatchBit

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalGlobalFamilyCoefficientWordComputable :
    BitTM
      physicalGlobalFamilyCoefficientWord :=
  fourFamilyBooleanAndComputable
    paperVariableArityPhysicalColumnGlobalTypeBitComputable
    paperVariableArityPhysicalGlobalGridMatchBitComputable

@[simp] private theorem paperVariableArityPhysicalGlobalFamilyCoefficientWord_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalGlobalFamilyCoefficientWord
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      [decide
        (((column / physFieldCard formula) /
          physGridCard formula) = 0) &&
       decide
        (((column / physFieldCard formula) %
          physGridCard formula) =
            row / physDegree formula)] := by
  unfold physicalGlobalFamilyCoefficientWord
  exact fourFamilyBooleanAndOutput_bits
    physicalColumnGlobalTypeBit
    physicalGlobalGridMatchBit
    (affineCellQuery row column
      (encodeThreeCNF formula))
    (decide
      (((column / physFieldCard formula) /
        physGridCard formula) = 0))
    (decide
      (((column / physFieldCard formula) %
        physGridCard formula) =
          row / physDegree formula))
    (paperVariableArityPhysicalColumnGlobalTypeBit_query
      row column formula)
    (paperVariableArityPhysicalGlobalGridMatchBit_query
      row column formula)

/-- GapCVP reduction support. -/
def physicalGlobalCheckBit :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    physicalGlobalRowMarker
    (sourceFourFamilyBooleanAndOutput
      physicalRightHandSideBasisZeroBit
      physicalGlobalFamilyCoefficientWord)

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalGlobalCheckBitComputable :
    BitTM
      physicalGlobalCheckBit :=
  fourFamilyBooleanAndComputable
    paperVariableArityPhysicalGlobalRowMarkerComputable
    (fourFamilyBooleanAndComputable
      paperVariableArityPhysicalRightHandSideBasisZeroBitComputable
      paperVariableArityPhysicalGlobalFamilyCoefficientWordComputable)

@[simp] private theorem paperVariableArityPhysicalGlobalCheckBit_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalGlobalCheckBit
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      [decide
        (row < physicalFormulaGlobalBoundary formula) &&
        (decide (row % physDegree formula = 0) &&
          (decide
            (((column / physFieldCard formula) /
              physGridCard formula) = 0) &&
           decide
            (((column / physFieldCard formula) %
              physGridCard formula) =
                row / physDegree formula)))] := by
  let input := affineCellQuery row column
    (encodeThreeCNF formula)
  let basis := decide
    (row % physDegree formula = 0)
  let tag := decide
    (((column / physFieldCard formula) /
      physGridCard formula) = 0)
  let grid := decide
    (((column / physFieldCard formula) %
      physGridCard formula) =
        row / physDegree formula)
  have inner := fourFamilyBooleanAndOutput_bits
    physicalRightHandSideBasisZeroBit
    physicalGlobalFamilyCoefficientWord input
    basis (tag && grid)
    (paperVariableArityPhysicalRightHandSideBasisZeroBit_query
      row column formula)
    (paperVariableArityPhysicalGlobalFamilyCoefficientWord_query
      row column formula)
  exact fourFamilyBooleanAndOutput_bits
    physicalGlobalRowMarker
    (sourceFourFamilyBooleanAndOutput
      physicalRightHandSideBasisZeroBit
      physicalGlobalFamilyCoefficientWord)
    input
    (decide
      (row < physicalFormulaGlobalBoundary formula))
    (basis && (tag && grid))
    (paperVariableArityPhysicalGlobalRowMarker_query
      row column formula)
    inner

end PhysicalGlobalRefinementCoefficientTM

namespace PhysicalColumnOrderProjection

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinarySourceCoordinateOrder GapCVP.FormulaBridge GapCVP.SourceOrder
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalRowOrderProjection

theorem paperVariableAritySourceCoordinateFieldWordRank
    (encodingLength : ℕ) (formula : ThreeCNF)
    (column : Fin
      (sourceFormulaDimension encodingLength
        (srcFormula formula))) :
    ((sourceFormulaFieldCardOrder encodingLength
      (srcFormula formula)).symm
        ((sourceCoordinateWordOrder
          encodingLength formula column).2.2)).val =
      column.val % Fintype.card
        (sourceFormulaField encodingLength
          (srcFormula formula)) := by
  simp only [sourceCoordinateWordOrder, sourceFormulaCoordinateOrder, finProdFinEquiv,
      Equiv.symm_mk,
      Equiv.trans_apply, finCongr_apply, Equiv.coe_fn_mk, Equiv.prodCongr_apply, Prod.map_apply,
          Equiv.prodAssoc_apply,
      Equiv.coe_refl, id_eq, Equiv.symm_apply_apply, Fin.coe_modNat, Fin.val_cast]

theorem sourceCoordinateGridWordRank
    (encodingLength : ℕ) (formula : ThreeCNF)
    (column : Fin
      (sourceFormulaDimension encodingLength
        (srcFormula formula))) :
    ((sourceFormulaGridOrder encodingLength
      (srcFormula formula)).symm
        ((sourceCoordinateWordOrder
          encodingLength formula column).2.1)).val =
      (column.val / Fintype.card
        (sourceFormulaField encodingLength
          (srcFormula formula))) %
        (sourceFormulaGrid encodingLength
          (srcFormula formula)).card := by
  simp only [sourceCoordinateWordOrder, sourceFormulaCoordinateOrder, finProdFinEquiv,
      Equiv.symm_mk,
      Equiv.trans_apply, finCongr_apply, Equiv.coe_fn_mk, Equiv.prodCongr_apply, Prod.map_apply,
          Equiv.prodAssoc_apply,
      Equiv.coe_refl, id_eq, Equiv.symm_apply_apply, Fin.coe_modNat, Fin.coe_divNat, Fin.val_cast]

theorem sourceCoordinateTypeWordRank
    (encodingLength : ℕ) (formula : ThreeCNF)
    (column : Fin
      (sourceFormulaDimension encodingLength
        (srcFormula formula))) :
    ((sourceTypeCardWordOrder formula).symm
      ((sourceCoordinateWordOrder
        encodingLength formula column).1)).val =
      (column.val / Fintype.card
        (sourceFormulaField encodingLength
          (srcFormula formula))) /
        (sourceFormulaGrid encodingLength
          (srcFormula formula)).card := by
  simp only [sourceCoordinateWordOrder, sourceFormulaCoordinateOrder, finProdFinEquiv,
      Equiv.symm_mk,
      Equiv.trans_apply, finCongr_apply, Equiv.coe_fn_mk, Equiv.prodCongr_apply, Prod.map_apply,
          Equiv.prodAssoc_apply,
      Equiv.coe_refl, id_eq, Equiv.symm_apply_apply, Fin.coe_divNat, Fin.val_cast]

theorem physicalFormulaFieldCardinality_eq_card
    (formula : ThreeCNF) :
    Fintype.card
      (sourceFormulaField (encodeThreeCNF formula).length
        (srcFormula formula)) =
      physFieldCard formula := by
  exact sourceFormulaFieldWordOrder_card
    (encodeThreeCNF formula).length
    (srcFormula formula)

theorem physicalFormulaGridCardinality_eq_card
    (formula : ThreeCNF) :
    (sourceFormulaGrid (encodeThreeCNF formula).length
      (srcFormula formula)).card =
        physGridCard formula := by
  simpa only [physGridCard, physFieldCard, physDegree, physicalFormulaSize,
      physicalFormulaVariableCount,
      Fintype.card_coe] using physicalSourceGridCardinality_eq (encodeThreeCNF formula).length
          formula

private theorem paperVariableArityGlobalTypeWordRank_zero
    (formula : ThreeCNF) :
    ((sourceTypeCardWordOrder formula).symm
      (Sum.inl ())).val = 0 := by
  simp only [sourceTypeCardWordOrder, sourceTypeWordOrder, finSumFinEquiv, Equiv.symm_mk,
      List.get_eq_getElem,
      Equiv.symm_trans, Equiv.sumCongr_symm, finCongr_symm, Equiv.trans_apply,
          Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.coe_fn_mk, Sum.elim_inl, finCongr_apply, Fin.val_cast, Fin.val_castAdd,
          Fin.val_eq_zero]

private theorem paperVariableAritySourceTypeWord_isGlobal_iff
    (formula : ThreeCNF)
    (tableType : sourceSATTableType
      (srcFormula formula)) :
    tableType = Sum.inl () ↔
      ((sourceTypeCardWordOrder formula).symm
        tableType).val = 0 := by
  constructor
  · intro hglobal
    subst tableType
    exact paperVariableArityGlobalTypeWordRank_zero formula
  · intro hrank
    apply (sourceTypeCardWordOrder formula).symm.injective
    apply Fin.ext
    exact hrank.trans
      (paperVariableArityGlobalTypeWordRank_zero formula).symm

private theorem paperVariableAritySourceCoordinate_isGlobal_iff
    (formula : ThreeCNF)
    (column : Fin
      (sourceFormulaDimension (encodeThreeCNF formula).length
        (srcFormula formula))) :
    (sourceCoordinateWordOrder
      (encodeThreeCNF formula).length formula column).1 = Sum.inl () ↔
      (column.val /
        physFieldCard formula) /
        physGridCard formula = 0 := by
  rw [paperVariableAritySourceTypeWord_isGlobal_iff formula,
    sourceCoordinateTypeWordRank
      (encodeThreeCNF formula).length formula column,
    physicalFormulaFieldCardinality_eq_card,
    physicalFormulaGridCardinality_eq_card]

end PhysicalColumnOrderProjection

namespace PhysicalGlobalCoefficientCorrectness

open scoped BigOperators

open GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryExplicitAffineSystem
open GapCVP.BinarySourceCoordinateOrder GapCVP.FormulaBridge GapCVP.SourceOrder
open GapCVP.PhysicalColumnOrder GapCVP.PhysicalColumnOrderProjection GapCVP.PhysicalFamilyRowTM
open GapCVP.MatrixEntrySemantics GapCVP.PhysicalRowOrderProjection
open GapCVP.PhysicalGlobalRefinementCoefficientTM

attribute [local instance] Classical.propDecidable

private theorem paperVariableArityPhysicalWordCoordinateDelta_eq_coordinate
    (encodingLength : ℕ) (formula : ThreeCNF)
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula))
    (tableType : sourceSATTableType
      (srcFormula formula))
    (point : sourceSATGridPoint
      (PaperVariableArityPhysicalWordGrid encodingLength formula))
    (value : PaperVariableArityPhysicalWordField
      encodingLength formula) :
    physicalWordCoordinateDelta
        encodingLength formula column tableType point value =
      if (tableType, point, value) =
        sourceCoordinateWordOrder
          encodingLength formula column
      then 1 else 0 := by
  let order := sourceCoordinateWordOrder
    encodingLength formula
  change
    (if order.symm (tableType, point, value) = column
      then 1 else 0) =
    if (tableType, point, value) = order column
      then 1 else 0
  by_cases hcoordinate :
      (tableType, point, value) = order column
  · have hcolumn :
        order.symm (tableType, point, value) = column := by
      rw [hcoordinate, order.symm_apply_apply]
    rw [ite_eq_left hcolumn, ite_eq_left hcoordinate]
  · have hcolumn :
        order.symm (tableType, point, value) ≠ column := by
      intro hequal
      apply hcoordinate
      have happly := congrArg order hequal
      simpa only [Equiv.apply_symm_apply] using happly
    rw [ite_eq_right hcolumn, ite_eq_right hcoordinate]

private theorem paperVariableArityPhysicalWordGlobalFieldCoefficient_eq_coordinate
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula))))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    physicalWordFamilyFieldCoefficient
        encodingLength formula (.inl ()) row column =
      if
        (sourceCoordinateWordOrder
          encodingLength formula column).1 = .inl () ∧
        (sourceCoordinateWordOrder
          encodingLength formula column).2.1 =
          sourceFormulaExplicitGridOrder
            encodingLength
            (srcFormula formula) row
      then 1 else 0 := by
  let decoded := sourceCoordinateWordOrder
    encodingLength formula column
  let grid := sourceFormulaExplicitGridOrder
    encodingLength (srcFormula formula) row
  rw [paperVariableArityPhysicalWordGlobalFieldCoefficient
    encodingLength formula row column]
  simp_rw [paperVariableArityPhysicalWordCoordinateDelta_eq_coordinate
    encodingLength formula column]
  change
    (∑ value : PaperVariableArityPhysicalWordField
      encodingLength formula,
      if ((.inl () : sourceSATTableType
            (srcFormula formula)), grid, value) = decoded
      then 1 else 0) =
      if decoded.1 = .inl () ∧ decoded.2.1 = grid then 1 else 0
  by_cases htype : decoded.1 = .inl ()
  · by_cases hgrid : decoded.2.1 = grid
    · have hcoordinate (value : PaperVariableArityPhysicalWordField
          encodingLength formula) :
          ((.inl () : sourceSATTableType
              (srcFormula formula)), grid, value) =
            decoded ↔ value = decoded.2.2 := by
        constructor
        · intro hequal
          exact congrArg (fun coordinate => coordinate.2.2) hequal
        · intro hequal
          apply Prod.ext
          · exact htype.symm
          · apply Prod.ext
            · exact hgrid.symm
            · exact hequal
      simp_rw [hcoordinate]
      simp only [htype, hgrid, and_self, ite_true]
      simpa only [Finset.mem_univ, ite_true] using
        Finset.sum_ite_eq'
          (Finset.univ : Finset
            (PaperVariableArityPhysicalWordField encodingLength formula))
          decoded.2.2
          (fun _ : PaperVariableArityPhysicalWordField
            encodingLength formula => 1)
    · have hcoordinate (value : PaperVariableArityPhysicalWordField
          encodingLength formula) :
          ((.inl () : sourceSATTableType
              (srcFormula formula)), grid, value) ≠
            decoded := by
        intro hequal
        apply hgrid
        exact (congrArg (fun coordinate => coordinate.2.1) hequal).symm
      simp only [hcoordinate, ite_false, Finset.sum_const_zero,
        htype, true_and, hgrid]
  · have hcoordinate (value : PaperVariableArityPhysicalWordField
        encodingLength formula) :
        ((.inl () : sourceSATTableType
            (srcFormula formula)), grid, value) ≠
          decoded := by
      intro hequal
      apply htype
      exact (congrArg (fun coordinate => coordinate.1) hequal).symm
    simp only [hcoordinate, ite_false, Finset.sum_const_zero,
      htype, false_and]

private theorem paperVariableArityPhysicalGlobalRowFieldRank
    (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
    (hglobal :
      (physicalWordDecodedRow
        (encodeThreeCNF formula).length formula row).1 = .inl ()) :
    (physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row).2.1.val =
        row.val / physDegree formula := by
  let encodingLength := (encodeThreeCNF formula).length
  have hfirst :
      physicalRowDependentFamilyIndex
        encodingLength formula row =
      ⟨0, physicalFamilyTagCount_pos
        encodingLength formula⟩ := by
    apply (paperExplicitFamilyWordOrder
      encodingLength formula).injective
    calc
      paperExplicitFamilyWordOrder
          encodingLength formula
          (physicalRowDependentFamilyIndex
            encodingLength formula row) =
          (physicalWordDecodedRow
            encodingLength formula row).1 :=
        (physicalRowOrder_family
          encodingLength formula row).symm
      _ = .inl () := hglobal
      _ = paperExplicitFamilyWordOrder
          encodingLength formula
          ⟨0, physicalFamilyTagCount_pos
            encodingLength formula⟩ :=
        (physicalFamilyWordOrder_zero
          encodingLength formula).symm
  have hzero :
      (physicalRowDependentFamilyIndex
        encodingLength formula row).val = 0 :=
    congrArg Fin.val hfirst
  have hprefix :
      (∑ index : Fin
        (physicalRowDependentFamilyIndex
          encodingLength formula row).val,
        paperExplicitBinaryFamilyBlockCount
          encodingLength formula
          (Fin.castLE
            (physicalRowDependentFamilyIndex
              encodingLength formula row).isLt.le index)) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    exact Fin.elim0 (Fin.cast hzero index)
  have hrank := physicalRowDependentRank_eq_prefix
    encodingLength formula row
  have hblock :
      row.val =
        (physicalRowDependentBlockRank
          encodingLength formula row).val := by
    omega
  rw [physicalRowOrder_fieldRow]
  change
    (physicalRowDependentBlockRank
      encodingLength formula row).val /
        physDegree formula =
      row.val / physDegree formula
  rw [hblock]

private theorem paperVariableArityPhysicalGlobalFieldCoefficient_eq_mixedRadix
    (formula : ThreeCNF)
    (fieldRow : Fin
      (Fintype.card
        (ExplicitGridPoint (encodeThreeCNF formula).length
          (srcFormula formula))))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula)) :
    physicalWordFamilyFieldCoefficient
        (encodeThreeCNF formula).length formula
        (.inl ()) fieldRow column =
      if
        (column.val / physFieldCard formula) /
            physGridCard formula = 0 ∧
        (column.val / physFieldCard formula) %
            physGridCard formula =
              fieldRow.val
      then 1 else 0 := by
  let encodingLength := (encodeThreeCNF formula).length
  let decoded := sourceCoordinateWordOrder
    encodingLength formula column
  have htype :
      decoded.1 = .inl () ↔
        (column.val /
          physFieldCard formula) /
          physGridCard formula = 0 :=
    paperVariableAritySourceCoordinate_isGlobal_iff formula column
  have hgridrank :
      ((sourceFormulaGridOrder
        encodingLength (srcFormula formula)).symm
          decoded.2.1).val =
        (column.val /
          physFieldCard formula) %
          physGridCard formula := by
    simpa only [encodingLength, decoded,
      physicalFormulaFieldCardinality_eq_card,
      physicalFormulaGridCardinality_eq_card] using
      sourceCoordinateGridWordRank
        encodingLength formula column
  have hfieldrank :
      ((sourceFormulaGridOrder
        encodingLength (srcFormula formula)).symm
        (sourceFormulaExplicitGridOrder
          encodingLength (srcFormula formula)
          fieldRow)).val = fieldRow.val := by
    simp only [sourceFormulaExplicitGridOrder, Equiv.trans_apply, finCongr_apply,
        Equiv.symm_apply_apply,
        Fin.val_cast]
  have hgrid :
      decoded.2.1 =
          sourceFormulaExplicitGridOrder
            encodingLength (srcFormula formula)
            fieldRow ↔
        (column.val /
          physFieldCard formula) %
          physGridCard formula =
            fieldRow.val := by
    constructor
    · intro hequal
      have hrank := congrArg
        (fun point =>
          ((sourceFormulaGridOrder
            encodingLength (srcFormula formula)).symm
            point).val) hequal
      exact hgridrank.symm.trans (hrank.trans hfieldrank)
    · intro hrank
      apply (sourceFormulaGridOrder
        encodingLength (srcFormula formula)).symm.injective
      apply Fin.ext
      exact hgridrank.trans (hrank.trans hfieldrank.symm)
  rw [paperVariableArityPhysicalWordGlobalFieldCoefficient_eq_coordinate]
  by_cases hsource :
      decoded.1 = .inl () ∧
        decoded.2.1 =
          sourceFormulaExplicitGridOrder
            encodingLength (srcFormula formula)
            fieldRow
  · have hphysical :
        (column.val /
          physFieldCard formula) /
            physGridCard formula = 0 ∧
        (column.val /
          physFieldCard formula) %
            physGridCard formula =
              fieldRow.val :=
      ⟨htype.mp hsource.1, hgrid.mp hsource.2⟩
    rw [ite_eq_left hsource, ite_eq_left hphysical]
  · have hphysical :
        ¬ ((column.val /
            physFieldCard formula) /
            physGridCard formula = 0 ∧
          (column.val /
            physFieldCard formula) %
            physGridCard formula =
              fieldRow.val) := by
      intro hphysical
      exact hsource ⟨htype.mpr hphysical.1, hgrid.mpr hphysical.2⟩
    rw [ite_eq_right hsource, ite_eq_right hphysical]

private theorem paperVariableArityPhysicalGlobalWordBinaryCheck_eq_mixedRadix
    (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (hglobal :
      (physicalWordDecodedRow
        (encodeThreeCNF formula).length formula row).1 = .inl ()) :
    (physicalWordBinarySystem
      (encodeThreeCNF formula).length formula).check row column =
      if
        (column.val /
          physFieldCard formula) /
            physGridCard formula = 0 ∧
        (column.val /
          physFieldCard formula) %
            physGridCard formula =
              row.val / physDegree formula
      then bitValue
        (decide (row.val % physDegree formula = 0))
      else 0 := by
  have hfield := paperVariableArityPhysicalGlobalRowFieldRank
    formula row hglobal
  have hbasis :
      (physicalWordDecodedRow
        (encodeThreeCNF formula).length formula row).2.2.val =
        row.val % physDegree formula :=
    physicalRowOrder_basis_val
      (encodeThreeCNF formula).length formula row
  rw [physicalWordBinaryCheckCoefficient]
  generalize hdecoded :
    physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row = decoded
      at hglobal hfield hbasis ⊢
  rcases decoded with ⟨family, fieldRow, basis⟩
  cases family with
  | inl value =>
    cases value
    change fieldRow.val =
      row.val / physDegree formula at hfield
    change basis.val =
      row.val % physDegree formula at hbasis
    rw [paperVariableArityPhysicalGlobalFieldCoefficient_eq_mixedRadix]
    rw [hfield]
    split_ifs
    · rw [paperVariableArityPhysicalFieldBasis_one_coordinate]
      rw [hbasis]
    · simp only [map_zero, Pi.zero_apply]
  | inr value =>
    cases hglobal

private theorem paperVariableArityPhysicalGlobalCheckBit_valid_of_global
    (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (hglobal :
      row.val < physicalFormulaGlobalBoundary formula) :
    physicalGlobalCheckBit
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).check
            row column = 1)] := by
  have hsource :
      row.val < physicalSourceGlobalBoundary
        (encodeThreeCNF formula).length formula := by
    change row.val <
      Fintype.card
        (ExplicitGridPoint (encodeThreeCNF formula).length
          (srcFormula formula)) *
        physDegree formula
    rw [physicalSourceGridCardinality_eq]
    exact hglobal
  have hfamily :=
    (paperVariableArityPhysicalRowOrder_global_iff
      (encodeThreeCNF formula).length formula row).mpr hsource
  have hcheck := paperVariableArityPhysicalGlobalWordBinaryCheck_eq_mixedRadix
    formula row column hfamily
  rw [paperVariableArityPhysicalGlobalCheckBit_query, hcheck]
  apply congrArg (fun bit : Bool => [bit])
  by_cases htype :
      (column.val /
        physFieldCard formula) /
        physGridCard formula = 0
  · by_cases hgrid :
        (column.val /
          physFieldCard formula) %
          physGridCard formula =
            row.val / physDegree formula
    · by_cases hbasis :
          row.val % physDegree formula = 0
      · simp only [hglobal, htype, hgrid, hbasis, decide_true,
          and_self, ↓reduceIte, bitValue, Bool.true_and]
      · simp only [hglobal, htype, hgrid, hbasis, decide_true,
          decide_false, and_self, ↓reduceIte, bitValue,
          Bool.false_eq_true, zero_ne_one, Bool.true_and,
          Bool.false_and]
    · simp only [hglobal, htype, hgrid, decide_true, decide_false,
        and_false, ↓reduceIte, zero_ne_one, Bool.and_false]
  · simp only [hglobal, htype, decide_true, decide_false,
      false_and, ↓reduceIte, zero_ne_one, Bool.false_and,
      Bool.and_false]

theorem paperVariableArityPhysicalGlobalCheckBit_valid
    (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula)) :
    physicalGlobalCheckBit
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        (row.val < physicalFormulaGlobalBoundary formula) &&
        decide
          ((physicalWordBinarySystem
            (encodeThreeCNF formula).length formula).check
              row column = 1)] := by
  by_cases hglobal :
      row.val < physicalFormulaGlobalBoundary formula
  · rw [paperVariableArityPhysicalGlobalCheckBit_valid_of_global
      formula row column hglobal]
    simp only [hglobal, decide_true,
        Bool.true_and]
  · rw [paperVariableArityPhysicalGlobalCheckBit_query]
    simp only [hglobal, decide_false, Nat.div_eq_zero_iff, Bool.decide_or, Bool.false_and]

end PhysicalGlobalCoefficientCorrectness

namespace PhysicalRefinementFieldCoordinateCorrectness

open scoped BigOperators

open GapCVP.Core GapCVP.BinarySourceRowOrder GapCVP.BinaryExplicitAffineSystem
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalGlobalCoefficientCorrectness

attribute [local instance] Classical.propDecidable

private theorem paperVariableArityPhysicalWordRefinementFieldCoefficient_eq_coordinate
    (encodingLength : ℕ)
    (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length)
    (row : Fin
      (Fintype.card
        (ExplicitGridPoint encodingLength
          (srcFormula formula) ×
          PaperVariableArityPhysicalWordField encodingLength formula)))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    physicalWordFamilyFieldCoefficient
        encodingLength formula (.inr (.inl clause)) row column =
      if
        (sourceCoordinateWordOrder
          encodingLength formula column).2.1 =
            (sourceFormulaExplicitRefinementOrder
              encodingLength (srcFormula formula) row).1 ∧
        (sourceCoordinateWordOrder
          encodingLength formula column).2.2 =
            (sourceFormulaExplicitRefinementOrder
              encodingLength (srcFormula formula) row).2 ∧
        ((sourceCoordinateWordOrder
          encodingLength formula column).1 = .inl () ∨
          ∃ tuple :
            ((srcFormula formula).clauses.get
              clause).SatisfyingLocalTuple,
            (sourceCoordinateWordOrder
              encodingLength formula column).1 =
                .inr ⟨clause, tuple⟩)
      then 1 else 0 := by
  let decoded := sourceCoordinateWordOrder
    encodingLength formula column
  let position := sourceFormulaExplicitRefinementOrder
    encodingLength (srcFormula formula) row
  rw [paperVariableArityPhysicalWordRefinementFieldCoefficient]
  dsimp only
  simp_rw [paperVariableArityPhysicalWordCoordinateDelta_eq_coordinate
    encodingLength formula column]
  change
    (if
      ((.inl () : sourceSATTableType
        (srcFormula formula)),
        position.1, position.2) = decoded
      then 1 else 0) -
      (∑ tuple :
        ((srcFormula formula).clauses.get
          clause).SatisfyingLocalTuple,
        if
          ((.inr ⟨clause, tuple⟩ : sourceSATTableType
            (srcFormula formula)),
            position.1, position.2) = decoded
        then 1 else 0) =
      if
        decoded.2.1 = position.1 ∧
        decoded.2.2 = position.2 ∧
          (decoded.1 = .inl () ∨
            ∃ tuple :
              ((srcFormula formula).clauses.get
                clause).SatisfyingLocalTuple,
              decoded.1 = .inr ⟨clause, tuple⟩)
      then 1 else 0
  rcases decoded with ⟨type, grid, value⟩
  rcases position with ⟨point, entry⟩
  dsimp
  by_cases hgrid : grid = point
  · subst grid
    by_cases hvalue : value = entry
    · subst value
      rcases type with ⟨⟩ | ⟨selectedClause, selectedTuple⟩
      · simp only [List.get_eq_getElem, ↓reduceIte, Prod.mk.injEq, reduceCtorEq, and_true,
          Finset.sum_const_zero,
            sub_zero, exists_false, or_false, and_self]
      · by_cases hclause : selectedClause = clause
        · subst selectedClause
          simp only [List.get_eq_getElem, Prod.mk.injEq, reduceCtorEq, and_true, ↓reduceIte,
              Sum.inr.injEq,
              Sigma.mk.injEq, heq_eq_eq, true_and, Finset.sum_ite_eq', Finset.mem_univ,
                  CharTwo.sub_eq_add, zero_add, exists_eq',
              or_true, and_self]
        · simp only [List.get_eq_getElem, Prod.mk.injEq, reduceCtorEq, and_true, ↓reduceIte,
            Sum.inr.injEq,
              Sigma.mk.injEq, Ne.symm hclause, false_and, Finset.sum_const_zero, sub_self,
                  exists_and_left, Subtype.exists,
              false_or, true_and, right_eq_ite_iff, zero_ne_one, imp_false, not_and, not_exists]
          aesop
    · simp only [Prod.mk.injEq, Ne.symm hvalue, and_false, ↓reduceIte, Finset.sum_const_zero,
        sub_self,
          Subtype.exists, true_and, right_eq_ite_iff, zero_ne_one, imp_false, not_and, not_or,
              not_exists]
      aesop
  · simp only [Prod.mk.injEq, Ne.symm hgrid, false_and, and_false, ↓reduceIte,
      Finset.sum_const_zero, sub_self,
        Subtype.exists, right_eq_ite_iff, zero_ne_one, imp_false, not_and, not_or, not_exists]
    aesop

end PhysicalRefinementFieldCoordinateCorrectness

namespace PhysicalRefinementRowProjection

open scoped BigOperators

open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem
open GapCVP.BinarySourceCoordinateOrder GapCVP.BinarySourceRowOrder GapCVP.FormulaBridge
open GapCVP.SourceOrder GapCVP.PhysicalFamilyRowTM GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalRowOrderProjection

theorem physicalRefinementGridCard_eq
    (formula : ThreeCNF) :
    Fintype.card
      (ExplicitGridPoint (encodeThreeCNF formula).length
        (srcFormula formula)) =
      physGridCard formula := by
  simpa only [Fintype.card_coe, physGridCard, physFieldCard, physDegree, physicalFormulaSize,
      physicalFormulaVariableCount] using physicalSourceGridCardinality_eq (encodeThreeCNF
          formula).length formula

private theorem paperVariableArityPhysicalRefinementFieldCard_eq
    (formula : ThreeCNF) :
    Fintype.card
      (PaperVariableArityPhysicalWordField
        (encodeThreeCNF formula).length formula) =
      physFieldCard formula := by
  exact sourceFiniteField_card
    (sourceSizeParameter_ge_one_hundred
      (encodeThreeCNF formula).length
      (srcFormula formula))

/-- GapCVP reduction support. -/
abbrev physicalRefinementBlockWidth
    (formula : ThreeCNF) : ℕ :=
  physGridCard formula *
    physFieldCard formula *
      physDegree formula

theorem physicalRefinementDegree_pos
    (formula : ThreeCNF) :
    0 < physDegree formula :=
  sourceFieldExponent_pos
    (sourceSizeParameter_ge_one_hundred
      (encodeThreeCNF formula).length
      (srcFormula formula))

private theorem paperVariableArityPhysicalRefinementFieldCard_pos
    (formula : ThreeCNF) :
    0 < physFieldCard formula := by
  exact pow_pos (by decide : 0 < (2 : ℕ)) _

theorem physicalRefinementGridCard_pos
    (formula : ThreeCNF) :
    0 < physGridCard formula := by
  rw [← physicalRefinementGridCard_eq formula]
  simpa only [Fintype.card_coe, Finset.card_pos] using
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid_card_pos (encodeThreeCNF
          formula).length
        (srcFormula formula)

private theorem paperVariableArityPhysicalRefinementBlockWidth_pos
    (formula : ThreeCNF) :
    0 < physicalRefinementBlockWidth formula := by
  exact Nat.mul_pos
    (Nat.mul_pos
      (physicalRefinementGridCard_pos formula)
      (paperVariableArityPhysicalRefinementFieldCard_pos formula))
    (physicalRefinementDegree_pos formula)

theorem physicalRefinementFamilySourceBlockCount
    (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length) :
    paperExplicitBinaryFamilyBlockCount
      (encodeThreeCNF formula).length formula
      (physicalRefinementFamilyIndex
        (encodeThreeCNF formula).length formula clause) =
      physicalRefinementBlockWidth formula := by
  rw [paperVariableArityPhysicalRefinementFamilyBlockCount,
    physicalRefinementGridCard_eq,
    paperVariableArityPhysicalRefinementFieldCard_eq]

private theorem paperVariableArityPhysicalRefinementFamilyPrefix
    (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length) :
    physicalSigmaPrefix
      (paperExplicitBinaryFamilyBlockCount
        (encodeThreeCNF formula).length formula)
      (physicalRefinementFamilyIndex
        (encodeThreeCNF formula).length formula clause) =
      physicalFormulaGlobalBoundary formula +
        clause.val * physicalRefinementBlockWidth formula := by
  have familyBound :
      1 + clause.val ≤
        paperExplicitFamilyTagCount
          (encodeThreeCNF formula).length formula := by
    have bounded :=
      (physicalRefinementFamilyIndex
        (encodeThreeCNF formula).length formula clause).isLt
    rw [paperVariableArityPhysicalRefinementFamilyIndex_val] at bounded
    omega
  unfold physicalSigmaPrefix
  change
    (∑ index : Fin (1 + clause.val),
      paperExplicitBinaryFamilyBlockCount
        (encodeThreeCNF formula).length formula
        (Fin.castLE familyBound index)) =
      physicalFormulaGlobalBoundary formula +
        clause.val * physicalRefinementBlockWidth formula
  rw [Fin.sum_univ_add, Fin.sum_univ_one]
  have first :
      (Fin.castLE familyBound
        (Fin.castAdd clause.val (0 : Fin 1))) =
      (⟨0, physicalFamilyTagCount_pos
        (encodeThreeCNF formula).length formula⟩ :
          Fin (paperExplicitFamilyTagCount
            (encodeThreeCNF formula).length formula)) := by
    apply Fin.ext
    rfl
  rw [first, physicalFirstFamilyBlockCount,
    physicalRefinementGridCard_eq]
  congr 1
  have blocks :
      (∑ index : Fin clause.val,
        paperExplicitBinaryFamilyBlockCount
          (encodeThreeCNF formula).length formula
          (Fin.castLE familyBound (Fin.natAdd 1 index))) =
        ∑ _index : Fin clause.val,
          physicalRefinementBlockWidth formula := by
    apply Finset.sum_congr rfl
    intro index _
    let selectedClause :
        Fin (srcFormula formula).clauses.length :=
      ⟨index.val, Nat.lt_trans index.isLt clause.isLt⟩
    have selected :
        (Fin.castLE familyBound (Fin.natAdd 1 index)) =
          physicalRefinementFamilyIndex
            (encodeThreeCNF formula).length formula selectedClause := by
      apply Fin.ext
      simp only [Fin.val_castLE, Fin.val_natAdd,
          paperVariableArityPhysicalRefinementFamilyIndex_val,
        selectedClause]
    rw [selected,
      physicalRefinementFamilySourceBlockCount]
  rw [blocks]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

private theorem paperVariableArityPhysicalRowOrder_refinementClause_iff
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (clause : Fin (srcFormula formula).clauses.length) :
    (physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row).1 =
        .inr (.inl clause) ↔
      physicalFormulaGlobalBoundary formula +
          clause.val * physicalRefinementBlockWidth formula
          ≤ row.val ∧
        row.val <
          physicalFormulaGlobalBoundary formula +
            (clause.val + 1) *
              physicalRefinementBlockWidth formula := by
  let encodingLength := (encodeThreeCNF formula).length
  let blockCount := paperExplicitBinaryFamilyBlockCount
    encodingLength formula
  let selectedFamily := physicalRefinementFamilyIndex
    encodingLength formula clause
  calc
    (physicalWordDecodedRow
        encodingLength formula row).1 = .inr (.inl clause) ↔
      physicalRowDependentFamilyIndex
        encodingLength formula row = selectedFamily := by
        rw [physicalRowOrder_family]
        change
          paperExplicitFamilyWordOrder
            encodingLength formula
            (physicalRowDependentFamilyIndex
              encodingLength formula row) = .inr (.inl clause) ↔
          physicalRowDependentFamilyIndex
            encodingLength formula row =
              (paperExplicitFamilyWordOrder
                encodingLength formula).symm (.inr (.inl clause))
        exact (paperExplicitFamilyWordOrder
          encodingLength formula).eq_symm_apply.symm
    _ ↔ physicalSigmaPrefix blockCount selectedFamily
          ≤ row.val ∧
        row.val <
          physicalSigmaPrefix blockCount selectedFamily +
            blockCount selectedFamily := by
        exact paperVariableArityPhysicalSigmaFamilyIndex_eq_iff
          blockCount row selectedFamily
    _ ↔ physicalFormulaGlobalBoundary formula +
          clause.val * physicalRefinementBlockWidth formula
          ≤ row.val ∧
        row.val <
          physicalFormulaGlobalBoundary formula +
            (clause.val + 1) *
              physicalRefinementBlockWidth formula := by
        change
          physicalSigmaPrefix
              (paperExplicitBinaryFamilyBlockCount
                (encodeThreeCNF formula).length formula)
              (physicalRefinementFamilyIndex
                (encodeThreeCNF formula).length formula clause) ≤ row.val ∧
            row.val <
              physicalSigmaPrefix
                (paperExplicitBinaryFamilyBlockCount
                  (encodeThreeCNF formula).length formula)
                (physicalRefinementFamilyIndex
                  (encodeThreeCNF formula).length formula clause) +
                paperExplicitBinaryFamilyBlockCount
                  (encodeThreeCNF formula).length formula
                  (physicalRefinementFamilyIndex
                    (encodeThreeCNF formula).length formula clause) ↔ _
        rw [paperVariableArityPhysicalRefinementFamilyPrefix,
          physicalRefinementFamilySourceBlockCount]
        simp only [Nat.add_mul, one_mul, Nat.add_assoc]

private theorem paperVariableArityPhysicalRefinementProductFieldWordRank
    (encodingLength : ℕ) (formula : ThreeCNF)
    (fieldRow : Fin
      (Fintype.card
        (ExplicitGridPoint encodingLength
          (srcFormula formula) ×
          PaperVariableArityPhysicalWordField encodingLength formula))) :
    ((sourceFormulaFieldCardOrder encodingLength
      (srcFormula formula)).symm
      ((sourceFormulaExplicitRefinementOrder encodingLength
        (srcFormula formula) fieldRow).2)).val =
      fieldRow.val %
        Fintype.card
          (PaperVariableArityPhysicalWordField encodingLength formula) := by
  simp only [sourceFormulaExplicitRefinementOrder, finProdFinEquiv, Equiv.symm_mk,
      Equiv.trans_apply,
      finCongr_apply, Equiv.coe_fn_mk, Equiv.prodCongr_apply, Prod.map_apply,
          Equiv.symm_apply_apply, Fin.coe_modNat,
      Fin.val_cast]

private theorem paperVariableArityPhysicalRefinementProductGridWordRank
    (encodingLength : ℕ) (formula : ThreeCNF)
    (fieldRow : Fin
      (Fintype.card
        (ExplicitGridPoint encodingLength
          (srcFormula formula) ×
          PaperVariableArityPhysicalWordField encodingLength formula))) :
    ((sourceFormulaGridOrder encodingLength
      (srcFormula formula)).symm
      ((sourceFormulaExplicitRefinementOrder encodingLength
        (srcFormula formula) fieldRow).1)).val =
      fieldRow.val /
        Fintype.card
          (PaperVariableArityPhysicalWordField encodingLength formula) := by
  simp only [sourceFormulaExplicitRefinementOrder, finProdFinEquiv, Equiv.symm_mk,
      sourceFormulaExplicitGridOrder, Equiv.trans_apply, finCongr_apply, Equiv.coe_fn_mk,
          Equiv.prodCongr_apply,
      Equiv.coe_trans, Prod.map_apply, Function.comp_apply, Equiv.symm_apply_apply, Fin.val_cast,
          Fin.coe_divNat]

end PhysicalRefinementRowProjection

namespace PhysicalRefinementSelectedRowProjection

open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.MatrixEntrySemantics GapCVP.PhysicalRowOrderProjection
open GapCVP.PhysicalRefinementRowProjection

private def physicalDecodedRefinementClause
    (formula : ThreeCNF) (row : ℕ)
    (inRefinement :
      physicalFormulaGlobalBoundary formula ≤ row ∧
        row < physicalFormulaRefinementBoundary formula) :
    Fin (srcFormula formula).clauses.length := by
  refine ⟨(row - physicalFormulaGlobalBoundary formula) /
    physicalRefinementBlockWidth formula, ?_⟩
  apply (Nat.div_lt_iff_lt_mul
    (paperVariableArityPhysicalRefinementBlockWidth_pos formula)).mpr
  have upper := inRefinement.2
  change
    row < physicalFormulaGlobalBoundary formula +
      (noTautClauses formula).length *
        physGridCard formula *
        physFieldCard formula *
        physDegree formula at upper
  change
    row - physicalFormulaGlobalBoundary formula <
      (srcFormula formula).clauses.length *
        (physGridCard formula *
          physFieldCard formula *
            physDegree formula)
  rw [paperVariableAritySourceFormula_clauses_length]
  simp only [← Nat.mul_assoc] at upper ⊢
  omega

private theorem paperVariableArityPhysicalDecodedRefinementClause_val
    (formula : ThreeCNF) (row : ℕ)
    (inRefinement :
      physicalFormulaGlobalBoundary formula ≤ row ∧
        row < physicalFormulaRefinementBoundary formula) :
    (physicalDecodedRefinementClause
      formula row inRefinement).val =
      (((row - physicalFormulaGlobalBoundary formula) /
        physDegree formula) /
          physFieldCard formula) /
            physGridCard formula := by
  change
    (row - physicalFormulaGlobalBoundary formula) /
      (physGridCard formula *
        physFieldCard formula *
          physDegree formula) = _
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  congr 1
  ac_rfl

private theorem paperVariableArityPhysicalRowOrder_refinementFamily
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inRefinement :
      physicalFormulaGlobalBoundary formula ≤ row.val ∧
        row.val <
          physicalFormulaRefinementBoundary formula) :
    (physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row).1 =
      .inr (.inl
        (physicalDecodedRefinementClause
          formula row.val inRefinement)) := by
  let width := physicalRefinementBlockWidth formula
  let localRank :=
    row.val - physicalFormulaGlobalBoundary formula
  have positive := paperVariableArityPhysicalRefinementBlockWidth_pos formula
  have selected :
      (physicalDecodedRefinementClause
        formula row.val inRefinement).val = localRank / width := by
    rfl
  apply (paperVariableArityPhysicalRowOrder_refinementClause_iff
    formula row
    (physicalDecodedRefinementClause
      formula row.val inRefinement)).mpr
  change
    physicalFormulaGlobalBoundary formula +
        (physicalDecodedRefinementClause
          formula row.val inRefinement).val * width ≤ row.val ∧
      row.val < physicalFormulaGlobalBoundary formula +
        ((physicalDecodedRefinementClause
          formula row.val inRefinement).val + 1) * width
  rw [selected]
  have lower := Nat.div_mul_le_self localRank width
  have upper := (Nat.div_lt_iff_lt_mul positive).mp
    (Nat.lt_succ_self (localRank / width))
  dsimp [localRank, width] at lower upper ⊢
  omega

private theorem paperVariableArityPhysicalRefinementDependentFamilyIndex
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inRefinement :
      physicalFormulaGlobalBoundary formula ≤ row.val ∧
        row.val <
          physicalFormulaRefinementBoundary formula) :
    physicalRowDependentFamilyIndex
      (encodeThreeCNF formula).length formula row =
      physicalRefinementFamilyIndex
        (encodeThreeCNF formula).length formula
        (physicalDecodedRefinementClause
          formula row.val inRefinement) := by
  apply (paperExplicitFamilyWordOrder
    (encodeThreeCNF formula).length formula).injective
  rw [← physicalRowOrder_family,
    paperVariableArityPhysicalRowOrder_refinementFamily formula row
      inRefinement]
  simp only [List.get_eq_getElem, physicalRefinementFamilyIndex, Equiv.apply_symm_apply]

private theorem paperVariableArityPhysicalRefinementDependentBlockRank_lt
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inRefinement :
      physicalFormulaGlobalBoundary formula ≤ row.val ∧
        row.val <
          physicalFormulaRefinementBoundary formula) :
    (physicalRowDependentBlockRank
      (encodeThreeCNF formula).length formula row).val <
      physicalRefinementBlockWidth formula := by
  calc
    (physicalRowDependentBlockRank
        (encodeThreeCNF formula).length formula row).val <
      paperExplicitBinaryFamilyBlockCount
        (encodeThreeCNF formula).length formula
        (physicalRowDependentFamilyIndex
          (encodeThreeCNF formula).length formula row) :=
      (physicalRowDependentBlockRank
        (encodeThreeCNF formula).length formula row).isLt
    _ = physicalRefinementBlockWidth formula := by
      rw [paperVariableArityPhysicalRefinementDependentFamilyIndex
        formula row inRefinement,
        physicalRefinementFamilySourceBlockCount]

private theorem paperVariableArityPhysicalRefinementGlobalSubtractedRank
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inRefinement :
      physicalFormulaGlobalBoundary formula ≤ row.val ∧
        row.val <
          physicalFormulaRefinementBoundary formula) :
    row.val - physicalFormulaGlobalBoundary formula =
      (physicalDecodedRefinementClause
        formula row.val inRefinement).val *
        physicalRefinementBlockWidth formula +
      (physicalRowDependentBlockRank
        (encodeThreeCNF formula).length formula row).val := by
  let blockCount := paperExplicitBinaryFamilyBlockCount
    (encodeThreeCNF formula).length formula
  let selected := physicalDecodedRefinementClause
    formula row.val inRefinement
  have family := paperVariableArityPhysicalRefinementDependentFamilyIndex
    formula row inRefinement
  have prefixEquality :
      physicalSigmaPrefix blockCount
          (physicalRowDependentFamilyIndex
            (encodeThreeCNF formula).length formula row) =
        physicalFormulaGlobalBoundary formula +
          selected.val *
            physicalRefinementBlockWidth formula := by
    calc
      physicalSigmaPrefix blockCount
          (physicalRowDependentFamilyIndex
            (encodeThreeCNF formula).length formula row) =
        physicalSigmaPrefix blockCount
          (physicalRefinementFamilyIndex
            (encodeThreeCNF formula).length formula selected) :=
        congrArg (physicalSigmaPrefix blockCount) family
      _ = physicalFormulaGlobalBoundary formula +
        selected.val *
          physicalRefinementBlockWidth formula :=
        paperVariableArityPhysicalRefinementFamilyPrefix formula selected
  have rank := physicalRowDependentRank_eq_prefix
    (encodeThreeCNF formula).length formula row
  change
    row.val =
      physicalSigmaPrefix blockCount
        (physicalRowDependentFamilyIndex
          (encodeThreeCNF formula).length formula row) +
      (physicalRowDependentBlockRank
        (encodeThreeCNF formula).length formula row).val at rank
  rw [prefixEquality] at rank
  dsimp [selected] at rank ⊢
  omega

private theorem paperVariableArityPhysicalRefinementDecodedFieldRowRank
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inRefinement :
      physicalFormulaGlobalBoundary formula ≤ row.val ∧
        row.val <
          physicalFormulaRefinementBoundary formula) :
    (physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row).2.1.val =
      ((row.val - physicalFormulaGlobalBoundary formula) /
        physDegree formula) %
          (physGridCard formula *
            physFieldCard formula) := by
  rw [physicalRowOrder_fieldRow]
  let localRank := (physicalRowDependentBlockRank
    (encodeThreeCNF formula).length formula row).val
  let grid := physGridCard formula
  let field := physFieldCard formula
  let degree := physDegree formula
  let clause := physicalDecodedRefinementClause
    formula row.val inRefinement
  have bounded : localRank < grid * field * degree :=
    paperVariableArityPhysicalRefinementDependentBlockRank_lt
      formula row inRefinement
  have degreePositive : 0 < degree :=
    physicalRefinementDegree_pos formula
  have quotientBound : localRank / degree < grid * field := by
    apply (Nat.div_lt_iff_lt_mul degreePositive).mpr
    simpa only [Nat.mul_assoc] using bounded
  have sourceRank :
      row.val - physicalFormulaGlobalBoundary formula =
        clause.val * (grid * field * degree) + localRank :=
    paperVariableArityPhysicalRefinementGlobalSubtractedRank
      formula row inRefinement
  change localRank / degree =
    ((row.val - physicalFormulaGlobalBoundary formula) /
      degree) % (grid * field)
  rw [sourceRank]
  have quotient :
      (clause.val * (grid * field * degree) + localRank) / degree =
        clause.val * (grid * field) + localRank / degree := by
    calc
      (clause.val * (grid * field * degree) + localRank) / degree =
        (degree * (clause.val * (grid * field)) + localRank) / degree := by
          congr 1
          ac_rfl
      _ = clause.val * (grid * field) + localRank / degree :=
        Nat.mul_add_div degreePositive
          (clause.val * (grid * field)) localRank
  rw [quotient]
  simp only [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt quotientBound, zero_add]

end PhysicalRefinementSelectedRowProjection

namespace PhysicalRefinementSelectedProductProjection

open GapCVP.BinaryEncoding GapCVP.SourceOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.MatrixEntrySemantics

private theorem paperVariableArityPhysicalDecodedRefinementBasisRank
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula)) :
    (physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row).2.2.val =
      row.val % physDegree formula :=
  GapCVP.PhysicalRowOrderProjection.physicalRowOrder_basis_val
    (encodeThreeCNF formula).length formula row

end PhysicalRefinementSelectedProductProjection

namespace PhysicalRefinementColumnTagProjection

open scoped BigOperators

open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.ClauseOffsetTM

private def physicalRetainedClause
    (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length) :
    ThreeClause :=
  (noTautClauses formula).get
    ⟨clause.val, by
      simpa only [srcFormula, paperSourceNormalizedClauses,
        List.length_map, List.length_attach] using clause.isLt⟩

@[simp] private theorem paperVariableArityPhysicalRetainedClauseWidth
    (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length) :
    paperFormulaClauseWidth formula clause =
      (paperSourceNormalizedClause
        (physicalRetainedClause formula clause)).length := by
  simp only [paperFormulaClauseWidth, paperSourceNormalizedClauses, paperFormulaRetainedClause,
      srcFormula,
      List.get_eq_getElem, List.getElem_attach, List.getElem_map,
          physicalRetainedClause]
  rfl

private theorem paperVariableArityPhysicalRetainedClauseWeight
    (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length) :
    2 ^ paperFormulaClauseWidth formula clause - 1 =
      sourceClauseWeight
        (physicalRetainedClause formula clause) := by
  simp only [paperVariableArityPhysicalRetainedClauseWidth, sourceClauseWeight]

private def paperDependentClausePrefix
    {size : ℕ} (weight : Fin size → ℕ) (clause : Fin size) : ℕ :=
  ∑ index : Fin clause.val, weight (Fin.castLE clause.isLt.le index)

private theorem paperVariableArityDependentClausePrefix_next_le
    {size : ℕ} (weight : Fin size → ℕ)
    (left right : Fin size) (hless : left.val < right.val) :
    paperDependentClausePrefix weight left + weight left ≤
      paperDependentClausePrefix weight right := by
  let extended : ℕ → ℕ :=
    fun index => if hindex : index < size
      then weight ⟨index, hindex⟩ else 0
  have leftSum :
      paperDependentClausePrefix weight left =
        ∑ index ∈ Finset.range left.val, extended index := by
    unfold paperDependentClausePrefix
    rw [← Fin.sum_univ_eq_sum_range extended left.val]
    apply Finset.sum_congr rfl
    intro index _
    simp only [extended, dite_eq_left (Nat.lt_trans index.isLt left.isLt)]
    rfl
  have rightSum :
      paperDependentClausePrefix weight right =
        ∑ index ∈ Finset.range right.val, extended index := by
    unfold paperDependentClausePrefix
    rw [← Fin.sum_univ_eq_sum_range extended right.val]
    apply Finset.sum_congr rfl
    intro index _
    simp only [extended, dite_eq_left (Nat.lt_trans index.isLt right.isLt)]
    rfl
  rw [leftSum, rightSum]
  calc
    (∑ index ∈ Finset.range left.val, extended index) + weight left =
        ∑ index ∈ Finset.range (left.val + 1), extended index := by
          rw [Finset.sum_range_succ]
          simp only [left.isLt, ↓reduceDIte, Fin.eta, extended]
    _ ≤ ∑ index ∈ Finset.range right.val, extended index :=
      Finset.sum_le_sum_of_subset
        (Finset.range_mono (by omega))

private theorem paperVariableArityDependentSigmaClause_iff
    {size : ℕ} (weight : Fin size → ℕ)
    (clause : Fin size)
    (word : Fin (∑ index : Fin size, weight index)) :
    ((finSigmaFinEquiv.symm word :
      (index : Fin size) × Fin (weight index)).fst = clause) ↔
      paperDependentClausePrefix weight clause ≤ word.val ∧
        word.val <
          paperDependentClausePrefix weight clause +
            weight clause := by
  let decoded : (index : Fin size) × Fin (weight index) :=
    finSigmaFinEquiv.symm word
  have rank : word.val =
      paperDependentClausePrefix weight decoded.fst +
        decoded.snd.val := by
    have hword : finSigmaFinEquiv decoded = word := by
      simp only [Equiv.apply_symm_apply, decoded]
    have hval := congrArg Fin.val hword
    simpa only [paperDependentClausePrefix, finSigmaFinEquiv_apply] using hval.symm
  constructor
  · intro hclause
    change decoded.fst = clause at hclause
    subst clause
    have hbound := decoded.snd.isLt
    omega
  · rintro ⟨hlower, hupper⟩
    change decoded.fst = clause
    apply Fin.ext
    rcases lt_trichotomy decoded.fst.val clause.val with hless | hequal | hgreater
    · have hdisjoint :=
        paperVariableArityDependentClausePrefix_next_le
          weight decoded.fst clause hless
      have hbound := decoded.snd.isLt
      omega
    · exact hequal
    · have hdisjoint :=
        paperVariableArityDependentClausePrefix_next_le
          weight clause decoded.fst hgreater
      omega

end PhysicalRefinementColumnTagProjection

namespace SourceClausePrefixBridge

open scoped BigOperators

open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.FormulaBridge GapCVP.ClauseOffsetTM
open GapCVP.SourceOrder GapCVP.CanonicalOffsetIdentity

private theorem paperVariableAritySourceFiniteClauseWeight_eq
    (formula : ThreeCNF)
    (index : Fin (srcFormula formula).clauses.length) :
    2 ^ paperFormulaClauseWidth formula index - 1 =
      sourceClauseWeight
        ((noTautClauses formula).get
          (Fin.cast
            (paperVariableAritySourceFormula_clauses_length formula)
            index)) := by
  let retainedIndex : Fin
      (noTautClauses formula).length :=
    Fin.cast
      (paperVariableAritySourceFormula_clauses_length formula)
      index
  have hindex :
      paperRetainedOriginalClauseIndexOrder
          formula retainedIndex = index := by
    apply Fin.ext
    rfl
  have hwidth := paperFormulaClauseWidth_retainedOriginal
    formula retainedIndex
  rw [hindex] at hwidth
  rw [hwidth]
  rfl

/-- GapCVP reduction support. -/
def sourceRetainedPrefixIndex
    (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length)
    (index : Fin clause.val) :
    Fin (noTautClauses formula).length :=
  Fin.cast (paperVariableAritySourceFormula_clauses_length formula)
    (Fin.castLE clause.isLt.le index)

private theorem paperVariableAritySourceIndexedClausePrefix_eq_weightSum
    (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length) :
    (∑ index : Fin clause.val,
      sourceClauseWeight
        ((noTautClauses formula).get
          (sourceRetainedPrefixIndex
            formula clause index))) =
      sourceClauseWeightSum
        ((noTautClauses formula).take clause.val) := by
  let retained := noTautClauses formula
  have hretained : clause.val ≤ retained.length := by
    have positive : clause.val < retained.length := by
      simpa only [srcFormula,
        GapCVP.SourcePreprocessingSemantics.paperSourceNormalizedClauses,
        List.length_map, List.length_attach, retained] using clause.isLt
    exact Nat.le_of_lt positive
  have htake : (retained.take clause.val).length = clause.val := by
    simp only [List.length_take, Nat.min_eq_left hretained]
  let order : Fin (retained.take clause.val).length ≃ Fin clause.val :=
    finCongr htake
  let weight : Fin clause.val → ℕ := fun index =>
    sourceClauseWeight
      (retained.get
        (sourceRetainedPrefixIndex
          formula clause index))
  change (∑ index : Fin clause.val, weight index) = _
  calc
    (∑ index : Fin clause.val, weight index) =
        ∑ index : Fin (retained.take clause.val).length,
          weight (order index) := by
          symm
          exact order.sum_comp weight
    _ = ∑ index : Fin (retained.take clause.val).length,
          sourceClauseWeight
            ((retained.take clause.val).get index) := by
          apply Finset.sum_congr rfl
          intro index _
          have hget :
              retained.get
                  (sourceRetainedPrefixIndex
                    formula clause (order index)) =
                (retained.take clause.val).get index := by
            simp only [List.get_eq_getElem, List.getElem_take]
            rfl
          exact congrArg sourceClauseWeight hget
    _ = sourceClauseWeightSum
          (retained.take clause.val) := by
          symm
          exact sourceListWeightSum
            (retained.take clause.val)
            sourceClauseWeight

theorem paperVariableAritySourceDependentClausePrefix_eq_weightSum
    (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length) :
    (∑ index : Fin clause.val,
      (2 ^ paperFormulaClauseWidth formula
        (Fin.castLE clause.isLt.le index) - 1)) =
      sourceClauseWeightSum
        ((noTautClauses formula).take clause.val) := by
  calc
    (∑ index : Fin clause.val,
      (2 ^ paperFormulaClauseWidth formula
        (Fin.castLE clause.isLt.le index) - 1)) =
      ∑ index : Fin clause.val,
        sourceClauseWeight
          ((noTautClauses formula).get
            (sourceRetainedPrefixIndex
              formula clause index)) := by
        apply Finset.sum_congr rfl
        intro index _
        exact paperVariableAritySourceFiniteClauseWeight_eq
          formula (Fin.castLE clause.isLt.le index)
    _ = sourceClauseWeightSum
          ((noTautClauses formula).take clause.val) :=
        paperVariableAritySourceIndexedClausePrefix_eq_weightSum
          formula clause

end SourceClausePrefixBridge

namespace PhysicalRefinementColumnTagSourceCorrectness

open scoped BigOperators

open GapCVP.BinaryEncoding GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.FormulaBridge GapCVP.SourceOrder
open GapCVP.ClauseOffsetTM GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalColumnOrderProjection
open GapCVP.PhysicalRefinementColumnTagProjection GapCVP.SourceClausePrefixBridge

theorem paperVariableAritySourceLocalTypeWordRank
    (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length)
    (tuple : ((srcFormula
      formula).clauses.get clause).SatisfyingLocalTuple) :
    ((sourceTypeCardWordOrder formula).symm
        (Sum.inr ⟨clause, tuple⟩)).val =
      1 + (finSigmaFinEquiv
        (n := fun index :
          Fin (srcFormula formula).clauses.length =>
            2 ^ paperFormulaClauseWidth formula index - 1)
        ⟨clause,
          (paperFormulaClauseTupleWordOrder
            formula clause).symm tuple⟩).val := by
  rfl

private theorem paperVariableAritySourceTypeLocalTag_iff
    (formula : ThreeCNF)
    (tableType : GapCVP.Core.sourceSATTableType
      (srcFormula formula))
    (clause : Fin (srcFormula formula).clauses.length) :
    (∃ tuple : ((srcFormula
        formula).clauses.get clause).SatisfyingLocalTuple,
      tableType = Sum.inr ⟨clause, tuple⟩) ↔
      ((sourceTypeCardWordOrder
        formula).symm tableType).val ≠ 0 ∧
        paperDependentClausePrefix
          (fun index =>
            2 ^ paperFormulaClauseWidth formula index - 1)
          clause ≤
            ((sourceTypeCardWordOrder
              formula).symm tableType).val - 1 ∧
        ((sourceTypeCardWordOrder
          formula).symm tableType).val - 1 <
          paperDependentClausePrefix
            (fun index =>
              2 ^ paperFormulaClauseWidth formula index - 1)
            clause +
              (2 ^ paperFormulaClauseWidth formula clause - 1) := by
  classical
  cases tableType with
  | inl global =>
      cases global
      constructor
      · rintro ⟨tuple, equality⟩
        cases equality
      · rintro ⟨nonzero, _⟩
        exact False.elim
          (nonzero
            (paperVariableArityGlobalTypeWordRank_zero formula))
  | inr selectedLocal =>
      rcases selectedLocal with ⟨selected, tuple⟩
      let weight :
          Fin (srcFormula formula).clauses.length → ℕ :=
        fun index =>
          2 ^ paperFormulaClauseWidth formula index - 1
      let word : Fin (∑ index, weight index) :=
        finSigmaFinEquiv (n := weight)
          ⟨selected,
            (paperFormulaClauseTupleWordOrder
              formula selected).symm tuple⟩
      have rank :
          ((sourceTypeCardWordOrder formula).symm
            (Sum.inr ⟨selected, tuple⟩)).val = 1 + word.val := by
        exact paperVariableAritySourceLocalTypeWordRank
          formula selected tuple
      have selectedTag :
          (∃ candidate : ((srcFormula
              formula).clauses.get clause).SatisfyingLocalTuple,
            (Sum.inr ⟨selected, tuple⟩ :
              GapCVP.Core.sourceSATTableType
                (srcFormula formula)) =
              Sum.inr ⟨clause, candidate⟩) ↔
            selected = clause := by
        constructor
        · rintro ⟨candidate, hcandidate⟩
          have hsigma :
              (⟨selected, tuple⟩ :
                (index : Fin (srcFormula
                  formula).clauses.length) ×
                    ((srcFormula
                      formula).clauses.get index).SatisfyingLocalTuple) =
                ⟨clause, candidate⟩ := Sum.inr.inj hcandidate
          exact congrArg Sigma.fst hsigma
        · intro hselected
          subst clause
          exact ⟨tuple, rfl⟩
      have decoded :
          ((finSigmaFinEquiv.symm word :
            (index : Fin (srcFormula
              formula).clauses.length) × Fin (weight index)).fst) =
            selected := by
        simp only [List.get_eq_getElem, Equiv.symm_apply_apply, word]
      have interval :=
        paperVariableArityDependentSigmaClause_iff
          weight clause word
      rw [decoded] at interval
      rw [selectedTag, rank]
      change selected = clause ↔
        1 + word.val ≠ 0 ∧
          paperDependentClausePrefix weight clause ≤
            1 + word.val - 1 ∧
          1 + word.val - 1 <
            paperDependentClausePrefix weight clause +
              weight clause
      omega

private theorem paperVariableArityPhysicalSourceCoordinateLocalTag_iff
    (formula : ThreeCNF)
    (column : Fin
      (sourceFormulaDimension (encodeThreeCNF formula).length
        (srcFormula formula)))
    (clause : Fin (srcFormula formula).clauses.length) :
    (∃ tuple : ((srcFormula
        formula).clauses.get clause).SatisfyingLocalTuple,
      (sourceCoordinateWordOrder
        (encodeThreeCNF formula).length formula column).1 =
          Sum.inr ⟨clause, tuple⟩) ↔
      let rank :=
        (column.val /
          physFieldCard formula) /
          physGridCard formula
      let lower := sourceClauseWeightSum
        ((noTautClauses formula).take clause.val)
      let weight := sourceClauseWeight
        (physicalRetainedClause formula clause)
      rank ≠ 0 ∧ lower ≤ rank - 1 ∧ rank - 1 < lower + weight := by
  have hsemantic := paperVariableAritySourceTypeLocalTag_iff
    formula
    (sourceCoordinateWordOrder
      (encodeThreeCNF formula).length formula column).1 clause
  have hrank := sourceCoordinateTypeWordRank
    (encodeThreeCNF formula).length formula column
  rw [physicalFormulaFieldCardinality_eq_card,
    physicalFormulaGridCardinality_eq_card] at hrank
  rw [hrank] at hsemantic
  unfold paperDependentClausePrefix at hsemantic
  rw [paperVariableAritySourceDependentClausePrefix_eq_weightSum
    formula clause] at hsemantic
  rw [paperVariableArityPhysicalRetainedClauseWeight
    formula clause] at hsemantic
  exact hsemantic

private theorem paperVariableArityPhysicalSourceCoordinateGlobalOrLocalTag_iff
    (formula : ThreeCNF)
    (column : Fin
      (sourceFormulaDimension (encodeThreeCNF formula).length
        (srcFormula formula)))
    (clause : Fin (srcFormula formula).clauses.length) :
    ((sourceCoordinateWordOrder
        (encodeThreeCNF formula).length formula column).1 = Sum.inl () ∨
      ∃ tuple : ((srcFormula
          formula).clauses.get clause).SatisfyingLocalTuple,
        (sourceCoordinateWordOrder
          (encodeThreeCNF formula).length formula column).1 =
            Sum.inr ⟨clause, tuple⟩) ↔
      let rank :=
        (column.val /
          physFieldCard formula) /
          physGridCard formula
      let lower := sourceClauseWeightSum
        ((noTautClauses formula).take clause.val)
      let weight := sourceClauseWeight
        (physicalRetainedClause formula clause)
      rank = 0 ∨
        (lower ≤ rank - 1 ∧ rank - 1 < lower + weight) := by
  rw [paperVariableAritySourceCoordinate_isGlobal_iff,
    paperVariableArityPhysicalSourceCoordinateLocalTag_iff]
  dsimp
  omega

end PhysicalRefinementColumnTagSourceCorrectness

namespace RefinementClauseOffsetTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert
open GapCVP.SourceIndexedClauseLookupTM GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingTM GapCVP.ClauseOffsetTM GapCVP.ShiftedTupleTM

/-- GapCVP reduction support. -/
def paperRefinementClauseRankEnvelope
    (formula : ThreeCNF) (rank : ℕ) : List Bool :=
  lengthPrefixedWord (List.replicate rank true) ++
    sourceQaryMaskDynamicGridBaseSource
      paperShiftedRetainedClauseWidth
      (encodeThreeCNF formula)

/-- GapCVP reduction support. -/
noncomputable def paperRefinementPrefixRankWidth :
    SourceQaryMaskDynamicGridWidth where
  output := firstFieldContents
  computer := firstFieldContentsComputable

@[simp] private theorem paperVariableArityRefinementPrefixRankWidth_output
    (input : List Bool) :
    paperRefinementPrefixRankWidth.output input =
      firstFieldContents input := by
  rfl

/-- GapCVP reduction support. -/
def paperRefinementPrefixRankEnvelope
    (formula : ThreeCNF) (outer inner : ℕ) : List Bool :=
  lengthPrefixedWord (List.replicate inner true) ++
    sourceQaryMaskDynamicGridBaseSource
      paperRefinementPrefixRankWidth
      (paperRefinementClauseRankEnvelope formula outer)

/-- GapCVP reduction support. -/
def paperRefinementPrefixIndexedClauseQuery
    (input : List Bool) : List Bool :=
  firstFieldContents input ++
    false :: paperVariableArityShiftedRetainedSourceWord
      (paperSourcePreprocessingSuffixAt 4 input)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityRefinementPrefixIndexedClauseQueryComputable :
    BitTM
      paperRefinementPrefixIndexedClauseQuery := by
  have retained := GapCVP.TMComposition.computableInPolyTime
    (paperPreprocessingSuffixAtComputable 4)
    paperVariableArityShiftedRetainedSourceWordComputable
  have delimited := GapCVP.TMComposition.computableInPolyTime
    retained (prependBitComputable false)
  exact pointwiseAppendComputable
    firstFieldContentsComputable delimited

@[simp] theorem paperVariableArityRefinementPrefixIndexedClauseQuery_valid
    (formula : ThreeCNF) (outer inner : ℕ) :
    paperRefinementPrefixIndexedClauseQuery
      (paperRefinementPrefixRankEnvelope formula outer inner) =
      sourceOriginalIndexedClauseQuery inner
        (noTautClauses formula) := by
  simp [paperRefinementPrefixIndexedClauseQuery,
    paperRefinementPrefixRankEnvelope,
    paperRefinementClauseRankEnvelope,
    sourceQaryMaskDynamicGridBaseSource,
    paperVariableArityRefinementPrefixRankWidth_output,
    paperSourcePreprocessingSuffixAt,
    Function.iterate_succ_apply,
    sourceOriginalIndexedClauseQuery,
    paperSourcePreprocessingFilteredFormulaWord_valid]

private def paperRefinementPrefixIndexedClauseWeightUnary :
    List Bool → List Bool :=
  paperVariableArityClauseWeightUnary ∘
    sourceOriginalIndexedClauseOutput ∘
    paperRefinementPrefixIndexedClauseQuery

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityRefinementPrefixIndexedClauseWeightUnaryComputable :
    BitTM
      paperRefinementPrefixIndexedClauseWeightUnary := by
  have indexed := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityRefinementPrefixIndexedClauseQueryComputable
    sourceOriginalIndexedClauseComputable
  exact GapCVP.TMComposition.computableInPolyTime
    indexed paperClauseWeightUnaryComputable

private theorem paperVariableArityRefinementPrefixIndexedClauseWeightUnary_valid
    (formula : ThreeCNF) (outer inner : ℕ)
    (hinner : inner < (noTautClauses formula).length) :
    paperRefinementPrefixIndexedClauseWeightUnary
      (paperRefinementPrefixRankEnvelope
        formula outer inner) =
      List.replicate
        (sourceClauseWeight
          ((noTautClauses formula).get
            ⟨inner, hinner⟩)) true := by
  unfold paperRefinementPrefixIndexedClauseWeightUnary
  simp only [Function.comp_apply]
  rw [paperVariableArityRefinementPrefixIndexedClauseQuery_valid,
    sourceOriginalIndexedClauseOutput_valid inner
      (noTautClauses formula) hinner]
  simpa only [List.get_eq_getElem, sourceClauseWeight, List.append_nil] using
      paperVariableArityClauseWeightUnary_valid ((noTautClauses formula).get ⟨inner, hinner⟩) []

private def paperRefinementIndexedSourceClauseWeight
    (clauses : List ThreeClause) (rank : ℕ) : ℕ :=
  match clauses[rank]? with
  | some clause => sourceClauseWeight clause
  | none => 0

private theorem paperVariableArityRefinementSourceClauseWeight_flatMap
    (clauses : List ThreeClause) :
    (List.range clauses.length).flatMap
      (fun rank => List.replicate
        (paperRefinementIndexedSourceClauseWeight
          clauses rank) true) =
      List.replicate
        (sourceClauseWeightSum clauses) true := by
  induction clauses with
  | nil =>
      simp only [List.length_nil, List.range_zero, List.flatMap_nil, sourceClauseWeightSum,
          List.map_nil,
          List.sum_nil, List.replicate_zero]
  | cons clause remaining ih =>
      simp only [paperRefinementIndexedSourceClauseWeight, List.length_cons,
          List.range_succ_eq_map,
          List.flatMap_cons, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, getElem?_pos,
              List.getElem_cons_zero,
          List.flatMap_map, Nat.succ_eq_add_one, List.getElem?_cons_succ, sourceClauseWeightSum,
              List.map_cons, List.sum_cons]
      change
        List.replicate (sourceClauseWeight clause) true ++
          (List.range remaining.length).flatMap
            (fun rank => List.replicate
              (paperRefinementIndexedSourceClauseWeight
                remaining rank) true) =
          List.replicate
            (sourceClauseWeight clause +
              sourceClauseWeightSum remaining)
            true
      rw [ih, List.replicate_append_replicate]

/-- GapCVP reduction support. -/
def paperRefinementClauseOffsetUnary :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    paperRefinementPrefixRankWidth
    paperVariableArityRefinementPrefixIndexedClauseWeightUnaryComputable

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityRefinementClauseOffsetUnaryComputable :
    BitTM
      paperRefinementClauseOffsetUnary :=
  maskDynamicGridRecordCatalogueComputable
    paperRefinementPrefixRankWidth
    paperVariableArityRefinementPrefixIndexedClauseWeightUnaryComputable

theorem paperVariableArityRefinementClauseOffsetUnary_valid
    (formula : ThreeCNF) (rank : ℕ)
    (hbound : rank ≤ (noTautClauses formula).length) :
    paperRefinementClauseOffsetUnary
        (paperRefinementClauseRankEnvelope formula rank) =
      List.replicate
        (sourceClauseWeightSum
          ((noTautClauses formula).take rank)) true := by
  have hwidth :
      paperRefinementPrefixRankWidth.output
          (paperRefinementClauseRankEnvelope formula rank) =
        List.replicate rank true := by
    rw [paperVariableArityRefinementPrefixRankWidth_output]
    simp only [paperRefinementClauseRankEnvelope, firstFieldContents_valid]
  have catalogue := maskDynamicGridRecordCatalogueOutput_valid
    paperRefinementPrefixRankWidth
    paperVariableArityRefinementPrefixIndexedClauseWeightUnaryComputable
    (paperRefinementClauseRankEnvelope formula rank)
    rank hwidth
  change maskDynamicGridRecordCatalogueOutput
    paperRefinementPrefixRankWidth
    paperVariableArityRefinementPrefixIndexedClauseWeightUnaryComputable
    (paperRefinementClauseRankEnvelope formula rank) = _
  rw [catalogue]
  rw [← paperVariableArityRefinementSourceClauseWeight_flatMap
    ((noTautClauses formula).take rank)]
  have hlength :
      ((noTautClauses formula).take rank).length = rank := by
    simp only [List.length_take, Nat.min_eq_left hbound]
  rw [hlength]
  apply List.flatMap_congr
  intro inner hmem
  have hlt : inner < rank := List.mem_range.mp hmem
  have hinner : inner <
      (noTautClauses formula).length :=
    Nat.lt_of_lt_of_le hlt hbound
  change paperRefinementPrefixIndexedClauseWeightUnary
    (paperRefinementPrefixRankEnvelope
      formula rank inner) = _
  rw [paperVariableArityRefinementPrefixIndexedClauseWeightUnary_valid
    formula rank inner hinner]
  simp only [paperRefinementIndexedSourceClauseWeight,
    List.getElem?_take, ite_eq_left hlt,
    List.getElem?_eq_getElem hinner, List.get_eq_getElem]

end RefinementClauseOffsetTM

namespace PhysicalRefinementClauseLocalTagTM

open Turing
open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceIndexedClauseLookupTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryDimensionTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryPhysicalRowBasisDivisionTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.ClauseOffsetTM GapCVP.ShiftedTupleTM
open GapCVP.RefinementClauseOffsetTM GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.PhysicalRightHandSideTM GapCVP.PhysicalGlobalRefinementCoefficientTM
open GapCVP.PhysicalRefinementRowProjection

private def physicalRefinementRowLocalRankUnary :
    List Bool → List Bool :=
  unarySubtractionOutput sourceExplicitAffineCellRow
    physicalCellGlobalBoundaryUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementRowLocalRankUnaryComputable :
    BitTM
      physicalRefinementRowLocalRankUnary :=
  unarySubtractionComputable sourceExplicitAffineCellRowComputable
    paperVariableArityPhysicalCellGlobalBoundaryUnaryComputable

@[simp] private theorem paperVariableArityPhysicalRefinementRowLocalRankUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRefinementRowLocalRankUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (row - physicalFormulaGlobalBoundary formula)
        true := by
  unfold physicalRefinementRowLocalRankUnary
  exact unarySubtractionOutput_valid
    sourceExplicitAffineCellRow
    physicalCellGlobalBoundaryUnary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    row (physicalFormulaGlobalBoundary formula)
    (sourceExplicitAffineCellRow_query row column
      (encodeThreeCNF formula))
    (paperVariableArityPhysicalCellGlobalBoundaryUnary_query
      row column formula)

private def physicalRefinementRowFieldQuotientUnary :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryQuotient
    physicalRefinementRowLocalRankUnary
    physicalRightHandSideCellDegreeUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementRowFieldQuotientUnaryComputable :
    BitTM
      physicalRefinementRowFieldQuotientUnary :=
  sourcePhysicalComputedUnaryQuotientComputable
    paperVariableArityPhysicalRefinementRowLocalRankUnaryComputable
    paperVariableArityPhysicalRightHandSideCellDegreeUnaryComputable

@[simp] theorem
    paperVariableArityPhysicalRefinementRowFieldQuotientUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRefinementRowFieldQuotientUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        ((row - physicalFormulaGlobalBoundary formula) /
          physDegree formula) true := by
  unfold physicalRefinementRowFieldQuotientUnary
  exact sourcePhysicalComputedUnaryQuotient_valid
    physicalRefinementRowLocalRankUnary
    physicalRightHandSideCellDegreeUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    (row - physicalFormulaGlobalBoundary formula)
    (physDegree formula)
    (physicalRefinementDegree_pos formula)
    (paperVariableArityPhysicalRefinementRowLocalRankUnary_query
      row column formula)
    (paperVariableArityPhysicalRightHandSideCellDegreeUnary_query
      row column formula)

private def physicalRefinementRowFieldValueRankUnary :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryRemainder
    physicalRefinementRowFieldQuotientUnary
    physicalCoefficientFieldCardinalityUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementRowFieldValueRankUnaryComputable :
    BitTM
      physicalRefinementRowFieldValueRankUnary :=
  sourcePhysicalComputedUnaryRemainderComputable
    paperVariableArityPhysicalRefinementRowFieldQuotientUnaryComputable
    paperVariableArityPhysicalCoefficientFieldCardinalityUnaryComputable

@[simp] theorem
    paperVariableArityPhysicalRefinementRowFieldValueRankUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRefinementRowFieldValueRankUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (((row - physicalFormulaGlobalBoundary formula) /
          physDegree formula) %
          physFieldCard formula)
        true := by
  unfold physicalRefinementRowFieldValueRankUnary
  exact sourcePhysicalComputedUnaryRemainder_valid
    physicalRefinementRowFieldQuotientUnary
    physicalCoefficientFieldCardinalityUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    ((row - physicalFormulaGlobalBoundary formula) /
      physDegree formula)
    (physFieldCard formula)
    (physicalCoefficientFieldCardinality_pos formula)
    (paperVariableArityPhysicalRefinementRowFieldQuotientUnary_query
      row column formula)
    (paperVariableArityPhysicalCoefficientFieldCardinalityUnary_query
      row column formula)

private def physicalRefinementRowGridQuotientUnary :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryQuotient
    physicalRefinementRowFieldQuotientUnary
    physicalCoefficientFieldCardinalityUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementRowGridQuotientUnaryComputable :
    BitTM
      physicalRefinementRowGridQuotientUnary :=
  sourcePhysicalComputedUnaryQuotientComputable
    paperVariableArityPhysicalRefinementRowFieldQuotientUnaryComputable
    paperVariableArityPhysicalCoefficientFieldCardinalityUnaryComputable

@[simp] theorem
    paperVariableArityPhysicalRefinementRowGridQuotientUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRefinementRowGridQuotientUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (((row - physicalFormulaGlobalBoundary formula) /
          physDegree formula) /
          physFieldCard formula)
        true := by
  unfold physicalRefinementRowGridQuotientUnary
  exact sourcePhysicalComputedUnaryQuotient_valid
    physicalRefinementRowFieldQuotientUnary
    physicalCoefficientFieldCardinalityUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    ((row - physicalFormulaGlobalBoundary formula) /
      physDegree formula)
    (physFieldCard formula)
    (physicalCoefficientFieldCardinality_pos formula)
    (paperVariableArityPhysicalRefinementRowFieldQuotientUnary_query
      row column formula)
    (paperVariableArityPhysicalCoefficientFieldCardinalityUnary_query
      row column formula)

private def physicalRefinementRowGridRankUnary :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryRemainder
    physicalRefinementRowGridQuotientUnary
    physicalCoefficientGridCardinalityUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementRowGridRankUnaryComputable :
    BitTM
      physicalRefinementRowGridRankUnary :=
  sourcePhysicalComputedUnaryRemainderComputable
    paperVariableArityPhysicalRefinementRowGridQuotientUnaryComputable
    paperVariableArityPhysicalCoefficientGridCardinalityUnaryComputable

@[simp] private theorem paperVariableArityPhysicalRefinementRowGridRankUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRefinementRowGridRankUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        ((((row - physicalFormulaGlobalBoundary formula) /
          physDegree formula) /
          physFieldCard formula) %
          physGridCard formula)
        true := by
  unfold physicalRefinementRowGridRankUnary
  exact sourcePhysicalComputedUnaryRemainder_valid
    physicalRefinementRowGridQuotientUnary
    physicalCoefficientGridCardinalityUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    (((row - physicalFormulaGlobalBoundary formula) /
      physDegree formula) /
      physFieldCard formula)
    (physGridCard formula)
    (physicalCoefficientGridCardinality_pos formula)
    (paperVariableArityPhysicalRefinementRowGridQuotientUnary_query
      row column formula)
    (paperVariableArityPhysicalCoefficientGridCardinalityUnary_query
      row column formula)

private def physicalRefinementClauseRankUnary :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryQuotient
    physicalRefinementRowGridQuotientUnary
    physicalCoefficientGridCardinalityUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementClauseRankUnaryComputable :
    BitTM
      physicalRefinementClauseRankUnary :=
  sourcePhysicalComputedUnaryQuotientComputable
    paperVariableArityPhysicalRefinementRowGridQuotientUnaryComputable
    paperVariableArityPhysicalCoefficientGridCardinalityUnaryComputable

private abbrev physicalRefinementRowClauseRank
    (row : ℕ) (formula : ThreeCNF) : ℕ :=
  (((row - physicalFormulaGlobalBoundary formula) /
      physDegree formula) /
      physFieldCard formula) /
    physGridCard formula

@[simp] private theorem paperVariableArityPhysicalRefinementClauseRankUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRefinementClauseRankUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (physicalRefinementRowClauseRank row formula)
        true := by
  unfold physicalRefinementClauseRankUnary
  exact sourcePhysicalComputedUnaryQuotient_valid
    physicalRefinementRowGridQuotientUnary
    physicalCoefficientGridCardinalityUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    (((row - physicalFormulaGlobalBoundary formula) /
      physDegree formula) /
      physFieldCard formula)
    (physGridCard formula)
    (physicalCoefficientGridCardinality_pos formula)
    (paperVariableArityPhysicalRefinementRowGridQuotientUnary_query
      row column formula)
    (paperVariableArityPhysicalCoefficientGridCardinalityUnary_query
      row column formula)

private def physicalRefinementClauseRankEnvelopeOutput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (physicalRefinementClauseRankUnary input) ++
    sourceQaryMaskDynamicGridBaseSource
      paperShiftedRetainedClauseWidth
      (sourceExplicitAffineCellOriginalSource input)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementClauseRankEnvelopeOutputComputable :
    BitTM
      physicalRefinementClauseRankEnvelopeOutput := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalRefinementClauseRankUnaryComputable
    structuralPrefixWriterComputable
  have hbase := GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    (maskDynamicGridBaseSourceComputable
      paperShiftedRetainedClauseWidth)
  exact pointwiseAppendComputable hprefix hbase

@[simp] theorem
    paperVariableArityPhysicalRefinementClauseRankEnvelopeOutput_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRefinementClauseRankEnvelopeOutput
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      paperRefinementClauseRankEnvelope formula
        (physicalRefinementRowClauseRank row formula) := by
  unfold physicalRefinementClauseRankEnvelopeOutput
    paperRefinementClauseRankEnvelope
  rw [paperVariableArityPhysicalRefinementClauseRankUnary_query,
    sourceExplicitAffineCellOriginalSource_query]

private def physicalRefinementClauseOffsetUnary :
    List Bool → List Bool :=
  GapCVP.RefinementClauseOffsetTM.paperRefinementClauseOffsetUnary ∘
    physicalRefinementClauseRankEnvelopeOutput

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementClauseOffsetUnaryComputable :
    BitTM
      physicalRefinementClauseOffsetUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalRefinementClauseRankEnvelopeOutputComputable
    GapCVP.RefinementClauseOffsetTM.paperVariableArityRefinementClauseOffsetUnaryComputable

@[simp] private theorem paperVariableArityPhysicalRefinementClauseOffsetUnary_query
    (row column : ℕ) (formula : ThreeCNF)
    (hbound : physicalRefinementRowClauseRank row formula ≤
      (noTautClauses formula).length) :
    physicalRefinementClauseOffsetUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (sourceClauseWeightSum
          ((noTautClauses formula).take
            (physicalRefinementRowClauseRank row formula)))
        true := by
  unfold physicalRefinementClauseOffsetUnary
  rw [Function.comp_apply,
    paperVariableArityPhysicalRefinementClauseRankEnvelopeOutput_query]
  exact paperVariableArityRefinementClauseOffsetUnary_valid
    formula (physicalRefinementRowClauseRank row formula)
    hbound

private def physicalRefinementClauseWidthUnary :
    List Bool → List Bool :=
  paperVariableArityClauseWeightUnary ∘
    sourceOriginalIndexedClauseOutput ∘
    paperShiftedIndexedClauseQuery ∘
    physicalRefinementClauseRankEnvelopeOutput

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementClauseWidthUnaryComputable :
    BitTM
      physicalRefinementClauseWidthUnary := by
  have indexed := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalRefinementClauseRankEnvelopeOutputComputable
    paperVariableArityShiftedIndexedClauseQueryComputable
  have clause := GapCVP.TMComposition.computableInPolyTime
    indexed sourceOriginalIndexedClauseComputable
  exact GapCVP.TMComposition.computableInPolyTime
    clause paperClauseWeightUnaryComputable

@[simp] private theorem paperVariableArityPhysicalRefinementClauseWidthUnary_query
    (row column : ℕ) (formula : ThreeCNF)
    (hbound : physicalRefinementRowClauseRank row formula <
      (noTautClauses formula).length) :
    physicalRefinementClauseWidthUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (sourceClauseWeight
          ((noTautClauses formula).get
            ⟨physicalRefinementRowClauseRank row formula,
              hbound⟩)) true := by
  unfold physicalRefinementClauseWidthUnary
  simp only [Function.comp_apply]
  rw [paperVariableArityPhysicalRefinementClauseRankEnvelopeOutput_query]
  unfold paperRefinementClauseRankEnvelope
  rw [paperVariableArityShiftedIndexedClauseQuery_valid,
    sourceOriginalIndexedClauseOutput_valid
      (physicalRefinementRowClauseRank row formula)
      (noTautClauses formula) hbound]
  simpa only [sourceClauseWeight, List.append_nil] using
    (paperVariableArityClauseWeightUnary_valid
      ((noTautClauses formula).get
        ⟨physicalRefinementRowClauseRank row formula,
          hbound⟩) [])

private def physicalRefinementColumnLocalTagUnary :
    List Bool → List Bool :=
  unarySubtractionOutput
    physicalColumnTypeRankUnary
    (fun _ => [true])

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementColumnLocalTagUnaryComputable :
    BitTM
      physicalRefinementColumnLocalTagUnary :=
  unarySubtractionComputable
    paperVariableArityPhysicalColumnTypeRankUnaryComputable
    (sourceFixedWordComputable [true])

@[simp] theorem
    paperVariableArityPhysicalRefinementColumnLocalTagUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRefinementColumnLocalTagUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (((column /
            physFieldCard formula) /
          physGridCard formula) - 1)
        true := by
  unfold physicalRefinementColumnLocalTagUnary
  exact unarySubtractionOutput_valid
    physicalColumnTypeRankUnary
    (fun _ => [true])
    (affineCellQuery row column (encodeThreeCNF formula))
    ((column / physFieldCard formula) /
      physGridCard formula)
    1
    (paperVariableArityPhysicalColumnTypeRankUnary_query
      row column formula)
    (by rfl)

private def physicalRefinementClauseLocalTagUpperUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    physicalRefinementClauseOffsetUnary
    physicalRefinementClauseWidthUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementClauseLocalTagUpperUnaryComputable :
    BitTM
      physicalRefinementClauseLocalTagUpperUnary :=
  fourFamilyComputedUnarySumComputable
    paperVariableArityPhysicalRefinementClauseOffsetUnaryComputable
    paperVariableArityPhysicalRefinementClauseWidthUnaryComputable

@[simp] theorem
    paperVariableArityPhysicalRefinementClauseLocalTagUpperUnary_query
    (row column : ℕ) (formula : ThreeCNF)
    (hbound : physicalRefinementRowClauseRank row formula <
      (noTautClauses formula).length) :
    physicalRefinementClauseLocalTagUpperUnary
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (sourceClauseWeightSum
          ((noTautClauses formula).take
            (physicalRefinementRowClauseRank row formula)) +
          sourceClauseWeight
            ((noTautClauses formula).get
              ⟨physicalRefinementRowClauseRank row formula,
                hbound⟩)) true := by
  unfold physicalRefinementClauseLocalTagUpperUnary
  exact fourFamilyComputedUnarySumOutput_valid
    physicalRefinementClauseOffsetUnary
    physicalRefinementClauseWidthUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    (sourceClauseWeightSum
      ((noTautClauses formula).take
        (physicalRefinementRowClauseRank row formula)))
    (sourceClauseWeight
      ((noTautClauses formula).get
        ⟨physicalRefinementRowClauseRank row formula,
          hbound⟩))
    (paperVariableArityPhysicalRefinementClauseOffsetUnary_query
      row column formula hbound.le)
    (paperVariableArityPhysicalRefinementClauseWidthUnary_query
      row column formula hbound)

private def physicalRefinementLocalTagBelowPrefixBit :
    List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    physicalRefinementColumnLocalTagUnary
    physicalRefinementClauseOffsetUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementLocalTagBelowPrefixBitComputable :
    BitTM
      physicalRefinementLocalTagBelowPrefixBit :=
  fourFamilyComputedUnaryLessBitComputable
    paperVariableArityPhysicalRefinementColumnLocalTagUnaryComputable
    paperVariableArityPhysicalRefinementClauseOffsetUnaryComputable

private def physicalRefinementLocalTagBelowUpperBit :
    List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    physicalRefinementColumnLocalTagUnary
    physicalRefinementClauseLocalTagUpperUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementLocalTagBelowUpperBitComputable :
    BitTM
      physicalRefinementLocalTagBelowUpperBit :=
  fourFamilyComputedUnaryLessBitComputable
    paperVariableArityPhysicalRefinementColumnLocalTagUnaryComputable
    paperVariableArityPhysicalRefinementClauseLocalTagUpperUnaryComputable

private def physicalRefinementLocalTagMarker :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    (sourceFourFamilyBooleanNotOutput
      physicalRefinementLocalTagBelowPrefixBit)
    physicalRefinementLocalTagBelowUpperBit

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementLocalTagMarkerComputable :
    BitTM
      physicalRefinementLocalTagMarker :=
  fourFamilyBooleanAndComputable
    (fourFamilyBooleanNotOutputComputable
      paperVariableArityPhysicalRefinementLocalTagBelowPrefixBitComputable)
    paperVariableArityPhysicalRefinementLocalTagBelowUpperBitComputable

@[simp] private theorem paperVariableArityPhysicalRefinementLocalTagMarker_query
    (row column : ℕ) (formula : ThreeCNF)
    (hbound : physicalRefinementRowClauseRank row formula <
      (noTautClauses formula).length) :
    physicalRefinementLocalTagMarker
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      [decide
        (sourceClauseWeightSum
            ((noTautClauses formula).take
              (physicalRefinementRowClauseRank row formula)) ≤
          ((column /
              physFieldCard formula) /
            physGridCard formula) - 1 ∧
          ((column /
              physFieldCard formula) /
            physGridCard formula) - 1 <
            sourceClauseWeightSum
              ((noTautClauses formula).take
                (physicalRefinementRowClauseRank
                  row formula)) +
              sourceClauseWeight
                ((noTautClauses formula).get
                  ⟨physicalRefinementRowClauseRank
                    row formula, hbound⟩))] := by
  let input := affineCellQuery row column
    (encodeThreeCNF formula)
  let selectedTag := ((column /
    physFieldCard formula) /
      physGridCard formula) - 1
  let lower := sourceClauseWeightSum
    ((noTautClauses formula).take
      (physicalRefinementRowClauseRank row formula))
  let width := sourceClauseWeight
    ((noTautClauses formula).get
      ⟨physicalRefinementRowClauseRank row formula,
        hbound⟩)
  have hlocal :
      physicalRefinementColumnLocalTagUnary input =
        List.replicate selectedTag true :=
    paperVariableArityPhysicalRefinementColumnLocalTagUnary_query
      row column formula
  have hlower :
      physicalRefinementClauseOffsetUnary input =
        List.replicate lower true :=
    paperVariableArityPhysicalRefinementClauseOffsetUnary_query
      row column formula hbound.le
  have hupper :
      physicalRefinementClauseLocalTagUpperUnary input =
        List.replicate (lower + width) true :=
    paperVariableArityPhysicalRefinementClauseLocalTagUpperUnary_query
      row column formula hbound
  have hlessLower :
      physicalRefinementLocalTagBelowPrefixBit input =
        [decide (selectedTag < lower)] :=
    fourFamilyComputedUnaryLessBitOutput_valid
      physicalRefinementColumnLocalTagUnary
      physicalRefinementClauseOffsetUnary
      input selectedTag lower hlocal hlower
  have hlessUpper :
      physicalRefinementLocalTagBelowUpperBit input =
        [decide (selectedTag < lower + width)] :=
    fourFamilyComputedUnaryLessBitOutput_valid
      physicalRefinementColumnLocalTagUnary
      physicalRefinementClauseLocalTagUpperUnary
      input selectedTag (lower + width) hlocal hupper
  have hnot := fourFamilyBooleanNotOutput_bit
    physicalRefinementLocalTagBelowPrefixBit
    input (decide (selectedTag < lower)) hlessLower
  have hand := fourFamilyBooleanAndOutput_bits
    (sourceFourFamilyBooleanNotOutput
      physicalRefinementLocalTagBelowPrefixBit)
    physicalRefinementLocalTagBelowUpperBit
    input (!(decide (selectedTag < lower)))
    (decide (selectedTag < lower + width)) hnot hlessUpper
  change physicalRefinementLocalTagMarker input =
    [decide (lower ≤ selectedTag ∧ selectedTag < lower + width)]
  change sourceFourFamilyBooleanAndOutput
    (sourceFourFamilyBooleanNotOutput
      physicalRefinementLocalTagBelowPrefixBit)
    physicalRefinementLocalTagBelowUpperBit input = _
  simpa only [← decide_not, Nat.not_lt, ← Bool.decide_and] using hand

end PhysicalRefinementClauseLocalTagTM

namespace PhysicalRefinementCheckSourceCorrectness

open scoped BigOperators

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.FormulaBridge GapCVP.SourceOrder
open GapCVP.ClauseOffsetTM GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.MatrixEntrySemantics GapCVP.PhysicalRightHandSideTM
open GapCVP.PhysicalGlobalRefinementCoefficientTM GapCVP.PhysicalRefinementSelectedRowProjection
open GapCVP.PhysicalRefinementColumnTagProjection
open GapCVP.PhysicalRefinementColumnTagSourceCorrectness
open GapCVP.PhysicalRefinementClauseLocalTagTM

attribute [local instance] Classical.propDecidable

private abbrev physicalRefinementColumnTypeRank
    (column : ℕ) (formula : ThreeCNF) : ℕ :=
  (column / physFieldCard formula) /
    physGridCard formula

private abbrev paperVariableArityPhysicalRefinementLocalSourcePrefix
    (row : ℕ) (formula : ThreeCNF) : ℕ :=
  sourceClauseWeightSum
    ((noTautClauses formula).take
      (physicalRefinementRowClauseRank row formula))

private abbrev paperVariableArityPhysicalRefinementLocalSourceWidth
    (row : ℕ) (formula : ThreeCNF)
    (hbound : physicalRefinementRowClauseRank row formula <
      (noTautClauses formula).length) : ℕ :=
  sourceClauseWeight
    ((noTautClauses formula).get
      ⟨physicalRefinementRowClauseRank row formula,
        hbound⟩)

attribute [-instance] Classical.propDecidable in
private def physicalRefinementSourceLocalTagInRange
    (row column : ℕ) (formula : ThreeCNF)
    (hbound : physicalRefinementRowClauseRank row formula <
      (noTautClauses formula).length) : Bool :=
  decide (
  paperVariableArityPhysicalRefinementLocalSourcePrefix row formula ≤
      physicalRefinementColumnTypeRank column formula - 1 ∧
    physicalRefinementColumnTypeRank column formula - 1 <
      paperVariableArityPhysicalRefinementLocalSourcePrefix row formula +
        paperVariableArityPhysicalRefinementLocalSourceWidth
          row formula hbound
  )
attribute [-instance] Classical.propDecidable in
private def physicalRefinementSourceFieldMatch
    (row column : ℕ) (formula : ThreeCNF)
    (hbound : physicalRefinementRowClauseRank row formula <
      (noTautClauses formula).length) : Bool :=
  decide (
  ((column / physFieldCard formula) %
      physGridCard formula =
    (((row - physicalFormulaGlobalBoundary formula) /
      physDegree formula) /
      physFieldCard formula) %
      physGridCard formula) ∧
  (column % physFieldCard formula =
    ((row - physicalFormulaGlobalBoundary formula) /
      physDegree formula) %
      physFieldCard formula) ∧
  (physicalRefinementColumnTypeRank column formula = 0 ∨
    physicalRefinementSourceLocalTagInRange
      row column formula hbound)
  )
private def physicalRefinementGridMatchBit :
    List Bool → List Bool :=
  physicalCoefficientUnaryEquality
    physicalColumnGridRankUnary
    physicalRefinementRowGridRankUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementGridMatchBitComputable :
    BitTM
      physicalRefinementGridMatchBit :=
  paperVariableArityPhysicalCoefficientUnaryEqualityComputable
    physicalColumnGridRankUnaryComputable
    paperVariableArityPhysicalRefinementRowGridRankUnaryComputable

@[simp] private theorem paperVariableArityPhysicalRefinementGridMatchBit_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRefinementGridMatchBit
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (((column /
          physFieldCard formula) %
          physGridCard formula) =
          (((row - physicalFormulaGlobalBoundary formula) /
            physDegree formula) /
            physFieldCard formula) %
              physGridCard formula)] := by
  unfold physicalRefinementGridMatchBit
  exact physicalCoefficientUnaryEquality_valid
    physicalColumnGridRankUnary
    physicalRefinementRowGridRankUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    ((column / physFieldCard formula) %
      physGridCard formula)
    ((((row - physicalFormulaGlobalBoundary formula) /
      physDegree formula) /
      physFieldCard formula) %
      physGridCard formula)
    (paperVariableArityPhysicalColumnGridRankUnary_query row column formula)
    (paperVariableArityPhysicalRefinementRowGridRankUnary_query
      row column formula)

private def physicalRefinementFieldValueMatchBit :
    List Bool → List Bool :=
  physicalCoefficientUnaryEquality
    physicalColumnFieldValueRankUnary
    physicalRefinementRowFieldValueRankUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementFieldValueMatchBitComputable :
    BitTM
      physicalRefinementFieldValueMatchBit :=
  paperVariableArityPhysicalCoefficientUnaryEqualityComputable
    paperVariableArityPhysicalColumnFieldValueRankUnaryComputable
    paperVariableArityPhysicalRefinementRowFieldValueRankUnaryComputable

@[simp] private theorem paperVariableArityPhysicalRefinementFieldValueMatchBit_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRefinementFieldValueMatchBit
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (column % physFieldCard formula =
          ((row - physicalFormulaGlobalBoundary formula) /
            physDegree formula) %
              physFieldCard formula)] := by
  unfold physicalRefinementFieldValueMatchBit
  exact physicalCoefficientUnaryEquality_valid
    physicalColumnFieldValueRankUnary
    physicalRefinementRowFieldValueRankUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    (column % physFieldCard formula)
    (((row - physicalFormulaGlobalBoundary formula) /
      physDegree formula) %
      physFieldCard formula)
    (paperVariableArityPhysicalColumnFieldValueRankUnary_query
      row column formula)
    (paperVariableArityPhysicalRefinementRowFieldValueRankUnary_query
      row column formula)

private def physicalRefinementAllowedTypeBit :
    List Bool → List Bool :=
  sourceFourFamilyBooleanOrOutput
    physicalColumnGlobalTypeBit
    physicalRefinementLocalTagMarker

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementAllowedTypeBitComputable :
    BitTM
      physicalRefinementAllowedTypeBit :=
  sourceFourFamilyBooleanOrComputable
    paperVariableArityPhysicalColumnGlobalTypeBitComputable
    paperVariableArityPhysicalRefinementLocalTagMarkerComputable

@[simp] private theorem paperVariableArityPhysicalRefinementAllowedTypeBit_query
    (row column : ℕ) (formula : ThreeCNF)
    (hbound : physicalRefinementRowClauseRank row formula <
      (noTautClauses formula).length) :
    physicalRefinementAllowedTypeBit
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (physicalRefinementColumnTypeRank
          column formula = 0) ||
        decide
          (physicalRefinementSourceLocalTagInRange
            row column formula hbound)] := by
  unfold physicalRefinementAllowedTypeBit
  exact fourFamilyBooleanOrOutput_bits
    physicalColumnGlobalTypeBit
    physicalRefinementLocalTagMarker
    (affineCellQuery row column
      (encodeThreeCNF formula))
    (decide
      (physicalRefinementColumnTypeRank
        column formula = 0))
    (decide
      (physicalRefinementSourceLocalTagInRange
        row column formula hbound))
    (paperVariableArityPhysicalColumnGlobalTypeBit_query
      row column formula)
    (by simpa only [physicalRefinementSourceLocalTagInRange,
      decide_eq_true_eq] using
        (paperVariableArityPhysicalRefinementLocalTagMarker_query
          row column formula hbound))

private def physicalRefinementFamilyCoefficientWord :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    physicalRefinementGridMatchBit
    (sourceFourFamilyBooleanAndOutput
      physicalRefinementFieldValueMatchBit
      physicalRefinementAllowedTypeBit)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementFamilyCoefficientWordComputable :
    BitTM
      physicalRefinementFamilyCoefficientWord :=
  fourFamilyBooleanAndComputable
    paperVariableArityPhysicalRefinementGridMatchBitComputable
    (fourFamilyBooleanAndComputable
      paperVariableArityPhysicalRefinementFieldValueMatchBitComputable
      paperVariableArityPhysicalRefinementAllowedTypeBitComputable)

@[simp] theorem
    paperVariableArityPhysicalRefinementFamilyCoefficientWord_query
    (row column : ℕ) (formula : ThreeCNF)
    (hbound : physicalRefinementRowClauseRank row formula <
      (noTautClauses formula).length) :
    physicalRefinementFamilyCoefficientWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (((column /
          physFieldCard formula) %
          physGridCard formula) =
          (((row - physicalFormulaGlobalBoundary formula) /
            physDegree formula) /
            physFieldCard formula) %
              physGridCard formula) &&
       (decide
        (column % physFieldCard formula =
          ((row - physicalFormulaGlobalBoundary formula) /
            physDegree formula) %
              physFieldCard formula) &&
        (decide
          (physicalRefinementColumnTypeRank
            column formula = 0) ||
          decide
            (physicalRefinementSourceLocalTagInRange
              row column formula hbound)))] := by
  let input := affineCellQuery row column
    (encodeThreeCNF formula)
  let grid := decide
    (((column / physFieldCard formula) %
      physGridCard formula) =
      (((row - physicalFormulaGlobalBoundary formula) /
        physDegree formula) /
        physFieldCard formula) %
          physGridCard formula)
  let value := decide
    (column % physFieldCard formula =
      ((row - physicalFormulaGlobalBoundary formula) /
        physDegree formula) %
          physFieldCard formula)
  let allowed := decide
      (physicalRefinementColumnTypeRank
        column formula = 0) ||
    decide
      (physicalRefinementSourceLocalTagInRange
        row column formula hbound)
  have inner := fourFamilyBooleanAndOutput_bits
    physicalRefinementFieldValueMatchBit
    physicalRefinementAllowedTypeBit
    input value allowed
    (paperVariableArityPhysicalRefinementFieldValueMatchBit_query
      row column formula)
    (paperVariableArityPhysicalRefinementAllowedTypeBit_query
      row column formula hbound)
  exact fourFamilyBooleanAndOutput_bits
    physicalRefinementGridMatchBit
    (sourceFourFamilyBooleanAndOutput
      physicalRefinementFieldValueMatchBit
      physicalRefinementAllowedTypeBit)
    input grid (value && allowed)
    (paperVariableArityPhysicalRefinementGridMatchBit_query
      row column formula)
    inner

/-- GapCVP reduction support. -/
def physicalRefinementCheckBit :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    physicalRefinementRowMarker
    (sourceFourFamilyBooleanAndOutput
      physicalRightHandSideBasisZeroBit
      physicalRefinementFamilyCoefficientWord)

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalRefinementCheckBitComputable :
    BitTM
      physicalRefinementCheckBit :=
  fourFamilyBooleanAndComputable
    paperVariableArityPhysicalRefinementRowMarkerComputable
    (fourFamilyBooleanAndComputable
      paperVariableArityPhysicalRightHandSideBasisZeroBitComputable
      paperVariableArityPhysicalRefinementFamilyCoefficientWordComputable)

private def paperVariableArityPhysicalRefinementCheckDecision
    (row column : ℕ) (formula : ThreeCNF)
    (hbound : physicalRefinementRowClauseRank row formula <
      (noTautClauses formula).length) : Bool :=
  decide
    (physicalFormulaGlobalBoundary formula ≤ row ∧
      row < physicalFormulaRefinementBoundary formula) &&
    (decide (row % physDegree formula = 0) &&
      (decide
        (((column /
          physFieldCard formula) %
          physGridCard formula) =
          (((row - physicalFormulaGlobalBoundary formula) /
            physDegree formula) /
            physFieldCard formula) %
              physGridCard formula) &&
        (decide
          (column % physFieldCard formula =
            ((row - physicalFormulaGlobalBoundary formula) /
              physDegree formula) %
                physFieldCard formula) &&
          (decide
            (physicalRefinementColumnTypeRank
              column formula = 0) ||
            decide
              (physicalRefinementSourceLocalTagInRange
                row column formula hbound)))))

@[simp] private theorem paperVariableArityPhysicalRefinementCheckBit_query
    (row column : ℕ) (formula : ThreeCNF)
    (hbound : physicalRefinementRowClauseRank row formula <
      (noTautClauses formula).length) :
    physicalRefinementCheckBit
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      [paperVariableArityPhysicalRefinementCheckDecision
        row column formula hbound] := by
  let input := affineCellQuery row column
    (encodeThreeCNF formula)
  let marker := decide
    (physicalFormulaGlobalBoundary formula ≤ row ∧
      row < physicalFormulaRefinementBoundary formula)
  let basis := decide
    (row % physDegree formula = 0)
  let grid := decide
    (((column /
      physFieldCard formula) %
      physGridCard formula) =
      (((row - physicalFormulaGlobalBoundary formula) /
        physDegree formula) /
        physFieldCard formula) %
          physGridCard formula)
  let value := decide
    (column % physFieldCard formula =
      ((row - physicalFormulaGlobalBoundary formula) /
        physDegree formula) %
          physFieldCard formula)
  let allowed := decide
      (physicalRefinementColumnTypeRank
        column formula = 0) ||
    decide
      (physicalRefinementSourceLocalTagInRange
        row column formula hbound)
  have coefficient :=
    paperVariableArityPhysicalRefinementFamilyCoefficientWord_query
      row column formula hbound
  have inner := fourFamilyBooleanAndOutput_bits
    physicalRightHandSideBasisZeroBit
    physicalRefinementFamilyCoefficientWord
    input basis (grid && (value && allowed))
    (paperVariableArityPhysicalRightHandSideBasisZeroBit_query
      row column formula)
    coefficient
  have outer := fourFamilyBooleanAndOutput_bits
    physicalRefinementRowMarker
    (sourceFourFamilyBooleanAndOutput
      physicalRightHandSideBasisZeroBit
      physicalRefinementFamilyCoefficientWord)
    input marker (basis && (grid && (value && allowed)))
    (paperVariableArityPhysicalRefinementRowMarker_query
      row column formula)
    inner
  exact outer

private theorem paperVariableArityPhysicalRefinementRowClauseRank_lt
    (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
    (hinterval :
      physicalFormulaGlobalBoundary formula ≤ row.val ∧
        row.val < physicalFormulaRefinementBoundary formula) :
    physicalRefinementRowClauseRank row.val formula <
      (noTautClauses formula).length := by
  calc
    physicalRefinementRowClauseRank row.val formula =
        (physicalDecodedRefinementClause
          formula row.val hinterval).val := by
      exact (paperVariableArityPhysicalDecodedRefinementClause_val
        formula row.val hinterval).symm
    _ < (srcFormula formula).clauses.length :=
      (physicalDecodedRefinementClause
        formula row.val hinterval).isLt
    _ = (noTautClauses formula).length :=
      paperVariableAritySourceFormula_clauses_length formula

private theorem paperVariableArityPhysicalRefinementAllowedCoordinate_iff
    (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (hinterval :
      physicalFormulaGlobalBoundary formula ≤ row.val ∧
        row.val < physicalFormulaRefinementBoundary formula)
    (hbound : physicalRefinementRowClauseRank
      row.val formula <
        (noTautClauses formula).length) :
    ((sourceCoordinateWordOrder
        (encodeThreeCNF formula).length formula column).1 = .inl () ∨
      ∃ tuple :
        ((srcFormula formula).clauses.get
          (physicalDecodedRefinementClause
            formula row.val hinterval)).SatisfyingLocalTuple,
        (sourceCoordinateWordOrder
          (encodeThreeCNF formula).length formula column).1 =
          .inr ⟨physicalDecodedRefinementClause
            formula row.val hinterval, tuple⟩) ↔
      physicalRefinementColumnTypeRank
          column.val formula = 0 ∨
        physicalRefinementSourceLocalTagInRange
          row.val column.val formula hbound := by
  let selected := physicalDecodedRefinementClause
    formula row.val hinterval
  have hselected :
      selected.val =
        physicalRefinementRowClauseRank row.val formula :=
    paperVariableArityPhysicalDecodedRefinementClause_val
      formula row.val hinterval
  have hretained :
      physicalRetainedClause formula selected =
        (noTautClauses formula).get
          ⟨physicalRefinementRowClauseRank
            row.val formula, hbound⟩ := by
    unfold physicalRetainedClause
    apply congrArg ((noTautClauses formula).get)
    apply Fin.ext
    exact hselected
  have hsource :=
    paperVariableArityPhysicalSourceCoordinateGlobalOrLocalTag_iff
      formula column selected
  dsimp only at hsource
  rw [hselected, hretained] at hsource
  simpa only [physicalRefinementSourceLocalTagInRange,
    decide_eq_true_eq] using hsource

end PhysicalRefinementCheckSourceCorrectness

namespace PhysicalRefinementGuardAbsorption

open GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryExplicitAffineSystem GapCVP.BinarySourceCoordinateOrder
open GapCVP.BinarySourceRowOrder GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.PhysicalColumnOrder
open GapCVP.PhysicalColumnOrderProjection GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalFamilyMarkerTM GapCVP.MatrixEntrySemantics GapCVP.PhysicalRightHandSideTM
open GapCVP.PhysicalRefinementRowProjection GapCVP.PhysicalRefinementSelectedRowProjection
open GapCVP.PhysicalRefinementSelectedProductProjection
open GapCVP.PhysicalRefinementFieldCoordinateCorrectness
open GapCVP.PhysicalRefinementClauseLocalTagTM GapCVP.PhysicalRefinementCheckSourceCorrectness

attribute [local instance] Classical.propDecidable

private theorem paperVariableArityPhysicalBooleanAnd_false_left
    (first second : List Bool → List Bool)
    (input : List Bool)
    (hfirst : first input = [false]) :
    sourceFourFamilyBooleanAndOutput first second input = [false] := by
  simp only [sourceFourFamilyBooleanAndOutput, sourceFourFamilyBooleanAndPairWord,
      OutputPolynomialCompositionClosure.markerConditionalOutput, hfirst, List.cons_append,
          List.nil_append]

private theorem paperVariableArityPhysicalRefinementFieldCoefficient_eq_sourceRanks
    (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inRefinement :
      physicalFormulaGlobalBoundary formula ≤ row.val ∧
        row.val < physicalFormulaRefinementBoundary formula)
    (clauseBound :
      physicalRefinementRowClauseRank row.val formula <
        (noTautClauses formula).length)
    (fieldRow : Fin
      (Fintype.card
        (ExplicitGridPoint (encodeThreeCNF formula).length
          (srcFormula formula) ×
          PaperVariableArityPhysicalWordField
            (encodeThreeCNF formula).length formula))) :
    physicalWordFamilyFieldCoefficient
        (encodeThreeCNF formula).length formula
        (.inr (.inl
          (physicalDecodedRefinementClause
            formula row.val inRefinement)))
        fieldRow column =
      if
        (column.val /
          physFieldCard formula) %
            physGridCard formula =
          ((sourceFormulaGridOrder
            (encodeThreeCNF formula).length
            (srcFormula formula)).symm
            (sourceFormulaExplicitRefinementOrder
              (encodeThreeCNF formula).length
              (srcFormula formula) fieldRow).1).val ∧
        column.val %
            physFieldCard formula =
          ((sourceFormulaFieldCardOrder
            (encodeThreeCNF formula).length
            (srcFormula formula)).symm
            (sourceFormulaExplicitRefinementOrder
              (encodeThreeCNF formula).length
              (srcFormula formula) fieldRow).2).val ∧
        (physicalRefinementColumnTypeRank
          column.val formula = 0 ∨
          physicalRefinementSourceLocalTagInRange
            row.val column.val formula clauseBound)
      then 1 else 0 := by
  let encodingLength := (encodeThreeCNF formula).length
  let decoded := sourceCoordinateWordOrder
    encodingLength formula column
  let position := sourceFormulaExplicitRefinementOrder
    encodingLength (srcFormula formula) fieldRow
  have columnGrid :
      ((sourceFormulaGridOrder
        encodingLength (srcFormula formula)).symm
          decoded.2.1).val =
        (column.val /
          physFieldCard formula) %
            physGridCard formula := by
    simpa only [encodingLength, decoded,
      physicalFormulaFieldCardinality_eq_card,
      physicalFormulaGridCardinality_eq_card] using
      sourceCoordinateGridWordRank
        encodingLength formula column
  have columnField :
      ((sourceFormulaFieldCardOrder
        encodingLength (srcFormula formula)).symm
          decoded.2.2).val =
        column.val %
          physFieldCard formula := by
    simpa only [encodingLength, decoded,
      physicalFormulaFieldCardinality_eq_card] using
      paperVariableAritySourceCoordinateFieldWordRank
        encodingLength formula column
  have sameGrid :
      decoded.2.1 = position.1 ↔
        (column.val /
          physFieldCard formula) %
            physGridCard formula =
          ((sourceFormulaGridOrder
            encodingLength (srcFormula formula)).symm
              position.1).val := by
    constructor
    · intro equality
      rw [← columnGrid, equality]
    · intro equality
      apply (sourceFormulaGridOrder
        encodingLength (srcFormula formula)).symm.injective
      apply Fin.ext
      exact columnGrid.trans equality
  have sameField :
      decoded.2.2 = position.2 ↔
        column.val %
            physFieldCard formula =
          ((sourceFormulaFieldCardOrder
            encodingLength (srcFormula formula)).symm
              position.2).val := by
    constructor
    · intro equality
      rw [← columnField, equality]
    · intro equality
      apply (sourceFormulaFieldCardOrder
        encodingLength (srcFormula formula)).symm.injective
      apply Fin.ext
      exact columnField.trans equality
  have allowed := paperVariableArityPhysicalRefinementAllowedCoordinate_iff
    formula row column inRefinement clauseBound
  rw [paperVariableArityPhysicalWordRefinementFieldCoefficient_eq_coordinate]
  change
    (if decoded.2.1 = position.1 ∧ decoded.2.2 = position.2 ∧
      (decoded.1 = .inl () ∨
        ∃ tuple :
          ((srcFormula formula).clauses.get
            (physicalDecodedRefinementClause
              formula row.val inRefinement)).SatisfyingLocalTuple,
          decoded.1 = .inr
            ⟨physicalDecodedRefinementClause
              formula row.val inRefinement, tuple⟩)
      then 1 else 0) = _
  by_cases sourceCondition :
      decoded.2.1 = position.1 ∧ decoded.2.2 = position.2 ∧
        (decoded.1 = .inl () ∨
          ∃ tuple :
            ((srcFormula formula).clauses.get
              (physicalDecodedRefinementClause
                formula row.val inRefinement)).SatisfyingLocalTuple,
            decoded.1 = .inr
              ⟨physicalDecodedRefinementClause
                formula row.val inRefinement, tuple⟩)
  · have physicalCondition :
        (column.val /
          physFieldCard formula) %
            physGridCard formula =
            ((sourceFormulaGridOrder encodingLength
              (srcFormula formula)).symm
                position.1).val ∧
          column.val %
              physFieldCard formula =
            ((sourceFormulaFieldCardOrder encodingLength
              (srcFormula formula)).symm
                position.2).val ∧
          (physicalRefinementColumnTypeRank
            column.val formula = 0 ∨
            physicalRefinementSourceLocalTagInRange
              row.val column.val formula clauseBound) :=
      ⟨sameGrid.mp sourceCondition.1,
        sameField.mp sourceCondition.2.1,
        allowed.mp sourceCondition.2.2⟩
    rw [ite_eq_left sourceCondition, ite_eq_left physicalCondition]
  · have physicalCondition :
        ¬ ((column.val /
          physFieldCard formula) %
            physGridCard formula =
            ((sourceFormulaGridOrder encodingLength
              (srcFormula formula)).symm
                position.1).val ∧
          column.val %
              physFieldCard formula =
            ((sourceFormulaFieldCardOrder encodingLength
              (srcFormula formula)).symm
                position.2).val ∧
          (physicalRefinementColumnTypeRank
            column.val formula = 0 ∨
            physicalRefinementSourceLocalTagInRange
              row.val column.val formula clauseBound)) := by
      rintro ⟨gridEquality, fieldEquality, tagEquality⟩
      exact sourceCondition
        ⟨sameGrid.mpr gridEquality, sameField.mpr fieldEquality,
          allowed.mpr tagEquality⟩
    rw [ite_eq_right sourceCondition, ite_eq_right physicalCondition]

private theorem paperVariableArityPhysicalRefinementWordBinaryCheck_eq_sourceRanks
    (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inRefinement :
      physicalFormulaGlobalBoundary formula ≤ row.val ∧
        row.val < physicalFormulaRefinementBoundary formula)
    (clauseBound :
      physicalRefinementRowClauseRank row.val formula <
        (noTautClauses formula).length) :
    (physicalWordBinarySystem
      (encodeThreeCNF formula).length formula).check row column =
      if physicalRefinementSourceFieldMatch
        row.val column.val formula clauseBound
      then bitValue
        (decide
          (row.val % physDegree formula = 0))
      else 0 := by
  let selected := physicalDecodedRefinementClause
    formula row.val inRefinement
  have family := paperVariableArityPhysicalRowOrder_refinementFamily
    formula row inRefinement
  have fieldRank := paperVariableArityPhysicalRefinementDecodedFieldRowRank
    formula row inRefinement
  have basisRank := paperVariableArityPhysicalDecodedRefinementBasisRank
    formula row
  rw [physicalWordBinaryCheckCoefficient]
  generalize decodedEquality :
    physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row = decoded
      at family fieldRank basisRank ⊢
  rcases decoded with ⟨rowFamily, fieldRow, basis⟩
  cases rowFamily with
  | inl value =>
      cases family
  | inr otherFamily =>
      cases otherFamily with
      | inr other =>
          cases family
      | inl actualClause =>
          have sameClause : actualClause = selected := by
            exact Sum.inl.inj (Sum.inr.inj family)
          subst actualClause
          change
            fieldRow.val =
              ((row.val -
                physicalFormulaGlobalBoundary formula) /
                physDegree formula) %
                  (physGridCard formula *
                    physFieldCard formula)
            at fieldRank
          change
            basis.val =
              row.val % physDegree formula
            at basisRank
          have gridRank :
              ((sourceFormulaGridOrder
                (encodeThreeCNF formula).length
                (srcFormula formula)).symm
                (sourceFormulaExplicitRefinementOrder
                  (encodeThreeCNF formula).length
                  (srcFormula formula) fieldRow).1).val =
                (((row.val -
                  physicalFormulaGlobalBoundary formula) /
                  physDegree formula) /
                  physFieldCard formula) %
                  physGridCard formula := by
            calc
              ((sourceFormulaGridOrder
                (encodeThreeCNF formula).length
                (srcFormula formula)).symm
                (sourceFormulaExplicitRefinementOrder
                  (encodeThreeCNF formula).length
                  (srcFormula formula) fieldRow).1).val =
                fieldRow.val /
                  Fintype.card
                    (PaperVariableArityPhysicalWordField
                      (encodeThreeCNF formula).length formula) :=
                paperVariableArityPhysicalRefinementProductGridWordRank
                  (encodeThreeCNF formula).length formula fieldRow
              _ =
                (((row.val -
                  physicalFormulaGlobalBoundary formula) /
                  physDegree formula) %
                  (physGridCard formula *
                    physFieldCard formula)) /
                    physFieldCard formula := by
                rw [fieldRank, paperVariableArityPhysicalRefinementFieldCard_eq]
              _ = _ :=
                Nat.mod_mul_left_div_self
                  ((row.val -
                    physicalFormulaGlobalBoundary formula) /
                    physDegree formula)
                  (physFieldCard formula)
                  (physGridCard formula)
          have valueRank :
              ((sourceFormulaFieldCardOrder
                (encodeThreeCNF formula).length
                (srcFormula formula)).symm
                (sourceFormulaExplicitRefinementOrder
                  (encodeThreeCNF formula).length
                  (srcFormula formula) fieldRow).2).val =
                ((row.val -
                  physicalFormulaGlobalBoundary formula) /
                  physDegree formula) %
                  physFieldCard formula := by
            calc
              ((sourceFormulaFieldCardOrder
                (encodeThreeCNF formula).length
                (srcFormula formula)).symm
                (sourceFormulaExplicitRefinementOrder
                  (encodeThreeCNF formula).length
                  (srcFormula formula) fieldRow).2).val =
                fieldRow.val %
                  Fintype.card
                    (PaperVariableArityPhysicalWordField
                      (encodeThreeCNF formula).length formula) :=
                paperVariableArityPhysicalRefinementProductFieldWordRank
                  (encodeThreeCNF formula).length formula fieldRow
              _ =
                (((row.val -
                  physicalFormulaGlobalBoundary formula) /
                  physDegree formula) %
                  (physGridCard formula *
                    physFieldCard formula)) %
                    physFieldCard formula := by
                rw [fieldRank, paperVariableArityPhysicalRefinementFieldCard_eq]
              _ = _ :=
                Nat.mod_mul_left_mod
                  ((row.val -
                    physicalFormulaGlobalBoundary formula) /
                    physDegree formula)
                  (physGridCard formula)
                  (physFieldCard formula)
          have coefficient :=
            paperVariableArityPhysicalRefinementFieldCoefficient_eq_sourceRanks
              formula row column inRefinement clauseBound fieldRow
          dsimp [selected] at family ⊢
          rw [gridRank, valueRank] at coefficient
          rw [coefficient]
          simp only [physicalRefinementSourceFieldMatch,
            decide_eq_true_eq]
          split_ifs
          · rw [← Module.Basis.equivFun_apply]
            rw [paperVariableArityPhysicalFieldBasis_one_coordinate]
            rw [basisRank]
          · rw [map_zero]
            rfl

private theorem paperVariableArityPhysicalRefinementCheckBit_valid_of_refinement
    (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inRefinement :
      physicalFormulaGlobalBoundary formula ≤ row.val ∧
        row.val < physicalFormulaRefinementBoundary formula) :
    physicalRefinementCheckBit
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).check row column = 1)] := by
  let clauseBound := paperVariableArityPhysicalRefinementRowClauseRank_lt
    formula row inRefinement
  let basisRank := row.val %
    physDegree formula
  let fieldMatch : Prop :=
    physicalRefinementSourceFieldMatch
      row.val column.val formula clauseBound
  have checkEntry :=
    paperVariableArityPhysicalRefinementWordBinaryCheck_eq_sourceRanks
      formula row column inRefinement clauseBound
  have entry :
      (physicalWordBinarySystem
        (encodeThreeCNF formula).length formula).check row column = 1 ↔
        basisRank = 0 ∧ fieldMatch := by
    rw [checkEntry]
    change
      (if fieldMatch then bitValue (decide (basisRank = 0)) else 0) = 1 ↔
        basisRank = 0 ∧ fieldMatch
    by_cases fieldAccepted : fieldMatch
    · rw [ite_eq_left fieldAccepted]
      simp only [bitValue, decide_eq_true_eq, ite_eq_left_iff, zero_ne_one, imp_false,
          Decidable.not_not,
          fieldAccepted, and_true]
    · rw [ite_eq_right fieldAccepted]
      simp only [zero_ne_one, fieldAccepted, and_false]
  have source :
      paperVariableArityPhysicalRefinementCheckDecision
        row.val column.val formula clauseBound = true ↔
        basisRank = 0 ∧ fieldMatch := by
    simp only [paperVariableArityPhysicalRefinementCheckDecision, inRefinement, and_self,
        decide_true,
        Nat.div_eq_zero_iff, Bool.decide_or, Bool.decide_eq_true, Bool.true_and, Bool.and_eq_true,
            decide_eq_true_eq,
        Bool.or_eq_true, physicalRefinementSourceFieldMatch, Bool.decide_and, basisRank,
            fieldMatch]
  rw [paperVariableArityPhysicalRefinementCheckBit_query
    row.val column.val formula clauseBound]
  apply congrArg (fun bit : Bool => [bit])
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    exact decide_eq_true (entry.mpr (source.mp accepted))
  · intro accepted
    exact source.mpr (entry.mp (of_decide_eq_true accepted))

theorem paperVariableArityPhysicalRefinementCheckBit_valid
    (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula)) :
    physicalRefinementCheckBit
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        (physicalFormulaGlobalBoundary formula ≤ row.val ∧
          row.val <
            physicalFormulaRefinementBoundary formula) &&
        decide
          ((physicalWordBinarySystem
            (encodeThreeCNF formula).length formula).check row column = 1)] := by
  by_cases inRefinement :
      physicalFormulaGlobalBoundary formula ≤ row.val ∧
        row.val <
          physicalFormulaRefinementBoundary formula
  · rw [paperVariableArityPhysicalRefinementCheckBit_valid_of_refinement
      formula row column inRefinement]
    simp only [inRefinement, and_self,
        decide_true,
        Bool.true_and]
  · have marker :
        physicalRefinementRowMarker
          (affineCellQuery row.val column.val
            (encodeThreeCNF formula)) = [false] := by
      rw [paperVariableArityPhysicalRefinementRowMarker_query]
      simp only [inRefinement, decide_false]
    change
      sourceFourFamilyBooleanAndOutput
        physicalRefinementRowMarker
        (sourceFourFamilyBooleanAndOutput
          physicalRightHandSideBasisZeroBit
          physicalRefinementFamilyCoefficientWord)
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) = _
    rw [paperVariableArityPhysicalBooleanAnd_false_left
      physicalRefinementRowMarker
      (sourceFourFamilyBooleanAndOutput
        physicalRightHandSideBasisZeroBit
        physicalRefinementFamilyCoefficientWord)
      (affineCellQuery row.val column.val
        (encodeThreeCNF formula)) marker]
    simp only [inRefinement, decide_false,
        Bool.false_and]

end PhysicalRefinementGuardAbsorption

namespace Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine

section

open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceAnchoredGridRecordFoldTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.BinaryDimensionTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryFieldBasis
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryFieldInverseTM
open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceFieldMultiplicationTM

private abbrev physicalFieldFormulaDegree
    (formula : ThreeCNF) : ℕ :=
  GapCVP.Core.sourceFieldExponent
    (GapCVP.Core.sourceSizeParameter
      (encodeThreeCNF formula).length
      (srcFormula formula))

private def physicalFieldInverseCounter : List Bool → List Bool :=
  unarySubtractionOutput
    physicalFamilyFieldCardinalityUnary
    (fun _ => [true, true, true]) ∘
      binarySourceFieldInverseSource

private noncomputable def paperVariableArityPhysicalFieldInverseCounterComputable :
    BitTM
      physicalFieldInverseCounter :=
  GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceFieldInverseSourceComputable
    (unarySubtractionComputable
      paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable
      (sourceFixedWordComputable [true, true, true]))

@[simp] private theorem paperVariableArityPhysicalFieldInverseCounter_valid
    (formula : ThreeCNF) (lower operand : List Bool) :
    physicalFieldInverseCounter
      (binarySourceFieldInverseQuery
        lower operand (encodeThreeCNF formula)) =
      List.replicate
        (2 ^ physicalFieldFormulaDegree formula - 3) true := by
  unfold physicalFieldInverseCounter
  simp only [Function.comp_apply]
  rw [factor400BinarySourceFieldInverseSource_query]
  exact unarySubtractionOutput_valid
    physicalFamilyFieldCardinalityUnary
    (fun _ => [true, true, true])
    (encodeThreeCNF formula)
    (2 ^ physicalFieldFormulaDegree formula)
    3 (paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid formula) rfl

private def paperVariableArityPhysicalFieldInversePreparation
    (input : List Bool) : List Bool :=
  physicalFieldInverseCounter input ++ false ::
    (lengthPrefixedWord input ++
      lengthPrefixedWord (factor400BinarySourceLeftBits input))

@[simp] private theorem paperVariableArityPhysicalFieldInverseOperand_query
    (lower operand source : List Bool) :
    factor400BinarySourceLeftBits
      (binarySourceFieldInverseQuery lower operand source) =
      operand := by
  simp only [factor400BinarySourceLeftBits, Function.comp_apply,
    binarySourceFieldInverseQuery,
    List.append_assoc, firstFieldSuffix_valid, firstFieldContents_valid]

private noncomputable def paperVariableArityPhysicalFieldInversePreparationComputable :
    BitTM
      paperVariableArityPhysicalFieldInversePreparation := by
  have hoperand := GapCVP.TMComposition.computableInPolyTime
    binarySourceLeftBitsComputable
    structuralPrefixWriterComputable
  have hstate := pointwiseAppendComputable
    structuralPrefixWriterComputable hoperand
  have hdelimiter := GapCVP.TMComposition.computableInPolyTime
    hstate (prependBitComputable false)
  have hphysical := pointwiseAppendComputable
    paperVariableArityPhysicalFieldInverseCounterComputable hdelimiter
  change BitTM
    (fun input =>
      physicalFieldInverseCounter input ++ false ::
        (lengthPrefixedWord input ++
          lengthPrefixedWord (factor400BinarySourceLeftBits input)))
  simpa only [Function.comp_apply] using hphysical

private def physicalFieldInverseWord : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix ∘
    boundedRecordFoldOutput
      (sourceAnchoredGridRecordRotationOutput
        binarySourceFieldPowerCandidate) ∘
    paperVariableArityPhysicalFieldInversePreparation

private noncomputable def paperVariableArityPhysicalFieldInverseComputable :
    BitTM
      physicalFieldInverseWord :=
  GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      (GapCVP.TMComposition.computableInPolyTime
        paperVariableArityPhysicalFieldInversePreparationComputable
        (sourceAnchoredGridRecordFoldComputable
          (factor400BinarySourceFieldPowerCandidateComputable
            binarySourceMultiplyModComputable)))
      firstFieldSuffixComputable)
    firstFieldContentsComputable

private theorem paperVariableArityPhysicalFieldInverseWord_valid
    (formula : ThreeCNF)
    (lower operand : GapCVP.Core.EffectiveBinaryField.Word
      (physicalFieldFormulaDegree formula)) :
    physicalFieldInverseWord
      (binarySourceFieldInverseQuery
        (finiteWordBits lower) (finiteWordBits operand)
        (encodeThreeCNF formula)) =
      finiteWordBits
        (sourceFieldPowerIterate lower operand
          (2 ^ physicalFieldFormulaDegree formula - 3)) := by
  let count := 2 ^ physicalFieldFormulaDegree formula - 3
  let anchor := binarySourceFieldInverseQuery
    (finiteWordBits lower) (finiteWordBits operand)
    (encodeThreeCNF formula)
  have hcounter :
      physicalFieldInverseCounter anchor =
        List.replicate count true :=
    paperVariableArityPhysicalFieldInverseCounter_valid
      formula (finiteWordBits lower) (finiteWordBits operand)
  have hoperand :
      factor400BinarySourceLeftBits anchor = finiteWordBits operand :=
    paperVariableArityPhysicalFieldInverseOperand_query
      (finiteWordBits lower) (finiteWordBits operand)
      (encodeThreeCNF formula)
  unfold physicalFieldInverseWord
    paperVariableArityPhysicalFieldInversePreparation
  simp only [Function.comp_apply]
  rw [hcounter, hoperand]
  rw [show
    List.replicate count true ++ false ::
      (lengthPrefixedWord anchor ++
        lengthPrefixedWord (finiteWordBits operand)) =
      unaryBoundedFoldWord count
        (lengthPrefixedWord anchor ++
          lengthPrefixedWord (finiteWordBits operand)) from rfl]
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word]
  rw [factor400BinarySourceFieldPowerRotation_iterate
    lower operand operand (encodeThreeCNF formula) count]
  rw [firstFieldSuffix_valid anchor
    (lengthPrefixedWord
      (finiteWordBits
        (((sourceFieldPowerStep lower operand)^[count]) operand)))]
  simpa only [List.append_nil, sourceFieldPowerIterate] using
    firstFieldContents_valid
      (finiteWordBits
        (((sourceFieldPowerStep lower operand)^[count]) operand)) []

theorem paperVariableArityPhysicalSourceWordValue_injective
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula) :
    Function.Injective (sourceWordValue encodingLength formula) := by
  intro left right hequal
  apply wordElement_injective
    (GapCVP.Core.sourceFieldExponent
      (GapCVP.Core.sourceSizeParameter encodingLength formula))
  apply
    (GapCVP.Core.EffectiveBinaryField.extensionAlgEquivGaloisField
      (GapCVP.Core.sourceFieldExponent
        (GapCVP.Core.sourceSizeParameter encodingLength formula))
      (GapCVP.Core.sourceFieldExponent_pos
        (GapCVP.Core.sourceSizeParameter_ge_one_hundred
          encodingLength formula))).injective
  exact hequal

private theorem paperVariableArityPhysicalFieldInverseSelectedWord_valid
    (formula : ThreeCNF)
    (operand : GapCVP.Core.EffectiveBinaryField.Word
      (physicalFieldFormulaDegree formula)) :
    physicalFieldInverseWord
      (binarySourceFieldInverseQuery
        (finiteWordBits
          (GapCVP.Core.EffectiveBinaryField.irreducibleWord
            (physicalFieldFormulaDegree formula)))
        (finiteWordBits operand)
        (encodeThreeCNF formula)) =
      finiteWordBits (sourceInverseWord operand) := by
  rw [paperVariableArityPhysicalFieldInverseWord_valid]
  congr 1
  apply paperVariableArityPhysicalSourceWordValue_injective
    (encodeThreeCNF formula).length (srcFormula formula)
  rw [sourceWordValue_sourceFieldPowerIterate,
    sourceInverseWord, sourceWordValue_sourceWordPow]
  congr 1
  have hsize := GapCVP.Core.sourceSizeParameter_ge_one_hundred
    (encodeThreeCNF formula).length (srcFormula formula)
  have hsourcePower :
      GapCVP.Core.sourceSizeParameter
          (encodeThreeCNF formula).length (srcFormula formula) ≤
        GapCVP.Core.sourceSizeParameter
            (encodeThreeCNF formula).length (srcFormula formula) ^
          200 := by
    calc
      GapCVP.Core.sourceSizeParameter
          (encodeThreeCNF formula).length (srcFormula formula) =
        GapCVP.Core.sourceSizeParameter
            (encodeThreeCNF formula).length (srcFormula formula) ^
          1 := by simp only [pow_one]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hfield := GapCVP.Core.sourceFiniteField_card_lower hsize
  rw [GapCVP.Core.sourceFiniteField_card hsize] at hfield
  have hcardinality :
      3 ≤ 2 ^ physicalFieldFormulaDegree formula := by
    change
      3 ≤ 2 ^ GapCVP.Core.sourceFieldExponent
        (GapCVP.Core.sourceSizeParameter
          (encodeThreeCNF formula).length (srcFormula formula))
    calc
      3 ≤ GapCVP.Core.sourceSizeParameter
          (encodeThreeCNF formula).length
          (srcFormula formula) := by omega
      _ ≤ GapCVP.Core.sourceSizeParameter
          (encodeThreeCNF formula).length
          (srcFormula formula) ^ 200 := hsourcePower
      _ ≤ _ := hfield
  change
    (2 ^ physicalFieldFormulaDegree formula - 3) + 1 =
      2 ^ physicalFieldFormulaDegree formula - 2
  omega

end

section

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryFieldInverseTM
open GapCVP.BinaryModularReductionTM GapCVP.PhysicalFamilyRowTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM

private def paperVariableAritySourceSelectedFieldOperandQuery
    (operand source : List Bool) : List Bool :=
  lengthPrefixedWord operand ++ source

private def sourceSelectedFieldInversePreparation
    (input : List Bool) : List Bool :=
  binarySourceFieldInverseQuery
    (sourceSelectedIrreducibleWord
      (firstFieldSuffix input))
    (firstFieldContents input)
    (firstFieldSuffix input)

private noncomputable def paperVariableAritySourceSelectedFieldInversePreparationComputable :
    BitTM
      sourceSelectedFieldInversePreparation := by
  have hmodulus := GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      firstFieldSuffixComputable
      paperVariableAritySourceSelectedIrreducibleWordComputable)
    structuralPrefixWriterComputable
  have hoperand := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable hmodulus
    (pointwiseAppendComputable
      hoperand firstFieldSuffixComputable)
  unfold sourceSelectedFieldInversePreparation
  simpa only [binarySourceFieldInverseQuery, List.append_assoc, Function.comp_apply]
      using hphysical

/-- GapCVP reduction support. -/
def sourceSelectedFieldInverseWord : List Bool → List Bool :=
  physicalFieldInverseWord ∘
    sourceSelectedFieldInversePreparation

/-- GapCVP reduction support. -/
noncomputable def paperVariableAritySourceSelectedFieldInverseComputable :
    BitTM
      sourceSelectedFieldInverseWord :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableAritySourceSelectedFieldInversePreparationComputable
    paperVariableArityPhysicalFieldInverseComputable

@[simp] theorem paperVariableAritySourceSelectedFieldInverseWord_valid
    (formula : ThreeCNF)
    (operand : GapCVP.Core.EffectiveBinaryField.Word
      (physicalFieldFormulaDegree formula)) :
    sourceSelectedFieldInverseWord
      (paperVariableAritySourceSelectedFieldOperandQuery
        (finiteWordBits operand) (encodeThreeCNF formula)) =
      finiteWordBits (sourceInverseWord operand) := by
  unfold sourceSelectedFieldInverseWord
    sourceSelectedFieldInversePreparation
    paperVariableAritySourceSelectedFieldOperandQuery
  simp only [Function.comp_apply,
    firstFieldSuffix_valid, firstFieldContents_valid]
  rw [paperVariableAritySourceSelectedIrreducibleWord_valid]
  exact paperVariableArityPhysicalFieldInverseSelectedWord_valid formula operand

end

section

open Turing GapCVP.BinaryEncoding GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.PhysicalFamilyRowTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine

private def physicalCellSelectedModulusWord :
    List Bool → List Bool :=
  sourceSelectedIrreducibleWord ∘
    sourceExplicitAffineCellOriginalSource

private noncomputable def paperVariableArityPhysicalCellSelectedModulusComputable :
    BitTM
      physicalCellSelectedModulusWord :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    paperVariableAritySourceSelectedIrreducibleWordComputable

private noncomputable def physicalCellSelectedModulusComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalCellSelectedModulusWord
  computer := paperVariableArityPhysicalCellSelectedModulusComputable

@[simp] private theorem paperVariableArityPhysicalCellSelectedModulusWord_valid
    (row column : ℕ) (formula : ThreeCNF) :
    physicalCellSelectedModulusWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      finiteWordBits
        (GapCVP.Core.EffectiveBinaryField.irreducibleWord
          (sourceIrreducibleFormulaDegree formula)) := by
  unfold physicalCellSelectedModulusWord
  rw [Function.comp_apply, sourceExplicitAffineCellOriginalSource_query]
  exact paperVariableAritySourceSelectedIrreducibleWord_valid formula

private def paperVariableArityPhysicalCellInverseQuery
    (operand : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (operand.output input) ++
    sourceExplicitAffineCellOriginalSource input

private noncomputable def paperVariableArityPhysicalCellInverseQueryComputable
    (operand : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (paperVariableArityPhysicalCellInverseQuery operand) := by
  have hprefixed := GapCVP.TMComposition.computableInPolyTime
    operand.computer structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable hprefixed
    sourceExplicitAffineCellOriginalSourceComputable
  change BitTM
    (fun input => lengthPrefixedWord (operand.output input) ++
      sourceExplicitAffineCellOriginalSource input)
  simpa only [Function.comp_apply] using hphysical

/-- GapCVP reduction support. -/
def physicalCellInverseWord
    (operand : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  sourceSelectedFieldInverseWord ∘
    paperVariableArityPhysicalCellInverseQuery operand

private noncomputable def paperVariableArityPhysicalCellInverseComputable
    (operand : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalCellInverseWord operand) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityPhysicalCellInverseQueryComputable operand)
    paperVariableAritySourceSelectedFieldInverseComputable

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalCellInverseComputer
    (operand : SourcePhysicalLagrangeWordComputer) :
    SourcePhysicalLagrangeWordComputer where
  output := physicalCellInverseWord operand
  computer := paperVariableArityPhysicalCellInverseComputable operand

@[simp] theorem paperVariableArityPhysicalCellInverseWord_valid
    (operand : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (physicalFieldFormulaDegree formula))
    (hvalue : operand.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits value) :
    physicalCellInverseWord operand
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      finiteWordBits (sourceInverseWord value) := by
  unfold physicalCellInverseWord
    paperVariableArityPhysicalCellInverseQuery
  rw [Function.comp_apply, hvalue,
    sourceExplicitAffineCellOriginalSource_query]
  exact paperVariableAritySourceSelectedFieldInverseWord_valid
    formula value

private def paperVariableArityPhysicalCellFieldRankQuery
    (rank : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (rank.output input) ++
    lengthPrefixedWord
      (physicalFamilyFieldCardinalityUnary
        (sourceExplicitAffineCellOriginalSource input)) ++
      sourceExplicitAffineCellOriginalSource input

private noncomputable def paperVariableArityPhysicalCellFieldRankQueryComputable
    (rank : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (paperVariableArityPhysicalCellFieldRankQuery rank) := by
  have hrank := GapCVP.TMComposition.computableInPolyTime
    rank.computer structuralPrefixWriterComputable
  have hcard := GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      sourceExplicitAffineCellOriginalSourceComputable
      paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable)
    structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable hrank
    (pointwiseAppendComputable hcard
      sourceExplicitAffineCellOriginalSourceComputable)
  change BitTM
    (fun input => lengthPrefixedWord (rank.output input) ++
      lengthPrefixedWord
        (physicalFamilyFieldCardinalityUnary
          (sourceExplicitAffineCellOriginalSource input)) ++
        sourceExplicitAffineCellOriginalSource input)
  simpa only [List.append_assoc, Function.comp_apply] using hphysical

/-- GapCVP reduction support. -/
def physicalCellFieldWordAt
    (rank : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  sourceIrreducibleRankCoefficientWord ∘
    paperVariableArityPhysicalCellFieldRankQuery rank

/-- GapCVP reduction support. -/
noncomputable def physicalCellFieldWordAtComputable
    (rank : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalCellFieldWordAt rank) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityPhysicalCellFieldRankQueryComputable rank)
    paperVariableAritySourceIrreducibleRankCoefficientWordComputable

theorem physicalCellFieldWordAt_valid
    (rank : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (index : Fin
      (2 ^ sourceIrreducibleFormulaDegree formula))
    (hrank : rank.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate index.val true) :
    physicalCellFieldWordAt rank
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      finiteWordBits
        (indexedWord (sourceIrreducibleFormulaDegree formula)
          index) := by
  unfold physicalCellFieldWordAt
    paperVariableArityPhysicalCellFieldRankQuery
  rw [Function.comp_apply, hrank,
    sourceExplicitAffineCellOriginalSource_query,
    paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid]
  exact sourceIrreducibleRankCoefficientWord_eq_indexedWord
    formula index
    (List.replicate
      (physFieldCard formula) true)

end

end Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine

namespace BinaryCompactPhysicalFieldWordXorTM

open Turing Polynomial GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.GaussianXorWorker GapCVP.BinaryFieldBasis
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalCellGridWordTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryPhysicalWordRuntimeDegreeTM

/-- GapCVP reduction support. -/
def compactPhysicalFieldWordXorValue {degree : ℕ}
    (left right : GapCVP.Core.EffectiveBinaryField.Word degree) :
    GapCVP.Core.EffectiveBinaryField.Word degree :=
  fun position => Bool.xor (left position) (right position)

private theorem compactPhysicalFieldWordXorValue_wordPolynomial
    {degree : ℕ}
    (left right : GapCVP.Core.EffectiveBinaryField.Word degree) :
    wordPolynomial (compactPhysicalFieldWordXorValue left right) =
      wordPolynomial left + wordPolynomial right := by
  apply Polynomial.ext
  intro position
  by_cases hposition : position < degree
  · let index : Fin degree := ⟨position, hposition⟩
    change
      (wordPolynomial
        (compactPhysicalFieldWordXorValue left right)).coeff index.val =
        (wordPolynomial left + wordPolynomial right).coeff index.val
    rw [Polynomial.coeff_add, wordPolynomial_coeff_fin,
      wordPolynomial_coeff_fin, wordPolynomial_coeff_fin]
    exact bitValue_xor (left index) (right index)
  · have hlarge : degree ≤ position := Nat.le_of_not_gt hposition
    rw [wordPolynomial_coeff_eq_zero _ position hlarge,
      Polynomial.coeff_add,
      wordPolynomial_coeff_eq_zero left position hlarge,
      wordPolynomial_coeff_eq_zero right position hlarge,
      add_zero]

private theorem compactPhysicalFieldWordXorValue_wordElement
    {degree : ℕ}
    (left right : GapCVP.Core.EffectiveBinaryField.Word degree) :
    wordElement (compactPhysicalFieldWordXorValue left right) =
      wordElement left + wordElement right := by
  unfold wordElement
  rw [compactPhysicalFieldWordXorValue_wordPolynomial, map_add]

private theorem compactPhysicalFieldWordXorValue_sourceWordValue
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (left right : GapCVP.Core.EffectiveBinaryField.Word
      (GapCVP.Core.sourceFieldExponent
        (GapCVP.Core.sourceSizeParameter encodingLength formula))) :
    sourceWordValue encodingLength formula
        (compactPhysicalFieldWordXorValue left right) =
      sourceWordValue encodingLength formula left +
        sourceWordValue encodingLength formula right := by
  unfold sourceWordValue
  rw [compactPhysicalFieldWordXorValue_wordElement, map_add]

theorem compactPhysicalFieldWordXorValue_sourceWordValue_sub
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (left right : GapCVP.Core.EffectiveBinaryField.Word
      (GapCVP.Core.sourceFieldExponent
        (GapCVP.Core.sourceSizeParameter encodingLength formula))) :
    sourceWordValue encodingLength formula
        (compactPhysicalFieldWordXorValue left right) =
      sourceWordValue encodingLength formula left -
        sourceWordValue encodingLength formula right := by
  rw [CharTwo.sub_eq_add]
  exact compactPhysicalFieldWordXorValue_sourceWordValue
    encodingLength formula left right

private def compactPhysicalFieldWordXorOriginalCell : List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldWordXorOriginalCellComputable :
    BitTM
      compactPhysicalFieldWordXorOriginalCell :=
  factor400BinaryPhysicalWordRuntimeCompositionComputer
    firstFieldSuffixComputable firstFieldSuffixComputable

private def compactPhysicalFieldWordXorCandidateOperand
    (worker : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  worker.output ∘ compactPhysicalFieldWordXorOriginalCell

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldWordXorCandidateOperandComputable
    (worker : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalFieldWordXorCandidateOperand worker) :=
  factor400BinaryPhysicalWordRuntimeCompositionComputer
    compactPhysicalFieldWordXorOriginalCellComputable worker.computer

private def compactPhysicalFieldWordXorCandidateBit
    (worker : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  fiveFamilyOriginalDynamicBitWord firstFieldContents
    (compactPhysicalFieldWordXorCandidateOperand worker)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldWordXorCandidateBitComputable
    (worker : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalFieldWordXorCandidateBit worker) :=
  fiveOriginalDynamicBitComputable firstFieldContentsComputable
    (compactPhysicalFieldWordXorCandidateOperandComputable worker)

private def compactPhysicalFieldWordXorCandidate
    (left right : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  binaryGaussianXorHeadWord ∘
    (fun input =>
      compactPhysicalFieldWordXorCandidateBit left input ++
        compactPhysicalFieldWordXorCandidateBit right input)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldWordXorCandidateComputable
    (left right : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalFieldWordXorCandidate left right) :=
  factor400BinaryPhysicalWordRuntimeCompositionComputer
    (physicalCellGridAppendComputer
      (compactPhysicalFieldWordXorCandidateBitComputable left)
      (compactPhysicalFieldWordXorCandidateBitComputable right))
    binaryGaussianXorHeadComputable

@[simp] private theorem compactPhysicalFieldWordXorOriginalCell_query
    (width : SourceQaryMaskDynamicGridWidth)
    (input : List Bool) (rank : ℕ) :
    compactPhysicalFieldWordXorOriginalCell
        (lengthPrefixedWord (List.replicate rank true) ++
          sourceQaryMaskDynamicGridBaseSource width input) = input := by
  simp only [compactPhysicalFieldWordXorOriginalCell, sourceQaryMaskDynamicGridBaseSource,
      Function.comp_apply,
      firstFieldSuffix_valid]

private theorem compactPhysicalFieldWordXorCandidateBit_query
    (worker : SourcePhysicalLagrangeWordComputer)
    (width : SourceQaryMaskDynamicGridWidth)
    (input : List Bool) (rank : ℕ) :
    compactPhysicalFieldWordXorCandidateBit worker
        (lengthPrefixedWord (List.replicate rank true) ++
          sourceQaryMaskDynamicGridBaseSource width input) =
      [((worker.output input).drop rank).headD false] := by
  let query := lengthPrefixedWord (List.replicate rank true) ++
    sourceQaryMaskDynamicGridBaseSource width input
  have hrank : firstFieldContents query =
      List.replicate rank true := by
    simp only [firstFieldContents_valid, query]
  unfold compactPhysicalFieldWordXorCandidateBit
  rw [fiveOriginalDynamicBitWord_valid firstFieldContents
    (compactPhysicalFieldWordXorCandidateOperand worker)
    query rank hrank]
  simp only [compactPhysicalFieldWordXorCandidateOperand, Function.comp_apply,
      compactPhysicalFieldWordXorOriginalCell_query, List.headD_eq_head?_getD, List.head?_drop,
          query]

private theorem compactPhysicalFieldWordXorCandidate_query
    (left right : SourcePhysicalLagrangeWordComputer)
    (width : SourceQaryMaskDynamicGridWidth)
    (input : List Bool) (rank : ℕ) :
    compactPhysicalFieldWordXorCandidate left right
        (lengthPrefixedWord (List.replicate rank true) ++
          sourceQaryMaskDynamicGridBaseSource width input) =
      [Bool.xor
        (((left.output input).drop rank).headD false)
        (((right.output input).drop rank).headD false)] := by
  unfold compactPhysicalFieldWordXorCandidate
  simp only [Function.comp_apply,
    compactPhysicalFieldWordXorCandidateBit_query]
  rfl

private noncomputable def compactPhysicalFieldWordXorDegreeWidth
    (degree : SourcePhysicalLagrangeWordComputer) :
    SourceQaryMaskDynamicGridWidth where
  output := degree.output
  computer := degree.computer

/-- GapCVP reduction support. -/
def compactPhysicalFieldWordXorWithDegree
    (degree left right : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    (compactPhysicalFieldWordXorDegreeWidth degree)
    (compactPhysicalFieldWordXorCandidateComputable left right)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldWordXorWithDegreeComputable
    (degree left right : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalFieldWordXorWithDegree degree left right) :=
  maskDynamicGridRecordCatalogueComputable
    (compactPhysicalFieldWordXorDegreeWidth degree)
    (compactPhysicalFieldWordXorCandidateComputable left right)

private theorem finiteWordBits_compactPhysicalFieldWordXorValue
    {degree : ℕ}
    (left right : GapCVP.Core.EffectiveBinaryField.Word degree) :
    (List.range degree).map
        (fun rank => Bool.xor
          (((finiteWordBits left).drop rank).headD false)
          (((finiteWordBits right).drop rank).headD false)) =
      finiteWordBits (compactPhysicalFieldWordXorValue left right) := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  unfold finiteWordBits
  apply List.map_congr_left
  intro index _
  simp only [List.headD_eq_head?_getD, List.head?_drop, List.getElem?_map, Function.comp_apply,
      List.length_finRange, Fin.is_lt, getElem?_pos, List.getElem_finRange, Fin.cast_mk, Fin.eta,
          Option.map_some,
      Option.getD_some, compactPhysicalFieldWordXorValue]

theorem compactPhysicalFieldWordXorWithDegree_valid
    (degreeWorker left right : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) (degree : ℕ)
    (leftWord rightWord : GapCVP.Core.EffectiveBinaryField.Word degree)
    (hdegree : degreeWorker.output input =
      List.replicate degree true)
    (hleft : left.output input = finiteWordBits leftWord)
    (hright : right.output input = finiteWordBits rightWord) :
    compactPhysicalFieldWordXorWithDegree
        degreeWorker left right input =
      finiteWordBits
        (compactPhysicalFieldWordXorValue leftWord rightWord) := by
  unfold compactPhysicalFieldWordXorWithDegree
  rw [maskDynamicGridRecordCatalogueOutput_valid
    (compactPhysicalFieldWordXorDegreeWidth degreeWorker)
    (compactPhysicalFieldWordXorCandidateComputable left right)
    input degree hdegree]
  simp_rw [compactPhysicalFieldWordXorCandidate_query]
  rw [hleft, hright, ← List.map_eq_flatMap]
  exact finiteWordBits_compactPhysicalFieldWordXorValue
    leftWord rightWord

end BinaryCompactPhysicalFieldWordXorTM

namespace BinaryCompactPhysicalLagrangeProductFoldTM

open Turing GapCVP.SourceFormulaStructuralDecoder GapCVP.BinaryModularReductionTM
open GapCVP.BinarySourceFieldMultiplicationTM GapCVP.BinaryPhysicalLagrangeProductFoldTM

private def compactPhysicalLagrangeProductFold :
    List Bool → List Bool :=
  sourcePhysicalLagrangeProductFoldOutput

private noncomputable def compactPhysicalLagrangeProductFoldComputable :
    BitTM
      compactPhysicalLagrangeProductFold :=
  sourcePhysicalLagrangeProductFoldComputable
    binarySourceMultiplyModComputable

private def compactPhysicalLagrangeProductWord :
    List Bool → List Bool :=
  sourcePhysicalLagrangeProductAccumulator ∘
    compactPhysicalLagrangeProductFold

private noncomputable def compactPhysicalLagrangeProductWordComputable :
    BitTM
      compactPhysicalLagrangeProductWord :=
  GapCVP.TMComposition.computableInPolyTime
    compactPhysicalLagrangeProductFoldComputable
    sourcePhysicalLagrangeProductAccumulatorComputable

private theorem compactPhysicalLagrangeProductWord_generic_valid
    {degree : ℕ}
    (lower initial : GapCVP.Core.EffectiveBinaryField.Word degree)
    (factors : List (GapCVP.Core.EffectiveBinaryField.Word degree))
    (source : List Bool) :
    compactPhysicalLagrangeProductWord
      (sourcePhysicalLagrangeProductFoldWord
        lower initial factors source) =
      finiteWordBits
        (factors.foldl
          (GapCVP.Core.EffectiveBinaryField.multiplyMod lower)
          initial) := by
  change
    firstFieldContents
      (firstFieldSuffix
        (sourcePhysicalLagrangeProductFoldOutput
          (sourcePhysicalLagrangeProductFoldWord
            lower initial factors source))) = _
  rw [sourcePhysicalLagrangeProductFoldOutput_valid]
  rw [firstFieldSuffix_valid]
  simpa only [List.append_nil] using
    (firstFieldContents_valid
      (finiteWordBits
        (factors.foldl
          (GapCVP.Core.EffectiveBinaryField.multiplyMod lower)
          initial)) [])

end BinaryCompactPhysicalLagrangeProductFoldTM

namespace BinaryCompactPhysicalLagrangeFactorStreamTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryPhysicalLagrangeProductFoldTM
open GapCVP.BinaryCompactPhysicalLagrangeProductFoldTM

private def compactPhysicalLagrangeNodeFactorRecord
    (factor : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (factor.output input)

private noncomputable def compactPhysicalLagrangeNodeFactorRecordComputable
    (factor : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalLagrangeNodeFactorRecord factor) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    factor.computer structuralPrefixWriterComputable
  change BitTM
    (fun input => lengthPrefixedWord (factor.output input))
  simpa only [Function.comp_def] using hphysical

/-- GapCVP reduction support. -/
def compactPhysicalLagrangeNodeFactorCatalogue
    (width : SourceQaryMaskDynamicGridWidth)
    (factor : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    width (compactPhysicalLagrangeNodeFactorRecordComputable factor)

private noncomputable def compactPhysicalLagrangeNodeFactorCatalogueComputable
    (width : SourceQaryMaskDynamicGridWidth)
    (factor : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalLagrangeNodeFactorCatalogue width factor) :=
  maskDynamicGridRecordCatalogueComputable
    width (compactPhysicalLagrangeNodeFactorRecordComputable factor)

/-- GapCVP reduction support. -/
def compactPhysicalLagrangeNodeFactorQuery
    (width : SourceQaryMaskDynamicGridWidth)
    (input : List Bool) (rank : ℕ) : List Bool :=
  lengthPrefixedWord (List.replicate rank true) ++
    sourceQaryMaskDynamicGridBaseSource width input

theorem compactPhysicalLagrangeNodeFactorCatalogue_valid
    (width : SourceQaryMaskDynamicGridWidth)
    (factor : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) (count : ℕ)
    (hwidth : width.output input = List.replicate count true) :
    compactPhysicalLagrangeNodeFactorCatalogue width factor input =
      (List.range count).flatMap
        (fun rank =>
          lengthPrefixedWord
            (factor.output
              (compactPhysicalLagrangeNodeFactorQuery
                width input rank))) := by
  exact maskDynamicGridRecordCatalogueOutput_valid
    width (compactPhysicalLagrangeNodeFactorRecordComputable factor)
    input count hwidth

private noncomputable def compactPhysicalLagrangeOriginalSourceComputer :
    SourcePhysicalLagrangeWordComputer where
  output := sourceExplicitAffineCellOriginalSource
  computer := sourceExplicitAffineCellOriginalSourceComputable

private def compactPhysicalLagrangeFactorProductAnchor
    (lower source : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (lower.output input) ++ source.output input

private noncomputable def compactPhysicalLagrangeFactorProductAnchorComputable
    (lower source : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalLagrangeFactorProductAnchor lower source) := by
  have hphysical := pointwiseAppendComputable
    (sourcePhysicalLagrangePrefixedComputable lower)
    source.computer
  change BitTM
    (fun input =>
      lengthPrefixedWord (lower.output input) ++ source.output input)
  exact hphysical

private def compactPhysicalLagrangeFactorProductPreparation
    (width : SourceQaryMaskDynamicGridWidth)
    (lower initial source factor : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  width.output input ++ false ::
    (lengthPrefixedWord
        (compactPhysicalLagrangeFactorProductAnchor lower source input) ++
      lengthPrefixedWord (initial.output input) ++
        compactPhysicalLagrangeNodeFactorCatalogue width factor input)

/-- GapCVP reduction support. -/
noncomputable def
    compactPhysicalLagrangeFactorProductPreparationComputable
    (width : SourceQaryMaskDynamicGridWidth)
    (lower initial source factor : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalLagrangeFactorProductPreparation
        width lower initial source factor) := by
  have hanchor := GapCVP.TMComposition.computableInPolyTime
    (compactPhysicalLagrangeFactorProductAnchorComputable lower source)
    structuralPrefixWriterComputable
  have htail := pointwiseAppendComputable
    (sourcePhysicalLagrangePrefixedComputable initial)
    (compactPhysicalLagrangeNodeFactorCatalogueComputable width factor)
  have hseed := pointwiseAppendComputable hanchor htail
  have hdelimiter := GapCVP.TMComposition.computableInPolyTime
    hseed (prependBitComputable false)
  have hphysical := pointwiseAppendComputable
    width.computer hdelimiter
  change BitTM
    (fun input =>
      width.output input ++ false ::
        (lengthPrefixedWord
            (compactPhysicalLagrangeFactorProductAnchor
              lower source input) ++
          lengthPrefixedWord (initial.output input) ++
            compactPhysicalLagrangeNodeFactorCatalogue
              width factor input))
  simpa only [List.append_assoc, Function.comp_apply, sourcePhysicalLagrangePrefixedOutput]
      using hphysical

/-- GapCVP reduction support. -/
def compactPhysicalLagrangeFactorProductWord
    (width : SourceQaryMaskDynamicGridWidth)
    (lower initial source factor : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  compactPhysicalLagrangeProductWord ∘
    compactPhysicalLagrangeFactorProductPreparation
      width lower initial source factor

/-- GapCVP reduction support. -/
noncomputable def compactPhysicalLagrangeFactorProductComputable
    (width : SourceQaryMaskDynamicGridWidth)
    (lower initial source factor : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalLagrangeFactorProductWord
        width lower initial source factor) :=
  GapCVP.TMComposition.computableInPolyTime
    (compactPhysicalLagrangeFactorProductPreparationComputable
      width lower initial source factor)
    compactPhysicalLagrangeProductWordComputable

theorem compactPhysicalLagrangeFactorProductWord_valid
    {degree : ℕ}
    (width : SourceQaryMaskDynamicGridWidth)
    (lower initial source factor : SourcePhysicalLagrangeWordComputer)
    (input : List Bool)
    (lowerWord initialWord : GapCVP.Core.EffectiveBinaryField.Word degree)
    (factors : List (GapCVP.Core.EffectiveBinaryField.Word degree))
    (original : List Bool)
    (hwidth : width.output input = List.replicate factors.length true)
    (hlower : lower.output input = finiteWordBits lowerWord)
    (hinitial : initial.output input = finiteWordBits initialWord)
    (hsource : source.output input = original)
    (hfactors : compactPhysicalLagrangeNodeFactorCatalogue
      width factor input =
        sourcePhysicalLagrangePackedFactorWords factors) :
    compactPhysicalLagrangeFactorProductWord
      width lower initial source factor input =
        finiteWordBits
          (factors.foldl
            (GapCVP.Core.EffectiveBinaryField.multiplyMod lowerWord)
            initialWord) := by
  unfold compactPhysicalLagrangeFactorProductWord
    compactPhysicalLagrangeFactorProductPreparation
    compactPhysicalLagrangeFactorProductAnchor
  rw [Function.comp_apply, hwidth, hlower, hinitial, hsource,
    hfactors]
  exact compactPhysicalLagrangeProductWord_generic_valid
    lowerWord initialWord factors original

end BinaryCompactPhysicalLagrangeFactorStreamTM

namespace PhysicalOrdinaryShiftedCoefficientTM

open Turing GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinarySourceFieldMultiplicationTM GapCVP.BinaryCompactPhysicalFieldWordXorTM
open GapCVP.PhysicalFamilyRowTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine

/-- GapCVP reduction support. -/
abbrev PaperVariableArityPhysicalInterpolationWord (formula : ThreeCNF) :=
  GapCVP.Core.EffectiveBinaryField.Word
    (physDegree formula)

private def physicalInterpolationDegreeWord :
    List Bool → List Bool :=
  physicalFamilyFieldDegreeUnary ∘
    sourceExplicitAffineCellOriginalSource

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationDegreeWordComputable :
    BitTM
      physicalInterpolationDegreeWord :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable

private noncomputable def paperVariableArityPhysicalInterpolationDegreeComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationDegreeWord
  computer := paperVariableArityPhysicalInterpolationDegreeWordComputable

@[simp] private theorem paperVariableArityPhysicalInterpolationDegreeWord_valid
    (row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationDegreeWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physDegree formula) true := by
  unfold physicalInterpolationDegreeWord
  rw [Function.comp_apply, sourceExplicitAffineCellOriginalSource_query]
  exact paperVariableArityPhysicalFamilyFieldDegreeUnary_valid formula

private def physicalInterpolationDifferenceWord
    (left right : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  compactPhysicalFieldWordXorWithDegree
    paperVariableArityPhysicalInterpolationDegreeComputer left right

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationDifferenceWordComputable
    (left right : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalInterpolationDifferenceWord left right) :=
  compactPhysicalFieldWordXorWithDegreeComputable
    paperVariableArityPhysicalInterpolationDegreeComputer left right

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalInterpolationDifferenceComputer
    (left right : SourcePhysicalLagrangeWordComputer) :
    SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationDifferenceWord left right
  computer :=
    paperVariableArityPhysicalInterpolationDifferenceWordComputable left right

theorem paperVariableArityPhysicalInterpolationDifferenceWord_valid
    (left right : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (leftWord rightWord : PaperVariableArityPhysicalInterpolationWord formula)
    (hleft : left.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits leftWord)
    (hright : right.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits rightWord) :
    physicalInterpolationDifferenceWord left right
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      finiteWordBits
        (compactPhysicalFieldWordXorValue leftWord rightWord) := by
  exact compactPhysicalFieldWordXorWithDegree_valid
    paperVariableArityPhysicalInterpolationDegreeComputer left right
    (affineCellQuery row column (encodeThreeCNF formula))
    (physDegree formula) leftWord rightWord
    (paperVariableArityPhysicalInterpolationDegreeWord_valid
      row column formula) hleft hright

/-- GapCVP reduction support. -/
def paperVariableArityPhysicalInterpolationProductWord
    (left right : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  sourcePhysicalLagrangeMultiplyWord
    physicalCellSelectedModulusComputer left right

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalInterpolationProductWordComputable
    (left right : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (paperVariableArityPhysicalInterpolationProductWord left right) :=
  sourcePhysicalLagrangeMultiplyComputable
    binarySourceMultiplyModComputable
    physicalCellSelectedModulusComputer left right

theorem paperVariableArityPhysicalInterpolationProductWord_valid
    (left right : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (leftWord rightWord : PaperVariableArityPhysicalInterpolationWord formula)
    (hleft : left.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits leftWord)
    (hright : right.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits rightWord) :
    paperVariableArityPhysicalInterpolationProductWord left right
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      finiteWordBits
        (GapCVP.Core.EffectiveBinaryField.multiplyMod
          (GapCVP.Core.EffectiveBinaryField.irreducibleWord
            (physDegree formula))
          leftWord rightWord) := by
  exact sourcePhysicalLagrangeMultiplyWord_valid
    (GapCVP.Core.EffectiveBinaryField.irreducibleWord
      (physDegree formula))
    leftWord rightWord
    physicalCellSelectedModulusComputer left right
    row column (encodeThreeCNF formula)
    (paperVariableArityPhysicalCellSelectedModulusWord_valid
      row column formula) hleft hright

end PhysicalOrdinaryShiftedCoefficientTM

namespace BinaryCompactPhysicalNodeParityTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert
open GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.Factor400BinaryPhysicalParityTM

private def compactPhysicalNodeParityPreparation
    (width : SourceQaryMaskDynamicGridWidth)
    {term : List Bool → List Bool}
    (computer : BitTM term)
    (input : List Bool) : List Bool :=
  width.output input ++ false ::
    (false :: maskDynamicGridRecordCatalogueOutput
      width computer input)

private noncomputable def compactPhysicalNodeParityPreparationComputable
    (width : SourceQaryMaskDynamicGridWidth)
    {term : List Bool → List Bool}
    (computer : BitTM term) :
    BitTM
      (compactPhysicalNodeParityPreparation width computer) := by
  have hcatalogue :=
    maskDynamicGridRecordCatalogueComputable width computer
  have hseed := GapCVP.TMComposition.computableInPolyTime
    hcatalogue (prependBitComputable false)
  have hdelimiter := GapCVP.TMComposition.computableInPolyTime
    hseed (prependBitComputable false)
  have hphysical := pointwiseAppendComputable
    width.computer hdelimiter
  change BitTM
    (fun input => width.output input ++
      false :: (false ::
        maskDynamicGridRecordCatalogueOutput
          width computer input))
  simpa only [Function.comp_apply] using hphysical

private def compactPhysicalNodeParity
    (width : SourceQaryMaskDynamicGridWidth)
    {term : List Bool → List Bool}
    (computer : BitTM term) : List Bool → List Bool :=
  prefixParityOutput ∘
    compactPhysicalNodeParityPreparation width computer

private noncomputable def compactPhysicalNodeParityComputable
    (width : SourceQaryMaskDynamicGridWidth)
    {term : List Bool → List Bool}
    (computer : BitTM term) :
    BitTM
      (compactPhysicalNodeParity width computer) :=
  GapCVP.TMComposition.computableInPolyTime
    (compactPhysicalNodeParityPreparationComputable width computer)
    prefixParityComputable

private theorem compactPhysicalNodeParity_valid
    (width : SourceQaryMaskDynamicGridWidth)
    {term : List Bool → List Bool}
    (computer : BitTM term)
    (input : List Bool) (count : ℕ) (value : ℕ → Bool)
    (hwidth : width.output input = List.replicate count true)
    (hterm : ∀ rank ∈ List.range count,
      term (lengthPrefixedWord (List.replicate rank true) ++
        sourceQaryMaskDynamicGridBaseSource width input) =
          [value rank]) :
    compactPhysicalNodeParity width computer input =
      [((List.range count).map value).foldl Bool.xor false] := by
  have hcatalogue :=
    maskDynamicGridRecordCatalogueOutput_valid
      width computer input count hwidth
  have hrecords :
      (List.range count).flatMap
          (fun rank => term
            (lengthPrefixedWord (List.replicate rank true) ++
              sourceQaryMaskDynamicGridBaseSource width input)) =
        (List.range count).map value := by
    rw [List.map_eq_flatMap]
    exact List.flatMap_congr hterm
  unfold compactPhysicalNodeParity compactPhysicalNodeParityPreparation
  simp only [Function.comp_apply]
  rw [hwidth, hcatalogue, hrecords]
  have hparity := prefixParityOutput_valid
    false ((List.range count).map value) []
  simpa only [unaryBoundedFoldWord, List.length_map, List.length_range, List.append_nil]
      using hparity

end BinaryCompactPhysicalNodeParityTM

namespace PhysicalOrdinaryShiftedCoefficientSumTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryDimensionTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalNodeParityTM GapCVP.PhysicalFamilyRowTM

private def physicalInterpolationVariableCountWord :
    List Bool → List Bool :=
  physicalFamilyVariableCountUnary ∘
    sourceExplicitAffineCellOriginalSource

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationVariableCountWordComputable :
    BitTM
      physicalInterpolationVariableCountWord :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    paperVariableArityPhysicalFamilyVariableCountUnaryComputable

@[simp] private theorem paperVariableArityPhysicalInterpolationVariableCountWord_valid
    (row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationVariableCountWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalFormulaVariableCount formula) true := by
  unfold physicalInterpolationVariableCountWord
  rw [Function.comp_apply, sourceExplicitAffineCellOriginalSource_query]
  exact paperVariableArityPhysicalFamilyVariableCountUnary_valid formula

private def physicalInterpolationShiftedVariableCountWord :
    List Bool → List Bool :=
  unarySubtractionOutput
    physicalInterpolationVariableCountWord
    (fun _ => [true])

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationShiftedVariableCountWordComputable :
    BitTM
      physicalInterpolationShiftedVariableCountWord :=
  unarySubtractionComputable
    paperVariableArityPhysicalInterpolationVariableCountWordComputable
    (sourceFixedWordComputable [true])

@[simp] theorem
    paperVariableArityPhysicalInterpolationShiftedVariableCountWord_valid
    (row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationShiftedVariableCountWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalFormulaVariableCount formula - 1) true := by
  exact unarySubtractionOutput_valid
    physicalInterpolationVariableCountWord
    (fun _ => [true])
    (affineCellQuery row column (encodeThreeCNF formula))
    (physicalFormulaVariableCount formula) 1
    (paperVariableArityPhysicalInterpolationVariableCountWord_valid
      row column formula)
    rfl

/-- GapCVP reduction support. -/
def physicalOrdinaryNodePrefixWord
    (moment : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  true :: fourFamilyComputedUnaryProductOutput
    physicalInterpolationVariableCountWord
    moment.output input

private noncomputable def paperVariableArityPhysicalOrdinaryNodePrefixWordComputable
    (moment : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalOrdinaryNodePrefixWord moment) :=
  GapCVP.TMComposition.computableInPolyTime
    (fourFamilyComputedUnaryProductComputable
      paperVariableArityPhysicalInterpolationVariableCountWordComputable
      moment.computer)
    (GapCVP.SourceMachineCert.prependBitComputable
      true)

theorem paperVariableArityPhysicalOrdinaryNodePrefixWord_valid
    (moment : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF) (momentRank : ℕ)
    (hmoment : moment.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
        List.replicate momentRank true) :
    physicalOrdinaryNodePrefixWord moment
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (physicalFormulaVariableCount formula *
          momentRank + 1) true := by
  unfold physicalOrdinaryNodePrefixWord
  rw [fourFamilyComputedUnaryProductOutput_valid
    physicalInterpolationVariableCountWord
    moment.output
    (affineCellQuery row column (encodeThreeCNF formula))
    (physicalFormulaVariableCount formula)
    momentRank
    (paperVariableArityPhysicalInterpolationVariableCountWord_valid
      row column formula)
    hmoment]
  simp only [List.replicate_succ]

/-- GapCVP reduction support. -/
noncomputable def physicalOrdinaryNodePrefixWidth
    (moment : SourcePhysicalLagrangeWordComputer) :
    SourceQaryMaskDynamicGridWidth where
  output := physicalOrdinaryNodePrefixWord moment
  computer := paperVariableArityPhysicalOrdinaryNodePrefixWordComputable moment

/-- GapCVP reduction support. -/
def physicalShiftedNodePrefixWord
    (moment : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  true :: fourFamilyComputedUnaryProductOutput
    physicalInterpolationShiftedVariableCountWord
    moment.output input

private noncomputable def paperVariableArityPhysicalShiftedNodePrefixWordComputable
    (moment : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalShiftedNodePrefixWord moment) :=
  GapCVP.TMComposition.computableInPolyTime
    (fourFamilyComputedUnaryProductComputable
      paperVariableArityPhysicalInterpolationShiftedVariableCountWordComputable
      moment.computer)
    (GapCVP.SourceMachineCert.prependBitComputable
      true)

theorem paperVariableArityPhysicalShiftedNodePrefixWord_valid
    (moment : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF) (momentRank : ℕ)
    (hmoment : moment.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
        List.replicate momentRank true) :
    physicalShiftedNodePrefixWord moment
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        ((physicalFormulaVariableCount formula - 1) *
          momentRank + 1) true := by
  unfold physicalShiftedNodePrefixWord
  rw [fourFamilyComputedUnaryProductOutput_valid
    physicalInterpolationShiftedVariableCountWord
    moment.output
    (affineCellQuery row column (encodeThreeCNF formula))
    (physicalFormulaVariableCount formula - 1)
    momentRank
    (paperVariableArityPhysicalInterpolationShiftedVariableCountWord_valid
      row column formula)
    hmoment]
  simp only [List.replicate_succ]

/-- GapCVP reduction support. -/
noncomputable def physicalShiftedNodePrefixWidth
    (moment : SourcePhysicalLagrangeWordComputer) :
    SourceQaryMaskDynamicGridWidth where
  output := physicalShiftedNodePrefixWord moment
  computer := paperVariableArityPhysicalShiftedNodePrefixWordComputable moment

/-- GapCVP reduction support. -/
def physicalInterpolationNodeParity
    (width : SourceQaryMaskDynamicGridWidth)
    {term : List Bool → List Bool}
    (computer : BitTM term) : List Bool → List Bool :=
  compactPhysicalNodeParity width computer

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalInterpolationNodeParityComputable
    (width : SourceQaryMaskDynamicGridWidth)
    {term : List Bool → List Bool}
    (computer : BitTM term) :
    BitTM
      (physicalInterpolationNodeParity width computer) :=
  compactPhysicalNodeParityComputable width computer

theorem paperVariableArityPhysicalInterpolationNodeParity_valid
    (width : SourceQaryMaskDynamicGridWidth)
    {term : List Bool → List Bool}
    (computer : BitTM term)
    (input : List Bool) (count : ℕ) (value : ℕ → Bool)
    (hwidth : width.output input = List.replicate count true)
    (hterm : ∀ rank ∈ List.range count,
      term (lengthPrefixedWord (List.replicate rank true) ++
        sourceQaryMaskDynamicGridBaseSource width input) =
          [value rank]) :
    physicalInterpolationNodeParity
      width computer input =
      [((List.range count).map value).foldl Bool.xor false] := by
  exact compactPhysicalNodeParity_valid width computer input count value
    hwidth hterm

end PhysicalOrdinaryShiftedCoefficientSumTM

namespace BinaryCompactPhysicalLagrangeNestedNodeTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalWordRuntimeDegreeTM

/-- GapCVP reduction support. -/
def compactPhysicalLagrangeNestedNodeEnvelope
    (width : SourceQaryMaskDynamicGridWidth)
    (rank : ℕ) (source : List Bool) : List Bool :=
  lengthPrefixedWord (List.replicate rank true) ++
    sourceQaryMaskDynamicGridBaseSource width source

/-- GapCVP reduction support. -/
def compactPhysicalLagrangeNestedNodeRank : List Bool → List Bool :=
  firstFieldContents

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalLagrangeNestedNodeRankComputable :
    BitTM
      compactPhysicalLagrangeNestedNodeRank :=
  firstFieldContentsComputable

/-- GapCVP reduction support. -/
def compactPhysicalLagrangeNestedNodeOuterCell : List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalLagrangeNestedNodeOuterCellComputable :
    BitTM
      compactPhysicalLagrangeNestedNodeOuterCell :=
  factor400BinaryPhysicalWordRuntimeCompositionComputer
    firstFieldSuffixComputable firstFieldSuffixComputable

@[simp] theorem compactPhysicalLagrangeNestedNodeRank_query
    (width : SourceQaryMaskDynamicGridWidth)
    (rank : ℕ) (source : List Bool) :
    compactPhysicalLagrangeNestedNodeRank
        (compactPhysicalLagrangeNestedNodeEnvelope
          width rank source) =
      List.replicate rank true := by
  simp only [compactPhysicalLagrangeNestedNodeRank, compactPhysicalLagrangeNestedNodeEnvelope,
      firstFieldContents_valid]

@[simp] theorem compactPhysicalLagrangeNestedNodeOuterCell_query
    (width : SourceQaryMaskDynamicGridWidth)
    (rank : ℕ) (source : List Bool) :
    compactPhysicalLagrangeNestedNodeOuterCell
        (compactPhysicalLagrangeNestedNodeEnvelope
          width rank source) = source := by
  simp only [compactPhysicalLagrangeNestedNodeOuterCell, compactPhysicalLagrangeNestedNodeEnvelope,
      sourceQaryMaskDynamicGridBaseSource, Function.comp_apply, firstFieldSuffix_valid]

/-- GapCVP reduction support. -/
def compactPhysicalLagrangeNestedNodeOriginalSource :
    List Bool → List Bool :=
  sourceExplicitAffineCellOriginalSource ∘
    compactPhysicalLagrangeNestedNodeOuterCell

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalLagrangeNestedNodeOriginalSourceComputable :
    BitTM
      compactPhysicalLagrangeNestedNodeOriginalSource :=
  factor400BinaryPhysicalWordRuntimeCompositionComputer
    compactPhysicalLagrangeNestedNodeOuterCellComputable
    factor400BinaryPhysicalWordCellOriginalSourceComputer

@[simp] theorem compactPhysicalLagrangeNestedNodeOriginalSource_query
    (width : SourceQaryMaskDynamicGridWidth)
    (node row column : ℕ) (formula : ThreeCNF) :
    compactPhysicalLagrangeNestedNodeOriginalSource
        (compactPhysicalLagrangeNestedNodeEnvelope width node
          (affineCellQuery row column
            (encodeThreeCNF formula))) =
      encodeThreeCNF formula := by
  simp only [compactPhysicalLagrangeNestedNodeOriginalSource, Function.comp_apply,
      compactPhysicalLagrangeNestedNodeOuterCell_query,
          sourceExplicitAffineCellOriginalSource_query]

/-- GapCVP reduction support. -/
def compactPhysicalLagrangeNestedOtherActualCell :
    List Bool → List Bool :=
  compactPhysicalLagrangeNestedNodeOuterCell ∘
    compactPhysicalLagrangeNestedNodeOuterCell

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalLagrangeNestedOtherActualCellComputable :
    BitTM
      compactPhysicalLagrangeNestedOtherActualCell :=
  factor400BinaryPhysicalWordRuntimeCompositionComputer
    compactPhysicalLagrangeNestedNodeOuterCellComputable
    compactPhysicalLagrangeNestedNodeOuterCellComputable

@[simp] theorem compactPhysicalLagrangeNestedOtherActualCell_query
    (innerWidth outerWidth : SourceQaryMaskDynamicGridWidth)
    (other node : ℕ) (cell : List Bool) :
    compactPhysicalLagrangeNestedOtherActualCell
        (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
          (compactPhysicalLagrangeNestedNodeEnvelope
            outerWidth node cell)) = cell := by
  simp only [compactPhysicalLagrangeNestedOtherActualCell, Function.comp_apply,
      compactPhysicalLagrangeNestedNodeOuterCell_query]

/-- GapCVP reduction support. -/
def compactPhysicalLagrangeNestedOtherOriginalSource :
    List Bool → List Bool :=
  sourceExplicitAffineCellOriginalSource ∘
    compactPhysicalLagrangeNestedOtherActualCell

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalLagrangeNestedOtherOriginalSourceComputable :
    BitTM
      compactPhysicalLagrangeNestedOtherOriginalSource :=
  factor400BinaryPhysicalWordRuntimeCompositionComputer
    compactPhysicalLagrangeNestedOtherActualCellComputable
    factor400BinaryPhysicalWordCellOriginalSourceComputer

@[simp] theorem compactPhysicalLagrangeNestedOtherOriginalSource_query
    (innerWidth outerWidth : SourceQaryMaskDynamicGridWidth)
    (other node row column : ℕ) (formula : ThreeCNF) :
    compactPhysicalLagrangeNestedOtherOriginalSource
        (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
          (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node
            (affineCellQuery row column
              (encodeThreeCNF formula)))) =
      encodeThreeCNF formula := by
  simp only [compactPhysicalLagrangeNestedOtherOriginalSource, Function.comp_apply,
      compactPhysicalLagrangeNestedOtherActualCell_query,
          sourceExplicitAffineCellOriginalSource_query]

/-- GapCVP reduction support. -/
def compactPhysicalLagrangeNestedAnchorRank : List Bool → List Bool :=
  compactPhysicalLagrangeNestedNodeRank ∘
    compactPhysicalLagrangeNestedNodeOuterCell

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalLagrangeNestedAnchorRankComputable :
    BitTM
      compactPhysicalLagrangeNestedAnchorRank :=
  factor400BinaryPhysicalWordRuntimeCompositionComputer
    compactPhysicalLagrangeNestedNodeOuterCellComputable
    compactPhysicalLagrangeNestedNodeRankComputable

@[simp] theorem compactPhysicalLagrangeNestedAnchorRank_query
    (innerWidth outerWidth : SourceQaryMaskDynamicGridWidth)
    (other node : ℕ) (cell : List Bool) :
    compactPhysicalLagrangeNestedAnchorRank
        (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
          (compactPhysicalLagrangeNestedNodeEnvelope
            outerWidth node cell)) =
      List.replicate node true := by
  simp only [compactPhysicalLagrangeNestedAnchorRank, Function.comp_apply,
      compactPhysicalLagrangeNestedNodeOuterCell_query,
          compactPhysicalLagrangeNestedNodeRank_query]

/-- GapCVP reduction support. -/
noncomputable def compactPhysicalLagrangeNestedNodeSourceWordComputer :
    SourcePhysicalLagrangeWordComputer where
  output := compactPhysicalLagrangeNestedNodeOriginalSource
  computer := compactPhysicalLagrangeNestedNodeOriginalSourceComputable

/-- GapCVP reduction support. -/
noncomputable def compactPhysicalLagrangeNestedOtherSourceWordComputer :
    SourcePhysicalLagrangeWordComputer where
  output := compactPhysicalLagrangeNestedOtherOriginalSource
  computer := compactPhysicalLagrangeNestedOtherOriginalSourceComputable

/-- GapCVP reduction support. -/
noncomputable def compactPhysicalLagrangeNestedOtherRankWordComputer :
    SourcePhysicalLagrangeWordComputer where
  output := compactPhysicalLagrangeNestedNodeRank
  computer := compactPhysicalLagrangeNestedNodeRankComputable

/-- GapCVP reduction support. -/
noncomputable def compactPhysicalLagrangeNestedAnchorRankWordComputer :
    SourcePhysicalLagrangeWordComputer where
  output := compactPhysicalLagrangeNestedAnchorRank
  computer := compactPhysicalLagrangeNestedAnchorRankComputable

end BinaryCompactPhysicalLagrangeNestedNodeTM

namespace BinaryCompactPhysicalLagrangeMomentWeightTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryPhysicalLagrangeProductFoldTM
open GapCVP.BinaryCompactPhysicalLagrangeFactorStreamTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM

private def compactPhysicalLagrangeMomentNodeFactorWord
    (base : SourcePhysicalLagrangeWordComputer) : List Bool → List Bool :=
  base.output ∘ compactPhysicalLagrangeNestedNodeOuterCell

private noncomputable def compactPhysicalLagrangeMomentNodeFactorComputable
    (base : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalLagrangeMomentNodeFactorWord base) :=
  GapCVP.TMComposition.computableInPolyTime
    compactPhysicalLagrangeNestedNodeOuterCellComputable base.computer

private noncomputable def compactPhysicalLagrangeMomentNodeFactorComputer
    (base : SourcePhysicalLagrangeWordComputer) :
    SourcePhysicalLagrangeWordComputer where
  output := compactPhysicalLagrangeMomentNodeFactorWord base
  computer := compactPhysicalLagrangeMomentNodeFactorComputable base

@[simp] private theorem compactPhysicalLagrangeMomentNodeFactorWord_valid
    (base : SourcePhysicalLagrangeWordComputer)
    (width : SourceQaryMaskDynamicGridWidth)
    (rank : ℕ) (input : List Bool) :
    compactPhysicalLagrangeMomentNodeFactorWord base
      (compactPhysicalLagrangeNestedNodeEnvelope width rank input) =
      base.output input := by
  simp only [compactPhysicalLagrangeMomentNodeFactorWord, Function.comp_apply,
      compactPhysicalLagrangeNestedNodeOuterCell_query]

private theorem compactPhysicalLagrangeMomentFactorCatalogue_valid
    {degree : ℕ}
    (width : SourceQaryMaskDynamicGridWidth)
    (base : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) (count : ℕ)
    (value : GapCVP.Core.EffectiveBinaryField.Word degree)
    (hwidth : width.output input = List.replicate count true)
    (hvalue : base.output input = finiteWordBits value) :
    compactPhysicalLagrangeNodeFactorCatalogue width
        (compactPhysicalLagrangeMomentNodeFactorComputer base) input =
      sourcePhysicalLagrangePackedFactorWords
        (List.replicate count value) := by
  rw [compactPhysicalLagrangeNodeFactorCatalogue_valid
    width (compactPhysicalLagrangeMomentNodeFactorComputer base)
    input count hwidth]
  change
    (List.range count).flatMap
      (fun rank => lengthPrefixedWord
        (compactPhysicalLagrangeMomentNodeFactorWord base
          (compactPhysicalLagrangeNodeFactorQuery width input rank))) =
      (List.replicate count value).flatMap
        (fun factor => lengthPrefixedWord (finiteWordBits factor))
  have hfactor (rank : ℕ) :
      compactPhysicalLagrangeMomentNodeFactorWord base
        (compactPhysicalLagrangeNodeFactorQuery width input rank) =
        finiteWordBits value := by
    change
      compactPhysicalLagrangeMomentNodeFactorWord base
        (compactPhysicalLagrangeNestedNodeEnvelope width rank input) = _
    exact
      (compactPhysicalLagrangeMomentNodeFactorWord_valid
        base width rank input).trans hvalue
  simp_rw [hfactor]
  have hflat (amount : ℕ) :
      (List.range amount).flatMap
          (fun _ => lengthPrefixedWord (finiteWordBits value)) =
        (List.replicate amount value).flatMap
          (fun factor => lengthPrefixedWord (finiteWordBits factor)) := by
    induction amount with
    | zero => simp only [List.range_zero, List.flatMap_nil, List.replicate_zero]
    | succ amount ih =>
        simpa only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            List.append_nil,
            List.replicate_succ', List.append_cancel_right_eq] using
            congrArg (fun words => words ++ lengthPrefixedWord (finiteWordBits value)) ih
  exact hflat count

end BinaryCompactPhysicalLagrangeMomentWeightTM

namespace BinaryCompactPhysicalLagrangeNodeProductTM

open Turing GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

/-- GapCVP reduction support. -/
noncomputable def compactPhysicalLagrangeNestedNodePrefixWidth
    (width : SourceQaryMaskDynamicGridWidth) :
    SourceQaryMaskDynamicGridWidth where
  output := width.output ∘ compactPhysicalLagrangeNestedNodeOuterCell
  computer := GapCVP.TMComposition.computableInPolyTime
    compactPhysicalLagrangeNestedNodeOuterCellComputable width.computer

@[simp] theorem compactPhysicalLagrangeNestedNodePrefixWidth_valid
    (inner outer : SourceQaryMaskDynamicGridWidth)
    (node : ℕ) (cell : List Bool) :
    (compactPhysicalLagrangeNestedNodePrefixWidth inner).output
        (compactPhysicalLagrangeNestedNodeEnvelope outer node cell) =
      inner.output cell := by
  simp only [compactPhysicalLagrangeNestedNodePrefixWidth, Function.comp_apply,
      compactPhysicalLagrangeNestedNodeOuterCell_query]

end BinaryCompactPhysicalLagrangeNodeProductTM

namespace BinaryCompactPhysicalLagrangeMomentWeightTM

open Turing GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryFieldBasis
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalLagrangeFactorStreamTM

theorem compactPhysicalLagrangeIndexedOneWord
    (degree : ℕ) (hdegree : 0 < degree) :
    indexedWord degree
      ⟨1, Nat.one_lt_two_pow (Nat.ne_of_gt hdegree)⟩ =
      oneWord degree := by
  funext bit
  cases bit with
  | mk index hindex =>
      cases index with
      | zero => simp only [indexedWord, Nat.testBit, Nat.shiftRight_zero, Nat.and_self,
          Nat.reduceBNe, oneWord, decide_true]
      | succ index =>
          have hpower : 1 < 2 ^ (index + 1) :=
            Nat.one_lt_two_pow (Nat.succ_ne_zero index)
          simp only [indexedWord, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hpower,
              Nat.and_zero,
              bne_self_eq_false, oneWord, Nat.add_eq_zero_iff, one_ne_zero, and_false,
                  decide_false]

private theorem compactPhysicalLagrangeRepeatedMomentProduct
    {degree : ℕ}
    (value : GapCVP.Core.EffectiveBinaryField.Word degree)
    (count : ℕ) :
    (List.replicate count value).foldl
        (GapCVP.Core.EffectiveBinaryField.multiplyMod
          (GapCVP.Core.EffectiveBinaryField.irreducibleWord degree))
        (oneWord degree) =
      sourceWordPow value count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ', List.foldl_append, ih]
      rfl

private theorem compactPhysicalLagrangeMomentFactorProductWord_valid
    {degree : ℕ}
    (width : SourceQaryMaskDynamicGridWidth)
    (lower initial original base : SourcePhysicalLagrangeWordComputer)
    (input source : List Bool) (count : ℕ)
    (lowerWord initialWord value :
      GapCVP.Core.EffectiveBinaryField.Word degree)
    (hwidth : width.output input = List.replicate count true)
    (hlower : lower.output input = finiteWordBits lowerWord)
    (hinitial : initial.output input = finiteWordBits initialWord)
    (hsource : original.output input = source)
    (hvalue : base.output input = finiteWordBits value) :
    compactPhysicalLagrangeFactorProductWord
        width lower initial original
        (compactPhysicalLagrangeMomentNodeFactorComputer base) input =
      finiteWordBits
        ((List.replicate count value).foldl
          (GapCVP.Core.EffectiveBinaryField.multiplyMod lowerWord)
          initialWord) := by
  have hcount :
      width.output input =
        List.replicate (List.replicate count value).length true := by
    rw [List.length_replicate]
    exact hwidth
  have hcatalogue := compactPhysicalLagrangeMomentFactorCatalogue_valid
    width base input count value hwidth hvalue
  exact compactPhysicalLagrangeFactorProductWord_valid
    width lower initial original
    (compactPhysicalLagrangeMomentNodeFactorComputer base)
    input lowerWord initialWord (List.replicate count value) source
    hcount hlower hinitial hsource hcatalogue

end BinaryCompactPhysicalLagrangeMomentWeightTM

namespace SourceFieldMomentOperationsTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryDimensionTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.BinaryCompactPhysicalLagrangeFactorStreamTM
open GapCVP.BinaryCompactPhysicalLagrangeMomentWeightTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.PhysicalRefinementRowProjection
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine

/-- GapCVP reduction support. -/
def physicalFamilyStart
    (family : Fin 4) (formula : ThreeCNF) : ℕ :=
  if family.val = 0 then 0
  else if family.val = 1 then
    physicalFormulaGlobalBoundary formula
  else if family.val = 2 then
    physicalFormulaRefinementBoundary formula
  else physicalFormulaOrdinaryBoundary formula

private def physicalFamilyStartUnary
    (family : Fin 4) : List Bool → List Bool :=
  if family.val = 0 then fun _ => []
  else if family.val = 1 then
    physicalCellGlobalBoundaryUnary
  else if family.val = 2 then
    physicalCellRefinementBoundaryUnary
  else physicalCellOrdinaryBoundaryUnary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalFamilyStartUnaryComputable
    (family : Fin 4) :
    BitTM
      (physicalFamilyStartUnary family) := by
  unfold physicalFamilyStartUnary
  split
  · exact sourceFixedWordComputable []
  next =>
    split
    · exact paperVariableArityPhysicalCellGlobalBoundaryUnaryComputable
    next =>
      split
      · exact paperVariableArityPhysicalCellRefinementBoundaryUnaryComputable
      · exact paperVariableArityPhysicalCellOrdinaryBoundaryUnaryComputable

@[simp] private theorem paperVariableArityPhysicalFamilyStartUnary_valid
    (family : Fin 4) (row column : ℕ) (formula : ThreeCNF) :
    physicalFamilyStartUnary family
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalFamilyStart family formula) true := by
  by_cases hzero : family.val = 0
  · simp only [physicalFamilyStartUnary, hzero, ↓reduceIte, physicalFamilyStart,
      List.replicate_zero]
  · by_cases hone : family.val = 1
    · simp only [physicalFamilyStartUnary, hone, one_ne_zero, ↓reduceIte,
          paperVariableArityPhysicalCellGlobalBoundaryUnary_query, physicalFamilyStart]
    · by_cases htwo : family.val = 2
      · simp only [physicalFamilyStartUnary, htwo, OfNat.ofNat_ne_zero, ↓reduceIte,
          OfNat.ofNat_ne_one,
            paperVariableArityPhysicalCellRefinementBoundaryUnary_query, physicalFamilyStart]
      · simp only [physicalFamilyStartUnary, hzero, ↓reduceIte, hone, htwo,
            paperVariableArityPhysicalCellOrdinaryBoundaryUnary_query, physicalFamilyStart]

private def physicalMomentCellDegreeUnary :
    List Bool → List Bool :=
  physicalCellSourceLift
    physicalFamilyFieldDegreeUnary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalMomentCellDegreeUnaryComputable :
    BitTM
      physicalMomentCellDegreeUnary :=
  physicalCellSourceLiftComputable
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable

@[simp] private theorem paperVariableArityPhysicalMomentCellDegreeUnary_valid
    (row column : ℕ) (formula : ThreeCNF) :
    physicalMomentCellDegreeUnary
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physDegree formula) true := by
  unfold physicalMomentCellDegreeUnary
  rw [paperVariableArityPhysicalCellSourceLift_query,
    paperVariableArityPhysicalFamilyFieldDegreeUnary_valid]

/-- GapCVP reduction support. -/
def physicalMomentCellGridCardinalityUnary :
    List Bool → List Bool :=
  physicalCellSourceLift
    physicalFamilyGridCardinalityUnary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalMomentCellGridCardinalityUnaryComputable :
    BitTM
      physicalMomentCellGridCardinalityUnary :=
  physicalCellSourceLiftComputable
    paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable

@[simp] theorem paperVariableArityPhysicalMomentCellGridCardinalityUnary_valid
    (row column : ℕ) (formula : ThreeCNF) :
    physicalMomentCellGridCardinalityUnary
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physGridCard formula) true := by
  unfold physicalMomentCellGridCardinalityUnary
  rw [paperVariableArityPhysicalCellSourceLift_query,
    paperVariableArityPhysicalFamilyGridCardinalityUnary_valid]

/-- GapCVP reduction support. -/
def physicalMomentCellMomentCountUnary :
    List Bool → List Bool :=
  physicalCellSourceLift
    physicalFamilyMomentCountUnary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalMomentCellMomentCountUnaryComputable :
    BitTM
      physicalMomentCellMomentCountUnary :=
  physicalCellSourceLiftComputable
    paperVariableArityPhysicalFamilyMomentCountUnaryComputable

@[simp] theorem paperVariableArityPhysicalMomentCellMomentCountUnary_valid
    (row column : ℕ) (formula : ThreeCNF) :
    physicalMomentCellMomentCountUnary
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalFormulaMomentCount formula) true := by
  unfold physicalMomentCellMomentCountUnary
  rw [paperVariableArityPhysicalCellSourceLift_query,
    paperVariableArityPhysicalFamilyMomentCountUnary_valid]

private def physicalFamilyRowLocalOffsetWord
    (family : Fin 4) : List Bool → List Bool :=
  unarySubtractionOutput sourceExplicitAffineCellRow
    (physicalFamilyStartUnary family)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalFamilyRowLocalOffsetComputable
    (family : Fin 4) :
    BitTM
      (physicalFamilyRowLocalOffsetWord family) :=
  unarySubtractionComputable sourceExplicitAffineCellRowComputable
    (paperVariableArityPhysicalFamilyStartUnaryComputable family)

@[simp] private theorem paperVariableArityPhysicalFamilyRowLocalOffsetWord_valid
    (family : Fin 4) (row column : ℕ) (formula : ThreeCNF) :
    physicalFamilyRowLocalOffsetWord family
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (row - physicalFamilyStart family formula) true :=
  unarySubtractionOutput_valid sourceExplicitAffineCellRow
    (physicalFamilyStartUnary family)
    (affineCellQuery row column
      (encodeThreeCNF formula))
    row (physicalFamilyStart family formula)
    (sourceExplicitAffineCellRow_query row column
      (encodeThreeCNF formula))
    (paperVariableArityPhysicalFamilyStartUnary_valid
      family row column formula)

/-- GapCVP reduction support. -/
def physicalFamilyRowFieldRankWord
    (family : Fin 4) : List Bool → List Bool :=
  sourcePhysicalComputedUnaryQuotient
    (physicalFamilyRowLocalOffsetWord family)
    physicalMomentCellDegreeUnary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalFamilyRowFieldRankComputable
    (family : Fin 4) :
    BitTM
      (physicalFamilyRowFieldRankWord family) :=
  sourcePhysicalComputedUnaryQuotientComputable
    (paperVariableArityPhysicalFamilyRowLocalOffsetComputable family)
    paperVariableArityPhysicalMomentCellDegreeUnaryComputable

@[simp] theorem paperVariableArityPhysicalFamilyRowFieldRankWord_valid
    (family : Fin 4) (row column : ℕ) (formula : ThreeCNF) :
    physicalFamilyRowFieldRankWord family
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        ((row - physicalFamilyStart family formula) /
          physDegree formula) true :=
  sourcePhysicalComputedUnaryQuotient_valid
    (physicalFamilyRowLocalOffsetWord family)
    physicalMomentCellDegreeUnary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    (row - physicalFamilyStart family formula)
    (physDegree formula)
    (physicalRefinementDegree_pos formula)
    (paperVariableArityPhysicalFamilyRowLocalOffsetWord_valid
      family row column formula)
    (paperVariableArityPhysicalMomentCellDegreeUnary_valid
      row column formula)

/-- GapCVP reduction support. -/
def physicalFamilyRowGridQuotientWord
    (family : Fin 4) : List Bool → List Bool :=
  sourcePhysicalComputedUnaryQuotient
    (physicalFamilyRowFieldRankWord family)
    physicalMomentCellGridCardinalityUnary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalFamilyRowGridQuotientComputable
    (family : Fin 4) :
    BitTM
      (physicalFamilyRowGridQuotientWord family) :=
  sourcePhysicalComputedUnaryQuotientComputable
    (paperVariableArityPhysicalFamilyRowFieldRankComputable family)
    paperVariableArityPhysicalMomentCellGridCardinalityUnaryComputable

@[simp] theorem paperVariableArityPhysicalFamilyRowGridQuotientWord_valid
    (family : Fin 4) (row column : ℕ) (formula : ThreeCNF) :
    physicalFamilyRowGridQuotientWord family
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (((row - physicalFamilyStart family formula) /
          physDegree formula) /
          physGridCard formula) true :=
  sourcePhysicalComputedUnaryQuotient_valid
    (physicalFamilyRowFieldRankWord family)
    physicalMomentCellGridCardinalityUnary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    ((row - physicalFamilyStart family formula) /
      physDegree formula)
    (physGridCard formula)
    (physicalRefinementGridCard_pos formula)
    (paperVariableArityPhysicalFamilyRowFieldRankWord_valid
      family row column formula)
    (paperVariableArityPhysicalMomentCellGridCardinalityUnary_valid
      row column formula)

/-- GapCVP reduction support. -/
def physicalFamilyRowMoment
    (family : Fin 4) (row : ℕ) (formula : ThreeCNF) : ℕ :=
  (((row - physicalFamilyStart family formula) /
    physDegree formula) /
    physGridCard formula) %
    physicalFormulaMomentCount formula

theorem physicalFormulaMomentCount_pos
    (formula : ThreeCNF) :
    0 < physicalFormulaMomentCount formula := by
  change 0 < physicalFormulaSize formula ^ 30 + 1
  omega

/-- GapCVP reduction support. -/
def physicalFamilyRowMomentRankWord
    (family : Fin 4) : List Bool → List Bool :=
  sourcePhysicalComputedUnaryRemainder
    (physicalFamilyRowGridQuotientWord family)
    physicalMomentCellMomentCountUnary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalFamilyRowMomentRankComputable
    (family : Fin 4) :
    BitTM
      (physicalFamilyRowMomentRankWord family) :=
  sourcePhysicalComputedUnaryRemainderComputable
    (paperVariableArityPhysicalFamilyRowGridQuotientComputable family)
    paperVariableArityPhysicalMomentCellMomentCountUnaryComputable

/-- GapCVP reduction support. -/
noncomputable def physicalFamilyRowMomentRankComputer
    (family : Fin 4) : SourcePhysicalLagrangeWordComputer where
  output := physicalFamilyRowMomentRankWord family
  computer := paperVariableArityPhysicalFamilyRowMomentRankComputable family

@[simp] theorem paperVariableArityPhysicalFamilyRowMomentRankWord_valid
    (family : Fin 4) (row column : ℕ) (formula : ThreeCNF) :
    physicalFamilyRowMomentRankWord family
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalFamilyRowMoment family row formula) true :=
  sourcePhysicalComputedUnaryRemainder_valid
    (physicalFamilyRowGridQuotientWord family)
    physicalMomentCellMomentCountUnary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    (((row - physicalFamilyStart family formula) /
      physDegree formula) /
      physGridCard formula)
    (physicalFormulaMomentCount formula)
    (physicalFormulaMomentCount_pos formula)
    (paperVariableArityPhysicalFamilyRowGridQuotientWord_valid
      family row column formula)
    (paperVariableArityPhysicalMomentCellMomentCountUnary_valid
      row column formula)

private noncomputable def physicalFamilyRowMomentWidth
    (family : Fin 4) : SourceQaryMaskDynamicGridWidth where
  output := physicalFamilyRowMomentRankWord family
  computer := paperVariableArityPhysicalFamilyRowMomentRankComputable family

private theorem paperVariableArityPhysicalFamilyRowMomentWidth_output
    (family : Fin 4) :
    (physicalFamilyRowMomentWidth family).output =
      physicalFamilyRowMomentRankWord family := by
  dsimp only [physicalFamilyRowMomentWidth]

@[simp] private theorem paperVariableArityPhysicalFamilyRowMomentWidth_valid
    (family : Fin 4) (row column : ℕ) (formula : ThreeCNF) :
    (physicalFamilyRowMomentWidth family).output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalFamilyRowMoment family row formula) true := by
  rw [paperVariableArityPhysicalFamilyRowMomentWidth_output]
  exact paperVariableArityPhysicalFamilyRowMomentRankWord_valid
    family row column formula

private noncomputable def paperVariableArityPhysicalMomentUnitRankComputer :
    SourcePhysicalLagrangeWordComputer where
  output := fun _ => [true]
  computer := sourceFixedWordComputable [true]

private def physicalMomentUnitWord : List Bool → List Bool :=
  physicalCellFieldWordAt
    paperVariableArityPhysicalMomentUnitRankComputer

private noncomputable def paperVariableArityPhysicalMomentUnitWordComputable :
    BitTM
      physicalMomentUnitWord :=
  physicalCellFieldWordAtComputable
    paperVariableArityPhysicalMomentUnitRankComputer

private noncomputable def paperVariableArityPhysicalMomentUnitComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalMomentUnitWord
  computer := paperVariableArityPhysicalMomentUnitWordComputable

@[simp] private theorem paperVariableArityPhysicalMomentUnitWord_valid
    (row column : ℕ) (formula : ThreeCNF) :
    physicalMomentUnitWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      finiteWordBits
        (oneWord
          (sourceIrreducibleFormulaDegree formula)) := by
  have hdegree :
      0 < sourceIrreducibleFormulaDegree formula :=
    sourceFieldExponent_pos
      (sourceSizeParameter_ge_one_hundred
        (encodeThreeCNF formula).length
        (srcFormula formula))
  let index : Fin
      (2 ^ sourceIrreducibleFormulaDegree formula) :=
    ⟨1, Nat.one_lt_two_pow (Nat.ne_of_gt hdegree)⟩
  have hword := physicalCellFieldWordAt_valid
    paperVariableArityPhysicalMomentUnitRankComputer
    row column formula index (by rfl)
  unfold physicalMomentUnitWord
  rw [hword]
  congr 1
  exact compactPhysicalLagrangeIndexedOneWord
    (sourceIrreducibleFormulaDegree formula) hdegree

private noncomputable def physicalMomentOriginalSourceComputer :
    SourcePhysicalLagrangeWordComputer :=
  compactPhysicalLagrangeOriginalSourceComputer

@[simp] private theorem paperVariableArityPhysicalMomentOriginalSourceComputer_valid
    (row column : ℕ) (formula : ThreeCNF) :
    physicalMomentOriginalSourceComputer.output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      encodeThreeCNF formula := by
  exact sourceExplicitAffineCellOriginalSource_query
    row column (encodeThreeCNF formula)

/-- GapCVP reduction support. -/
def physicalFamilyMomentPowerWord
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  compactPhysicalLagrangeFactorProductWord
    (physicalFamilyRowMomentWidth family)
    physicalCellSelectedModulusComputer
    paperVariableArityPhysicalMomentUnitComputer
    physicalMomentOriginalSourceComputer
    (compactPhysicalLagrangeMomentNodeFactorComputer base)

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalFamilyMomentPowerComputable
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalFamilyMomentPowerWord family base) :=
  compactPhysicalLagrangeFactorProductComputable
    (physicalFamilyRowMomentWidth family)
    physicalCellSelectedModulusComputer
    paperVariableArityPhysicalMomentUnitComputer
    physicalMomentOriginalSourceComputer
    (compactPhysicalLagrangeMomentNodeFactorComputer base)

/-- GapCVP reduction support. -/
noncomputable def physicalFamilyMomentPowerComputer
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer) :
    SourcePhysicalLagrangeWordComputer where
  output := physicalFamilyMomentPowerWord family base
  computer := paperVariableArityPhysicalFamilyMomentPowerComputable
    family base

theorem paperVariableArityPhysicalFamilyMomentPowerWord_valid
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (sourceIrreducibleFormulaDegree formula))
    (hvalue : base.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits value) :
    physicalFamilyMomentPowerWord family base
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      finiteWordBits
        (sourceWordPow value
          (physicalFamilyRowMoment family row formula)) := by
  unfold physicalFamilyMomentPowerWord
  rw [← compactPhysicalLagrangeRepeatedMomentProduct]
  apply compactPhysicalLagrangeMomentFactorProductWord_valid
    (physicalFamilyRowMomentWidth family)
    physicalCellSelectedModulusComputer
    paperVariableArityPhysicalMomentUnitComputer
    physicalMomentOriginalSourceComputer base
    (affineCellQuery row column
      (encodeThreeCNF formula))
    (encodeThreeCNF formula)
    (physicalFamilyRowMoment family row formula)
    (irreducibleWord
      (sourceIrreducibleFormulaDegree formula))
    (oneWord
      (sourceIrreducibleFormulaDegree formula)) value
  · exact paperVariableArityPhysicalFamilyRowMomentWidth_valid
      family row column formula
  · exact paperVariableArityPhysicalCellSelectedModulusWord_valid
      row column formula
  · exact paperVariableArityPhysicalMomentUnitWord_valid
      row column formula
  · exact paperVariableArityPhysicalMomentOriginalSourceComputer_valid
      row column formula
  · exact hvalue

end SourceFieldMomentOperationsTM


end GapCVP

end
