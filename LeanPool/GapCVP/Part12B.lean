/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part12A

/-! # GapCVP proof, part 12, continuation 02 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace FourFamilySoundness

open scoped BigOperators

open GapCVP.FormulaBridge GapCVP.Factor400BinaryConstructiveSourcePlaces

open GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryExplicitFourFamilyKernel

open GapCVP.BinaryExplicitSourceSoundness GapCVP.Factor400BinaryCodeDecodingCorollary

open GapCVP.Factor400BinaryDecodingPromiseReduction

end FourFamilySoundness

namespace SourcePreprocessingTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.SourceOriginalSourcePreservingTM
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceIndexedClauseLookupTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
open GapCVP.SourceNormalizedVariableRankScanTM GapCVP.CNFGuardedFiveFamilyTagDispatchTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CLStructuralNaturalBinaryWriter GapCVP.BinaryDimensionTM

/-- GapCVP reduction support. -/
def paperSourcePreprocessingSuffixAt (index : ℕ) :
    List Bool → List Bool :=
  (firstFieldSuffix^[index])

/-- GapCVP reduction support. -/
noncomputable def paperPreprocessingSuffixAtComputable
    (index : ℕ) :
    BitTM
      (paperSourcePreprocessingSuffixAt index) := by
  induction index with
  | zero =>
      exact Turing.idComputableInPolyTime bitEncoding
  | succ index ih =>
      have physical := GapCVP.TMComposition.computableInPolyTime
        firstFieldSuffixComputable ih
      change BitTM
        (firstFieldSuffix^[index + 1])
      simpa only [Function.iterate_succ, Function.comp_def, paperSourcePreprocessingSuffixAt]
          using physical

/-- GapCVP reduction support. -/
def paperSourcePreprocessingField (index : ℕ) :
    List Bool → List Bool :=
  firstFieldContents ∘ paperSourcePreprocessingSuffixAt index

/-- GapCVP reduction support. -/
noncomputable def paperPreprocessingFieldComputable
    (index : ℕ) :
    BitTM
      (paperSourcePreprocessingField index) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperPreprocessingSuffixAtComputable index)
    firstFieldContentsComputable

private def paperSourceClauseLiteralSuffixAt (index : ℕ) :
    List Bool → List Bool :=
  (literalSuffix^[index])

private noncomputable def paperSourceClauseLiteralSuffixAtComputable
    (index : ℕ) :
    BitTM
      (paperSourceClauseLiteralSuffixAt index) := by
  induction index with
  | zero =>
      exact Turing.idComputableInPolyTime bitEncoding
  | succ index ih =>
      have physical := GapCVP.TMComposition.computableInPolyTime
        literalSuffixComputable ih
      change BitTM
        (literalSuffix^[index + 1])
      simpa only [Function.iterate_succ, Function.comp_def, paperSourceClauseLiteralSuffixAt]
          using physical

/-- Internal support shared across GapCVP continuation modules. -/
def paperSourceClauseLiteralWord (position : Fin 3) :
    List Bool → List Bool :=
  sourceOriginalIndexedPhysicalLiteralOutput ∘
    paperSourceClauseLiteralSuffixAt position.val

private noncomputable def paperClauseLiteralWordComputable
    (position : Fin 3) :
    BitTM
      (paperSourceClauseLiteralWord position) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperSourceClauseLiteralSuffixAtComputable position.val)
    sourceOriginalIndexedPhysicalLiteralComputable

/-- GapCVP reduction support. -/
def paperSourceClauseVariableWord (position : Fin 3) :
    List Bool → List Bool :=
  firstFieldContents ∘ paperSourceClauseLiteralSuffixAt position.val

/-- GapCVP reduction support. -/
noncomputable def paperSourceClauseVariableWordComputable
    (position : Fin 3) :
    BitTM
      (paperSourceClauseVariableWord position) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperSourceClauseLiteralSuffixAtComputable position.val)
    firstFieldContentsComputable

/-- GapCVP reduction support. -/
def paperSourceClauseSignWord (position : Fin 3) :
    List Bool → List Bool :=
  sourceOriginalIndexedLiteralSignOutput ∘
    paperSourceClauseLiteralSuffixAt position.val

/-- GapCVP reduction support. -/
noncomputable def paperSourceClauseSignWordComputable
    (position : Fin 3) :
    BitTM
      (paperSourceClauseSignWord position) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperSourceClauseLiteralSuffixAtComputable position.val)
    sourceOriginalIndexedLiteralSignComputable

private def paperSourceClauseVariableEquality
    (first second : Fin 3) : List Bool → List Bool :=
  maskComputedWordEquality
    (paperSourceClauseVariableWord first)
    (paperSourceClauseVariableWord second)

private noncomputable def paperSourceClauseVariableEqualityComputable
    (first second : Fin 3) :
    BitTM
      (paperSourceClauseVariableEquality first second) :=
  maskComputedWordEqualityComputable
    (paperSourceClauseVariableWordComputable first)
    (paperSourceClauseVariableWordComputable second)

private def paperSourceClauseSignEquality
    (first second : Fin 3) : List Bool → List Bool :=
  maskComputedWordEquality
    (paperSourceClauseSignWord first)
    (paperSourceClauseSignWord second)

private noncomputable def paperSourceClauseSignEqualityComputable
    (first second : Fin 3) :
    BitTM
      (paperSourceClauseSignEquality first second) :=
  maskComputedWordEqualityComputable
    (paperSourceClauseSignWordComputable first)
    (paperSourceClauseSignWordComputable second)

private def paperSourceClauseOppositePair
    (first second : Fin 3) : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    (paperSourceClauseVariableEquality first second)
    (sourceFourFamilyBooleanNotOutput
      (paperSourceClauseSignEquality first second))

private noncomputable def paperSourceClauseOppositePairComputable
    (first second : Fin 3) :
    BitTM
      (paperSourceClauseOppositePair first second) :=
  fourFamilyBooleanAndComputable
    (paperSourceClauseVariableEqualityComputable first second)
    (fourFamilyBooleanNotOutputComputable
      (paperSourceClauseSignEqualityComputable first second))

private def paperSourceMarkerOr
    (first second : List Bool → List Bool) :
    List Bool → List Bool :=
  sourceFourFamilyBooleanOrOutput first second

private noncomputable def paperSourceMarkerOrComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (paperSourceMarkerOr first second) :=
  sourceFourFamilyBooleanOrComputable hfirst hsecond

private def paperSourceClauseTautologyMarker : List Bool → List Bool :=
  paperSourceMarkerOr (paperSourceClauseOppositePair 0 1)
    (paperSourceMarkerOr (paperSourceClauseOppositePair 0 2)
      (paperSourceClauseOppositePair 1 2))

private noncomputable def paperSourceClauseTautologyMarkerComputable :
    BitTM
      paperSourceClauseTautologyMarker :=
  paperSourceMarkerOrComputable
    (paperSourceClauseOppositePairComputable 0 1)
    (paperSourceMarkerOrComputable
      (paperSourceClauseOppositePairComputable 0 2)
      (paperSourceClauseOppositePairComputable 1 2))

private def paperSourceClauseLiteralEquality
    (first second : Fin 3) : List Bool → List Bool :=
  maskComputedWordEquality
    (paperSourceClauseLiteralWord first)
    (paperSourceClauseLiteralWord second)

private noncomputable def paperSourceClauseLiteralEqualityComputable
    (first second : Fin 3) :
    BitTM
      (paperSourceClauseLiteralEquality first second) :=
  maskComputedWordEqualityComputable
    (paperClauseLiteralWordComputable first)
    (paperClauseLiteralWordComputable second)

/-- GapCVP reduction support. -/
def paperSourceClauseSecondKeepMarker : List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    (paperSourceClauseLiteralEquality 0 1)

/-- GapCVP reduction support. -/
noncomputable def paperSourceClauseSecondKeepMarkerComputable :
    BitTM
      paperSourceClauseSecondKeepMarker :=
  fourFamilyBooleanNotOutputComputable
    (paperSourceClauseLiteralEqualityComputable 0 1)

/-- Internal support shared across GapCVP continuation modules. -/
def paperSourceClauseThirdKeepMarker : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    (sourceFourFamilyBooleanNotOutput
      (paperSourceClauseLiteralEquality 0 2))
    (sourceFourFamilyBooleanNotOutput
      (paperSourceClauseLiteralEquality 1 2))

private noncomputable def paperSourceClauseThirdKeepMarkerComputable :
    BitTM
      paperSourceClauseThirdKeepMarker :=
  fourFamilyBooleanAndComputable
    (fourFamilyBooleanNotOutputComputable
      (paperSourceClauseLiteralEqualityComputable 0 2))
    (fourFamilyBooleanNotOutputComputable
      (paperSourceClauseLiteralEqualityComputable 1 2))

private def paperSourcePhysicalMarkerSelection
    (marker : List Bool → List Bool) (input : List Bool) : List Bool :=
  (marker input).headD false :: input

private noncomputable def paperPhysicalMarkerSelectionComputable
    {marker : List Bool → List Bool}
    (computer : BitTM marker)
    (shape : ∀ input, ∃ bit : Bool, marker input = [bit]) :
    BitTM
      (paperSourcePhysicalMarkerSelection marker) := by
  have preserved := originalSourcePreservingComputable computer
  have physical := GapCVP.TMComposition.computableInPolyTime
    preserved keepFirstDropSecondComputable
  have equality :
      (fun input : List Bool =>
        keepFirstDropSecondWord (originalSourcePreservingOutput marker input)) =
          paperSourcePhysicalMarkerSelection marker := by
    funext input
    obtain ⟨bit, hbit⟩ := shape input
    simp only [keepFirstDropSecondWord, originalSourcePreservingOutput, hbit, List.cons_append,
        List.nil_append,
        List.tail_cons, paperSourcePhysicalMarkerSelection, List.headD_eq_head?_getD,
            List.head?_cons, Option.getD_some]
  rw [← equality]
  exact physical

private theorem paperSourceClauseLiteralEquality_shape
    (first second : Fin 3) (input : List Bool) :
    ∃ bit : Bool,
      paperSourceClauseLiteralEquality first second input = [bit] := by
  refine ⟨decide
    (paperSourceClauseLiteralWord first input =
      paperSourceClauseLiteralWord second input), ?_⟩
  simp only [paperSourceClauseLiteralEquality, sourceQaryMaskSquareComputedWordEquality_valid]

private theorem paperSourceClauseVariableEquality_shape
    (first second : Fin 3) (input : List Bool) :
    ∃ bit : Bool,
      paperSourceClauseVariableEquality first second input = [bit] := by
  refine ⟨decide
    (paperSourceClauseVariableWord first input =
      paperSourceClauseVariableWord second input), ?_⟩
  simp only [paperSourceClauseVariableEquality, sourceQaryMaskSquareComputedWordEquality_valid]

private theorem paperSourceClauseSignEquality_shape
    (first second : Fin 3) (input : List Bool) :
    ∃ bit : Bool,
      paperSourceClauseSignEquality first second input = [bit] := by
  refine ⟨decide
    (paperSourceClauseSignWord first input =
      paperSourceClauseSignWord second input), ?_⟩
  simp only [paperSourceClauseSignEquality, sourceQaryMaskSquareComputedWordEquality_valid]

private theorem paperSourceBooleanNot_shape
    (marker : List Bool → List Bool)
    (shape : ∀ input, ∃ bit : Bool, marker input = [bit])
    (input : List Bool) :
    ∃ bit : Bool,
      sourceFourFamilyBooleanNotOutput marker input = [bit] := by
  obtain ⟨bit, hbit⟩ := shape input
  refine ⟨!bit, ?_⟩
  exact fourFamilyBooleanNotOutput_bit marker input bit hbit

private theorem paperSourceBooleanAnd_shape
    (first second : List Bool → List Bool)
    (hfirst : ∀ input, ∃ bit : Bool, first input = [bit])
    (hsecond : ∀ input, ∃ bit : Bool, second input = [bit])
    (input : List Bool) :
    ∃ bit : Bool,
      sourceFourFamilyBooleanAndOutput first second input = [bit] := by
  obtain ⟨left, hleft⟩ := hfirst input
  obtain ⟨right, hright⟩ := hsecond input
  refine ⟨left && right, ?_⟩
  exact fourFamilyBooleanAndOutput_bits
    first second input left right hleft hright

private theorem paperSourceMarkerOr_shape
    (first second : List Bool → List Bool)
    (hfirst : ∀ input, ∃ bit : Bool, first input = [bit])
    (hsecond : ∀ input, ∃ bit : Bool, second input = [bit])
    (input : List Bool) :
    ∃ bit : Bool, paperSourceMarkerOr first second input = [bit] := by
  unfold paperSourceMarkerOr
  apply paperSourceBooleanNot_shape
  exact paperSourceBooleanAnd_shape _ _
    (paperSourceBooleanNot_shape first hfirst)
    (paperSourceBooleanNot_shape second hsecond)

private theorem paperSourceClauseOppositePair_shape
    (first second : Fin 3) (input : List Bool) :
    ∃ bit : Bool, paperSourceClauseOppositePair first second input = [bit] := by
  unfold paperSourceClauseOppositePair
  exact paperSourceBooleanAnd_shape _ _
    (paperSourceClauseVariableEquality_shape first second)
    (paperSourceBooleanNot_shape _
      (paperSourceClauseSignEquality_shape first second)) input

private theorem paperSourceClauseTautologyMarker_shape
    (input : List Bool) :
    ∃ bit : Bool, paperSourceClauseTautologyMarker input = [bit] := by
  unfold paperSourceClauseTautologyMarker
  exact paperSourceMarkerOr_shape _ _
    (paperSourceClauseOppositePair_shape 0 1)
    (paperSourceMarkerOr_shape _ _
      (paperSourceClauseOppositePair_shape 0 2)
      (paperSourceClauseOppositePair_shape 1 2)) input

private theorem paperSourceClauseSecondKeepMarker_shape
    (input : List Bool) :
    ∃ bit : Bool, paperSourceClauseSecondKeepMarker input = [bit] := by
  exact paperSourceBooleanNot_shape _
    (paperSourceClauseLiteralEquality_shape 0 1) input

private theorem paperSourceClauseThirdKeepMarker_shape
    (input : List Bool) :
    ∃ bit : Bool, paperSourceClauseThirdKeepMarker input = [bit] := by
  unfold paperSourceClauseThirdKeepMarker
  exact paperSourceBooleanAnd_shape _ _
    (paperSourceBooleanNot_shape _
      (paperSourceClauseLiteralEquality_shape 0 2))
    (paperSourceBooleanNot_shape _
      (paperSourceClauseLiteralEquality_shape 1 2)) input

/-- Internal support shared across GapCVP continuation modules. -/
def paperClauseSelectedSecondLiteral
    (input : List Bool) : List Bool :=
  if (paperSourceClauseSecondKeepMarker input).headD false then
    paperSourceClauseLiteralWord 1 input
  else []

private noncomputable def paperSourceClauseSelectedSecondLiteralComputable :
    BitTM
      paperClauseSelectedSecondLiteral := by
  exact sourcePreservingConditionalComputable
    (paperPhysicalMarkerSelectionComputable
      paperSourceClauseSecondKeepMarkerComputable
      paperSourceClauseSecondKeepMarker_shape)
    (paperClauseLiteralWordComputable 1) []

/-- Internal support shared across GapCVP continuation modules. -/
def paperClauseSelectedThirdLiteral
    (input : List Bool) : List Bool :=
  if (paperSourceClauseThirdKeepMarker input).headD false then
    paperSourceClauseLiteralWord 2 input
  else []

private noncomputable def paperSourceClauseSelectedThirdLiteralComputable :
    BitTM
      paperClauseSelectedThirdLiteral := by
  exact sourcePreservingConditionalComputable
    (paperPhysicalMarkerSelectionComputable
      paperSourceClauseThirdKeepMarkerComputable
      paperSourceClauseThirdKeepMarker_shape)
    (paperClauseLiteralWordComputable 2) []

/-- Internal support shared across GapCVP continuation modules. -/
def paperSourceClauseSecondKeepUnary
    (input : List Bool) : List Bool :=
  if (paperSourceClauseSecondKeepMarker input).headD false then [true] else []

private noncomputable def paperSourceClauseSecondKeepUnaryComputable :
    BitTM
      paperSourceClauseSecondKeepUnary := by
  exact sourcePreservingConditionalComputable
    (paperPhysicalMarkerSelectionComputable
      paperSourceClauseSecondKeepMarkerComputable
      paperSourceClauseSecondKeepMarker_shape)
    (sourceFixedWordComputable [true]) []

/-- Internal support shared across GapCVP continuation modules. -/
def paperSourceClauseThirdKeepUnary
    (input : List Bool) : List Bool :=
  if (paperSourceClauseThirdKeepMarker input).headD false then [true] else []

private noncomputable def paperSourceClauseThirdKeepUnaryComputable :
    BitTM
      paperSourceClauseThirdKeepUnary := by
  exact sourcePreservingConditionalComputable
    (paperPhysicalMarkerSelectionComputable
      paperSourceClauseThirdKeepMarkerComputable
      paperSourceClauseThirdKeepMarker_shape)
    (sourceFixedWordComputable [true]) []

/-- Internal support shared across GapCVP continuation modules. -/
def paperSourceClauseNormalizedRecord
    (input : List Bool) : List Bool :=
  true ::
    (paperSourceClauseSecondKeepUnary input ++
    (paperSourceClauseThirdKeepUnary input ++
    (false ::
      (paperSourceClauseLiteralWord 0 input ++
      (paperClauseSelectedSecondLiteral input ++
        paperClauseSelectedThirdLiteral input)))))

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def paperSourceClauseNormalizedRecordComputable :
    BitTM
      paperSourceClauseNormalizedRecord := by
  have literals := pointwiseAppendComputable
    (paperClauseLiteralWordComputable 0)
    (pointwiseAppendComputable
      paperSourceClauseSelectedSecondLiteralComputable
      paperSourceClauseSelectedThirdLiteralComputable)
  have stopped := GapCVP.TMComposition.computableInPolyTime
    literals (prependBitComputable false)
  have fields := pointwiseAppendComputable
    paperSourceClauseSecondKeepUnaryComputable
    (pointwiseAppendComputable
      paperSourceClauseThirdKeepUnaryComputable stopped)
  exact GapCVP.TMComposition.computableInPolyTime
    fields (prependBitComputable true)

private def paperSourceClauseOriginalRecord : List Bool → List Bool :=
  sourceOriginalIndexedPhysicalThreeClauseOutput

private noncomputable def paperSourceClauseOriginalRecordComputable :
    BitTM
      paperSourceClauseOriginalRecord :=
  sourceOriginalIndexedPhysicalThreeClauseComputable

private def paperSourceClauseRetainMarker : List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput paperSourceClauseTautologyMarker

private noncomputable def paperSourceClauseRetainMarkerComputable :
    BitTM
      paperSourceClauseRetainMarker :=
  fourFamilyBooleanNotOutputComputable
    paperSourceClauseTautologyMarkerComputable

private theorem paperSourceClauseRetainMarker_shape (input : List Bool) :
    ∃ bit : Bool, paperSourceClauseRetainMarker input = [bit] := by
  exact paperSourceBooleanNot_shape _
    paperSourceClauseTautologyMarker_shape input

private def paperSourceRetainedOriginalClause
    (input : List Bool) : List Bool :=
  if (paperSourceClauseRetainMarker input).headD false then
    paperSourceClauseOriginalRecord input
  else []

private noncomputable def paperSourceRetainedOriginalClauseComputable :
    BitTM
      paperSourceRetainedOriginalClause := by
  exact sourcePreservingConditionalComputable
    (paperPhysicalMarkerSelectionComputable
      paperSourceClauseRetainMarkerComputable
      paperSourceClauseRetainMarker_shape)
    paperSourceClauseOriginalRecordComputable []

private def paperSourceRetainedNormalizedClause
    (input : List Bool) : List Bool :=
  if (paperSourceClauseRetainMarker input).headD false then
    paperSourceClauseNormalizedRecord input
  else []

private noncomputable def paperSourceRetainedNormalizedClauseComputable :
    BitTM
      paperSourceRetainedNormalizedClause := by
  exact sourcePreservingConditionalComputable
    (paperPhysicalMarkerSelectionComputable
      paperSourceClauseRetainMarkerComputable
      paperSourceClauseRetainMarker_shape)
    paperSourceClauseNormalizedRecordComputable []

private def paperSourceRetainedClauseUnary
    (input : List Bool) : List Bool :=
  if (paperSourceClauseRetainMarker input).headD false then [true] else []

private noncomputable def paperSourceRetainedClauseUnaryComputable :
    BitTM
      paperSourceRetainedClauseUnary := by
  exact sourcePreservingConditionalComputable
    (paperPhysicalMarkerSelectionComputable
      paperSourceClauseRetainMarkerComputable
      paperSourceClauseRetainMarker_shape)
    (sourceFixedWordComputable [true]) []

private def paperSourcePreprocessingCurrent
    (worker : List Bool → List Bool) : List Bool → List Bool :=
  worker ∘ paperSourcePreprocessingField 3

private noncomputable def paperSourcePreprocessingCurrentComputable
    {worker : List Bool → List Bool}
    (computer : BitTM worker) :
    BitTM
      (paperSourcePreprocessingCurrent worker) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperPreprocessingFieldComputable 3) computer

private def paperPreprocessingNextOriginalBody
    (input : List Bool) : List Bool :=
  paperSourcePreprocessingField 0 input ++
    paperSourcePreprocessingCurrent paperSourceRetainedOriginalClause input

private noncomputable def paperSourcePreprocessingNextOriginalBodyComputable :
    BitTM
      paperPreprocessingNextOriginalBody :=
  pointwiseAppendComputable
    (paperPreprocessingFieldComputable 0)
    (paperSourcePreprocessingCurrentComputable
      paperSourceRetainedOriginalClauseComputable)

private def paperPreprocessingNextNormalizedBody
    (input : List Bool) : List Bool :=
  paperSourcePreprocessingField 1 input ++
    paperSourcePreprocessingCurrent paperSourceRetainedNormalizedClause input

private noncomputable def paperSourcePreprocessingNextNormalizedBodyComputable :
    BitTM
      paperPreprocessingNextNormalizedBody :=
  pointwiseAppendComputable
    (paperPreprocessingFieldComputable 1)
    (paperSourcePreprocessingCurrentComputable
      paperSourceRetainedNormalizedClauseComputable)

private def paperPreprocessingNextClauseCount
    (input : List Bool) : List Bool :=
  paperSourcePreprocessingField 2 input ++
    paperSourcePreprocessingCurrent paperSourceRetainedClauseUnary input

private noncomputable def paperSourcePreprocessingNextClauseCountComputable :
    BitTM
      paperPreprocessingNextClauseCount :=
  pointwiseAppendComputable
    (paperPreprocessingFieldComputable 2)
    (paperSourcePreprocessingCurrentComputable
      paperSourceRetainedClauseUnaryComputable)

private def paperSourcePreprocessingNextPending : List Bool → List Bool :=
  clauseSuffix ∘ paperSourcePreprocessingField 3

private noncomputable def paperSourcePreprocessingNextPendingComputable :
    BitTM
      paperSourcePreprocessingNextPending :=
  GapCVP.TMComposition.computableInPolyTime
    (paperPreprocessingFieldComputable 3)
    clauseSuffixComputable

private def paperSourcePreprocessingOriginal : List Bool → List Bool :=
  paperSourcePreprocessingSuffixAt 5

private noncomputable def paperSourcePreprocessingOriginalComputable :
    BitTM
      paperSourcePreprocessingOriginal :=
  paperPreprocessingSuffixAtComputable 5

private def paperSourcePreprocessingStep (input : List Bool) : List Bool :=
  lengthPrefixedWord (paperPreprocessingNextOriginalBody input) ++
    (lengthPrefixedWord (paperPreprocessingNextNormalizedBody input) ++
    (lengthPrefixedWord (paperPreprocessingNextClauseCount input) ++
    (lengthPrefixedWord (paperSourcePreprocessingNextPending input) ++
    (lengthPrefixedWord (paperSourcePreprocessingField 4 input) ++
      paperSourcePreprocessingOriginal input))))

private noncomputable def paperSourcePreprocessingStepComputable :
    BitTM
      paperSourcePreprocessingStep := by
  have originalBody := GapCVP.TMComposition.computableInPolyTime
    paperSourcePreprocessingNextOriginalBodyComputable
    structuralPrefixWriterComputable
  have normalizedBody := GapCVP.TMComposition.computableInPolyTime
    paperSourcePreprocessingNextNormalizedBodyComputable
    structuralPrefixWriterComputable
  have count := GapCVP.TMComposition.computableInPolyTime
    paperSourcePreprocessingNextClauseCountComputable
    structuralPrefixWriterComputable
  have pending := GapCVP.TMComposition.computableInPolyTime
    paperSourcePreprocessingNextPendingComputable
    structuralPrefixWriterComputable
  have archive := GapCVP.TMComposition.computableInPolyTime
    (paperPreprocessingFieldComputable 4)
    structuralPrefixWriterComputable
  exact pointwiseAppendComputable originalBody
    (pointwiseAppendComputable normalizedBody
      (pointwiseAppendComputable count
        (pointwiseAppendComputable pending
          (pointwiseAppendComputable archive
            paperSourcePreprocessingOriginalComputable))))

/-- Internal support shared across GapCVP continuation modules. -/
def paperSourcePreprocessingValidState
    (formula : ThreeCNF)
    (originalBody normalizedBody : List Bool)
    (retainedCount : ℕ) (pending : ThreeCNF) : List Bool :=
  lengthPrefixedWord originalBody ++
    (lengthPrefixedWord normalizedBody ++
    (lengthPrefixedWord (List.replicate retainedCount true) ++
    (lengthPrefixedWord (pending.flatMap encodeThreeClause) ++
    (lengthPrefixedWord (formula.flatMap encodeThreeClause) ++
      encodeThreeCNF formula))))

@[simp] private theorem paperSourcePreprocessingField_valid_zero
    (formula : ThreeCNF) (originalBody normalizedBody : List Bool)
    (retainedCount : ℕ) (pending : ThreeCNF) :
    paperSourcePreprocessingField 0
      (paperSourcePreprocessingValidState
        formula originalBody normalizedBody retainedCount pending) =
      originalBody := by
  simp only [paperSourcePreprocessingField, paperSourcePreprocessingSuffixAt,
      Function.iterate_zero,
      paperSourcePreprocessingValidState, Function.comp_apply, id_eq, firstFieldContents_valid]

@[simp] private theorem paperSourcePreprocessingField_valid_one
    (formula : ThreeCNF) (originalBody normalizedBody : List Bool)
    (retainedCount : ℕ) (pending : ThreeCNF) :
    paperSourcePreprocessingField 1
      (paperSourcePreprocessingValidState
        formula originalBody normalizedBody retainedCount pending) =
      normalizedBody := by
  simp only [paperSourcePreprocessingField, paperSourcePreprocessingSuffixAt, Function.iterate_one,
      paperSourcePreprocessingValidState, Function.comp_apply, firstFieldSuffix_valid,
          firstFieldContents_valid]

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem paperSourcePreprocessingField_valid_two
    (formula : ThreeCNF) (originalBody normalizedBody : List Bool)
    (retainedCount : ℕ) (pending : ThreeCNF) :
    paperSourcePreprocessingField 2
      (paperSourcePreprocessingValidState
        formula originalBody normalizedBody retainedCount pending) =
      List.replicate retainedCount true := by
  simp [paperSourcePreprocessingField,
    paperSourcePreprocessingSuffixAt,
    paperSourcePreprocessingValidState, Function.comp_apply]

@[simp] private theorem paperSourcePreprocessingField_valid_three
    (formula : ThreeCNF) (originalBody normalizedBody : List Bool)
    (retainedCount : ℕ) (pending : ThreeCNF) :
    paperSourcePreprocessingField 3
      (paperSourcePreprocessingValidState
        formula originalBody normalizedBody retainedCount pending) =
      pending.flatMap encodeThreeClause := by
  simp [paperSourcePreprocessingField,
    paperSourcePreprocessingSuffixAt,
    paperSourcePreprocessingValidState, Function.comp_apply]

@[simp] private theorem paperSourcePreprocessingField_valid_four
    (formula : ThreeCNF) (originalBody normalizedBody : List Bool)
    (retainedCount : ℕ) (pending : ThreeCNF) :
    paperSourcePreprocessingField 4
      (paperSourcePreprocessingValidState
        formula originalBody normalizedBody retainedCount pending) =
      formula.flatMap encodeThreeClause := by
  simp [paperSourcePreprocessingField,
    paperSourcePreprocessingSuffixAt,
    paperSourcePreprocessingValidState, Function.comp_apply]

@[simp] private theorem paperSourcePreprocessingOriginal_valid
    (formula : ThreeCNF) (originalBody normalizedBody : List Bool)
    (retainedCount : ℕ) (pending : ThreeCNF) :
    paperSourcePreprocessingOriginal
      (paperSourcePreprocessingValidState
        formula originalBody normalizedBody retainedCount pending) =
      encodeThreeCNF formula := by
  simp [paperSourcePreprocessingOriginal,
    paperSourcePreprocessingSuffixAt,
    paperSourcePreprocessingValidState, Function.comp_apply]

private theorem paperSourcePreprocessingFieldAccounting
    (input : List Bool) :
    2 * (paperSourcePreprocessingField 0 input).length +
    2 * (paperSourcePreprocessingField 1 input).length +
    2 * (paperSourcePreprocessingField 2 input).length +
    2 * (paperSourcePreprocessingField 3 input).length +
    2 * (paperSourcePreprocessingField 4 input).length +
    (paperSourcePreprocessingOriginal input).length ≤ input.length := by
  have first := sourceNormalizedVariableScanStructuralFieldAccounting input
  have second := sourceNormalizedVariableScanStructuralFieldAccounting
    (firstFieldSuffix input)
  have third := sourceNormalizedVariableScanStructuralFieldAccounting
    (firstFieldSuffix (firstFieldSuffix input))
  have fourth := sourceNormalizedVariableScanStructuralFieldAccounting
    (firstFieldSuffix (firstFieldSuffix (firstFieldSuffix input)))
  have fifth := sourceNormalizedVariableScanStructuralFieldAccounting
    (firstFieldSuffix
      (firstFieldSuffix (firstFieldSuffix (firstFieldSuffix input))))
  simp only [paperSourcePreprocessingField, paperSourcePreprocessingSuffixAt,
      Function.iterate_zero,
    Function.comp_apply, id_eq, Function.iterate_succ, paperSourcePreprocessingOriginal, ge_iff_le]
        at *
  omega

private theorem paperSourcePreprocessingPending_length_le
    (input : List Bool) :
    (paperSourcePreprocessingField 3 input).length ≤ input.length := by
  have accounting := paperSourcePreprocessingFieldAccounting input
  omega

@[simp] private theorem paperSourcePreprocessingField_three_step
    (input : List Bool) :
    paperSourcePreprocessingField 3
      (paperSourcePreprocessingStep input) =
        clauseSuffix (paperSourcePreprocessingField 3 input) := by
  simp [paperSourcePreprocessingField,
    paperSourcePreprocessingSuffixAt,
    paperSourcePreprocessingStep,
    paperSourcePreprocessingNextPending,
    Function.comp_apply]

private theorem paperSourcePreprocessingPending_step_length_le
    (input : List Bool) :
    (paperSourcePreprocessingField 3
      (paperSourcePreprocessingStep input)).length ≤
        (paperSourcePreprocessingField 3 input).length := by
  rw [paperSourcePreprocessingField_three_step]
  exact sourceOriginalIndexedClauseSuffix_length_le _

private theorem paperSourcePreprocessingPending_iterate_length_le
    (seed : List Bool) (stage : ℕ) :
    (paperSourcePreprocessingField 3
      ((paperSourcePreprocessingStep^[stage]) seed)).length ≤
        (paperSourcePreprocessingField 3 seed).length := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      exact (paperSourcePreprocessingPending_step_length_le _).trans ih

private theorem paperSourceClauseLiteralSuffixAt_length_le
    (position : ℕ) (input : List Bool) :
    (paperSourceClauseLiteralSuffixAt position input).length ≤
      input.length := by
  induction position with
  | zero => simp only [paperSourceClauseLiteralSuffixAt, Function.iterate_zero, id_eq, Std.le_refl]
  | succ position ih =>
      simp only [paperSourceClauseLiteralSuffixAt,
        Function.iterate_succ_apply']
      exact (sourceOriginalIndexedLiteralSuffix_length_le _).trans ih

private theorem paperSourceOriginalLiteralSign_length
    (input : List Bool) :
    (sourceOriginalIndexedLiteralSignOutput input).length = 1 := by
  unfold sourceOriginalIndexedLiteralSignOutput
  cases hfield : firstFieldSuffix input with
  | nil => simp only [markerConditionalOutput, List.length_cons, List.length_nil, zero_add]
  | cons bit remaining =>
      cases bit <;> simp [markerConditionalOutput]

private theorem paperClauseLiteralWord_length_le
    (position : Fin 3) (input : List Bool) :
    (paperSourceClauseLiteralWord position input).length ≤
      input.length + 2 := by
  have skipped := paperSourceClauseLiteralSuffixAt_length_le
    position.val input
  have accounting := sourceNormalizedVariableScanStructuralFieldAccounting
    (paperSourceClauseLiteralSuffixAt position.val input)
  have sign := paperSourceOriginalLiteralSign_length
    (paperSourceClauseLiteralSuffixAt position.val input)
  change
    (sourceOriginalIndexedPhysicalLiteralOutput
      (paperSourceClauseLiteralSuffixAt position.val input)).length ≤
        input.length + 2
  simp only [sourceOriginalIndexedPhysicalLiteralOutput,
    sourceOriginalIndexedLiteralVariableOutput,
    List.length_append, lengthPrefixedWord_length]
  omega

private theorem paperSourceClauseOriginalRecord_length_le
    (input : List Bool) :
    (paperSourceClauseOriginalRecord input).length ≤
      3 * input.length + 6 := by
  have first :
      (sourceOriginalIndexedPhysicalLiteralOutput input).length ≤
        input.length + 2 := by
    simpa [paperSourceClauseLiteralWord,
      paperSourceClauseLiteralSuffixAt, Function.comp_apply] using
      paperClauseLiteralWord_length_le 0 input
  have second :
      (sourceOriginalIndexedPhysicalLiteralOutput
        (literalSuffix input)).length ≤ input.length + 2 := by
    simpa [paperSourceClauseLiteralWord,
      paperSourceClauseLiteralSuffixAt, Function.comp_apply] using
      paperClauseLiteralWord_length_le 1 input
  have third :
      (sourceOriginalIndexedPhysicalLiteralOutput
        (literalSuffix (literalSuffix input))).length ≤
          input.length + 2 := by
    simpa [paperSourceClauseLiteralWord,
      paperSourceClauseLiteralSuffixAt, Function.comp_apply] using
      paperClauseLiteralWord_length_le 2 input
  simp only [paperSourceClauseOriginalRecord,
    sourceOriginalIndexedPhysicalThreeClauseOutput,
    sourceOriginalIndexedSecondLiteralOutput,
    sourceOriginalIndexedThirdLiteralOutput,
    Function.comp_apply, List.length_append]
  omega

private theorem paperSourceClauseSelectedSecondLiteral_length_le
    (input : List Bool) :
    (paperClauseSelectedSecondLiteral input).length ≤
      input.length + 2 := by
  unfold paperClauseSelectedSecondLiteral
  split <;> simp_all [paperClauseLiteralWord_length_le]

private theorem paperSourceClauseSelectedThirdLiteral_length_le
    (input : List Bool) :
    (paperClauseSelectedThirdLiteral input).length ≤
      input.length + 2 := by
  unfold paperClauseSelectedThirdLiteral
  split <;> simp_all [paperClauseLiteralWord_length_le]

private theorem paperSourceClauseSecondKeepUnary_length_le
    (input : List Bool) :
    (paperSourceClauseSecondKeepUnary input).length ≤ 1 := by
  unfold paperSourceClauseSecondKeepUnary
  split <;> simp

private theorem paperSourceClauseThirdKeepUnary_length_le
    (input : List Bool) :
    (paperSourceClauseThirdKeepUnary input).length ≤ 1 := by
  unfold paperSourceClauseThirdKeepUnary
  split <;> simp

/-- Internal support shared across GapCVP continuation modules. -/
theorem paperSourceClauseNormalizedRecord_length_le
    (input : List Bool) :
    (paperSourceClauseNormalizedRecord input).length ≤
      3 * input.length + 10 := by
  have first := paperClauseLiteralWord_length_le 0 input
  have second := paperSourceClauseSelectedSecondLiteral_length_le input
  have third := paperSourceClauseSelectedThirdLiteral_length_le input
  have secondMarker := paperSourceClauseSecondKeepUnary_length_le input
  have thirdMarker := paperSourceClauseThirdKeepUnary_length_le input
  simp only [paperSourceClauseNormalizedRecord,
    List.length_cons, List.length_append]
  omega

private theorem paperSourceRetainedOriginalClause_length_le
    (input : List Bool) :
    (paperSourceRetainedOriginalClause input).length ≤
      3 * input.length + 6 := by
  unfold paperSourceRetainedOriginalClause
  split
  · exact paperSourceClauseOriginalRecord_length_le input
  · simp only [List.length_nil, le_add_iff_nonneg_left, zero_le]

private theorem paperSourceRetainedNormalizedClause_length_le
    (input : List Bool) :
    (paperSourceRetainedNormalizedClause input).length ≤
      3 * input.length + 10 := by
  unfold paperSourceRetainedNormalizedClause
  split
  · exact paperSourceClauseNormalizedRecord_length_le input
  · simp only [List.length_nil, le_add_iff_nonneg_left, zero_le]

private theorem paperSourceRetainedClauseUnary_length_le
    (input : List Bool) :
    (paperSourceRetainedClauseUnary input).length ≤ 1 := by
  unfold paperSourceRetainedClauseUnary
  split <;> simp

private theorem paperSourcePreprocessingStep_length_le
    (input : List Bool) :
    (paperSourcePreprocessingStep input).length ≤
      input.length +
        12 * (paperSourcePreprocessingField 3 input).length + 39 := by
  have accounting := paperSourcePreprocessingFieldAccounting input
  have skipped := sourceOriginalIndexedClauseSuffix_length_le
    (paperSourcePreprocessingField 3 input)
  have original := paperSourceRetainedOriginalClause_length_le
    (paperSourcePreprocessingField 3 input)
  have normalized := paperSourceRetainedNormalizedClause_length_le
    (paperSourcePreprocessingField 3 input)
  have count := paperSourceRetainedClauseUnary_length_le
    (paperSourcePreprocessingField 3 input)
  simp only [paperSourcePreprocessingStep,
    paperPreprocessingNextOriginalBody,
    paperPreprocessingNextNormalizedBody,
    paperPreprocessingNextClauseCount,
    paperSourcePreprocessingCurrent,
    paperSourcePreprocessingNextPending,
    Function.comp_apply, List.length_append,
    lengthPrefixedWord_length]
  omega

private def paperSourcePreprocessingFoldBound : Polynomial ℕ :=
  40 * (Polynomial.X + 1) ^ 2

private theorem paperSourcePreprocessing_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates paperSourcePreprocessingStep
      paperSourcePreprocessingFoldBound := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage hstage
  have seedBound := GapCVP.CNFTypedRecordWorkerTM.parsedUnaryFold_seed_length_le
    input count seed hparse
  have countBound := parsedUnaryFold_count_le_length
    input count seed hparse
  have pendingSeed := paperSourcePreprocessingPending_length_le seed
  have intermediate : ∀ number : ℕ,
      ((paperSourcePreprocessingStep^[number]) seed).length ≤
        seed.length + number * (12 * seed.length + 39) := by
    intro number
    induction number with
    | zero => simp only [Function.iterate_zero, id_eq, zero_mul, add_zero, Std.le_refl]
    | succ number ih =>
        rw [Function.iterate_succ_apply']
        have worker := paperSourcePreprocessingStep_length_le
          ((paperSourcePreprocessingStep^[number]) seed)
        have pending := paperSourcePreprocessingPending_iterate_length_le
          seed number
        simp only [Nat.add_mul, one_mul]
        omega
  have state := intermediate stage
  have stageBound : stage ≤ input.length :=
    Nat.le_trans hstage countBound
  have productBound : stage * seed.length ≤ input.length * input.length :=
    Nat.mul_le_mul stageBound seedBound
  simp only [paperSourcePreprocessingFoldBound,
    Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

private noncomputable def paperSourcePreprocessingFoldComputable :
    BitTM
      (boundedRecordFoldOutput paperSourcePreprocessingStep) :=
  boundedDependentRecordFoldComputable
    paperSourcePreprocessingStepComputable
    paperSourcePreprocessingFoldBound
    paperSourcePreprocessing_polynomiallyBoundedFoldStates

private def paperSourcePreprocessingSeed (input : List Bool) : List Bool :=
  lengthPrefixedWord [] ++
    (lengthPrefixedWord [] ++
    (lengthPrefixedWord [] ++
    (lengthPrefixedWord (firstFieldSuffix input) ++
    (lengthPrefixedWord (firstFieldSuffix input) ++ input))))

private noncomputable def paperSourcePreprocessingSeedComputable :
    BitTM
      paperSourcePreprocessingSeed := by
  have body := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable structuralPrefixWriterComputable
  have preserved := pointwiseAppendComputable body
    (pointwiseAppendComputable body
      (Turing.idComputableInPolyTime bitEncoding))
  have emptyFields := prependWordComputable
    (lengthPrefixedWord [] ++
      (lengthPrefixedWord [] ++ lengthPrefixedWord []))
  have physical := GapCVP.TMComposition.computableInPolyTime
    preserved emptyFields
  change BitTM
    (fun input => lengthPrefixedWord [] ++
      (lengthPrefixedWord [] ++
      (lengthPrefixedWord [] ++
      (lengthPrefixedWord (firstFieldSuffix input) ++
      (lengthPrefixedWord (firstFieldSuffix input) ++ input)))))
  simpa only [List.append_assoc, Function.comp_apply, id_eq, Function.comp_def] using physical

private def paperSourcePreprocessingPreparation
    (input : List Bool) : List Bool :=
  sourceClauseCountUnary input ++ false :: paperSourcePreprocessingSeed input

private noncomputable def paperSourcePreprocessingPreparationComputable :
    BitTM
      paperSourcePreprocessingPreparation := by
  have marked := GapCVP.TMComposition.computableInPolyTime
    paperSourcePreprocessingSeedComputable (prependBitComputable false)
  exact pointwiseAppendComputable
    sourceClauseCountUnaryComputable marked

/-- Internal support shared across GapCVP continuation modules. -/
def paperSourcePreprocessingFinalState : List Bool → List Bool :=
  boundedRecordFoldOutput paperSourcePreprocessingStep ∘
    paperSourcePreprocessingPreparation

private noncomputable def paperSourcePreprocessingFinalStateComputable :
    BitTM
      paperSourcePreprocessingFinalState :=
  GapCVP.TMComposition.computableInPolyTime
    paperSourcePreprocessingPreparationComputable
    paperSourcePreprocessingFoldComputable

/-- Internal support shared across GapCVP continuation modules. -/
def paperSourcePreprocessingFinalField
    (index : ℕ) : List Bool → List Bool :=
  paperSourcePreprocessingField index ∘
    paperSourcePreprocessingFinalState

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def paperPreprocessingFinalFieldComputable
    (index : ℕ) :
    BitTM
      (paperSourcePreprocessingFinalField index) :=
  GapCVP.TMComposition.computableInPolyTime
    paperSourcePreprocessingFinalStateComputable
    (paperPreprocessingFieldComputable index)

private def paperPreprocessingRetainedCountBinary :
    List Bool → List Bool :=
  (fun unary : List Bool => Computability.encodeNat unary.length) ∘
    paperSourcePreprocessingFinalField 2

private noncomputable def paperSourcePreprocessingRetainedCountBinaryComputable :
    BitTM
      paperPreprocessingRetainedCountBinary :=
  GapCVP.TMComposition.computableInPolyTime
    (paperPreprocessingFinalFieldComputable 2)
    structuralNaturalBinaryWriterComputable

/-- GapCVP reduction support. -/
def paperPreprocessingFilteredFormulaWord
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
    (paperPreprocessingRetainedCountBinary input) ++
      paperSourcePreprocessingFinalField 0 input

/-- GapCVP reduction support. -/
noncomputable def paperSourcePreprocessingFilteredFormulaWordComputable :
    BitTM
      paperPreprocessingFilteredFormulaWord := by
  have count := GapCVP.TMComposition.computableInPolyTime
    paperSourcePreprocessingRetainedCountBinaryComputable
    structuralPrefixWriterComputable
  exact pointwiseAppendComputable count
    (paperPreprocessingFinalFieldComputable 0)

private def paperPreprocessingRecoveredOriginal :
    List Bool → List Bool :=
  paperSourcePreprocessingOriginal ∘
    paperSourcePreprocessingFinalState

private noncomputable def paperSourcePreprocessingRecoveredOriginalComputable :
    BitTM
      paperPreprocessingRecoveredOriginal :=
  GapCVP.TMComposition.computableInPolyTime
    paperSourcePreprocessingFinalStateComputable
    paperSourcePreprocessingOriginalComputable

/-- GapCVP reduction support. -/
def paperSourcePreprocessingOutput (input : List Bool) : List Bool :=
  lengthPrefixedWord (paperPreprocessingFilteredFormulaWord input) ++
    (lengthPrefixedWord (paperSourcePreprocessingFinalField 1 input) ++
      paperPreprocessingRecoveredOriginal input)

/-- GapCVP reduction support. -/
noncomputable def paperSourcePreprocessingComputable :
    BitTM
      paperSourcePreprocessingOutput := by
  have filtered := GapCVP.TMComposition.computableInPolyTime
    paperSourcePreprocessingFilteredFormulaWordComputable
    structuralPrefixWriterComputable
  have normalized := GapCVP.TMComposition.computableInPolyTime
    (paperPreprocessingFinalFieldComputable 1)
    structuralPrefixWriterComputable
  exact pointwiseAppendComputable filtered
    (pointwiseAppendComputable normalized
      paperSourcePreprocessingRecoveredOriginalComputable)

end SourcePreprocessingTM

namespace SourcePreprocessingPairwiseIdentity

open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics

private theorem sourceClauseIsTautology_pairwise
    (clause : ThreeClause) :
    sourceClauseIsTautology clause =
      ((decide ((clause 0).1 = (clause 1).1) &&
          !(decide ((clause 0).2 = (clause 1).2))) ||
        ((decide ((clause 0).1 = (clause 2).1) &&
            !(decide ((clause 0).2 = (clause 2).2))) ||
          (decide ((clause 1).1 = (clause 2).1) &&
            !(decide ((clause 1).2 = (clause 2).2))))) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro htautology
    obtain ⟨left, right, hvariable, hsign⟩ :=
      (sourceClauseIsTautology_iff clause).mp htautology
    have hor :
        ((clause 0).1 = (clause 1).1 ∧
            (clause 0).2 ≠ (clause 1).2) ∨
          (((clause 0).1 = (clause 2).1 ∧
              (clause 0).2 ≠ (clause 2).2) ∨
            ((clause 1).1 = (clause 2).1 ∧
              (clause 1).2 ≠ (clause 2).2)) := by
      fin_cases left <;> fin_cases right
      · exact (hsign rfl).elim
      · exact Or.inl ⟨hvariable, hsign⟩
      · exact Or.inr (Or.inl ⟨hvariable, hsign⟩)
      · exact Or.inl ⟨hvariable.symm, Ne.symm hsign⟩
      · exact (hsign rfl).elim
      · exact Or.inr (Or.inr ⟨hvariable, hsign⟩)
      · exact Or.inr (Or.inl ⟨hvariable.symm, Ne.symm hsign⟩)
      · exact Or.inr (Or.inr ⟨hvariable.symm, Ne.symm hsign⟩)
      · exact (hsign rfl).elim
    simpa only [Fin.isValue, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not, ne_eq] using hor
  · intro hpair
    have hor :
        ((clause 0).1 = (clause 1).1 ∧
            (clause 0).2 ≠ (clause 1).2) ∨
          (((clause 0).1 = (clause 2).1 ∧
              (clause 0).2 ≠ (clause 2).2) ∨
            ((clause 1).1 = (clause 2).1 ∧
              (clause 1).2 ≠ (clause 2).2)) := by
      simpa only [Fin.isValue, ne_eq, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          Bool.not_eq_eq_eq_not,
          Bool.not_true, decide_eq_false_iff_not] using hpair
    apply (sourceClauseIsTautology_iff clause).mpr
    rcases hor with hfirst | hsecond | hthird
    · exact ⟨0, 1, hfirst⟩
    · exact ⟨0, 2, hsecond⟩
    · exact ⟨1, 2, hthird⟩

theorem paperSourceEraseDupsThree_pairwise
    (first second third : Literal) :
    [first, second, third].eraseDups =
      first ::
        ((if first = second then [] else [second]) ++
          (if first = third ∨ second = third then [] else [third])) := by
  classical
  by_cases hfirst : first = second
  · subst second
    by_cases hsecond : first = third
    · subst third
      simp only [List.eraseDups_cons, BEq.rfl, Bool.not_true, Bool.false_eq_true,
          not_false_eq_true,
          List.filter_cons_of_neg, List.filter_nil, List.eraseDups_nil, ↓reduceIte, or_self,
              List.append_nil]
    · have hreverse := Ne.symm hsecond
      simp only [List.eraseDups_cons, BEq.rfl, Bool.not_true, Bool.false_eq_true,
          not_false_eq_true,
          List.filter_cons_of_neg, Bool.not_eq_eq_eq_not, beq_eq_false_iff_ne, ne_eq, hreverse,
              List.filter_cons_of_pos,
          List.filter_nil, List.eraseDups_nil, ↓reduceIte, hsecond, or_self, List.nil_append]
  · have hreverseFirst := Ne.symm hfirst
    by_cases hsecond : first = third
    · subst third
      simp only [List.eraseDups_cons, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne,
          ne_eq,
          hreverseFirst, not_false_eq_true, List.filter_cons_of_pos, BEq.rfl, Bool.false_eq_true,
              List.filter_cons_of_neg,
          List.filter_nil, List.eraseDups_nil, hfirst, ↓reduceIte, or_false, List.append_nil]
    · have hreverseSecond := Ne.symm hsecond
      by_cases hthird : second = third
      · subst third
        simp only [List.eraseDups_cons, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne,
            ne_eq,
            hreverseFirst, not_false_eq_true, List.filter_cons_of_pos, List.filter_nil, BEq.rfl,
                Bool.false_eq_true,
            List.filter_cons_of_neg, List.eraseDups_nil, hfirst, ↓reduceIte, or_true,
                List.append_nil]
      · have hreverseThird := Ne.symm hthird
        simp only [List.eraseDups_cons, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne,
            ne_eq,
            hreverseFirst, not_false_eq_true, List.filter_cons_of_pos, hreverseSecond,
                List.filter_nil, hreverseThird,
            List.eraseDups_nil, hfirst, ↓reduceIte, hsecond, hthird, or_self, List.cons_append,
                List.nil_append]

theorem paperSourceNormalizedClause_pairwise
    (clause : ThreeClause) :
    paperSourceNormalizedClause clause =
      clause 0 ::
        ((if clause 0 = clause 1 then [] else [clause 1]) ++
          (if clause 0 = clause 2 ∨ clause 1 = clause 2
            then [] else [clause 2])) := by
  exact paperSourceEraseDupsThree_pairwise
    (clause 0) (clause 1) (clause 2)

private theorem paperSourceNormalizedClauseRecord_pairwise
    (clause : ThreeClause) :
    paperSourceNormalizedClauseRecord clause =
      let literals :=
        clause 0 ::
          ((if clause 0 = clause 1 then [] else [clause 1]) ++
            (if clause 0 = clause 2 ∨ clause 1 = clause 2
              then [] else [clause 2]))
      List.replicate literals.length true ++
        false :: literals.flatMap encodeLiteral := by
  simp only [paperSourceNormalizedClauseRecord,
    paperSourceNormalizedClause_pairwise]

end SourcePreprocessingPairwiseIdentity

namespace SourcePreprocessingTM

open GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceIndexedClauseLookupTM
open GapCVP.SourceIndexedClauseSignTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM GapCVP.BinaryDimensionTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.SourcePreprocessingPairwiseIdentity

@[simp] private theorem paperSourceClauseLiteralWord_valid
    (position : Fin 3) (clause : ThreeClause) (suffix : List Bool) :
    paperSourceClauseLiteralWord position
      (encodeThreeClause clause ++ suffix) =
      encodeLiteral (clause position) := by
  fin_cases position <;>
    simp [paperSourceClauseLiteralWord,
      paperSourceClauseLiteralSuffixAt, encodeThreeClause,
      Function.comp_apply, List.append_assoc,
      literalSuffix_valid,
      sourceOriginalIndexedPhysicalLiteralOutput_valid]

private theorem paperSourceClauseVariableWord_eq_literalField
    (position : Fin 3) (input : List Bool) :
    paperSourceClauseVariableWord position input =
      firstFieldContents (paperSourceClauseLiteralWord position input) := by
  unfold paperSourceClauseVariableWord paperSourceClauseLiteralWord
    sourceOriginalIndexedPhysicalLiteralOutput
    sourceOriginalIndexedLiteralVariableOutput
  simp only [Function.comp_apply, firstFieldContents_valid]

@[simp] theorem paperSourceClauseVariableWord_valid
    (position : Fin 3) (clause : ThreeClause) (suffix : List Bool) :
    paperSourceClauseVariableWord position
      (encodeThreeClause clause ++ suffix) =
      Computability.encodeNat (clause position).1 := by
  rw [paperSourceClauseVariableWord_eq_literalField,
    paperSourceClauseLiteralWord_valid]
  simp only [encodeLiteral, firstFieldContents_valid]

@[simp] theorem paperSourceClauseSignWord_valid
    (position : Fin 3) (clause : ThreeClause) (suffix : List Bool) :
    paperSourceClauseSignWord position
      (encodeThreeClause clause ++ suffix) =
      [(clause position).2] := by
  fin_cases position <;>
    simp [paperSourceClauseSignWord,
      paperSourceClauseLiteralSuffixAt, encodeThreeClause,
      Function.comp_apply, List.append_assoc,
      literalSuffix_valid,
      sourceOriginalIndexedLiteralSignOutput_valid]

@[simp] private theorem paperSourceEncodeNat_eq_iff
    (first second : ℕ) :
    Computability.encodeNat first = Computability.encodeNat second ↔
      first = second := by
  constructor
  · intro heq
    have hdecode := congrArg Computability.decodeNat heq
    simpa only [Computability.decode_encodeNat] using hdecode
  · intro heq
    rw [heq]

@[simp] private theorem paperSourceEncodeLiteral_eq_iff
    (first second : Literal) :
    encodeLiteral first = encodeLiteral second ↔ first = second := by
  constructor
  · intro heq
    have hdecode := congrArg readLiteral heq
    have hfirst : readLiteral (encodeLiteral first) =
        some (first, []) := by
      simpa only [List.append_nil] using readLiteral_append first []
    have hsecond : readLiteral (encodeLiteral second) =
        some (second, []) := by
      simpa only [List.append_nil] using readLiteral_append second []
    rw [hfirst, hsecond] at hdecode
    exact congrArg Prod.fst (Option.some.inj hdecode)
  · intro heq
    rw [heq]

@[simp] private theorem paperSourceClauseVariableEquality_valid
    (first second : Fin 3)
    (clause : ThreeClause) (suffix : List Bool) :
    paperSourceClauseVariableEquality first second
      (encodeThreeClause clause ++ suffix) =
      [decide ((clause first).1 = (clause second).1)] := by
  unfold paperSourceClauseVariableEquality
  rw [sourceQaryMaskSquareComputedWordEquality_valid,
    paperSourceClauseVariableWord_valid,
    paperSourceClauseVariableWord_valid]
  simp only [paperSourceEncodeNat_eq_iff]

@[simp] private theorem paperSourceClauseSignEquality_valid
    (first second : Fin 3)
    (clause : ThreeClause) (suffix : List Bool) :
    paperSourceClauseSignEquality first second
      (encodeThreeClause clause ++ suffix) =
      [decide ((clause first).2 = (clause second).2)] := by
  unfold paperSourceClauseSignEquality
  rw [sourceQaryMaskSquareComputedWordEquality_valid,
    paperSourceClauseSignWord_valid,
    paperSourceClauseSignWord_valid]
  simp only [List.cons.injEq, and_true]

@[simp] private theorem paperSourceClauseLiteralEquality_valid
    (first second : Fin 3)
    (clause : ThreeClause) (suffix : List Bool) :
    paperSourceClauseLiteralEquality first second
      (encodeThreeClause clause ++ suffix) =
      [decide (clause first = clause second)] := by
  unfold paperSourceClauseLiteralEquality
  rw [sourceQaryMaskSquareComputedWordEquality_valid,
    paperSourceClauseLiteralWord_valid,
    paperSourceClauseLiteralWord_valid]
  simp only [paperSourceEncodeLiteral_eq_iff]

private theorem paperSourceMarkerOr_bits
    (first second : List Bool → List Bool)
    (input : List Bool) (firstBit secondBit : Bool)
    (hfirst : first input = [firstBit])
    (hsecond : second input = [secondBit]) :
    paperSourceMarkerOr first second input =
      [firstBit || secondBit] := by
  exact GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM.fourFamilyBooleanOrOutput_bits
    first second input firstBit secondBit hfirst hsecond

@[simp] private theorem paperSourceClauseOppositePair_valid
    (first second : Fin 3)
    (clause : ThreeClause) (suffix : List Bool) :
    paperSourceClauseOppositePair first second
      (encodeThreeClause clause ++ suffix) =
      [decide ((clause first).1 = (clause second).1) &&
        !(decide ((clause first).2 = (clause second).2))] := by
  unfold paperSourceClauseOppositePair
  have hvariable := paperSourceClauseVariableEquality_valid
    first second clause suffix
  have hsign := paperSourceClauseSignEquality_valid
    first second clause suffix
  have hnot := fourFamilyBooleanNotOutput_bit
    (paperSourceClauseSignEquality first second)
    (encodeThreeClause clause ++ suffix)
    (decide ((clause first).2 = (clause second).2)) hsign
  exact fourFamilyBooleanAndOutput_bits
    (paperSourceClauseVariableEquality first second)
    (sourceFourFamilyBooleanNotOutput
      (paperSourceClauseSignEquality first second))
    (encodeThreeClause clause ++ suffix)
    (decide ((clause first).1 = (clause second).1))
    (!(decide ((clause first).2 = (clause second).2)))
    hvariable hnot

@[simp] private theorem paperSourceClauseTautologyMarker_valid
    (clause : ThreeClause) (suffix : List Bool) :
    paperSourceClauseTautologyMarker
      (encodeThreeClause clause ++ suffix) =
      [sourceClauseIsTautology clause] := by
  unfold paperSourceClauseTautologyMarker
  rw [paperSourceMarkerOr_bits
    (paperSourceClauseOppositePair 0 1)
    (paperSourceMarkerOr (paperSourceClauseOppositePair 0 2)
      (paperSourceClauseOppositePair 1 2))
    (encodeThreeClause clause ++ suffix)
    (decide ((clause 0).1 = (clause 1).1) &&
      !(decide ((clause 0).2 = (clause 1).2)))
    ((decide ((clause 0).1 = (clause 2).1) &&
      !(decide ((clause 0).2 = (clause 2).2))) ||
      (decide ((clause 1).1 = (clause 2).1) &&
        !(decide ((clause 1).2 = (clause 2).2))))
    (paperSourceClauseOppositePair_valid 0 1 clause suffix)
    (paperSourceMarkerOr_bits
      (paperSourceClauseOppositePair 0 2)
      (paperSourceClauseOppositePair 1 2)
      (encodeThreeClause clause ++ suffix)
      (decide ((clause 0).1 = (clause 2).1) &&
        !(decide ((clause 0).2 = (clause 2).2)))
      (decide ((clause 1).1 = (clause 2).1) &&
        !(decide ((clause 1).2 = (clause 2).2)))
      (paperSourceClauseOppositePair_valid 0 2 clause suffix)
      (paperSourceClauseOppositePair_valid 1 2 clause suffix))]
  rw [sourceClauseIsTautology_pairwise]

@[simp] private theorem paperSourceClauseRetainMarker_valid
    (clause : ThreeClause) (suffix : List Bool) :
    paperSourceClauseRetainMarker
      (encodeThreeClause clause ++ suffix) =
      [!(sourceClauseIsTautology clause)] := by
  unfold paperSourceClauseRetainMarker
  exact fourFamilyBooleanNotOutput_bit
    paperSourceClauseTautologyMarker
    (encodeThreeClause clause ++ suffix)
    (sourceClauseIsTautology clause)
    (paperSourceClauseTautologyMarker_valid clause suffix)

@[simp] theorem paperSourceClauseSecondKeepMarker_valid
    (clause : ThreeClause) (suffix : List Bool) :
    paperSourceClauseSecondKeepMarker
      (encodeThreeClause clause ++ suffix) =
      [!(decide (clause 0 = clause 1))] := by
  unfold paperSourceClauseSecondKeepMarker
  exact fourFamilyBooleanNotOutput_bit
    (paperSourceClauseLiteralEquality 0 1)
    (encodeThreeClause clause ++ suffix)
    (decide (clause 0 = clause 1))
    (paperSourceClauseLiteralEquality_valid 0 1 clause suffix)

@[simp] private theorem paperSourceClauseThirdKeepMarker_valid
    (clause : ThreeClause) (suffix : List Bool) :
    paperSourceClauseThirdKeepMarker
      (encodeThreeClause clause ++ suffix) =
      [(!(decide (clause 0 = clause 2))) &&
        (!(decide (clause 1 = clause 2)))] := by
  unfold paperSourceClauseThirdKeepMarker
  have hfirst := fourFamilyBooleanNotOutput_bit
    (paperSourceClauseLiteralEquality 0 2)
    (encodeThreeClause clause ++ suffix)
    (decide (clause 0 = clause 2))
    (paperSourceClauseLiteralEquality_valid 0 2 clause suffix)
  have hsecond := fourFamilyBooleanNotOutput_bit
    (paperSourceClauseLiteralEquality 1 2)
    (encodeThreeClause clause ++ suffix)
    (decide (clause 1 = clause 2))
    (paperSourceClauseLiteralEquality_valid 1 2 clause suffix)
  exact fourFamilyBooleanAndOutput_bits
    (sourceFourFamilyBooleanNotOutput
      (paperSourceClauseLiteralEquality 0 2))
    (sourceFourFamilyBooleanNotOutput
      (paperSourceClauseLiteralEquality 1 2))
    (encodeThreeClause clause ++ suffix)
    (!(decide (clause 0 = clause 2)))
    (!(decide (clause 1 = clause 2))) hfirst hsecond

@[simp] private theorem paperSourceClauseOriginalRecord_valid
    (clause : ThreeClause) (suffix : List Bool) :
    paperSourceClauseOriginalRecord
      (encodeThreeClause clause ++ suffix) =
      encodeThreeClause clause := by
  exact sourceOriginalIndexedPhysicalThreeClauseOutput_valid clause suffix

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem paperSourceClauseNormalizedRecord_valid
    (clause : ThreeClause) (suffix : List Bool) :
    paperSourceClauseNormalizedRecord
      (encodeThreeClause clause ++ suffix) =
      paperSourceNormalizedClauseRecord clause := by
  unfold paperSourceClauseNormalizedRecord
    paperSourceClauseSecondKeepUnary
    paperSourceClauseThirdKeepUnary
    paperClauseSelectedSecondLiteral
    paperClauseSelectedThirdLiteral
  rw [paperSourceClauseSecondKeepMarker_valid,
    paperSourceClauseThirdKeepMarker_valid,
    paperSourceClauseLiteralWord_valid,
    paperSourceClauseLiteralWord_valid,
    paperSourceClauseLiteralWord_valid,
    paperSourceNormalizedClauseRecord_pairwise]
  by_cases hfirst : clause 0 = clause 1 <;>
    by_cases hsecond : clause 0 = clause 2 <;>
    by_cases hthird : clause 1 = clause 2 <;>
    simp_all

@[simp] private theorem paperSourceRetainedOriginalClause_valid
    (clause : ThreeClause) (suffix : List Bool) :
    paperSourceRetainedOriginalClause
      (encodeThreeClause clause ++ suffix) =
      if sourceClauseIsTautology clause then []
        else encodeThreeClause clause := by
  unfold paperSourceRetainedOriginalClause
  rw [paperSourceClauseRetainMarker_valid]
  cases htautology : sourceClauseIsTautology clause <;>
    simp_all [paperSourceClauseOriginalRecord_valid]

@[simp] private theorem paperSourceRetainedNormalizedClause_valid
    (clause : ThreeClause) (suffix : List Bool) :
    paperSourceRetainedNormalizedClause
      (encodeThreeClause clause ++ suffix) =
      if sourceClauseIsTautology clause then []
        else paperSourceNormalizedClauseRecord clause := by
  unfold paperSourceRetainedNormalizedClause
  rw [paperSourceClauseRetainMarker_valid]
  cases htautology : sourceClauseIsTautology clause <;>
    simp_all [paperSourceClauseNormalizedRecord_valid]

@[simp] private theorem paperSourceRetainedClauseUnary_valid
    (clause : ThreeClause) (suffix : List Bool) :
    paperSourceRetainedClauseUnary
      (encodeThreeClause clause ++ suffix) =
      if sourceClauseIsTautology clause then [] else [true] := by
  unfold paperSourceRetainedClauseUnary
  rw [paperSourceClauseRetainMarker_valid]
  cases htautology : sourceClauseIsTautology clause <;>
    simp_all

private theorem paperSourcePreprocessingStep_valid_cons
    (formula : ThreeCNF)
    (originalBody normalizedBody : List Bool)
    (retainedCount : ℕ)
    (clause : ThreeClause) (pending : ThreeCNF) :
    paperSourcePreprocessingStep
      (paperSourcePreprocessingValidState
        formula originalBody normalizedBody retainedCount
        (clause :: pending)) =
      if sourceClauseIsTautology clause then
        paperSourcePreprocessingValidState
          formula originalBody normalizedBody retainedCount pending
      else
        paperSourcePreprocessingValidState formula
          (originalBody ++ encodeThreeClause clause)
          (normalizedBody ++ paperSourceNormalizedClauseRecord clause)
          (retainedCount + 1) pending := by
  unfold paperSourcePreprocessingStep
    paperPreprocessingNextOriginalBody
    paperPreprocessingNextNormalizedBody
    paperPreprocessingNextClauseCount
    paperSourcePreprocessingNextPending
    paperSourcePreprocessingCurrent
  simp only [Function.comp_apply,
    paperSourcePreprocessingField_valid_zero,
    paperSourcePreprocessingField_valid_one,
    paperSourcePreprocessingField_valid_two,
    paperSourcePreprocessingField_valid_three,
    paperSourcePreprocessingField_valid_four,
    paperSourcePreprocessingOriginal_valid,
    List.flatMap_cons,
    paperSourceRetainedOriginalClause_valid,
    paperSourceRetainedNormalizedClause_valid,
    paperSourceRetainedClauseUnary_valid,
    clauseSuffix_valid]
  cases htautology : sourceClauseIsTautology clause <;>
    simp_all [paperSourcePreprocessingValidState, List.replicate_succ]

private theorem paperSourcePreprocessingStep_iterate_valid
    (formula : ThreeCNF)
    (originalBody normalizedBody : List Bool)
    (retainedCount : ℕ) (pending : ThreeCNF) :
    ((paperSourcePreprocessingStep^[pending.length])
      (paperSourcePreprocessingValidState
        formula originalBody normalizedBody retainedCount pending)) =
      paperSourcePreprocessingValidState formula
        (originalBody ++
          (noTautClauses pending).flatMap
            encodeThreeClause)
        (normalizedBody ++ paperSourceNormalizedClauseStream pending)
        (retainedCount +
          (noTautClauses pending).length)
        [] := by
  induction pending generalizing originalBody normalizedBody
      retainedCount with
  | nil =>
      simp only [List.length_nil, Function.iterate_zero, id_eq, noTautClauses, List.filter_nil,
          List.flatMap_nil,
          List.append_nil, paperSourceNormalizedClauseStream, add_zero]
  | cons clause remaining ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply,
        paperSourcePreprocessingStep_valid_cons]
      cases htautology : sourceClauseIsTautology clause with
      | false =>
          simp only [Bool.false_eq_true, ite_false]
          rw [ih]
          simp only [noTautClauses, List.append_assoc, paperSourceNormalizedClauseStream,
              Nat.add_assoc, htautology,
              Bool.not_false, List.filter_cons_of_pos, List.flatMap_cons, List.length_cons,
                  Nat.add_comm]
      | true =>
          simp only [ite_true]
          rw [ih]
          simp only [noTautClauses, paperSourceNormalizedClauseStream, htautology, Bool.not_true,
              Bool.false_eq_true,
              not_false_eq_true, List.filter_cons_of_neg]

@[simp] private theorem paperSourcePreprocessingSeed_valid
    (formula : ThreeCNF) :
    paperSourcePreprocessingSeed (encodeThreeCNF formula) =
      paperSourcePreprocessingValidState
        formula [] [] 0 formula := by
  simp only [paperSourcePreprocessingSeed, encodeThreeCNF, firstFieldSuffix_valid,
      paperSourcePreprocessingValidState, List.replicate_zero]

@[simp] private theorem paperSourcePreprocessingPreparation_valid
    (formula : ThreeCNF) :
    paperSourcePreprocessingPreparation (encodeThreeCNF formula) =
      unaryBoundedFoldWord formula.length
        (paperSourcePreprocessingValidState
          formula [] [] 0 formula) := by
  unfold paperSourcePreprocessingPreparation
  rw [sourceClauseCountUnary_valid,
    paperSourcePreprocessingSeed_valid]
  rfl

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem paperSourcePreprocessingFinalState_valid
    (formula : ThreeCNF) :
    paperSourcePreprocessingFinalState (encodeThreeCNF formula) =
      paperSourcePreprocessingValidState formula
        ((noTautClauses formula).flatMap
          encodeThreeClause)
        (paperSourceNormalizedClauseStream formula)
        (noTautClauses formula).length
        [] := by
  unfold paperSourcePreprocessingFinalState
  rw [Function.comp_apply,
    paperSourcePreprocessingPreparation_valid]
  simp only [boundedRecordFoldOutput,
    parseUnaryBoundedFold_word]
  simpa only [List.nil_append, Nat.zero_add] using
    paperSourcePreprocessingStep_iterate_valid formula [] [] 0 formula

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem paperSourcePreprocessingFinalOriginalBody_valid
    (formula : ThreeCNF) :
    paperSourcePreprocessingFinalField 0
      (encodeThreeCNF formula) =
      (noTautClauses formula).flatMap
        encodeThreeClause := by
  unfold paperSourcePreprocessingFinalField
  rw [Function.comp_apply,
    paperSourcePreprocessingFinalState_valid,
    paperSourcePreprocessingField_valid_zero]

@[simp] private theorem paperSourcePreprocessingFinalNormalizedBody_valid
    (formula : ThreeCNF) :
    paperSourcePreprocessingFinalField 1
      (encodeThreeCNF formula) =
      paperSourceNormalizedClauseStream formula := by
  unfold paperSourcePreprocessingFinalField
  rw [Function.comp_apply,
    paperSourcePreprocessingFinalState_valid,
    paperSourcePreprocessingField_valid_one]

@[simp] private theorem paperSourcePreprocessingRetainedCountBinary_valid
    (formula : ThreeCNF) :
    paperPreprocessingRetainedCountBinary
      (encodeThreeCNF formula) =
      Computability.encodeNat
        (noTautClauses formula).length := by
  unfold paperPreprocessingRetainedCountBinary
    paperSourcePreprocessingFinalField
  rw [Function.comp_apply, Function.comp_apply,
    paperSourcePreprocessingFinalState_valid,
    paperSourcePreprocessingField_valid_two]
  simp only [List.length_replicate]

@[simp] theorem paperSourcePreprocessingFilteredFormulaWord_valid
    (formula : ThreeCNF) :
    paperPreprocessingFilteredFormulaWord
      (encodeThreeCNF formula) =
      encodeThreeCNF (noTautClauses formula) := by
  unfold paperPreprocessingFilteredFormulaWord
  rw [paperSourcePreprocessingRetainedCountBinary_valid,
    paperSourcePreprocessingFinalOriginalBody_valid]
  rfl

@[simp] private theorem paperSourcePreprocessingRecoveredOriginal_valid
    (formula : ThreeCNF) :
    paperPreprocessingRecoveredOriginal
      (encodeThreeCNF formula) =
      encodeThreeCNF formula := by
  unfold paperPreprocessingRecoveredOriginal
  rw [Function.comp_apply,
    paperSourcePreprocessingFinalState_valid,
    paperSourcePreprocessingOriginal_valid]

theorem paperSourcePreprocessingOutput_valid
    (formula : ThreeCNF) :
    paperSourcePreprocessingOutput (encodeThreeCNF formula) =
      lengthPrefixedWord
        (encodeThreeCNF (noTautClauses formula)) ++
      (lengthPrefixedWord
        (paperSourceNormalizedClauseStream formula) ++
        encodeThreeCNF formula) := by
  unfold paperSourcePreprocessingOutput
  rw [paperSourcePreprocessingFilteredFormulaWord_valid,
    paperSourcePreprocessingFinalNormalizedBody_valid,
    paperSourcePreprocessingRecoveredOriginal_valid]

end SourcePreprocessingTM

namespace NormalizedRecordDecoder

open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.SourcePreprocessingTM

private def readPaperVariableArityLiterals :
    ℕ → List Bool → Option (List Literal × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits =>
    match readLiteral bits with
    | none => none
    | some (literal, remaining) =>
      match readPaperVariableArityLiterals count remaining with
      | none => none
      | some (literals, suffix) =>
        some (literal :: literals, suffix)

@[simp] private theorem readPaperVariableArityLiterals_flatMap
    (literals : List Literal) (suffix : List Bool) :
    readPaperVariableArityLiterals literals.length
      (literals.flatMap encodeLiteral ++ suffix) =
        some (literals, suffix) := by
  induction literals with
  | nil => simp only [List.length_nil, List.flatMap_nil, List.nil_append,
      readPaperVariableArityLiterals]
  | cons literal remaining ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc,
        readPaperVariableArityLiterals,
        readLiteral_append, ih]

private def readPaperVariableArityClauseRecord
    (bits : List Bool) : Option (List Literal × List Bool) :=
  match readUnaryPrefix bits with
  | none => none
  | some (count, remaining) =>
    if 0 < count ∧ count ≤ 3 then
      readPaperVariableArityLiterals count remaining
    else
      none

@[simp] private theorem readPaperVariableArityClauseRecord_append
    (clause : ThreeClause) (suffix : List Bool) :
    readPaperVariableArityClauseRecord
        (paperSourceNormalizedClauseRecord clause ++ suffix) =
      some (paperSourceNormalizedClause clause, suffix) := by
  have hpositive :
      0 < (paperSourceNormalizedClause clause).length :=
    List.length_pos_iff.mpr
      (paperSourceNormalizedClause_ne_nil clause)
  have hbound := paperNormalizedClause_length_le_three clause
  unfold readPaperVariableArityClauseRecord
  simp only [paperSourceNormalizedClauseRecord, List.append_assoc, List.cons_append,
      readUnaryPrefix_replicate,
      hpositive, hbound, and_self, ↓reduceIte, readPaperVariableArityLiterals_flatMap]

private def readPaperVariableArityClauseRecords :
    ℕ → List Bool → Option (List (List Literal) × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits =>
    match readPaperVariableArityClauseRecord bits with
    | none => none
    | some (clause, remaining) =>
      match readPaperVariableArityClauseRecords count remaining with
      | none => none
      | some (clauses, suffix) => some (clause :: clauses, suffix)

@[simp] private theorem readPaperVariableArityClauseRecords_flatMap
    (clauses : List ThreeClause) (suffix : List Bool) :
    readPaperVariableArityClauseRecords clauses.length
      (clauses.flatMap paperSourceNormalizedClauseRecord ++ suffix) =
        some (clauses.map paperSourceNormalizedClause, suffix) := by
  induction clauses with
  | nil => simp only [List.length_nil, List.flatMap_nil, List.nil_append,
      readPaperVariableArityClauseRecords,
               List.map_nil]
  | cons clause remaining ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc,
        readPaperVariableArityClauseRecords,
        readPaperVariableArityClauseRecord_append, ih, List.map_cons]

@[simp] private theorem readPaperVariableArityClauseRecords_normalizedStream
    (formula : ThreeCNF) :
    readPaperVariableArityClauseRecords
      (noTautClauses formula).length
      (paperSourceNormalizedClauseStream formula) =
      some (paperSourceNormalizedClauses formula, []) := by
  simpa only [paperSourceNormalizedClauseStream, paperSourceNormalizedClauses, List.append_nil]
      using
      readPaperVariableArityClauseRecords_flatMap (noTautClauses formula) []

/-- GapCVP reduction support. -/
structure PaperVariableArityNormalizedSourceDescriptor where
  /-- GapCVP reduction support. -/
  retainedFormula : ThreeCNF
  /-- GapCVP reduction support. -/
  normalizedClauses : List (List Literal)
  /-- GapCVP reduction support. -/
  originalFormula : ThreeCNF
  /-- GapCVP reduction support. -/
  originalWord : List Bool

/-- GapCVP reduction support. -/
def readPaperVariableArityNormalizedSourceDescriptor
    (bits : List Bool) :
    Option PaperVariableArityNormalizedSourceDescriptor :=
  match readLengthPrefixedWord bits with
  | none => none
  | some (retainedWord, suffix) =>
    match readLengthPrefixedWord suffix with
    | none => none
    | some (normalizedWord, originalWord) =>
      match decodeThreeCNF retainedWord, decodeThreeCNF originalWord with
      | some retained, some original =>
        if encodeThreeCNF retained = retainedWord ∧
            encodeThreeCNF original = originalWord then
          match readPaperVariableArityClauseRecords
              retained.length normalizedWord with
          | some (normalized, []) =>
            if retained = noTautClauses original ∧
                normalized = paperSourceNormalizedClauses original then
              some
                { retainedFormula := retained
                  normalizedClauses := normalized
                  originalFormula := original
                  originalWord := originalWord }
            else
              none
          | _ => none
        else
          none
      | _, _ => none

@[simp] theorem readPaperVariableArityNormalizedSourceDescriptor_valid
    (formula : ThreeCNF) :
    readPaperVariableArityNormalizedSourceDescriptor
      (paperSourcePreprocessingOutput
        (encodeThreeCNF formula)) =
      some
        { retainedFormula := noTautClauses formula
          normalizedClauses := paperSourceNormalizedClauses formula
          originalFormula := formula
          originalWord := encodeThreeCNF formula } := by
  rw [paperSourcePreprocessingOutput_valid]
  unfold readPaperVariableArityNormalizedSourceDescriptor
  simp only [readLengthPrefixedWord_append, decodeThreeCNF_encode, and_self, ↓reduceIte,
      readPaperVariableArityClauseRecords_normalizedStream]

@[simp] theorem readPaperVariableArityNormalizedSourceDescriptor_retainedCount
    (formula : ThreeCNF) :
    (paperSourceNormalizedClauses formula).length =
      (noTautClauses formula).length := by
  simp only [paperSourceNormalizedClauses, List.length_map]

end NormalizedRecordDecoder

namespace ClauseCardinality

open GapCVP.SourcePreprocessingSemantics GapCVP.BinarySourceTautologyNormalizationExact

private theorem paperVariableArity_retainedClause_signed_nodup
    (formula : ThreeCNF) (clause : List Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula) :
    clause.Nodup := by
  obtain ⟨original, _, horiginal⟩ :=
    (mem_paperSourceNormalizedClauses_iff formula clause).mp hclause
  rw [← horiginal]
  exact paperSourceNormalizedClause_nodup original

private theorem paperVariableArity_retainedClause_fst_injective
    (formula : ThreeCNF) (clause : List Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula)
    (first : Literal) (hfirst : first ∈ clause)
    (second : Literal) (hsecond : second ∈ clause)
    (hname : first.1 = second.1) :
    first = second := by
  obtain ⟨original, hretained, horiginal⟩ :=
    (mem_paperSourceNormalizedClauses_iff formula clause).mp hclause
  have hfirstSource : first ∈ paperSourceNormalizedClause original := by
    rw [horiginal]
    exact hfirst
  have hsecondSource : second ∈ paperSourceNormalizedClause original := by
    rw [horiginal]
    exact hsecond
  obtain ⟨firstIndex, hfirstIndex⟩ :=
    (mem_paperSourceNormalizedClause_iff original first).mp hfirstSource
  obtain ⟨secondIndex, hsecondIndex⟩ :=
    (mem_paperSourceNormalizedClause_iff original second).mp hsecondSource
  by_cases hsign : first.2 = second.2
  · exact Prod.ext hname hsign
  · have htautology : sourceClauseIsTautology original = true := by
      apply (sourceClauseIsTautology_iff original).mpr
      refine ⟨firstIndex, secondIndex, ?_, ?_⟩
      · simpa only [hfirstIndex, hsecondIndex] using hname
      · simpa only [hfirstIndex, hsecondIndex, ne_eq] using hsign
    have hnot :=
      ((mem_sourceClausesWithoutTautologies formula original).mp
        hretained).2
    rw [hnot] at htautology
    contradiction

end ClauseCardinality

namespace SourceOrder

open scoped BigOperators

open GapCVP.Core GapCVP.BinaryFieldBasis GapCVP.BinarySourceCoordinateOrder
open GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryOrderedAssembly
open GapCVP.BinaryOrderedRefinement GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge
open GapCVP.ClauseCardinality

/-- GapCVP reduction support. -/
def paperVariableArityBooleanWordOrder (arity : ℕ) :
    Fin (2 ^ arity) ≃ (Fin arity → Bool) := by
  classical
  refine Equiv.ofBijective (indexedWord arity) ?_
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨indexedWord_injective arity, ?_⟩
  simp only [Fintype.card_fin, Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
      Finset.card_univ]

/-- GapCVP reduction support. -/
def paperVariableArityRejectedWord
    (arity : ℕ) (sign : Fin arity → Bool) : Fin (2 ^ arity) :=
  (paperVariableArityBooleanWordOrder arity).symm
    (fun index => Bool.not (sign index))

private theorem paperVariableArityWord_ne_rejected_iff
    (arity : ℕ) (sign : Fin arity → Bool) (word : Fin (2 ^ arity)) :
    word ≠ paperVariableArityRejectedWord arity sign ↔
      ∃ index : Fin arity,
        paperVariableArityBooleanWordOrder arity word index = sign index := by
  let rejected : Fin arity → Bool := fun index => Bool.not (sign index)
  have neverSatisfied :
      ¬ ∃ index : Fin arity, rejected index = sign index := by
    rintro ⟨index, hequal⟩
    change Bool.not (sign index) = sign index at hequal
    cases hsign : sign index <;> simp [hsign] at hequal
  constructor
  · intro different
    by_contra noneSatisfied
    apply different
    apply (paperVariableArityBooleanWordOrder arity).injective
    have allOpposite :
        paperVariableArityBooleanWordOrder arity word = rejected := by
      funext index
      change
        paperVariableArityBooleanWordOrder arity word index =
          Bool.not (sign index)
      apply Bool.eq_not_iff.mpr
      intro hequal
      exact noneSatisfied ⟨index, hequal⟩
    simpa only [paperVariableArityRejectedWord, Equiv.apply_symm_apply] using allOpposite
  · rintro ⟨index, hsatisfies⟩ hequal
    have wordIsRejected :
        paperVariableArityBooleanWordOrder arity word = rejected := by
      subst word
      simp only [paperVariableArityRejectedWord, Equiv.apply_symm_apply, rejected]
    exact neverSatisfied ⟨index, wordIsRejected ▸ hsatisfies⟩

/-- GapCVP reduction support. -/
def paperSatisfyingWordOrder
    (arity : ℕ) (sign : Fin arity → Bool) :
    Fin (2 ^ arity - 1) ≃
      {assignment : Fin arity → Bool //
        ∃ index : Fin arity, assignment index = sign index} := by
  have positive : 0 < 2 ^ arity := by positivity
  have cardinality : 2 ^ arity - 1 + 1 = 2 ^ arity := by omega
  let correction :
      Fin (2 ^ arity - 1 + 1) ≃ Fin (2 ^ arity) :=
    finCongr cardinality
  let removed : Fin (2 ^ arity - 1 + 1) :=
    correction.symm (paperVariableArityRejectedWord arity sign)
  refine (finSuccAboveEquiv removed).trans ?_
  refine Equiv.subtypeEquiv
    (correction.trans (paperVariableArityBooleanWordOrder arity)) ?_
  intro word
  change word ≠ removed ↔
    ∃ index : Fin arity,
      paperVariableArityBooleanWordOrder arity (correction word) index =
        sign index
  constructor
  · intro different
    apply (paperVariableArityWord_ne_rejected_iff
      arity sign (correction word)).mp
    intro equal
    apply different
    apply correction.injective
    simpa [removed] using equal
  · intro satisfied equal
    have different := (paperVariableArityWord_ne_rejected_iff
      arity sign (correction word)).mpr satisfied
    apply different
    simpa [removed] using congrArg correction equal

private theorem paperVariableAritySourceLiteral_mem_sourceClause
    (formula : ThreeCNF) (clause : List GapCVP.Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula)
    (literal : GapCVP.Literal) (hliteral : literal ∈ clause) :
    paperVariableAritySourceLiteral
        formula clause hclause literal hliteral ∈
      (paperVariableAritySourceClause formula clause hclause).literals := by
  simp only [paperVariableAritySourceClause]
  exact List.mem_toFinset.mpr
    (List.mem_map.mpr
      ⟨⟨literal, hliteral⟩, List.mem_attach _ _, rfl⟩)

private def paperLocalVariableEmbedding
    (formula : ThreeCNF) (clause : List GapCVP.Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula) :
    Fin clause.length ↪
      (paperVariableAritySourceClause formula clause hclause).LocalVariable where
  toFun index :=
    ⟨(paperVariableAritySourceLiteral formula clause hclause
        (clause.get index) (List.get_mem clause index)).variableIndex,
      Finset.mem_image_of_mem
        (fun literal : GapCVP.Core.Literal
          (paperVariableArityVariableCount formula) => literal.variableIndex)
        (paperVariableAritySourceLiteral_mem_sourceClause formula clause hclause
          (clause.get index) (List.get_mem clause index))⟩
  inj' := by
    intro first second hequal
    have hrank := congrArg
      (fun localVariable :
        (paperVariableAritySourceClause formula clause hclause).LocalVariable =>
          localVariable.val.val) hequal
    change
      paperVariableArityVariableRank formula (clause.get first).1 =
        paperVariableArityVariableRank formula (clause.get second).1 at hrank
    have hfirstMem :
        (clause.get first).1 ∈ paperNormalizedOccurringVariables formula := by
      apply List.idxOf_lt_length_iff.mp
      exact paperVariableArityVariableRank_lt
        formula clause hclause (clause.get first) (List.get_mem clause first)
    have hname : (clause.get first).1 = (clause.get second).1 := by
      apply (List.idxOf_inj hfirstMem).mp
      exact hrank
    have hliteral : clause.get first = clause.get second :=
      paperVariableArity_retainedClause_fst_injective
        formula clause hclause
        (clause.get first) (List.get_mem clause first)
        (clause.get second) (List.get_mem clause second) hname
    apply Fin.ext
    calc
      first.val = clause.idxOf (clause.get first) :=
        (List.get_idxOf
          (paperVariableArity_retainedClause_signed_nodup
            formula clause hclause) first).symm
      _ = clause.idxOf (clause.get second) := congrArg clause.idxOf hliteral
      _ = second.val :=
        List.get_idxOf
          (paperVariableArity_retainedClause_signed_nodup
            formula clause hclause) second

private theorem paperVariableArityLocalVariableEmbedding_surjective
    (formula : ThreeCNF) (clause : List GapCVP.Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula) :
    Function.Surjective
      (paperLocalVariableEmbedding formula clause hclause) := by
  intro localVariable
  obtain ⟨literal, hliteral, hvariable⟩ :=
    Finset.mem_image.mp localVariable.property
  simp only [paperVariableAritySourceClause] at hliteral
  obtain ⟨item, _, hequal⟩ :=
    List.mem_map.mp (List.mem_toFinset.mp hliteral)
  obtain ⟨index, hindex⟩ := List.mem_iff_get.mp item.property
  refine ⟨index, ?_⟩
  apply Subtype.ext
  change
    (paperVariableAritySourceLiteral formula clause hclause
      (clause.get index) (List.get_mem clause index)).variableIndex =
      localVariable.val
  have hsource :
      paperVariableAritySourceLiteral formula clause hclause
          (clause.get index) (List.get_mem clause index) = literal := by
    have hitem :
        (⟨clause.get index, List.get_mem clause index⟩ :
          {retained : GapCVP.Literal // retained ∈ clause}) = item :=
      Subtype.ext hindex
    exact (congrArg
      (fun retained : {retained : GapCVP.Literal // retained ∈ clause} =>
        paperVariableAritySourceLiteral formula clause hclause
          retained.val retained.property) hitem).trans hequal
  exact (congrArg
    (fun source : GapCVP.Core.Literal
      (paperVariableArityVariableCount formula) => source.variableIndex)
      hsource).trans hvariable

/-- GapCVP reduction support. -/
def paperLocalVariableWordOrder
    (formula : ThreeCNF) (clause : List GapCVP.Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula) :
    Fin clause.length ≃
      (paperVariableAritySourceClause formula clause hclause).LocalVariable :=
  Equiv.ofBijective
    (paperLocalVariableEmbedding formula clause hclause)
    ⟨(paperLocalVariableEmbedding
        formula clause hclause).injective,
      paperVariableArityLocalVariableEmbedding_surjective
        formula clause hclause⟩

/-- GapCVP reduction support. -/
def paperLocalAssignmentWordOrder
    (formula : ThreeCNF) (clause : List GapCVP.Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula) :
    (paperVariableAritySourceClause formula clause hclause).LocalAssignment ≃
      (Fin clause.length → Bool) :=
  Equiv.arrowCongr
    (paperLocalVariableWordOrder formula clause hclause).symm
    (Equiv.refl Bool)

theorem paperVariableAritySourceClause_localSatisfied_iff
    (formula : ThreeCNF) (clause : List GapCVP.Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula)
    (assignment :
      (paperVariableAritySourceClause formula clause hclause).LocalAssignment) :
    (paperVariableAritySourceClause
        formula clause hclause).LocalSatisfied assignment ↔
      ∃ index : Fin clause.length,
        paperLocalAssignmentWordOrder
          formula clause hclause assignment index =
            (clause.get index).2 := by
  simp only [GapCVP.Core.Clause.LocalSatisfied, decide_eq_true_eq] at *
  constructor
  · rintro ⟨literal, hliteral, hsatisfied⟩
    simp only [paperVariableAritySourceClause] at hliteral
    obtain ⟨item, _, hequal⟩ :=
      List.mem_map.mp (List.mem_toFinset.mp hliteral)
    subst literal
    obtain ⟨index, hindex⟩ := List.mem_iff_get.mp item.property
    have hitem :
        (⟨clause.get index, List.get_mem clause index⟩ :
          {retained : GapCVP.Literal // retained ∈ clause}) = item :=
      Subtype.ext hindex
    subst item
    refine ⟨index, ?_⟩
    simpa only [paperLocalAssignmentWordOrder, paperLocalVariableWordOrder,
        paperLocalVariableEmbedding,
        paperVariableAritySourceLiteral, List.get_eq_getElem, Function.Embedding.coeFn_mk,
            Equiv.arrowCongr_apply,
        Equiv.coe_refl, Equiv.symm_symm, Equiv.coe_ofBijective, Function.comp_apply, id_eq]
            using hsatisfied
  · rintro ⟨index, hsatisfied⟩
    refine ⟨paperVariableAritySourceLiteral formula clause hclause
      (clause.get index) (List.get_mem clause index),
      paperVariableAritySourceLiteral_mem_sourceClause
        formula clause hclause (clause.get index)
          (List.get_mem clause index), ?_⟩
    simpa only [paperVariableAritySourceLiteral, List.get_eq_getElem,
        paperLocalAssignmentWordOrder,
        paperLocalVariableWordOrder, paperLocalVariableEmbedding, Function.Embedding.coeFn_mk,
            Equiv.arrowCongr_apply,
        Equiv.coe_refl, Equiv.symm_symm, Equiv.coe_ofBijective, Function.comp_apply, id_eq]
            using hsatisfied

/-- GapCVP reduction support. -/
def paperVariableAritySatisfyingLocalTupleWordEquiv
    (formula : ThreeCNF) (clause : List GapCVP.Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula) :
    (paperVariableAritySourceClause
      formula clause hclause).SatisfyingLocalTuple ≃
      {assignment : Fin clause.length → Bool //
        ∃ index : Fin clause.length,
          assignment index = (clause.get index).2} :=
  Equiv.subtypeEquiv
    (paperLocalAssignmentWordOrder formula clause hclause)
    (paperVariableAritySourceClause_localSatisfied_iff
      formula clause hclause)

/-- GapCVP reduction support. -/
def sourceClauseTupleWordOrder
    (formula : ThreeCNF) (clause : List GapCVP.Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula) :
    Fin (2 ^ clause.length - 1) ≃
      (paperVariableAritySourceClause
        formula clause hclause).SatisfyingLocalTuple :=
  (paperSatisfyingWordOrder
    clause.length (fun index => (clause.get index).2)).trans
      (paperVariableAritySatisfyingLocalTupleWordEquiv
        formula clause hclause).symm

/-- GapCVP reduction support. -/
abbrev paperFormulaRetainedClause
    (formula : ThreeCNF)
    (index : Fin (srcFormula formula).clauses.length) :
    {clause : List GapCVP.Literal //
      clause ∈ paperSourceNormalizedClauses formula} := by
  have hlength :
      (srcFormula formula).clauses.length =
        (paperSourceNormalizedClauses formula).attach.length := by
    simp only [srcFormula, List.length_map, List.length_attach,
        NormalizedRecordDecoder.readPaperVariableArityNormalizedSourceDescriptor_retainedCount]
  exact (paperSourceNormalizedClauses formula).attach.get
    (Fin.cast hlength index)

theorem paperFormulaRetainedClause_sourceClause
    (formula : ThreeCNF)
    (index : Fin (srcFormula formula).clauses.length) :
    paperVariableAritySourceClause formula
        (paperFormulaRetainedClause formula index).val
        (paperFormulaRetainedClause formula index).property =
      (srcFormula formula).clauses.get index := by
  simp only [paperFormulaRetainedClause, srcFormula, List.get_eq_getElem, Fin.val_cast,
      List.getElem_attach,
      List.getElem_map]

/-- GapCVP reduction support. -/
def paperFormulaClauseWidth
    (formula : ThreeCNF)
    (index : Fin (srcFormula formula).clauses.length) : ℕ :=
  (paperFormulaRetainedClause formula index).val.length

/-- GapCVP reduction support. -/
def paperFormulaClauseTupleWordOrder
    (formula : ThreeCNF)
    (index : Fin (srcFormula formula).clauses.length) :
    Fin (2 ^ paperFormulaClauseWidth formula index - 1) ≃
      ((srcFormula
        formula).clauses.get index).SatisfyingLocalTuple := by
  let retained := paperFormulaRetainedClause formula index
  have hequal :
      paperVariableAritySourceClause
          formula retained.val retained.property =
        (srcFormula formula).clauses.get index :=
    paperFormulaRetainedClause_sourceClause formula index
  change Fin (2 ^ retained.val.length - 1) ≃ _
  exact hequal ▸ sourceClauseTupleWordOrder
    formula retained.val retained.property

/-- GapCVP reduction support. -/
def paperFormulaClauseVariableWordOrder
    (formula : ThreeCNF)
    (index : Fin (srcFormula formula).clauses.length) :
    Fin (paperFormulaClauseWidth formula index) ≃
      ((srcFormula
        formula).clauses.get index).LocalVariable := by
  let retained := paperFormulaRetainedClause formula index
  have hequal :
      paperVariableAritySourceClause
          formula retained.val retained.property =
        (srcFormula formula).clauses.get index :=
    paperFormulaRetainedClause_sourceClause formula index
  change Fin retained.val.length ≃ _
  exact hequal ▸ paperLocalVariableWordOrder
    formula retained.val retained.property

/-- GapCVP reduction support. -/
def paperVariableArityLocalTagCount (formula : ThreeCNF) : ℕ :=
  ∑ index : Fin (srcFormula formula).clauses.length,
    (2 ^ paperFormulaClauseWidth formula index - 1)

/-- GapCVP reduction support. -/
def paperVariableArityLocalTagWordOrder
    (formula : ThreeCNF) :
    Fin (paperVariableArityLocalTagCount formula) ≃
      (Σ index : Fin (srcFormula formula).clauses.length,
        ((srcFormula
          formula).clauses.get index).SatisfyingLocalTuple) := by
  change Fin
    (∑ index : Fin (srcFormula formula).clauses.length,
      (2 ^ paperFormulaClauseWidth formula index - 1)) ≃ _
  exact finSigmaFinEquiv.symm.trans
    (Equiv.sigmaCongrRight
      (paperFormulaClauseTupleWordOrder formula))

/-- GapCVP reduction support. -/
def sourceTypeWordOrder
    (formula : ThreeCNF) :
    Fin (1 + paperVariableArityLocalTagCount formula) ≃
      sourceSATTableType (srcFormula formula) :=
  (finSumFinEquiv
    (m := 1) (n := paperVariableArityLocalTagCount formula)).symm.trans
      (Equiv.sumCongr finOneEquiv
        (paperVariableArityLocalTagWordOrder formula))

theorem sourceTableType_card
    (formula : ThreeCNF) :
    Fintype.card
      (sourceSATTableType (srcFormula formula)) =
        1 + paperVariableArityLocalTagCount formula := by
  simpa only [Fintype.card_sum, Fintype.card_unique, List.get_eq_getElem, Fintype.card_sigma,
      Nat.add_left_cancel_iff, Fintype.card_fin] using (Fintype.card_congr (sourceTypeWordOrder
          formula)).symm

end SourceOrder

end GapCVP

end
