/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part07A

/-! # GapCVP proof, part 07, continuation 02 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFFiveFamilyPackedInitialCellDecoderTM

open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLBoundedStates GapCVP.CLCellRows

open GapCVP.CLLocalWindows GapCVP.CLCellRowBounds GapCVP.CLFullTableauEmitter

open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding

open GapCVP.SourceUniformTuringTM GapCVP.SourceMachineCert

open GapCVP.OutputPolynomialCompositionClosure GapCVP.CLEmittedCNFTM GapCVP.CLWindowTruthTable

open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFUnaryPairIndexTM

open GapCVP.CNFUnaryPairIndexTotalRuntimeCert GapCVP.CNFFiveFamilyFlatCandidateGenerationTM

open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM

open GapCVP.CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM

open GapCVP.CNFFiveFamilyPackedInitialOffsetFeatureTM

open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM

private def fiveFamilyPackedInitialFeatureLimit
    (tm : Turing.FinTM2) : ℕ :=
  12 * blockSize tm

private def fivePackedInitialDecodedSymbolValue
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (features : List Bool) : ℕ :=
  (completePhaseSymbolEquiv machine.tm
    (fiveFamilyPackedInitialDecodedCell machine features)).val

private def fivePackedInitialThresholdBitWord
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (index : ℕ) (features : List Bool) : List Bool :=
  [boundedLookupOutput
    (fiveFamilyPackedInitialFeatureLimit machine.tm)
    (fun bits => decide
      (index < fivePackedInitialDecodedSymbolValue
        machine bits)) features]

private noncomputable def fiveFamilyPackedInitialThresholdBitComputable
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (index : ℕ) :
    BitTM
      (fivePackedInitialThresholdBitWord machine index) :=
  boundedLookupComputable
    (fiveFamilyPackedInitialFeatureLimit machine.tm)
    (fun bits => decide
      (index < fivePackedInitialDecodedSymbolValue
        machine bits))

private def fivePackedInitialThresholdMarkerWord
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (index : ℕ) (features : List Bool) : List Bool :=
  markerConditionalOutput (fun _ => [true]) []
    (fivePackedInitialThresholdBitWord
      machine index features)

private noncomputable def fiveFamilyPackedInitialThresholdMarkerComputable
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (index : ℕ) :
    BitTM
      (fivePackedInitialThresholdMarkerWord machine index) := by
  have branch := markerConditionalComputable
    (constantWordComputable [true]) []
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyPackedInitialThresholdBitComputable machine index)
    branch
  change BitTM
    (fun features =>
      markerConditionalOutput (fun _ => [true]) []
        (fivePackedInitialThresholdBitWord
          machine index features))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyPackedInitialThresholdMarkerWord_valid
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (index : ℕ) (features : List Bool)
    (hfeatures : features.length ≤
      fiveFamilyPackedInitialFeatureLimit machine.tm) :
    fivePackedInitialThresholdMarkerWord
      machine index features =
      if index < fivePackedInitialDecodedSymbolValue
        machine features then [true] else [] := by
  unfold fivePackedInitialThresholdMarkerWord
    fivePackedInitialThresholdBitWord
  rw [boundedLookupOutput_of_length_le
    (fiveFamilyPackedInitialFeatureLimit machine.tm)
    (fun bits => decide
      (index < fivePackedInitialDecodedSymbolValue
        machine bits)) features hfeatures]
  by_cases hindex : index <
      fivePackedInitialDecodedSymbolValue machine features <;>
    simp [hindex, markerConditionalOutput]

private def fivePackedInitialThresholdStreamWord
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (indices : List ℕ) (features : List Bool) : List Bool :=
  indices.flatMap fun index =>
    fivePackedInitialThresholdMarkerWord
      machine index features

private noncomputable def fiveFamilyPackedInitialThresholdStreamComputable
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (indices : List ℕ) :
    BitTM
      (fivePackedInitialThresholdStreamWord machine indices) := by
  induction indices with
  | nil => exact constantWordComputable []
  | cons index remaining ih =>
      exact pointwiseAppendComputable
        (fiveFamilyPackedInitialThresholdMarkerComputable
          machine index) ih

private theorem fiveFamilyPackedInitialWholeFeatureWord_length_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (position : Position (rowWidth bound machine original)) :
    (fivePackedInitialWholeFeatureWord bound machine
      (lengthPrefixedWord (List.replicate position.val true) ++
        lengthPrefixedWord original ++ suffix)).length =
      fiveFamilyPackedInitialFeatureLimit machine.tm := by
  rw [fiveFamilyPackedInitialWholeFeatureWord_valid
    bound machine original suffix position]
  simp only [List.length_append, List.length_flatMap,
      fiveFamilyPackedActualOffsetObservation_length,
      List.map_const', List.length_range, List.sum_replicate, smul_eq_mul,
          fiveFamilyPackedInitialFeatureLimit]
  ring

private theorem fiveFamilyPackedInitialThresholdMarkers_eq_replicate
    (alphabet value : ℕ) (hvalue : value ≤ alphabet) :
    (List.range alphabet).flatMap
      (fun index => if index < value then [true] else []) =
      List.replicate value true := by
  induction alphabet generalizing value with
  | zero =>
      have hzero : value = 0 := by omega
      simp only [hzero, not_lt_zero, ↓reduceIte, List.range_zero, List.flatMap_nil,
          List.replicate_zero]
  | succ alphabet ih =>
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_singleton]
      by_cases hlast : alphabet < value
      · have hvalue' : value = alphabet + 1 := by omega
        subst value
        have hprefix :
            (List.range alphabet).flatMap
              (fun index =>
                if index < alphabet + 1 then [true] else []) =
              (List.range alphabet).flatMap
                (fun index =>
                  if index < alphabet then [true] else []) := by
          apply List.flatMap_congr
          intro index hindex
          have hlt : index < alphabet := by
            simpa only [List.mem_range] using hindex
          simp only [Nat.lt_succ_of_lt hlt, ↓reduceIte, hlt]
        rw [hprefix, ih alphabet (Nat.le_refl alphabet)]
        simp only [lt_add_iff_pos_right, Order.lt_one_iff, ↓reduceIte,
            SourceStructuralDecoder.replicate_true_append_cons, List.append_nil,
                List.replicate_succ]
      · rw [ih value (by omega)]
        simp only [hlast, ↓reduceIte, List.append_nil]

private def fivePackedInitialSourceSymbolUnary
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) : List Bool :=
  fivePackedInitialThresholdStreamWord machine
    (List.range (completePhaseSymbolCount machine.tm))
    (fivePackedInitialWholeFeatureWord bound machine input)

private noncomputable def fiveFamilyPackedInitialSourceSymbolUnaryComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fivePackedInitialSourceSymbolUnary bound machine) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyPackedInitialWholeFeatureComputable bound machine)
    (fiveFamilyPackedInitialThresholdStreamComputable machine
      (List.range (completePhaseSymbolCount machine.tm)))
  change BitTM
    (fun input =>
      fivePackedInitialThresholdStreamWord machine
        (List.range (completePhaseSymbolCount machine.tm))
        (fivePackedInitialWholeFeatureWord
          bound machine input))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyPackedInitialSourceSymbolUnary_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (position : Position (rowWidth bound machine original)) :
    fivePackedInitialSourceSymbolUnary bound machine
      (lengthPrefixedWord (List.replicate position.val true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate
        (completePhaseSymbolEquiv machine.tm
          (initialPhaseCell bound machine original position)).val
        true := by
  let query := lengthPrefixedWord (List.replicate position.val true) ++
    lengthPrefixedWord original ++ suffix
  let features := fivePackedInitialWholeFeatureWord
    bound machine query
  let symbol := completePhaseSymbolEquiv machine.tm
    (initialPhaseCell bound machine original position)
  have hfeatures :
      features.length ≤ fiveFamilyPackedInitialFeatureLimit machine.tm :=
    Nat.le_of_eq (fiveFamilyPackedInitialWholeFeatureWord_length_valid
      bound machine original suffix position)
  have hdecoded :
      fivePackedInitialDecodedSymbolValue machine features =
        symbol.val := by
    unfold fivePackedInitialDecodedSymbolValue
    rw [fiveFamilyPackedInitialDecodedCell_valid
      bound machine original suffix position]
  unfold fivePackedInitialSourceSymbolUnary
    fivePackedInitialThresholdStreamWord
  change
    (List.range (completePhaseSymbolCount machine.tm)).flatMap
      (fun index => fivePackedInitialThresholdMarkerWord
        machine index features) =
      List.replicate symbol.val true
  calc
    (List.range (completePhaseSymbolCount machine.tm)).flatMap
      (fun index => fivePackedInitialThresholdMarkerWord
        machine index features) =
        (List.range (completePhaseSymbolCount machine.tm)).flatMap
          (fun index => if index < symbol.val then [true] else []) := by
            apply List.flatMap_congr
            intro index _
            rw [fiveFamilyPackedInitialThresholdMarkerWord_valid
              machine index features hfeatures, hdecoded]
    _ = List.replicate symbol.val true :=
      fiveFamilyPackedInitialThresholdMarkers_eq_replicate
        (completePhaseSymbolCount machine.tm) symbol.val
        (by have hlt := symbol.isLt; omega)

private def fivePackedInitialPositionSymbolPairInput
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) : List Bool :=
  fiveFamilyFlatIndexedPhysicalRank input ++
    false :: (fivePackedInitialSourceSymbolUnary
      bound machine input ++ [false])

private noncomputable def fiveFamilyPackedInitialPositionSymbolPairInputComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fivePackedInitialPositionSymbolPairInput
        bound machine) := by
  have symbolSuffix := pointwiseAppendComputable
    (fiveFamilyPackedInitialSourceSymbolUnaryComputable
      bound machine)
    (constantWordComputable [false])
  have delimiter := GapCVP.TMComposition.computableInPolyTime
    symbolSuffix (prependBitComputable false)
  have physical := pointwiseAppendComputable
    fiveFlatIndexedPhysicalRankComputable delimiter
  change BitTM
    (fun input =>
      fiveFamilyFlatIndexedPhysicalRank input ++
        false :: (fivePackedInitialSourceSymbolUnary
          bound machine input ++ [false]))
  simpa only [Function.comp_apply] using physical

private def fivePackedInitialPositionSymbolCode
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) : List Bool :=
  unarySourcePairOutput
    (fivePackedInitialPositionSymbolPairInput
      bound machine input)

private noncomputable def fiveFamilyPackedInitialPositionSymbolCodeComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fivePackedInitialPositionSymbolCode bound machine) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyPackedInitialPositionSymbolPairInputComputable
      bound machine)
    actualUnaryPairIndexComputable
  change BitTM
    (fun input => unarySourcePairOutput
      (fivePackedInitialPositionSymbolPairInput
        bound machine input))
  simpa only [Function.comp_def] using physical

private def fivePackedInitialSourceVariablePairInput
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) : List Bool :=
  false :: (fivePackedInitialPositionSymbolCode
    bound machine input ++ [false])

private noncomputable def fiveFamilyPackedInitialSourceVariablePairInputComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fivePackedInitialSourceVariablePairInput bound machine) := by
  have field := pointwiseAppendComputable
    (fiveFamilyPackedInitialPositionSymbolCodeComputable
      bound machine)
    (constantWordComputable [false])
  have physical := GapCVP.TMComposition.computableInPolyTime
    field (prependBitComputable false)
  change BitTM
    (fun input => false ::
      (fivePackedInitialPositionSymbolCode
        bound machine input ++ [false]))
  simpa only [Function.comp_def] using physical

private def fivePackedInitialSourceVariableCode
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) : List Bool :=
  unarySourcePairOutput
    (fivePackedInitialSourceVariablePairInput
      bound machine input)

private noncomputable def fiveFamilyPackedInitialSourceVariableCodeComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fivePackedInitialSourceVariableCode bound machine) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyPackedInitialSourceVariablePairInputComputable
      bound machine)
    actualUnaryPairIndexComputable
  change BitTM
    (fun input => unarySourcePairOutput
      (fivePackedInitialSourceVariablePairInput
        bound machine input))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyPackedInitialSourceVariableCode_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (position : Position (rowWidth bound machine original)) :
    fivePackedInitialSourceVariableCode bound machine
      (lengthPrefixedWord (List.replicate position.val true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate
        (Encodable.encode
          (((0 : Time (rowWidth bound machine original)),
            position,
            completePhaseSymbolEquiv machine.tm
              (initialPhaseCell bound machine original position)) :
            Variable (rowWidth bound machine original)
              (completePhaseSymbolCount machine.tm))) true := by
  unfold fivePackedInitialSourceVariableCode
    fivePackedInitialSourceVariablePairInput
    fivePackedInitialPositionSymbolCode
    fivePackedInitialPositionSymbolPairInput
  rw [fiveFamilyFlatIndexedPhysicalRank_valid,
    fiveFamilyPackedInitialSourceSymbolUnary_valid
      bound machine original suffix position]
  let symbol := completePhaseSymbolEquiv machine.tm
    (initialPhaseCell bound machine original position)
  have hinner :
      unarySourcePairOutput
        (List.replicate position.val true ++
          false :: (List.replicate symbol.val true ++ [false])) =
        List.replicate (Nat.pair position.val symbol.val) true := by
    exact unarySourcePairOutput_word position.val symbol.val
  change
    unarySourcePairOutput
      (false :: (unarySourcePairOutput
        (List.replicate position.val true ++
          false :: (List.replicate symbol.val true ++ [false])) ++
        [false])) = _
  rw [hinner]
  change
    unarySourcePairOutput
      (unarySourcePairWord 0
        (Nat.pair position.val symbol.val)) = _
  rw [unarySourcePairOutput_word]
  rfl

/-- GapCVP reduction support. -/
def fiveFlatWholePackedInitialClauseRecordWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) : List Bool :=
  fiveFlatSourceVariableSingletonRecordWord true
    (fivePackedInitialSourceVariableCode
      bound machine input)

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def fiveFamilyFlatWholePackedInitialClauseRecordComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveFlatWholePackedInitialClauseRecordWord
        bound machine) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyPackedInitialSourceVariableCodeComputable
      bound machine)
    (fiveFamilyFlatSourceVariableSingletonRecordComputable true)
  change BitTM
    (fun input => fiveFlatSourceVariableSingletonRecordWord true
      (fivePackedInitialSourceVariableCode
        bound machine input))
  simpa only [Function.comp_def] using physical

theorem fiveFamilyFlatWholePackedInitialClauseRecordWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (position : Position (rowWidth bound machine original)) :
    fiveFlatWholePackedInitialClauseRecordWord
      bound machine
      (lengthPrefixedWord (List.replicate position.val true) ++
        lengthPrefixedWord original ++ suffix) =
      flatSourceClauseAnnotatedRecord
        (initialClause
          (paddedAcceptancePhaseSpecification
            bound machine original).input position) := by
  unfold fiveFlatWholePackedInitialClauseRecordWord
  rw [fiveFamilyPackedInitialSourceVariableCode_valid
    bound machine original suffix position,
    fiveFamilyFlatSourceVariableSingletonRecordWord_valid]
  rfl

end CNFFiveFamilyPackedInitialCellDecoderTM

namespace CNFFiveFamilyForbiddenWindowCoordinateTM

open Computability Turing GapCVP.CL GapCVP.CLCompleteVerifierSimulation GapCVP.CLCellRowBounds
open GapCVP.BinaryEncoding GapCVP.SourceUniformTuringTM GapCVP.SourceMachineCert
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFUnaryPairIndexTM GapCVP.CNFUnaryPairIndexTotalRuntimeCert
open GapCVP.CNFCappedUnaryMinimumTM GapCVP.CNFCappedUnaryMinimumTotalCert
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM
open GapCVP.CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM

/-- GapCVP reduction support. -/
inductive FiveFamilyForbiddenWindowCoordinate where
  | left
  | center
  | right
  | next

/-- GapCVP reduction support. -/
def fiveForbiddenUnarySuccessorWord
    (source : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  true :: source input

/-- GapCVP reduction support. -/
noncomputable def fiveForbiddenUnarySuccessorComputable
    {source : List Bool → List Bool}
    (computer : BitTM source) :
    BitTM
      (fiveForbiddenUnarySuccessorWord source) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    computer (prependBitComputable true)
  change BitTM
    (fun input => true :: source input)
  simpa only [Function.comp_def] using physical

private def fiveForbiddenComputedUnaryPairInput
    (left right : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  left input ++ false :: (right input ++ [false])

private noncomputable def fiveFamilyForbiddenComputedUnaryPairInputComputable
    {left right : List Bool → List Bool}
    (hleft : BitTM left)
    (hright : BitTM right) :
    BitTM
      (fiveForbiddenComputedUnaryPairInput left right) := by
  have suffix := pointwiseAppendComputable
    hright (constantWordComputable [false])
  have delimiter := GapCVP.TMComposition.computableInPolyTime
    suffix (prependBitComputable false)
  have physical := pointwiseAppendComputable
    hleft delimiter
  change BitTM
    (fun input => left input ++ false :: (right input ++ [false]))
  simpa only [Function.comp_apply] using physical

private def fiveForbiddenComputedUnaryMinimumWord
    (left right : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  cappedUnaryMinimumOutput
    (fiveForbiddenComputedUnaryPairInput left right input)

private noncomputable def fiveFamilyForbiddenComputedUnaryMinimumComputable
    {left right : List Bool → List Bool}
    (hleft : BitTM left)
    (hright : BitTM right) :
    BitTM
      (fiveForbiddenComputedUnaryMinimumWord left right) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyForbiddenComputedUnaryPairInputComputable
      hleft hright)
    actualCappedUnaryMinimumComputable
  change BitTM
    (fun input => cappedUnaryMinimumOutput
      (fiveForbiddenComputedUnaryPairInput
        left right input))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyForbiddenComputedUnaryMinimumWord_valid
    (left right : List Bool → List Bool)
    (input : List Bool) (first second : ℕ)
    (hfirst : left input = List.replicate first true)
    (hsecond : right input = List.replicate second true) :
    fiveForbiddenComputedUnaryMinimumWord
      left right input = List.replicate (min first second) true := by
  unfold fiveForbiddenComputedUnaryMinimumWord
    fiveForbiddenComputedUnaryPairInput
  rw [hfirst, hsecond]
  simpa only [unarySourcePairWord, List.append_nil] using cappedUnaryMinimumOutput_pair first
      second []

/-- GapCVP reduction support. -/
def fiveFamilyForbiddenWindowSourceRank
    {T : ℕ} (window : Window T) : ℕ :=
  fiveFamilyFlatSourceRowMajorIndex window.1.1 window.1.2

private def fiveFamilyForbiddenCurrentTimeUnary
    (grid : Polynomial ℕ) : List Bool → List Bool :=
  fiveFlatIndexedOriginalQuotientUnary grid

private noncomputable def fiveFamilyForbiddenCurrentTimeUnaryComputable
    (grid : Polynomial ℕ) :
    BitTM
      (fiveFamilyForbiddenCurrentTimeUnary grid) :=
  fiveFamilyFlatIndexedOriginalQuotientUnaryComputable grid

private def fiveForbiddenCenterPositionUnary
    (grid : Polynomial ℕ) : List Bool → List Bool :=
  fiveFlatIndexedOriginalRemainderUnary grid

private noncomputable def fiveFamilyForbiddenCenterPositionUnaryComputable
    (grid : Polynomial ℕ) :
    BitTM
      (fiveForbiddenCenterPositionUnary grid) :=
  fiveFamilyFlatIndexedOriginalRemainderUnaryComputable grid

private def fiveForbiddenLeftPositionUnary
    (grid : Polynomial ℕ) (input : List Bool) : List Bool :=
  (fiveForbiddenCenterPositionUnary grid input).tail

private noncomputable def fiveFamilyForbiddenLeftPositionUnaryComputable
    (grid : Polynomial ℕ) :
    BitTM
      (fiveForbiddenLeftPositionUnary grid) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyForbiddenCenterPositionUnaryComputable grid)
    dropHeadComputable
  change BitTM
    (fun input =>
      (fiveForbiddenCenterPositionUnary grid input).tail)
  simpa only [Function.comp_def] using physical

private def fiveForbiddenLastPositionUnary
    (grid : Polynomial ℕ) (input : List Bool) : List Bool :=
  (fiveFlatIndexedOriginalPolynomialUnary grid input).tail

private noncomputable def fiveFamilyForbiddenLastPositionUnaryComputable
    (grid : Polynomial ℕ) :
    BitTM
      (fiveForbiddenLastPositionUnary grid) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFlatIndexedOriginalPolynomialUnaryComputable grid)
    dropHeadComputable
  change BitTM
    (fun input =>
      (fiveFlatIndexedOriginalPolynomialUnary grid input).tail)
  simpa only [Function.comp_def] using physical

private def fiveForbiddenRightCandidateUnary
    (grid : Polynomial ℕ) : List Bool → List Bool :=
  fiveForbiddenUnarySuccessorWord
    (fiveForbiddenCenterPositionUnary grid)

private noncomputable def fiveFamilyForbiddenRightCandidateUnaryComputable
    (grid : Polynomial ℕ) :
    BitTM
      (fiveForbiddenRightCandidateUnary grid) :=
  fiveForbiddenUnarySuccessorComputable
    (fiveFamilyForbiddenCenterPositionUnaryComputable grid)

private def fiveForbiddenRightPositionUnary
    (grid : Polynomial ℕ) : List Bool → List Bool :=
  fiveForbiddenComputedUnaryMinimumWord
    (fiveForbiddenRightCandidateUnary grid)
    (fiveForbiddenLastPositionUnary grid)

private noncomputable def fiveFamilyForbiddenRightPositionUnaryComputable
    (grid : Polynomial ℕ) :
    BitTM
      (fiveForbiddenRightPositionUnary grid) :=
  fiveFamilyForbiddenComputedUnaryMinimumComputable
    (fiveFamilyForbiddenRightCandidateUnaryComputable grid)
    (fiveFamilyForbiddenLastPositionUnaryComputable grid)

private def fiveFamilyForbiddenNextTimeUnary
    (grid : Polynomial ℕ) : List Bool → List Bool :=
  fiveForbiddenUnarySuccessorWord
    (fiveFamilyForbiddenCurrentTimeUnary grid)

private noncomputable def fiveFamilyForbiddenNextTimeUnaryComputable
    (grid : Polynomial ℕ) :
    BitTM
      (fiveFamilyForbiddenNextTimeUnary grid) :=
  fiveForbiddenUnarySuccessorComputable
    (fiveFamilyForbiddenCurrentTimeUnaryComputable grid)

private theorem fiveFamilyForbiddenCurrentTimeUnary_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (window : Window (rowWidth bound machine original)) :
    fiveFamilyForbiddenCurrentTimeUnary
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyForbiddenWindowSourceRank window) true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate window.1.1.val true := by
  have hgrid :
      0 < (fiveFamilyFlatIndexedGridPolynomial
        bound machine).eval original.length := by simp only
            [fiveFamilyFlatIndexedGridPolynomial_eval, lt_add_iff_pos_left, Order.lt_add_one_iff,
            zero_le]
  unfold fiveFamilyForbiddenCurrentTimeUnary
    fiveFamilyForbiddenWindowSourceRank
  rw [fiveFamilyFlatIndexedOriginalQuotientUnary_valid
    (fiveFamilyFlatIndexedGridPolynomial bound machine)
    (fiveFamilyFlatSourceRowMajorIndex
      window.1.1 window.1.2)
    original suffix hgrid,
    fiveFamilyFlatIndexedGridPolynomial_eval,
    fiveFamilyFlatSourceRowMajorIndex_div]

private theorem fiveFamilyForbiddenCenterPositionUnary_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (window : Window (rowWidth bound machine original)) :
    fiveForbiddenCenterPositionUnary
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyForbiddenWindowSourceRank window) true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate window.1.2.val true := by
  have hgrid :
      0 < (fiveFamilyFlatIndexedGridPolynomial
        bound machine).eval original.length := by simp only
            [fiveFamilyFlatIndexedGridPolynomial_eval, lt_add_iff_pos_left, Order.lt_add_one_iff,
            zero_le]
  unfold fiveForbiddenCenterPositionUnary
    fiveFamilyForbiddenWindowSourceRank
  rw [fiveFamilyFlatIndexedOriginalRemainderUnary_valid
    (fiveFamilyFlatIndexedGridPolynomial bound machine)
    (fiveFamilyFlatSourceRowMajorIndex
      window.1.1 window.1.2)
    original suffix hgrid,
    fiveFamilyFlatIndexedGridPolynomial_eval,
    fiveFamilyFlatSourceRowMajorIndex_mod]

private theorem fiveFamilyForbiddenLeftPositionUnary_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (window : Window (rowWidth bound machine original)) :
    fiveForbiddenLeftPositionUnary
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyForbiddenWindowSourceRank window) true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate (leftPosition window).val true := by
  unfold fiveForbiddenLeftPositionUnary
  rw [fiveFamilyForbiddenCenterPositionUnary_valid
    bound machine original suffix window]
  change (List.replicate window.1.2.val true).tail =
    List.replicate (window.1.2.val - 1) true
  cases window.1.2.val with
  | zero => rfl
  | succ position =>
      simp only [List.replicate_succ, List.tail_cons, add_tsub_cancel_right]

private theorem fiveFamilyForbiddenLastPositionUnary_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (window : Window (rowWidth bound machine original)) :
    fiveForbiddenLastPositionUnary
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyForbiddenWindowSourceRank window) true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate (rowWidth bound machine original) true := by
  unfold fiveForbiddenLastPositionUnary
  rw [fiveFamilyFlatIndexedOriginalPolynomialUnary_valid
    (fiveFamilyFlatIndexedGridPolynomial bound machine)
    (fiveFamilyForbiddenWindowSourceRank window)
    original suffix,
    fiveFamilyFlatIndexedGridPolynomial_eval]
  simp only [List.replicate_succ, List.tail_cons]

private theorem fiveFamilyForbiddenRightCandidateUnary_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (window : Window (rowWidth bound machine original)) :
    fiveForbiddenRightCandidateUnary
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyForbiddenWindowSourceRank window) true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate (window.1.2.val + 1) true := by
  unfold fiveForbiddenRightCandidateUnary
    fiveForbiddenUnarySuccessorWord
  rw [fiveFamilyForbiddenCenterPositionUnary_valid
    bound machine original suffix window]
  simp only [List.replicate_succ]

private theorem fiveFamilyForbiddenRightPositionUnary_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (window : Window (rowWidth bound machine original)) :
    fiveForbiddenRightPositionUnary
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyForbiddenWindowSourceRank window) true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate (rightPosition window).val true := by
  unfold fiveForbiddenRightPositionUnary
  rw [fiveFamilyForbiddenComputedUnaryMinimumWord_valid
    (fiveForbiddenRightCandidateUnary
      (fiveFamilyFlatIndexedGridPolynomial bound machine))
    (fiveForbiddenLastPositionUnary
      (fiveFamilyFlatIndexedGridPolynomial bound machine))
    (lengthPrefixedWord
      (List.replicate
        (fiveFamilyForbiddenWindowSourceRank window) true) ++
      lengthPrefixedWord original ++ suffix)
    (window.1.2.val + 1) (rowWidth bound machine original)
    (fiveFamilyForbiddenRightCandidateUnary_valid
      bound machine original suffix window)
    (fiveFamilyForbiddenLastPositionUnary_valid
      bound machine original suffix window)]
  rfl

private theorem fiveFamilyForbiddenNextTimeUnary_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (window : Window (rowWidth bound machine original)) :
    fiveFamilyForbiddenNextTimeUnary
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyForbiddenWindowSourceRank window) true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate (nextTime window).val true := by
  unfold fiveFamilyForbiddenNextTimeUnary
    fiveForbiddenUnarySuccessorWord
  rw [fiveFamilyForbiddenCurrentTimeUnary_valid
    bound machine original suffix window]
  simp only [nextTime, List.replicate_succ]

private def fiveForbiddenCoordinateTimeUnary
    (grid : Polynomial ℕ) :
    FiveFamilyForbiddenWindowCoordinate → List Bool → List Bool
  | .left | .center | .right =>
      fiveFamilyForbiddenCurrentTimeUnary grid
  | .next => fiveFamilyForbiddenNextTimeUnary grid

private noncomputable def fiveFamilyForbiddenCoordinateTimeUnaryComputable
    (grid : Polynomial ℕ)
    (coordinate : FiveFamilyForbiddenWindowCoordinate) :
    BitTM
      (fiveForbiddenCoordinateTimeUnary grid coordinate) := by
  cases coordinate with
  | left | center | right =>
      exact fiveFamilyForbiddenCurrentTimeUnaryComputable grid
  | next => exact fiveFamilyForbiddenNextTimeUnaryComputable grid

private def fiveForbiddenCoordinatePositionUnary
    (grid : Polynomial ℕ) :
    FiveFamilyForbiddenWindowCoordinate → List Bool → List Bool
  | .left => fiveForbiddenLeftPositionUnary grid
  | .center | .next => fiveForbiddenCenterPositionUnary grid
  | .right => fiveForbiddenRightPositionUnary grid

private noncomputable def fiveFamilyForbiddenCoordinatePositionUnaryComputable
    (grid : Polynomial ℕ)
    (coordinate : FiveFamilyForbiddenWindowCoordinate) :
    BitTM
      (fiveForbiddenCoordinatePositionUnary grid coordinate) := by
  cases coordinate with
  | left => exact fiveFamilyForbiddenLeftPositionUnaryComputable grid
  | center | next =>
      exact fiveFamilyForbiddenCenterPositionUnaryComputable grid
  | right => exact fiveFamilyForbiddenRightPositionUnaryComputable grid

private def fiveForbiddenCoordinatePositionSymbolCode
    (grid : Polynomial ℕ)
    (coordinate : FiveFamilyForbiddenWindowCoordinate)
    (symbol : ℕ) (input : List Bool) : List Bool :=
  unarySourcePairOutput
    (fiveForbiddenComputedUnaryPairInput
      (fiveForbiddenCoordinatePositionUnary grid coordinate)
      (fun _ => List.replicate symbol true) input)

private noncomputable def fiveFamilyForbiddenCoordinatePositionSymbolCodeComputable
    (grid : Polynomial ℕ)
    (coordinate : FiveFamilyForbiddenWindowCoordinate)
    (symbol : ℕ) :
    BitTM
      (fiveForbiddenCoordinatePositionSymbolCode
        grid coordinate symbol) := by
  have query := fiveFamilyForbiddenComputedUnaryPairInputComputable
    (fiveFamilyForbiddenCoordinatePositionUnaryComputable
      grid coordinate)
    (constantWordComputable (List.replicate symbol true))
  have physical := GapCVP.TMComposition.computableInPolyTime
    query actualUnaryPairIndexComputable
  change BitTM
    (fun input => unarySourcePairOutput
      (fiveForbiddenComputedUnaryPairInput
        (fiveForbiddenCoordinatePositionUnary grid coordinate)
        (fun _ => List.replicate symbol true) input))
  simpa only [Function.comp_def] using physical

/-- Internal support shared across GapCVP continuation modules. -/
def fiveForbiddenCoordinateSourceVariableCode
    (grid : Polynomial ℕ)
    (coordinate : FiveFamilyForbiddenWindowCoordinate)
    (symbol : ℕ) (input : List Bool) : List Bool :=
  unarySourcePairOutput
    (fiveForbiddenComputedUnaryPairInput
      (fiveForbiddenCoordinateTimeUnary grid coordinate)
      (fiveForbiddenCoordinatePositionSymbolCode
        grid coordinate symbol) input)

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def fiveFamilyForbiddenCoordinateSourceVariableCodeComputable
    (grid : Polynomial ℕ)
    (coordinate : FiveFamilyForbiddenWindowCoordinate)
    (symbol : ℕ) :
    BitTM
      (fiveForbiddenCoordinateSourceVariableCode
        grid coordinate symbol) := by
  have query := fiveFamilyForbiddenComputedUnaryPairInputComputable
    (fiveFamilyForbiddenCoordinateTimeUnaryComputable
      grid coordinate)
    (fiveFamilyForbiddenCoordinatePositionSymbolCodeComputable
      grid coordinate symbol)
  have physical := GapCVP.TMComposition.computableInPolyTime
    query actualUnaryPairIndexComputable
  change BitTM
    (fun input => unarySourcePairOutput
      (fiveForbiddenComputedUnaryPairInput
        (fiveForbiddenCoordinateTimeUnary grid coordinate)
        (fiveForbiddenCoordinatePositionSymbolCode
          grid coordinate symbol) input))
  simpa only [Function.comp_def] using physical

/-- GapCVP reduction support. -/
def fiveForbiddenWindowSourceVariable
    {T S : ℕ}
    (window : Window T)
    (symbols : WindowSymbols S) :
    FiveFamilyForbiddenWindowCoordinate → Variable T S
  | .left => (window.1.1, leftPosition window, symbols.1)
  | .center => (window.1.1, window.1.2, symbols.2.1)
  | .right => (window.1.1, rightPosition window, symbols.2.2.1)
  | .next => (nextTime window, window.1.2, symbols.2.2.2)

/-- GapCVP reduction support. -/
def fiveFamilyForbiddenWindowSlotSymbol
    {S : ℕ} (symbols : WindowSymbols S) :
    FiveFamilyForbiddenWindowCoordinate → Symbol S
  | .left => symbols.1
  | .center => symbols.2.1
  | .right => symbols.2.2.1
  | .next => symbols.2.2.2

private theorem fiveFamilyForbiddenCoordinateTimeUnary_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (window : Window (rowWidth bound machine original))
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm))
    (coordinate : FiveFamilyForbiddenWindowCoordinate) :
    fiveForbiddenCoordinateTimeUnary
      (fiveFamilyFlatIndexedGridPolynomial bound machine) coordinate
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyForbiddenWindowSourceRank window) true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate
        (fiveForbiddenWindowSourceVariable
          window symbols coordinate).1.val true := by
  cases coordinate with
  | left | center | right =>
      exact fiveFamilyForbiddenCurrentTimeUnary_valid
        bound machine original suffix window
  | next =>
      exact fiveFamilyForbiddenNextTimeUnary_valid
        bound machine original suffix window

private theorem fiveFamilyForbiddenCoordinatePositionUnary_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (window : Window (rowWidth bound machine original))
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm))
    (coordinate : FiveFamilyForbiddenWindowCoordinate) :
    fiveForbiddenCoordinatePositionUnary
      (fiveFamilyFlatIndexedGridPolynomial bound machine) coordinate
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyForbiddenWindowSourceRank window) true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate
        (fiveForbiddenWindowSourceVariable
          window symbols coordinate).2.1.val true := by
  cases coordinate with
  | left =>
      exact fiveFamilyForbiddenLeftPositionUnary_valid
        bound machine original suffix window
  | center | next =>
      exact fiveFamilyForbiddenCenterPositionUnary_valid
        bound machine original suffix window
  | right =>
      exact fiveFamilyForbiddenRightPositionUnary_valid
        bound machine original suffix window

theorem fiveFamilyForbiddenCoordinateSourceVariableCode_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (window : Window (rowWidth bound machine original))
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm))
    (coordinate : FiveFamilyForbiddenWindowCoordinate) :
    fiveForbiddenCoordinateSourceVariableCode
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      coordinate (fiveFamilyForbiddenWindowSlotSymbol
        symbols coordinate).val
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyForbiddenWindowSourceRank window) true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate
        (Encodable.encode
          (fiveForbiddenWindowSourceVariable
            window symbols coordinate)) true := by
  let query := lengthPrefixedWord
    (List.replicate
      (fiveFamilyForbiddenWindowSourceRank window) true) ++
      lengthPrefixedWord original ++ suffix
  let atom := fiveForbiddenWindowSourceVariable
    window symbols coordinate
  have htime :
      fiveForbiddenCoordinateTimeUnary
        (fiveFamilyFlatIndexedGridPolynomial bound machine)
        coordinate query =
        List.replicate atom.1.val true :=
    fiveFamilyForbiddenCoordinateTimeUnary_valid
      bound machine original suffix window symbols coordinate
  have hposition :
      fiveForbiddenCoordinatePositionUnary
        (fiveFamilyFlatIndexedGridPolynomial bound machine)
        coordinate query =
        List.replicate atom.2.1.val true :=
    fiveFamilyForbiddenCoordinatePositionUnary_valid
      bound machine original suffix window symbols coordinate
  have hsymbol :
      (fiveFamilyForbiddenWindowSlotSymbol
        symbols coordinate).val = atom.2.2.val := by
    cases coordinate <;> rfl
  unfold fiveForbiddenCoordinateSourceVariableCode
    fiveForbiddenCoordinatePositionSymbolCode
    fiveForbiddenComputedUnaryPairInput
  change
    unarySourcePairOutput
      (fiveForbiddenCoordinateTimeUnary
          (fiveFamilyFlatIndexedGridPolynomial bound machine)
          coordinate query ++
        false ::
          (unarySourcePairOutput
            (fiveForbiddenCoordinatePositionUnary
                (fiveFamilyFlatIndexedGridPolynomial bound machine)
                coordinate query ++
              false ::
                (List.replicate
                    (fiveFamilyForbiddenWindowSlotSymbol
                      symbols coordinate).val true ++ [false])) ++
            [false])) =
      List.replicate (Encodable.encode atom) true
  rw [htime, hposition, hsymbol]
  have hinner :
      unarySourcePairOutput
        (List.replicate atom.2.1.val true ++
          false ::
            (List.replicate atom.2.2.val true ++ [false])) =
        List.replicate
          (Nat.pair atom.2.1.val atom.2.2.val) true :=
    unarySourcePairOutput_word atom.2.1.val atom.2.2.val
  rw [hinner]
  change unarySourcePairOutput
    (unarySourcePairWord atom.1.val
      (Nat.pair atom.2.1.val atom.2.2.val)) = _
  rw [unarySourcePairOutput_word]
  rfl

end CNFFiveFamilyForbiddenWindowCoordinateTM

end GapCVP

end
