/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part07E

/-! # GapCVP proof, part 07, continuation 06 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFFiveFamilyForbiddenWholeClauseExactSourceTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceUniformTuringTM

open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatSourceGridDescriptorTM

open GapCVP.CNFFlatPhysicalBinaryAppendTM

open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM

open GapCVP.CNFFiveFamilyForbiddenWholeClauseWorkerTM

open GapCVP.CNFFiveFamilyForbiddenWholeClauseSourceCert

end CNFFiveFamilyForbiddenWholeClauseExactSourceTM

namespace CNFFiveFamilyIndependentAnchoredFamilyStreamTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert
open GapCVP.SourceUniformTuringTM GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceCanonicalUnaryGridIndexTM
open GapCVP.SourceAnchoredGridRecordFoldTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFBoundedRecordFoldTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFFiveFamilyFlatIndexedCatalogueTM

/-- GapCVP reduction support. -/
def fiveIndependentSourceCountWord
    (count : Polynomial ℕ) (original : List Bool) : List Bool :=
  List.replicate (count.eval original.length) true

/-- GapCVP reduction support. -/
noncomputable def fiveFamilyIndependentSourceCountComputable
    (count : Polynomial ℕ) :
    BitTM
      (fiveIndependentSourceCountWord count) :=
  polynomialValueUnaryComputable count

private def fiveIndependentSourceRankDescriptorWord
    (count : Polynomial ℕ) (original : List Bool) : List Bool :=
  sourceCanonicalUnaryGridIndexOutput
    (fiveIndependentSourceCountWord count original ++ [false])

private noncomputable def fiveFamilyIndependentSourceRankDescriptorComputable
    (count : Polynomial ℕ) :
    BitTM
      (fiveIndependentSourceRankDescriptorWord count) := by
  have query := pointwiseAppendComputable
    (fiveFamilyIndependentSourceCountComputable count)
    (constantWordComputable [false])
  have physical := GapCVP.TMComposition.computableInPolyTime
    query sourceCanonicalUnaryGridIndexComputable
  change BitTM
    (fun original => sourceCanonicalUnaryGridIndexOutput
      (fiveIndependentSourceCountWord
        count original ++ [false]))
  simpa only [Function.comp_def] using physical

/-- GapCVP reduction support. -/
def fiveIndependentSourceRankWords
    (count : ℕ) : List (List Bool) :=
  (List.range count).map fun rank => List.replicate rank true

@[simp] private theorem fiveFamilyIndependentSourceRankWords_descriptors
    (count : ℕ) :
    (fiveIndependentSourceRankWords count).flatMap
        lengthPrefixedWord =
      sourceCanonicalUnaryGridIndexDescriptors count := by
  simp only [fiveIndependentSourceRankWords,
    sourceCanonicalUnaryGridIndexDescriptors, List.flatMap_map]
  rfl

@[simp] private theorem fiveFamilyIndependentSourceRankDescriptorWord_valid
    (count : Polynomial ℕ) (original : List Bool) :
    fiveIndependentSourceRankDescriptorWord
        count original =
      sourceCanonicalUnaryGridIndexDescriptors
        (count.eval original.length) := by
  simp only [fiveIndependentSourceRankDescriptorWord, fiveIndependentSourceCountWord,
      sourceCanonicalUnaryGridIndexOutput_valid, List.append_nil]

private def fiveIndependentAnchoredFamilyFoldInput
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  fiveIndependentSourceCountWord count original ++
    false ::
      (lengthPrefixedWord
        (fiveFlatOriginalSourceAnchorWord
          bound machine original) ++
        fiveIndependentSourceRankDescriptorWord
          count original)

private noncomputable def fiveFamilyIndependentAnchoredFamilyFoldInputComputable
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentAnchoredFamilyFoldInput
        bound count machine) := by
  have anchor := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatOriginalSourceAnchorComputable bound machine)
    structuralPrefixWriterComputable
  have seed := pointwiseAppendComputable
    anchor (fiveFamilyIndependentSourceRankDescriptorComputable count)
  have delimiter := GapCVP.TMComposition.computableInPolyTime
    seed (prependBitComputable false)
  have physical := pointwiseAppendComputable
    (fiveFamilyIndependentSourceCountComputable count) delimiter
  change BitTM
    (fun original =>
      fiveIndependentSourceCountWord count original ++
        false ::
          (lengthPrefixedWord
            (fiveFlatOriginalSourceAnchorWord
              bound machine original) ++
            fiveIndependentSourceRankDescriptorWord
              count original))
  simpa only [Function.comp_def] using physical

private def fiveIndependentAnchoredFamilyCatalogueWord
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (candidate : List Bool → List Bool)
    (original : List Bool) : List Bool :=
  boundedRecordFoldOutput
    (sourceAnchoredGridRecordRotationOutput candidate)
    (fiveIndependentAnchoredFamilyFoldInput
      bound count machine original)

private noncomputable def fiveFamilyIndependentAnchoredFamilyCatalogueComputable
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (fiveIndependentAnchoredFamilyCatalogueWord
        bound count machine candidate) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyIndependentAnchoredFamilyFoldInputComputable
      bound count machine)
    (sourceAnchoredGridRecordFoldComputable computer)
  change BitTM
    (fun original =>
      boundedRecordFoldOutput
        (sourceAnchoredGridRecordRotationOutput candidate)
        (fiveIndependentAnchoredFamilyFoldInput
          bound count machine original))
  simpa only [Function.comp_def] using physical

private theorem fiveFamilyIndependentAnchoredFamilyCatalogueWord_valid
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (candidate : List Bool → List Bool)
    (original : List Bool)
    (hfit : ∀ rank : Fin (count.eval original.length),
      (candidate
        (lengthPrefixedWord (List.replicate rank.val true) ++
          fiveFlatOriginalSourceAnchorWord
            bound machine original)).length ≤
        (fiveFlatOriginalSourceAnchorWord
          bound machine original).length) :
    fiveIndependentAnchoredFamilyCatalogueWord
        bound count machine candidate original =
      lengthPrefixedWord
        (fiveFlatOriginalSourceAnchorWord
          bound machine original) ++
        (fiveIndependentSourceRankWords
          (count.eval original.length)).flatMap
            (fun rank => lengthPrefixedWord
              (candidate (lengthPrefixedWord rank ++
                fiveFlatOriginalSourceAnchorWord
                  bound machine original))) := by
  let size := count.eval original.length
  let ranks := fiveIndependentSourceRankWords size
  have hranks : ranks.length = size := by
    simp only [fiveIndependentSourceRankWords, List.length_map, List.length_range, ranks]
  have hfit' : ∀ rank ∈ ranks,
      (candidate
        (lengthPrefixedWord rank ++
          fiveFlatOriginalSourceAnchorWord
            bound machine original)).length ≤
        (fiveFlatOriginalSourceAnchorWord
          bound machine original).length := by
    intro rank hrank
    obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hrank
    have hlt : index < size := by
      simpa only [List.mem_range] using hindex
    exact hfit ⟨index, hlt⟩
  have hseed :
      fiveIndependentAnchoredFamilyFoldInput
        bound count machine original =
        unaryBoundedFoldWord ranks.length
          (lengthPrefixedWord
              (fiveFlatOriginalSourceAnchorWord
                bound machine original) ++
            ranks.flatMap lengthPrefixedWord ++ []) := by
    simp only [fiveIndependentAnchoredFamilyFoldInput, fiveIndependentSourceCountWord,
        fiveFamilyIndependentSourceRankDescriptorWord_valid, unaryBoundedFoldWord, hranks,
        fiveFamilyIndependentSourceRankWords_descriptors, List.append_nil, ranks, size]
  unfold fiveIndependentAnchoredFamilyCatalogueWord
  rw [hseed,
    boundedRecordFoldOutput_sourceAnchoredGridRecordRanks
      candidate
      (fiveFlatOriginalSourceAnchorWord
        bound machine original)
      ranks [] hfit']
  simp only [List.append_nil, ranks, size]

/-- GapCVP reduction support. -/
def fiveIndependentAnchoredFamilyBundledStreamWord
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (candidate : List Bool → List Bool)
    (original : List Bool) : List Bool :=
  firstFieldSuffix
    (fiveIndependentAnchoredFamilyCatalogueWord
      bound count machine candidate original)

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def fiveIndependentAnchoredFamilyBundledStreamComputable
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (fiveIndependentAnchoredFamilyBundledStreamWord
        bound count machine candidate) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyIndependentAnchoredFamilyCatalogueComputable
      bound count machine computer)
    firstFieldSuffixComputable
  change BitTM
    (fun original => firstFieldSuffix
      (fiveIndependentAnchoredFamilyCatalogueWord
        bound count machine candidate original))
  simpa only [Function.comp_def] using physical

theorem fiveFamilyIndependentAnchoredFamilyBundledStreamWord_valid
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (candidate : List Bool → List Bool)
    (original : List Bool)
    (hfit : ∀ rank : Fin (count.eval original.length),
      (candidate
        (lengthPrefixedWord (List.replicate rank.val true) ++
          fiveFlatOriginalSourceAnchorWord
            bound machine original)).length ≤
        (fiveFlatOriginalSourceAnchorWord
          bound machine original).length) :
    fiveIndependentAnchoredFamilyBundledStreamWord
        bound count machine candidate original =
      (fiveIndependentSourceRankWords
        (count.eval original.length)).flatMap
          (fun rank => lengthPrefixedWord
            (candidate (lengthPrefixedWord rank ++
              fiveFlatOriginalSourceAnchorWord
                bound machine original))) := by
  unfold fiveIndependentAnchoredFamilyBundledStreamWord
  rw [fiveFamilyIndependentAnchoredFamilyCatalogueWord_valid
    bound count machine candidate original hfit]
  exact firstFieldSuffix_valid
    (fiveFlatOriginalSourceAnchorWord bound machine original)
    ((fiveIndependentSourceRankWords
      (count.eval original.length)).flatMap
        (fun rank => lengthPrefixedWord
          (candidate (lengthPrefixedWord rank ++
            fiveFlatOriginalSourceAnchorWord
              bound machine original))))

end CNFFiveFamilyIndependentAnchoredFamilyStreamTM

namespace CNFFiveFamilyIndependentFiveFamilyBundledCatalogueTM

open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLCellRowBounds GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding
open GapCVP.SourceUniformTuringTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFiveFamilyFlatCandidateGenerationTM
open GapCVP.CNFFiveFamilyFlatIndexedCatalogueTM GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM
open GapCVP.CNFFiveFamilyFlatRowMajorCatalogueTM
open GapCVP.CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM
open GapCVP.CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM
open GapCVP.CNFFiveFamilyFlatAcceptanceClauseFoldTM
open GapCVP.CNFFiveFamilyPackedInitialCellDecoderTM
open GapCVP.CNFFiveFamilyForbiddenWholeClauseExactSourceTM
open GapCVP.CNFFiveFamilyIndependentAnchoredFamilyStreamTM

theorem fiveFamilyActualAnnotatedRecord_fits_originalAnchor
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (clause : Clause
      (rowWidth bound machine original)
      (completePhaseSymbolCount machine.tm)) :
    (flatSourceClauseAnnotatedRecord clause).length ≤
      (fiveFlatOriginalSourceAnchorWord
        bound machine original).length := by
  have hbound := flatSourceClauseAnnotatedRecord_length_le clause
  have hpolynomial := flatSourceAnnotatedClauseLengthBound_eq_polynomial
    bound machine original
  change
    (flatSourceClauseAnnotatedRecord clause).length ≤
      flatSourceAnnotatedClauseLengthBound
        (rowWidth bound machine original)
        (completePhaseSymbolCount machine.tm) at hbound
  rw [hpolynomial] at hbound
  simp only [fiveFlatOriginalSourceAnchorWord,
    List.length_append, List.length_replicate]
  omega

end CNFFiveFamilyIndependentFiveFamilyBundledCatalogueTM

end GapCVP

end
