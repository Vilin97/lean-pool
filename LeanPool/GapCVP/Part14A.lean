/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part13

/-! # GapCVP proof, part 14 -/

noncomputable section

open StateTransition (EvalsToInTime)
open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace BinarySelectedIrreducibleWordOrderCorrectness

open GapCVP.BinaryAllWordRankOrder GapCVP.BinaryFieldBasis GapCVP.BinaryModularReductionTM
open GapCVP.BinarySelectedIrreducibleWordTM GapCVP.Core.EffectiveBinaryField

/-- Internal support shared across GapCVP continuation modules. -/
theorem finiteWordBits_monicWord
    {degree : ℕ} (hdegree : 0 < degree)
    (lower : Word degree) :
    finiteWordBits (monicWord lower) =
      finiteWordBits lower ++
        ([true] ++ List.replicate (degree - 1) false) := by
  apply List.ext_getElem
  · simp only [finiteWordBits, List.length_map, List.length_finRange, List.cons_append,
      List.nil_append,
        List.length_append, List.length_cons, List.length_replicate]
    omega
  · intro index hleft hright
    by_cases hlow : index < degree
    · simp only [finiteWordBits, List.getElem_map, monicWord, List.getElem_finRange, Fin.cast_mk,
        hlow, ↓reduceDIte,
          List.cons_append, List.nil_append, List.length_map, List.length_finRange,
              List.getElem_append_left]
    · by_cases htop : index = degree
      · subst index
        simp only [finiteWordBits, List.getElem_map, monicWord, List.getElem_finRange, Fin.cast_mk,
            lt_self_iff_false,
            ↓reduceDIte, decide_true, List.cons_append, List.nil_append, List.length_map,
                List.length_finRange, Std.le_refl,
            List.getElem_append_right, tsub_self, List.getElem_cons_zero]
      · have hge : degree ≤ index := Nat.le_of_not_gt hlow
        have hgt : degree < index := by omega
        simp only [finiteWordBits, List.getElem_map, monicWord, List.getElem_finRange, Fin.cast_mk,
            hlow, ↓reduceDIte,
            htop, decide_false, List.cons_append, List.nil_append, Bool.false_eq]
        rw [List.getElem_append_right (by
          simpa only [List.length_map, List.length_finRange] using hge)]
        have hpositive : 0 < index - degree := Nat.sub_pos_of_lt hgt
        cases hdifference : index - degree with
        | zero => omega
        | succ remaining => simp only [List.length_map, List.length_finRange, hdifference,
            List.getElem_cons_succ, List.getElem_replicate]

private theorem factor400IndexedIrreducibleCandidateMarkers_eq_finRange
    (degree : ℕ) :
    binaryIndexedIrreducibleCandidateMarkers degree =
      (List.finRange (2 ^ degree)).map
        (fun rank => noProperFactors degree
          (indexedWord degree rank)) := by
  unfold binaryIndexedIrreducibleCandidateMarkers
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  apply List.map_congr_left
  intro rank _
  simp only [Function.comp_apply, binaryIndexedNoProperFactorsBit, rank.isLt, ↓reduceDIte, Fin.eta]

private theorem finRange_idxOfOption_eq_some
    {count : ℕ} (rank : Fin count) :
    (List.finRange count).idxOf? rank = some rank.val := by
  exact GapCVP.GaussianAdaptiveEliminationCorrectness.finRange_idxOfOption_eq_some rank

private theorem finRange_findIdxOption_of_findOption
    {count : ℕ}
    (predicate : Fin count → Bool)
    (rank : Fin count)
    (hfound : (List.finRange count).find? predicate = some rank) :
    (List.finRange count).findIdx? predicate = some rank.val := by
  rw [List.findIdx?_eq_bind_find?_idxOf?, hfound]
  exact finRange_idxOfOption_eq_some rank

private theorem factor400IndexedIrreducibleCandidateMarkers_findIdxOption
    (degree : ℕ)
    (rank : Fin (2 ^ degree))
    (hfound :
      (List.finRange (2 ^ degree)).find?
        (fun candidate => noProperFactors degree
          (indexedWord degree candidate)) = some rank) :
    (binaryIndexedIrreducibleCandidateMarkers degree).findIdx?
        id = some rank.val := by
  rw [factor400IndexedIrreducibleCandidateMarkers_eq_finRange,
    List.findIdx?_map]
  simpa only [CompTriple.comp_eq] using
      finRange_findIdxOption_of_findOption
        (fun candidate : Fin (2 ^ degree) => noProperFactors degree (indexedWord degree candidate))
            rank hfound

private theorem findIrreducibleWordOption_eq_finRange_findOption
    (degree : ℕ) :
    findIrreducibleWordOption degree =
      ((List.finRange (2 ^ degree)).find?
        (fun rank => noProperFactors degree
          (indexedWord degree rank))).map
            (indexedWord degree) := by
  unfold findIrreducibleWordOption
  rw [allWords_eq_finRange_indexedWord,
    List.find?_map]
  rfl

/-- Internal support shared across GapCVP continuation modules. -/
theorem exists_first_source_irreducible_rank
    (degree : ℕ) (hdegree : 0 < degree) :
    ∃ rank : Fin (2 ^ degree),
      (binaryIndexedIrreducibleCandidateMarkers
        degree).findIdx? id = some rank.val ∧
      indexedWord degree rank = irreducibleWord degree := by
  obtain ⟨word, hword, _⟩ :=
    findIrreducibleWordOption_exists degree hdegree
  rw [findIrreducibleWordOption_eq_finRange_findOption] at hword
  cases hfound :
      (List.finRange (2 ^ degree)).find?
        (fun rank => noProperFactors degree
          (indexedWord degree rank)) with
  | none =>
      simp only [hfound, Option.map_none, reduceCtorEq] at hword
  | some rank =>
      have hrank : indexedWord degree rank = word := by
        simpa only [hfound, Option.map_some, Option.some.injEq] using hword
      refine ⟨rank,
        factor400IndexedIrreducibleCandidateMarkers_findIdxOption
          degree rank hfound, ?_⟩
      unfold irreducibleWord
      have horiginal : findIrreducibleWordOption degree = some word := by
        rw [findIrreducibleWordOption_eq_finRange_findOption, hfound]
        simp only [Option.map_some, hrank]
      rw [horiginal]
      exact hrank

end BinarySelectedIrreducibleWordOrderCorrectness

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

/-- GapCVP reduction support. -/
abbrev sourceIrreducibleFormulaDegree (formula : ThreeCNF) : ℕ :=
  GapCVP.Core.sourceFieldExponent
    (GapCVP.Core.sourceSizeParameter
      (encodeThreeCNF formula).length
      (srcFormula formula))

private def sourceIrreducibleRankDegreeUnary : List Bool → List Bool :=
  physicalFamilyFieldDegreeUnary ∘ binaryIrreducibleRankOriginal

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleRankDegreeUnaryComputable :
    BitTM
    sourceIrreducibleRankDegreeUnary :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    factor400BinaryIrreducibleRankOriginalComputable
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable

private theorem paperVariableAritySourceIrreducibleRankDegreeUnary_query
    (formula : ThreeCNF) (rank : ℕ) (auxiliary : List Bool) :
    sourceIrreducibleRankDegreeUnary
      (lengthPrefixedWord (List.replicate rank true) ++
        lengthPrefixedWord auxiliary ++ encodeThreeCNF formula) =
      List.replicate
        (sourceIrreducibleFormulaDegree formula) true := by
  unfold sourceIrreducibleRankDegreeUnary
  rw [Function.comp_apply,
    factor400BinaryIrreducibleRankOriginal_valid,
    paperVariableArityPhysicalFamilyFieldDegreeUnary_valid]

private noncomputable def sourceIrreducibleRankDegreeWidth :
    SourceQaryMaskDynamicGridWidth :=
  factor400BinaryIrreduciblePhysicalDynamicWidth
    paperVariableAritySourceIrreducibleRankDegreeUnaryComputable

@[simp] private theorem paperVariableAritySourceIrreducibleRankDegreeWidth_output
    (input : List Bool) :
    sourceIrreducibleRankDegreeWidth.output input =
      sourceIrreducibleRankDegreeUnary input := by
  exact factor400BinaryIrreduciblePhysicalDynamicWidth_output
    paperVariableAritySourceIrreducibleRankDegreeUnaryComputable input

/-- Internal support shared across GapCVP continuation modules. -/
def sourceIrreducibleRankCoefficientWord : List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    sourceIrreducibleRankDegreeWidth
    factor400BinaryIrreducibleCoefficientBitComputable

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableAritySourceIrreducibleRankCoefficientWordComputable :
    BitTM
    sourceIrreducibleRankCoefficientWord :=
  factor400BinaryIrreduciblePhysicalDynamicCatalogueComputer
    sourceIrreducibleRankDegreeWidth
    factor400BinaryIrreducibleCoefficientBitComputable

private theorem paperVariableAritySourceIrreducibleCoefficientBitWord_query
    (width : SourceQaryMaskDynamicGridWidth)
    (formula : ThreeCNF) (rank bitRank : ℕ)
    (auxiliary : List Bool) :
    binaryIrreducibleCoefficientBitWord
      (lengthPrefixedWord (List.replicate bitRank true) ++
        sourceQaryMaskDynamicGridBaseSource width
          (lengthPrefixedWord (List.replicate rank true) ++
            lengthPrefixedWord auxiliary ++
              encodeThreeCNF formula)) =
      [rank.testBit bitRank] := by
  let outer := lengthPrefixedWord (List.replicate rank true) ++
    lengthPrefixedWord auxiliary ++ encodeThreeCNF formula
  let inner := lengthPrefixedWord (List.replicate bitRank true) ++
    sourceQaryMaskDynamicGridBaseSource width outer
  have hbit : factor400BinaryIrreducibleRankUnary inner =
      List.replicate bitRank true := by
    dsimp [inner, factor400BinaryIrreducibleRankUnary]
    exact firstFieldContents_valid
      (List.replicate bitRank true)
      (sourceQaryMaskDynamicGridBaseSource width outer)
  have houter :
      binaryIrreducibleCoefficientOuterSource inner = outer := by
    simp only [binaryIrreducibleCoefficientOuterSource, binaryIrreducibleRankOriginal,
        sourceQaryMaskDynamicGridBaseSource, Function.comp_apply, firstFieldSuffix_valid, inner]
  have hrank :
      binaryIrreducibleRankBinary outer =
        Computability.encodeNat rank := by
    simp only [binaryIrreducibleRankBinary, List.append_assoc, Function.comp_apply,
        factor400BinaryIrreducibleRankUnary, firstFieldContents_valid, List.length_replicate,
            outer]
  change binaryIrreducibleCoefficientBitWord inner = _
  unfold binaryIrreducibleCoefficientBitWord
  rw [fiveOriginalDynamicBitWord_valid
    factor400BinaryIrreducibleRankUnary
    factor400BinaryIrreducibleCoefficientRankBinary
    inner bitRank hbit]
  change
    [((binaryIrreducibleRankBinary
      (binaryIrreducibleCoefficientOuterSource inner)).drop
        bitRank).headD false] = _
  rw [houter, hrank, factor400Irreducible_encodeNat_drop_head]

private theorem paperVariableAritySourceIrreducibleRankCoefficientWord_query
    (formula : ThreeCNF) (rank : ℕ) (auxiliary : List Bool) :
    sourceIrreducibleRankCoefficientWord
      (lengthPrefixedWord (List.replicate rank true) ++
        lengthPrefixedWord auxiliary ++ encodeThreeCNF formula) =
      (List.range
        (sourceIrreducibleFormulaDegree formula)).map
          (fun bitRank => rank.testBit bitRank) := by
  let outer := lengthPrefixedWord (List.replicate rank true) ++
    lengthPrefixedWord auxiliary ++ encodeThreeCNF formula
  let degree := sourceIrreducibleFormulaDegree formula
  have hdegree :
      sourceIrreducibleRankDegreeWidth.output outer =
        List.replicate degree true := by
    rw [paperVariableAritySourceIrreducibleRankDegreeWidth_output]
    exact paperVariableAritySourceIrreducibleRankDegreeUnary_query
      formula rank auxiliary
  change
    maskDynamicGridRecordCatalogueOutput
      sourceIrreducibleRankDegreeWidth
      factor400BinaryIrreducibleCoefficientBitComputable outer = _
  rw [maskDynamicGridRecordCatalogueOutput_valid
    sourceIrreducibleRankDegreeWidth
    factor400BinaryIrreducibleCoefficientBitComputable
    outer degree hdegree]
  change
    (List.range degree).flatMap (fun bitRank =>
      binaryIrreducibleCoefficientBitWord
        (lengthPrefixedWord (List.replicate bitRank true) ++
          sourceQaryMaskDynamicGridBaseSource
            sourceIrreducibleRankDegreeWidth outer)) = _
  simp_rw [show outer =
    lengthPrefixedWord (List.replicate rank true) ++
      lengthPrefixedWord auxiliary ++ encodeThreeCNF formula from rfl,
    paperVariableAritySourceIrreducibleCoefficientBitWord_query]
  simpa only [degree] using
    (List.map_eq_flatMap (f := fun bitRank => rank.testBit bitRank)
      (l := List.range degree)).symm

/-- Internal support shared across GapCVP continuation modules. -/
theorem sourceIrreducibleRankCoefficientWord_eq_indexedWord
    (formula : ThreeCNF)
    (rank : Fin (2 ^ sourceIrreducibleFormulaDegree formula))
    (auxiliary : List Bool) :
    sourceIrreducibleRankCoefficientWord
      (lengthPrefixedWord (List.replicate rank.val true) ++
        lengthPrefixedWord auxiliary ++ encodeThreeCNF formula) =
      finiteWordBits
        (indexedWord (sourceIrreducibleFormulaDegree formula)
          rank) := by
  rw [paperVariableAritySourceIrreducibleRankCoefficientWord_query,
    factor400BinaryIrreducibleFiniteWordBits_indexedWord]

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def sourceIrreducibleCandidateWidth :
    SourceQaryMaskDynamicGridWidth :=
  factor400BinaryIrreduciblePhysicalDynamicWidth
    paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem paperVariableAritySourceIrreducibleCandidateWidth_output
    (input : List Bool) :
    sourceIrreducibleCandidateWidth.output input =
      physicalFamilyFieldCardinalityUnary input := by
  exact factor400BinaryIrreduciblePhysicalDynamicWidth_output
    paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable input

end

end Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine

end GapCVP

end
