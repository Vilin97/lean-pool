/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part12

/-! # GapCVP proof, part 13 -/

noncomputable section

open StateTransition (EvalsToInTime)
open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace GaussianAdaptivePhysicalUpdatedMatrixCatalogueTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceMachineCert GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceStructuralTuringTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFCappedUnaryPairArithmeticTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceMixedRadixUnaryQuotientRemainderTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryPhysicalWordPackedMatrixTM GapCVP.BinaryPhysicalWordQueryCatalogueTM
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePhysicalStateCellTM
open GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM
open GapCVP.GaussianAdaptivePhysicalColumnStateTM
open GapCVP.GaussianAdaptivePhysicalColumnCellUpdateTM

private def gaussianPhysicalUpdatedRowsUnary : List Bool → List Bool :=
  gaussianDenseStateRowCountUnary ∘
    gaussianPhysicalColumnCurrentState

private noncomputable def gaussianPhysicalUpdatedRowsUnaryComputable :
    BitTM
      gaussianPhysicalUpdatedRowsUnary :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnCurrentStateComputable
    gaussianDenseStateRowCountUnaryComputable

private def gaussianPhysicalUpdatedCheckWidthOutput :
    List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    gaussianPhysicalUpdatedRowsUnary
    gaussianPhysicalColumnPivotWidthOutput

private noncomputable def gaussianPhysicalUpdatedCheckWidthComputable :
    BitTM
      gaussianPhysicalUpdatedCheckWidthOutput :=
  fourFamilyComputedUnaryProductComputable
    gaussianPhysicalUpdatedRowsUnaryComputable
    gaussianPhysicalColumnPivotWidthComputable

private noncomputable def gaussianPhysicalUpdatedCheckWidth :
    SourceQaryMaskDynamicGridWidth where
  output := gaussianPhysicalUpdatedCheckWidthOutput
  computer := gaussianPhysicalUpdatedCheckWidthComputable

private noncomputable def gaussianPhysicalUpdatedRhsWidth :
    SourceQaryMaskDynamicGridWidth where
  output := gaussianPhysicalUpdatedRowsUnary
  computer := gaussianPhysicalUpdatedRowsUnaryComputable

private def gaussianPhysicalUpdatedRankDimension : List Bool → List Bool :=
  gaussianDenseStateDimensionUnary ∘
    gaussianPhysicalPivotRecordState

private noncomputable def gaussianPhysicalUpdatedRankDimensionComputable :
    BitTM
      gaussianPhysicalUpdatedRankDimension :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPivotRecordStateComputable
    gaussianDenseStateDimensionUnaryComputable

private def gaussianPhysicalUpdatedRankDivisionInput
    (input : List Bool) : List Bool :=
  gaussianPhysicalPivotRecordRow input ++ false ::
    (gaussianPhysicalUpdatedRankDimension input ++ false ::
      gaussianPhysicalColumnPivotRecordOuter input)

private noncomputable def gaussianPhysicalUpdatedRankDivisionInputComputable :
    BitTM
      gaussianPhysicalUpdatedRankDivisionInput := by
  have hsource := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnPivotRecordOuterComputable
    (prependBitComputable false)
  have hdimension := pointwiseAppendComputable
    gaussianPhysicalUpdatedRankDimensionComputable hsource
  have hseparator := GapCVP.TMComposition.computableInPolyTime
    hdimension (prependBitComputable false)
  have hphysical := pointwiseAppendComputable
    gaussianPhysicalPivotRecordRowComputable hseparator
  change BitTM
    (fun input =>
      gaussianPhysicalPivotRecordRow input ++ false ::
        (gaussianPhysicalUpdatedRankDimension input ++ false ::
          gaussianPhysicalColumnPivotRecordOuter input))
  simpa only [Function.comp_apply] using hphysical

private def gaussianPhysicalUpdatedRankDivisionOutput :
    List Bool → List Bool :=
  sourceUnaryDivisionOutput ∘
    gaussianPhysicalUpdatedRankDivisionInput

private noncomputable def gaussianPhysicalUpdatedRankDivisionComputable :
    BitTM
      gaussianPhysicalUpdatedRankDivisionOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedRankDivisionInputComputable
    sourceUnaryDivisionComputable

private def gaussianPhysicalUpdatedRankRow
    (input : List Bool) : List Bool :=
  (unaryPrefixOutput
    (gaussianPhysicalUpdatedRankDivisionOutput input)).tail

private noncomputable def gaussianPhysicalUpdatedRankRowComputable :
    BitTM
      gaussianPhysicalUpdatedRankRow := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedRankDivisionComputable
    unaryPrefixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hprefix dropHeadComputable

private def gaussianPhysicalUpdatedRankColumn
    (input : List Bool) : List Bool :=
  (unaryPrefixOutput
    (unaryPrefixSuffixOutput
      (gaussianPhysicalUpdatedRankDivisionOutput input))).tail

private noncomputable def gaussianPhysicalUpdatedRankColumnComputable :
    BitTM
      gaussianPhysicalUpdatedRankColumn := by
  have hsuffix := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedRankDivisionComputable
    actualUnaryPrefixSuffixComputable
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    hsuffix unaryPrefixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hprefix dropHeadComputable

private def gaussianPhysicalUpdatedCheckCellQuery
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (gaussianPhysicalUpdatedRankRow input) ++
    (lengthPrefixedWord (gaussianPhysicalUpdatedRankColumn input) ++
      gaussianPhysicalColumnPivotRecordOuter input)

private noncomputable def gaussianPhysicalUpdatedCheckCellQueryComputable :
    BitTM
      gaussianPhysicalUpdatedCheckCellQuery := by
  have hrow := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedRankRowComputable
    structuralPrefixWriterComputable
  have hcolumn := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedRankColumnComputable
    structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable hrow
    (pointwiseAppendComputable hcolumn
      gaussianPhysicalColumnPivotRecordOuterComputable)
  change BitTM
    (fun input =>
      lengthPrefixedWord (gaussianPhysicalUpdatedRankRow input) ++
        (lengthPrefixedWord (gaussianPhysicalUpdatedRankColumn input) ++
          gaussianPhysicalColumnPivotRecordOuter input))
  simpa only [Function.comp_apply] using hphysical

private def gaussianPhysicalUpdatedCheckRecordOutput :
    List Bool → List Bool :=
  gaussianPhysicalColumnUpdatedCheckWord ∘
    gaussianPhysicalUpdatedCheckCellQuery

private noncomputable def gaussianPhysicalUpdatedCheckRecordComputable :
    BitTM
      gaussianPhysicalUpdatedCheckRecordOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedCheckCellQueryComputable
    gaussianPhysicalColumnUpdatedCheckComputable

private def gaussianPhysicalUpdatedRhsCellQuery
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (gaussianPhysicalPivotRecordRow input) ++
    (lengthPrefixedWord [] ++
      gaussianPhysicalColumnPivotRecordOuter input)

private noncomputable def gaussianPhysicalUpdatedRhsCellQueryComputable :
    BitTM
      gaussianPhysicalUpdatedRhsCellQuery := by
  have hrow := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPivotRecordRowComputable
    structuralPrefixWriterComputable
  have hzero := sourceFixedWordComputable
    (lengthPrefixedWord ([] : List Bool))
  have hphysical := pointwiseAppendComputable hrow
    (pointwiseAppendComputable hzero
      gaussianPhysicalColumnPivotRecordOuterComputable)
  change BitTM
    (fun input =>
      lengthPrefixedWord (gaussianPhysicalPivotRecordRow input) ++
        (lengthPrefixedWord [] ++
          gaussianPhysicalColumnPivotRecordOuter input))
  simpa only [Function.comp_apply] using hphysical

private def gaussianPhysicalUpdatedRhsRecordOutput :
    List Bool → List Bool :=
  gaussianPhysicalColumnUpdatedRhsWord ∘
    gaussianPhysicalUpdatedRhsCellQuery

private noncomputable def gaussianPhysicalUpdatedRhsRecordComputable :
    BitTM
      gaussianPhysicalUpdatedRhsRecordOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedRhsCellQueryComputable
    gaussianPhysicalColumnUpdatedRhsComputable

private def gaussianPhysicalUpdatedCheckBitsOutput :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    gaussianPhysicalUpdatedCheckWidth
    gaussianPhysicalUpdatedCheckRecordComputable

private noncomputable def gaussianPhysicalUpdatedCheckBitsComputable :
    BitTM
      gaussianPhysicalUpdatedCheckBitsOutput :=
  maskDynamicGridRecordCatalogueComputable
    gaussianPhysicalUpdatedCheckWidth
    gaussianPhysicalUpdatedCheckRecordComputable

private def gaussianPhysicalUpdatedRhsBitsOutput :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    gaussianPhysicalUpdatedRhsWidth
    gaussianPhysicalUpdatedRhsRecordComputable

private noncomputable def gaussianPhysicalUpdatedRhsBitsComputable :
    BitTM
      gaussianPhysicalUpdatedRhsBitsOutput :=
  maskDynamicGridRecordCatalogueComputable
    gaussianPhysicalUpdatedRhsWidth
    gaussianPhysicalUpdatedRhsRecordComputable

@[simp] private theorem gaussianPhysicalUpdatedRowsUnary_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n) :
    gaussianPhysicalUpdatedRowsUnary
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate m true := by
  unfold gaussianPhysicalUpdatedRowsUnary
  rw [Function.comp_apply,
    gaussianPhysicalColumnCurrentState_query,
    gaussianDenseStateRowCountUnary_effective]

private theorem gaussianPhysicalUpdatedCheckWidth_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalUpdatedCheckWidth.output
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate (m * n) true := by
  apply fourFamilyComputedUnaryProductOutput_valid
    gaussianPhysicalUpdatedRowsUnary
    gaussianPhysicalColumnPivotWidthOutput
    (gaussianPhysicalPivotColumnQuery active.val
      (effectiveGaussianPackedStateWord state source)) m n
  · exact gaussianPhysicalUpdatedRowsUnary_effective
      state source active
  · exact gaussianPhysicalColumnPivotWidth_effective
      state source active hrows

private theorem gaussianPhysicalUpdatedRhsWidth_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n) :
    gaussianPhysicalUpdatedRhsWidth.output
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate m true := by
  exact gaussianPhysicalUpdatedRowsUnary_effective
    state source active

private theorem gaussianPhysicalUpdatedRankDimension_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalUpdatedRankDimension
        (gaussianPhysicalPivotRecordWord rank width active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate n true := by
  unfold gaussianPhysicalUpdatedRankDimension
  rw [Function.comp_apply,
    gaussianPhysicalPivotRecordState_word]
  exact gaussianDenseStateDimensionUnary_effective
    state source hrows

private theorem gaussianPhysicalUpdatedRankDivisionInput_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalUpdatedRankDivisionInput
        (gaussianPhysicalPivotRecordWord rank width active.val
          (effectiveGaussianPackedStateWord state source)) =
      sourceUnaryDivisionQuery rank n
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) := by
  unfold gaussianPhysicalUpdatedRankDivisionInput
  rw [gaussianPhysicalPivotRecordRow_word,
    gaussianPhysicalUpdatedRankDimension_word
      state source active rank width hrows,
    gaussianPhysicalColumnPivotRecordOuter_word]
  rfl

private theorem gaussianPhysicalUpdatedRankDivisionOutput_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalUpdatedRankDivisionOutput
        (gaussianPhysicalPivotRecordWord rank width active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate (rank / n) true ++ false ::
        (List.replicate (rank % n) true ++ false ::
          sourceUnaryDivisionQuery rank n
            (gaussianPhysicalPivotColumnQuery active.val
              (effectiveGaussianPackedStateWord state source))) := by
  have hn : 0 < n :=
    lt_of_le_of_lt (Nat.zero_le active.val) active.isLt
  unfold gaussianPhysicalUpdatedRankDivisionOutput
  rw [Function.comp_apply,
    gaussianPhysicalUpdatedRankDivisionInput_word
      state source active rank width hrows,
    sourceUnaryDivisionOutput_valid rank n
      (gaussianPhysicalPivotColumnQuery active.val
        (effectiveGaussianPackedStateWord state source)) hn]

private theorem gaussianPhysicalUpdatedRankRow_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalUpdatedRankRow
        (gaussianPhysicalPivotRecordWord rank width active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate (rank / n) true := by
  unfold gaussianPhysicalUpdatedRankRow
  rw [gaussianPhysicalUpdatedRankDivisionOutput_word
    state source active rank width hrows,
    unaryPrefixOutput_replicate_delimiter]
  rfl

private theorem gaussianPhysicalUpdatedRankColumn_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalUpdatedRankColumn
        (gaussianPhysicalPivotRecordWord rank width active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate (rank % n) true := by
  unfold gaussianPhysicalUpdatedRankColumn
  rw [gaussianPhysicalUpdatedRankDivisionOutput_word
    state source active rank width hrows,
    unaryPrefixSuffixOutput_valid,
    unaryPrefixOutput_replicate_delimiter]
  rfl

private theorem gaussianPhysicalUpdatedCheckCellQuery_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalUpdatedCheckCellQuery
        (gaussianPhysicalPivotRecordWord rank width active.val
          (effectiveGaussianPackedStateWord state source)) =
      gaussianPhysicalColumnCellQuery
        (rank / n) (rank % n) active.val
        (effectiveGaussianPackedStateWord state source) := by
  unfold gaussianPhysicalUpdatedCheckCellQuery
    gaussianPhysicalColumnCellQuery
    affineCellQuery
  rw [gaussianPhysicalUpdatedRankRow_word
    state source active rank width hrows,
    gaussianPhysicalUpdatedRankColumn_word
      state source active rank width hrows,
    gaussianPhysicalColumnPivotRecordOuter_word]
  simp only [List.append_assoc]

private theorem gaussianPhysicalUpdatedRhsCellQuery_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (row width : ℕ) :
    gaussianPhysicalUpdatedRhsCellQuery
        (gaussianPhysicalPivotRecordWord row width active.val
          (effectiveGaussianPackedStateWord state source)) =
      gaussianPhysicalColumnCellQuery row 0 active.val
        (effectiveGaussianPackedStateWord state source) := by
  unfold gaussianPhysicalUpdatedRhsCellQuery
    gaussianPhysicalColumnCellQuery
    affineCellQuery
  rw [gaussianPhysicalPivotRecordRow_word,
    gaussianPhysicalColumnPivotRecordOuter_word]
  simp only [List.append_assoc, List.replicate_zero]

private theorem gaussianPhysicalUpdatedCheckBitsOutput_valid
    (input : List Bool) (count : ℕ)
    (hwidth : gaussianPhysicalUpdatedCheckWidth.output input =
      List.replicate count true) :
    gaussianPhysicalUpdatedCheckBitsOutput input =
      (List.range count).flatMap (fun rank =>
        gaussianPhysicalUpdatedCheckRecordOutput
          (lengthPrefixedWord (List.replicate rank true) ++
            sourceQaryMaskDynamicGridBaseSource
              gaussianPhysicalUpdatedCheckWidth input)) := by
  exact maskDynamicGridRecordCatalogueOutput_valid
    gaussianPhysicalUpdatedCheckWidth
    gaussianPhysicalUpdatedCheckRecordComputable input count hwidth

private theorem gaussianPhysicalUpdatedRhsBitsOutput_valid
    (input : List Bool) (count : ℕ)
    (hwidth : gaussianPhysicalUpdatedRhsWidth.output input =
      List.replicate count true) :
    gaussianPhysicalUpdatedRhsBitsOutput input =
      (List.range count).flatMap (fun rank =>
        gaussianPhysicalUpdatedRhsRecordOutput
          (lengthPrefixedWord (List.replicate rank true) ++
            sourceQaryMaskDynamicGridBaseSource
              gaussianPhysicalUpdatedRhsWidth input)) := by
  exact maskDynamicGridRecordCatalogueOutput_valid
    gaussianPhysicalUpdatedRhsWidth
    gaussianPhysicalUpdatedRhsRecordComputable input count hwidth

private theorem gaussianPhysicalUpdatedCheckGeneratedRecord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank : ℕ) (hrows : 0 < m) :
    lengthPrefixedWord (List.replicate rank true) ++
        sourceQaryMaskDynamicGridBaseSource
          gaussianPhysicalUpdatedCheckWidth
          (gaussianPhysicalPivotColumnQuery active.val
            (effectiveGaussianPackedStateWord state source)) =
      gaussianPhysicalPivotRecordWord rank (m * n) active.val
        (effectiveGaussianPackedStateWord state source) := by
  unfold sourceQaryMaskDynamicGridBaseSource
  rw [gaussianPhysicalUpdatedCheckWidth_effective
    state source active hrows]
  simp only [gaussianPhysicalPivotRecordWord,
    List.append_assoc]

private theorem gaussianPhysicalUpdatedRhsGeneratedRecord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (row : ℕ) :
    lengthPrefixedWord (List.replicate row true) ++
        sourceQaryMaskDynamicGridBaseSource
          gaussianPhysicalUpdatedRhsWidth
          (gaussianPhysicalPivotColumnQuery active.val
            (effectiveGaussianPackedStateWord state source)) =
      gaussianPhysicalPivotRecordWord row m active.val
        (effectiveGaussianPackedStateWord state source) := by
  unfold sourceQaryMaskDynamicGridBaseSource
  rw [gaussianPhysicalUpdatedRhsWidth_effective
    state source active]
  simp only [gaussianPhysicalPivotRecordWord,
    List.append_assoc]

private theorem gaussianPhysicalUpdatedCheckRecordOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (row : Fin m) (column : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalUpdatedCheckRecordOutput
        (gaussianPhysicalPivotRecordWord
          (row.val * n + column.val) (m * n) active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide
        ((columnStep state active).system.check row column =
          (1 : ZMod 2))] := by
  have hn : 0 < n :=
    lt_of_le_of_lt (Nat.zero_le active.val) active.isLt
  have hquotient :
      (row.val * n + column.val) / n = row.val := by
    simpa only [Nat.mul_comm, Nat.div_eq_of_lt column.isLt, add_zero] using Nat.mul_add_div hn
        row.val column.val
  have hremainder :
      (row.val * n + column.val) % n = column.val := by
    simp only [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt column.isLt, zero_add]
  have hquery := gaussianPhysicalUpdatedCheckCellQuery_word
    state source active (row.val * n + column.val)
    (m * n) hrows
  rw [hquotient, hremainder] at hquery
  unfold gaussianPhysicalUpdatedCheckRecordOutput
  rw [Function.comp_apply, hquery]
  exact gaussianPhysicalColumnUpdatedCheckWord_effective
    state source row column active

private theorem gaussianPhysicalUpdatedRhsRecordOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (row : Fin m) :
    gaussianPhysicalUpdatedRhsRecordOutput
        (gaussianPhysicalPivotRecordWord row.val m active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide
        ((columnStep state active).system.rhs row =
          (1 : ZMod 2))] := by
  have hn : 0 < n :=
    lt_of_le_of_lt (Nat.zero_le active.val) active.isLt
  let zero : Fin n := ⟨0, hn⟩
  unfold gaussianPhysicalUpdatedRhsRecordOutput
  rw [Function.comp_apply,
    gaussianPhysicalUpdatedRhsCellQuery_word]
  exact gaussianPhysicalColumnUpdatedRhsWord_effective
    state source row zero active

private theorem gaussianPhysicalUpdatedCheckBitsOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalUpdatedCheckBitsOutput
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianPackedCheckBits
        (columnStep state active) := by
  let input := gaussianPhysicalPivotColumnQuery active.val
    (effectiveGaussianPackedStateWord state source)
  have hwidth : gaussianPhysicalUpdatedCheckWidth.output input =
      List.replicate (m * n) true :=
    gaussianPhysicalUpdatedCheckWidth_effective
      state source active hrows
  have hcatalogue := gaussianPhysicalUpdatedCheckBitsOutput_valid
    input (m * n) hwidth
  calc
    gaussianPhysicalUpdatedCheckBitsOutput input =
        (List.range (m * n)).flatMap (fun rank =>
          gaussianPhysicalUpdatedCheckRecordOutput
            (lengthPrefixedWord (List.replicate rank true) ++
              sourceQaryMaskDynamicGridBaseSource
                gaussianPhysicalUpdatedCheckWidth input)) :=
      hcatalogue
    _ = (List.range (m * n)).flatMap (fun rank =>
          gaussianPhysicalUpdatedCheckRecordOutput
            (gaussianPhysicalPivotRecordWord rank (m * n)
              active.val
              (effectiveGaussianPackedStateWord state source))) := by
      apply List.flatMap_congr
      intro rank _
      exact congrArg gaussianPhysicalUpdatedCheckRecordOutput
        (gaussianPhysicalUpdatedCheckGeneratedRecord_effective
          state source active rank hrows)
    _ = (List.range m).flatMap (fun row =>
          (List.range n).flatMap (fun column =>
            gaussianPhysicalUpdatedCheckRecordOutput
              (gaussianPhysicalPivotRecordWord
                (row * n + column) (m * n) active.val
                (effectiveGaussianPackedStateWord state source)))) := by
      rw [sourcePhysicalWordCanonical_range_mul_flatMap]
      simp only [List.flatMap_assoc, List.flatMap_map]
    _ = (List.finRange m).flatMap (fun row =>
          (List.finRange n).flatMap (fun column =>
            [decide
              ((columnStep state active).system.check row column =
                (1 : ZMod 2))])) := by
      rw [gaussianPhysicalPivot_range_flatMap_finRange]
      apply List.flatMap_congr
      intro row _
      rw [gaussianPhysicalPivot_range_flatMap_finRange]
      apply List.flatMap_congr
      intro column _
      exact gaussianPhysicalUpdatedCheckRecordOutput_effective
        state source active row column hrows
    _ = effectiveGaussianPackedCheckBits
          (columnStep state active) := by
      unfold effectiveGaussianPackedCheckBits
      apply List.flatMap_congr
      intro row _
      exact sourcePhysicalWordPackedFlatMap_singleton
        (List.finRange n)
        (fun column =>
          decide
            ((columnStep state active).system.check row column =
              (1 : ZMod 2)))

private theorem gaussianPhysicalUpdatedRhsBitsOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n) :
    gaussianPhysicalUpdatedRhsBitsOutput
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianPackedRhsBits
        (columnStep state active) := by
  let input := gaussianPhysicalPivotColumnQuery active.val
    (effectiveGaussianPackedStateWord state source)
  have hwidth : gaussianPhysicalUpdatedRhsWidth.output input =
      List.replicate m true :=
    gaussianPhysicalUpdatedRhsWidth_effective
      state source active
  have hcatalogue := gaussianPhysicalUpdatedRhsBitsOutput_valid
    input m hwidth
  calc
    gaussianPhysicalUpdatedRhsBitsOutput input =
        (List.range m).flatMap (fun row =>
          gaussianPhysicalUpdatedRhsRecordOutput
            (lengthPrefixedWord (List.replicate row true) ++
              sourceQaryMaskDynamicGridBaseSource
                gaussianPhysicalUpdatedRhsWidth input)) :=
      hcatalogue
    _ = (List.range m).flatMap (fun row =>
          gaussianPhysicalUpdatedRhsRecordOutput
            (gaussianPhysicalPivotRecordWord row m active.val
              (effectiveGaussianPackedStateWord state source))) := by
      apply List.flatMap_congr
      intro row _
      exact congrArg gaussianPhysicalUpdatedRhsRecordOutput
        (gaussianPhysicalUpdatedRhsGeneratedRecord_effective
          state source active row)
    _ = (List.finRange m).flatMap (fun row =>
          [decide
            ((columnStep state active).system.rhs row =
              (1 : ZMod 2))]) := by
      rw [gaussianPhysicalPivot_range_flatMap_finRange]
      apply List.flatMap_congr
      intro row _
      exact gaussianPhysicalUpdatedRhsRecordOutput_effective
        state source active row
    _ = effectiveGaussianPackedRhsBits
          (columnStep state active) := by
      unfold effectiveGaussianPackedRhsBits
      exact sourcePhysicalWordPackedFlatMap_singleton
        (List.finRange m)
        (fun row =>
          decide
            ((columnStep state active).system.rhs row =
              (1 : ZMod 2)))

private def gaussianPhysicalUpdatedOriginalSource : List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix ∘ firstFieldSuffix ∘
    firstFieldSuffix ∘ gaussianPhysicalColumnCurrentState

private noncomputable def gaussianPhysicalUpdatedOriginalSourceComputable :
    BitTM
      gaussianPhysicalUpdatedOriginalSource := by
  have hcheck := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnCurrentStateComputable
    firstFieldSuffixComputable
  have hrhs := GapCVP.TMComposition.computableInPolyTime
    hcheck firstFieldSuffixComputable
  have hnext := GapCVP.TMComposition.computableInPolyTime
    hrhs firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hnext firstFieldSuffixComputable

@[simp] private theorem gaussianPhysicalUpdatedOriginalSource_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n) :
    gaussianPhysicalUpdatedOriginalSource
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      source := by
  simp only [gaussianPhysicalUpdatedOriginalSource, gaussianPhysicalColumnCurrentState,
      gaussianPhysicalPivotColumnQuery, effectiveGaussianPackedStateWord, List.append_assoc,
          Function.comp_apply,
      firstFieldSuffix_valid]

private def gaussianPhysicalColumnStateOutput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (gaussianPhysicalUpdatedCheckBitsOutput input) ++
    lengthPrefixedWord (gaussianPhysicalUpdatedRhsBitsOutput input) ++
    lengthPrefixedWord
      (GaussianAdaptivePhysicalColumnStateTM.gaussianPhysicalColumnNextPivotUnary input) ++
    lengthPrefixedWord
      (gaussianPhysicalColumnUpdatedPivotCatalogueOutput input) ++
    gaussianPhysicalUpdatedOriginalSource input

private noncomputable def gaussianPhysicalColumnStateComputable :
    BitTM
      gaussianPhysicalColumnStateOutput := by
  have hcheck := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedCheckBitsComputable
    structuralPrefixWriterComputable
  have hrhs := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedRhsBitsComputable
    structuralPrefixWriterComputable
  have hnext := GapCVP.TMComposition.computableInPolyTime
    GaussianAdaptivePhysicalColumnStateTM.gaussianPhysicalColumnNextPivotUnaryComputable
    structuralPrefixWriterComputable
  have hpivots := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnUpdatedPivotCatalogueComputable
    structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable hcheck
    (pointwiseAppendComputable hrhs
      (pointwiseAppendComputable hnext
        (pointwiseAppendComputable hpivots
          gaussianPhysicalUpdatedOriginalSourceComputable)))
  change BitTM
    (fun input =>
      lengthPrefixedWord (gaussianPhysicalUpdatedCheckBitsOutput input) ++
        lengthPrefixedWord (gaussianPhysicalUpdatedRhsBitsOutput input) ++
        lengthPrefixedWord
          (GaussianAdaptivePhysicalColumnStateTM.gaussianPhysicalColumnNextPivotUnary input) ++
        lengthPrefixedWord
          (gaussianPhysicalColumnUpdatedPivotCatalogueOutput input) ++
        gaussianPhysicalUpdatedOriginalSource input)
  simpa only [Function.comp_apply, List.append_assoc] using hphysical

private theorem gaussianPhysicalColumnStateOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalColumnStateOutput
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianPackedStateWord
        (columnStep state active) source := by
  unfold gaussianPhysicalColumnStateOutput
  rw [gaussianPhysicalUpdatedCheckBitsOutput_effective
    state source active hrows,
    gaussianPhysicalUpdatedRhsBitsOutput_effective
      state source active,
    GaussianAdaptivePhysicalColumnStateTM.gaussianPhysicalColumnNextPivotUnary_effective
      state source active hrows,
    gaussianPhysicalColumnUpdatedPivotCatalogueOutput_effective
      state source active hrows,
    gaussianPhysicalUpdatedOriginalSource_effective]
  rfl

end GaussianAdaptivePhysicalUpdatedMatrixCatalogueTM

namespace GaussianAdaptivePhysicalInitialStateTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.SourceStructuralTuringTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.SourceMixedRadixUnaryQuotientRemainderTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryDimensionTM
open GapCVP.BinaryPhysicalWordPackedMatrixTM GapCVP.GaussianAdaptiveEliminationCorrectness
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePhysicalStateCellTM

private noncomputable def gaussianPhysicalInitialPivotWidth :
    SourceQaryMaskDynamicGridWidth where
  output := gaussianDenseStateDimensionUnary
  computer := gaussianDenseStateDimensionUnaryComputable

private def gaussianPhysicalInitialPivotCatalogue : List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    gaussianPhysicalInitialPivotWidth
    (sourceFixedWordComputable (lengthPrefixedWord [false]))

private noncomputable def gaussianPhysicalInitialPivotCatalogueComputable :
    BitTM
      gaussianPhysicalInitialPivotCatalogue :=
  maskDynamicGridRecordCatalogueComputable
    gaussianPhysicalInitialPivotWidth
    (sourceFixedWordComputable (lengthPrefixedWord [false]))

private def gaussianPhysicalPackedFullInitialStateOutput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (gaussianPackedStateCheckBits input) ++
    lengthPrefixedWord (gaussianPackedStateRhsBits input) ++
    lengthPrefixedWord [] ++
    lengthPrefixedWord
      (gaussianPhysicalInitialPivotCatalogue input) ++
    gaussianPackedInitialOriginalSource input

private noncomputable def gaussianPhysicalPackedFullInitialStateComputable :
    BitTM
      gaussianPhysicalPackedFullInitialStateOutput := by
  have hcheck := GapCVP.TMComposition.computableInPolyTime
    gaussianPackedStateCheckBitsComputable
    structuralPrefixWriterComputable
  have hrhs := GapCVP.TMComposition.computableInPolyTime
    gaussianPackedStateRhsBitsComputable
    structuralPrefixWriterComputable
  have hpivot := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalInitialPivotCatalogueComputable
    structuralPrefixWriterComputable
  have hzero := sourceFixedWordComputable
    (lengthPrefixedWord ([] : List Bool))
  have hphysical := pointwiseAppendComputable hcheck
    (pointwiseAppendComputable hrhs
      (pointwiseAppendComputable hzero
        (pointwiseAppendComputable hpivot
          gaussianPackedInitialOriginalSourceComputable)))
  change BitTM
    (fun input =>
      lengthPrefixedWord (gaussianPackedStateCheckBits input) ++
        lengthPrefixedWord (gaussianPackedStateRhsBits input) ++
        lengthPrefixedWord [] ++
        lengthPrefixedWord
          (gaussianPhysicalInitialPivotCatalogue input) ++
        gaussianPackedInitialOriginalSource input)
  simpa only [Function.comp_apply, List.append_assoc] using hphysical

private theorem gaussianDenseStateCheckLengthUnary_matrixWord
    (checks rhs source : List Bool) :
    gaussianDenseStateCheckLengthUnary
        (lengthPrefixedWord checks ++
          lengthPrefixedWord rhs ++ source) =
      List.replicate checks.length true := by
  change
    sourceInputLengthUnary
      (gaussianPackedStateCheckBits
        (lengthPrefixedWord checks ++
          lengthPrefixedWord rhs ++ source)) = _
  rw [gaussianPackedStateCheckBits_matrixWord]
  rfl

private theorem gaussianDenseStateRowCountUnary_matrixWord
    (checks rhs source : List Bool) :
    gaussianDenseStateRowCountUnary
        (lengthPrefixedWord checks ++
          lengthPrefixedWord rhs ++ source) =
      List.replicate rhs.length true := by
  change
    sourceInputLengthUnary
      (gaussianPackedStateRhsBits
        (lengthPrefixedWord checks ++
          lengthPrefixedWord rhs ++ source)) = _
  rw [gaussianPackedStateRhsBits_matrixWord]
  rfl

private theorem gaussianDenseStateDimensionUnary_matrixWord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (hrows : 0 < m) :
    gaussianDenseStateDimensionUnary
        (lengthPrefixedWord (effectiveGaussianPackedCheckBits state) ++
          lengthPrefixedWord (effectiveGaussianPackedRhsBits state) ++
          source) =
      List.replicate n true := by
  let word :=
    lengthPrefixedWord (effectiveGaussianPackedCheckBits state) ++
      lengthPrefixedWord (effectiveGaussianPackedRhsBits state) ++
      source
  have hcheck : gaussianDenseStateCheckLengthUnary word =
      List.replicate (m * n) true := by
    dsimp [word]
    rw [gaussianDenseStateCheckLengthUnary_matrixWord,
      effectiveGaussianPackedCheckBits_length]
  have hrhs : gaussianDenseStateRowCountUnary word =
      List.replicate m true := by
    dsimp [word]
    rw [gaussianDenseStateRowCountUnary_matrixWord,
      effectiveGaussianPackedRhsBits_length]
  have hquery : gaussianDenseStateDimensionDivisionQuery word =
      sourceUnaryDivisionQuery (m * n) m word := by
    simp only [gaussianDenseStateDimensionDivisionQuery, hcheck, hrhs, sourceUnaryDivisionQuery]
  change gaussianDenseStateDimensionUnary word = _
  unfold gaussianDenseStateDimensionUnary
  simp only [Function.comp_apply]
  rw [hquery, sourceUnaryDivisionOutput_valid
    (m * n) m word hrows]
  rw [unaryPrefixOutput_replicate_delimiter]
  simp only [List.tail_cons]
  rw [Nat.mul_div_cancel_left n hrows]

private theorem gaussianPhysicalInitialPivotCatalogue_valid
    (input : List Bool) (dimension : ℕ)
    (hdimension : gaussianDenseStateDimensionUnary input =
      List.replicate dimension true) :
    gaussianPhysicalInitialPivotCatalogue input =
      binaryGaussianPivotBatchStream
        (List.replicate dimension [false]) := by
  change
    maskDynamicGridRecordCatalogueOutput
      gaussianPhysicalInitialPivotWidth
      (sourceFixedWordComputable
        (lengthPrefixedWord [false])) input = _
  rw [maskDynamicGridRecordCatalogueOutput_valid
    gaussianPhysicalInitialPivotWidth
    (sourceFixedWordComputable
      (lengthPrefixedWord [false]))
    input dimension hdimension]
  change
    (List.range dimension).flatMap
        (fun _ => lengthPrefixedWord [false]) =
      (List.replicate dimension [false]).flatMap
        lengthPrefixedWord
  rw [← List.flatMap_map]
  simp only [List.map_const', List.length_range]

private theorem gaussianPhysicalPackedFullInitialStateOutput_effective
    (system : BinaryAffineSystem)
    (source : List Bool) (hrows : 0 < system.rowCount) :
    gaussianPhysicalPackedFullInitialStateOutput
        (lengthPrefixedWord
          (sourcePhysicalWordPackedCheckBits system) ++
          lengthPrefixedWord
            (sourcePhysicalWordPackedRhsBits system) ++ source) =
      effectiveGaussianPackedStateWord
        (initialState system.effectiveGaussianSystem) source := by
  let initial := initialState system.effectiveGaussianSystem
  let word :=
    lengthPrefixedWord
      (sourcePhysicalWordPackedCheckBits system) ++
      lengthPrefixedWord
        (sourcePhysicalWordPackedRhsBits system) ++ source
  have hcheck : sourcePhysicalWordPackedCheckBits system =
      effectiveGaussianPackedCheckBits initial :=
    sourcePhysicalWordPackedCheckBits_eq_effective_initial system
  have hrhs : sourcePhysicalWordPackedRhsBits system =
      effectiveGaussianPackedRhsBits initial :=
    sourcePhysicalWordPackedRhsBits_eq_effective_initial system
  have hdimension : gaussianDenseStateDimensionUnary word =
      List.replicate system.dimension true := by
    dsimp [word]
    rw [hcheck, hrhs]
    exact gaussianDenseStateDimensionUnary_matrixWord_effective
      initial source hrows
  have hpivots := gaussianPhysicalInitialPivotCatalogue_valid
    word system.dimension hdimension
  change gaussianPhysicalPackedFullInitialStateOutput word = _
  unfold gaussianPhysicalPackedFullInitialStateOutput
    effectiveGaussianPackedStateWord
  rw [gaussianPackedStateCheckBits_matrixWord,
    gaussianPackedStateRhsBits_matrixWord,
    gaussianPackedInitialOriginalSource_matrixWord,
    hpivots, effectiveGaussianPackedPivotCatalogue_initial]
  rw [hcheck, hrhs]
  rfl

end GaussianAdaptivePhysicalInitialStateTM

namespace GaussianAdaptivePhysicalColumnIterationBoundTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM GapCVP.BinaryDimensionTM
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePhysicalStateCellTM
open GapCVP.GaussianAdaptivePhysicalColumnStateTM
open GapCVP.GaussianAdaptivePhysicalUpdatedMatrixCatalogueTM
open GapCVP.GaussianAdaptivePhysicalInitialStateTM

private def gaussianPhysicalColumnIterationBudgetWord
    (packed : List Bool) : List Bool :=
  List.replicate (64 * (packed.length + 1) ^ 2) true

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationBudgetWordComputable :
    BitTM
      gaussianPhysicalColumnIterationBudgetWord := by
  have hphysical := polynomialValueUnaryComputable
    (64 * (Polynomial.X + 1) ^ 2)
  change BitTM
    (fun packed : List Bool =>
      List.replicate (64 * (packed.length + 1) ^ 2) true)
  simpa only [Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one] using hphysical

private abbrev gaussianPhysicalColumnIterationBudgetArchive :
    List Bool → List Bool :=
  firstFieldContents

private abbrev gaussianPhysicalColumnIterationCurrentQuery :
    List Bool → List Bool :=
  firstFieldSuffix

private def gaussianPhysicalColumnIterationActiveUnary :
    List Bool → List Bool :=
  gaussianPhysicalColumnActiveUnary ∘
    gaussianPhysicalColumnIterationCurrentQuery

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationActiveUnaryComputable :
    BitTM
      gaussianPhysicalColumnIterationActiveUnary :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable
    gaussianPhysicalColumnActiveUnaryComputable

private def gaussianPhysicalColumnIterationCandidate
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
    (true :: gaussianPhysicalColumnIterationActiveUnary input) ++
    gaussianPhysicalColumnStateOutput
      (gaussianPhysicalColumnIterationCurrentQuery input)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationCandidateComputable :
    BitTM
      gaussianPhysicalColumnIterationCandidate := by
  have hactive := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnIterationActiveUnaryComputable
    (prependBitComputable true)
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    hactive structuralPrefixWriterComputable
  have hstate := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable gaussianPhysicalColumnStateComputable
  exact pointwiseAppendComputable hprefix hstate

private def gaussianPhysicalColumnIterationBudgetLengthUnary :
    List Bool → List Bool :=
  sourceInputLengthUnary ∘
    gaussianPhysicalColumnIterationBudgetArchive

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationBudgetLengthUnaryComputable :
    BitTM
      gaussianPhysicalColumnIterationBudgetLengthUnary :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable sourceInputLengthUnaryComputable

private def gaussianPhysicalColumnIterationCandidateLengthUnary :
    List Bool → List Bool :=
  sourceInputLengthUnary ∘
    gaussianPhysicalColumnIterationCandidate

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationCandidateLengthUnaryComputable :
    BitTM
      gaussianPhysicalColumnIterationCandidateLengthUnary :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnIterationCandidateComputable
    sourceInputLengthUnaryComputable

private def gaussianPhysicalColumnIterationOverflowMarker :
    List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    gaussianPhysicalColumnIterationBudgetLengthUnary
    gaussianPhysicalColumnIterationCandidateLengthUnary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationOverflowMarkerComputable :
    BitTM
      gaussianPhysicalColumnIterationOverflowMarker :=
  fourFamilyComputedUnaryLessBitComputable
    gaussianPhysicalColumnIterationBudgetLengthUnaryComputable
    gaussianPhysicalColumnIterationCandidateLengthUnaryComputable

private def gaussianPhysicalColumnIterationAcceptMarker :
    List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    gaussianPhysicalColumnIterationOverflowMarker

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationAcceptMarkerComputable :
    BitTM
      gaussianPhysicalColumnIterationAcceptMarker :=
  fourFamilyBooleanNotOutputComputable
    gaussianPhysicalColumnIterationOverflowMarkerComputable

private def gaussianPhysicalColumnIterationAccepted
    (input : List Bool) : Bool :=
  (gaussianPhysicalColumnIterationAcceptMarker input).headD false

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationAcceptedComputable :
    BitTM
      (fun input =>
        gaussianPhysicalColumnIterationAccepted input :: input) :=
  gaussianPhysicalComputedMarkerPreservingComputable
    gaussianPhysicalColumnIterationAcceptMarkerComputable

private def gaussianPhysicalColumnIterationAcceptedOutput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
    (gaussianPhysicalColumnIterationBudgetArchive input) ++
    gaussianPhysicalColumnIterationCandidate input

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationAcceptedOutputComputable :
    BitTM
      gaussianPhysicalColumnIterationAcceptedOutput := by
  have hbudget := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable structuralPrefixWriterComputable
  exact pointwiseAppendComputable hbudget
    gaussianPhysicalColumnIterationCandidateComputable

private def gaussianPhysicalColumnIterationStep :
    List Bool → List Bool :=
  binaryGaussianDynamicBranchOutput
    gaussianPhysicalColumnIterationAccepted
    gaussianPhysicalColumnIterationAcceptedOutput id

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationStepComputable :
    BitTM
      gaussianPhysicalColumnIterationStep :=
  binaryGaussianDynamicBranchComputable
    gaussianPhysicalColumnIterationAcceptedComputable
    gaussianPhysicalColumnIterationAcceptedOutputComputable
    (Turing.idComputableInPolyTime bitEncoding)

@[simp] private theorem gaussianPhysicalColumnIterationOverflowMarker_valid
    (input : List Bool) :
    gaussianPhysicalColumnIterationOverflowMarker input =
      [decide
        ((gaussianPhysicalColumnIterationBudgetArchive input).length <
          (gaussianPhysicalColumnIterationCandidate input).length)] := by
  unfold gaussianPhysicalColumnIterationOverflowMarker
  apply fourFamilyComputedUnaryLessBitOutput_valid
    gaussianPhysicalColumnIterationBudgetLengthUnary
    gaussianPhysicalColumnIterationCandidateLengthUnary input
    (gaussianPhysicalColumnIterationBudgetArchive input).length
    (gaussianPhysicalColumnIterationCandidate input).length
  · rfl
  · rfl

@[simp] private theorem gaussianPhysicalColumnIterationAccepted_valid
    (input : List Bool) :
    gaussianPhysicalColumnIterationAccepted input =
      decide
        ((gaussianPhysicalColumnIterationCandidate input).length ≤
          (gaussianPhysicalColumnIterationBudgetArchive input).length) := by
  unfold gaussianPhysicalColumnIterationAccepted
    gaussianPhysicalColumnIterationAcceptMarker
  rw [fourFamilyBooleanNotOutput_bit
    gaussianPhysicalColumnIterationOverflowMarker input
    (decide
      ((gaussianPhysicalColumnIterationBudgetArchive input).length <
        (gaussianPhysicalColumnIterationCandidate input).length))
    (gaussianPhysicalColumnIterationOverflowMarker_valid input)]
  simp only [List.headD_cons, ← decide_not, Nat.not_lt]

@[simp] private theorem gaussianPhysicalColumnIterationBudgetArchive_step
    (input : List Bool) :
    gaussianPhysicalColumnIterationBudgetArchive
        (gaussianPhysicalColumnIterationStep input) =
      gaussianPhysicalColumnIterationBudgetArchive input := by
  unfold gaussianPhysicalColumnIterationStep
    binaryGaussianDynamicBranchOutput
  cases haccept : gaussianPhysicalColumnIterationAccepted input with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, id_eq]
  | true =>
      simp only [↓reduceIte, gaussianPhysicalColumnIterationAcceptedOutput,
          firstFieldContents_valid]

private theorem gaussianPhysicalColumnIterationStep_length_le
    (input : List Bool) :
    (gaussianPhysicalColumnIterationStep input).length ≤
      max input.length
        (3 * (gaussianPhysicalColumnIterationBudgetArchive input).length + 1) := by
  unfold gaussianPhysicalColumnIterationStep
    binaryGaussianDynamicBranchOutput
  cases haccept : gaussianPhysicalColumnIterationAccepted input with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, id_eq, le_sup_left]
  | true =>
      have hfits :
          (gaussianPhysicalColumnIterationCandidate input).length ≤
            (gaussianPhysicalColumnIterationBudgetArchive input).length := by
        have hdecision :=
          gaussianPhysicalColumnIterationAccepted_valid input
        rw [haccept] at hdecision
        exact of_decide_eq_true hdecision.symm
      change
        (lengthPrefixedWord
          (gaussianPhysicalColumnIterationBudgetArchive input) ++
          gaussianPhysicalColumnIterationCandidate input).length ≤ _
      simp only [List.length_append, lengthPrefixedWord_length]
      omega

@[simp] private theorem gaussianPhysicalColumnIterationBudgetArchive_iterate
    (input : List Bool) (stage : ℕ) :
    gaussianPhysicalColumnIterationBudgetArchive
        ((gaussianPhysicalColumnIterationStep^[stage]) input) =
      gaussianPhysicalColumnIterationBudgetArchive input := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq]
  | succ stage ih =>
      rw [Function.iterate_succ_apply',
        gaussianPhysicalColumnIterationBudgetArchive_step, ih]

private theorem gaussianPhysicalColumnIteration_iterate_length_le
    (seed : List Bool) (stage : ℕ) :
    ((gaussianPhysicalColumnIterationStep^[stage]) seed).length ≤
      max seed.length
        (3 * (gaussianPhysicalColumnIterationBudgetArchive seed).length + 1) := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, le_sup_left]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      have hstep := gaussianPhysicalColumnIterationStep_length_le
        ((gaussianPhysicalColumnIterationStep^[stage]) seed)
      rw [gaussianPhysicalColumnIterationBudgetArchive_iterate] at hstep
      omega

private theorem gaussianPhysicalColumnIterationStep_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates
      gaussianPhysicalColumnIterationStep (4 * Polynomial.X + 1) := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage _
  have hword := parseUnaryBoundedFold_eq_word
    input count seed hparse
  have hseed : seed.length ≤ input.length := by
    rw [hword]
    simp only [unaryBoundedFoldWord, List.length_append,
      List.length_replicate, List.length_cons]
    omega
  have hbudget := annotatedStructuralFieldAccounting seed
  have harchive :
      (gaussianPhysicalColumnIterationBudgetArchive seed).length ≤
        seed.length := by
    change (firstFieldContents seed).length ≤ seed.length
    omega
  have hstate := gaussianPhysicalColumnIteration_iterate_length_le
    seed stage
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
  omega

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationFoldComputable :
    BitTM
      (boundedRecordFoldOutput gaussianPhysicalColumnIterationStep) :=
  boundedDependentRecordFoldComputable
    gaussianPhysicalColumnIterationStepComputable
    (4 * Polynomial.X + 1)
    gaussianPhysicalColumnIterationStep_polynomiallyBoundedFoldStates

private def gaussianPhysicalColumnIterationSeed
    (packed : List Bool) : List Bool :=
  lengthPrefixedWord
    (gaussianPhysicalColumnIterationBudgetWord packed) ++
    lengthPrefixedWord ([] : List Bool) ++ packed

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationSeedComputable :
    BitTM
      gaussianPhysicalColumnIterationSeed := by
  have hbudget := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnIterationBudgetWordComputable
    structuralPrefixWriterComputable
  have hzero := sourceFixedWordComputable
    (lengthPrefixedWord ([] : List Bool))
  have hphysical := pointwiseAppendComputable hbudget
    (pointwiseAppendComputable hzero
      (Turing.idComputableInPolyTime bitEncoding))
  change BitTM
    (fun packed : List Bool =>
      lengthPrefixedWord
          (gaussianPhysicalColumnIterationBudgetWord packed) ++
        lengthPrefixedWord ([] : List Bool) ++ packed)
  simpa only [Function.comp_apply, List.append_assoc, id_eq] using hphysical

private def gaussianPhysicalColumnIterationPreparation
    (packed : List Bool) : List Bool :=
  gaussianDenseStateDimensionUnary packed ++
    false :: gaussianPhysicalColumnIterationSeed packed

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationPreparationComputable :
    BitTM
      gaussianPhysicalColumnIterationPreparation := by
  have hseed := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnIterationSeedComputable
    (prependBitComputable false)
  exact pointwiseAppendComputable
    gaussianDenseStateDimensionUnaryComputable hseed

private def gaussianPhysicalColumnIterationOutput : List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix ∘
    boundedRecordFoldOutput gaussianPhysicalColumnIterationStep ∘
    gaussianPhysicalColumnIterationPreparation

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationComputable :
    BitTM
      gaussianPhysicalColumnIterationOutput := by
  have hfold := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnIterationPreparationComputable
    gaussianPhysicalColumnIterationFoldComputable
  have hbudget := GapCVP.TMComposition.computableInPolyTime
    hfold firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hbudget firstFieldSuffixComputable

private def gaussianPhysicalSourceEliminationOutput : List Bool → List Bool :=
  gaussianPhysicalColumnIterationOutput ∘
    gaussianPhysicalPackedFullInitialStateOutput

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalSourceEliminationComputable :
    BitTM
      gaussianPhysicalSourceEliminationOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPackedFullInitialStateComputable
    gaussianPhysicalColumnIterationComputable

end GaussianAdaptivePhysicalColumnIterationBoundTM

namespace GaussianAdaptivePhysicalPackedStateBoundTM

open GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM

private theorem gaussianPhysicalPackedCheckBits_length
    {m n : ℕ} (state : State m n) :
    (effectiveGaussianPackedCheckBits state).length = m * n := by
  simp only [effectiveGaussianPackedCheckBits, List.length_flatMap, List.length_map,
      List.length_finRange,
      List.map_const', List.sum_replicate, smul_eq_mul]

private theorem gaussianPhysicalPackedRhsBits_length
    {m n : ℕ} (state : State m n) :
    (effectiveGaussianPackedRhsBits state).length = m := by
  simp only [effectiveGaussianPackedRhsBits, List.length_map, List.length_finRange]

private theorem gaussianPhysicalPackedPivotWord_length_le
    {m n : ℕ} (state : State m n) (column : Fin n) :
    (effectiveGaussianStatePivotWord state column).length ≤ m + 1 := by
  cases hpivot : effectiveGaussianStatePivotRowOption state column with
  | none => simp only [effectiveGaussianStatePivotWord, hpivot, List.length_cons, List.length_nil,
      zero_add,
                le_add_iff_nonneg_left, zero_le]
  | some row =>
      simp only [effectiveGaussianStatePivotWord, hpivot,
        List.length_cons, List.length_replicate]
      have hrow := row.isLt
      omega

private theorem gaussianPhysicalPackedPrefixedPivotWord_length_le
    {m n : ℕ} (state : State m n) (column : Fin n) :
    (lengthPrefixedWord
      (effectiveGaussianStatePivotWord state column)).length ≤
      2 * m + 3 := by
  rw [lengthPrefixedWord_length]
  have hpivot := gaussianPhysicalPackedPivotWord_length_le state column
  omega

private theorem gaussianPhysicalPackedPivotRecords_length_le
    {m n : ℕ} (state : State m n)
    (columns : List (Fin n)) :
    ((columns.map
      (effectiveGaussianStatePivotWord state)).flatMap
        lengthPrefixedWord).length ≤
      columns.length * (2 * m + 3) := by
  induction columns with
  | nil => simp only [List.map_nil, List.flatMap_nil, List.length_nil, zero_mul, Std.le_refl]
  | cons column remaining ih =>
      have hpivot :=
        gaussianPhysicalPackedPrefixedPivotWord_length_le state column
      calc
        (((column :: remaining).map
          (effectiveGaussianStatePivotWord state)).flatMap
            lengthPrefixedWord).length =
            (lengthPrefixedWord
              (effectiveGaussianStatePivotWord state column)).length +
              ((remaining.map
                (effectiveGaussianStatePivotWord state)).flatMap
                  lengthPrefixedWord).length := by
                    simp only [List.map_cons, List.flatMap_cons, List.length_append,
                      lengthPrefixedWord_length, List.length_flatMap, List.map_map]
        _ ≤ (2 * m + 3) + remaining.length * (2 * m + 3) :=
          Nat.add_le_add hpivot ih
        _ = (column :: remaining).length * (2 * m + 3) := by
          simp only [List.length_cons, Nat.succ_mul]
          omega

private theorem gaussianPhysicalPackedPivotCatalogue_length_le
    {m n : ℕ} (state : State m n) :
    (effectiveGaussianPackedPivotCatalogue state).length ≤
      n * (2 * m + 3) := by
  unfold effectiveGaussianPackedPivotCatalogue
    binaryGaussianPivotBatchStream
    sourceMixedRadixOriginalSourceQueryStream
  simpa only [List.length_finRange] using
    gaussianPhysicalPackedPivotRecords_length_le
      state (List.finRange n)

private theorem gaussianPhysicalPackedPrefixedPivotWord_length_pos
    {m n : ℕ} (state : State m n) (column : Fin n) :
    0 < (lengthPrefixedWord
      (effectiveGaussianStatePivotWord state column)).length := by
  rw [lengthPrefixedWord_length]
  omega

private theorem gaussianPhysicalPackedPivotRecords_length_ge
    {m n : ℕ} (state : State m n)
    (columns : List (Fin n)) :
    columns.length ≤
      ((columns.map
        (effectiveGaussianStatePivotWord state)).flatMap
          lengthPrefixedWord).length := by
  induction columns with
  | nil => simp only [List.length_nil, List.map_nil, List.flatMap_nil, Std.le_refl]
  | cons column remaining ih =>
      have hpivot :=
        gaussianPhysicalPackedPrefixedPivotWord_length_pos state column
      simp only [List.map_cons, List.flatMap_cons,
        List.length_append, List.length_cons]
      omega

private theorem gaussianPhysicalPackedPivotCatalogue_length_ge
    {m n : ℕ} (state : State m n) :
    n ≤ (effectiveGaussianPackedPivotCatalogue state).length := by
  unfold effectiveGaussianPackedPivotCatalogue
    binaryGaussianPivotBatchStream
    sourceMixedRadixOriginalSourceQueryStream
  simpa only [List.length_finRange] using
    gaussianPhysicalPackedPivotRecords_length_ge
      state (List.finRange n)

private theorem gaussianPhysicalPackedState_rows_le_length
    {m n : ℕ} (state : State m n) (source : List Bool) :
    m ≤ (effectiveGaussianPackedStateWord state source).length := by
  unfold effectiveGaussianPackedStateWord
  simp only [List.length_append, lengthPrefixedWord_length,
    gaussianPhysicalPackedRhsBits_length, List.length_replicate]
  omega

private theorem gaussianPhysicalPackedState_columns_le_length
    {m n : ℕ} (state : State m n) (source : List Bool) :
    n ≤ (effectiveGaussianPackedStateWord state source).length := by
  have hpivots := gaussianPhysicalPackedPivotCatalogue_length_ge state
  unfold effectiveGaussianPackedStateWord
  simp only [List.length_append, lengthPrefixedWord_length,
    List.length_replicate]
  omega

private theorem gaussianPhysicalPackedState_source_le_length
    {m n : ℕ} (state : State m n) (source : List Bool) :
    source.length ≤
      (effectiveGaussianPackedStateWord state source).length := by
  unfold effectiveGaussianPackedStateWord
  simp only [List.length_append]
  omega

private def gaussianPhysicalPackedStateSizeBound
    (rows columns sourceLength : ℕ) : ℕ :=
  2 * (rows * columns) + 4 * rows +
    2 * (columns * (2 * rows + 3)) + 4 + sourceLength

private theorem gaussianPhysicalPackedStateWord_length_le
    {m n : ℕ} (state : State m n)
    (source : List Bool) (hnext : state.nextPivot ≤ m) :
    (effectiveGaussianPackedStateWord state source).length ≤
      gaussianPhysicalPackedStateSizeBound m n source.length := by
  unfold effectiveGaussianPackedStateWord
    gaussianPhysicalPackedStateSizeBound
  simp only [List.length_append, lengthPrefixedWord_length,
    gaussianPhysicalPackedCheckBits_length,
    gaussianPhysicalPackedRhsBits_length,
    List.length_replicate]
  have hpivots := gaussianPhysicalPackedPivotCatalogue_length_le state
  omega

private theorem gaussianPhysicalColumnStep_nextPivot_le
    {m n : ℕ} (state : State m n) (column : Fin n)
    (hnext : state.nextPivot ≤ m) :
    (columnStep state column).nextPivot ≤ m := by
  by_cases hrow : state.nextPivot < m
  · cases hpivot : findPivotOption state column with
    | none => simpa only [columnStep, hrow, ↓reduceDIte, hpivot] using hnext
    | some candidate =>
        simp only [columnStep, hrow, ↓reduceDIte, hpivot]
        omega
  · simpa only [columnStep, hrow, ↓reduceDIte] using hnext

private theorem gaussianPhysicalRunColumns_nextPivot_le
    {m n : ℕ} (columns : List (Fin n)) (state : State m n)
    (hnext : state.nextPivot ≤ m) :
    (runColumns columns state).nextPivot ≤ m := by
  induction columns generalizing state with
  | nil => simpa only [runColumns, List.foldl_nil] using hnext
  | cons column remaining ih =>
      change
        (runColumns remaining (columnStep state column)).nextPivot ≤ m
      exact ih (columnStep state column)
        (gaussianPhysicalColumnStep_nextPivot_le state column hnext)

private theorem gaussianPhysicalInitialState_nextPivot_le
    {m n : ℕ} (system : System m n) :
    (initialState system).nextPivot ≤ m := by
  simp only [initialState, zero_le]

private theorem gaussianPhysicalPackedColumnCandidate_length_le
    {m n : ℕ}
    (reference state : State m n) (source : List Bool)
    (column : Fin n) (hnext : state.nextPivot ≤ m) :
    (gaussianPhysicalPivotColumnQuery (column.val + 1)
      (effectiveGaussianPackedStateWord
        (columnStep state column) source)).length ≤
      64 *
        ((effectiveGaussianPackedStateWord reference source).length + 1) ^ 2 := by
  let originalLength :=
    (effectiveGaussianPackedStateWord reference source).length
  have hrows : m ≤ originalLength :=
    gaussianPhysicalPackedState_rows_le_length reference source
  have hcolumns : n ≤ originalLength :=
    gaussianPhysicalPackedState_columns_le_length reference source
  have hsource : source.length ≤ originalLength :=
    gaussianPhysicalPackedState_source_le_length reference source
  have hproduct : m * n ≤ originalLength * originalLength :=
    Nat.mul_le_mul hrows hcolumns
  have hstep := gaussianPhysicalPackedStateWord_length_le
    (columnStep state column) source
    (gaussianPhysicalColumnStep_nextPivot_le state column hnext)
  have hcolumn := column.isLt
  have hshape :
      (effectiveGaussianPackedStateWord
        (columnStep state column) source).length ≤
        6 * (m * n) + 4 * m + 6 * n + 4 + source.length := by
    calc
      _ ≤ gaussianPhysicalPackedStateSizeBound
          m n source.length := hstep
      _ = _ := by
        unfold gaussianPhysicalPackedStateSizeBound
        ring
  have hcandidate :
      (gaussianPhysicalPivotColumnQuery (column.val + 1)
        (effectiveGaussianPackedStateWord
          (columnStep state column) source)).length ≤
        6 * (originalLength * originalLength) +
          13 * originalLength + 7 := by
    unfold gaussianPhysicalPivotColumnQuery
    simp only [List.length_append, lengthPrefixedWord_length,
      List.length_replicate]
    omega
  calc
    _ ≤ 6 * (originalLength * originalLength) +
        13 * originalLength + 7 := hcandidate
    _ ≤ 64 * (originalLength + 1) ^ 2 := by
      linarith
    _ = _ := by rfl

end GaussianAdaptivePhysicalPackedStateBoundTM

namespace GaussianAdaptivePhysicalColumnIterationBoundTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.OutputBoundedDependentRecordFold GapCVP.BinaryPhysicalWordPackedMatrixTM
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePhysicalStateCellTM
open GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM
open GapCVP.GaussianAdaptivePhysicalColumnStateTM
open GapCVP.GaussianAdaptivePhysicalUpdatedMatrixCatalogueTM
open GapCVP.GaussianAdaptivePhysicalInitialStateTM
open GapCVP.GaussianAdaptivePhysicalPackedStateBoundTM

private def gaussianPhysicalColumnIterationExpectedState
    {m n : ℕ}
    (reference current : State m n)
    (source : List Bool) (active : ℕ) : List Bool :=
  lengthPrefixedWord
      (gaussianPhysicalColumnIterationBudgetWord
        (effectiveGaussianPackedStateWord reference source)) ++
    gaussianPhysicalPivotColumnQuery active
      (effectiveGaussianPackedStateWord current source)

@[simp] private theorem gaussianPhysicalColumnIterationExpectedState_archive
    {m n : ℕ}
    (reference current : State m n)
    (source : List Bool) (active : ℕ) :
    gaussianPhysicalColumnIterationBudgetArchive
        (gaussianPhysicalColumnIterationExpectedState
          reference current source active) =
      gaussianPhysicalColumnIterationBudgetWord
        (effectiveGaussianPackedStateWord reference source) := by
  simp only [gaussianPhysicalColumnIterationExpectedState,
      SourceFormulaStructuralDecoder.firstFieldContents_valid]

@[simp] private theorem gaussianPhysicalColumnIterationExpectedState_query
    {m n : ℕ}
    (reference current : State m n)
    (source : List Bool) (active : ℕ) :
    gaussianPhysicalColumnIterationCurrentQuery
        (gaussianPhysicalColumnIterationExpectedState
          reference current source active) =
      gaussianPhysicalPivotColumnQuery active
        (effectiveGaussianPackedStateWord current source) := by
  simp only [gaussianPhysicalColumnIterationExpectedState,
      SourceFormulaStructuralDecoder.firstFieldSuffix_valid]

@[simp] private theorem gaussianPhysicalColumnIterationExpectedState_active
    {m n : ℕ}
    (reference current : State m n)
    (source : List Bool) (active : ℕ) :
    gaussianPhysicalColumnIterationActiveUnary
        (gaussianPhysicalColumnIterationExpectedState
          reference current source active) =
      List.replicate active true := by
  unfold gaussianPhysicalColumnIterationActiveUnary
  rw [Function.comp_apply,
    gaussianPhysicalColumnIterationExpectedState_query,
    gaussianPhysicalColumnActiveUnary_query]

private theorem gaussianPhysicalColumnIterationCandidate_effective
    {m n : ℕ}
    (reference current : State m n)
    (source : List Bool) (column : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalColumnIterationCandidate
        (gaussianPhysicalColumnIterationExpectedState
          reference current source column.val) =
      gaussianPhysicalPivotColumnQuery (column.val + 1)
        (effectiveGaussianPackedStateWord
          (columnStep current column) source) := by
  unfold gaussianPhysicalColumnIterationCandidate
  rw [gaussianPhysicalColumnIterationExpectedState_active,
    gaussianPhysicalColumnIterationExpectedState_query,
    gaussianPhysicalColumnStateOutput_effective
      current source column hrows]
  simp only [gaussianPhysicalPivotColumnQuery, List.replicate_succ]

private theorem gaussianPhysicalColumnIterationAccepted_effective
    {m n : ℕ}
    (reference current : State m n)
    (source : List Bool) (column : Fin n)
    (hrows : 0 < m)
    (hnext : current.nextPivot ≤ m) :
    gaussianPhysicalColumnIterationAccepted
        (gaussianPhysicalColumnIterationExpectedState
          reference current source column.val) = true := by
  let input := gaussianPhysicalColumnIterationExpectedState
    reference current source column.val
  have hbound := gaussianPhysicalPackedColumnCandidate_length_le
    reference current source column hnext
  have hcandidate := gaussianPhysicalColumnIterationCandidate_effective
    reference current source column hrows
  have harchive := gaussianPhysicalColumnIterationExpectedState_archive
    reference current source column.val
  rw [gaussianPhysicalColumnIterationAccepted_valid]
  change decide
    ((gaussianPhysicalColumnIterationCandidate input).length ≤
      (gaussianPhysicalColumnIterationBudgetArchive input).length) = true
  rw [hcandidate, harchive]
  simp only [gaussianPhysicalColumnIterationBudgetWord,
    List.length_replicate]
  exact decide_eq_true hbound

private theorem gaussianPhysicalColumnIterationStep_effective
    {m n : ℕ}
    (reference current : State m n)
    (source : List Bool) (column : Fin n)
    (hrows : 0 < m)
    (hnext : current.nextPivot ≤ m) :
    gaussianPhysicalColumnIterationStep
        (gaussianPhysicalColumnIterationExpectedState
          reference current source column.val) =
      gaussianPhysicalColumnIterationExpectedState
        reference (columnStep current column)
        source (column.val + 1) := by
  let input := gaussianPhysicalColumnIterationExpectedState
    reference current source column.val
  have haccept := gaussianPhysicalColumnIterationAccepted_effective
    reference current source column hrows hnext
  have harchive := gaussianPhysicalColumnIterationExpectedState_archive
    reference current source column.val
  have hcandidate := gaussianPhysicalColumnIterationCandidate_effective
    reference current source column hrows
  change gaussianPhysicalColumnIterationStep input = _
  unfold gaussianPhysicalColumnIterationStep
    binaryGaussianDynamicBranchOutput
  rw [haccept, ite_eq_left rfl]
  unfold gaussianPhysicalColumnIterationAcceptedOutput
  rw [harchive, hcandidate]
  rfl

private theorem gaussianPhysicalEffectiveRunColumns_append
    {m n : ℕ} (first second : List (Fin n))
    (state : State m n) :
    runColumns (first ++ second) state =
      runColumns second (runColumns first state) := by
  induction first generalizing state with
  | nil => simp only [runColumns, List.nil_append, List.foldl_nil]
  | cons column rest ih =>
      simp only [List.cons_append, runColumns]
      exact ih (columnStep state column)

private theorem gaussianPhysicalColumnIterationSeed_effective
    {m n : ℕ} (reference : State m n)
    (source : List Bool) :
    gaussianPhysicalColumnIterationSeed
        (effectiveGaussianPackedStateWord reference source) =
      gaussianPhysicalColumnIterationExpectedState
        reference reference source 0 := by
  simp only [gaussianPhysicalColumnIterationSeed, List.append_assoc,
      gaussianPhysicalColumnIterationExpectedState, gaussianPhysicalPivotColumnQuery,
          List.replicate_zero]

private theorem gaussianPhysicalColumnIteration_iterate_effective
    {m n : ℕ} (reference : State m n)
    (source : List Bool) (hrows : 0 < m)
    (hnext : reference.nextPivot ≤ m)
    (stage : ℕ) (hstage : stage ≤ n) :
    ((gaussianPhysicalColumnIterationStep^[stage])
      (gaussianPhysicalColumnIterationSeed
        (effectiveGaussianPackedStateWord reference source))) =
      gaussianPhysicalColumnIterationExpectedState
        reference
        (runColumns ((List.finRange n).take stage) reference)
        source stage := by
  induction stage with
  | zero =>
      simpa only [Function.iterate_zero, id_eq, runColumns, List.take_zero, List.foldl_nil] using
          gaussianPhysicalColumnIterationSeed_effective reference source
  | succ stage ih =>
      have hlt : stage < n := by omega
      have hprev : stage ≤ n := by omega
      let active : Fin n := ⟨stage, hlt⟩
      let current :=
        runColumns ((List.finRange n).take stage) reference
      have hcurrent : current.nextPivot ≤ m :=
        gaussianPhysicalRunColumns_nextPivot_le
          ((List.finRange n).take stage) reference hnext
      rw [Function.iterate_succ_apply']
      rw [ih hprev]
      have hstep := gaussianPhysicalColumnIterationStep_effective
        reference current source active hrows hcurrent
      have hactiveval : active.val = stage := rfl
      rw [hactiveval] at hstep
      rw [hstep]
      have hindex : stage < (List.finRange n).length := by
        simpa only [List.length_finRange] using hlt
      have hget : (List.finRange n)[stage] = active := by
        apply Fin.ext
        simpa only [List.getElem_finRange, Fin.cast_mk] using hactiveval.symm
      rw [List.take_succ_eq_append_getElem hindex,
        hget, gaussianPhysicalEffectiveRunColumns_append]
      simp only [runColumns, List.foldl_cons, List.foldl_nil, current]

private theorem gaussianPhysicalColumnIterationPreparation_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (hrows : 0 < m) :
    gaussianPhysicalColumnIterationPreparation
        (effectiveGaussianPackedStateWord state source) =
      unaryBoundedFoldWord n
        (gaussianPhysicalColumnIterationSeed
          (effectiveGaussianPackedStateWord state source)) := by
  unfold gaussianPhysicalColumnIterationPreparation
    unaryBoundedFoldWord
  rw [gaussianDenseStateDimensionUnary_effective
    state source hrows]

private theorem gaussianPhysicalColumnIterationOutput_state_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (hrows : 0 < m)
    (hnext : state.nextPivot ≤ m) :
    gaussianPhysicalColumnIterationOutput
        (effectiveGaussianPackedStateWord state source) =
      effectiveGaussianPackedStateWord
        (runColumns (List.finRange n) state) source := by
  unfold gaussianPhysicalColumnIterationOutput
  simp only [Function.comp_apply]
  rw [gaussianPhysicalColumnIterationPreparation_effective
    state source hrows]
  simp only [boundedRecordFoldOutput,
    parseUnaryBoundedFold_word]
  rw [gaussianPhysicalColumnIteration_iterate_effective
    state source hrows hnext n (Nat.le_refl n)]
  have htake : (List.finRange n).take n =
      List.finRange n := by
    simpa only [List.length_finRange] using
      (List.take_length (l := List.finRange n))
  rw [htake]
  simp only [gaussianPhysicalColumnIterationExpectedState, gaussianPhysicalPivotColumnQuery,
      SourceFormulaStructuralDecoder.firstFieldSuffix_valid]

private theorem gaussianPhysicalColumnIterationOutput_effective
    {m n : ℕ} (system : System m n)
    (source : List Bool) (hrows : 0 < m) :
    gaussianPhysicalColumnIterationOutput
        (effectiveGaussianPackedStateWord
          (initialState system) source) =
      effectiveGaussianPackedStateWord
        (eliminate system) source := by
  have hnext := gaussianPhysicalInitialState_nextPivot_le system
  simpa only [eliminate] using
      gaussianPhysicalColumnIterationOutput_state_effective (initialState system) source hrows
          hnext

private theorem gaussianPhysicalSourceEliminationOutput_effective
    (system : BinaryAffineSystem) (source : List Bool)
    (hrows : 0 < system.rowCount) :
    gaussianPhysicalSourceEliminationOutput
        (lengthPrefixedWord
          (sourcePhysicalWordPackedCheckBits system) ++
          lengthPrefixedWord
            (sourcePhysicalWordPackedRhsBits system) ++ source) =
      effectiveGaussianPackedStateWord
        system.effectiveGaussianState source := by
  unfold gaussianPhysicalSourceEliminationOutput
  rw [Function.comp_apply,
    gaussianPhysicalPackedFullInitialStateOutput_effective
      system source hrows]
  exact gaussianPhysicalColumnIterationOutput_effective
    system.effectiveGaussianSystem source hrows

end GaussianAdaptivePhysicalColumnIterationBoundTM

namespace GaussianSourceInitializer

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem
open GapCVP.FormulaBridge GapCVP.PhysicalColumnOrder GapCVP.SourceOrder
open GapCVP.BinaryPhysicalWordPackedMatrixTM GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePhysicalColumnIterationBoundTM

private theorem paperVariableArityPhysicalWordBinarySystem_rowCount_pos
    (encodingLength : ℕ) (formula : ThreeCNF) :
    0 < (physicalWordBinarySystem
      encodingLength formula).rowCount := by
  let normalized := srcFormula formula
  let degree := sourceFieldExponent
    (sourceSizeParameter encodingLength normalized)
  have hdegree : 0 < degree :=
    sourceFieldExponent_pos
      (sourceSizeParameter_ge_one_hundred encodingLength normalized)
  have hgrid : 0 < Fintype.card
      (ExplicitGridPoint encodingLength normalized) := by
    simpa [ExplicitGridPoint] using
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid_card_pos
        encodingLength normalized
  let global : ExplicitConstraintFamily encodingLength normalized := .inl ()
  have hglobal : 0 < explicitFamilyRowCount
      encodingLength normalized global := by
    simpa [global, explicitFamilyRowCount] using hgrid
  let actual : assembledBinaryRow
      (explicitFamilyRowCount encodingLength normalized) degree :=
    ⟨global, (⟨0, hglobal⟩, ⟨0, hdegree⟩)⟩
  let physical :=
    (paperVariableArityExplicitBinaryRowWordOrder
      encodingLength formula).symm actual
  have hphysical := physical.isLt
  change 0 < paperExplicitBinaryRowWordCount
    encodingLength formula
  omega

private structure PaperVariableArityPhysicalPackedMatrixSourceComputer where
  output : List Bool → List Bool
  computer : BitTM output
  output_valid : ∀ formula : ThreeCNF,
    output (encodeThreeCNF formula) =
      lengthPrefixedWord
        (sourcePhysicalWordPackedCheckBits
          (physicalWordBinarySystem
            (encodeThreeCNF formula).length formula)) ++
        lengthPrefixedWord
          (sourcePhysicalWordPackedRhsBits
            (physicalWordBinarySystem
              (encodeThreeCNF formula).length formula)) ++
        encodeThreeCNF formula

private def gaussianPaperVariableAritySourceReducedStateOutput
    (matrix : PaperVariableArityPhysicalPackedMatrixSourceComputer) :
    List Bool → List Bool :=
  gaussianPhysicalSourceEliminationOutput ∘ matrix.output

private noncomputable def gaussianPaperVariableAritySourceReducedStateComputable
    (matrix : PaperVariableArityPhysicalPackedMatrixSourceComputer) :
    BitTM
      (gaussianPaperVariableAritySourceReducedStateOutput matrix) :=
  GapCVP.TMComposition.computableInPolyTime
    matrix.computer gaussianPhysicalSourceEliminationComputable

private theorem gaussianPaperVariableAritySourceReducedStateOutput_effective
    (matrix : PaperVariableArityPhysicalPackedMatrixSourceComputer)
    (formula : ThreeCNF) :
    gaussianPaperVariableAritySourceReducedStateOutput matrix
        (encodeThreeCNF formula) =
      effectiveGaussianPackedStateWord
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).effectiveGaussianState
        (encodeThreeCNF formula) := by
  unfold gaussianPaperVariableAritySourceReducedStateOutput
  rw [Function.comp_apply, matrix.output_valid formula]
  exact gaussianPhysicalSourceEliminationOutput_effective
    (physicalWordBinarySystem
      (encodeThreeCNF formula).length formula)
    (encodeThreeCNF formula)
    (paperVariableArityPhysicalWordBinarySystem_rowCount_pos
      (encodeThreeCNF formula).length formula)

end GaussianSourceInitializer

namespace GaussianAdaptivePhysicalReducedConsistencyCatalogueTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM
open GapCVP.OutputBoundedDependentRecordFold GapCVP.BinaryExplicitAffineRows
open GapCVP.GaussianPackedPivotColumnTM GapCVP.GaussianReducedConsistencyTM
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianAdaptivePhysicalStateCellTM GapCVP.GaussianAdaptivePackedStateLookupTM
open GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM

private def gaussianPhysicalReducedRowRecordWord
    (row width : ℕ) (state : List Bool) : List Bool :=
  lengthPrefixedWord (List.replicate row true) ++
    lengthPrefixedWord (List.replicate width true) ++ state

private def gaussianPhysicalReducedRowRank : List Bool → List Bool :=
  firstFieldContents

private noncomputable def gaussianPhysicalReducedRowRankComputable :
    BitTM
      gaussianPhysicalReducedRowRank :=
  firstFieldContentsComputable

private def gaussianPhysicalReducedRowState : List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix

private noncomputable def gaussianPhysicalReducedRowStateComputable :
    BitTM
      gaussianPhysicalReducedRowState :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable

private def gaussianPhysicalReducedNextUnary : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix ∘ firstFieldSuffix ∘
    gaussianPhysicalReducedRowState

private noncomputable def gaussianPhysicalReducedNextUnaryComputable :
    BitTM
      gaussianPhysicalReducedNextUnary := by
  have hcheck := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalReducedRowStateComputable
    firstFieldSuffixComputable
  have hrhs := GapCVP.TMComposition.computableInPolyTime
    hcheck firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hrhs firstFieldContentsComputable

private def gaussianPhysicalReducedRowEligibleWord :
    List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    (fourFamilyComputedUnaryLessBitOutput
      gaussianPhysicalReducedRowRank
      gaussianPhysicalReducedNextUnary)

private noncomputable def gaussianPhysicalReducedRowEligibleComputable :
    BitTM
      gaussianPhysicalReducedRowEligibleWord :=
  fourFamilyBooleanNotOutputComputable
    (fourFamilyComputedUnaryLessBitComputable
      gaussianPhysicalReducedRowRankComputable
      gaussianPhysicalReducedNextUnaryComputable)

private def gaussianPhysicalReducedRowRhsQuery
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (gaussianPhysicalReducedRowRank input) ++
    (lengthPrefixedWord [] ++ gaussianPhysicalReducedRowState input)

private noncomputable def gaussianPhysicalReducedRowRhsQueryComputable :
    BitTM
      gaussianPhysicalReducedRowRhsQuery := by
  have hrank := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalReducedRowRankComputable
    structuralPrefixWriterComputable
  have hzero :=
    GapCVP.SourceCanonicalFixedWordTuringTM.sourceFixedWordComputable
      (lengthPrefixedWord ([] : List Bool))
  have hphysical := pointwiseAppendComputable hrank
    (pointwiseAppendComputable hzero
      gaussianPhysicalReducedRowStateComputable)
  change BitTM
    (fun input =>
      lengthPrefixedWord (gaussianPhysicalReducedRowRank input) ++
        (lengthPrefixedWord [] ++
          gaussianPhysicalReducedRowState input))
  simpa only [Function.comp_apply] using hphysical

private def gaussianPhysicalReducedRowRhsWord : List Bool → List Bool :=
  gaussianPackedStateRhsCellWord ∘
    gaussianPhysicalReducedRowRhsQuery

private noncomputable def gaussianPhysicalReducedRowRhsComputable :
    BitTM
      gaussianPhysicalReducedRowRhsWord :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalReducedRowRhsQueryComputable
    gaussianPackedStateRhsCellComputable

private def gaussianPhysicalReducedRowOriginalSource :
    List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix ∘ firstFieldSuffix ∘
    firstFieldSuffix ∘ gaussianPhysicalReducedRowState

private noncomputable def gaussianPhysicalReducedRowOriginalSourceComputable :
    BitTM
      gaussianPhysicalReducedRowOriginalSource := by
  have hcheck := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalReducedRowStateComputable
    firstFieldSuffixComputable
  have hrhs := GapCVP.TMComposition.computableInPolyTime
    hcheck firstFieldSuffixComputable
  have hnext := GapCVP.TMComposition.computableInPolyTime
    hrhs firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hnext firstFieldSuffixComputable

private def gaussianPhysicalReducedRowPayload
    (input : List Bool) : List Bool :=
  gaussianPhysicalReducedRowEligibleWord input ++
    (gaussianPhysicalReducedRowRhsWord input ++
      gaussianPhysicalReducedRowOriginalSource input)

private noncomputable def gaussianPhysicalReducedRowPayloadComputable :
    BitTM
      gaussianPhysicalReducedRowPayload := by
  have hphysical := pointwiseAppendComputable
    gaussianPhysicalReducedRowEligibleComputable
    (pointwiseAppendComputable
      gaussianPhysicalReducedRowRhsComputable
      gaussianPhysicalReducedRowOriginalSourceComputable)
  change BitTM
    (fun input =>
      gaussianPhysicalReducedRowEligibleWord input ++
        (gaussianPhysicalReducedRowRhsWord input ++
          gaussianPhysicalReducedRowOriginalSource input))
  simpa only [Function.comp_apply] using hphysical

private def gaussianPhysicalReducedRowRecordOutput :
    List Bool → List Bool :=
  (fun payload => lengthPrefixedWord payload) ∘
    gaussianPhysicalReducedRowPayload

private noncomputable def gaussianPhysicalReducedRowRecordComputable :
    BitTM
      gaussianPhysicalReducedRowRecordOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalReducedRowPayloadComputable
    structuralPrefixWriterComputable

private noncomputable def gaussianPhysicalReducedRowWidth :
    SourceQaryMaskDynamicGridWidth where
  output := gaussianDenseStateRowCountUnary
  computer := gaussianDenseStateRowCountUnaryComputable

private def gaussianPhysicalReducedRowCatalogueOutput :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    gaussianPhysicalReducedRowWidth
    gaussianPhysicalReducedRowRecordComputable

private noncomputable def gaussianPhysicalReducedRowCatalogueComputable :
    BitTM
      gaussianPhysicalReducedRowCatalogueOutput :=
  maskDynamicGridRecordCatalogueComputable
    gaussianPhysicalReducedRowWidth
    gaussianPhysicalReducedRowRecordComputable

private def gaussianPhysicalReducedConsistencyQueryOutput
    (input : List Bool) : List Bool :=
  gaussianDenseStateRowCountUnary input ++
    (false :: gaussianPhysicalReducedRowCatalogueOutput input)

private noncomputable def gaussianPhysicalReducedConsistencyQueryComputable :
    BitTM
      gaussianPhysicalReducedConsistencyQueryOutput := by
  have htail := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalReducedRowCatalogueComputable
    (GapCVP.SourceMachineCert.prependBitComputable false)
  have hphysical := pointwiseAppendComputable
    gaussianDenseStateRowCountUnaryComputable htail
  change BitTM
    (fun input =>
      gaussianDenseStateRowCountUnary input ++
        (false :: gaussianPhysicalReducedRowCatalogueOutput input))
  simpa only [Function.comp_apply] using hphysical

@[simp] private theorem gaussianPhysicalReducedRowRank_word
    (row width : ℕ) (state : List Bool) :
    gaussianPhysicalReducedRowRank
        (gaussianPhysicalReducedRowRecordWord row width state) =
      List.replicate row true := by
  simp only [gaussianPhysicalReducedRowRank, gaussianPhysicalReducedRowRecordWord,
      List.append_assoc,
      firstFieldContents_valid]

@[simp] private theorem gaussianPhysicalReducedRowState_word
    (row width : ℕ) (state : List Bool) :
    gaussianPhysicalReducedRowState
        (gaussianPhysicalReducedRowRecordWord row width state) =
      state := by
  simp only [gaussianPhysicalReducedRowState, gaussianPhysicalReducedRowRecordWord,
      List.append_assoc,
      Function.comp_apply, firstFieldSuffix_valid]

@[simp] private theorem gaussianPhysicalReducedNextUnary_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row width : ℕ) :
    gaussianPhysicalReducedNextUnary
        (gaussianPhysicalReducedRowRecordWord row width
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate state.nextPivot true := by
  simp only [gaussianPhysicalReducedNextUnary, effectiveGaussianPackedStateWord, List.append_assoc,
      Function.comp_apply, gaussianPhysicalReducedRowState_word, firstFieldSuffix_valid,
          firstFieldContents_valid]

private theorem gaussianPhysicalReducedRowEligibleWord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row width : ℕ) :
    gaussianPhysicalReducedRowEligibleWord
        (gaussianPhysicalReducedRowRecordWord row width
          (effectiveGaussianPackedStateWord state source)) =
      [decide (state.nextPivot ≤ row)] := by
  let input := gaussianPhysicalReducedRowRecordWord row width
    (effectiveGaussianPackedStateWord state source)
  have hless := fourFamilyComputedUnaryLessBitOutput_valid
    gaussianPhysicalReducedRowRank
    gaussianPhysicalReducedNextUnary input row state.nextPivot
    (gaussianPhysicalReducedRowRank_word row width
      (effectiveGaussianPackedStateWord state source))
    (gaussianPhysicalReducedNextUnary_word
      state source row width)
  change gaussianPhysicalReducedRowEligibleWord input = _
  unfold gaussianPhysicalReducedRowEligibleWord
  rw [fourFamilyBooleanNotOutput_bit _ input _ hless]
  by_cases hlt : row < state.nextPivot
  · have hnot : ¬ state.nextPivot ≤ row := by omega
    simp only [hlt, decide_true, Bool.not_true, hnot, decide_false]
  · have hle : state.nextPivot ≤ row := by omega
    simp only [hlt, decide_false, Bool.not_false, hle, decide_true]

@[simp] private theorem gaussianPhysicalReducedRowRhsQuery_word
    (row width : ℕ) (state : List Bool) :
    gaussianPhysicalReducedRowRhsQuery
        (gaussianPhysicalReducedRowRecordWord row width state) =
      affineCellQuery row 0 state := by
  simp only [gaussianPhysicalReducedRowRhsQuery, gaussianPhysicalReducedRowRank_word,
      gaussianPhysicalReducedRowState_word, affineCellQuery, List.replicate_zero,
          List.append_assoc]

private theorem gaussianPhysicalReducedRowRhsWord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row : Fin m) (width : ℕ) :
    gaussianPhysicalReducedRowRhsWord
        (gaussianPhysicalReducedRowRecordWord row.val width
          (effectiveGaussianPackedStateWord state source)) =
      [decide (state.system.rhs row = (1 : ZMod 2))] := by
  unfold gaussianPhysicalReducedRowRhsWord
  rw [Function.comp_apply,
    gaussianPhysicalReducedRowRhsQuery_word]
  exact gaussianPackedStateRhsCellWord_query
    state source row 0

@[simp] private theorem gaussianPhysicalReducedRowOriginalSource_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row width : ℕ) :
    gaussianPhysicalReducedRowOriginalSource
        (gaussianPhysicalReducedRowRecordWord row width
          (effectiveGaussianPackedStateWord state source)) =
      source := by
  simp only [gaussianPhysicalReducedRowOriginalSource, effectiveGaussianPackedStateWord,
      List.append_assoc,
      Function.comp_apply, gaussianPhysicalReducedRowState_word, firstFieldSuffix_valid]

private theorem gaussianPhysicalReducedRowPayload_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row : Fin m) (width : ℕ) :
    gaussianPhysicalReducedRowPayload
        (gaussianPhysicalReducedRowRecordWord row.val width
          (effectiveGaussianPackedStateWord state source)) =
      binaryGaussianPackedPivotRowQuery
        (decide (state.nextPivot ≤ row.val))
        (decide (state.system.rhs row = (1 : ZMod 2))) source := by
  unfold gaussianPhysicalReducedRowPayload
    binaryGaussianPackedPivotRowQuery
  rw [gaussianPhysicalReducedRowEligibleWord_effective
    state source row.val width,
    gaussianPhysicalReducedRowRhsWord_effective
      state source row width,
    gaussianPhysicalReducedRowOriginalSource_effective]
  rfl

private theorem gaussianPhysicalReducedRowRecordOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row : Fin m) (width : ℕ) :
    gaussianPhysicalReducedRowRecordOutput
        (gaussianPhysicalReducedRowRecordWord row.val width
          (effectiveGaussianPackedStateWord state source)) =
      lengthPrefixedWord
        (binaryGaussianPackedPivotRowQuery
          (decide (state.nextPivot ≤ row.val))
          (decide (state.system.rhs row = (1 : ZMod 2))) source) := by
  unfold gaussianPhysicalReducedRowRecordOutput
  rw [Function.comp_apply,
    gaussianPhysicalReducedRowPayload_effective
      state source row width]

private theorem gaussianPhysicalReducedRowWidth_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) :
    gaussianPhysicalReducedRowWidth.output
        (effectiveGaussianPackedStateWord state source) =
      List.replicate m true := by
  exact gaussianDenseStateRowCountUnary_effective
    state source

private theorem gaussianPhysicalReducedRowCatalogueOutput_valid
    (input : List Bool) (count : ℕ)
    (hwidth : gaussianPhysicalReducedRowWidth.output input =
      List.replicate count true) :
    gaussianPhysicalReducedRowCatalogueOutput input =
      (List.range count).flatMap (fun rank =>
        gaussianPhysicalReducedRowRecordOutput
          (lengthPrefixedWord (List.replicate rank true) ++
            sourceQaryMaskDynamicGridBaseSource
              gaussianPhysicalReducedRowWidth input)) := by
  exact maskDynamicGridRecordCatalogueOutput_valid
    gaussianPhysicalReducedRowWidth
    gaussianPhysicalReducedRowRecordComputable
    input count hwidth

private theorem gaussianPhysicalReducedGeneratedRecord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (rank : ℕ) :
    lengthPrefixedWord (List.replicate rank true) ++
        sourceQaryMaskDynamicGridBaseSource
          gaussianPhysicalReducedRowWidth
          (effectiveGaussianPackedStateWord state source) =
      gaussianPhysicalReducedRowRecordWord rank m
        (effectiveGaussianPackedStateWord state source) := by
  unfold sourceQaryMaskDynamicGridBaseSource
  rw [gaussianPhysicalReducedRowWidth_effective state source]
  simp only [gaussianPhysicalReducedRowRecordWord,
    List.append_assoc]

private theorem gaussianPhysicalReducedRowCatalogueOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) :
    gaussianPhysicalReducedRowCatalogueOutput
        (effectiveGaussianPackedStateWord state source) =
      sourceMixedRadixOriginalSourceQueryStream
        ((effectiveGaussianStateReducedConsistencyRows state).map
          (fun row => binaryGaussianPackedPivotRowQuery
            row.1 row.2 source)) := by
  let input := effectiveGaussianPackedStateWord state source
  have hwidth : gaussianPhysicalReducedRowWidth.output input =
      List.replicate m true :=
    gaussianPhysicalReducedRowWidth_effective state source
  have hcatalogue := gaussianPhysicalReducedRowCatalogueOutput_valid
    input m hwidth
  calc
    gaussianPhysicalReducedRowCatalogueOutput input =
        (List.range m).flatMap (fun rank =>
          gaussianPhysicalReducedRowRecordOutput
            (lengthPrefixedWord (List.replicate rank true) ++
              sourceQaryMaskDynamicGridBaseSource
                gaussianPhysicalReducedRowWidth input)) :=
      hcatalogue
    _ = (List.range m).flatMap (fun rank =>
          gaussianPhysicalReducedRowRecordOutput
            (gaussianPhysicalReducedRowRecordWord rank m
              (effectiveGaussianPackedStateWord state source))) := by
      apply List.flatMap_congr
      intro rank _
      exact congrArg gaussianPhysicalReducedRowRecordOutput
        (gaussianPhysicalReducedGeneratedRecord_effective
          state source rank)
    _ = (List.finRange m).flatMap (fun row =>
          lengthPrefixedWord
            (binaryGaussianPackedPivotRowQuery
              (decide (state.nextPivot ≤ row.val))
              (decide (state.system.rhs row = (1 : ZMod 2)))
              source)) := by
      rw [gaussianPhysicalPivot_range_flatMap_finRange]
      apply List.flatMap_congr
      intro row _
      exact gaussianPhysicalReducedRowRecordOutput_effective
        state source row m
    _ = sourceMixedRadixOriginalSourceQueryStream
          ((effectiveGaussianStateReducedConsistencyRows state).map
            (fun row => binaryGaussianPackedPivotRowQuery
              row.1 row.2 source)) := by
      unfold sourceMixedRadixOriginalSourceQueryStream
        effectiveGaussianStateReducedConsistencyRows
      simp only [List.flatMap_map, List.map_map,
        Function.comp_apply]

private theorem gaussianPhysicalReducedConsistencyQueryOutput_state_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) :
    gaussianPhysicalReducedConsistencyQueryOutput
        (effectiveGaussianPackedStateWord state source) =
      effectiveGaussianStateReducedConsistencyQuery state source := by
  unfold gaussianPhysicalReducedConsistencyQueryOutput
  rw [gaussianDenseStateRowCountUnary_effective,
    gaussianPhysicalReducedRowCatalogueOutput_effective]
  unfold effectiveGaussianStateReducedConsistencyQuery
    binaryGaussianPackedPivotColumnWord
    unaryBoundedFoldWord
  simp only [effectiveGaussianStateReducedConsistencyRows,
    List.length_map, List.length_finRange]

private theorem gaussianPhysicalReducedConsistencyQueryOutput_effective
    (system : BinaryAffineSystem) (source : List Bool) :
    gaussianPhysicalReducedConsistencyQueryOutput
        (effectiveGaussianPackedStateWord
          system.effectiveGaussianState source) =
      effectiveGaussianReducedConsistencyQuery system source := by
  exact gaussianPhysicalReducedConsistencyQueryOutput_state_effective
    system.effectiveGaussianState source

end GaussianAdaptivePhysicalReducedConsistencyCatalogueTM

namespace GaussianSourceReducedConsistency

open Turing GapCVP.BinaryEncoding GapCVP.PhysicalColumnOrder GapCVP.GaussianSourceInitializer
open GapCVP.GaussianAdaptivePhysicalReducedConsistencyCatalogueTM
open GapCVP.GaussianReducedConsistencyTM

private def gaussianPaperVariableAritySourceReducedConsistencyQueryOutput
    (matrix : PaperVariableArityPhysicalPackedMatrixSourceComputer) :
    List Bool → List Bool :=
  gaussianPhysicalReducedConsistencyQueryOutput ∘
    gaussianPaperVariableAritySourceReducedStateOutput matrix

/-- GapCVP reduction support. -/
noncomputable def
    gaussianPaperVariableAritySourceReducedConsistencyQueryComputable
    (matrix : PaperVariableArityPhysicalPackedMatrixSourceComputer) :
    BitTM
      (gaussianPaperVariableAritySourceReducedConsistencyQueryOutput
        matrix) :=
  GapCVP.TMComposition.computableInPolyTime
    (gaussianPaperVariableAritySourceReducedStateComputable matrix)
    gaussianPhysicalReducedConsistencyQueryComputable

private theorem gaussianPaperVariableAritySourceReducedConsistencyQueryOutput_valid
    (matrix : PaperVariableArityPhysicalPackedMatrixSourceComputer)
    (formula : ThreeCNF) :
    gaussianPaperVariableAritySourceReducedConsistencyQueryOutput matrix
        (encodeThreeCNF formula) =
      effectiveGaussianReducedConsistencyQuery
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula)
        (encodeThreeCNF formula) := by
  unfold gaussianPaperVariableAritySourceReducedConsistencyQueryOutput
  rw [Function.comp_apply,
    gaussianPaperVariableAritySourceReducedStateOutput_effective
      matrix formula]
  exact gaussianPhysicalReducedConsistencyQueryOutput_effective
    (physicalWordBinarySystem
      (encodeThreeCNF formula).length formula)
    (encodeThreeCNF formula)

end GaussianSourceReducedConsistency

namespace GaussianSourceInitializerInstantiation

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.CanonicalMatrixShape
open GapCVP.CanonicalSourceCatalogue GapCVP.PhysicalColumnOrder
open GapCVP.GaussianAdaptivePackedTraceCorrectness GapCVP.GaussianReducedConsistencyTM
open GapCVP.GaussianSourceInitializer GapCVP.GaussianSourceReducedConsistency

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityCanonicalPhysicalPackedMatrixSourceComputer
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    PaperVariableArityPhysicalPackedMatrixSourceComputer where
  output := paperCanonicalBinaryMatrixPackedOutput worker
  computer := paperVariableArityCanonicalBinaryMatrixPackedComputable worker
  output_valid := paperVariableArityCanonicalBinaryMatrixPackedOutput_valid worker

/-- GapCVP reduction support. -/
def gaussianPaperVariableArityCanonicalSourceReducedStateOutput
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    List Bool → List Bool :=
  gaussianPaperVariableAritySourceReducedStateOutput
    (paperVariableArityCanonicalPhysicalPackedMatrixSourceComputer worker)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPaperVariableArityCanonicalSourceReducedStateComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (gaussianPaperVariableArityCanonicalSourceReducedStateOutput worker) :=
  gaussianPaperVariableAritySourceReducedStateComputable
    (paperVariableArityCanonicalPhysicalPackedMatrixSourceComputer worker)

theorem gaussianPaperVariableArityCanonicalSourceReducedStateOutput_effective
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF) :
    gaussianPaperVariableArityCanonicalSourceReducedStateOutput worker
        (encodeThreeCNF formula) =
      effectiveGaussianPackedStateWord
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).effectiveGaussianState
        (encodeThreeCNF formula) :=
  gaussianPaperVariableAritySourceReducedStateOutput_effective
    (paperVariableArityCanonicalPhysicalPackedMatrixSourceComputer worker)
    formula

private def gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryOutput
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    List Bool → List Bool :=
  gaussianPaperVariableAritySourceReducedConsistencyQueryOutput
    (paperVariableArityCanonicalPhysicalPackedMatrixSourceComputer worker)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryOutput
        worker) :=
  gaussianPaperVariableAritySourceReducedConsistencyQueryComputable
    (paperVariableArityCanonicalPhysicalPackedMatrixSourceComputer worker)

theorem
    gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryOutput_valid
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF) :
    gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryOutput
        worker (encodeThreeCNF formula) =
      effectiveGaussianReducedConsistencyQuery
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula)
        (encodeThreeCNF formula) :=
  gaussianPaperVariableAritySourceReducedConsistencyQueryOutput_valid
    (paperVariableArityCanonicalPhysicalPackedMatrixSourceComputer worker)
    formula

end GaussianSourceInitializerInstantiation

namespace GaussianOutputSerializerTM

open Turing GapCVP.Core GapCVP.Factor400BinaryInstanceBridge GapCVP.BinaryEncoding
open GapCVP.SourceMachineCert GapCVP.CLStructuralPrefixWriter
open GapCVP.CLStructuralAtomicNaturalWriter GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.BinaryDimensionTM GapCVP.BinaryExplicitAffineRows GapCVP.BinaryStructuralRecordTM
open GapCVP.BinaryGaussianStructuralAtomTM GapCVP.BinaryGaussianStructuralRecordIndex
open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.GaussianPhysicalWordRankIndexTM
open GapCVP.GaussianPackedStateTargetAtomTM GapCVP.GaussianPackedStateBasisAtomTM
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.Factor400BinaryCompactPhysicalGaussianOutputSerializerTM GapCVP.CanonicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

/-- GapCVP reduction support. -/
noncomputable def paperGaussianSourceDimensionWidth
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    SourceQaryMaskDynamicGridWidth where
  output := shape.columns
  computer := shape.columnsComputable

theorem paperVariableArityGaussianSourceDimensionWidth_valid
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) :
    (paperGaussianSourceDimensionWidth shape).output
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension true := by
  change shape.columns (encodeThreeCNF formula) = _
  have actual := shape.columnsCorrect formula
  rw [shape.systemCorrect] at actual
  exact actual

/-- GapCVP reduction support. -/
def paperGaussianRankDimensionUnary
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    List Bool → List Bool :=
  shape.columns ∘ structuralRankOriginalSource

private noncomputable def paperGaussianRankDimensionComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperGaussianRankDimensionUnary shape) :=
  GapCVP.TMComposition.computableInPolyTime
    structuralRankOriginalSourceComputable shape.columnsComputable

theorem paperGaussianRankDimensionUnary_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) (rank : ℕ) :
    paperGaussianRankDimensionUnary shape
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      List.replicate
        (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension true := by
  unfold paperGaussianRankDimensionUnary
  rw [Function.comp_apply, structuralRankOriginalSource_query]
  exact paperVariableArityGaussianSourceDimensionWidth_valid shape formula

/-- GapCVP reduction support. -/
def paperGaussianRankDimensionAtomicOutput
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    List Bool → List Bool :=
  structuralAtomicNaturalWord ∘
    paperGaussianRankDimensionUnary shape

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityGaussianRankDimensionAtomicComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperGaussianRankDimensionAtomicOutput shape) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperGaussianRankDimensionComputable shape)
    structuralAtomicNaturalWriterComputable

/-- GapCVP reduction support. -/
def paperGaussianRankTargetBound
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (input : List Bool) : List Bool :=
  true :: true :: paperGaussianRankDimensionUnary shape input

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityGaussianRankTargetBoundComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperGaussianRankTargetBound shape) := by
  have once := GapCVP.TMComposition.computableInPolyTime
    (paperGaussianRankDimensionComputable shape)
    (prependBitComputable true)
  exact GapCVP.TMComposition.computableInPolyTime
    once (prependBitComputable true)

theorem paperVariableArityGaussianRankTargetBound_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) (rank : ℕ) :
    paperGaussianRankTargetBound shape
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      List.replicate
        (2 + (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension) true := by
  unfold paperGaussianRankTargetBound
  rw [paperGaussianRankDimensionUnary_query]
  rw [show 2 + (physicalFormulaSystem
      (encodeThreeCNF formula).length formula).dimension =
    Nat.succ (Nat.succ (physicalFormulaSystem
      (encodeThreeCNF formula).length formula).dimension) by omega]
  simp only [paperVariableArityPhysicalFormulaSystem_dimension, Nat.succ_eq_add_one,
      List.replicate_succ]

private def paperGaussianBasisFlatUnary
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    List Bool → List Bool :=
  unarySubtractionOutput structuralRankUnary
    (paperGaussianRankTargetBound shape)

private noncomputable def paperVariableArityGaussianBasisFlatComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperGaussianBasisFlatUnary shape) :=
  unarySubtractionComputable structuralRankUnaryComputable
    (paperVariableArityGaussianRankTargetBoundComputable shape)

private theorem paperVariableArityGaussianBasisFlatUnary_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) (rank : ℕ) :
    paperGaussianBasisFlatUnary shape
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      List.replicate
        (rank - (2 + (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension)) true := by
  exact unarySubtractionOutput_valid structuralRankUnary
    (paperGaussianRankTargetBound shape)
    (constructiveStructuralRankQuery
      (paperGaussianSourceDimensionWidth shape)
      (encodeThreeCNF formula) rank)
    rank
    (2 + (physicalFormulaSystem
      (encodeThreeCNF formula).length formula).dimension)
    (structuralRankUnary_query
      (paperGaussianSourceDimensionWidth shape)
      (encodeThreeCNF formula) rank)
    (paperVariableArityGaussianRankTargetBound_query
      shape formula rank)

/-- GapCVP reduction support. -/
def paperGaussianBasisRowUnary
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryQuotient
    (paperGaussianBasisFlatUnary shape)
    (paperGaussianRankDimensionUnary shape)

private noncomputable def paperVariableArityGaussianBasisRowComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperGaussianBasisRowUnary shape) :=
  sourcePhysicalComputedUnaryQuotientComputable
    (paperVariableArityGaussianBasisFlatComputable shape)
    (paperGaussianRankDimensionComputable shape)

/-- GapCVP reduction support. -/
def paperGaussianBasisColumnUnary
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryRemainder
    (paperGaussianBasisFlatUnary shape)
    (paperGaussianRankDimensionUnary shape)

private noncomputable def paperVariableArityGaussianBasisColumnComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperGaussianBasisColumnUnary shape) :=
  sourcePhysicalComputedUnaryRemainderComputable
    (paperVariableArityGaussianBasisFlatComputable shape)
    (paperGaussianRankDimensionComputable shape)

theorem paperVariableArityGaussianBasisRowUnary_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) (rank : ℕ) :
    paperGaussianBasisRowUnary shape
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      List.replicate
        ((rank - (2 + (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension)) /
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).dimension) true := by
  exact sourcePhysicalComputedUnaryQuotient_valid
    (paperGaussianBasisFlatUnary shape)
    (paperGaussianRankDimensionUnary shape)
    (constructiveStructuralRankQuery
      (paperGaussianSourceDimensionWidth shape)
      (encodeThreeCNF formula) rank)
    (rank - (2 + (physicalFormulaSystem
      (encodeThreeCNF formula).length formula).dimension))
    (physicalFormulaSystem
      (encodeThreeCNF formula).length formula).dimension
    (physicalFormulaSystem_dimension_pos
      (encodeThreeCNF formula).length formula)
    (paperVariableArityGaussianBasisFlatUnary_query shape formula rank)
    (paperGaussianRankDimensionUnary_query
      shape formula rank)

theorem paperVariableArityGaussianBasisColumnUnary_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) (rank : ℕ) :
    paperGaussianBasisColumnUnary shape
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      List.replicate
        ((rank - (2 + (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension)) %
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).dimension) true := by
  exact sourcePhysicalComputedUnaryRemainder_valid
    (paperGaussianBasisFlatUnary shape)
    (paperGaussianRankDimensionUnary shape)
    (constructiveStructuralRankQuery
      (paperGaussianSourceDimensionWidth shape)
      (encodeThreeCNF formula) rank)
    (rank - (2 + (physicalFormulaSystem
      (encodeThreeCNF formula).length formula).dimension))
    (physicalFormulaSystem
      (encodeThreeCNF formula).length formula).dimension
    (physicalFormulaSystem_dimension_pos
      (encodeThreeCNF formula).length formula)
    (paperVariableArityGaussianBasisFlatUnary_query shape formula rank)
    (paperGaussianRankDimensionUnary_query
      shape formula rank)

/-- GapCVP reduction support. -/
def paperGaussianRankBasisStateQuery
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (reduced : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (paperGaussianBasisRowUnary shape input) ++
    (lengthPrefixedWord
      (paperGaussianBasisColumnUnary shape input) ++
      compactPhysicalGaussianRankReducedState reduced input)

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityGaussianRankBasisStateQueryComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (computer : BitTM reduced) :
    BitTM
      (paperGaussianRankBasisStateQuery shape reduced) := by
  have row := GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityGaussianBasisRowComputable shape)
    structuralPrefixWriterComputable
  have column := GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityGaussianBasisColumnComputable shape)
    structuralPrefixWriterComputable
  have tail := pointwiseAppendComputable column
    (compactPhysicalGaussianRankReducedStateComputable computer)
  have physical := pointwiseAppendComputable row tail
  change BitTM
    (fun input =>
      lengthPrefixedWord
          (paperGaussianBasisRowUnary shape input) ++
        (lengthPrefixedWord
          (paperGaussianBasisColumnUnary shape input) ++
          compactPhysicalGaussianRankReducedState reduced input))
  simpa only [Function.comp_apply] using physical

private def paperGaussianRankBasisAtom
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (reduced : List Bool → List Bool) : List Bool → List Bool :=
  gaussianPackedIndexedBasisAtom ∘
    paperGaussianRankBasisStateQuery shape reduced

private noncomputable def paperVariableArityGaussianRankBasisAtomComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (computer : BitTM reduced) :
    BitTM
      (paperGaussianRankBasisAtom shape reduced) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityGaussianRankBasisStateQueryComputable
      shape computer)
    gaussianPackedIndexedBasisAtomComputable

private def paperGaussianStructuralAtomOutput
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (radius reduced : List Bool → List Bool) : List Bool → List Bool :=
  binaryGaussianDynamicBranchOutput
    (structuralRankLessBit structuralRankOneBound)
    (paperGaussianRankDimensionAtomicOutput shape)
    (binaryGaussianDynamicBranchOutput
      (structuralRankLessBit structuralRankTwoBound)
      (compactPhysicalGaussianRankRadiusAtom radius)
      (binaryGaussianDynamicBranchOutput
        (structuralRankLessBit
          (paperGaussianRankTargetBound shape))
        (compactPhysicalGaussianRankTargetAtom reduced)
        (paperGaussianRankBasisAtom shape reduced)))

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityGaussianStructuralAtomComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {radius reduced : List Bool → List Bool}
    (radiusComputer : BitTM radius)
    (reducedComputer : BitTM reduced) :
    BitTM
      (paperGaussianStructuralAtomOutput
        shape radius reduced) := by
  have tail := binaryGaussianDynamicBranchComputable
    (structuralRankLessSelectionComputable
      (paperVariableArityGaussianRankTargetBoundComputable shape))
    (compactPhysicalGaussianRankTargetAtomComputable reducedComputer)
    (paperVariableArityGaussianRankBasisAtomComputable
      shape reducedComputer)
  have scalar := binaryGaussianDynamicBranchComputable
    (structuralRankLessSelectionComputable
      structuralRankTwoBoundComputable)
    (compactPhysicalGaussianRankRadiusAtomComputable radiusComputer)
    tail
  exact binaryGaussianDynamicBranchComputable
    (structuralRankLessSelectionComputable
      structuralRankOneBoundComputable)
    (paperVariableArityGaussianRankDimensionAtomicComputable shape)
    scalar

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityGaussianStructuralAtomComputer
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {radius reduced : List Bool → List Bool}
    (radiusComputer : BitTM radius)
    (reducedComputer : BitTM reduced) :
    ConstructiveStructuralAtomComputer :=
  compactPhysicalGaussianStructuralAtomComputerPack
    (paperGaussianStructuralAtomOutput
      shape radius reduced)
    (paperVariableArityGaussianStructuralAtomComputable
      shape radiusComputer reducedComputer)

@[simp] private theorem paperVariableArityGaussianStructuralAtomComputer_output
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {radius reduced : List Bool → List Bool}
    (radiusComputer : BitTM radius)
    (reducedComputer : BitTM reduced)
    (input : List Bool) :
    (paperVariableArityGaussianStructuralAtomComputer
      shape radiusComputer reducedComputer).output input =
      paperGaussianStructuralAtomOutput
        shape radius reduced input := by
  unfold paperVariableArityGaussianStructuralAtomComputer
  exact compactPhysicalGaussianStructuralAtomComputerPack_output
    (paperGaussianStructuralAtomOutput
      shape radius reduced)
    (paperVariableArityGaussianStructuralAtomComputable
      shape radiusComputer reducedComputer) input

/-- GapCVP reduction support. -/
noncomputable def paperGaussianStructuralSourceWord
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {radius reduced : List Bool → List Bool}
    (radiusComputer : BitTM radius)
    (reducedComputer : BitTM reduced) : List Bool → List Bool :=
  constructiveStructuralSourceWord
    (paperGaussianSourceDimensionWidth shape)
    (paperVariableArityGaussianStructuralAtomComputer
      shape radiusComputer reducedComputer)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityGaussianStructuralSourceWordComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {radius reduced : List Bool → List Bool}
    (radiusComputer : BitTM radius)
    (reducedComputer : BitTM reduced) :
    BitTM
      (paperGaussianStructuralSourceWord
        shape radiusComputer reducedComputer) :=
  constructiveStructuralSourceWordComputable
    (paperGaussianSourceDimensionWidth shape)
    (paperVariableArityGaussianStructuralAtomComputer
      shape radiusComputer reducedComputer)

theorem paperGaussianRankReducedState_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (formula : ThreeCNF) (rank : ℕ)
    (actual :
      reduced (encodeThreeCNF formula) =
        effectiveGaussianPackedStateWord
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).effectiveGaussianState
          (encodeThreeCNF formula)) :
    compactPhysicalGaussianRankReducedState reduced
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      effectiveGaussianPackedStateWord
        (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).effectiveGaussianState
        (encodeThreeCNF formula) := by
  unfold compactPhysicalGaussianRankReducedState
  rw [Function.comp_apply, structuralRankOriginalSource_query, actual]

private theorem paperVariableArityGaussianRankTargetAtom_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (formula : ThreeCNF) (rank : ℕ)
    (index : Fin
      (physicalFormulaSystem
        (encodeThreeCNF formula).length formula).dimension)
    (indexCorrect : rank - 2 = index.val)
    (actual :
      reduced (encodeThreeCNF formula) =
        effectiveGaussianPackedStateWord
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).effectiveGaussianState
          (encodeThreeCNF formula)) :
    compactPhysicalGaussianRankTargetAtom reduced
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      encodeAtomic
        (((physicalFormulaSystem
          (encodeThreeCNF formula).length formula).effectiveAffineRepresentative
            index : ℤ) : ℚ) := by
  unfold compactPhysicalGaussianRankTargetAtom
  rw [Function.comp_apply]
  unfold compactPhysicalGaussianRankTargetStateQuery
  rw [factor400PhysicalWordGaussianTargetCoordinateUnary_query,
    paperGaussianRankReducedState_query
      shape formula rank actual, indexCorrect]
  exact gaussianPackedIndexedTargetAtom_effective
    (physicalFormulaSystem
      (encodeThreeCNF formula).length formula)
    index (encodeThreeCNF formula)

private theorem paperVariableArityGaussianRankBasisAtom_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (formula : ThreeCNF) (rank : ℕ)
    (row column : Fin
      (physicalFormulaSystem
        (encodeThreeCNF formula).length formula).dimension)
    (rowCorrect :
      (rank - (2 + (physicalFormulaSystem
        (encodeThreeCNF formula).length formula).dimension)) /
        (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension = row.val)
    (columnCorrect :
      (rank - (2 + (physicalFormulaSystem
        (encodeThreeCNF formula).length formula).dimension)) %
        (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension = column.val)
    (actual :
      reduced (encodeThreeCNF formula) =
        effectiveGaussianPackedStateWord
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).effectiveGaussianState
          (encodeThreeCNF formula)) :
    paperGaussianRankBasisAtom shape reduced
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      encodeAtomic
        ((physicalFormulaSystem
          (encodeThreeCNF formula).length formula).effectiveSquareBasisMatrix
          row column) := by
  unfold paperGaussianRankBasisAtom
  rw [Function.comp_apply]
  unfold paperGaussianRankBasisStateQuery
  rw [paperVariableArityGaussianBasisRowUnary_query
        shape formula rank,
      paperVariableArityGaussianBasisColumnUnary_query
        shape formula rank,
      paperGaussianRankReducedState_query
        shape formula rank actual,
      rowCorrect, columnCorrect]
  simpa only [gaussianPackedIndexedBasisStateWord,
    affineCellQuery, List.append_assoc] using
    gaussianPackedIndexedBasisAtom_effective
      (physicalFormulaSystem
        (encodeThreeCNF formula).length formula)
      row column (encodeThreeCNF formula)

private theorem paperVariableArityGaussianStructuralAtomOutput_correct
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {radius reduced : List Bool → List Bool}
    (formula : ThreeCNF)
    (radiusValue : ℚ)
    (radiusPositive : 0 < radiusValue)
    (actualRadius :
      radius (encodeThreeCNF formula) = encodeAtomic radiusValue)
    (actualReduced :
      reduced (encodeThreeCNF formula) =
        effectiveGaussianPackedStateWord
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).effectiveGaussianState
          (encodeThreeCNF formula))
    (rank : ℕ)
    (recordBound :
      rank <
        (sourceLatticeStructuralRecords
          (effectiveGapCVPInstance
            (physicalFormulaSystem
              (encodeThreeCNF formula).length formula)
            (physicalFormulaSystem_dimension_pos
              (encodeThreeCNF formula).length formula)
            radiusValue radiusPositive)).length) :
    paperGaussianStructuralAtomOutput
        shape radius reduced
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      (sourceLatticeStructuralRecords
        (effectiveGapCVPInstance
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula)
          (physicalFormulaSystem_dimension_pos
            (encodeThreeCNF formula).length formula)
          radiusValue radiusPositive)).getD rank [] := by
  let source := encodeThreeCNF formula
  let system := physicalFormulaSystem
    source.length formula
  let positiveDimension :=
    physicalFormulaSystem_dimension_pos
      source.length formula
  let lattice := effectiveGapCVPInstance
    system positiveDimension radiusValue radiusPositive
  let width := paperGaussianSourceDimensionWidth shape
  let query := constructiveStructuralRankQuery width source rank
  have one :
      structuralRankLessBit structuralRankOneBound query =
        decide (rank < 1) :=
    structuralRankOneDecision_query width source rank
  have two :
      structuralRankLessBit structuralRankTwoBound query =
        decide (rank < 2) :=
    structuralRankTwoDecision_query width source rank
  have boundary :
      paperGaussianRankTargetBound shape query =
        List.replicate (2 + lattice.dimension) true := by
    have dimension : lattice.dimension = system.dimension := rfl
    rw [dimension]
    simpa only [query, source, width, system] using
      paperVariableArityGaussianRankTargetBound_query
        shape formula rank
  have target :
      structuralRankLessBit
        (paperGaussianRankTargetBound shape) query =
          decide (rank < 2 + lattice.dimension) :=
    structuralRankLessBit_valid
      (paperGaussianRankTargetBound shape)
      query rank (2 + lattice.dimension)
      (structuralRankUnary_query width source rank) boundary
  change paperGaussianStructuralAtomOutput
    shape radius reduced query =
    (sourceLatticeStructuralRecords lattice).getD rank []
  unfold paperGaussianStructuralAtomOutput
    binaryGaussianDynamicBranchOutput
  rw [one]
  by_cases zeroRank : rank < 1
  · rw [decide_eq_true zeroRank, ite_eq_left (by decide)]
    have exactRank : rank = 0 := by omega
    subst rank
    change
      paperGaussianRankDimensionAtomicOutput shape
          (constructiveStructuralRankQuery width source 0) =
        (sourceLatticeStructuralRecords lattice).getD 0 []
    unfold paperGaussianRankDimensionAtomicOutput
    rw [Function.comp_apply]
    change
      structuralAtomicNaturalWord
          (paperGaussianRankDimensionUnary shape
            (constructiveStructuralRankQuery
              (paperGaussianSourceDimensionWidth shape)
              (encodeThreeCNF formula) 0)) =
        (sourceLatticeStructuralRecords lattice).getD 0 []
    rw [paperGaussianRankDimensionUnary_query
      shape formula 0,
      sourceLatticeStructuralRecords_getD_dimension lattice]
    simp only [structuralAtomicNaturalWord, List.length_replicate]
    rfl
  · rw [decide_eq_false zeroRank, ite_eq_right (by decide), two]
    by_cases radiusRank : rank < 2
    · rw [decide_eq_true radiusRank, ite_eq_left (by decide)]
      have exactRank : rank = 1 := by omega
      subst rank
      change
        compactPhysicalGaussianRankRadiusAtom radius
            (constructiveStructuralRankQuery width source 1) =
          (sourceLatticeStructuralRecords lattice).getD 1 []
      unfold compactPhysicalGaussianRankRadiusAtom
      rw [Function.comp_apply, structuralRankOriginalSource_query]
      change radius (encodeThreeCNF formula) =
        (sourceLatticeStructuralRecords lattice).getD 1 []
      rw [actualRadius,
        sourceLatticeStructuralRecords_getD_radius lattice]
      rfl
    · rw [decide_eq_false radiusRank, ite_eq_right (by decide), target]
      by_cases targetRank : rank < 2 + lattice.dimension
      · rw [decide_eq_true targetRank, ite_eq_left (by decide)]
        have dimension : lattice.dimension = system.dimension := rfl
        have indexBound : rank - 2 < system.dimension := by omega
        let index : Fin system.dimension := ⟨rank - 2, indexBound⟩
        have exactRank : rank = 2 + index.val := by
          dsimp [index]
          omega
        have atom := paperVariableArityGaussianRankTargetAtom_query
          shape formula rank index rfl actualReduced
        have exactRecord :
            (sourceLatticeStructuralRecords lattice).getD rank [] =
              encodeAtomic
                ((system.effectiveAffineRepresentative index : ℤ) : ℚ) := by
          rw [exactRank,
            sourceLatticeStructuralRecords_getD_target lattice index]
          rfl
        rw [exactRecord]
        exact atom
      · rw [decide_eq_false targetRank, ite_eq_right (by decide)]
        have positive : 0 < system.dimension := positiveDimension
        have dimension : lattice.dimension = system.dimension := rfl
        have latticeRecords :
            rank < 2 + lattice.dimension +
              lattice.dimension * lattice.dimension := by
          simpa only [sourceLatticeStructuralRecords_length]
            using recordBound
        rw [dimension] at latticeRecords
        have records :
            rank < 2 + system.dimension +
              system.dimension * system.dimension := latticeRecords
        have start : 2 + system.dimension ≤ rank := by omega
        have offset :
            rank - (2 + system.dimension) <
              system.dimension * system.dimension := by omega
        have rowBound :
            (rank - (2 + system.dimension)) / system.dimension <
              system.dimension :=
          (Nat.div_lt_iff_lt_mul positive).2 offset
        let row : Fin system.dimension :=
          ⟨(rank - (2 + system.dimension)) / system.dimension,
            rowBound⟩
        let column : Fin system.dimension :=
          ⟨(rank - (2 + system.dimension)) % system.dimension,
            Nat.mod_lt _ positive⟩
        have decompose :
            row.val * system.dimension + column.val =
              rank - (2 + system.dimension) := by
          dsimp [row, column]
          rw [Nat.mul_comm]
          exact Nat.div_add_mod _ _
        have exactRank :
            rank = 2 + system.dimension +
              row.val * system.dimension + column.val := by omega
        have atom := paperVariableArityGaussianRankBasisAtom_query
          shape formula rank row column rfl rfl actualReduced
        have exactRecord :
            (sourceLatticeStructuralRecords lattice).getD rank [] =
              encodeAtomic
                (system.effectiveSquareBasisMatrix row column) := by
          rw [exactRank]
          change
            (sourceLatticeStructuralRecords lattice).getD
                (2 + lattice.dimension +
                  row.val * lattice.dimension + column.val) [] =
              encodeAtomic (lattice.basis row column)
          exact sourceLatticeStructuralRecords_getD_basis
            lattice row column
        rw [exactRecord]
        exact atom

theorem paperVariableArityGaussianStructuralSourceWord_eq_encodeGapCVPInstance
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {radius reduced : List Bool → List Bool}
    (radiusComputer : BitTM radius)
    (reducedComputer : BitTM reduced)
    (formula : ThreeCNF)
    (radiusValue : ℚ)
    (radiusPositive : 0 < radiusValue)
    (actualRadius :
      radius (encodeThreeCNF formula) = encodeAtomic radiusValue)
    (actualReduced :
      reduced (encodeThreeCNF formula) =
        effectiveGaussianPackedStateWord
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).effectiveGaussianState
          (encodeThreeCNF formula)) :
    paperGaussianStructuralSourceWord
        shape radiusComputer reducedComputer
        (encodeThreeCNF formula) =
      encodeGapCVPInstance
        (effectiveGapCVPInstance
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula)
          (physicalFormulaSystem_dimension_pos
            (encodeThreeCNF formula).length formula)
          radiusValue radiusPositive) := by
  let lattice := effectiveGapCVPInstance
    (physicalFormulaSystem
      (encodeThreeCNF formula).length formula)
    (physicalFormulaSystem_dimension_pos
      (encodeThreeCNF formula).length formula)
    radiusValue radiusPositive
  unfold paperGaussianStructuralSourceWord
  apply constructiveStructuralSourceWord_eq_encodeGapCVPInstance
    (paperGaussianSourceDimensionWidth shape)
    (paperVariableArityGaussianStructuralAtomComputer
      shape radiusComputer reducedComputer)
    (encodeThreeCNF formula) lattice
  · exact paperVariableArityGaussianSourceDimensionWidth_valid
      shape formula
  · intro rank bound
    rw [paperVariableArityGaussianStructuralAtomComputer_output]
    exact paperVariableArityGaussianStructuralAtomOutput_correct
      shape formula radiusValue radiusPositive
      actualRadius actualReduced rank bound

end GaussianOutputSerializerTM

namespace PhysicalFamilyRowTM

open scoped BigOperators

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceMachineCert GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.CNFBoundedRecordFoldTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CLStructuralNaturalBinaryWriter GapCVP.CLVerifier GapCVP.BinaryDimensionTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.BinarySourceVariableCompaction
open GapCVP.BinaryCompactSourceFirstOccurrenceTM GapCVP.SourcePreprocessingSemantics
open GapCVP.SourcePreprocessingTM GapCVP.FormulaBridge GapCVP.ClauseOffsetTM

/-- GapCVP reduction support. -/
abbrev physicalFormulaSize (formula : ThreeCNF) : ℕ :=
  sourceSizeParameter (encodeThreeCNF formula).length
    (srcFormula formula)

/-- GapCVP reduction support. -/
abbrev physDegree (formula : ThreeCNF) : ℕ :=
  sourceFieldExponent (physicalFormulaSize formula)

/-- GapCVP reduction support. -/
abbrev physFieldCard
    (formula : ThreeCNF) : ℕ :=
  2 ^ physDegree formula

/-- GapCVP reduction support. -/
abbrev physicalFormulaVariableCount
    (formula : ThreeCNF) : ℕ :=
  paperVariableArityVariableCount formula

/-- GapCVP reduction support. -/
abbrev physGridCard
    (formula : ThreeCNF) : ℕ :=
  physFieldCard formula -
    physicalFormulaVariableCount formula

/-- GapCVP reduction support. -/
abbrev physicalFormulaMomentCount
    (formula : ThreeCNF) : ℕ :=
  physicalFormulaSize formula ^ 30 + 1

/-- GapCVP reduction support. -/
abbrev physicalFormulaTupleCount
    (formula : ThreeCNF) : ℕ :=
  sourceClauseWeightSum
    (noTautClauses formula)

/-- GapCVP reduction support. -/
abbrev physicalFormulaGlobalBoundary
    (formula : ThreeCNF) : ℕ :=
  physGridCard formula *
    physDegree formula

/-- GapCVP reduction support. -/
abbrev physicalFormulaRefinementBoundary
    (formula : ThreeCNF) : ℕ :=
  physicalFormulaGlobalBoundary formula +
    (noTautClauses formula).length *
      physGridCard formula *
      physFieldCard formula *
      physDegree formula

/-- GapCVP reduction support. -/
abbrev physicalFormulaOrdinaryBoundary
    (formula : ThreeCNF) : ℕ :=
  physicalFormulaRefinementBoundary formula +
    (1 + physicalFormulaTupleCount formula) *
      physicalFormulaMomentCount formula *
      physGridCard formula *
      physDegree formula

private def physicalFamilyRetainedSource :
    List Bool → List Bool :=
  firstFieldContents ∘ paperSourcePreprocessingOutput

private noncomputable def paperVariableArityPhysicalFamilyRetainedSourceComputable :
    BitTM
      physicalFamilyRetainedSource :=
  GapCVP.TMComposition.computableInPolyTime
    paperSourcePreprocessingComputable firstFieldContentsComputable

@[simp] private theorem paperVariableArityPhysicalFamilyRetainedSource_valid
    (formula : ThreeCNF) :
    physicalFamilyRetainedSource
        (encodeThreeCNF formula) =
      encodeThreeCNF (noTautClauses formula) := by
  unfold physicalFamilyRetainedSource
  rw [Function.comp_apply, paperSourcePreprocessingOutput_valid]
  exact firstFieldContents_valid
    (encodeThreeCNF (noTautClauses formula))
    (lengthPrefixedWord (paperSourceNormalizedClauseStream formula) ++
      encodeThreeCNF formula)

private def physicalFamilyClauseCountUnary :
    List Bool → List Bool :=
  sourceClauseCountUnary ∘ physicalFamilyRetainedSource

private noncomputable def physicalFamilyClauseCountUnaryComputable :
    BitTM
      physicalFamilyClauseCountUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilyRetainedSourceComputable
    sourceClauseCountUnaryComputable

@[simp] private theorem paperVariableArityPhysicalFamilyClauseCountUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyClauseCountUnary
        (encodeThreeCNF formula) =
      List.replicate (noTautClauses formula).length true := by
  simp only [physicalFamilyClauseCountUnary, Function.comp_apply,
      paperVariableArityPhysicalFamilyRetainedSource_valid, sourceClauseCountUnary_valid]

private theorem paperVariableArityPhysicalFamilyRetainedVariableCount_eq
    (formula : ThreeCNF) :
    occurringVariableCount
        (noTautClauses formula) =
      paperVariableArityVariableCount formula := by
  classical
  let retained := noTautClauses formula
  have sameVariables :
      (occurringVariables retained).toFinset =
        (paperNormalizedOccurringVariables formula).toFinset := by
    ext name
    simp only [List.mem_toFinset]
    exact (mem_occurringVariables_iff retained name).trans
      ((mem_formulaVariables_iff_exists_literal retained name).trans
        (mem_paperSourceNormalizedOccurringVariables_iff
          formula name).symm)
  unfold occurringVariableCount paperVariableArityVariableCount
  change (occurringVariables retained).length =
    (paperNormalizedOccurringVariables formula).length
  calc
    (occurringVariables retained).length =
        (occurringVariables retained).toFinset.card :=
      (List.toFinset_card_of_nodup
        (occurringVariables_nodup retained)).symm
    _ = (paperNormalizedOccurringVariables formula).toFinset.card :=
      congrArg Finset.card sameVariables
    _ = (paperNormalizedOccurringVariables formula).length :=
      List.toFinset_card_of_nodup
        (paperSourceNormalizedOccurringVariables_nodup formula)

/-- GapCVP reduction support. -/
def physicalFamilyVariableCountUnary :
    List Bool → List Bool :=
  compactSourceOccurringVariableCountUnary ∘
    physicalFamilyRetainedSource

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyVariableCountUnaryComputable :
    BitTM
      physicalFamilyVariableCountUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilyRetainedSourceComputable
    compactSourceOccurringVariableCountUnaryComputable

@[simp] theorem paperVariableArityPhysicalFamilyVariableCountUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyVariableCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaVariableCount formula) true := by
  unfold physicalFamilyVariableCountUnary
  rw [Function.comp_apply,
    paperVariableArityPhysicalFamilyRetainedSource_valid,
    compactSourceOccurringVariableCountUnary_valid,
    paperVariableArityPhysicalFamilyRetainedVariableCount_eq]

private def physicalFamilySizeUnary
    (input : List Bool) : List Bool :=
  List.replicate 100 true ++
    (sourceInputLengthUnary input ++
    (physicalFamilyVariableCountUnary input ++
      physicalFamilyClauseCountUnary input))

private noncomputable def paperVariableArityPhysicalFamilySizeUnaryComputable :
    BitTM
      physicalFamilySizeUnary :=
  pointwiseAppendComputable
    (sourceFixedWordComputable (List.replicate 100 true))
    (pointwiseAppendComputable sourceInputLengthUnaryComputable
      (pointwiseAppendComputable
        paperVariableArityPhysicalFamilyVariableCountUnaryComputable
        physicalFamilyClauseCountUnaryComputable))

@[simp] private theorem paperVariableArityPhysicalFamilySizeUnary_valid
    (formula : ThreeCNF) :
    physicalFamilySizeUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaSize formula) true := by
  simp only [physicalFamilySizeUnary,
    sourceInputLengthUnary,
    paperVariableArityPhysicalFamilyVariableCountUnary_valid,
    paperVariableArityPhysicalFamilyClauseCountUnary_valid,
    ← List.replicate_add,
    GapCVP.Core.sourceSizeParameter,
    physicalFormulaVariableCount, srcFormula,
    paperSourceNormalizedClauses, List.length_map,
    List.length_attach]
  simp only [Nat.add_assoc]

private def physicalFamilyPowerTwoHundredUnary :
    List Bool → List Bool :=
  (fun input : List Bool =>
    List.replicate ((Polynomial.X ^ 200).eval input.length) true) ∘
      physicalFamilySizeUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyPowerTwoHundredUnaryComputable :
    BitTM
      physicalFamilyPowerTwoHundredUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilySizeUnaryComputable
    (polynomialValueUnaryComputable (Polynomial.X ^ 200))

@[simp] private theorem paperVariableArityPhysicalFamilyPowerTwoHundredUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyPowerTwoHundredUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaSize formula ^ 200) true := by
  unfold physicalFamilyPowerTwoHundredUnary
  rw [Function.comp_apply, paperVariableArityPhysicalFamilySizeUnary_valid,
    List.length_replicate, Polynomial.eval_pow, Polynomial.eval_X]

/-- GapCVP reduction support. -/
def physicalFamilyFieldCardinalityUnary :
    List Bool → List Bool :=
  nextPowerUnaryOutput physicalFamilyPowerTwoHundredUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable :
    BitTM
      physicalFamilyFieldCardinalityUnary :=
  nextPowerUnaryComputable
    paperVariableArityPhysicalFamilyPowerTwoHundredUnaryComputable

@[simp] theorem paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyFieldCardinalityUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physFieldCard formula) true := by
  unfold physicalFamilyFieldCardinalityUnary
  rw [show physFieldCard formula =
      2 ^ Nat.clog 2 (physicalFormulaSize formula ^ 200) by
    simp only [physFieldCard, physDegree, sourceFieldExponent_eq]]
  apply nextPowerUnaryOutput_valid
    physicalFamilyPowerTwoHundredUnary
    (encodeThreeCNF formula)
    (physicalFormulaSize formula ^ 200)
  · exact paperVariableArityPhysicalFamilyPowerTwoHundredUnary_valid formula
  · have size := GapCVP.Core.sourceSizeParameter_ge_one_hundred
      (encodeThreeCNF formula).length
      (srcFormula formula)
    positivity

private def paperVariableArityPhysicalFamilyFieldCardinalityBinary :
    List Bool → List Bool :=
  (fun input : List Bool => Computability.encodeNat input.length) ∘
    physicalFamilyFieldCardinalityUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyFieldCardinalityBinaryComputable :
    BitTM
      paperVariableArityPhysicalFamilyFieldCardinalityBinary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable
    structuralNaturalBinaryWriterComputable

private def paperVariableArityPhysicalFamilyFieldBitLengthUnary :
    List Bool → List Bool :=
  sourceInputLengthUnary ∘
    paperVariableArityPhysicalFamilyFieldCardinalityBinary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyFieldBitLengthUnaryComputable :
    BitTM
      paperVariableArityPhysicalFamilyFieldBitLengthUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilyFieldCardinalityBinaryComputable
    sourceInputLengthUnaryComputable

/-- GapCVP reduction support. -/
def physicalFamilyFieldDegreeUnary :
    List Bool → List Bool :=
  List.tail ∘ paperVariableArityPhysicalFamilyFieldBitLengthUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable :
    BitTM
      physicalFamilyFieldDegreeUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilyFieldBitLengthUnaryComputable
    dropHeadComputable

@[simp] theorem paperVariableArityPhysicalFamilyFieldDegreeUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyFieldDegreeUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physDegree formula) true := by
  unfold physicalFamilyFieldDegreeUnary
    paperVariableArityPhysicalFamilyFieldBitLengthUnary
    paperVariableArityPhysicalFamilyFieldCardinalityBinary
    sourceInputLengthUnary
  simp only [Function.comp_apply]
  rw [paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid]
  simp only [List.length_replicate, encodeNat_length_eq_size, Nat.size_pow, List.replicate_succ,
      List.tail_cons]

/-- GapCVP reduction support. -/
def physicalFamilyGridCardinalityUnary :
    List Bool → List Bool :=
  unarySubtractionOutput
    physicalFamilyFieldCardinalityUnary
    physicalFamilyVariableCountUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable :
    BitTM
      physicalFamilyGridCardinalityUnary :=
  unarySubtractionComputable
    paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable
    paperVariableArityPhysicalFamilyVariableCountUnaryComputable

@[simp] theorem paperVariableArityPhysicalFamilyGridCardinalityUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyGridCardinalityUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physGridCard formula) true := by
  unfold physicalFamilyGridCardinalityUnary
  exact unarySubtractionOutput_valid
    physicalFamilyFieldCardinalityUnary
    physicalFamilyVariableCountUnary
    (encodeThreeCNF formula)
    (physFieldCard formula)
    (physicalFormulaVariableCount formula)
    (paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid formula)
    (paperVariableArityPhysicalFamilyVariableCountUnary_valid formula)

private def paperVariableArityPhysicalFamilyMomentBudgetUnary :
    List Bool → List Bool :=
  (fun input : List Bool =>
    List.replicate ((Polynomial.X ^ 30).eval input.length) true) ∘
      physicalFamilySizeUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyMomentBudgetUnaryComputable :
    BitTM
      paperVariableArityPhysicalFamilyMomentBudgetUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilySizeUnaryComputable
    (polynomialValueUnaryComputable (Polynomial.X ^ 30))

/-- GapCVP reduction support. -/
def physicalFamilyMomentCountUnary
    (input : List Bool) : List Bool :=
  true :: paperVariableArityPhysicalFamilyMomentBudgetUnary input

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyMomentCountUnaryComputable :
    BitTM
      physicalFamilyMomentCountUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilyMomentBudgetUnaryComputable
    (prependBitComputable true)

@[simp] theorem paperVariableArityPhysicalFamilyMomentCountUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyMomentCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaMomentCount formula) true := by
  unfold physicalFamilyMomentCountUnary
    paperVariableArityPhysicalFamilyMomentBudgetUnary
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Function.comp_apply,
      paperVariableArityPhysicalFamilySizeUnary_valid, List.length_replicate, List.replicate_succ]

private def physicalFamilyTupleCountUnary :
    List Bool → List Bool :=
  paperSourcePreprocessingField 1 ∘
    paperClauseOffsetOutput

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyTupleCountUnaryComputable :
    BitTM
      physicalFamilyTupleCountUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityClauseOffsetOutputComputable
    (paperPreprocessingFieldComputable 1)

@[simp] private theorem paperVariableArityPhysicalFamilyTupleCountUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyTupleCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaTupleCount formula) true := by
  unfold physicalFamilyTupleCountUnary
  rw [Function.comp_apply, paperVariableArityClauseOffsetOutput_valid]
  simp only [paperSourcePreprocessingField, paperSourcePreprocessingSuffixAt, Function.iterate_one,
      Function.comp_apply, firstFieldSuffix_valid, firstFieldContents_valid]

private def physicalFamilyTypeCountUnary
    (input : List Bool) : List Bool :=
  true :: physicalFamilyTupleCountUnary input

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyTypeCountUnaryComputable :
    BitTM
      physicalFamilyTypeCountUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilyTupleCountUnaryComputable
    (prependBitComputable true)

@[simp] private theorem paperVariableArityPhysicalFamilyTypeCountUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyTypeCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (1 + physicalFormulaTupleCount formula) true := by
  unfold physicalFamilyTypeCountUnary
  rw [paperVariableArityPhysicalFamilyTupleCountUnary_valid]
  rw [Nat.add_comm]
  rfl

end PhysicalFamilyRowTM

namespace Factor400BinaryConstructivePaperVariableArityPhysicalRadiusMachine

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceMachineCert
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap GapCVP.BinaryRadiusTM

private def physicalOneHotClauseCountUnary
    (input : List Bool) : List Bool :=
  true :: physicalFamilyClauseCountUnary input

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalOneHotClauseCountUnaryComputable :
    BitTM
      physicalOneHotClauseCountUnary := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    physicalFamilyClauseCountUnaryComputable
    (prependBitComputable true)
  change BitTM
    (fun input => true :: physicalFamilyClauseCountUnary input)
  simpa only [Function.comp_def] using physical

@[simp] private theorem paperVariableArityPhysicalOneHotClauseCountUnary_valid
    (formula : ThreeCNF) :
    physicalOneHotClauseCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        ((noTautClauses formula).length + 1) true := by
  simp only [physicalOneHotClauseCountUnary,
      paperVariableArityPhysicalFamilyClauseCountUnary_valid,
      List.replicate_succ]

private theorem paperVariableArityPhysicalFamilyGridCardinalityUnary_eq_actualGrid
    (formula : ThreeCNF) :
    physicalFamilyGridCardinalityUnary
        (encodeThreeCNF formula) =
      List.replicate
        (sourceFormulaGrid (encodeThreeCNF formula).length
          (srcFormula formula)).card true := by
  rw [paperVariableArityPhysicalFamilyGridCardinalityUnary_valid]
  congr 1
  simpa only [physGridCard, physFieldCard, physDegree, physicalFormulaSize,
      physicalFormulaVariableCount,
      paperVariableAritySourceFormula_variableCount] using
      (sourceFormulaGrid_card_eq_fieldWordCount (encodeThreeCNF formula).length (srcFormula
          formula)).symm

/-- GapCVP reduction support. -/
def physicalOneHotWeightUnary : List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    physicalOneHotClauseCountUnary
    physicalFamilyGridCardinalityUnary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalOneHotWeightUnaryComputable :
    BitTM
      physicalOneHotWeightUnary :=
  fourFamilyComputedUnaryProductComputable
    paperVariableArityPhysicalOneHotClauseCountUnaryComputable
    paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable

@[simp] theorem paperVariableArityPhysicalOneHotWeightUnary_valid
    (formula : ThreeCNF) :
    physicalOneHotWeightUnary
        (encodeThreeCNF formula) =
      List.replicate
        (((noTautClauses formula).length + 1) *
          (sourceFormulaGrid (encodeThreeCNF formula).length
            (srcFormula formula)).card)
        true := by
  exact fourFamilyComputedUnaryProductOutput_valid
    physicalOneHotClauseCountUnary
    physicalFamilyGridCardinalityUnary
    (encodeThreeCNF formula)
    ((noTautClauses formula).length + 1)
    (sourceFormulaGrid (encodeThreeCNF formula).length
      (srcFormula formula)).card
    (paperVariableArityPhysicalOneHotClauseCountUnary_valid formula)
    (paperVariableArityPhysicalFamilyGridCardinalityUnary_eq_actualGrid
      formula)

private def paperVariableArityPhysicalRadiusAtomicOutput : List Bool → List Bool :=
  ceilSquareRootAtomicRationalOutput
    physicalOneHotWeightUnary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalRadiusAtomicComputable :
    BitTM
      paperVariableArityPhysicalRadiusAtomicOutput :=
  ceilSquareRootAtomicRationalComputable
    paperVariableArityPhysicalOneHotWeightUnaryComputable

@[simp] private theorem paperVariableArityPhysicalRadiusAtomicOutput_valid
    (formula : ThreeCNF) :
    paperVariableArityPhysicalRadiusAtomicOutput
        (encodeThreeCNF formula) =
      encodeAtomic
        (physicalFormulaRadius
          (encodeThreeCNF formula).length formula) := by
  unfold paperVariableArityPhysicalRadiusAtomicOutput
  rw [ceilSquareRootAtomicRationalOutput_valid
    physicalOneHotWeightUnary
    (encodeThreeCNF formula)
    (((noTautClauses formula).length + 1) *
      (sourceFormulaGrid (encodeThreeCNF formula).length
        (srcFormula formula)).card)
    (paperVariableArityPhysicalOneHotWeightUnary_valid formula)]
  unfold physicalFormulaRadius
    GapCVP.Core.sourceOneHotCompletenessRadius
  rw [paperVariableAritySourceFormula_clauses_length]

end Factor400BinaryConstructivePaperVariableArityPhysicalRadiusMachine

namespace PhysicalNormalizedBranchTM

open Turing GapCVP.BinaryEncoding GapCVP.OutputPolynomialCompositionClosure
open GapCVP.SourceOriginalSourcePreservingTM GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.PhysicalFamilyRowTM GapCVP.GaussianRowWorker
open GapCVP.Factor400BinaryPhysicalWorkers

/-- GapCVP reduction support. -/
def physicalNormalizedNonemptyMarker
    (input : List Bool) : Bool :=
  (physicalFamilyClauseCountUnary input).headD false

private def physicalNormalizedNonemptyDecisionWord :
    List Bool → List Bool :=
  binaryGaussianFirstCellWord ∘
    physicalFamilyClauseCountUnary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalNormalizedNonemptyDecisionComputable :
    BitTM
      physicalNormalizedNonemptyDecisionWord :=
  GapCVP.TMComposition.computableInPolyTime
    physicalFamilyClauseCountUnaryComputable
    binaryGaussianFirstCellComputable

private theorem paperVariableArityPhysicalNormalizedNonemptyDecisionWord_eq
    (input : List Bool) :
    physicalNormalizedNonemptyDecisionWord input =
      [physicalNormalizedNonemptyMarker input] := by
  unfold physicalNormalizedNonemptyDecisionWord
    physicalNormalizedNonemptyMarker
  cases hcount : physicalFamilyClauseCountUnary input with
  | nil =>
      simp only [binaryGaussianFirstCellWord, Function.comp_apply, markerConditionalOutput, hcount,
          List.headD_eq_head?_getD, List.head?_nil, Option.getD_none]
  | cons bit remaining =>
      simp only [Function.comp_apply, hcount, binaryGaussianFirstCellWord_valid,
          List.headD_eq_head?_getD,
          List.head?_cons, Option.getD_some]

@[simp] theorem paperVariableArityPhysicalNormalizedNonemptyMarker_valid
    (formula : ThreeCNF) :
    physicalNormalizedNonemptyMarker
        (encodeThreeCNF formula) =
      decide (paperSourceNormalizedClauses formula ≠ []) := by
  unfold physicalNormalizedNonemptyMarker
  rw [paperVariableArityPhysicalFamilyClauseCountUnary_valid]
  cases hretained : noTautClauses formula with
  | nil =>
      simp only [List.length_nil, List.replicate_zero, List.headD_eq_head?_getD, List.head?_nil,
          Option.getD_none,
          paperSourceNormalizedClauses, hretained, List.map_nil, ne_eq, not_true_eq_false,
              decide_false]
  | cons clause remaining =>
      simp only [List.length_cons, List.replicate_succ, List.headD_eq_head?_getD, List.head?_cons,
          Option.getD_some,
          paperSourceNormalizedClauses, hretained, List.map_cons, ne_eq, reduceCtorEq,
              not_false_eq_true, decide_true]

private def physicalNormalizedEmptyDecisionWord :
    List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    physicalNormalizedNonemptyDecisionWord

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalNormalizedEmptyDecisionComputable :
    BitTM
      physicalNormalizedEmptyDecisionWord :=
  fourFamilyBooleanNotOutputComputable
    paperVariableArityPhysicalNormalizedNonemptyDecisionComputable

private def physicalCanonicalDecisionWord :
    List Bool → List Bool :=
  binaryGaussianFirstCellWord ∘
    (fun input => constructiveCanonicalSourceMarker input :: input)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalDecisionComputable :
    BitTM
      physicalCanonicalDecisionWord :=
  GapCVP.TMComposition.computableInPolyTime
    constructiveCanonicalSourceMarkerComputable
    binaryGaussianFirstCellComputable

@[simp] private theorem paperVariableArityPhysicalCanonicalDecisionWord_eq
    (input : List Bool) :
    physicalCanonicalDecisionWord input =
      [constructiveCanonicalSourceMarker input] := by
  simp only [physicalCanonicalDecisionWord, Function.comp_apply, binaryGaussianFirstCellWord_valid]

/-- GapCVP reduction support. -/
def physicalCanonicalNormalizedNonemptyGuard
    (input : List Bool) : Bool :=
  constructiveCanonicalSourceMarker input &&
    physicalNormalizedNonemptyMarker input

private def physicalCanonicalNormalizedNonemptyDecisionWord :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    physicalCanonicalDecisionWord
    physicalNormalizedNonemptyDecisionWord

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedNonemptyDecisionComputable :
    BitTM
      physicalCanonicalNormalizedNonemptyDecisionWord :=
  fourFamilyBooleanAndComputable
    paperVariableArityPhysicalCanonicalDecisionComputable
    paperVariableArityPhysicalNormalizedNonemptyDecisionComputable

private theorem paperVariableArityPhysicalCanonicalNormalizedNonemptyDecisionWord_eq
    (input : List Bool) :
    physicalCanonicalNormalizedNonemptyDecisionWord input =
      [physicalCanonicalNormalizedNonemptyGuard input] := by
  unfold physicalCanonicalNormalizedNonemptyDecisionWord
    physicalCanonicalNormalizedNonemptyGuard
  exact fourFamilyBooleanAndOutput_bits
    physicalCanonicalDecisionWord
    physicalNormalizedNonemptyDecisionWord
    input (constructiveCanonicalSourceMarker input)
    (physicalNormalizedNonemptyMarker input)
    (paperVariableArityPhysicalCanonicalDecisionWord_eq input)
    (paperVariableArityPhysicalNormalizedNonemptyDecisionWord_eq input)

private def physicalCanonicalNormalizedNonemptySelectionOutput :
    List Bool → List Bool :=
  factor400KeepFirstDropSecondWord ∘
    originalSourcePreservingOutput
      physicalCanonicalNormalizedNonemptyDecisionWord

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedNonemptyPreservedComputable :
    BitTM
      (originalSourcePreservingOutput
        physicalCanonicalNormalizedNonemptyDecisionWord) :=
  originalSourcePreservingComputable
    paperVariableArityPhysicalCanonicalNormalizedNonemptyDecisionComputable

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedNonemptySelectionComputable :
    BitTM
      physicalCanonicalNormalizedNonemptySelectionOutput :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalCanonicalNormalizedNonemptyPreservedComputable
    factor400KeepFirstDropSecondComputable

private theorem paperVariableArityPhysicalCanonicalNormalizedNonemptySelectionOutput_eq
    (input : List Bool) :
    physicalCanonicalNormalizedNonemptySelectionOutput
        input =
      physicalCanonicalNormalizedNonemptyGuard input ::
        input := by
  unfold physicalCanonicalNormalizedNonemptySelectionOutput
    originalSourcePreservingOutput
  rw [Function.comp_apply,
    paperVariableArityPhysicalCanonicalNormalizedNonemptyDecisionWord_eq
      input]
  simp only [factor400KeepFirstDropSecondWord, List.cons_append, List.nil_append, List.tail_cons]

end PhysicalNormalizedBranchTM

namespace PhysicalNormalizedCanonicalGuardTM

open Turing GapCVP.SourceOriginalSourcePreservingTM GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.PhysicalNormalizedBranchTM
open GapCVP.Factor400BinaryPhysicalWorkers

/-- GapCVP reduction support. -/
def physicalNormalizedEmptyMarker
    (input : List Bool) : Bool :=
  !physicalNormalizedNonemptyMarker input

private theorem paperVariableArityPhysicalNormalizedEmptyDecisionWord_eq
    (input : List Bool) :
    physicalNormalizedEmptyDecisionWord input =
      [physicalNormalizedEmptyMarker input] := by
  unfold physicalNormalizedEmptyDecisionWord
    physicalNormalizedEmptyMarker
  exact fourFamilyBooleanNotOutput_bit
    physicalNormalizedNonemptyDecisionWord input
    (physicalNormalizedNonemptyMarker input)
    (paperVariableArityPhysicalNormalizedNonemptyDecisionWord_eq input)

/-- GapCVP reduction support. -/
def physicalCanonicalNormalizedEmptyGuard
    (input : List Bool) : Bool :=
  constructiveCanonicalSourceMarker input &&
    physicalNormalizedEmptyMarker input

private def physicalCanonicalNormalizedEmptyDecisionWord :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    physicalCanonicalDecisionWord
    physicalNormalizedEmptyDecisionWord

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedEmptyDecisionComputable :
    BitTM
      physicalCanonicalNormalizedEmptyDecisionWord :=
  fourFamilyBooleanAndComputable
    paperVariableArityPhysicalCanonicalDecisionComputable
    paperVariableArityPhysicalNormalizedEmptyDecisionComputable

private theorem paperVariableArityPhysicalCanonicalNormalizedEmptyDecisionWord_eq
    (input : List Bool) :
    physicalCanonicalNormalizedEmptyDecisionWord input =
      [physicalCanonicalNormalizedEmptyGuard input] := by
  unfold physicalCanonicalNormalizedEmptyDecisionWord
    physicalCanonicalNormalizedEmptyGuard
  exact fourFamilyBooleanAndOutput_bits
    physicalCanonicalDecisionWord
    physicalNormalizedEmptyDecisionWord input
    (constructiveCanonicalSourceMarker input)
    (physicalNormalizedEmptyMarker input)
    (paperVariableArityPhysicalCanonicalDecisionWord_eq input)
    (paperVariableArityPhysicalNormalizedEmptyDecisionWord_eq input)

private def physicalCanonicalNormalizedEmptySelectionOutput :
    List Bool → List Bool :=
  factor400KeepFirstDropSecondWord ∘
    originalSourcePreservingOutput
      physicalCanonicalNormalizedEmptyDecisionWord

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedEmptyPreservedComputable :
    BitTM
      (originalSourcePreservingOutput
        physicalCanonicalNormalizedEmptyDecisionWord) :=
  originalSourcePreservingComputable
    paperVariableArityPhysicalCanonicalNormalizedEmptyDecisionComputable

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedEmptySelectionComputable :
    BitTM
      physicalCanonicalNormalizedEmptySelectionOutput :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalCanonicalNormalizedEmptyPreservedComputable
    factor400KeepFirstDropSecondComputable

private theorem paperVariableArityPhysicalCanonicalNormalizedEmptySelectionOutput_eq
    (input : List Bool) :
    physicalCanonicalNormalizedEmptySelectionOutput input =
      physicalCanonicalNormalizedEmptyGuard input ::
        input := by
  unfold physicalCanonicalNormalizedEmptySelectionOutput
    originalSourcePreservingOutput
  rw [Function.comp_apply,
    paperVariableArityPhysicalCanonicalNormalizedEmptyDecisionWord_eq input]
  simp only [factor400KeepFirstDropSecondWord, List.cons_append, List.nil_append, List.tail_cons]

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedEmptyGuardComputable :
    BitTM
      (fun input =>
        physicalCanonicalNormalizedEmptyGuard input ::
          input) := by
  have equality :
      physicalCanonicalNormalizedEmptySelectionOutput =
        (fun input =>
          physicalCanonicalNormalizedEmptyGuard input ::
            input) :=
    funext paperVariableArityPhysicalCanonicalNormalizedEmptySelectionOutput_eq
  rw [← equality]
  exact paperVariableArityPhysicalCanonicalNormalizedEmptySelectionComputable

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedNonemptyGuardComputable :
    BitTM
      (fun input =>
        physicalCanonicalNormalizedNonemptyGuard input ::
          input) := by
  have equality :
      physicalCanonicalNormalizedNonemptySelectionOutput =
        (fun input =>
          physicalCanonicalNormalizedNonemptyGuard input ::
            input) :=
    funext paperVariableArityPhysicalCanonicalNormalizedNonemptySelectionOutput_eq
  rw [← equality]
  exact paperVariableArityPhysicalCanonicalNormalizedNonemptySelectionComputable

end PhysicalNormalizedCanonicalGuardTM

namespace GaussianExactSourceInitializer

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.OutputPolynomialCompositionClosure
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.CanonicalMatrixShape GapCVP.PhysicalColumnOrder
open GapCVP.GaussianSourceConsistencyBridge GapCVP.GaussianSourceInitializerInstantiation

/-- GapCVP reduction support. -/
def paperCanonicalSourceBinarySystem
    (input : List Bool) : Option BinaryAffineSystem :=
  match decodeThreeCNF input with
  | none => none
  | some formula =>
      if encodeThreeCNF formula = input then
        some (physicalWordBinarySystem input.length formula)
      else
        none

@[simp] private theorem paperVariableArityCanonicalSourceBinarySystem_encode
    (formula : ThreeCNF) :
    paperCanonicalSourceBinarySystem
        (encodeThreeCNF formula) =
      some (physicalWordBinarySystem
        (encodeThreeCNF formula).length formula) := by
  simp only [paperCanonicalSourceBinarySystem, decodeThreeCNF_encode, ↓reduceIte]

private def gaussianPaperVariableArityExactSourceReducedStateOutput
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (input : List Bool) : List Bool :=
  if constructiveCanonicalSourceMarker input then
    gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryOutput
      worker input
  else
    binaryGaussianMalformedReducedState

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPaperVariableArityExactSourceReducedStateComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (gaussianPaperVariableArityExactSourceReducedStateOutput worker) := by
  change BitTM
    (fun input =>
      if constructiveCanonicalSourceMarker input then
        gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryOutput
          worker input
      else
        binaryGaussianMalformedReducedState)
  exact sourcePreservingConditionalComputable
    constructiveCanonicalSourceMarkerComputable
    (gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryComputable
      worker)
    binaryGaussianMalformedReducedState

private theorem gaussianPaperVariableArityExactSourceReducedStateOutput_eq
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (input : List Bool) :
    gaussianPaperVariableArityExactSourceReducedStateOutput worker input =
      binaryGaussianExpectedReducedSourceState
        paperCanonicalSourceBinarySystem input := by
  cases hdecode : decodeThreeCNF input with
  | none =>
      simp only [gaussianPaperVariableArityExactSourceReducedStateOutput,
          constructiveCanonicalSourceMarker,
          hdecode, Bool.false_eq_true, ↓reduceIte, binaryGaussianExpectedReducedSourceState,
              paperCanonicalSourceBinarySystem]
  | some formula =>
      by_cases hcanonical : encodeThreeCNF formula = input
      · subst input
        simpa only [gaussianPaperVariableArityExactSourceReducedStateOutput,
            constructiveCanonicalSourceMarker,
            decodeThreeCNF_encode, decide_true, ↓reduceIte,
                binaryGaussianExpectedReducedSourceState,
            paperCanonicalSourceBinarySystem] using
            gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryOutput_valid worker
                formula
      · simp only [gaussianPaperVariableArityExactSourceReducedStateOutput,
          constructiveCanonicalSourceMarker,
            hdecode, hcanonical, decide_false, Bool.false_eq_true, ↓reduceIte,
                binaryGaussianExpectedReducedSourceState,
            paperCanonicalSourceBinarySystem]

@[irreducible] private noncomputable def gaussianPaperVariableArityExactSourceInitializer
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BinaryGaussianExactSourceInitializer
      paperCanonicalSourceBinarySystem where
  output := gaussianPaperVariableArityExactSourceReducedStateOutput worker
  computer := gaussianPaperVariableArityExactSourceReducedStateComputable worker
  output_eq := gaussianPaperVariableArityExactSourceReducedStateOutput_eq worker

private def gaussianPaperVariableArityAllInputExactConsistencyOutput
    (input : List Bool) : List Bool :=
  binaryGaussianSourceConsistencyGuard
      paperCanonicalSourceBinarySystem input :: input

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPaperVariableArityAllInputExactConsistencyComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      gaussianPaperVariableArityAllInputExactConsistencyOutput :=
  binaryGaussianExactSourceConsistencyComputable
    (gaussianPaperVariableArityExactSourceInitializer worker)

end GaussianExactSourceInitializer

namespace ExactPhysicalSourceTM

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianSourceConsistencyBridge
open GapCVP.SourcePreprocessingSemantics GapCVP.CanonicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.PhysicalNormalizedBranchTM GapCVP.PhysicalNormalizedCanonicalGuardTM
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalRadiusMachine
open GapCVP.GaussianExactSourceInitializer GapCVP.GaussianSourceInitializerInstantiation
open GapCVP.GaussianOutputSerializerTM

private noncomputable def paperExactPhysicalStructuralOutput
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    List Bool → List Bool :=
  paperGaussianStructuralSourceWord shape
    paperVariableArityPhysicalRadiusAtomicComputable
    (gaussianPaperVariableArityCanonicalSourceReducedStateComputable cell)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityExactPhysicalStructuralOutputComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (paperExactPhysicalStructuralOutput cell) :=
  paperVariableArityGaussianStructuralSourceWordComputable shape
    paperVariableArityPhysicalRadiusAtomicComputable
    (gaussianPaperVariableArityCanonicalSourceReducedStateComputable cell)

private theorem paperVariableArityExactPhysicalStructuralOutput_valid
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF) :
    paperExactPhysicalStructuralOutput cell
        (encodeThreeCNF formula) =
      encodeGapCVPInstance
        (physicalFormulaInstance
          (encodeThreeCNF formula).length formula) := by
  unfold paperExactPhysicalStructuralOutput
  exact paperVariableArityGaussianStructuralSourceWord_eq_encodeGapCVPInstance
    shape
    paperVariableArityPhysicalRadiusAtomicComputable
    (gaussianPaperVariableArityCanonicalSourceReducedStateComputable cell)
    formula
    (physicalFormulaRadius
      (encodeThreeCNF formula).length formula)
    (physicalFormulaRadius_pos
      (encodeThreeCNF formula).length formula)
    (paperVariableArityPhysicalRadiusAtomicOutput_valid formula)
    (gaussianPaperVariableArityCanonicalSourceReducedStateOutput_effective
      cell formula)

private def paperExactPhysicalRoutedOutput
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (input : List Bool) : List Bool :=
  if physicalCanonicalNormalizedEmptyGuard input then
    SourceMachineRouting.canonicalYesWord
  else if physicalCanonicalNormalizedNonemptyGuard input then
    if binaryGaussianSourceConsistencyGuard
        paperCanonicalSourceBinarySystem input then
      paperExactPhysicalStructuralOutput cell input
    else
      Factor400BinaryCanonicalNo.adaptedCanonicalNoWord
  else
    Factor400BinaryCanonicalNo.adaptedCanonicalNoWord

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityExactPhysicalRoutedOutputComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (paperExactPhysicalRoutedOutput cell) := by
  have consistency := sourcePreservingConditionalComputable
    (gaussianPaperVariableArityAllInputExactConsistencyComputable cell)
    (paperVariableArityExactPhysicalStructuralOutputComputable cell)
    Factor400BinaryCanonicalNo.adaptedCanonicalNoWord
  have nonempty := sourcePreservingConditionalComputable
    paperVariableArityPhysicalCanonicalNormalizedNonemptyGuardComputable
    consistency Factor400BinaryCanonicalNo.adaptedCanonicalNoWord
  have routed := binaryGaussianDynamicBranchComputable
    paperVariableArityPhysicalCanonicalNormalizedEmptyGuardComputable
    (sourceFixedWordComputable SourceMachineRouting.canonicalYesWord)
    nonempty
  exact routed

@[simp] theorem paperVariableArityExactPhysicalConsistencyGuard_encode
    (formula : ThreeCNF) :
    binaryGaussianSourceConsistencyGuard
        paperCanonicalSourceBinarySystem
        (encodeThreeCNF formula) =
      (physicalFormulaSystem
        (encodeThreeCNF formula).length formula).effectiveReducedConsistent := by
  unfold binaryGaussianSourceConsistencyGuard
  rw [paperVariableArityCanonicalSourceBinarySystem_encode]
  rfl

/-- Identifies the shared physical routing tree from its five semantic branches. -/
theorem physicalRoutedOutput_eq_sourceMap
    (structuralOutput sourceMap : List Bool → List Bool) (noWord : List Bool)
    (decodeNone : ∀ input, decodeThreeCNF input = none → noWord = sourceMap input)
    (noncanonical : ∀ input formula, decodeThreeCNF input = some formula →
      encodeThreeCNF formula ≠ input → noWord = sourceMap input)
    (normalizedEmpty : ∀ formula, paperSourceNormalizedClauses formula = [] →
      SourceMachineRouting.canonicalYesWord = sourceMap (encodeThreeCNF formula))
    (inconsistent : ∀ formula, paperSourceNormalizedClauses formula ≠ [] →
      (physicalFormulaSystem (encodeThreeCNF formula).length
        formula).effectiveReducedConsistent = false →
      noWord = sourceMap (encodeThreeCNF formula))
    (consistent : ∀ formula, paperSourceNormalizedClauses formula ≠ [] →
      (physicalFormulaSystem (encodeThreeCNF formula).length
        formula).effectiveReducedConsistent = true →
      structuralOutput (encodeThreeCNF formula) = sourceMap (encodeThreeCNF formula))
    (input : List Bool) :
    (if physicalCanonicalNormalizedEmptyGuard input then
      SourceMachineRouting.canonicalYesWord
    else if physicalCanonicalNormalizedNonemptyGuard input then
      if binaryGaussianSourceConsistencyGuard paperCanonicalSourceBinarySystem input then
        structuralOutput input
      else noWord
    else noWord) = sourceMap input := by
  cases decoded : decodeThreeCNF input with
  | none =>
      have canonical : constructiveCanonicalSourceMarker input = false := by
        simp only [constructiveCanonicalSourceMarker, decoded]
      have empty : physicalCanonicalNormalizedEmptyGuard input = false := by
        simp only [physicalCanonicalNormalizedEmptyGuard, canonical, Bool.false_and]
      have nonempty : physicalCanonicalNormalizedNonemptyGuard input = false := by
        simp only [physicalCanonicalNormalizedNonemptyGuard, canonical, Bool.false_and]
      simpa only [empty, Bool.false_eq_true, ↓reduceIte, nonempty] using
        decodeNone input decoded
  | some formula =>
      by_cases canonical : encodeThreeCNF formula = input
      · subst input
        by_cases empty : paperSourceNormalizedClauses formula = []
        · have emptyGuard :
              physicalCanonicalNormalizedEmptyGuard (encodeThreeCNF formula) = true := by
            simp only [physicalCanonicalNormalizedEmptyGuard, constructiveCanonicalSourceMarker,
              decodeThreeCNF_encode, decide_true, physicalNormalizedEmptyMarker,
              paperVariableArityPhysicalNormalizedNonemptyMarker_valid, empty, ne_eq,
              not_true_eq_false, decide_false, Bool.not_false, Bool.and_self]
          simpa only [emptyGuard, ↓reduceIte] using normalizedEmpty formula empty
        · have emptyGuard :
              physicalCanonicalNormalizedEmptyGuard (encodeThreeCNF formula) = false := by
            simp only [physicalCanonicalNormalizedEmptyGuard, constructiveCanonicalSourceMarker,
              decodeThreeCNF_encode, decide_true, physicalNormalizedEmptyMarker,
              paperVariableArityPhysicalNormalizedNonemptyMarker_valid, ne_eq, empty,
              not_false_eq_true, Bool.not_true, Bool.and_false]
          have nonemptyGuard :
              physicalCanonicalNormalizedNonemptyGuard (encodeThreeCNF formula) = true := by
            simp only [physicalCanonicalNormalizedNonemptyGuard, constructiveCanonicalSourceMarker,
              decodeThreeCNF_encode, decide_true,
              paperVariableArityPhysicalNormalizedNonemptyMarker_valid, ne_eq, empty,
              not_false_eq_true, Bool.and_self]
          cases consistency : (physicalFormulaSystem
              (encodeThreeCNF formula).length formula).effectiveReducedConsistent with
          | false =>
              simpa only [emptyGuard, Bool.false_eq_true, ↓reduceIte, nonemptyGuard,
                paperVariableArityExactPhysicalConsistencyGuard_encode, consistency] using
                inconsistent formula empty consistency
          | true =>
              simpa only [emptyGuard, Bool.false_eq_true, ↓reduceIte, nonemptyGuard,
                paperVariableArityExactPhysicalConsistencyGuard_encode, consistency] using
                consistent formula empty consistency
      · have sourceGuard : constructiveCanonicalSourceMarker input = false := by
          simp only [constructiveCanonicalSourceMarker, decoded, canonical, decide_false]
        have emptyGuard : physicalCanonicalNormalizedEmptyGuard input = false := by
          simp only [physicalCanonicalNormalizedEmptyGuard, sourceGuard, Bool.false_and]
        have nonemptyGuard : physicalCanonicalNormalizedNonemptyGuard input = false := by
          simp only [physicalCanonicalNormalizedNonemptyGuard, sourceGuard, Bool.false_and]
        simpa only [emptyGuard, Bool.false_eq_true, ↓reduceIte, nonemptyGuard] using
          noncanonical input formula decoded canonical

private theorem paperVariableArityExactPhysicalRoutedOutput_eq_sourceMap
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (input : List Bool) :
    paperExactPhysicalRoutedOutput cell input =
      paperVariableArityPhysicalSourceMap input := by
  unfold paperExactPhysicalRoutedOutput
  apply physicalRoutedOutput_eq_sourceMap
    (paperExactPhysicalStructuralOutput cell)
    paperVariableArityPhysicalSourceMap
    Factor400BinaryCanonicalNo.adaptedCanonicalNoWord
  · intro source decode
    unfold paperVariableArityPhysicalSourceMap
    rw [paperVariableArityPhysicalSourceInstance_of_decode_none source decode]
    rfl
  · intro source formula decode noncanonical
    unfold paperVariableArityPhysicalSourceMap
    rw [paperVariableArityPhysicalSourceInstance_of_noncanonical
      source formula decode noncanonical]
    rfl
  · intro formula empty
    unfold paperVariableArityPhysicalSourceMap
    rw [paperVariableArityPhysicalSourceInstance_of_normalized_empty
      (encodeThreeCNF formula) formula (by simp only [decodeThreeCNF_encode]) rfl empty]
    rfl
  · intro formula nonempty inconsistent
    unfold paperVariableArityPhysicalSourceMap
    rw [paperVariableArityPhysicalSourceInstance_of_inconsistent
      (encodeThreeCNF formula) formula (by simp only [decodeThreeCNF_encode])
      rfl nonempty inconsistent]
    rfl
  · intro formula nonempty consistent
    unfold paperVariableArityPhysicalSourceMap
    rw [paperVariableArityPhysicalSourceInstance_of_consistent
      (encodeThreeCNF formula) formula (by simp only [decodeThreeCNF_encode])
      rfl nonempty consistent]
    exact paperVariableArityExactPhysicalStructuralOutput_valid cell formula

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalSourceMapMachineOfCell
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      paperVariableArityPhysicalSourceMap := by
  have machine := paperVariableArityExactPhysicalRoutedOutputComputable cell
  have equality :
      paperExactPhysicalRoutedOutput cell =
        paperVariableArityPhysicalSourceMap :=
    funext (paperVariableArityExactPhysicalRoutedOutput_eq_sourceMap cell)
  rwa [equality] at machine

end ExactPhysicalSourceTM

namespace PhysicalFamilyMarkerTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.PhysicalFamilyRowTM

private def physicalGlobalBoundaryUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    physicalFamilyGridCardinalityUnary
    physicalFamilyFieldDegreeUnary

private noncomputable def paperVariableArityPhysicalGlobalBoundaryUnaryComputable :
    BitTM
      physicalGlobalBoundaryUnary :=
  fourFamilyComputedUnaryProductComputable
    paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable

@[simp] private theorem paperVariableArityPhysicalGlobalBoundaryUnary_valid
    (formula : ThreeCNF) :
    physicalGlobalBoundaryUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaGlobalBoundary formula) true := by
  unfold physicalGlobalBoundaryUnary
  exact fourFamilyComputedUnaryProductOutput_valid
    physicalFamilyGridCardinalityUnary
    physicalFamilyFieldDegreeUnary
    (encodeThreeCNF formula)
    (physGridCard formula)
    (physDegree formula)
    (paperVariableArityPhysicalFamilyGridCardinalityUnary_valid formula)
    (paperVariableArityPhysicalFamilyFieldDegreeUnary_valid formula)

private def physicalRefinementWidthUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    (fourFamilyComputedUnaryProductOutput
      (fourFamilyComputedUnaryProductOutput
        physicalFamilyClauseCountUnary
        physicalFamilyGridCardinalityUnary)
      physicalFamilyFieldCardinalityUnary)
    physicalFamilyFieldDegreeUnary

private noncomputable def paperVariableArityPhysicalRefinementWidthUnaryComputable :
    BitTM
      physicalRefinementWidthUnary :=
  fourFamilyComputedUnaryProductComputable
    (fourFamilyComputedUnaryProductComputable
      (fourFamilyComputedUnaryProductComputable
        physicalFamilyClauseCountUnaryComputable
        paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable)
      paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable)
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable

@[simp] private theorem paperVariableArityPhysicalRefinementWidthUnary_valid
    (formula : ThreeCNF) :
    physicalRefinementWidthUnary
        (encodeThreeCNF formula) =
      List.replicate
        ((noTautClauses formula).length *
          physGridCard formula *
          physFieldCard formula *
          physDegree formula) true := by
  let input := encodeThreeCNF formula
  have clauseGrid := fourFamilyComputedUnaryProductOutput_valid
    physicalFamilyClauseCountUnary
    physicalFamilyGridCardinalityUnary input
    (noTautClauses formula).length
    (physGridCard formula)
    (paperVariableArityPhysicalFamilyClauseCountUnary_valid formula)
    (paperVariableArityPhysicalFamilyGridCardinalityUnary_valid formula)
  have field := fourFamilyComputedUnaryProductOutput_valid
    (fourFamilyComputedUnaryProductOutput
      physicalFamilyClauseCountUnary
      physicalFamilyGridCardinalityUnary)
    physicalFamilyFieldCardinalityUnary input
    ((noTautClauses formula).length *
      physGridCard formula)
    (physFieldCard formula)
    clauseGrid
    (paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid formula)
  exact fourFamilyComputedUnaryProductOutput_valid
    (fourFamilyComputedUnaryProductOutput
      (fourFamilyComputedUnaryProductOutput
        physicalFamilyClauseCountUnary
        physicalFamilyGridCardinalityUnary)
      physicalFamilyFieldCardinalityUnary)
    physicalFamilyFieldDegreeUnary input
    ((noTautClauses formula).length *
      physGridCard formula *
      physFieldCard formula)
    (physDegree formula)
    field
    (paperVariableArityPhysicalFamilyFieldDegreeUnary_valid formula)

private def physicalRefinementBoundaryUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    physicalGlobalBoundaryUnary
    physicalRefinementWidthUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementBoundaryUnaryComputable :
    BitTM
      physicalRefinementBoundaryUnary :=
  fourFamilyComputedUnarySumComputable
    paperVariableArityPhysicalGlobalBoundaryUnaryComputable
    paperVariableArityPhysicalRefinementWidthUnaryComputable

@[simp] private theorem paperVariableArityPhysicalRefinementBoundaryUnary_valid
    (formula : ThreeCNF) :
    physicalRefinementBoundaryUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaRefinementBoundary formula)
        true := by
  unfold physicalRefinementBoundaryUnary
  exact fourFamilyComputedUnarySumOutput_valid
    physicalGlobalBoundaryUnary
    physicalRefinementWidthUnary
    (encodeThreeCNF formula)
    (physicalFormulaGlobalBoundary formula)
    ((noTautClauses formula).length *
      physGridCard formula *
      physFieldCard formula *
      physDegree formula)
    (paperVariableArityPhysicalGlobalBoundaryUnary_valid formula)
    (paperVariableArityPhysicalRefinementWidthUnary_valid formula)

private def physicalOrdinaryWidthUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    (fourFamilyComputedUnaryProductOutput
      (fourFamilyComputedUnaryProductOutput
        physicalFamilyTypeCountUnary
        physicalFamilyMomentCountUnary)
      physicalFamilyGridCardinalityUnary)
    physicalFamilyFieldDegreeUnary

private noncomputable def paperVariableArityPhysicalOrdinaryWidthUnaryComputable :
    BitTM
      physicalOrdinaryWidthUnary :=
  fourFamilyComputedUnaryProductComputable
    (fourFamilyComputedUnaryProductComputable
      (fourFamilyComputedUnaryProductComputable
        paperVariableArityPhysicalFamilyTypeCountUnaryComputable
        paperVariableArityPhysicalFamilyMomentCountUnaryComputable)
      paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable)
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable

@[simp] private theorem paperVariableArityPhysicalOrdinaryWidthUnary_valid
    (formula : ThreeCNF) :
    physicalOrdinaryWidthUnary
        (encodeThreeCNF formula) =
      List.replicate
        ((1 + physicalFormulaTupleCount formula) *
          physicalFormulaMomentCount formula *
          physGridCard formula *
          physDegree formula) true := by
  let input := encodeThreeCNF formula
  have tagMoment := fourFamilyComputedUnaryProductOutput_valid
    physicalFamilyTypeCountUnary
    physicalFamilyMomentCountUnary input
    (1 + physicalFormulaTupleCount formula)
    (physicalFormulaMomentCount formula)
    (paperVariableArityPhysicalFamilyTypeCountUnary_valid formula)
    (paperVariableArityPhysicalFamilyMomentCountUnary_valid formula)
  have grid := fourFamilyComputedUnaryProductOutput_valid
    (fourFamilyComputedUnaryProductOutput
      physicalFamilyTypeCountUnary
      physicalFamilyMomentCountUnary)
    physicalFamilyGridCardinalityUnary input
    ((1 + physicalFormulaTupleCount formula) *
      physicalFormulaMomentCount formula)
    (physGridCard formula)
    tagMoment
    (paperVariableArityPhysicalFamilyGridCardinalityUnary_valid formula)
  exact fourFamilyComputedUnaryProductOutput_valid
    (fourFamilyComputedUnaryProductOutput
      (fourFamilyComputedUnaryProductOutput
        physicalFamilyTypeCountUnary
        physicalFamilyMomentCountUnary)
      physicalFamilyGridCardinalityUnary)
    physicalFamilyFieldDegreeUnary input
    ((1 + physicalFormulaTupleCount formula) *
      physicalFormulaMomentCount formula *
      physGridCard formula)
    (physDegree formula)
    grid
    (paperVariableArityPhysicalFamilyFieldDegreeUnary_valid formula)

private def physicalOrdinaryBoundaryUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    physicalRefinementBoundaryUnary
    physicalOrdinaryWidthUnary

private noncomputable def paperVariableArityPhysicalOrdinaryBoundaryUnaryComputable :
    BitTM
      physicalOrdinaryBoundaryUnary :=
  fourFamilyComputedUnarySumComputable
    paperVariableArityPhysicalRefinementBoundaryUnaryComputable
    paperVariableArityPhysicalOrdinaryWidthUnaryComputable

@[simp] private theorem paperVariableArityPhysicalOrdinaryBoundaryUnary_valid
    (formula : ThreeCNF) :
    physicalOrdinaryBoundaryUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaOrdinaryBoundary formula)
        true := by
  unfold physicalOrdinaryBoundaryUnary
  exact fourFamilyComputedUnarySumOutput_valid
    physicalRefinementBoundaryUnary
    physicalOrdinaryWidthUnary
    (encodeThreeCNF formula)
    (physicalFormulaRefinementBoundary formula)
    ((1 + physicalFormulaTupleCount formula) *
      physicalFormulaMomentCount formula *
      physGridCard formula *
      physDegree formula)
    (paperVariableArityPhysicalRefinementBoundaryUnary_valid formula)
    (paperVariableArityPhysicalOrdinaryWidthUnary_valid formula)

/-- GapCVP reduction support. -/
def physicalCellSourceLift
    (worker : List Bool → List Bool) : List Bool → List Bool :=
  worker ∘ sourceExplicitAffineCellOriginalSource

/-- GapCVP reduction support. -/
noncomputable def physicalCellSourceLiftComputable
    {worker : List Bool → List Bool}
    (computer : BitTM worker) :
    BitTM
      (physicalCellSourceLift worker) :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable computer

@[simp] theorem paperVariableArityPhysicalCellSourceLift_query
    (worker : List Bool → List Bool)
    (row column : ℕ) (formula : ThreeCNF) :
    physicalCellSourceLift worker
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      worker (encodeThreeCNF formula) := by
  simp only [physicalCellSourceLift, Function.comp_apply,
      sourceExplicitAffineCellOriginalSource_query]

/-- GapCVP reduction support. -/
def physicalCellGlobalBoundaryUnary :
    List Bool → List Bool :=
  physicalCellSourceLift
    physicalGlobalBoundaryUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalCellGlobalBoundaryUnaryComputable :
    BitTM
      physicalCellGlobalBoundaryUnary :=
  physicalCellSourceLiftComputable
    paperVariableArityPhysicalGlobalBoundaryUnaryComputable

@[simp] theorem paperVariableArityPhysicalCellGlobalBoundaryUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalCellGlobalBoundaryUnary
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalFormulaGlobalBoundary formula) true := by
  unfold physicalCellGlobalBoundaryUnary
  rw [paperVariableArityPhysicalCellSourceLift_query,
    paperVariableArityPhysicalGlobalBoundaryUnary_valid]

/-- GapCVP reduction support. -/
def physicalCellRefinementBoundaryUnary :
    List Bool → List Bool :=
  physicalCellSourceLift
    physicalRefinementBoundaryUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalCellRefinementBoundaryUnaryComputable :
    BitTM
      physicalCellRefinementBoundaryUnary :=
  physicalCellSourceLiftComputable
    paperVariableArityPhysicalRefinementBoundaryUnaryComputable

@[simp] theorem paperVariableArityPhysicalCellRefinementBoundaryUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalCellRefinementBoundaryUnary
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalFormulaRefinementBoundary formula)
        true := by
  unfold physicalCellRefinementBoundaryUnary
  rw [paperVariableArityPhysicalCellSourceLift_query,
    paperVariableArityPhysicalRefinementBoundaryUnary_valid]

/-- GapCVP reduction support. -/
def physicalCellOrdinaryBoundaryUnary :
    List Bool → List Bool :=
  physicalCellSourceLift
    physicalOrdinaryBoundaryUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalCellOrdinaryBoundaryUnaryComputable :
    BitTM
      physicalCellOrdinaryBoundaryUnary :=
  physicalCellSourceLiftComputable
    paperVariableArityPhysicalOrdinaryBoundaryUnaryComputable

@[simp] theorem paperVariableArityPhysicalCellOrdinaryBoundaryUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalCellOrdinaryBoundaryUnary
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalFormulaOrdinaryBoundary formula)
        true := by
  unfold physicalCellOrdinaryBoundaryUnary
  rw [paperVariableArityPhysicalCellSourceLift_query,
    paperVariableArityPhysicalOrdinaryBoundaryUnary_valid]

private def physicalRowBeforeGlobal : List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    sourceExplicitAffineCellRow
    physicalCellGlobalBoundaryUnary

private noncomputable def paperVariableArityPhysicalRowBeforeGlobalComputable :
    BitTM
      physicalRowBeforeGlobal :=
  fourFamilyComputedUnaryLessBitComputable
    sourceExplicitAffineCellRowComputable
    paperVariableArityPhysicalCellGlobalBoundaryUnaryComputable

@[simp] private theorem paperVariableArityPhysicalRowBeforeGlobal_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRowBeforeGlobal
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (row < physicalFormulaGlobalBoundary formula)] := by
  unfold physicalRowBeforeGlobal
  exact fourFamilyComputedUnaryLessBitOutput_valid
    sourceExplicitAffineCellRow
    physicalCellGlobalBoundaryUnary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    row (physicalFormulaGlobalBoundary formula)
    (sourceExplicitAffineCellRow_query row column
      (encodeThreeCNF formula))
    (paperVariableArityPhysicalCellGlobalBoundaryUnary_query
      row column formula)

private def physicalRowBeforeRefinement :
    List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    sourceExplicitAffineCellRow
    physicalCellRefinementBoundaryUnary

private noncomputable def paperVariableArityPhysicalRowBeforeRefinementComputable :
    BitTM
      physicalRowBeforeRefinement :=
  fourFamilyComputedUnaryLessBitComputable
    sourceExplicitAffineCellRowComputable
    paperVariableArityPhysicalCellRefinementBoundaryUnaryComputable

@[simp] private theorem paperVariableArityPhysicalRowBeforeRefinement_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRowBeforeRefinement
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (row < physicalFormulaRefinementBoundary formula)] := by
  unfold physicalRowBeforeRefinement
  exact fourFamilyComputedUnaryLessBitOutput_valid
    sourceExplicitAffineCellRow
    physicalCellRefinementBoundaryUnary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    row (physicalFormulaRefinementBoundary formula)
    (sourceExplicitAffineCellRow_query row column
      (encodeThreeCNF formula))
    (paperVariableArityPhysicalCellRefinementBoundaryUnary_query
      row column formula)

private def physicalRowBeforeOrdinary :
    List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    sourceExplicitAffineCellRow
    physicalCellOrdinaryBoundaryUnary

private noncomputable def paperVariableArityPhysicalRowBeforeOrdinaryComputable :
    BitTM
      physicalRowBeforeOrdinary :=
  fourFamilyComputedUnaryLessBitComputable
    sourceExplicitAffineCellRowComputable
    paperVariableArityPhysicalCellOrdinaryBoundaryUnaryComputable

@[simp] private theorem paperVariableArityPhysicalRowBeforeOrdinary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRowBeforeOrdinary
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (row < physicalFormulaOrdinaryBoundary formula)] := by
  unfold physicalRowBeforeOrdinary
  exact fourFamilyComputedUnaryLessBitOutput_valid
    sourceExplicitAffineCellRow
    physicalCellOrdinaryBoundaryUnary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    row (physicalFormulaOrdinaryBoundary formula)
    (sourceExplicitAffineCellRow_query row column
      (encodeThreeCNF formula))
    (paperVariableArityPhysicalCellOrdinaryBoundaryUnary_query
      row column formula)

/-- GapCVP reduction support. -/
abbrev physicalGlobalRowMarker : List Bool → List Bool :=
  physicalRowBeforeGlobal

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalGlobalRowMarkerComputable :
    BitTM
      physicalGlobalRowMarker :=
  paperVariableArityPhysicalRowBeforeGlobalComputable

theorem paperVariableArityPhysicalGlobalRowMarker_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalGlobalRowMarker
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (row < physicalFormulaGlobalBoundary formula)] :=
  paperVariableArityPhysicalRowBeforeGlobal_query row column formula

/-- GapCVP reduction support. -/
def physicalRefinementRowMarker : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    (sourceFourFamilyBooleanNotOutput
      physicalRowBeforeGlobal)
    physicalRowBeforeRefinement

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalRefinementRowMarkerComputable :
    BitTM
      physicalRefinementRowMarker :=
  fourFamilyBooleanAndComputable
    (fourFamilyBooleanNotOutputComputable
      paperVariableArityPhysicalRowBeforeGlobalComputable)
    paperVariableArityPhysicalRowBeforeRefinementComputable

@[simp] theorem paperVariableArityPhysicalRefinementRowMarker_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRefinementRowMarker
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (physicalFormulaGlobalBoundary formula ≤ row ∧
          row < physicalFormulaRefinementBoundary formula)] := by
  let query := affineCellQuery row column
    (encodeThreeCNF formula)
  have notGlobal := fourFamilyBooleanNotOutput_bit
    physicalRowBeforeGlobal query
    (decide (row < physicalFormulaGlobalBoundary formula))
    (paperVariableArityPhysicalRowBeforeGlobal_query row column formula)
  have both := fourFamilyBooleanAndOutput_bits
    (sourceFourFamilyBooleanNotOutput
      physicalRowBeforeGlobal)
    physicalRowBeforeRefinement query
    (!(decide
      (row < physicalFormulaGlobalBoundary formula)))
    (decide
      (row < physicalFormulaRefinementBoundary formula))
    notGlobal
    (paperVariableArityPhysicalRowBeforeRefinement_query
      row column formula)
  change sourceFourFamilyBooleanAndOutput
    (sourceFourFamilyBooleanNotOutput
      physicalRowBeforeGlobal)
    physicalRowBeforeRefinement query = _
  simpa only [← decide_not, Nat.not_lt, ← Bool.decide_and] using both

/-- GapCVP reduction support. -/
def physicalOrdinaryRowMarker : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    (sourceFourFamilyBooleanNotOutput
      physicalRowBeforeRefinement)
    physicalRowBeforeOrdinary

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalOrdinaryRowMarkerComputable :
    BitTM
      physicalOrdinaryRowMarker :=
  fourFamilyBooleanAndComputable
    (fourFamilyBooleanNotOutputComputable
      paperVariableArityPhysicalRowBeforeRefinementComputable)
    paperVariableArityPhysicalRowBeforeOrdinaryComputable

@[simp] theorem paperVariableArityPhysicalOrdinaryRowMarker_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalOrdinaryRowMarker
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (physicalFormulaRefinementBoundary formula ≤ row ∧
          row < physicalFormulaOrdinaryBoundary formula)] := by
  let query := affineCellQuery row column
    (encodeThreeCNF formula)
  have notRefinement := fourFamilyBooleanNotOutput_bit
    physicalRowBeforeRefinement query
    (decide
      (row < physicalFormulaRefinementBoundary formula))
    (paperVariableArityPhysicalRowBeforeRefinement_query
      row column formula)
  have both := fourFamilyBooleanAndOutput_bits
    (sourceFourFamilyBooleanNotOutput
      physicalRowBeforeRefinement)
    physicalRowBeforeOrdinary query
    (!(decide
      (row < physicalFormulaRefinementBoundary formula)))
    (decide
      (row < physicalFormulaOrdinaryBoundary formula))
    notRefinement
    (paperVariableArityPhysicalRowBeforeOrdinary_query
      row column formula)
  change sourceFourFamilyBooleanAndOutput
    (sourceFourFamilyBooleanNotOutput
      physicalRowBeforeRefinement)
    physicalRowBeforeOrdinary query = _
  simpa only [← decide_not, Nat.not_lt, ← Bool.decide_and] using both

/-- GapCVP reduction support. -/
def physicalShiftedRowMarker : List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    physicalRowBeforeOrdinary

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalShiftedRowMarkerComputable :
    BitTM
      physicalShiftedRowMarker :=
  fourFamilyBooleanNotOutputComputable
    paperVariableArityPhysicalRowBeforeOrdinaryComputable

@[simp] theorem paperVariableArityPhysicalShiftedRowMarker_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalShiftedRowMarker
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (physicalFormulaOrdinaryBoundary formula ≤ row)] := by
  unfold physicalShiftedRowMarker
  have negation := fourFamilyBooleanNotOutput_bit
    physicalRowBeforeOrdinary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    (decide
      (row < physicalFormulaOrdinaryBoundary formula))
    (paperVariableArityPhysicalRowBeforeOrdinary_query
      row column formula)
  simpa only [← decide_not, Nat.not_lt] using negation

end PhysicalFamilyMarkerTM

namespace ShiftedTupleTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert
open GapCVP.SourceIndexedClauseLookupTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.SourcePreprocessingTM GapCVP.ClauseOffsetTM

/-- GapCVP reduction support. -/
def paperShiftedSourceClauseWeight (clause : ThreeClause) : ℕ :=
  (paperSourceNormalizedClause clause).length *
    (2 ^ (paperSourceNormalizedClause clause).length - 1)

/-- GapCVP reduction support. -/
def paperShiftedSourceClauseWeightSum
    (clauses : List ThreeClause) : ℕ :=
  (clauses.map paperShiftedSourceClauseWeight).sum

/-- GapCVP reduction support. -/
def paperShiftedClauseWeightUnary : List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    paperVariableArityClauseArityUnary
    paperVariableArityClauseWeightUnary

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityShiftedClauseWeightUnaryComputable :
    BitTM
      paperShiftedClauseWeightUnary :=
  fourFamilyComputedUnaryProductComputable
    paperClauseArityUnaryComputable
    paperClauseWeightUnaryComputable

@[simp] theorem paperVariableArityShiftedClauseWeightUnary_valid
    (clause : ThreeClause) (suffix : List Bool) :
    paperShiftedClauseWeightUnary
        (encodeThreeClause clause ++ suffix) =
      List.replicate
        (paperShiftedSourceClauseWeight clause) true := by
  unfold paperShiftedClauseWeightUnary
    paperShiftedSourceClauseWeight
  exact fourFamilyComputedUnaryProductOutput_valid
    paperVariableArityClauseArityUnary
    paperVariableArityClauseWeightUnary
    (encodeThreeClause clause ++ suffix)
    (paperSourceNormalizedClause clause).length
    (2 ^ (paperSourceNormalizedClause clause).length - 1)
    (paperVariableArityClauseArityUnary_valid clause suffix)
    (paperVariableArityClauseWeightUnary_valid clause suffix)

/-- GapCVP reduction support. -/
abbrev paperVariableArityShiftedRetainedSourceWord :
    List Bool → List Bool :=
  paperPreprocessingFilteredFormulaWord

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityShiftedRetainedSourceWordComputable :
    BitTM
      paperVariableArityShiftedRetainedSourceWord :=
  paperSourcePreprocessingFilteredFormulaWordComputable

/-- GapCVP reduction support. -/
noncomputable def paperShiftedRetainedClauseWidth :
    SourceQaryMaskDynamicGridWidth where
  output := paperRetainedClauseCountUnary
  computer := paperVariableArityRetainedClauseCountUnaryComputable

@[simp] theorem paperVariableArityShiftedRetainedClauseWidth_output
    (input : List Bool) :
    paperShiftedRetainedClauseWidth.output input =
      paperRetainedClauseCountUnary input := by
  rfl

/-- GapCVP reduction support. -/
def paperShiftedIndexedClauseQuery
    (input : List Bool) : List Bool :=
  firstFieldContents input ++
    false :: paperVariableArityShiftedRetainedSourceWord
      (firstFieldSuffix (firstFieldSuffix input))

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityShiftedIndexedClauseQueryComputable :
    BitTM
      paperShiftedIndexedClauseQuery := by
  have original := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable
  have retained := GapCVP.TMComposition.computableInPolyTime
    original paperVariableArityShiftedRetainedSourceWordComputable
  have delimited := GapCVP.TMComposition.computableInPolyTime
    retained (prependBitComputable false)
  exact pointwiseAppendComputable
    firstFieldContentsComputable delimited

@[simp] theorem paperVariableArityShiftedIndexedClauseQuery_valid
    (formula : ThreeCNF) (rank : ℕ) :
    paperShiftedIndexedClauseQuery
      (lengthPrefixedWord (List.replicate rank true) ++
        sourceQaryMaskDynamicGridBaseSource
          paperShiftedRetainedClauseWidth
          (encodeThreeCNF formula)) =
      sourceOriginalIndexedClauseQuery rank
        (noTautClauses formula) := by
  simp only [paperShiftedIndexedClauseQuery, sourceQaryMaskDynamicGridBaseSource,
      paperShiftedRetainedClauseWidth, paperVariableArityRetainedClauseCountUnary_valid,
          firstFieldContents_valid,
      firstFieldSuffix_valid, paperSourcePreprocessingFilteredFormulaWord_valid,
          sourceOriginalIndexedClauseQuery]

private def paperVariableArityShiftedIndexedClauseWeightUnary :
    List Bool → List Bool :=
  paperShiftedClauseWeightUnary ∘
    sourceOriginalIndexedClauseOutput ∘
    paperShiftedIndexedClauseQuery

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityShiftedIndexedClauseWeightUnaryComputable :
    BitTM
      paperVariableArityShiftedIndexedClauseWeightUnary := by
  have indexed := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityShiftedIndexedClauseQueryComputable
    sourceOriginalIndexedClauseComputable
  exact GapCVP.TMComposition.computableInPolyTime
    indexed paperVariableArityShiftedClauseWeightUnaryComputable

private theorem paperVariableArityShiftedIndexedClauseWeightUnary_valid
    (formula : ThreeCNF) (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length) :
    paperVariableArityShiftedIndexedClauseWeightUnary
      (lengthPrefixedWord (List.replicate rank true) ++
        sourceQaryMaskDynamicGridBaseSource
          paperShiftedRetainedClauseWidth
          (encodeThreeCNF formula)) =
      List.replicate
        (paperShiftedSourceClauseWeight
          ((noTautClauses formula).get
            ⟨rank, hbound⟩)) true := by
  unfold paperVariableArityShiftedIndexedClauseWeightUnary
  simp only [Function.comp_apply]
  rw [paperVariableArityShiftedIndexedClauseQuery_valid,
    sourceOriginalIndexedClauseOutput_valid rank
      (noTautClauses formula) hbound]
  simpa only [List.get_eq_getElem, List.append_nil] using
      paperVariableArityShiftedClauseWeightUnary_valid ((noTautClauses formula).get ⟨rank, hbound⟩)
          []

/-- GapCVP reduction support. -/
def paperShiftedIndexedSourceClauseWeight
    (clauses : List ThreeClause) (rank : ℕ) : ℕ :=
  match clauses[rank]? with
  | some clause => paperShiftedSourceClauseWeight clause
  | none => 0

theorem paperVariableArityShiftedSourceClauseWeight_flatMap
    (clauses : List ThreeClause) :
    (List.range clauses.length).flatMap
      (fun rank => List.replicate
        (paperShiftedIndexedSourceClauseWeight
          clauses rank) true) =
      List.replicate
        (paperShiftedSourceClauseWeightSum clauses) true := by
  induction clauses with
  | nil =>
      simp only [List.length_nil, List.range_zero, List.flatMap_nil,
          paperShiftedSourceClauseWeightSum,
          List.map_nil, List.sum_nil, List.replicate_zero]
  | cons clause remaining ih =>
      simp only [paperShiftedIndexedSourceClauseWeight, List.length_cons, List.range_succ_eq_map,
          List.flatMap_cons,
          lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, getElem?_pos, List.getElem_cons_zero,
              List.flatMap_map,
          Nat.succ_eq_add_one, List.getElem?_cons_succ, paperShiftedSourceClauseWeightSum,
              List.map_cons, List.sum_cons]
      change
        List.replicate
            (paperShiftedSourceClauseWeight clause) true ++
          (List.range remaining.length).flatMap
            (fun rank => List.replicate
              (paperShiftedIndexedSourceClauseWeight
                remaining rank) true) =
          List.replicate
            (paperShiftedSourceClauseWeight clause +
              paperShiftedSourceClauseWeightSum remaining)
            true
      rw [ih, List.replicate_append_replicate]

private def paperVariableArityShiftedTagCountUnary : List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    paperShiftedRetainedClauseWidth
    paperVariableArityShiftedIndexedClauseWeightUnaryComputable

private noncomputable def paperVariableArityShiftedTagCountUnaryComputable :
    BitTM
      paperVariableArityShiftedTagCountUnary :=
  maskDynamicGridRecordCatalogueComputable
    paperShiftedRetainedClauseWidth
    paperVariableArityShiftedIndexedClauseWeightUnaryComputable

private theorem paperVariableArityShiftedTagCountUnary_valid
    (formula : ThreeCNF) :
    paperVariableArityShiftedTagCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (paperShiftedSourceClauseWeightSum
          (noTautClauses formula)) true := by
  have hwidth :
      paperShiftedRetainedClauseWidth.output
          (encodeThreeCNF formula) =
        List.replicate
          (noTautClauses formula).length true := by
    rw [paperVariableArityShiftedRetainedClauseWidth_output]
    exact paperVariableArityRetainedClauseCountUnary_valid formula
  have catalogue := maskDynamicGridRecordCatalogueOutput_valid
    paperShiftedRetainedClauseWidth
    paperVariableArityShiftedIndexedClauseWeightUnaryComputable
    (encodeThreeCNF formula)
    (noTautClauses formula).length hwidth
  change maskDynamicGridRecordCatalogueOutput
    paperShiftedRetainedClauseWidth
    paperVariableArityShiftedIndexedClauseWeightUnaryComputable
    (encodeThreeCNF formula) = _
  rw [catalogue]
  rw [← paperVariableArityShiftedSourceClauseWeight_flatMap
    (noTautClauses formula)]
  apply List.flatMap_congr
  intro rank hrank
  have hbound : rank < (noTautClauses formula).length :=
    List.mem_range.mp hrank
  rw [paperVariableArityShiftedIndexedClauseWeightUnary_valid
    formula rank hbound]
  simp only [paperShiftedIndexedSourceClauseWeight,
    List.getElem?_eq_getElem hbound, List.get_eq_getElem]

end ShiftedTupleTM

namespace CanonicalOffsetIdentity

open scoped BigOperators

open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.FormulaBridge GapCVP.ClauseOffsetTM GapCVP.ShiftedTupleTM GapCVP.SourceOrder

theorem sourceListWeightSum
    {α : Type*} (clauses : List α) (weight : α → ℕ) :
    (clauses.map weight).sum =
      ∑ index : Fin clauses.length, weight (clauses.get index) := by
  calc
    (clauses.map weight).sum =
        (List.map weight (List.ofFn clauses.get)).sum := by
      rw [List.ofFn_get]
    _ = (List.ofFn
        (fun index : Fin clauses.length =>
          weight (clauses.get index))).sum := by
      rw [List.map_ofFn]
      rfl
    _ = ∑ index : Fin clauses.length, weight (clauses.get index) :=
      List.sum_ofFn

/-- GapCVP reduction support. -/
abbrev paperRetainedOriginalClauseIndexOrder
    (formula : ThreeCNF) :
    Fin (noTautClauses formula).length ≃
      Fin (srcFormula formula).clauses.length := by
  apply finCongr
  simp only [srcFormula, paperSourceNormalizedClauses, List.length_map, List.length_attach]

theorem paperFormulaClauseWidth_retainedOriginal
    (formula : ThreeCNF)
    (index : Fin (noTautClauses formula).length) :
    paperFormulaClauseWidth formula
        (paperRetainedOriginalClauseIndexOrder
          formula index) =
      (paperSourceNormalizedClause
        ((noTautClauses formula).get index)).length := by
  simp only [paperFormulaClauseWidth, paperSourceNormalizedClauses, paperFormulaRetainedClause,
      Fin.cast,
      srcFormula, paperRetainedOriginalClauseIndexOrder, finCongr, List.get_eq_getElem,
          List.getElem_attach,
      List.getElem_map]
  congr 3

theorem sourceClauseWeightSum_eq_localTagCount
    (formula : ThreeCNF) :
    sourceClauseWeightSum
        (noTautClauses formula) =
      paperVariableArityLocalTagCount formula := by
  let retained := noTautClauses formula
  let indexOrder :=
    paperRetainedOriginalClauseIndexOrder formula
  unfold sourceClauseWeightSum
    paperVariableArityLocalTagCount
  calc
    (retained.map sourceClauseWeight).sum =
        ∑ index : Fin retained.length,
          sourceClauseWeight
            (retained.get index) :=
      sourceListWeightSum
        retained sourceClauseWeight
    _ = ∑ index : Fin retained.length,
          (2 ^ paperFormulaClauseWidth
            formula (indexOrder index) - 1) := by
      apply Finset.sum_congr rfl
      intro index _
      simp only [sourceClauseWeight, List.get_eq_getElem]
      rw [paperFormulaClauseWidth_retainedOriginal]
      rfl
    _ = ∑ index : Fin
          (srcFormula formula).clauses.length,
          (2 ^ paperFormulaClauseWidth formula index - 1) :=
      indexOrder.sum_comp
        (fun index =>
          2 ^ paperFormulaClauseWidth formula index - 1)

private theorem paperVariableArityShiftedSourceClauseWeightSum_eq_localWeights
    (formula : ThreeCNF) :
    paperShiftedSourceClauseWeightSum
        (noTautClauses formula) =
      ∑ index : Fin
        (srcFormula formula).clauses.length,
        paperFormulaClauseWidth formula index *
          (2 ^ paperFormulaClauseWidth formula index - 1) := by
  let retained := noTautClauses formula
  let indexOrder :=
    paperRetainedOriginalClauseIndexOrder formula
  unfold paperShiftedSourceClauseWeightSum
  calc
    (retained.map paperShiftedSourceClauseWeight).sum =
        ∑ index : Fin retained.length,
          paperShiftedSourceClauseWeight
            (retained.get index) :=
      sourceListWeightSum
        retained paperShiftedSourceClauseWeight
    _ = ∑ index : Fin retained.length,
          paperFormulaClauseWidth
            formula (indexOrder index) *
            (2 ^ paperFormulaClauseWidth
              formula (indexOrder index) - 1) := by
      apply Finset.sum_congr rfl
      intro index _
      simp only [paperShiftedSourceClauseWeight, List.get_eq_getElem]
      rw [paperFormulaClauseWidth_retainedOriginal]
      rfl
    _ = ∑ index : Fin
          (srcFormula formula).clauses.length,
          paperFormulaClauseWidth formula index *
            (2 ^ paperFormulaClauseWidth
              formula index - 1) :=
      indexOrder.sum_comp
        (fun index =>
          paperFormulaClauseWidth formula index *
            (2 ^ paperFormulaClauseWidth
              formula index - 1))

theorem paperVariableArityShiftedFamilyTagCount_eq_sourceWeight
    (formula : ThreeCNF) (momentBudget : ℕ) :
    paperShiftedFamilyTagCount formula momentBudget =
      paperShiftedSourceClauseWeightSum
        (noTautClauses formula) *
          (momentBudget + 1) := by
  unfold paperShiftedFamilyTagCount
    paperShiftedClauseTagCount
  calc
    (∑ index : Fin
      (srcFormula formula).clauses.length,
      (2 ^ paperFormulaClauseWidth formula index - 1) *
        (paperFormulaClauseWidth formula index *
          (momentBudget + 1))) =
      ∑ index : Fin
        (srcFormula formula).clauses.length,
        (paperFormulaClauseWidth formula index *
          (2 ^ paperFormulaClauseWidth
            formula index - 1)) * (momentBudget + 1) := by
        apply Finset.sum_congr rfl
        intro index _
        ring
    _ =
      (∑ index : Fin
        (srcFormula formula).clauses.length,
        paperFormulaClauseWidth formula index *
          (2 ^ paperFormulaClauseWidth
            formula index - 1)) * (momentBudget + 1) := by
        rw [Finset.sum_mul]
    _ = paperShiftedSourceClauseWeightSum
        (noTautClauses formula) *
          (momentBudget + 1) := by
        rw [paperVariableArityShiftedSourceClauseWeightSum_eq_localWeights]

end CanonicalOffsetIdentity

namespace Factor400BinaryConstructivePaperVariableArityPhysicalRowCountMachine

open scoped BigOperators

open Turing GapCVP.Core GapCVP.BinaryEncoding
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.BinaryExplicitAffineSystem
open GapCVP.FormulaBridge GapCVP.ClauseOffsetTM GapCVP.SourceOrder GapCVP.ShiftedTupleTM
open GapCVP.CanonicalOffsetIdentity GapCVP.PhysicalColumnOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalFamilyMarkerTM

/-- GapCVP reduction support. -/
abbrev physicalFormulaShiftedTupleCount
    (formula : ThreeCNF) : ℕ :=
  paperShiftedSourceClauseWeightSum
    (noTautClauses formula)

private abbrev paperVariableArityPhysicalFormulaShiftedWidth
    (formula : ThreeCNF) : ℕ :=
  physicalFormulaShiftedTupleCount formula *
    physicalFormulaMomentCount formula *
    physGridCard formula *
    physDegree formula

/-- GapCVP reduction support. -/
abbrev paperVariableArityPhysicalFormulaRowCount
    (formula : ThreeCNF) : ℕ :=
  physicalFormulaOrdinaryBoundary formula +
    paperVariableArityPhysicalFormulaShiftedWidth formula

private abbrev physicalFormulaColumnCount
    (formula : ThreeCNF) : ℕ :=
  (1 + physicalFormulaTupleCount formula) *
    physGridCard formula *
    physFieldCard formula

private def physicalShiftedTupleCountUnary :
    List Bool → List Bool :=
  paperVariableArityShiftedTagCountUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalShiftedTupleCountUnaryComputable :
    BitTM
      physicalShiftedTupleCountUnary :=
  paperVariableArityShiftedTagCountUnaryComputable

@[simp] private theorem paperVariableArityPhysicalShiftedTupleCountUnary_valid
    (formula : ThreeCNF) :
    physicalShiftedTupleCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaShiftedTupleCount formula) true := by
  exact paperVariableArityShiftedTagCountUnary_valid formula

private def physicalShiftedWidthUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    (fourFamilyComputedUnaryProductOutput
      (fourFamilyComputedUnaryProductOutput
        physicalShiftedTupleCountUnary
        physicalFamilyMomentCountUnary)
      physicalFamilyGridCardinalityUnary)
    physicalFamilyFieldDegreeUnary

private noncomputable def paperVariableArityPhysicalShiftedWidthUnaryComputable :
    BitTM
      physicalShiftedWidthUnary :=
  fourFamilyComputedUnaryProductComputable
    (fourFamilyComputedUnaryProductComputable
      (fourFamilyComputedUnaryProductComputable
        paperVariableArityPhysicalShiftedTupleCountUnaryComputable
        paperVariableArityPhysicalFamilyMomentCountUnaryComputable)
      paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable)
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable

@[simp] private theorem paperVariableArityPhysicalShiftedWidthUnary_valid
    (formula : ThreeCNF) :
    physicalShiftedWidthUnary
        (encodeThreeCNF formula) =
      List.replicate
        (paperVariableArityPhysicalFormulaShiftedWidth formula) true := by
  let input := encodeThreeCNF formula
  have tagMoment := fourFamilyComputedUnaryProductOutput_valid
    physicalShiftedTupleCountUnary
    physicalFamilyMomentCountUnary input
    (physicalFormulaShiftedTupleCount formula)
    (physicalFormulaMomentCount formula)
    (paperVariableArityPhysicalShiftedTupleCountUnary_valid formula)
    (paperVariableArityPhysicalFamilyMomentCountUnary_valid formula)
  have grid := fourFamilyComputedUnaryProductOutput_valid
    (fourFamilyComputedUnaryProductOutput
      physicalShiftedTupleCountUnary
      physicalFamilyMomentCountUnary)
    physicalFamilyGridCardinalityUnary input
    (physicalFormulaShiftedTupleCount formula *
      physicalFormulaMomentCount formula)
    (physGridCard formula)
    tagMoment
    (paperVariableArityPhysicalFamilyGridCardinalityUnary_valid formula)
  exact fourFamilyComputedUnaryProductOutput_valid
    (fourFamilyComputedUnaryProductOutput
      (fourFamilyComputedUnaryProductOutput
        physicalShiftedTupleCountUnary
        physicalFamilyMomentCountUnary)
      physicalFamilyGridCardinalityUnary)
    physicalFamilyFieldDegreeUnary input
    (physicalFormulaShiftedTupleCount formula *
      physicalFormulaMomentCount formula *
      physGridCard formula)
    (physDegree formula)
    grid
    (paperVariableArityPhysicalFamilyFieldDegreeUnary_valid formula)

/-- GapCVP reduction support. -/
def physicalRowCountUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    physicalOrdinaryBoundaryUnary
    physicalShiftedWidthUnary

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalRowCountUnaryComputable :
    BitTM
      physicalRowCountUnary :=
  fourFamilyComputedUnarySumComputable
    paperVariableArityPhysicalOrdinaryBoundaryUnaryComputable
    paperVariableArityPhysicalShiftedWidthUnaryComputable

@[simp] private theorem paperVariableArityPhysicalRowCountUnary_formula_valid
    (formula : ThreeCNF) :
    physicalRowCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (paperVariableArityPhysicalFormulaRowCount formula) true := by
  unfold physicalRowCountUnary
  exact fourFamilyComputedUnarySumOutput_valid
    physicalOrdinaryBoundaryUnary
    physicalShiftedWidthUnary
    (encodeThreeCNF formula)
    (physicalFormulaOrdinaryBoundary formula)
    (paperVariableArityPhysicalFormulaShiftedWidth formula)
    (paperVariableArityPhysicalOrdinaryBoundaryUnary_valid formula)
    (paperVariableArityPhysicalShiftedWidthUnary_valid formula)

/-- GapCVP reduction support. -/
def physicalColumnCountUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    (fourFamilyComputedUnaryProductOutput
      physicalFamilyTypeCountUnary
      physicalFamilyGridCardinalityUnary)
    physicalFamilyFieldCardinalityUnary

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalColumnCountUnaryComputable :
    BitTM
      physicalColumnCountUnary :=
  fourFamilyComputedUnaryProductComputable
    (fourFamilyComputedUnaryProductComputable
      paperVariableArityPhysicalFamilyTypeCountUnaryComputable
      paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable)
    paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable

@[simp] private theorem paperVariableArityPhysicalColumnCountUnary_formula_valid
    (formula : ThreeCNF) :
    physicalColumnCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaColumnCount formula) true := by
  let input := encodeThreeCNF formula
  have typeGrid := fourFamilyComputedUnaryProductOutput_valid
    physicalFamilyTypeCountUnary
    physicalFamilyGridCardinalityUnary input
    (1 + physicalFormulaTupleCount formula)
    (physGridCard formula)
    (paperVariableArityPhysicalFamilyTypeCountUnary_valid formula)
    (paperVariableArityPhysicalFamilyGridCardinalityUnary_valid formula)
  exact fourFamilyComputedUnaryProductOutput_valid
    (fourFamilyComputedUnaryProductOutput
      physicalFamilyTypeCountUnary
      physicalFamilyGridCardinalityUnary)
    physicalFamilyFieldCardinalityUnary input
    ((1 + physicalFormulaTupleCount formula) *
      physGridCard formula)
    (physFieldCard formula)
    typeGrid
    (paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid formula)

private theorem paperVariableArityPhysicalFormulaColumnCount_eq_sourceDimension
    (formula : ThreeCNF) :
    physicalFormulaColumnCount formula =
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        (encodeThreeCNF formula).length
        (srcFormula formula) := by
  symm
  unfold GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
  rw [GapCVP.Core.sourceSATTableDimension_eq,
    sourceTableType_card,
    sourceFormulaGrid_card_eq_fieldWordCount,
    GapCVP.Core.sourceFiniteField_card
      (GapCVP.Core.sourceSizeParameter_ge_one_hundred
        (encodeThreeCNF formula).length
        (srcFormula formula)),
    paperVariableAritySourceFormula_variableCount,
    ← sourceClauseWeightSum_eq_localTagCount formula]

theorem paperVariableArityPhysicalColumnCountUnary_valid
    (formula : ThreeCNF) :
    physicalColumnCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).dimension true := by
  rw [paperVariableArityPhysicalColumnCountUnary_formula_valid,
    paperVariableArityPhysicalFormulaColumnCount_eq_sourceDimension]

theorem paperVariableArityExplicitBinaryRowWordCount_eq_fourFamily
    (formula : ThreeCNF) :
    paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula =
      paperVariableArityPhysicalFormulaRowCount formula := by
  classical
  let length := (encodeThreeCNF formula).length
  let source := srcFormula formula
  let gridCount := Fintype.card
    (ExplicitGridPoint length source)
  let fieldCount := Fintype.card
    (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
      length source)
  let degree := physDegree formula
  let momentCount := physicalFormulaMomentCount formula
  have grid_valid :
      gridCount = physGridCard formula := by
    change Fintype.card
      (ExplicitGridPoint length source) = _
    simpa [length, source,
      paperVariableAritySourceFormula_variableCount] using
      sourceFormulaGrid_card_eq_fieldWordCount length source
  have field_valid :
      fieldCount =
        physFieldCard formula := by
    change Fintype.card
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
        length source) = _
    simpa [length, source] using
      GapCVP.Core.sourceFiniteField_card
        (GapCVP.Core.sourceSizeParameter_ge_one_hundred length source)
  have shifted_valid :
      Fintype.card
        (Σ clause : Fin source.clauses.length,
          Σ _tuple :
            (source.clauses.get clause).SatisfyingLocalTuple,
          (source.clauses.get clause).LocalVariable ×
            Fin (explicitMomentBudget length source + 1)) =
        physicalFormulaShiftedTupleCount formula *
          momentCount := by
    calc
      Fintype.card
          (Σ clause : Fin source.clauses.length,
            Σ _tuple :
              (source.clauses.get clause).SatisfyingLocalTuple,
            (source.clauses.get clause).LocalVariable ×
              Fin (explicitMomentBudget length source + 1)) =
          paperShiftedFamilyTagCount
            formula (explicitMomentBudget length source) := by
            simpa [source] using
              (Fintype.card_congr
                (paperShiftedFamilyWordOrder formula
                  (explicitMomentBudget length source))).symm
      _ = physicalFormulaShiftedTupleCount formula *
          (explicitMomentBudget length source + 1) :=
        paperVariableArityShiftedFamilyTagCount_eq_sourceWeight
          formula (explicitMomentBudget length source)
      _ = physicalFormulaShiftedTupleCount formula *
          momentCount := by
        rfl
  have table_valid :
      Fintype.card (sourceSATTableType source) =
        1 + physicalFormulaTupleCount formula := by
    change Fintype.card
      (sourceSATTableType (srcFormula formula)) = _
    rw [sourceTableType_card,
      ← sourceClauseWeightSum_eq_localTagCount formula]
  calc
    paperExplicitBinaryRowWordCount
        length formula =
      ∑ family : ExplicitConstraintFamily length source,
        explicitFamilyRowCount length source family * degree := by
          unfold paperExplicitBinaryRowWordCount
            paperExplicitBinaryFamilyBlockCount
          exact (paperExplicitFamilyWordOrder
            length formula).sum_comp
            (fun family => explicitFamilyRowCount
              length (srcFormula formula)
              family * degree)
    _ = gridCount * degree +
      (noTautClauses formula).length *
        gridCount * fieldCount * degree +
      (1 + physicalFormulaTupleCount formula) *
        momentCount * gridCount * degree +
      physicalFormulaShiftedTupleCount formula *
        momentCount * gridCount * degree := by
          simp only [Fintype.sum_sum_type,
            explicitFamilyRowCount, Fintype.card_prod,
            Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Fintype.card_fin]
          rw [shifted_valid, table_valid]
          simp [source,
            gridCount, fieldCount, degree, momentCount,
            explicitMomentBudget]
          ring
    _ = paperVariableArityPhysicalFormulaRowCount formula := by
      rw [grid_valid, field_valid]

theorem paperVariableArityPhysicalRowCountUnary_valid
    (formula : ThreeCNF) :
    physicalRowCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).rowCount true := by
  rw [paperVariableArityPhysicalRowCountUnary_formula_valid]
  rw [paperVariableArityPhysicalWordBinarySystem_rowCount]
  rw [paperVariableArityExplicitBinaryRowWordCount_eq_fourFamily]

end Factor400BinaryConstructivePaperVariableArityPhysicalRowCountMachine

namespace CanonicalPhysicalMatrixShape

open Turing GapCVP.BinaryEncoding GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.FormulaBridge GapCVP.CanonicalMatrixShape GapCVP.PhysicalColumnOrder
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalRowCountMachine

/-- GapCVP reduction support. -/
noncomputable def paperCanonicalPhysicalMatrixShape :
    PaperVariableArityCanonicalBinaryMatrixShape where
  system := physicalWordBinarySystem
  systemCorrect _ _ := rfl
  rows := physicalRowCountUnary
  columns := physicalColumnCountUnary
  rowsComputable := paperVariableArityPhysicalRowCountUnaryComputable
  columnsComputable := paperVariableArityPhysicalColumnCountUnaryComputable
  rowsCorrect formula :=
    paperVariableArityPhysicalRowCountUnary_valid formula
  columnsCorrect formula :=
    paperVariableArityPhysicalColumnCountUnary_valid formula
  columnsPositive formula :=
    sourceFormulaDimension_pos
      (encodeThreeCNF formula).length
      (srcFormula formula)

@[simp] private theorem paperVariableArityCanonicalPhysicalMatrixShape_system
    (encodingLength : ℕ) (formula : ThreeCNF) :
    paperCanonicalPhysicalMatrixShape.system
        encodingLength formula =
      physicalWordBinarySystem encodingLength formula := by
  rfl

@[simp] theorem paperVariableArityCanonicalPhysicalMatrixShape_rows_valid
    (formula : ThreeCNF) :
    paperCanonicalPhysicalMatrixShape.rows
        (encodeThreeCNF formula) =
      List.replicate
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).rowCount true := by
  simpa only [paperVariableArityCanonicalPhysicalMatrixShape_system] using
    paperCanonicalPhysicalMatrixShape.rowsCorrect formula

@[simp] theorem paperVariableArityCanonicalPhysicalMatrixShape_columns_valid
    (formula : ThreeCNF) :
    paperCanonicalPhysicalMatrixShape.columns
        (encodeThreeCNF formula) =
      List.replicate
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).dimension true := by
  simpa only [paperVariableArityCanonicalPhysicalMatrixShape_system] using
    paperCanonicalPhysicalMatrixShape.columnsCorrect formula

/-- GapCVP reduction support. -/
abbrev PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer :=
  PaperVariableArityCanonicalBinaryMatrixCellComputer
    paperCanonicalPhysicalMatrixShape

end CanonicalPhysicalMatrixShape

namespace BinaryCompactPhysicalFieldCoefficientBitTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalCellGridWordTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalWordRuntimeDegreeTM

private def compactPhysicalFieldCoefficientBitQuery
    (basisRank : ℕ) (coefficient source : List Bool) : List Bool :=
  lengthPrefixedWord (List.replicate basisRank true) ++
    (lengthPrefixedWord coefficient ++ source)

private def compactPhysicalFieldCoefficientBitIndex : List Bool → List Bool :=
  firstFieldContents

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldCoefficientBitIndexComputable :
    BitTM
      compactPhysicalFieldCoefficientBitIndex :=
  firstFieldContentsComputable

private def compactPhysicalFieldCoefficientBitSource : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldCoefficientBitSourceComputable :
    BitTM
      compactPhysicalFieldCoefficientBitSource :=
  factor400BinaryPhysicalWordRuntimeCompositionComputer
    firstFieldSuffixComputable firstFieldContentsComputable

@[simp] private theorem compactPhysicalFieldCoefficientBitIndex_query
    (basisRank : ℕ) (coefficient source : List Bool) :
    compactPhysicalFieldCoefficientBitIndex
      (compactPhysicalFieldCoefficientBitQuery
        basisRank coefficient source) =
      List.replicate basisRank true := by
  simp only [compactPhysicalFieldCoefficientBitIndex, compactPhysicalFieldCoefficientBitQuery,
      firstFieldContents_valid]

@[simp] private theorem compactPhysicalFieldCoefficientBitSource_query
    (basisRank : ℕ) (coefficient source : List Bool) :
    compactPhysicalFieldCoefficientBitSource
      (compactPhysicalFieldCoefficientBitQuery
        basisRank coefficient source) = coefficient := by
  simp only [compactPhysicalFieldCoefficientBitSource, compactPhysicalFieldCoefficientBitQuery,
      Function.comp_apply, firstFieldSuffix_valid, firstFieldContents_valid]

private def compactPhysicalFieldCoefficientBitWord : List Bool → List Bool :=
  fiveFamilyOriginalDynamicBitWord
    compactPhysicalFieldCoefficientBitIndex
    compactPhysicalFieldCoefficientBitSource

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldCoefficientBitComputable :
    BitTM
      compactPhysicalFieldCoefficientBitWord :=
  fiveOriginalDynamicBitComputable
    compactPhysicalFieldCoefficientBitIndexComputable
    compactPhysicalFieldCoefficientBitSourceComputable

@[simp] private theorem compactPhysicalFieldCoefficientBitWord_valid
    (basisRank : ℕ) (coefficient source : List Bool) :
    compactPhysicalFieldCoefficientBitWord
      (compactPhysicalFieldCoefficientBitQuery
        basisRank coefficient source) =
      [(coefficient.drop basisRank).headD false] := by
  unfold compactPhysicalFieldCoefficientBitWord
  rw [fiveOriginalDynamicBitWord_valid
    compactPhysicalFieldCoefficientBitIndex
    compactPhysicalFieldCoefficientBitSource
    (compactPhysicalFieldCoefficientBitQuery
      basisRank coefficient source)
    basisRank
    (compactPhysicalFieldCoefficientBitIndex_query
      basisRank coefficient source),
    compactPhysicalFieldCoefficientBitSource_query]

private theorem compactPhysicalFieldCoefficientFiniteWord_drop_head
    {degree : ℕ}
    (word : GapCVP.Core.EffectiveBinaryField.Word degree)
    (basisRank : ℕ) (hrank : basisRank < degree) :
    ((finiteWordBits word).drop basisRank).headD false =
      word ⟨basisRank, hrank⟩ := by
  exact GapCVP.BinarySourceConvolutionCorrectness.factor400BinaryFiniteWordBits_drop_head
    word basisRank hrank

private def compactPhysicalFieldCoefficientBitPreparedQuery
    (basisRank coefficient source : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (basisRank.output input) ++
    (lengthPrefixedWord (coefficient.output input) ++
      source.output input)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldCoefficientBitPreparedQueryComputable
    (basisRank coefficient source : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalFieldCoefficientBitPreparedQuery
        basisRank coefficient source) :=
  physicalCellGridAppendComputer
    (factor400BinaryPhysicalWordRuntimeCompositionComputer
      basisRank.computer physicalCellGridPrefixComputer)
    (physicalCellGridAppendComputer
      (factor400BinaryPhysicalWordRuntimeCompositionComputer
        coefficient.computer physicalCellGridPrefixComputer)
      source.computer)

private theorem compactPhysicalFieldCoefficientBitPreparedQuery_valid
    (basisRank coefficient source : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) (position : ℕ)
    (coefficientWord originalSource : List Bool)
    (hrank : basisRank.output input =
      List.replicate position true)
    (hcoefficient : coefficient.output input = coefficientWord)
    (hsource : source.output input = originalSource) :
    compactPhysicalFieldCoefficientBitPreparedQuery
        basisRank coefficient source input =
      compactPhysicalFieldCoefficientBitQuery
        position coefficientWord originalSource := by
  simp only [compactPhysicalFieldCoefficientBitPreparedQuery,
    compactPhysicalFieldCoefficientBitQuery,
    hrank, hcoefficient, hsource]

/-- GapCVP reduction support. -/
def compactPhysicalFieldCoefficientPreparedBit
    (basisRank coefficient source : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  compactPhysicalFieldCoefficientBitWord ∘
    compactPhysicalFieldCoefficientBitPreparedQuery
      basisRank coefficient source

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldCoefficientPreparedBitComputable
    (basisRank coefficient source : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalFieldCoefficientPreparedBit
        basisRank coefficient source) :=
  factor400BinaryPhysicalWordRuntimeCompositionComputer
    (compactPhysicalFieldCoefficientBitPreparedQueryComputable
      basisRank coefficient source)
    compactPhysicalFieldCoefficientBitComputable

private theorem compactPhysicalFieldCoefficientPreparedBit_valid
    (basisRank coefficient source : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) (position : ℕ)
    (coefficientWord originalSource : List Bool)
    (hrank : basisRank.output input =
      List.replicate position true)
    (hcoefficient : coefficient.output input = coefficientWord)
    (hsource : source.output input = originalSource) :
    compactPhysicalFieldCoefficientPreparedBit
        basisRank coefficient source input =
      [(coefficientWord.drop position).headD false] := by
  unfold compactPhysicalFieldCoefficientPreparedBit
  rw [Function.comp_apply,
    compactPhysicalFieldCoefficientBitPreparedQuery_valid
      basisRank coefficient source input position
      coefficientWord originalSource hrank hcoefficient hsource,
    compactPhysicalFieldCoefficientBitWord_valid]

theorem compactPhysicalFieldCoefficientPreparedBit_bounded_valid
    {degree : ℕ}
    (basisRank coefficient source : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) (formula : ThreeCNF)
    (word : GapCVP.Core.EffectiveBinaryField.Word degree)
    (position : ℕ) (hposition : position < degree)
    (hrank : basisRank.output input =
      List.replicate position true)
    (hcoefficient : coefficient.output input = finiteWordBits word)
    (hsource : source.output input = encodeThreeCNF formula) :
    compactPhysicalFieldCoefficientPreparedBit
        basisRank coefficient source input =
      [word ⟨position, hposition⟩] := by
  rw [compactPhysicalFieldCoefficientPreparedBit_valid
    basisRank coefficient source input position
    (finiteWordBits word) (encodeThreeCNF formula)
    hrank hcoefficient hsource,
    compactPhysicalFieldCoefficientFiniteWord_drop_head
      word position hposition]

private noncomputable def compactPhysicalFieldCoefficientCellSourceComputer :
    SourcePhysicalLagrangeWordComputer where
  output := sourceExplicitAffineCellOriginalSource
  computer := factor400BinaryPhysicalWordCellOriginalSourceComputer

@[simp] private theorem compactPhysicalFieldCoefficientCellSourceComputer_query
    (row column : ℕ) (formula : ThreeCNF) :
    compactPhysicalFieldCoefficientCellSourceComputer.output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      encodeThreeCNF formula := by
  change sourceExplicitAffineCellOriginalSource
    (affineCellQuery row column
      (encodeThreeCNF formula)) = encodeThreeCNF formula
  exact sourceExplicitAffineCellOriginalSource_query
    row column (encodeThreeCNF formula)

/-- GapCVP reduction support. -/
def compactPhysicalFieldCoefficientCellBit
    (basisRank coefficient : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  compactPhysicalFieldCoefficientPreparedBit
    basisRank coefficient compactPhysicalFieldCoefficientCellSourceComputer

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldCoefficientCellBitComputable
    (basisRank coefficient : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalFieldCoefficientCellBit basisRank coefficient) :=
  compactPhysicalFieldCoefficientPreparedBitComputable
    basisRank coefficient compactPhysicalFieldCoefficientCellSourceComputer

theorem compactPhysicalFieldCoefficientCellBit_valid
    {degree : ℕ}
    (basisRank coefficient : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (word : GapCVP.Core.EffectiveBinaryField.Word degree)
    (position : ℕ) (hposition : position < degree)
    (hrank : basisRank.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
        List.replicate position true)
    (hcoefficient : coefficient.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits word) :
    compactPhysicalFieldCoefficientCellBit basisRank coefficient
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [word ⟨position, hposition⟩] := by
  unfold compactPhysicalFieldCoefficientCellBit
  exact compactPhysicalFieldCoefficientPreparedBit_bounded_valid
    basisRank coefficient compactPhysicalFieldCoefficientCellSourceComputer
    (affineCellQuery row column
      (encodeThreeCNF formula))
    formula word position hposition hrank hcoefficient
    (compactPhysicalFieldCoefficientCellSourceComputer_query
      row column formula)

end BinaryCompactPhysicalFieldCoefficientBitTM

namespace BinaryCompactPhysicalFieldBasisCoordinates

open Polynomial GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryFieldBasis
open GapCVP.BinaryFieldInverseAlgebra

private theorem effectiveExtensionBasis_wordElement_coordinate
    (degree : ℕ) (word : Word degree) (index : Fin degree) :
    (effectiveExtensionBasis degree).equivFun
      (wordElement word) index = bitValue (word index) := by
  change
    ((AdjoinRoot.powerBasisAux'
      (selectedPolynomial_monic degree)).reindex
        (finCongr (selectedPolynomial_natDegree degree))).equivFun
      (AdjoinRoot.mk (selectedPolynomial degree)
        (wordPolynomial word)) index = _
  rw [Module.Basis.equivFun_apply,
    Module.Basis.repr_reindex_apply,
    AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
    AdjoinRoot.modByMonicHom_mk]
  have hdegree :
      (wordPolynomial word).degree <
        (selectedPolynomial degree).degree := by
    rw [Polynomial.degree_eq_natDegree
      (selectedPolynomial_monic degree).ne_zero,
      selectedPolynomial_natDegree]
    exact wordPolynomial_degree_lt word
  rw [(Polynomial.modByMonic_eq_self_iff
    (selectedPolynomial_monic degree)).mpr hdegree]
  exact wordPolynomial_coeff_fin word index

theorem sourceFormulaFieldBasis_sourceWordValue_coordinate
    (encodingLength : ℕ) (formula : Formula)
    (word : Word
      (sourceFieldExponent
        (sourceSizeParameter encodingLength formula)))
    (index : Fin
      (sourceFieldExponent
        (sourceSizeParameter encodingLength formula))) :
    (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
      encodingLength formula).equivFun
      (sourceWordValue encodingLength formula word) index =
        bitValue (word index) := by
  change
    (effectiveFieldBasis
      (sourceFieldExponent
        (sourceSizeParameter encodingLength formula))
      (sourceFieldExponent_pos
        (sourceSizeParameter_ge_one_hundred encodingLength formula))).equivFun
      (extensionAlgEquivGaloisField
        (sourceFieldExponent
          (sourceSizeParameter encodingLength formula))
        (sourceFieldExponent_pos
          (sourceSizeParameter_ge_one_hundred encodingLength formula))
        (wordElement word)) index = _
  rw [effectiveFieldBasis_coordinates_transport]
  exact effectiveExtensionBasis_wordElement_coordinate
    (sourceFieldExponent
      (sourceSizeParameter encodingLength formula)) word index

end BinaryCompactPhysicalFieldBasisCoordinates

namespace MatrixEntrySemantics

open scoped BigOperators

open GapCVP.Core GapCVP.Core.EffectiveBinaryField
open GapCVP.BinaryCompactPhysicalFieldBasisCoordinates GapCVP.BinaryExplicitAffineSystem
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryOrderedRefinement GapCVP.FormulaBridge
open GapCVP.PhysicalColumnOrder GapCVP.SourceOrder GapCVP.BinaryPhysicalWordEntries
open GapCVP.BinaryReedSolomonParity GapCVP.BinarySourceRowOrder

attribute [local instance] Classical.propDecidable

/-- GapCVP reduction support. -/
abbrev PaperVariableArityPhysicalWordField
    (encodingLength : ℕ) (formula : ThreeCNF) :=
  GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
    encodingLength (srcFormula formula)

/-- GapCVP reduction support. -/
abbrev PaperVariableArityPhysicalWordDimension
    (encodingLength : ℕ) (formula : ThreeCNF) :=
  GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
    encodingLength (srcFormula formula)

/-- GapCVP reduction support. -/
abbrev PaperVariableArityPhysicalWordGrid
    (encodingLength : ℕ) (formula : ThreeCNF) :=
  GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
    encodingLength (srcFormula formula)

private def physicalWordBasisVector
    (encodingLength : ℕ) (formula : ThreeCNF)
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    Fin (PaperVariableArityPhysicalWordDimension
      encodingLength formula) →
        PaperVariableArityPhysicalWordField encodingLength formula :=
  Pi.single
    (physicalColumnPermutation
      encodingLength formula column) 1

/-- GapCVP reduction support. -/
def physicalWordCoordinateDelta
    (encodingLength : ℕ) (formula : ThreeCNF)
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula))
    (tableType : sourceSATTableType
      (srcFormula formula))
    (point : sourceSATGridPoint
      (PaperVariableArityPhysicalWordGrid encodingLength formula))
    (value : PaperVariableArityPhysicalWordField
      encodingLength formula) :
    PaperVariableArityPhysicalWordField encodingLength formula :=
  if physicalCoordinateIndex
      encodingLength formula tableType point value = column
    then 1 else 0

@[simp] private theorem paperVariableArityPhysicalWordBasisVector_apply_coordinate
    (encodingLength : ℕ) (formula : ThreeCNF)
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula))
    (tableType : sourceSATTableType
      (srcFormula formula))
    (point : sourceSATGridPoint
      (PaperVariableArityPhysicalWordGrid encodingLength formula))
    (value : PaperVariableArityPhysicalWordField
      encodingLength formula) :
    physicalWordBasisVector
      encodingLength formula column
        (sourceSATColumnIndex
          (srcFormula formula)
          (PaperVariableArityPhysicalWordGrid encodingLength formula)
          tableType point value) =
      physicalWordCoordinateDelta
        encodingLength formula column tableType point value := by
  let permutation :=
    physicalColumnPermutation
      encodingLength formula
  let semantic := sourceSATColumnIndex
    (srcFormula formula)
    (PaperVariableArityPhysicalWordGrid encodingLength formula)
    tableType point value
  have index :
      permutation.symm semantic =
        physicalCoordinateIndex
          encodingLength formula tableType point value :=
    paperVariableArityPhysicalColumnPermutation_symm_sourceSATColumnIndex
      encodingLength formula tableType point value
  have equivalent :
      permutation column = semantic ↔
        physicalCoordinateIndex
          encodingLength formula tableType point value = column := by
    constructor
    · intro equality
      have inverse := congrArg permutation.symm equality
      simpa only [index, Equiv.symm_apply_apply] using inverse.symm
    · intro equality
      apply permutation.symm.injective
      simpa only [Equiv.symm_apply_apply, index] using equality.symm
  simp only [physicalWordBasisVector,
    physicalWordCoordinateDelta]
  change Pi.single (permutation column) 1 semantic =
    if physicalCoordinateIndex
        encodingLength formula tableType point value = column
      then 1 else 0
  by_cases physical :
      physicalCoordinateIndex
        encodingLength formula tableType point value = column
  · have semanticEquality : semantic = permutation column :=
      (equivalent.mpr physical).symm
    rw [semanticEquality, Pi.single_eq_same]
    simp only [physical, ↓reduceIte]
  · have semanticInequality : semantic ≠ permutation column := by
      intro equality
      exact physical (equivalent.mp equality.symm)
    rw [Pi.single_eq_of_ne semanticInequality]
    simp only [physical, ↓reduceIte]

/-- GapCVP reduction support. -/
def physicalWordFamilyFieldCoefficient
    (encodingLength : ℕ) (formula : ThreeCNF)
    (family : ExplicitConstraintFamily
      encodingLength (srcFormula formula))
    (row : Fin
      (explicitFamilyRowCount
        encodingLength (srcFormula formula) family))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    PaperVariableArityPhysicalWordField encodingLength formula :=
  sourceFormulaPhysicalFamilyLinearMap
    encodingLength (srcFormula formula) family
      (physicalWordBasisVector
        encodingLength formula column) row

@[simp] private theorem paperVariableArityPhysicalWordFamilyFieldCoefficient_eq_matrix
    (encodingLength : ℕ) (formula : ThreeCNF)
    (family : ExplicitConstraintFamily
      encodingLength (srcFormula formula))
    (row : Fin
      (explicitFamilyRowCount
        encodingLength (srcFormula formula) family))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    physicalWordFamilyFieldCoefficient
        encodingLength formula family row column =
      sourceFormulaPhysicalFamilyFieldMatrix
        encodingLength (srcFormula formula) family row
          (physicalColumnPermutation
            encodingLength formula column) := by
  rw [sourceFormulaPhysicalFamilyFieldMatrix,
    LinearMap.toMatrix'_apply]
  rfl

theorem paperVariableArityPhysicalWordGlobalFieldCoefficient
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula))))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    physicalWordFamilyFieldCoefficient
      encodingLength formula (.inl ()) row column =
      ∑ value : PaperVariableArityPhysicalWordField
        encodingLength formula,
        physicalWordCoordinateDelta
          encodingLength formula column (.inl ())
          (sourceFormulaExplicitGridOrder
            encodingLength (srcFormula formula)
            row) value := by
  change
    (∑ value : PaperVariableArityPhysicalWordField
      encodingLength formula,
      physicalWordBasisVector
        encodingLength formula column
          (sourceSATColumnIndex
            (srcFormula formula)
            (PaperVariableArityPhysicalWordGrid
              encodingLength formula) (.inl ())
            (sourceFormulaExplicitGridOrder encodingLength
              (srcFormula formula) row)
            value)) = _
  apply Finset.sum_congr rfl
  intro value _
  exact paperVariableArityPhysicalWordBasisVector_apply_coordinate
    encodingLength formula column (.inl ())
    (sourceFormulaExplicitGridOrder
      encodingLength (srcFormula formula) row) value

theorem paperVariableArityPhysicalWordRefinementFieldCoefficient
    (encodingLength : ℕ) (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length)
    (row : Fin (Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula) ×
        PaperVariableArityPhysicalWordField
          encodingLength formula)))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    physicalWordFamilyFieldCoefficient
      encodingLength formula (.inr (.inl clause)) row column =
      let position := sourceFormulaExplicitRefinementOrder
        encodingLength (srcFormula formula) row
      physicalWordCoordinateDelta
          encodingLength formula column
          (.inl ()) position.1 position.2 -
        ∑ tuple :
          ((srcFormula
            formula).clauses.get clause).SatisfyingLocalTuple,
          physicalWordCoordinateDelta
            encodingLength formula column
              (.inr ⟨clause, tuple⟩) position.1 position.2 := by
  dsimp only
  change
    physicalWordBasisVector
      encodingLength formula column
        (sourceSATColumnIndex
          (srcFormula formula)
          (PaperVariableArityPhysicalWordGrid
            encodingLength formula) (.inl ())
          (sourceFormulaExplicitRefinementOrder
            encodingLength (srcFormula formula) row).1
          (sourceFormulaExplicitRefinementOrder
            encodingLength (srcFormula formula) row).2) -
      ∑ tuple :
        ((srcFormula
          formula).clauses.get clause).SatisfyingLocalTuple,
        physicalWordBasisVector
          encodingLength formula column
            (sourceSATColumnIndex
              (srcFormula formula)
              (PaperVariableArityPhysicalWordGrid
                encodingLength formula)
              (.inr ⟨clause, tuple⟩)
              (sourceFormulaExplicitRefinementOrder
                encodingLength
                (srcFormula formula) row).1
              (sourceFormulaExplicitRefinementOrder
                encodingLength
                (srcFormula formula) row).2) = _
  rw [paperVariableArityPhysicalWordBasisVector_apply_coordinate]
  refine congrArg (HSub.hSub _) ?_
  apply Finset.sum_congr rfl
  intro tuple _
  exact paperVariableArityPhysicalWordBasisVector_apply_coordinate
    encodingLength formula column (.inr ⟨clause, tuple⟩)
    (sourceFormulaExplicitRefinementOrder
      encodingLength (srcFormula formula) row).1
    (sourceFormulaExplicitRefinementOrder
      encodingLength (srcFormula formula) row).2

theorem paperVariableArityPhysicalWordOrdinaryFieldCoefficient
    (encodingLength : ℕ) (formula : ThreeCNF)
    (tableType : sourceSATTableType
      (srcFormula formula))
    (moment : Fin
      (explicitMomentBudget
        encodingLength (srcFormula formula) + 1))
    (row : Fin (Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula))))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    physicalWordFamilyFieldCoefficient
      encodingLength formula
        (.inr (.inr (.inl (tableType, moment)))) row column =
      ∑ position : Fin (Fintype.card
        (ExplicitGridPoint encodingLength
          (srcFormula formula))),
        constructiveParityMatrix
          (fun index =>
            (sourceFormulaExplicitGridOrder encodingLength
              (srcFormula formula) index).val)
          (explicitOrdinaryDegree_lt_grid encodingLength
            (srcFormula formula) moment)
          row position *
        ∑ value : PaperVariableArityPhysicalWordField
          encodingLength formula,
          physicalWordCoordinateDelta
            encodingLength formula column tableType
            (sourceFormulaExplicitGridOrder encodingLength
              (srcFormula formula) position) value *
              value ^ moment.val := by
  let gridOrder := sourceFormulaExplicitGridOrder
    encodingLength (srcFormula formula)
  let fieldVector := physicalWordBasisVector
    encodingLength formula column
  change
    constructiveParityLinearMap
      (fun index => (gridOrder index).val)
      (explicitOrdinaryDegree_lt_grid encodingLength
        (srcFormula formula) moment)
      (fun position =>
        ∑ value : PaperVariableArityPhysicalWordField
          encodingLength formula,
          fieldVector
            (sourceSATColumnIndex
              (srcFormula formula)
              (PaperVariableArityPhysicalWordGrid
                encodingLength formula)
              tableType (gridOrder position) value) *
                value ^ moment.val) row = _
  rw [← LinearMap.toMatrix'_mulVec]
  change
    (∑ position : Fin (Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula))),
      constructiveParityMatrix
        (fun index => (gridOrder index).val)
        (explicitOrdinaryDegree_lt_grid encodingLength
          (srcFormula formula) moment)
        row position *
      ∑ value : PaperVariableArityPhysicalWordField
        encodingLength formula,
        fieldVector
          (sourceSATColumnIndex
            (srcFormula formula)
            (PaperVariableArityPhysicalWordGrid
              encodingLength formula)
            tableType (gridOrder position) value) *
              value ^ moment.val) = _
  apply Finset.sum_congr rfl
  intro position _
  refine congrArg (HMul.hMul _) ?_
  apply Finset.sum_congr rfl
  intro value _
  refine congrArg (· * _) ?_
  exact paperVariableArityPhysicalWordBasisVector_apply_coordinate
    encodingLength formula column tableType
      (gridOrder position) value

theorem paperVariableArityPhysicalWordShiftedFieldCoefficient
    (encodingLength : ℕ) (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length)
    (tuple :
      ((srcFormula
        formula).clauses.get clause).SatisfyingLocalTuple)
    (localVariable :
      ((srcFormula
        formula).clauses.get clause).LocalVariable)
    (moment : Fin
      (explicitMomentBudget
        encodingLength (srcFormula formula) + 1))
    (row : Fin (Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula))))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    physicalWordFamilyFieldCoefficient
      encodingLength formula
        (.inr (.inr (.inr
          ⟨clause, tuple, localVariable, moment⟩))) row column =
      ∑ position : Fin (Fintype.card
        (ExplicitGridPoint encodingLength
          (srcFormula formula))),
        constructiveParityMatrix
          (fun index =>
            (sourceFormulaExplicitGridOrder encodingLength
              (srcFormula formula) index).val)
          (explicitShiftedDegree_lt_grid encodingLength
            (srcFormula formula) moment)
          row position *
        ∑ value : PaperVariableArityPhysicalWordField
          encodingLength formula,
          physicalWordCoordinateDelta
            encodingLength formula column
            (.inr ⟨clause, tuple⟩)
            (sourceFormulaExplicitGridOrder encodingLength
              (srcFormula formula) position) value *
            ((value -
                sourceSATFieldBit
                  (K := PaperVariableArityPhysicalWordField
                    encodingLength formula)
                  (tuple.val localVariable)) /
              ((sourceFormulaExplicitGridOrder encodingLength
                (srcFormula formula) position).val -
                GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
                    encodingLength (srcFormula formula)
                    localVariable.val)) ^ moment.val := by
  let gridOrder := sourceFormulaExplicitGridOrder
    encodingLength (srcFormula formula)
  let fieldVector := physicalWordBasisVector
    encodingLength formula column
  change
    constructiveParityLinearMap
      (fun index => (gridOrder index).val)
      (explicitShiftedDegree_lt_grid encodingLength
        (srcFormula formula) moment)
      (fun position =>
        ∑ value : PaperVariableArityPhysicalWordField
          encodingLength formula,
          fieldVector
            (sourceSATColumnIndex
              (srcFormula formula)
              (PaperVariableArityPhysicalWordGrid
                encodingLength formula)
              (.inr ⟨clause, tuple⟩) (gridOrder position) value) *
            ((value -
                sourceSATFieldBit
                  (K := PaperVariableArityPhysicalWordField
                    encodingLength formula)
                  (tuple.val localVariable)) /
              ((gridOrder position).val -
                GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
                    encodingLength (srcFormula formula)
                    localVariable.val)) ^ moment.val) row = _
  rw [← LinearMap.toMatrix'_mulVec]
  change
    (∑ position : Fin (Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula))),
      constructiveParityMatrix
        (fun index => (gridOrder index).val)
        (explicitShiftedDegree_lt_grid encodingLength
          (srcFormula formula) moment)
        row position *
      ∑ value : PaperVariableArityPhysicalWordField
        encodingLength formula,
        fieldVector
          (sourceSATColumnIndex
            (srcFormula formula)
            (PaperVariableArityPhysicalWordGrid
              encodingLength formula)
            (.inr ⟨clause, tuple⟩) (gridOrder position) value) *
          ((value -
              sourceSATFieldBit
                (K := PaperVariableArityPhysicalWordField
                  encodingLength formula)
                (tuple.val localVariable)) /
            ((gridOrder position).val -
              GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
                  encodingLength (srcFormula formula)
                  localVariable.val)) ^ moment.val) = _
  apply Finset.sum_congr rfl
  intro position _
  refine congrArg (HMul.hMul _) ?_
  apply Finset.sum_congr rfl
  intro value _
  refine congrArg (· * _) ?_
  exact paperVariableArityPhysicalWordBasisVector_apply_coordinate
    encodingLength formula column
      (.inr ⟨clause, tuple⟩) (gridOrder position) value

/-- GapCVP reduction support. -/
abbrev physicalWordDecodedRow
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      encodingLength formula)) :=
  paperVariableArityExplicitBinaryRowWordOrder
    encodingLength formula row

theorem physicalWordBinaryCheckCoefficient
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      encodingLength formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    (physicalWordBinarySystem
      encodingLength formula).check row column =
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
          encodingLength (srcFormula formula)).equivFun
        (physicalWordFamilyFieldCoefficient
          encodingLength formula
          (physicalWordDecodedRow
            encodingLength formula row).1
          (physicalWordDecodedRow
            encodingLength formula row).2.1 column)
        (physicalWordDecodedRow
          encodingLength formula row).2.2 := by
  rw [paperVariableArityPhysicalWordBinarySystem_check_apply]
  change
    binaryFieldParityMatrix
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
          encodingLength (srcFormula formula))
      (sourceFormulaPhysicalFamilyFieldMatrix
        encodingLength (srcFormula formula)
        (physicalWordDecodedRow
          encodingLength formula row).1)
      ((physicalWordDecodedRow
        encodingLength formula row).2.1,
       (physicalWordDecodedRow
        encodingLength formula row).2.2)
      (physicalColumnPermutation
        encodingLength formula column) = _
  rw [binaryFieldParityMatrix_apply_basisCoordinate]
  rw [← paperVariableArityPhysicalWordFamilyFieldCoefficient_eq_matrix]

private theorem paperVariableArityPhysicalWordBinaryRightHandSideCoefficient
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      encodingLength formula)) :
    (physicalWordBinarySystem
      encodingLength formula).rightHandSide row =
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
          encodingLength (srcFormula formula)).equivFun
        (explicitFamilyTarget
          encodingLength (srcFormula formula)
          (physicalWordDecodedRow
            encodingLength formula row).1
          (physicalWordDecodedRow
            encodingLength formula row).2.1)
        (physicalWordDecodedRow
          encodingLength formula row).2.2 := by
  rfl

@[simp] theorem paperVariableArityPhysicalFieldBasis_one_coordinate
    (encodingLength : ℕ) (formula : ThreeCNF)
    (coordinate : Fin
      (sourceFieldExponent
        (sourceSizeParameter encodingLength
          (srcFormula formula)))) :
    (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
        encodingLength (srcFormula formula)).equivFun
      1 coordinate = bitValue (decide (coordinate.val = 0)) := by
  have word := sourceFormulaFieldBasis_sourceWordValue_coordinate
    encodingLength (srcFormula formula)
    (oneWord (sourceFieldExponent
      (sourceSizeParameter encodingLength
        (srcFormula formula)))) coordinate
  rw [sourceWordValue_oneWord] at word
  simpa only [Module.Basis.equivFun_apply, oneWord] using word

private theorem paperVariableArityExplicitFamilyTarget_eq
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (family : ExplicitConstraintFamily encodingLength formula)
    (row : Fin (explicitFamilyRowCount
      encodingLength formula family)) :
    explicitFamilyTarget encodingLength formula family row =
      if family = .inl () then 1 else 0 := by
  cases family with
  | inl value =>
    cases value
    simp only [explicitFamilyTarget, List.get_eq_getElem, ↓reduceIte]
  | inr value =>
    simp only [explicitFamilyTarget, List.get_eq_getElem, reduceCtorEq, ↓reduceIte]

private theorem paperVariableArityPhysicalWordBinaryRightHandSide_global
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      encodingLength formula))
    (global :
      (physicalWordDecodedRow
        encodingLength formula row).1 = .inl ()) :
    (physicalWordBinarySystem
      encodingLength formula).rightHandSide row =
      bitValue (decide
        ((physicalWordDecodedRow
          encodingLength formula row).2.2.val = 0)) := by
  rw [paperVariableArityPhysicalWordBinaryRightHandSideCoefficient]
  rw [paperVariableArityExplicitFamilyTarget_eq,
    ite_eq_left global]
  exact paperVariableArityPhysicalFieldBasis_one_coordinate
    encodingLength formula
      (physicalWordDecodedRow
        encodingLength formula row).2.2

private theorem paperVariableArityPhysicalWordBinaryRightHandSide_nonGlobal
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      encodingLength formula))
    (nonGlobal :
      (physicalWordDecodedRow
        encodingLength formula row).1 ≠ .inl ()) :
    (physicalWordBinarySystem
      encodingLength formula).rightHandSide row = 0 := by
  rw [paperVariableArityPhysicalWordBinaryRightHandSideCoefficient]
  rw [paperVariableArityExplicitFamilyTarget_eq,
    ite_eq_right nonGlobal]
  simp only [map_zero, Pi.zero_apply]

private theorem paperVariableArityPhysicalWordBinaryRightHandSide_eq_one_iff
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      encodingLength formula)) :
    (physicalWordBinarySystem
      encodingLength formula).rightHandSide row = 1 ↔
      (physicalWordDecodedRow
        encodingLength formula row).1 = .inl () ∧
      (physicalWordDecodedRow
        encodingLength formula row).2.2.val = 0 := by
  by_cases global :
      (physicalWordDecodedRow
        encodingLength formula row).1 = .inl ()
  · rw [paperVariableArityPhysicalWordBinaryRightHandSide_global
      encodingLength formula row global]
    simp only [bitValue, decide_eq_true_eq, ite_eq_left_iff, zero_ne_one, imp_false,
        Decidable.not_not, global,
        List.get_eq_getElem, true_and]
  · rw [paperVariableArityPhysicalWordBinaryRightHandSide_nonGlobal
      encodingLength formula row global]
    simp only [zero_ne_one, List.get_eq_getElem, global, false_and]

end MatrixEntrySemantics

namespace PhysicalRowOrderProjection

open scoped BigOperators

open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.FormulaBridge
open GapCVP.SourceOrder GapCVP.PhysicalColumnOrder GapCVP.MatrixEntrySemantics

/-- GapCVP reduction support. -/
def physicalRowDependentFamilyIndex
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    Fin (paperExplicitFamilyTagCount
      encodingLength formula) :=
  ((finSigmaFinEquiv
    (n := paperExplicitBinaryFamilyBlockCount
      encodingLength formula)).symm row).1

/-- GapCVP reduction support. -/
def physicalRowDependentBlockRank
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    Fin (paperExplicitBinaryFamilyBlockCount
      encodingLength formula
      (physicalRowDependentFamilyIndex
        encodingLength formula row)) :=
  ((finSigmaFinEquiv
    (n := paperExplicitBinaryFamilyBlockCount
      encodingLength formula)).symm row).2

theorem physicalRowDependentRank_eq_prefix
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    row.val =
      (∑ index : Fin
        (physicalRowDependentFamilyIndex
          encodingLength formula row).val,
        paperExplicitBinaryFamilyBlockCount
          encodingLength formula
          (Fin.castLE
            (physicalRowDependentFamilyIndex
              encodingLength formula row).isLt.le index)) +
        (physicalRowDependentBlockRank
          encodingLength formula row).val := by
  let decomposition :=
    (finSigmaFinEquiv
      (n := paperExplicitBinaryFamilyBlockCount
        encodingLength formula)).symm row
  change row.val =
    (∑ index : Fin decomposition.1.val,
      paperExplicitBinaryFamilyBlockCount
        encodingLength formula
        (Fin.castLE decomposition.1.isLt.le index)) +
      decomposition.2.val
  calc
    row.val = (finSigmaFinEquiv decomposition).val := by
      exact congrArg Fin.val
        ((finSigmaFinEquiv
          (n := paperExplicitBinaryFamilyBlockCount
            encodingLength formula)).apply_symm_apply row).symm
    _ = _ := finSigmaFinEquiv_apply decomposition

theorem physicalRowOrder_family
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    (physicalWordDecodedRow
      encodingLength formula row).1 =
      paperExplicitFamilyWordOrder
        encodingLength formula
        (physicalRowDependentFamilyIndex
          encodingLength formula row) := by
  rfl

theorem physicalRowOrder_fieldRow
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    (physicalWordDecodedRow
      encodingLength formula row).2.1.val =
      (physicalRowDependentBlockRank
        encodingLength formula row).val /
        paperExplicitBinaryRowDegree
          encodingLength formula := by
  rfl

private theorem paperVariableArityPhysicalRowOrder_basis
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    (physicalWordDecodedRow
      encodingLength formula row).2.2.val =
      (physicalRowDependentBlockRank
        encodingLength formula row).val %
        paperExplicitBinaryRowDegree
          encodingLength formula := by
  rfl

theorem physicalRowOrder_basis_val
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    (physicalWordDecodedRow
      encodingLength formula row).2.2.val =
      row.val % paperExplicitBinaryRowDegree
        encodingLength formula := by
  rw [paperVariableArityPhysicalRowOrder_basis]
  have rank := physicalRowDependentRank_eq_prefix
    encodingLength formula row
  have prefixSum :
      (∑ index : Fin
        (physicalRowDependentFamilyIndex
          encodingLength formula row).val,
        paperExplicitBinaryFamilyBlockCount
          encodingLength formula
          (Fin.castLE
            (physicalRowDependentFamilyIndex
              encodingLength formula row).isLt.le index)) =
        (∑ index : Fin
          (physicalRowDependentFamilyIndex
            encodingLength formula row).val,
          explicitFamilyRowCount encodingLength
            (srcFormula formula)
            (paperExplicitFamilyWordOrder
              encodingLength formula
              (Fin.castLE
                (physicalRowDependentFamilyIndex
                  encodingLength formula row).isLt.le index))) *
            paperExplicitBinaryRowDegree
              encodingLength formula := by
    simp only [paperExplicitBinaryFamilyBlockCount]
    rw [Finset.sum_mul]
  rw [prefixSum] at rank
  have residue := congrArg
    (fun value : ℕ =>
      value % paperExplicitBinaryRowDegree
        encodingLength formula) rank
  simpa only [Nat.add_mod, Nat.mul_mod_left, zero_add, dvd_refl, Nat.mod_mod_of_dvd]
      using residue.symm

private theorem paperVariableArityPhysicalSigmaFamilyIndex_zero_iff
    {familyCount : ℕ}
    (blockCount : Fin familyCount → ℕ)
    (positive : 0 < familyCount)
    (row : Fin (∑ index : Fin familyCount, blockCount index)) :
    ((finSigmaFinEquiv (n := blockCount)).symm row).1.val = 0 ↔
      row.val < blockCount ⟨0, positive⟩ := by
  let decomposition :=
    (finSigmaFinEquiv (n := blockCount)).symm row
  have rank :
      row.val =
        (∑ index : Fin decomposition.1.val,
          blockCount (Fin.castLE decomposition.1.isLt.le index)) +
        decomposition.2.val := by
    simpa only [decomposition, Equiv.apply_symm_apply] using
      finSigmaFinEquiv_apply decomposition
  constructor
  · intro zero
    change decomposition.1.val = 0 at zero
    have first : decomposition.1 = ⟨0, positive⟩ := by
      apply Fin.ext
      exact zero
    have prefixZero :
        (∑ index : Fin decomposition.1.val,
          blockCount (Fin.castLE decomposition.1.isLt.le index)) = 0 := by
      apply Finset.sum_eq_zero
      intro index _
      exact Fin.elim0 (Fin.cast zero index)
    have localEquality : row.val = decomposition.2.val := by
      omega
    rw [localEquality]
    simpa [first] using decomposition.2.isLt
  · intro bounded
    by_contra nonzero
    change decomposition.1.val ≠ 0 at nonzero
    have indexPositive : 0 < decomposition.1.val :=
      Nat.pos_of_ne_zero nonzero
    let first : Fin decomposition.1.val := ⟨0, indexPositive⟩
    have prefixLower :
        blockCount ⟨0, positive⟩ ≤
          ∑ index : Fin decomposition.1.val,
            blockCount (Fin.castLE decomposition.1.isLt.le index) := by
      have term := Finset.single_le_sum
        (f := fun index : Fin decomposition.1.val =>
          blockCount (Fin.castLE decomposition.1.isLt.le index))
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ first)
      simpa [first] using term
    omega

theorem physicalFamilyTagCount_pos
    (encodingLength : ℕ) (formula : ThreeCNF) :
    0 < paperExplicitFamilyTagCount
      encodingLength formula := by
  simp only [paperExplicitFamilyTagCount,
      add_pos_iff,
      Order.lt_one_iff, true_or, mul_pos_iff_of_pos_left, Order.lt_add_one_iff, zero_le, or_true,
          or_self]

theorem physicalFamilyWordOrder_zero
    (encodingLength : ℕ) (formula : ThreeCNF) :
    paperExplicitFamilyWordOrder
      encodingLength formula
      ⟨0, physicalFamilyTagCount_pos
        encodingLength formula⟩ = .inl () := by
  rfl

theorem physicalFirstFamilyBlockCount
    (encodingLength : ℕ) (formula : ThreeCNF) :
    paperExplicitBinaryFamilyBlockCount
      encodingLength formula
      ⟨0, physicalFamilyTagCount_pos
        encodingLength formula⟩ =
      Fintype.card
        (ExplicitGridPoint encodingLength
          (srcFormula formula)) *
        paperExplicitBinaryRowDegree
          encodingLength formula := by
  simp only [paperExplicitBinaryFamilyBlockCount, explicitFamilyRowCount,
      physicalFamilyWordOrder_zero,
      List.get_eq_getElem, Fintype.card_coe]

/-- GapCVP reduction support. -/
abbrev physicalSourceGlobalBoundary
    (encodingLength : ℕ) (formula : ThreeCNF) : ℕ :=
  Fintype.card
    (ExplicitGridPoint encodingLength
      (srcFormula formula)) *
    paperExplicitBinaryRowDegree
      encodingLength formula

theorem paperVariableArityPhysicalRowOrder_global_iff
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    (physicalWordDecodedRow
      encodingLength formula row).1 = .inl () ↔
      row.val < physicalSourceGlobalBoundary
        encodingLength formula := by
  let positive := physicalFamilyTagCount_pos
    encodingLength formula
  have first := paperVariableArityPhysicalSigmaFamilyIndex_zero_iff
    (paperExplicitBinaryFamilyBlockCount
      encodingLength formula) positive row
  constructor
  · intro global
    have selected :
        paperExplicitFamilyWordOrder
          encodingLength formula
          (physicalRowDependentFamilyIndex
            encodingLength formula row) = .inl () := by
      exact (physicalRowOrder_family
        encodingLength formula row).symm.trans global
    have zero :
        physicalRowDependentFamilyIndex
          encodingLength formula row = ⟨0, positive⟩ := by
      apply
        (paperExplicitFamilyWordOrder
          encodingLength formula).injective
      simpa only [physicalFamilyWordOrder_zero, List.get_eq_getElem] using selected
    have selectedZero :
        ((finSigmaFinEquiv
          (n := paperExplicitBinaryFamilyBlockCount
            encodingLength formula)).symm row).1.val = 0 := by
      change
        (physicalRowDependentFamilyIndex
          encodingLength formula row).val = 0
      exact congrArg Fin.val zero
    have bounded := first.mp selectedZero
    rw [physicalFirstFamilyBlockCount] at bounded
    exact bounded
  · intro bounded
    have inFirst :
        row.val < paperExplicitBinaryFamilyBlockCount
          encodingLength formula ⟨0, positive⟩ := by
      rw [physicalFirstFamilyBlockCount]
      exact bounded
    have zero := first.mpr inFirst
    have selected :
        physicalRowDependentFamilyIndex
          encodingLength formula row = ⟨0, positive⟩ := by
      apply Fin.ext
      exact zero
    rw [physicalRowOrder_family]
    change
      paperExplicitFamilyWordOrder
        encodingLength formula
        (physicalRowDependentFamilyIndex
          encodingLength formula row) = .inl ()
    rw [selected]
    exact physicalFamilyWordOrder_zero
      encodingLength formula

theorem physicalSourceGridCardinality_eq
    (encodingLength : ℕ) (formula : ThreeCNF) :
    Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula)) =
      2 ^ sourceFieldExponent
          (sourceSizeParameter encodingLength
            (srcFormula formula)) -
        paperVariableArityVariableCount formula := by
  simpa only [Fintype.card_coe, paperVariableAritySourceFormula_variableCount] using
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid_card_eq_fieldWordCount
          encodingLength
        (srcFormula formula)

private theorem paperVariableArityPhysicalSourceGlobalBoundary_eq
    (formula : ThreeCNF) :
    physicalSourceGlobalBoundary
      (encodeThreeCNF formula).length formula =
      (2 ^ sourceFieldExponent
        (sourceSizeParameter (encodeThreeCNF formula).length
          (srcFormula formula)) -
        paperVariableArityVariableCount formula) *
      sourceFieldExponent
        (sourceSizeParameter (encodeThreeCNF formula).length
          (srcFormula formula)) := by
  change
    Fintype.card
      (ExplicitGridPoint (encodeThreeCNF formula).length
        (srcFormula formula)) *
      sourceFieldExponent
        (sourceSizeParameter (encodeThreeCNF formula).length
          (srcFormula formula)) = _
  rw [physicalSourceGridCardinality_eq]

private theorem paperVariableArityPhysicalWordBinaryRightHandSide_eq_one_iff_sourceRanks
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    (physicalWordBinarySystem
      encodingLength formula).rightHandSide row = 1 ↔
      row.val < physicalSourceGlobalBoundary
        encodingLength formula ∧
      row.val % paperExplicitBinaryRowDegree
        encodingLength formula = 0 := by
  rw [paperVariableArityPhysicalWordBinaryRightHandSide_eq_one_iff]
  exact and_congr
    (paperVariableArityPhysicalRowOrder_global_iff
      encodingLength formula row)
    (by rw [physicalRowOrder_basis_val])

/-- GapCVP reduction support. -/
def physicalSigmaPrefix
    {familyCount : ℕ}
    (blockCount : Fin familyCount → ℕ)
    (family : Fin familyCount) : ℕ :=
  ∑ index : Fin family.val,
    blockCount (Fin.castLE family.isLt.le index)

theorem paperVariableArityPhysicalSigmaFamilyIndex_eq_iff
    {familyCount : ℕ}
    (blockCount : Fin familyCount → ℕ)
    (row : Fin (∑ index : Fin familyCount, blockCount index))
    (family : Fin familyCount) :
    ((finSigmaFinEquiv (n := blockCount)).symm row).1 = family ↔
      physicalSigmaPrefix
        blockCount family ≤ row.val ∧
        row.val < physicalSigmaPrefix
          blockCount family + blockCount family := by
  let decomposition :=
    (finSigmaFinEquiv (n := blockCount)).symm row
  have rank :
      row.val =
        physicalSigmaPrefix
          blockCount decomposition.1 + decomposition.2.val := by
    simpa only [physicalSigmaPrefix,
      decomposition, Equiv.apply_symm_apply] using
      finSigmaFinEquiv_apply decomposition
  constructor
  · intro selected
    change decomposition.1 = family at selected
    subst family
    have bound := decomposition.2.isLt
    omega
  · rintro ⟨lower, upper⟩
    let localRank : Fin (blockCount family) :=
      ⟨row.val - physicalSigmaPrefix
        blockCount family, by omega⟩
    have forward :
        finSigmaFinEquiv (n := blockCount)
          (⟨family, localRank⟩ : (index : Fin familyCount) ×
            Fin (blockCount index)) = row := by
      apply Fin.ext
      rw [finSigmaFinEquiv_apply]
      change
        physicalSigmaPrefix blockCount family +
          (row.val - physicalSigmaPrefix
            blockCount family) = row.val
      omega
    have decode :
        (finSigmaFinEquiv (n := blockCount)).symm row =
          (⟨family, localRank⟩ : (index : Fin familyCount) ×
            Fin (blockCount index)) := by
      rw [← forward, Equiv.symm_apply_apply]
    exact congrArg Sigma.fst decode

/-- GapCVP reduction support. -/
def physicalRefinementFamilyIndex
    (encodingLength : ℕ) (formula : ThreeCNF)
    (clause : Fin
      (srcFormula formula).clauses.length) :
    Fin (paperExplicitFamilyTagCount
      encodingLength formula) :=
  (paperExplicitFamilyWordOrder
    encodingLength formula).symm (.inr (.inl clause))

theorem paperVariableArityPhysicalRefinementFamilyIndex_val
    (encodingLength : ℕ) (formula : ThreeCNF)
    (clause : Fin
      (srcFormula formula).clauses.length) :
    (physicalRefinementFamilyIndex
      encodingLength formula clause).val = 1 + clause.val := by
  rfl

theorem paperVariableArityPhysicalRefinementFamilyBlockCount
    (encodingLength : ℕ) (formula : ThreeCNF)
    (clause : Fin
      (srcFormula formula).clauses.length) :
    paperExplicitBinaryFamilyBlockCount
      encodingLength formula
      (physicalRefinementFamilyIndex
        encodingLength formula clause) =
      Fintype.card
        (ExplicitGridPoint encodingLength
          (srcFormula formula)) *
      Fintype.card
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
          encodingLength (srcFormula formula)) *
      paperExplicitBinaryRowDegree
        encodingLength formula := by
  simp only [paperExplicitBinaryFamilyBlockCount, explicitFamilyRowCount,
      physicalRefinementFamilyIndex,
      List.get_eq_getElem, Equiv.apply_symm_apply, Fintype.card_prod, Fintype.card_coe]

end PhysicalRowOrderProjection

namespace PhysicalRightHandSideTM

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryPhysicalRowBasisDivisionTM
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.PhysicalColumnOrder
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalRowOrderProjection

/-- GapCVP reduction support. -/
def physicalRightHandSideCellDegreeUnary :
    List Bool → List Bool :=
  physicalFamilyFieldDegreeUnary ∘
    sourceExplicitAffineCellOriginalSource

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRightHandSideCellDegreeUnaryComputable :
    BitTM
      physicalRightHandSideCellDegreeUnary :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable

@[simp] theorem paperVariableArityPhysicalRightHandSideCellDegreeUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRightHandSideCellDegreeUnary
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physDegree formula) true := by
  unfold physicalRightHandSideCellDegreeUnary
  rw [Function.comp_apply, sourceExplicitAffineCellOriginalSource_query,
    paperVariableArityPhysicalFamilyFieldDegreeUnary_valid]

private def physicalRightHandSideBasisRankUnary :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryRemainder
    sourceExplicitAffineCellRow
    physicalRightHandSideCellDegreeUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRightHandSideBasisRankUnaryComputable :
    BitTM
      physicalRightHandSideBasisRankUnary :=
  sourcePhysicalComputedUnaryRemainderComputable
    sourceExplicitAffineCellRowComputable
    paperVariableArityPhysicalRightHandSideCellDegreeUnaryComputable

@[simp] private theorem paperVariableArityPhysicalRightHandSideBasisRankUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRightHandSideBasisRankUnary
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (row % physDegree formula) true := by
  unfold physicalRightHandSideBasisRankUnary
  apply sourcePhysicalComputedUnaryRemainder_valid
    sourceExplicitAffineCellRow
    physicalRightHandSideCellDegreeUnary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    row (physDegree formula)
  · exact GapCVP.Core.sourceFieldExponent_pos
      (GapCVP.Core.sourceSizeParameter_ge_one_hundred
        (encodeThreeCNF formula).length
        (srcFormula formula))
  · exact sourceExplicitAffineCellRow_query
      row column (encodeThreeCNF formula)
  · exact paperVariableArityPhysicalRightHandSideCellDegreeUnary_query
      row column formula

/-- GapCVP reduction support. -/
def physicalRightHandSideBasisZeroBit :
    List Bool → List Bool :=
  maskComputedWordEquality
    physicalRightHandSideBasisRankUnary
    (fun _ => [])

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRightHandSideBasisZeroBitComputable :
    BitTM
      physicalRightHandSideBasisZeroBit :=
  maskComputedWordEqualityComputable
    paperVariableArityPhysicalRightHandSideBasisRankUnaryComputable
    (sourceFixedWordComputable [])

@[simp] theorem paperVariableArityPhysicalRightHandSideBasisZeroBit_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRightHandSideBasisZeroBit
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide (row % physDegree formula = 0)] := by
  unfold physicalRightHandSideBasisZeroBit
  rw [sourceQaryMaskSquareComputedWordEquality_valid,
    paperVariableArityPhysicalRightHandSideBasisRankUnary_query]
  simp only [List.replicate_eq_nil_iff]

/-- GapCVP reduction support. -/
def physicalRightHandSideBit :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    physicalGlobalRowMarker
    physicalRightHandSideBasisZeroBit

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalRightHandSideBitComputable :
    BitTM
      physicalRightHandSideBit :=
  fourFamilyBooleanAndComputable
    paperVariableArityPhysicalGlobalRowMarkerComputable
    paperVariableArityPhysicalRightHandSideBasisZeroBitComputable

@[simp] private theorem paperVariableArityPhysicalRightHandSideBit_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRightHandSideBit
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (row < physicalFormulaGlobalBoundary formula) &&
       decide
        (row % physDegree formula = 0)] := by
  unfold physicalRightHandSideBit
  exact fourFamilyBooleanAndOutput_bits
    physicalGlobalRowMarker
    physicalRightHandSideBasisZeroBit
    (affineCellQuery row column
      (encodeThreeCNF formula))
    (decide
      (row < physicalFormulaGlobalBoundary formula))
    (decide
      (row % physDegree formula = 0))
    (paperVariableArityPhysicalGlobalRowMarker_query
      row column formula)
    (paperVariableArityPhysicalRightHandSideBasisZeroBit_query
      row column formula)

theorem paperVariableArityPhysicalRightHandSide_valid
    (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula)) :
    physicalRightHandSideBit
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).rightHandSide row =
            (1 : ZMod 2))] := by
  have boundary :
      physicalSourceGlobalBoundary
        (encodeThreeCNF formula).length formula =
        physicalFormulaGlobalBoundary formula :=
    paperVariableArityPhysicalSourceGlobalBoundary_eq formula
  have target :
      (row.val < physicalFormulaGlobalBoundary formula ∧
        row.val % physDegree formula = 0) ↔
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).rightHandSide row =
            (1 : ZMod 2) := by
    have ranks := paperVariableArityPhysicalWordBinaryRightHandSide_eq_one_iff_sourceRanks
      (encodeThreeCNF formula).length formula row
    rw [boundary] at ranks
    exact ranks.symm
  rw [paperVariableArityPhysicalRightHandSideBit_query,
    ← Bool.decide_and]
  exact congrArg (fun bit : Bool => [bit])
    (Bool.decide_congr target)

end PhysicalRightHandSideTM

namespace BinaryAllWordRankOrder

open GapCVP.BinaryFieldBasis GapCVP.Core.EffectiveBinaryField

private theorem naturalRange_double_flatMap (count : ℕ) :
    List.range (2 * count) =
      (List.range count).flatMap
        (fun rank => [2 * rank, 2 * rank + 1]) := by
  induction count with
  | zero => simp only [mul_zero, List.range_zero, List.flatMap_nil]
  | succ count ih =>
      rw [show 2 * (count + 1) = 2 * count + 2 by omega,
        List.range_add]
      simp only [ih, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
          List.map_cons, add_zero,
          List.map_nil, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

private def naturalRankWord (degree rank : ℕ) : Word degree :=
  fun bit => rank.testBit bit.val

private theorem naturalRankWord_even
    (degree rank : ℕ) :
    naturalRankWord (degree + 1) (2 * rank) =
      Fin.cases false (naturalRankWord degree rank) := by
  funext bit
  refine Fin.cases ?_ (fun next => ?_) bit
  · simp only [naturalRankWord, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.testBit_zero,
      Nat.mul_mod_right,
        zero_ne_one, decide_false, Fin.cases_zero]
  · simp only [naturalRankWord, Fin.val_succ, Nat.testBit_succ, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true,
        mul_div_cancel_left₀, Fin.cases_succ]

private theorem naturalRankWord_odd
    (degree rank : ℕ) :
    naturalRankWord (degree + 1) (2 * rank + 1) =
      Fin.cases true (naturalRankWord degree rank) := by
  funext bit
  refine Fin.cases ?_ (fun next => ?_) bit
  · simp only [naturalRankWord, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.testBit_zero,
      Nat.mul_add_mod_self_left,
        Nat.mod_succ, decide_true, Fin.cases_zero]
  · change
      (2 * rank + 1).testBit (next.val + 1) =
        rank.testBit next.val
    have hdivision : (2 * rank + 1) / 2 = rank := by
      omega
    rw [show next.val + 1 = Nat.succ next.val by omega,
      Nat.testBit_succ, hdivision]

private theorem allWords_eq_naturalRankWords (degree : ℕ) :
    allWords degree =
      (List.range (2 ^ degree)).map
        (naturalRankWord degree) := by
  induction degree with
  | zero =>
      change [(fun bit : Fin 0 => Fin.elim0 bit)] =
        [naturalRankWord 0 0]
      congr 1
      exact Subsingleton.elim _ _
  | succ degree ih =>
      calc
        allWords (degree + 1) =
            ((List.range (2 ^ degree)).map
              (naturalRankWord degree)).flatMap
              (fun tail =>
                [Fin.cases false tail, Fin.cases true tail]) := by
              rw [allWords, ih]
        _ = (List.range (2 ^ degree)).flatMap
              (fun rank =>
                [naturalRankWord (degree + 1) (2 * rank),
                 naturalRankWord (degree + 1) (2 * rank + 1)]) := by
              simp only [List.flatMap_map]
              apply List.flatMap_congr
              intro rank _
              rw [naturalRankWord_even, naturalRankWord_odd]
        _ = ((List.range (2 ^ degree)).flatMap
              (fun rank => [2 * rank, 2 * rank + 1])).map
                (naturalRankWord (degree + 1)) := by
              simp only [List.map_flatMap, List.map_cons, List.map_nil]
        _ = (List.range (2 * 2 ^ degree)).map
              (naturalRankWord (degree + 1)) := by
              rw [naturalRange_double_flatMap]
        _ = (List.range (2 ^ (degree + 1))).map
              (naturalRankWord (degree + 1)) := by
              rw [pow_succ]
              congr 2
              omega

theorem allWords_eq_finRange_indexedWord (degree : ℕ) :
    allWords degree =
      (List.finRange (2 ^ degree)).map (indexedWord degree) := by
  calc
    allWords degree =
        (List.range (2 ^ degree)).map
          (naturalRankWord degree) :=
      allWords_eq_naturalRankWords degree
    _ = ((List.finRange (2 ^ degree)).map
          (fun rank => rank.val)).map
            (naturalRankWord degree) := by
          rw [List.map_coe_finRange_eq_range]
    _ = (List.finRange (2 ^ degree)).map
          (indexedWord degree) := by
          rw [List.map_map]
          rfl

end BinaryAllWordRankOrder

namespace BinarySelectedIrreducibleWordTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryFieldBasis
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalWordRuntimeDegreeTM
open GapCVP.BinarySourceConvolutionTM

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalCompositionComputer
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g) :
    BitTM (g ∘ f) :=
  GapCVP.TMComposition.computableInPolyTime first second

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalAppendComputer
    {first second : List Bool → List Bool}
    (firstComputer : BitTM first)
    (secondComputer : BitTM second) :
    BitTM
      (fun input => first input ++ second input) :=
  pointwiseAppendComputable firstComputer secondComputer

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalDynamicCatalogueComputer
    (width : SourceQaryMaskDynamicGridWidth)
    {record : List Bool → List Bool}
    (computer : BitTM record) :
    BitTM
      (maskDynamicGridRecordCatalogueOutput width computer) :=
  maskDynamicGridRecordCatalogueComputable width computer

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalDynamicWidth
    {output : List Bool → List Bool}
    (computer : BitTM output) :
    SourceQaryMaskDynamicGridWidth where
  output := output
  computer := computer

@[simp] theorem factor400BinaryIrreduciblePhysicalDynamicWidth_output
    {output : List Bool → List Bool}
    (computer : BitTM output)
    (input : List Bool) :
    (factor400BinaryIrreduciblePhysicalDynamicWidth computer).output input =
      output input := by
  unfold factor400BinaryIrreduciblePhysicalDynamicWidth
  rfl

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalFalseComputer :
    BitTM
      (fun _ : List Bool => [false]) :=
  sourceFixedWordComputable [false]

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalTrueComputer :
    BitTM
      (fun _ : List Bool => [true]) :=
  sourceFixedWordComputable [true]

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalNaturalWriterComputer :
    BitTM
      (fun input : List Bool => Computability.encodeNat input.length) :=
  factor400BinaryPhysicalWordNaturalWriterComputer

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalDropHeadComputer :
    BitTM List.tail :=
  factor400BinaryPhysicalWordDropHeadComputer

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalFieldContentsComputer :
    BitTM
      firstFieldContents :=
  firstFieldContentsComputable

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalFieldSuffixComputer :
    BitTM
      firstFieldSuffix :=
  firstFieldSuffixComputable

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalPrefixWriterComputer :
    BitTM
      lengthPrefixedWord :=
  structuralPrefixWriterComputable

/-- GapCVP reduction support. -/
def binaryIrreduciblePhysicalComputedPrefixOutput
    (word : List Bool → List Bool) : List Bool → List Bool :=
  lengthPrefixedWord ∘ word

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalComputedPrefixComputer
    {word : List Bool → List Bool}
    (computer : BitTM word) :
    BitTM
      (binaryIrreduciblePhysicalComputedPrefixOutput word) :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    (f := word) (g := lengthPrefixedWord)
    computer factor400BinaryIrreduciblePhysicalPrefixWriterComputer

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalSquareComputer :
    BitTM
      (fun input : List Bool =>
        List.replicate ((Polynomial.X ^ 2).eval input.length) true) :=
  polynomialValueUnaryComputable (Polynomial.X ^ 2)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalConvolutionComputer :
    BitTM
      binarySourceRawConvolutionWord :=
  factor400BinarySourceRawConvolutionComputable

/-- GapCVP reduction support. -/
def factor400BinaryIrreducibleRankUnary
    (input : List Bool) : List Bool :=
  firstFieldContents input

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreducibleRankUnaryComputable :
    BitTM
      factor400BinaryIrreducibleRankUnary :=
  factor400BinaryIrreduciblePhysicalFieldContentsComputer

/-- GapCVP reduction support. -/
def binaryIrreducibleRankOriginal :
    List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreducibleRankOriginalComputable :
    BitTM
      binaryIrreducibleRankOriginal :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    (f := firstFieldSuffix) (g := firstFieldSuffix)
    factor400BinaryIrreduciblePhysicalFieldSuffixComputer
    factor400BinaryIrreduciblePhysicalFieldSuffixComputer

theorem factor400BinaryIrreducibleRankOriginal_valid
    (rank auxiliary source : List Bool) :
    binaryIrreducibleRankOriginal
      (lengthPrefixedWord rank ++
        lengthPrefixedWord auxiliary ++ source) = source := by
  simp only [binaryIrreducibleRankOriginal, List.append_assoc, Function.comp_apply,
      firstFieldSuffix_valid]

/-- GapCVP reduction support. -/
def binaryIrreducibleRankBinary :
    List Bool → List Bool :=
  (fun input : List Bool => Computability.encodeNat input.length) ∘
    factor400BinaryIrreducibleRankUnary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreducibleRankBinaryComputable :
    BitTM
      binaryIrreducibleRankBinary :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    (f := factor400BinaryIrreducibleRankUnary)
    (g := fun input : List Bool => Computability.encodeNat input.length)
    factor400BinaryIrreducibleRankUnaryComputable
    factor400BinaryIrreduciblePhysicalNaturalWriterComputer

/-- GapCVP reduction support. -/
def binaryIrreducibleCoefficientOuterSource :
    List Bool → List Bool :=
  binaryIrreducibleRankOriginal

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreducibleCoefficientOuterSourceComputable :
    BitTM
      binaryIrreducibleCoefficientOuterSource :=
  factor400BinaryIrreducibleRankOriginalComputable

/-- GapCVP reduction support. -/
def factor400BinaryIrreducibleCoefficientRankBinary :
    List Bool → List Bool :=
  binaryIrreducibleRankBinary ∘
    binaryIrreducibleCoefficientOuterSource

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreducibleCoefficientRankBinaryComputable :
    BitTM
      factor400BinaryIrreducibleCoefficientRankBinary :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    (f := binaryIrreducibleCoefficientOuterSource)
    (g := binaryIrreducibleRankBinary)
    factor400BinaryIrreducibleCoefficientOuterSourceComputable
    factor400BinaryIrreducibleRankBinaryComputable

/-- GapCVP reduction support. -/
def binaryIrreducibleCoefficientBitWord :
    List Bool → List Bool :=
  fiveFamilyOriginalDynamicBitWord
    factor400BinaryIrreducibleRankUnary
    factor400BinaryIrreducibleCoefficientRankBinary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreducibleCoefficientBitComputable :
    BitTM
      binaryIrreducibleCoefficientBitWord :=
  fiveOriginalDynamicBitComputable
    factor400BinaryIrreducibleRankUnaryComputable
    factor400BinaryIrreducibleCoefficientRankBinaryComputable

private theorem factor400Irreducible_encodePosNum_eq_bits (value : PosNum) :
    Computability.encodePosNum value = Nat.bits (value : ℕ) := by
  induction value with
  | one => rfl
  | bit0 value ih =>
      change false :: Computability.encodePosNum value =
        Nat.bits ((value : ℕ) + (value : ℕ))
      rw [← two_mul, Nat.bit0_bits]
      · exact congrArg (List.cons false) ih
      · exact Nat.ne_of_gt (PosNum.cast_pos value)
  | bit1 value ih =>
      change true :: Computability.encodePosNum value =
        Nat.bits ((value : ℕ) + (value : ℕ) + 1)
      rw [← two_mul, Nat.bit1_bits]
      exact congrArg (List.cons true) ih

private theorem factor400Irreducible_encodeNat_eq_bits (value : ℕ) :
    Computability.encodeNat value = Nat.bits value := by
  change Computability.encodeNum (value : Num) = Nat.bits value
  generalize hnum : (value : Num) = numeral
  have hvalue : (numeral : ℕ) = value := by
    rw [← hnum]
    exact Num.to_of_nat value
  cases numeral with
  | zero =>
      have hz : value = 0 := by simpa only [Num.cast_zero'] using hvalue.symm
      subst value
      rfl
  | pos positive =>
      change Computability.encodePosNum positive = Nat.bits value
      rw [← hvalue]
      exact factor400Irreducible_encodePosNum_eq_bits positive

theorem factor400Irreducible_encodeNat_drop_head
    (value index : ℕ) :
    ((Computability.encodeNat value).drop index).headD false =
      value.testBit index := by
  rw [factor400Irreducible_encodeNat_eq_bits,
    Nat.testBit_eq_inth, List.getI_eq_getElem?_getD]
  simp only [List.headD_eq_head?_getD, List.head?_drop, Bool.default_bool]

theorem factor400BinaryIrreducibleFiniteWordBits_indexedWord
    (degree : ℕ) (rank : Fin (2 ^ degree)) :
    finiteWordBits (indexedWord degree rank) =
      (List.range degree).map
        (fun bitRank => rank.val.testBit bitRank) := by
  apply List.ext_getElem
  · simp only [finiteWordBits, List.length_map, List.length_finRange, List.length_range]
  · intro bitRank hleft hright
    simp only [finiteWordBits, List.getElem_map, indexedWord, List.getElem_finRange, Fin.cast_mk,
        List.getElem_range]

/-- GapCVP reduction support. -/
def binaryIndexedNoProperFactorsBit
    (degree rank : ℕ) : Bool :=
  if h : rank < 2 ^ degree then
    GapCVP.Core.EffectiveBinaryField.noProperFactors degree
      (indexedWord degree ⟨rank, h⟩)
  else
    false

/-- GapCVP reduction support. -/
def binarySourceIrreducibleFactorPairCandidateSource :
    List Bool → List Bool :=
  factor400BinarySourceSkipFields 2

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinarySourceIrreducibleFactorPairCandidateSourceComputable :
    BitTM
      binarySourceIrreducibleFactorPairCandidateSource :=
  binarySourceSkipFieldsComputable 2

/-- GapCVP reduction support. -/
def factor400BinarySourceIrreducibleFactorPairOriginalSource :
    List Bool → List Bool :=
  binaryIrreducibleRankOriginal ∘
    binarySourceIrreducibleFactorPairCandidateSource

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinarySourceIrreducibleFactorPairOriginalSourceComputable :
    BitTM
      factor400BinarySourceIrreducibleFactorPairOriginalSource :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    factor400BinarySourceIrreducibleFactorPairCandidateSourceComputable
    factor400BinaryIrreducibleRankOriginalComputable

/-- GapCVP reduction support. -/
def binaryIndexedIrreducibleCandidateMarkers
    (degree : ℕ) : List Bool :=
  (List.range (2 ^ degree)).map
    (binaryIndexedNoProperFactorsBit degree)

end BinarySelectedIrreducibleWordTM

namespace BinarySelectedIrreducibleFactorCorrectness

open Turing GapCVP.BinaryFieldBasis
open GapCVP.BinaryAllWordRankOrder GapCVP.Core.EffectiveBinaryField

/-- GapCVP reduction support. -/
def binaryIndexedProperFactorPairBit
    (degree : ℕ) (lower : Word degree) (rank : ℕ) : Bool :=
  if h : rank < (2 ^ degree) ^ 2 then
    have hq : 0 < 2 ^ degree := by positivity
    let first : Fin (2 ^ degree) :=
      ⟨rank / (2 ^ degree), by
        apply (Nat.div_lt_iff_lt_mul hq).2
        simpa only [pow_two] using h⟩
    let second : Fin (2 ^ degree) :=
      ⟨rank % (2 ^ degree), Nat.mod_lt rank hq⟩
    decide
      (multiplyWords (indexedWord degree first)
        (indexedWord degree second) = monicWord lower)
  else
    false

private theorem factor400BinaryIndexedWord_surjective
    (degree : ℕ) (word : Word degree) :
    ∃ rank : Fin (2 ^ degree), indexedWord degree rank = word := by
  have hword := GapCVP.Core.EffectiveBinaryField.mem_allWords word
  rw [allWords_eq_finRange_indexedWord degree] at hword
  obtain ⟨rank, _, hrank⟩ := List.mem_map.mp hword
  exact ⟨rank, hrank⟩

private theorem factor400BinaryProperFactorPairRank_lt
    {degree : ℕ}
    (first second : Fin (2 ^ degree)) :
    first.val * 2 ^ degree + second.val < (2 ^ degree) ^ 2 := by
  calc
    first.val * 2 ^ degree + second.val <
        first.val * 2 ^ degree + 2 ^ degree :=
      Nat.add_lt_add_left second.isLt _
    _ = (first.val + 1) * 2 ^ degree := by
      simp only [Nat.add_mul, one_mul]
    _ ≤ (2 ^ degree) * (2 ^ degree) :=
      Nat.mul_le_mul_right (2 ^ degree)
        (Nat.succ_le_of_lt first.isLt)
    _ = (2 ^ degree) ^ 2 := by
      rw [pow_two]

private theorem factor400BinaryProperFactorPairRank_div
    {degree : ℕ}
    (first second : Fin (2 ^ degree)) :
    (first.val * 2 ^ degree + second.val) / (2 ^ degree) = first.val := by
  have hq : 0 < 2 ^ degree := by positivity
  rw [Nat.mul_comm first.val (2 ^ degree),
    Nat.mul_add_div hq, Nat.div_eq_of_lt second.isLt]
  simp only [add_zero]

private theorem factor400BinaryProperFactorPairRank_mod
    {degree : ℕ}
    (first second : Fin (2 ^ degree)) :
    (first.val * 2 ^ degree + second.val) % (2 ^ degree) = second.val := by
  rw [Nat.mul_add_mod' first.val (2 ^ degree) second.val,
    Nat.mod_eq_of_lt second.isLt]

private theorem factor400BinaryIndexedProperFactorPairBit_rank
    {degree : ℕ} (lower : Word degree)
    (first second : Fin (2 ^ degree)) :
    binaryIndexedProperFactorPairBit degree lower
        (first.val * 2 ^ degree + second.val) =
      decide
        (multiplyWords
          (indexedWord degree first)
          (indexedWord degree second) = monicWord lower) := by
  unfold binaryIndexedProperFactorPairBit
  rw [dite_eq_left (factor400BinaryProperFactorPairRank_lt first second)]
  dsimp
  simp only [factor400BinaryProperFactorPairRank_div first second,
    factor400BinaryProperFactorPairRank_mod first second, Fin.eta]

theorem factor400BinaryIndexedProperFactorPairMarkers_find_none_iff
    (degree : ℕ) (lower : Word degree) :
    ((List.range ((2 ^ degree) ^ 2)).map
        (binaryIndexedProperFactorPairBit degree lower)).findIdx?
          id = none ↔
      ∀ first second : Word degree,
        multiplyWords first second ≠ monicWord lower := by
  constructor
  · intro hnone first second
    obtain ⟨firstRank, hfirst⟩ :=
      factor400BinaryIndexedWord_surjective degree first
    obtain ⟨secondRank, hsecond⟩ :=
      factor400BinaryIndexedWord_surjective degree second
    let rank := firstRank.val * 2 ^ degree + secondRank.val
    have hbound : rank < (2 ^ degree) ^ 2 :=
      factor400BinaryProperFactorPairRank_lt firstRank secondRank
    have hmember :
        binaryIndexedProperFactorPairBit degree lower rank ∈
          (List.range ((2 ^ degree) ^ 2)).map
            (binaryIndexedProperFactorPairBit degree lower) :=
      List.mem_map.mpr
        ⟨rank, List.mem_range.mpr hbound, rfl⟩
    have hfalse := (List.findIdx?_eq_none_iff.mp hnone)
      (binaryIndexedProperFactorPairBit degree lower rank) hmember
    change
      binaryIndexedProperFactorPairBit degree lower rank = false
        at hfalse
    dsimp [rank] at hfalse
    rw [factor400BinaryIndexedProperFactorPairBit_rank] at hfalse
    rw [hfirst, hsecond] at hfalse
    exact of_decide_eq_false hfalse
  · intro hnone
    apply List.findIdx?_eq_none_iff.mpr
    intro marker hmember
    obtain ⟨rank, hrank, hmarker⟩ := List.mem_map.mp hmember
    subst marker
    have hbound : rank < (2 ^ degree) ^ 2 :=
      List.mem_range.mp hrank
    unfold binaryIndexedProperFactorPairBit
    rw [dite_eq_left hbound]
    dsimp
    exact decide_eq_false (hnone _ _)

end BinarySelectedIrreducibleFactorCorrectness


end GapCVP

end
