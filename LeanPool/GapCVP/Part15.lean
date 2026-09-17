/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part14

/-! # GapCVP proof, part 15 -/

noncomputable section

open StateTransition (EvalsToInTime)
open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace PhysicalInterpolationDirectMomentBitTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalGlobalRefinementCoefficientTM GapCVP.SourceFieldMomentOperationsTM
open GapCVP.PhysicalMatrixCellTM

private def physicalInterpolationRowGridRankWord
    (family : Fin 4) : List Bool → List Bool :=
  sourcePhysicalComputedUnaryRemainder
    (physicalFamilyRowFieldRankWord family)
    physicalMomentCellGridCardinalityUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationRowGridRankWordComputable
    (family : Fin 4) :
    BitTM
      (physicalInterpolationRowGridRankWord family) :=
  sourcePhysicalComputedUnaryRemainderComputable
    (paperVariableArityPhysicalFamilyRowFieldRankComputable family)
    paperVariableArityPhysicalMomentCellGridCardinalityUnaryComputable

@[simp] private theorem paperVariableArityPhysicalInterpolationRowGridRankWord_valid
    (family : Fin 4) (row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationRowGridRankWord family
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (((row - physicalFamilyStart family formula) /
          physDegree formula) %
          physGridCard formula) true := by
  exact sourcePhysicalComputedUnaryRemainder_valid
    (physicalFamilyRowFieldRankWord family)
    physicalMomentCellGridCardinalityUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    ((row - physicalFamilyStart family formula) /
      physDegree formula)
    (physGridCard formula)
    (physicalCoefficientGridCardinality_pos formula)
    (paperVariableArityPhysicalFamilyRowFieldRankWord_valid
      family row column formula)
    (paperVariableArityPhysicalMomentCellGridCardinalityUnary_valid
      row column formula)

private def physicalInterpolationDirectGridMatchBit
    (family : Fin 4) : List Bool → List Bool :=
  physicalCoefficientUnaryEquality
    (physicalInterpolationRowGridRankWord family)
    physicalColumnGridRankUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationDirectGridMatchBitComputable
    (family : Fin 4) :
    BitTM
      (physicalInterpolationDirectGridMatchBit family) :=
  paperVariableArityPhysicalCoefficientUnaryEqualityComputable
    (paperVariableArityPhysicalInterpolationRowGridRankWordComputable family)
    physicalColumnGridRankUnaryComputable

@[simp] theorem
    paperVariableArityPhysicalInterpolationDirectGridMatchBit_valid
    (family : Fin 4) (row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationDirectGridMatchBit family
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      [decide
        ((((row - physicalFamilyStart family formula) /
          physDegree formula) %
          physGridCard formula) =
        ((column / physFieldCard formula) %
          physGridCard formula))] := by
  exact physicalCoefficientUnaryEquality_valid
    (physicalInterpolationRowGridRankWord family)
    physicalColumnGridRankUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    (((row - physicalFamilyStart family formula) /
      physDegree formula) %
      physGridCard formula)
    ((column / physFieldCard formula) %
      physGridCard formula)
    (paperVariableArityPhysicalInterpolationRowGridRankWord_valid
      family row column formula)
    (paperVariableArityPhysicalColumnGridRankUnary_query
      row column formula)

/-- GapCVP reduction support. -/
def physicalFamilyDirectMomentBit
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    (physicalInterpolationDirectGridMatchBit family)
    (physicalMatrixCoefficientBit
      physicalMatrixSelectedBasisRankComputer
      (physicalFamilyMomentPowerComputer family base))

private noncomputable def paperVariableArityPhysicalFamilyDirectMomentBitComputable
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalFamilyDirectMomentBit family base) :=
  fourFamilyBooleanAndComputable
    (paperVariableArityPhysicalInterpolationDirectGridMatchBitComputable family)
    (paperVariableArityPhysicalMatrixCoefficientBitComputable
      physicalMatrixSelectedBasisRankComputer
      (physicalFamilyMomentPowerComputer family base))

private theorem paperVariableArityPhysicalFamilyMomentPowerComputer_output
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer) :
    (physicalFamilyMomentPowerComputer family base).output =
      physicalFamilyMomentPowerWord family base := by
  dsimp only [physicalFamilyMomentPowerComputer]

private theorem paperVariableArityPhysicalFamilyMomentPowerComputer_valid
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula))
    (hvalue : base.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits value) :
    (physicalFamilyMomentPowerComputer family base).output
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      finiteWordBits
        (sourceWordPow value
          (physicalFamilyRowMoment family row formula)) := by
  rw [paperVariableArityPhysicalFamilyMomentPowerComputer_output]
  exact paperVariableArityPhysicalFamilyMomentPowerWord_valid
    family base row column formula value hvalue

private theorem paperVariableArityPhysicalFamilyMomentBasisBit_valid
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula))
    (index : Fin (physDegree formula))
    (hindex : index.val =
      row % physDegree formula)
    (hvalue : base.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits value) :
    physicalMatrixCoefficientBit
        physicalMatrixSelectedBasisRankComputer
        (physicalFamilyMomentPowerComputer family base)
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [(sourceWordPow value
        (physicalFamilyRowMoment family row formula))
          index] := by
  apply paperVariableArityPhysicalMatrixCoefficientBit_valid
    physicalMatrixSelectedBasisRankComputer
    (physicalFamilyMomentPowerComputer family base)
    row column formula
    (sourceWordPow value
      (physicalFamilyRowMoment family row formula))
    index.val index.isLt
  · rw [hindex]
    exact paperVariableArityPhysicalMatrixSelectedBasisRankComputer_query
      row column formula
  · exact paperVariableArityPhysicalFamilyMomentPowerComputer_valid
      family base row column formula value hvalue

theorem paperVariableArityPhysicalFamilyDirectMomentBit_valid
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula))
    (index : Fin (physDegree formula))
    (hindex : index.val =
      row % physDegree formula)
    (hvalue : base.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits value) :
    physicalFamilyDirectMomentBit family base
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      [decide
        ((((row - physicalFamilyStart family formula) /
          physDegree formula) %
          physGridCard formula) =
        ((column / physFieldCard formula) %
          physGridCard formula)) &&
        (sourceWordPow value
          (physicalFamilyRowMoment family row formula))
          index] := by
  let query := affineCellQuery row column
    (encodeThreeCNF formula)
  exact fourFamilyBooleanAndOutput_bits
    (physicalInterpolationDirectGridMatchBit family)
    (physicalMatrixCoefficientBit
      physicalMatrixSelectedBasisRankComputer
      (physicalFamilyMomentPowerComputer family base))
    query
    (decide
      ((((row - physicalFamilyStart family formula) /
        physDegree formula) %
        physGridCard formula) =
      ((column / physFieldCard formula) %
        physGridCard formula)))
    ((sourceWordPow value
      (physicalFamilyRowMoment family row formula))
        index)
    (paperVariableArityPhysicalInterpolationDirectGridMatchBit_valid
      family row column formula)
    (paperVariableArityPhysicalFamilyMomentBasisBit_valid
      family base row column formula value index hindex hvalue)

end PhysicalInterpolationDirectMomentBitTM

namespace PhysicalMaskedInterpolationNodeParityTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalFieldCoefficientBitTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalGlobalRefinementCoefficientTM
open GapCVP.PhysicalMatrixCellTM GapCVP.SourceFieldMomentOperationsTM
open GapCVP.PhysicalOrdinaryShiftedCoefficientSumTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

private def physicalInterpolationOuterColumnGridRank :
    List Bool → List Bool :=
  physicalColumnGridRankUnary ∘
    compactPhysicalLagrangeNestedNodeOuterCell

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationOuterColumnGridRankComputable :
    BitTM
      physicalInterpolationOuterColumnGridRank :=
  GapCVP.TMComposition.computableInPolyTime
    compactPhysicalLagrangeNestedNodeOuterCellComputable
    physicalColumnGridRankUnaryComputable

private def physicalInterpolationNodeColumnGridMask :
    List Bool → List Bool :=
  physicalCoefficientUnaryEquality
    compactPhysicalLagrangeNestedNodeRank
    physicalInterpolationOuterColumnGridRank

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNodeColumnGridMaskComputable :
    BitTM
      physicalInterpolationNodeColumnGridMask :=
  paperVariableArityPhysicalCoefficientUnaryEqualityComputable
    compactPhysicalLagrangeNestedNodeRankComputable
    paperVariableArityPhysicalInterpolationOuterColumnGridRankComputable

private theorem paperVariableArityPhysicalInterpolationNodeColumnGridMask_valid
    (width : SourceQaryMaskDynamicGridWidth)
    (node row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationNodeColumnGridMask
        (compactPhysicalLagrangeNestedNodeEnvelope width node
          (affineCellQuery row column
            (encodeThreeCNF formula))) =
      [decide
        (node =
          ((column / physFieldCard formula) %
            physGridCard formula))] := by
  apply physicalCoefficientUnaryEquality_valid
    compactPhysicalLagrangeNestedNodeRank
    physicalInterpolationOuterColumnGridRank
    (compactPhysicalLagrangeNestedNodeEnvelope width node
      (affineCellQuery row column
        (encodeThreeCNF formula)))
    node
    ((column / physFieldCard formula) %
      physGridCard formula)
  · exact compactPhysicalLagrangeNestedNodeRank_query width node
      (affineCellQuery row column
        (encodeThreeCNF formula))
  · unfold physicalInterpolationOuterColumnGridRank
    rw [Function.comp_apply,
      compactPhysicalLagrangeNestedNodeOuterCell_query]
    exact paperVariableArityPhysicalColumnGridRankUnary_query
      row column formula

private def physicalInterpolationNestedBasisRankWord :
    List Bool → List Bool :=
  (physicalMatrixBasisRankComputer
    physicalMatrixFieldDegreeComputer).output ∘
    compactPhysicalLagrangeNestedNodeOuterCell

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedBasisRankWordComputable :
    BitTM
      physicalInterpolationNestedBasisRankWord :=
  GapCVP.TMComposition.computableInPolyTime
    compactPhysicalLagrangeNestedNodeOuterCellComputable
    (physicalMatrixBasisRankComputer
      physicalMatrixFieldDegreeComputer).computer

private noncomputable def paperVariableArityPhysicalInterpolationNestedBasisRankComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationNestedBasisRankWord
  computer :=
    paperVariableArityPhysicalInterpolationNestedBasisRankWordComputable

private theorem paperVariableArityPhysicalInterpolationNestedBasisRankWord_valid
    (width : SourceQaryMaskDynamicGridWidth)
    (node row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationNestedBasisRankWord
        (compactPhysicalLagrangeNestedNodeEnvelope width node
          (affineCellQuery row column
            (encodeThreeCNF formula))) =
      List.replicate
        (row % physDegree formula) true := by
  unfold physicalInterpolationNestedBasisRankWord
  rw [Function.comp_apply,
    compactPhysicalLagrangeNestedNodeOuterCell_query]
  exact paperVariableArityPhysicalMatrixBasisRankComputer_query
    physicalMatrixFieldDegreeComputer
    row column formula
    (physDegree formula)
    (GapCVP.Core.sourceFieldExponent_pos
      (GapCVP.Core.sourceSizeParameter_ge_one_hundred
        (encodeThreeCNF formula).length
        (srcFormula formula)))
    (paperVariableArityPhysicalMatrixFieldDegreeComputer_query
      row column formula)

/-- GapCVP reduction support. -/
def physicalInterpolationRowBasisIndex
    (row : ℕ) (formula : ThreeCNF) :
    Fin (physDegree formula) :=
  ⟨row % physDegree formula,
    Nat.mod_lt _
      (GapCVP.Core.sourceFieldExponent_pos
        (GapCVP.Core.sourceSizeParameter_ge_one_hundred
          (encodeThreeCNF formula).length
          (srcFormula formula)))⟩

private def physicalInterpolationNodeWeightBasisBit
    (weight : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  compactPhysicalFieldCoefficientPreparedBit
    paperVariableArityPhysicalInterpolationNestedBasisRankComputer
    weight compactPhysicalLagrangeNestedNodeSourceWordComputer

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNodeWeightBasisBitComputable
    (weight : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalInterpolationNodeWeightBasisBit weight) :=
  compactPhysicalFieldCoefficientPreparedBitComputable
    paperVariableArityPhysicalInterpolationNestedBasisRankComputer
    weight compactPhysicalLagrangeNestedNodeSourceWordComputer

private theorem paperVariableArityPhysicalInterpolationNodeWeightBasisBit_valid
    (weight : SourcePhysicalLagrangeWordComputer)
    (width : SourceQaryMaskDynamicGridWidth)
    (node row column : ℕ) (formula : ThreeCNF)
    (word : GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula))
    (correctWeight :
      weight.output
        (compactPhysicalLagrangeNestedNodeEnvelope width node
          (affineCellQuery row column
            (encodeThreeCNF formula))) = finiteWordBits word) :
    physicalInterpolationNodeWeightBasisBit weight
        (compactPhysicalLagrangeNestedNodeEnvelope width node
          (affineCellQuery row column
            (encodeThreeCNF formula))) =
      [word (physicalInterpolationRowBasisIndex
        row formula)] := by
  unfold physicalInterpolationNodeWeightBasisBit
  apply compactPhysicalFieldCoefficientPreparedBit_bounded_valid
    paperVariableArityPhysicalInterpolationNestedBasisRankComputer
    weight compactPhysicalLagrangeNestedNodeSourceWordComputer
    (compactPhysicalLagrangeNestedNodeEnvelope width node
      (affineCellQuery row column
        (encodeThreeCNF formula)))
    formula word
    (row % physDegree formula)
    (physicalInterpolationRowBasisIndex row formula).isLt
  · exact paperVariableArityPhysicalInterpolationNestedBasisRankWord_valid
      width node row column formula
  · exact correctWeight
  · exact compactPhysicalLagrangeNestedNodeOriginalSource_query
      width node row column formula

private def physicalMaskedNodeInterpolationBit
    (weight : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    physicalInterpolationNodeColumnGridMask
    (physicalInterpolationNodeWeightBasisBit weight)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalMaskedNodeInterpolationBitComputable
    (weight : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalMaskedNodeInterpolationBit weight) :=
  fourFamilyBooleanAndComputable
    paperVariableArityPhysicalInterpolationNodeColumnGridMaskComputable
    (paperVariableArityPhysicalInterpolationNodeWeightBasisBitComputable
      weight)

private theorem paperVariableArityPhysicalMaskedNodeInterpolationBit_valid
    (weight : SourcePhysicalLagrangeWordComputer)
    (width : SourceQaryMaskDynamicGridWidth)
    (node row column : ℕ) (formula : ThreeCNF)
    (word : GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula))
    (correctWeight :
      weight.output
        (compactPhysicalLagrangeNestedNodeEnvelope width node
          (affineCellQuery row column
            (encodeThreeCNF formula))) = finiteWordBits word) :
    physicalMaskedNodeInterpolationBit weight
        (compactPhysicalLagrangeNestedNodeEnvelope width node
          (affineCellQuery row column
            (encodeThreeCNF formula))) =
      [decide
        (node =
          ((column / physFieldCard formula) %
            physGridCard formula)) &&
        word (physicalInterpolationRowBasisIndex
          row formula)] := by
  unfold physicalMaskedNodeInterpolationBit
  exact fourFamilyBooleanAndOutput_bits
    physicalInterpolationNodeColumnGridMask
    (physicalInterpolationNodeWeightBasisBit weight)
    (compactPhysicalLagrangeNestedNodeEnvelope width node
      (affineCellQuery row column
        (encodeThreeCNF formula)))
    (decide
      (node =
        ((column / physFieldCard formula) %
          physGridCard formula)))
    (word (physicalInterpolationRowBasisIndex
      row formula))
    (paperVariableArityPhysicalInterpolationNodeColumnGridMask_valid
      width node row column formula)
    (paperVariableArityPhysicalInterpolationNodeWeightBasisBit_valid
      weight width node row column formula word correctWeight)

/-- GapCVP reduction support. -/
noncomputable def physicalOrdinaryInterpolationMomentComputer :
    SourcePhysicalLagrangeWordComputer :=
  physicalFamilyRowMomentRankComputer (2 : Fin 4)

/-- GapCVP reduction support. -/
noncomputable def physicalShiftedInterpolationMomentComputer :
    SourcePhysicalLagrangeWordComputer :=
  physicalFamilyRowMomentRankComputer (3 : Fin 4)

/-- GapCVP reduction support. -/
def physicalOrdinaryInterpolationNodeCount
    (row : ℕ) (formula : ThreeCNF) : ℕ :=
  physicalFormulaVariableCount formula *
    physicalFamilyRowMoment (2 : Fin 4) row formula + 1

/-- GapCVP reduction support. -/
def physicalShiftedInterpolationNodeCount
    (row : ℕ) (formula : ThreeCNF) : ℕ :=
  (physicalFormulaVariableCount formula - 1) *
    physicalFamilyRowMoment (3 : Fin 4) row formula + 1

private def physicalMaskedInterpolationNodeValue
    (row column : ℕ) (formula : ThreeCNF)
    (word : ℕ → GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula))
    (node : ℕ) : Bool :=
  decide
    (node =
      ((column / physFieldCard formula) %
        physGridCard formula)) &&
    word node
      (physicalInterpolationRowBasisIndex row formula)

private theorem paperVariableArityPhysicalOrdinaryInterpolationMomentComputer_output :
    physicalOrdinaryInterpolationMomentComputer.output =
      physicalFamilyRowMomentRankWord (2 : Fin 4) := by
  dsimp only [physicalOrdinaryInterpolationMomentComputer,
    physicalFamilyRowMomentRankComputer]

private theorem paperVariableArityPhysicalOrdinaryInterpolationMomentComputer_valid
    (row column : ℕ) (formula : ThreeCNF) :
    physicalOrdinaryInterpolationMomentComputer.output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalFamilyRowMoment (2 : Fin 4)
          row formula) true := by
  rw [paperVariableArityPhysicalOrdinaryInterpolationMomentComputer_output]
  exact paperVariableArityPhysicalFamilyRowMomentRankWord_valid
    (2 : Fin 4) row column formula

private theorem paperVariableArityPhysicalShiftedInterpolationMomentComputer_output :
    physicalShiftedInterpolationMomentComputer.output =
      physicalFamilyRowMomentRankWord (3 : Fin 4) := by
  dsimp only [physicalShiftedInterpolationMomentComputer,
    physicalFamilyRowMomentRankComputer]

private theorem paperVariableArityPhysicalShiftedInterpolationMomentComputer_valid
    (row column : ℕ) (formula : ThreeCNF) :
    physicalShiftedInterpolationMomentComputer.output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalFamilyRowMoment (3 : Fin 4)
          row formula) true := by
  rw [paperVariableArityPhysicalShiftedInterpolationMomentComputer_output]
  exact paperVariableArityPhysicalFamilyRowMomentRankWord_valid
    (3 : Fin 4) row column formula

private theorem paperVariableArityPhysicalOrdinaryInterpolationNodeWidth_output :
    (physicalOrdinaryNodePrefixWidth
      physicalOrdinaryInterpolationMomentComputer).output =
      physicalOrdinaryNodePrefixWord
        physicalOrdinaryInterpolationMomentComputer := by
  dsimp only [physicalOrdinaryNodePrefixWidth]

theorem paperVariableArityPhysicalOrdinaryInterpolationNodeWidth_valid
    (row column : ℕ) (formula : ThreeCNF) :
    (physicalOrdinaryNodePrefixWidth
      physicalOrdinaryInterpolationMomentComputer).output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalOrdinaryInterpolationNodeCount
          row formula) true := by
  rw [paperVariableArityPhysicalOrdinaryInterpolationNodeWidth_output]
  exact paperVariableArityPhysicalOrdinaryNodePrefixWord_valid
    physicalOrdinaryInterpolationMomentComputer
    row column formula
    (physicalFamilyRowMoment (2 : Fin 4) row formula)
    (paperVariableArityPhysicalOrdinaryInterpolationMomentComputer_valid
      row column formula)

private theorem paperVariableArityPhysicalShiftedInterpolationNodeWidth_output :
    (physicalShiftedNodePrefixWidth
      physicalShiftedInterpolationMomentComputer).output =
      physicalShiftedNodePrefixWord
        physicalShiftedInterpolationMomentComputer := by
  dsimp only [physicalShiftedNodePrefixWidth]

theorem paperVariableArityPhysicalShiftedInterpolationNodeWidth_valid
    (row column : ℕ) (formula : ThreeCNF) :
    (physicalShiftedNodePrefixWidth
      physicalShiftedInterpolationMomentComputer).output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalShiftedInterpolationNodeCount
          row formula) true := by
  rw [paperVariableArityPhysicalShiftedInterpolationNodeWidth_output]
  exact paperVariableArityPhysicalShiftedNodePrefixWord_valid
    physicalShiftedInterpolationMomentComputer
    row column formula
    (physicalFamilyRowMoment (3 : Fin 4) row formula)
    (paperVariableArityPhysicalShiftedInterpolationMomentComputer_valid
      row column formula)

private theorem paperVariableArityPhysicalMaskedInterpolationParity_valid
    (width : SourceQaryMaskDynamicGridWidth)
    (weight : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) (count : ℕ) (value : ℕ → Bool)
    (hwidth : width.output input = List.replicate count true)
    (hterm : ∀ node ∈ List.range count,
      physicalMaskedNodeInterpolationBit weight
        (compactPhysicalLagrangeNestedNodeEnvelope width node input) =
          [value node]) :
    physicalInterpolationNodeParity width
        (paperVariableArityPhysicalMaskedNodeInterpolationBitComputable
          weight) input =
      [((List.range count).map value).foldl Bool.xor false] := by
  apply paperVariableArityPhysicalInterpolationNodeParity_valid width
    (paperVariableArityPhysicalMaskedNodeInterpolationBitComputable weight)
    input count value hwidth
  intro node member
  change
    physicalMaskedNodeInterpolationBit weight
      (compactPhysicalLagrangeNestedNodeEnvelope width node input) =
        [value node]
  exact hterm node member

end PhysicalMaskedInterpolationNodeParityTM

namespace Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine

open Turing GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldBasis
open GapCVP.BinaryModularReductionTM GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinarySelectedIrreducibleWordTM
open GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCellVariableCountLiftComputable :
    BitTM
      (physicalCellSourceLift
        physicalFamilyVariableCountUnary) :=
  physicalCellSourceLiftComputable
    paperVariableArityPhysicalFamilyVariableCountUnaryComputable

private def physicalCellGridRankWord
    (rank : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  physicalCellSourceLift
      physicalFamilyVariableCountUnary input ++
    rank.output input

private noncomputable def paperVariableArityPhysicalCellGridRankWordComputable
    (rank : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalCellGridRankWord rank) := by
  cases rank with
  | mk rankWord rankComputer =>
      exact factor400BinaryIrreduciblePhysicalAppendComputer
        (first := physicalCellSourceLift
          physicalFamilyVariableCountUnary)
        (second := rankWord)
        paperVariableArityPhysicalCellVariableCountLiftComputable
        rankComputer

private noncomputable def physicalCellGridRankComputer
    (rank : SourcePhysicalLagrangeWordComputer) :
    SourcePhysicalLagrangeWordComputer where
  output := physicalCellGridRankWord rank
  computer := paperVariableArityPhysicalCellGridRankWordComputable rank

private theorem paperVariableArityPhysicalCellGridRankComputer_output
    (rank : SourcePhysicalLagrangeWordComputer) :
    (physicalCellGridRankComputer rank).output =
      physicalCellGridRankWord rank := by
  dsimp only [physicalCellGridRankComputer]

private theorem paperVariableArityPhysicalCellGridRankWord_valid
    (rank : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF) (position : ℕ)
    (hrank : rank.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate position true) :
    physicalCellGridRankWord rank
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        ((srcFormula formula).variableCount + position)
        true := by
  unfold physicalCellGridRankWord
  rw [paperVariableArityPhysicalCellSourceLift_query,
    paperVariableArityPhysicalFamilyVariableCountUnary_valid, hrank]
  exact (List.replicate_add _ _ _).symm

private def physicalCellGridWordAt
    (rank : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  physicalCellFieldWordAt
    (physicalCellGridRankComputer rank)

private noncomputable def paperVariableArityPhysicalCellGridWordAtComputable
    (rank : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalCellGridWordAt rank) :=
  physicalCellFieldWordAtComputable
    (physicalCellGridRankComputer rank)

private theorem paperVariableArityPhysicalCellGridWordAt_valid
    (rank : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (point : Fin
      (2 ^ sourceIrreducibleFormulaDegree formula -
        (srcFormula formula).variableCount))
    (hrank : rank.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate point.val true) :
    physicalCellGridWordAt rank
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      finiteWordBits
        (indexedWord (sourceIrreducibleFormulaDegree formula)
          (evaluationWordIndex
            (variableCount_le_fieldWordCount
              (encodeThreeCNF formula).length
              (srcFormula formula)) point)) := by
  let index := evaluationWordIndex
    (variableCount_le_fieldWordCount
      (encodeThreeCNF formula).length
      (srcFormula formula)) point
  have hindex :
      (physicalCellGridRankComputer rank).output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
        List.replicate index.val true := by
    rw [paperVariableArityPhysicalCellGridRankComputer_output]
    exact paperVariableArityPhysicalCellGridRankWord_valid
      rank row column formula point.val hrank
  exact physicalCellFieldWordAt_valid
    (physicalCellGridRankComputer rank)
    row column formula index hindex

end Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine

namespace PhysicalInterpolationNodeGridMaskTM

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.CLStructuralPrefixWriter GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalCellGridWordTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.FormulaBridge
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine

/-- GapCVP reduction support. -/
abbrev PaperVariableArityPhysicalInterpolationGridIndex
    (formula : ThreeCNF) :=
  Fin (2 ^ sourceIrreducibleFormulaDegree formula -
    (srcFormula formula).variableCount)

private def physicalInterpolationRebuiltGridCell
    (rank source : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (rank.output input) ++
    lengthPrefixedWord [] ++ source.output input

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationRebuiltGridCellComputable
    (rank source : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalInterpolationRebuiltGridCell rank source) := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    rank.computer structuralPrefixWriterComputable
  have hrecords := physicalCellGridAppendComputer
    hprefix (sourceFixedWordComputable (lengthPrefixedWord []))
  have hphysical := physicalCellGridAppendComputer hrecords source.computer
  change BitTM
    (fun input =>
      lengthPrefixedWord (rank.output input) ++
        lengthPrefixedWord [] ++ source.output input)
  simpa only [List.append_assoc, Function.comp_apply] using hphysical

private theorem paperVariableArityPhysicalInterpolationRebuiltGridCell_valid
    (rank source : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) (formula : ThreeCNF) (position : ℕ)
    (hrank : rank.output input = List.replicate position true)
    (hsource : source.output input = encodeThreeCNF formula) :
    physicalInterpolationRebuiltGridCell rank source input =
      affineCellQuery position 0
        (encodeThreeCNF formula) := by
  simp only [physicalInterpolationRebuiltGridCell, hrank, hsource, List.append_assoc,
      affineCellQuery,
      List.replicate_zero]

private noncomputable def paperVariableArityPhysicalInterpolationGridCellRowComputer :
    SourcePhysicalLagrangeWordComputer where
  output := sourceExplicitAffineCellRow
  computer := sourceExplicitAffineCellRowComputable

private def physicalInterpolationRebuiltGridWord
    (rank source : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  physicalCellGridWordAt
      paperVariableArityPhysicalInterpolationGridCellRowComputer ∘
    physicalInterpolationRebuiltGridCell rank source

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationRebuiltGridWordComputable
    (rank source : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalInterpolationRebuiltGridWord rank source) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityPhysicalInterpolationRebuiltGridCellComputable
      rank source)
    (paperVariableArityPhysicalCellGridWordAtComputable
      paperVariableArityPhysicalInterpolationGridCellRowComputer)

private noncomputable def paperVariableArityPhysicalInterpolationRebuiltGridWordComputer
    (rank source : SourcePhysicalLagrangeWordComputer) :
    SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationRebuiltGridWord
    rank source
  computer := paperVariableArityPhysicalInterpolationRebuiltGridWordComputable
    rank source

private theorem paperVariableArityPhysicalInterpolationRebuiltGridWord_valid
    (rank source : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) (formula : ThreeCNF)
    (point : PaperVariableArityPhysicalInterpolationGridIndex formula)
    (hrank : rank.output input = List.replicate point.val true)
    (hsource : source.output input = encodeThreeCNF formula) :
    physicalInterpolationRebuiltGridWord rank source input =
      finiteWordBits
        (indexedWord
          (sourceIrreducibleFormulaDegree formula)
          (evaluationWordIndex
            (variableCount_le_fieldWordCount
              (encodeThreeCNF formula).length
              (srcFormula formula)) point)) := by
  unfold physicalInterpolationRebuiltGridWord
  rw [Function.comp_apply,
    paperVariableArityPhysicalInterpolationRebuiltGridCell_valid
      rank source input formula point.val hrank hsource]
  apply paperVariableArityPhysicalCellGridWordAt_valid
    paperVariableArityPhysicalInterpolationGridCellRowComputer
    point.val 0 formula point
  exact sourceExplicitAffineCellRow_query
    point.val 0 (encodeThreeCNF formula)

private noncomputable def physicalInterpolationNestedOtherGridComputer :
    SourcePhysicalLagrangeWordComputer :=
  paperVariableArityPhysicalInterpolationRebuiltGridWordComputer
    compactPhysicalLagrangeNestedOtherRankWordComputer
    compactPhysicalLagrangeNestedOtherSourceWordComputer

private theorem paperVariableArityPhysicalInterpolationNestedOtherGridComputer_valid
    (innerWidth outerWidth : SourceQaryMaskDynamicGridWidth)
    (row column : ℕ) (formula : ThreeCNF)
    (other node : PaperVariableArityPhysicalInterpolationGridIndex formula) :
    physicalInterpolationNestedOtherGridComputer.output
        (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other.val
          (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
            (affineCellQuery row column
              (encodeThreeCNF formula)))) =
      finiteWordBits
        (indexedWord
          (sourceIrreducibleFormulaDegree formula)
          (evaluationWordIndex
            (variableCount_le_fieldWordCount
              (encodeThreeCNF formula).length
              (srcFormula formula)) other)) := by
  apply paperVariableArityPhysicalInterpolationRebuiltGridWord_valid
    compactPhysicalLagrangeNestedOtherRankWordComputer
    compactPhysicalLagrangeNestedOtherSourceWordComputer
    (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other.val
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
        (affineCellQuery row column
          (encodeThreeCNF formula)))) formula other
  · exact compactPhysicalLagrangeNestedNodeRank_query
      innerWidth other.val
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
        (affineCellQuery row column
          (encodeThreeCNF formula)))
  · exact compactPhysicalLagrangeNestedOtherOriginalSource_query
      innerWidth outerWidth other.val node.val row column formula

private noncomputable def physicalInterpolationNestedAnchorGridComputer :
    SourcePhysicalLagrangeWordComputer :=
  paperVariableArityPhysicalInterpolationRebuiltGridWordComputer
    compactPhysicalLagrangeNestedAnchorRankWordComputer
    compactPhysicalLagrangeNestedOtherSourceWordComputer

private theorem paperVariableArityPhysicalInterpolationNestedAnchorGridComputer_valid
    (innerWidth outerWidth : SourceQaryMaskDynamicGridWidth)
    (row column : ℕ) (formula : ThreeCNF)
    (other node : PaperVariableArityPhysicalInterpolationGridIndex formula) :
    physicalInterpolationNestedAnchorGridComputer.output
        (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other.val
          (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
            (affineCellQuery row column
              (encodeThreeCNF formula)))) =
      finiteWordBits
        (indexedWord
          (sourceIrreducibleFormulaDegree formula)
          (evaluationWordIndex
            (variableCount_le_fieldWordCount
              (encodeThreeCNF formula).length
              (srcFormula formula)) node)) := by
  apply paperVariableArityPhysicalInterpolationRebuiltGridWord_valid
    compactPhysicalLagrangeNestedAnchorRankWordComputer
    compactPhysicalLagrangeNestedOtherSourceWordComputer
    (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other.val
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
        (affineCellQuery row column
          (encodeThreeCNF formula)))) formula node
  · exact compactPhysicalLagrangeNestedAnchorRank_query
      innerWidth outerWidth other.val node.val
      (affineCellQuery row column
        (encodeThreeCNF formula))
  · exact compactPhysicalLagrangeNestedOtherOriginalSource_query
      innerWidth outerWidth other.val node.val row column formula

private def paperVariableArityPhysicalInterpolationNestedOtherSelfMask :
    List Bool → List Bool :=
  fourFamilyComputedUnaryEqBitOutput
    compactPhysicalLagrangeNestedNodeRank
    compactPhysicalLagrangeNestedAnchorRank

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedOtherSelfMaskComputable :
    BitTM
      paperVariableArityPhysicalInterpolationNestedOtherSelfMask :=
  fourFamilyComputedUnaryEqBitComputable
    compactPhysicalLagrangeNestedNodeRankComputable
    compactPhysicalLagrangeNestedAnchorRankComputable

private theorem paperVariableArityPhysicalInterpolationNestedOtherSelfMask_valid
    (innerWidth outerWidth : SourceQaryMaskDynamicGridWidth)
    (other node : ℕ) (cell : List Bool) :
    paperVariableArityPhysicalInterpolationNestedOtherSelfMask
        (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
          (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node cell)) =
      [decide (other = node)] := by
  exact fourFamilyComputedUnaryEqBitOutput_valid
    compactPhysicalLagrangeNestedNodeRank
    compactPhysicalLagrangeNestedAnchorRank
    (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node cell))
    other node
    (compactPhysicalLagrangeNestedNodeRank_query innerWidth other
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node cell))
    (compactPhysicalLagrangeNestedAnchorRank_query
      innerWidth outerWidth other node cell)

private noncomputable def paperVariableArityPhysicalInterpolationFieldOneRankComputer :
    SourcePhysicalLagrangeWordComputer where
  output := fun _ => [true]
  computer := sourceFixedWordComputable [true]

private def physicalInterpolationCellFieldOneWord :
    List Bool → List Bool :=
  physicalCellFieldWordAt
    paperVariableArityPhysicalInterpolationFieldOneRankComputer

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationCellFieldOneWordComputable :
    BitTM
      physicalInterpolationCellFieldOneWord :=
  physicalCellFieldWordAtComputable
    paperVariableArityPhysicalInterpolationFieldOneRankComputer

private theorem paperVariableArityPhysicalInterpolationCellFieldOneWord_valid
    (row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationCellFieldOneWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      finiteWordBits
        (oneWord
          (sourceIrreducibleFormulaDegree formula)) := by
  let degree := sourceIrreducibleFormulaDegree formula
  have positive : 0 < degree :=
    GapCVP.Core.sourceFieldExponent_pos
      (GapCVP.Core.sourceSizeParameter_ge_one_hundred
        (encodeThreeCNF formula).length
        (srcFormula formula))
  let unit : Fin (2 ^ degree) :=
    ⟨1, Nat.one_lt_pow (Nat.ne_of_gt positive) (by norm_num)⟩
  have indexed : indexedWord degree unit = oneWord degree := by
    funext bit
    change Nat.testBit 1 bit.val = decide (bit.val = 0)
    simpa only [Bool.toNat_true, Bool.and_true] using Nat.testBit_bool_toNat true bit.val
  unfold physicalInterpolationCellFieldOneWord
  rw [physicalCellFieldWordAt_valid
    paperVariableArityPhysicalInterpolationFieldOneRankComputer
    row column formula unit (by rfl)]
  exact congrArg finiteWordBits indexed

private def physicalInterpolationNestedOtherFieldOneWord :
    List Bool → List Bool :=
  physicalInterpolationCellFieldOneWord ∘
    compactPhysicalLagrangeNestedOtherActualCell

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedOtherFieldOneWordComputable :
    BitTM
      physicalInterpolationNestedOtherFieldOneWord :=
  GapCVP.TMComposition.computableInPolyTime
    compactPhysicalLagrangeNestedOtherActualCellComputable
    paperVariableArityPhysicalInterpolationCellFieldOneWordComputable

private theorem paperVariableArityPhysicalInterpolationNestedOtherFieldOneWord_valid
    (innerWidth outerWidth : SourceQaryMaskDynamicGridWidth)
    (other node row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationNestedOtherFieldOneWord
        (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
          (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node
            (affineCellQuery row column
              (encodeThreeCNF formula)))) =
      finiteWordBits
        (oneWord
          (sourceIrreducibleFormulaDegree formula)) := by
  unfold physicalInterpolationNestedOtherFieldOneWord
  rw [Function.comp_apply,
    compactPhysicalLagrangeNestedOtherActualCell_query]
  exact paperVariableArityPhysicalInterpolationCellFieldOneWord_valid
    row column formula

end PhysicalInterpolationNodeGridMaskTM

namespace PhysicalInterpolationNodeFactorTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceFourFamilyTaggedPredicateDispatchTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.BinaryCompactPhysicalFieldWordXorTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalRefinementRowProjection
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.SourceFieldMomentOperationsTM GapCVP.PhysicalInterpolationNodeGridMaskTM
open GapCVP.Factor400BinaryConstructiveSourcePlaces

/-- GapCVP reduction support. -/
def physicalInterpolationFamilyRowGridPosition
    (family : Fin 4) (row : ℕ) (formula : ThreeCNF) :
    PaperVariableArityPhysicalInterpolationGridIndex formula :=
  ⟨((row - physicalFamilyStart family formula) /
      physDegree formula) %
      physGridCard formula,
    by
      change
        ((row - physicalFamilyStart family formula) /
          physDegree formula) %
            physGridCard formula <
          physGridCard formula
      exact Nat.mod_lt _
        (physicalRefinementGridCard_pos formula)⟩

private def physicalInterpolationCellRowGridRankWord
    (family : Fin 4) : List Bool → List Bool :=
  sourcePhysicalComputedUnaryRemainder
    (physicalFamilyRowFieldRankWord family)
    physicalMomentCellGridCardinalityUnary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationCellRowGridRankWordComputable
    (family : Fin 4) :
    BitTM
      (physicalInterpolationCellRowGridRankWord family) :=
  sourcePhysicalComputedUnaryRemainderComputable
    (paperVariableArityPhysicalFamilyRowFieldRankComputable family)
    paperVariableArityPhysicalMomentCellGridCardinalityUnaryComputable

@[simp] theorem
    paperVariableArityPhysicalInterpolationCellRowGridRankWord_valid
    (family : Fin 4) (row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationCellRowGridRankWord family
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalInterpolationFamilyRowGridPosition
          family row formula).val true := by
  unfold physicalInterpolationCellRowGridRankWord
  exact sourcePhysicalComputedUnaryRemainder_valid
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

private def physicalInterpolationNestedRowGridRankWord
    (family : Fin 4) : List Bool → List Bool :=
  physicalInterpolationCellRowGridRankWord family ∘
    compactPhysicalLagrangeNestedOtherActualCell

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedRowGridRankWordComputable
    (family : Fin 4) :
    BitTM
      (physicalInterpolationNestedRowGridRankWord
        family) :=
  GapCVP.TMComposition.computableInPolyTime
    compactPhysicalLagrangeNestedOtherActualCellComputable
    (paperVariableArityPhysicalInterpolationCellRowGridRankWordComputable
      family)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationNestedRowGridRankComputer
    (family : Fin 4) : SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationNestedRowGridRankWord
    family
  computer :=
    paperVariableArityPhysicalInterpolationNestedRowGridRankWordComputable
      family

@[simp] theorem
    paperVariableArityPhysicalInterpolationNestedRowGridRankWord_valid
    (family : Fin 4)
    (innerWidth outerWidth : SourceQaryMaskDynamicGridWidth)
    (other node row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationNestedRowGridRankWord family
        (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
          (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node
            (affineCellQuery row column
              (encodeThreeCNF formula)))) =
      List.replicate
        (physicalInterpolationFamilyRowGridPosition
          family row formula).val true := by
  unfold physicalInterpolationNestedRowGridRankWord
  rw [Function.comp_apply,
    compactPhysicalLagrangeNestedOtherActualCell_query]
  exact paperVariableArityPhysicalInterpolationCellRowGridRankWord_valid
    family row column formula

private noncomputable def physicalInterpolationNestedRowGridComputer
    (family : Fin 4) : SourcePhysicalLagrangeWordComputer :=
  paperVariableArityPhysicalInterpolationRebuiltGridWordComputer
    (paperVariableArityPhysicalInterpolationNestedRowGridRankComputer family)
    compactPhysicalLagrangeNestedOtherSourceWordComputer

private theorem paperVariableArityPhysicalInterpolationNestedRowGridComputer_valid
    (family : Fin 4)
    (innerWidth outerWidth : SourceQaryMaskDynamicGridWidth)
    (row column : ℕ) (formula : ThreeCNF)
    (other node : PaperVariableArityPhysicalInterpolationGridIndex formula) :
    (physicalInterpolationNestedRowGridComputer
      family).output
        (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other.val
          (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
            (affineCellQuery row column
              (encodeThreeCNF formula)))) =
      finiteWordBits
        (indexedWord
          (sourceIrreducibleFormulaDegree formula)
          (evaluationWordIndex
            (variableCount_le_fieldWordCount
              (encodeThreeCNF formula).length
              (srcFormula formula))
            (physicalInterpolationFamilyRowGridPosition
              family row formula))) := by
  apply paperVariableArityPhysicalInterpolationRebuiltGridWord_valid
    (paperVariableArityPhysicalInterpolationNestedRowGridRankComputer
      family)
    compactPhysicalLagrangeNestedOtherSourceWordComputer
    (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other.val
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
        (affineCellQuery row column
          (encodeThreeCNF formula)))) formula
    (physicalInterpolationFamilyRowGridPosition
      family row formula)
  · exact
      paperVariableArityPhysicalInterpolationNestedRowGridRankWord_valid
        family innerWidth outerWidth other.val node.val row column formula
  · exact compactPhysicalLagrangeNestedOtherOriginalSource_query
      innerWidth outerWidth other.val node.val row column formula

private def physicalInterpolationNestedOtherDegreeWord :
    List Bool → List Bool :=
  physicalFamilyFieldDegreeUnary ∘
    compactPhysicalLagrangeNestedOtherOriginalSource

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedOtherDegreeWordComputable :
    BitTM
      physicalInterpolationNestedOtherDegreeWord :=
  GapCVP.TMComposition.computableInPolyTime
    compactPhysicalLagrangeNestedOtherOriginalSourceComputable
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationNestedOtherDegreeComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationNestedOtherDegreeWord
  computer :=
    paperVariableArityPhysicalInterpolationNestedOtherDegreeWordComputable

@[simp] theorem
    paperVariableArityPhysicalInterpolationNestedOtherDegreeWord_valid
    (innerWidth outerWidth : SourceQaryMaskDynamicGridWidth)
    (other node row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationNestedOtherDegreeWord
        (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
          (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node
            (affineCellQuery row column
              (encodeThreeCNF formula)))) =
      List.replicate
        (sourceIrreducibleFormulaDegree formula) true := by
  unfold physicalInterpolationNestedOtherDegreeWord
  rw [Function.comp_apply,
    compactPhysicalLagrangeNestedOtherOriginalSource_query,
    paperVariableArityPhysicalFamilyFieldDegreeUnary_valid]

private def physicalInterpolationNestedDifferenceWord
    (left right : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  compactPhysicalFieldWordXorWithDegree
    paperVariableArityPhysicalInterpolationNestedOtherDegreeComputer
    left right

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedDifferenceWordComputable
    (left right : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalInterpolationNestedDifferenceWord
        left right) :=
  compactPhysicalFieldWordXorWithDegreeComputable
    paperVariableArityPhysicalInterpolationNestedOtherDegreeComputer
    left right

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationNestedDifferenceComputer
    (left right : SourcePhysicalLagrangeWordComputer) :
    SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationNestedDifferenceWord
    left right
  computer :=
    paperVariableArityPhysicalInterpolationNestedDifferenceWordComputable
      left right

private theorem paperVariableArityPhysicalInterpolationNestedDifferenceWord_valid
    (left right : SourcePhysicalLagrangeWordComputer)
    (innerWidth outerWidth : SourceQaryMaskDynamicGridWidth)
    (other node row column : ℕ) (formula : ThreeCNF)
    (leftWord rightWord : GapCVP.Core.EffectiveBinaryField.Word
      (sourceIrreducibleFormulaDegree formula))
    (hleft : left.output
      (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
        (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node
          (affineCellQuery row column
            (encodeThreeCNF formula)))) = finiteWordBits leftWord)
    (hright : right.output
      (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
        (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node
          (affineCellQuery row column
            (encodeThreeCNF formula)))) = finiteWordBits rightWord) :
    physicalInterpolationNestedDifferenceWord left right
        (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
          (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node
            (affineCellQuery row column
              (encodeThreeCNF formula)))) =
      finiteWordBits
        (compactPhysicalFieldWordXorValue leftWord rightWord) := by
  exact compactPhysicalFieldWordXorWithDegree_valid
    paperVariableArityPhysicalInterpolationNestedOtherDegreeComputer
    left right
    (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node
        (affineCellQuery row column
          (encodeThreeCNF formula))))
    (sourceIrreducibleFormulaDegree formula)
    leftWord rightWord
    (paperVariableArityPhysicalInterpolationNestedOtherDegreeWord_valid
      innerWidth outerWidth other node row column formula)
    hleft hright

private def physicalInterpolationNestedEraseSelection :
    List Bool → List Bool :=
  flatPhysicalPrependComputedRecordOutput
    paperVariableArityPhysicalInterpolationNestedOtherSelfMask

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedEraseSelectionComputable :
    BitTM
      physicalInterpolationNestedEraseSelection :=
  flatPhysicalPrependComputedRecordComputable
    paperVariableArityPhysicalInterpolationNestedOtherSelfMaskComputable

@[simp] theorem
    paperVariableArityPhysicalInterpolationNestedEraseSelection_valid
    (innerWidth outerWidth : SourceQaryMaskDynamicGridWidth)
    (other node : ℕ) (cell : List Bool) :
    physicalInterpolationNestedEraseSelection
        (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
          (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node cell)) =
      lengthPrefixedWord [decide (other = node)] ++
        compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
          (compactPhysicalLagrangeNestedNodeEnvelope
            outerWidth node cell) := by
  simp only [physicalInterpolationNestedEraseSelection, flatPhysicalPrependComputedRecordOutput_eq,
      paperVariableArityPhysicalInterpolationNestedOtherSelfMask_valid]

private def paperVariableArityPhysicalInterpolationNestedEraseOneBranch :
    List Bool → List Bool :=
  fourFamilyTaggedGuardedWorkerWord [true]
      physicalInterpolationNestedOtherFieldOneWord ∘
    physicalInterpolationNestedEraseSelection

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedEraseOneBranchComputable :
    BitTM
      paperVariableArityPhysicalInterpolationNestedEraseOneBranch :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalInterpolationNestedEraseSelectionComputable
    (fourFamilyTaggedGuardedWorkerComputable [true]
      paperVariableArityPhysicalInterpolationNestedOtherFieldOneWordComputable)

private def paperVariableArityPhysicalInterpolationNestedEraseOtherBranch
    (factor : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  fourFamilyTaggedGuardedWorkerWord [false] factor.output ∘
    physicalInterpolationNestedEraseSelection

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedEraseOtherBranchComputable
    (factor : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (paperVariableArityPhysicalInterpolationNestedEraseOtherBranch
        factor) :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalInterpolationNestedEraseSelectionComputable
    (fourFamilyTaggedGuardedWorkerComputable [false]
      factor.computer)

private def physicalInterpolationNestedEraseFactorWord
    (factor : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  paperVariableArityPhysicalInterpolationNestedEraseOneBranch input ++
    paperVariableArityPhysicalInterpolationNestedEraseOtherBranch
      factor input

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedEraseFactorWordComputable
    (factor : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalInterpolationNestedEraseFactorWord
        factor) :=
  pointwiseAppendComputable
    paperVariableArityPhysicalInterpolationNestedEraseOneBranchComputable
    (paperVariableArityPhysicalInterpolationNestedEraseOtherBranchComputable
      factor)

private theorem paperVariableArityPhysicalInterpolationNestedEraseFactorWord_valid
    (factor : SourcePhysicalLagrangeWordComputer)
    (innerWidth outerWidth : SourceQaryMaskDynamicGridWidth)
    (other node row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationNestedEraseFactorWord factor
        (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
          (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node
            (affineCellQuery row column
              (encodeThreeCNF formula)))) =
      if other = node then
        finiteWordBits
          (oneWord
            (sourceIrreducibleFormulaDegree formula))
      else
        factor.output
          (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other
            (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node
              (affineCellQuery row column
                (encodeThreeCNF formula)))) := by
  unfold physicalInterpolationNestedEraseFactorWord
    paperVariableArityPhysicalInterpolationNestedEraseOneBranch
    paperVariableArityPhysicalInterpolationNestedEraseOtherBranch
  rw [Function.comp_apply, Function.comp_apply]
  rw [paperVariableArityPhysicalInterpolationNestedEraseSelection_valid]
  by_cases hequal : other = node
  · simp only [hequal, decide_true, sourceFourFamilyTaggedGuardedWorkerWord_valid, ↓reduceIte,
        paperVariableArityPhysicalInterpolationNestedOtherFieldOneWord_valid, List.cons.injEq,
            Bool.false_eq_true, and_true,
        List.append_nil]
  · simp only [hequal, decide_false, sourceFourFamilyTaggedGuardedWorkerWord_valid,
      List.cons.injEq,
        Bool.true_eq_false, and_true, ↓reduceIte, List.nil_append]

private abbrev physicalInterpolationNodeGridWord
    (formula : ThreeCNF)
    (point : PaperVariableArityPhysicalInterpolationGridIndex formula) :
    GapCVP.Core.EffectiveBinaryField.Word
      (sourceIrreducibleFormulaDegree formula) :=
  indexedWord
    (sourceIrreducibleFormulaDegree formula)
    (evaluationWordIndex
      (variableCount_le_fieldWordCount
        (encodeThreeCNF formula).length
        (srcFormula formula)) point)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationNumeratorNodeDifferenceComputer
    (family : Fin 4) : SourcePhysicalLagrangeWordComputer :=
  paperVariableArityPhysicalInterpolationNestedDifferenceComputer
    (physicalInterpolationNestedRowGridComputer family)
    physicalInterpolationNestedOtherGridComputer

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationDenominatorNodeDifferenceComputer :
    SourcePhysicalLagrangeWordComputer :=
  paperVariableArityPhysicalInterpolationNestedDifferenceComputer
    physicalInterpolationNestedAnchorGridComputer
    physicalInterpolationNestedOtherGridComputer

private def physicalInterpolationNumeratorNodeFactorWord
    (family : Fin 4) : List Bool → List Bool :=
  physicalInterpolationNestedEraseFactorWord
    (paperVariableArityPhysicalInterpolationNumeratorNodeDifferenceComputer
      family)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNumeratorNodeFactorWordComputable
    (family : Fin 4) :
    BitTM
      (physicalInterpolationNumeratorNodeFactorWord
        family) :=
  paperVariableArityPhysicalInterpolationNestedEraseFactorWordComputable
    (paperVariableArityPhysicalInterpolationNumeratorNodeDifferenceComputer
      family)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationNumeratorNodeFactorComputer
    (family : Fin 4) : SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationNumeratorNodeFactorWord
    family
  computer :=
    paperVariableArityPhysicalInterpolationNumeratorNodeFactorWordComputable
      family

private def physicalInterpolationDenominatorNodeFactorWord :
    List Bool → List Bool :=
  physicalInterpolationNestedEraseFactorWord
    paperVariableArityPhysicalInterpolationDenominatorNodeDifferenceComputer

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationDenominatorNodeFactorWordComputable :
    BitTM
      physicalInterpolationDenominatorNodeFactorWord :=
  paperVariableArityPhysicalInterpolationNestedEraseFactorWordComputable
    paperVariableArityPhysicalInterpolationDenominatorNodeDifferenceComputer

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationDenominatorNodeFactorComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationDenominatorNodeFactorWord
  computer :=
    paperVariableArityPhysicalInterpolationDenominatorNodeFactorWordComputable

private theorem paperVariableArityPhysicalInterpolationNumeratorNodeFactorWord_valid
    (family : Fin 4)
    (innerWidth outerWidth : SourceQaryMaskDynamicGridWidth)
    (row column : ℕ) (formula : ThreeCNF)
    (other node : PaperVariableArityPhysicalInterpolationGridIndex formula) :
    physicalInterpolationNumeratorNodeFactorWord family
        (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other.val
          (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
            (affineCellQuery row column
              (encodeThreeCNF formula)))) =
      finiteWordBits
        (if other = node then
          oneWord (sourceIrreducibleFormulaDegree formula)
        else
          compactPhysicalFieldWordXorValue
            (physicalInterpolationNodeGridWord formula
              (physicalInterpolationFamilyRowGridPosition
                family row formula))
            (physicalInterpolationNodeGridWord
              formula other)) := by
  unfold physicalInterpolationNumeratorNodeFactorWord
  rw [paperVariableArityPhysicalInterpolationNestedEraseFactorWord_valid]
  by_cases hequal : other = node
  · simp only [hequal, ↓reduceIte]
  · have hval : other.val ≠ node.val := by
      intro hvalues
      exact hequal (Fin.ext hvalues)
    rw [ite_eq_right hval]
    have hfactor :=
      paperVariableArityPhysicalInterpolationNestedDifferenceWord_valid
        (physicalInterpolationNestedRowGridComputer
          family)
        physicalInterpolationNestedOtherGridComputer
        innerWidth outerWidth other.val node.val row column formula
        (physicalInterpolationNodeGridWord formula
          (physicalInterpolationFamilyRowGridPosition
            family row formula))
        (physicalInterpolationNodeGridWord formula other)
        (paperVariableArityPhysicalInterpolationNestedRowGridComputer_valid
          family innerWidth outerWidth row column formula other node)
        (paperVariableArityPhysicalInterpolationNestedOtherGridComputer_valid
          innerWidth outerWidth row column formula other node)
    simp only [paperVariableArityPhysicalInterpolationNumeratorNodeDifferenceComputer,
      paperVariableArityPhysicalInterpolationNestedDifferenceComputer]
    simpa only [hequal, ↓reduceIte] using hfactor

theorem
    paperVariableArityPhysicalInterpolationDenominatorNodeFactorWord_valid
    (innerWidth outerWidth : SourceQaryMaskDynamicGridWidth)
    (row column : ℕ) (formula : ThreeCNF)
    (other node : PaperVariableArityPhysicalInterpolationGridIndex formula) :
    physicalInterpolationDenominatorNodeFactorWord
        (compactPhysicalLagrangeNestedNodeEnvelope innerWidth other.val
          (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
            (affineCellQuery row column
              (encodeThreeCNF formula)))) =
      finiteWordBits
        (if other = node then
          oneWord (sourceIrreducibleFormulaDegree formula)
        else
          compactPhysicalFieldWordXorValue
            (physicalInterpolationNodeGridWord
              formula node)
            (physicalInterpolationNodeGridWord
              formula other)) := by
  unfold physicalInterpolationDenominatorNodeFactorWord
  rw [paperVariableArityPhysicalInterpolationNestedEraseFactorWord_valid]
  by_cases hequal : other = node
  · simp only [hequal, ↓reduceIte]
  · have hval : other.val ≠ node.val := by
      intro hvalues
      exact hequal (Fin.ext hvalues)
    rw [ite_eq_right hval]
    have hfactor :=
      paperVariableArityPhysicalInterpolationNestedDifferenceWord_valid
        physicalInterpolationNestedAnchorGridComputer
        physicalInterpolationNestedOtherGridComputer
        innerWidth outerWidth other.val node.val row column formula
        (physicalInterpolationNodeGridWord formula node)
        (physicalInterpolationNodeGridWord formula other)
        (paperVariableArityPhysicalInterpolationNestedAnchorGridComputer_valid
          innerWidth outerWidth row column formula other node)
        (paperVariableArityPhysicalInterpolationNestedOtherGridComputer_valid
          innerWidth outerWidth row column formula other node)
    simp only [paperVariableArityPhysicalInterpolationDenominatorNodeDifferenceComputer,
      paperVariableArityPhysicalInterpolationNestedDifferenceComputer]
    simpa only [hequal, ↓reduceIte] using hfactor

end PhysicalInterpolationNodeFactorTM

namespace BinaryCompactPhysicalLagrangeNodeProductAlgebra

open scoped BigOperators

open GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryFieldInverseAlgebra

private theorem compactPhysicalLagrangeSelectedWordFold_sourceWordValue
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (initial : EffectiveBinaryField.Word
      (sourceFieldExponent
        (sourceSizeParameter encodingLength formula)))
    (factors : List (EffectiveBinaryField.Word
      (sourceFieldExponent
        (sourceSizeParameter encodingLength formula)))) :
    sourceWordValue encodingLength formula
        (factors.foldl
          (EffectiveBinaryField.multiplyMod
            (EffectiveBinaryField.irreducibleWord
              (sourceFieldExponent
                (sourceSizeParameter encodingLength formula)))) initial) =
      sourceWordValue encodingLength formula initial *
        (factors.map (sourceWordValue encodingLength formula)).prod := by
  induction factors generalizing initial with
  | nil => simp only [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
  | cons factor remaining ih =>
      simp only [List.foldl_cons, List.map_cons, List.prod_cons]
      rw [ih, sourceWordValue_multiplyMod]
      simp only [mul_assoc]

private theorem compactPhysicalLagrangeSelectedWordProduct_sourceWordValue
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (factors : List (EffectiveBinaryField.Word
      (sourceFieldExponent
        (sourceSizeParameter encodingLength formula)))) :
    sourceWordValue encodingLength formula
        (factors.foldl
          (EffectiveBinaryField.multiplyMod
            (EffectiveBinaryField.irreducibleWord
              (sourceFieldExponent
                (sourceSizeParameter encodingLength formula))))
          (oneWord
            (sourceFieldExponent
              (sourceSizeParameter encodingLength formula)))) =
      (factors.map (sourceWordValue encodingLength formula)).prod := by
  rw [compactPhysicalLagrangeSelectedWordFold_sourceWordValue,
    sourceWordValue_oneWord, one_mul]

private theorem compactPhysicalLagrangeRangeMap_prod
    {K : Type*} [CommMonoid K]
    (value : ℕ → K) (count : ℕ) :
    ((List.range count).map value).prod =
      ∏ index : Fin count, value index.val := by
  rw [Fin.prod_univ_eq_prod_range]
  induction count with
  | zero => simp only [List.range_zero, List.map_nil, List.prod_nil, Finset.range_zero,
      Finset.prod_empty]
  | succ count ih =>
      rw [List.range_succ, List.map_append, List.prod_append,
        Finset.prod_range_succ]
      simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using
          congrArg (fun product => product * value count) ih

end BinaryCompactPhysicalLagrangeNodeProductAlgebra

namespace PhysicalFieldWordSemantics

open GapCVP.Core GapCVP.Core.EffectiveBinaryField
open GapCVP.BinaryCompactPhysicalFieldBasisCoordinates GapCVP.BinaryFieldInverseAlgebra
open GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics

private theorem paperVariableArityPhysicalBinaryCoordinate_zero_or_one
    (value : ZMod 2) : value = 0 ∨ value = 1 := by
  exact GapCVP.Core.effectiveBinary_eq_zero_or_one value

private theorem paperVariableArityPhysicalBitValue_decide
    (value : ZMod 2) :
    bitValue (decide (value = 1)) = value := by
  rcases paperVariableArityPhysicalBinaryCoordinate_zero_or_one value with
    zero | one
  · simp only [bitValue, zero, zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte]
  · simp only [bitValue, one, decide_true, ↓reduceIte]

private theorem paperVariableArityPhysicalSourceWordValue_injective
    (encodingLength : ℕ) (formula : ThreeCNF) :
    Function.Injective
      (sourceWordValue encodingLength
        (srcFormula formula)) := by
  intro left right equal
  apply funext
  intro index
  have coordinate := congrArg
    (fun value : PaperVariableArityPhysicalWordField
      encodingLength formula =>
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
        encodingLength
        (srcFormula formula)).equivFun
        value index) equal
  rw [sourceFormulaFieldBasis_sourceWordValue_coordinate,
    sourceFormulaFieldBasis_sourceWordValue_coordinate] at coordinate
  cases leftBit : left index <;>
    cases rightBit : right index <;>
    simp_all [bitValue]

end PhysicalFieldWordSemantics

namespace PhysicalLagrangeNodeProductAlgebra

open scoped BigOperators

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.BinaryCompactPhysicalFieldWordXorTM
open GapCVP.BinaryCompactPhysicalLagrangeNodeProductAlgebra GapCVP.BinaryFieldBasis
open GapCVP.BinaryFieldInverseAlgebra GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalOrdinaryShiftedCoefficientTM GapCVP.BinarySourceCoordinateOrder
open GapCVP.Factor400BinaryConstructiveSourcePlaces

/-- GapCVP reduction support. -/
abbrev PaperVariableArityPhysicalLagrangeNodeGridIndex
    (formula : ThreeCNF) :=
  Fin (2 ^ physDegree formula -
    (srcFormula formula).variableCount)

/-- GapCVP reduction support. -/
def physicalLagrangeNodeEvaluationWord
    (formula : ThreeCNF)
    (point : PaperVariableArityPhysicalLagrangeNodeGridIndex formula) :
    PaperVariableArityPhysicalInterpolationWord formula :=
  indexedWord (physDegree formula)
    (evaluationWordIndex
      (variableCount_le_fieldWordCount
        (encodeThreeCNF formula).length
        (srcFormula formula)) point)

theorem physicalLagrangeNodeEvaluationWord_sourceField
    (formula : ThreeCNF)
    (point : PaperVariableArityPhysicalLagrangeNodeGridIndex formula) :
    sourceWordValue (encodeThreeCNF formula).length
      (srcFormula formula)
      (physicalLagrangeNodeEvaluationWord
        formula point) =
      sourceFormulaEvaluationWord (encodeThreeCNF formula).length
        (srcFormula formula) point := by
  rfl

private def physicalLagrangeNodeSelectedWordProduct
    (formula : ThreeCNF)
    (factors : List (PaperVariableArityPhysicalInterpolationWord formula)) :
    PaperVariableArityPhysicalInterpolationWord formula :=
  factors.foldl
    (multiplyMod
      (irreducibleWord
        (physDegree formula)))
    (oneWord (physDegree formula))

private theorem paperVariableArityPhysicalLagrangeNodeSelectedWordProduct_sourceField
    (formula : ThreeCNF)
    (factors : List (PaperVariableArityPhysicalInterpolationWord formula)) :
    sourceWordValue (encodeThreeCNF formula).length
      (srcFormula formula)
      (physicalLagrangeNodeSelectedWordProduct
        formula factors) =
      (factors.map
        (sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula))).prod := by
  exact compactPhysicalLagrangeSelectedWordProduct_sourceWordValue
    (encodeThreeCNF formula).length
    (srcFormula formula) factors

private def physicalLagrangeNumeratorNodeFactorValue
    (formula : ThreeCNF)
    (node point : PaperVariableArityPhysicalLagrangeNodeGridIndex formula)
    (other : ℕ) : PaperVariableArityPhysicalInterpolationWord formula :=
  if other = node.val then
    oneWord (physDegree formula)
  else if bounded : other <
      2 ^ physDegree formula -
        (srcFormula formula).variableCount then
    compactPhysicalFieldWordXorValue
      (physicalLagrangeNodeEvaluationWord
        formula point)
      (physicalLagrangeNodeEvaluationWord
        formula ⟨other, bounded⟩)
  else oneWord (physDegree formula)

private def physicalLagrangeNumeratorNodeFactorValues
    (formula : ThreeCNF)
    (node point : PaperVariableArityPhysicalLagrangeNodeGridIndex formula)
    (count : ℕ) :
    List (PaperVariableArityPhysicalInterpolationWord formula) :=
  (List.range count).map
    (physicalLagrangeNumeratorNodeFactorValue
      formula node point)

private def physicalLagrangeDenominatorNodeFactorValue
    (formula : ThreeCNF)
    (node : PaperVariableArityPhysicalLagrangeNodeGridIndex formula)
    (other : ℕ) : PaperVariableArityPhysicalInterpolationWord formula :=
  physicalLagrangeNumeratorNodeFactorValue
    formula node node other

private def physicalLagrangeDenominatorNodeFactorValues
    (formula : ThreeCNF)
    (node : PaperVariableArityPhysicalLagrangeNodeGridIndex formula)
    (count : ℕ) :
    List (PaperVariableArityPhysicalInterpolationWord formula) :=
  (List.range count).map
    (physicalLagrangeDenominatorNodeFactorValue
      formula node)

private theorem paperVariableArityPhysicalLagrangeNumeratorNodeFactorValues_sourceField
    (formula : ThreeCNF) (count : ℕ)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount)
    (node : Fin count)
    (point : PaperVariableArityPhysicalLagrangeNodeGridIndex formula) :
    sourceWordValue (encodeThreeCNF formula).length
      (srcFormula formula)
      (physicalLagrangeNodeSelectedWordProduct formula
        (physicalLagrangeNumeratorNodeFactorValues
          formula (Fin.castLE bounded node) point count)) =
      ∏ other ∈ (Finset.univ.erase node),
        (sourceFormulaEvaluationWord
          (encodeThreeCNF formula).length
          (srcFormula formula) point -
        sourceFormulaEvaluationWord
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (Fin.castLE bounded other)) := by
  classical
  rw [paperVariableArityPhysicalLagrangeNodeSelectedWordProduct_sourceField]
  unfold physicalLagrangeNumeratorNodeFactorValues
  rw [List.map_map, compactPhysicalLagrangeRangeMap_prod]
  let gridValue := fun other : Fin count =>
    sourceFormulaEvaluationWord (encodeThreeCNF formula).length
        (srcFormula formula) point -
      sourceFormulaEvaluationWord (encodeThreeCNF formula).length
        (srcFormula formula)
        (Fin.castLE bounded other)
  have factorValue (other : Fin count) :
      sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalLagrangeNumeratorNodeFactorValue
            formula (Fin.castLE bounded node) point other.val) =
        if other = node then 1 else gridValue other := by
    by_cases equal : other = node
    · subst other
      simp only [physicalLagrangeNumeratorNodeFactorValue, Fin.val_castLE, ↓reduceIte,
          sourceWordValue_oneWord]
    · have rankBound : other.val <
          2 ^ physDegree formula -
            (srcFormula formula).variableCount :=
        lt_of_lt_of_le other.isLt bounded
      have different : other.val ≠ node.val := by
        intro same
        exact equal (Fin.ext same)
      have samePoint :
          (⟨other.val, rankBound⟩ :
            PaperVariableArityPhysicalLagrangeNodeGridIndex formula) =
          Fin.castLE bounded other := by
        apply Fin.ext
        rfl
      simp only [physicalLagrangeNumeratorNodeFactorValue,
        Fin.val_castLE, different, ↓reduceIte, dite_eq_left rankBound,
        ite_eq_right equal, gridValue]
      rw [compactPhysicalFieldWordXorValue_sourceWordValue_sub,
        physicalLagrangeNodeEvaluationWord_sourceField,
        physicalLagrangeNodeEvaluationWord_sourceField,
        samePoint]
  calc
    ∏ other : Fin count,
        sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalLagrangeNumeratorNodeFactorValue
            formula (Fin.castLE bounded node) point other.val) =
      ∏ other : Fin count,
        if other = node then 1 else gridValue other := by
          exact Finset.prod_congr rfl
            (fun other _ => factorValue other)
    _ = ∏ other ∈ (Finset.univ.erase node), gridValue other := by
      calc
        (∏ other : Fin count,
          if other = node then 1 else gridValue other) =
          (∏ other ∈ (Finset.univ.erase node),
            if other = node then 1 else gridValue other) :=
          (Finset.prod_erase (Finset.univ : Finset (Fin count))
            (f := fun other => if other = node then 1 else gridValue other)
            (by simp only [↓reduceIte])).symm
        _ = ∏ other ∈ (Finset.univ.erase node), gridValue other := by
          apply Finset.prod_congr rfl
          intro other present
          simp only [Finset.mem_erase.mp present |>.1, ↓reduceIte]

private theorem paperVariableArityPhysicalLagrangeDenominatorNodeFactorValues_sourceField
    (formula : ThreeCNF) (count : ℕ)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount)
    (node : Fin count) :
    sourceWordValue (encodeThreeCNF formula).length
      (srcFormula formula)
      (physicalLagrangeNodeSelectedWordProduct formula
        (physicalLagrangeDenominatorNodeFactorValues
          formula (Fin.castLE bounded node) count)) =
      ∏ other ∈ (Finset.univ.erase node),
        (sourceFormulaEvaluationWord
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (Fin.castLE bounded node) -
        sourceFormulaEvaluationWord
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (Fin.castLE bounded other)) := by
  exact paperVariableArityPhysicalLagrangeNumeratorNodeFactorValues_sourceField
    formula count bounded node (Fin.castLE bounded node)

end PhysicalLagrangeNodeProductAlgebra

namespace PhysicalLagrangeNodeProductCatalogueCorrectness

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalLagrangeProductFoldTM
open GapCVP.BinaryCompactPhysicalFieldWordXorTM
open GapCVP.BinaryCompactPhysicalLagrangeFactorStreamTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM
open GapCVP.BinaryCompactPhysicalLagrangeNodeProductTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalLagrangeNodeProductAlgebra
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

private theorem physicalLagrangeNumeratorNodeFactorValue_fin
    (formula : ThreeCNF)
    (node point other : PaperVariableArityPhysicalLagrangeNodeGridIndex formula) :
    (if other = node then oneWord (physDegree formula)
      else compactPhysicalFieldWordXorValue
        (physicalLagrangeNodeEvaluationWord formula point)
        (physicalLagrangeNodeEvaluationWord formula other)) =
      physicalLagrangeNumeratorNodeFactorValue formula node point other.val := by
  by_cases equal : other = node
  · simp only [equal, ↓reduceIte, physicalLagrangeNumeratorNodeFactorValue]
  · have different : other.val ≠ node.val := fun same => equal (Fin.ext same)
    rw [ite_eq_right equal]
    unfold physicalLagrangeNumeratorNodeFactorValue
    rw [ite_eq_right different, dite_eq_left other.isLt]

private theorem compactPhysicalLagrangeNodeFactorCatalogue_map
    {degree : ℕ}
    (width : SourceQaryMaskDynamicGridWidth)
    (computer : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) (count : ℕ)
    (factors : ℕ → GapCVP.Core.EffectiveBinaryField.Word degree)
    (hwidth : width.output input = List.replicate count true)
    (hfactor : ∀ rank, rank < count → computer.output
      (compactPhysicalLagrangeNodeFactorQuery width input rank) =
        finiteWordBits (factors rank)) :
    compactPhysicalLagrangeNodeFactorCatalogue width computer input =
      sourcePhysicalLagrangePackedFactorWords
        ((List.range count).map factors) := by
  rw [compactPhysicalLagrangeNodeFactorCatalogue_valid
    width computer input count hwidth]
  unfold sourcePhysicalLagrangePackedFactorWords
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro rank present
  exact congrArg lengthPrefixedWord
    (hfactor rank (List.mem_range.mp present))

private theorem paperVariableArityPhysicalInterpolationNumeratorNodeCatalogue_valid
    (family : Fin 4)
    (width outerWidth : SourceQaryMaskDynamicGridWidth)
    (row column : ℕ) (formula : ThreeCNF)
    (node : PaperVariableArityPhysicalLagrangeNodeGridIndex formula)
    (count : ℕ)
    (correctWidth : width.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
        List.replicate count true)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount) :
    compactPhysicalLagrangeNodeFactorCatalogue
      (compactPhysicalLagrangeNestedNodePrefixWidth width)
      (paperVariableArityPhysicalInterpolationNumeratorNodeFactorComputer
        family)
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
        (affineCellQuery row column
          (encodeThreeCNF formula))) =
      sourcePhysicalLagrangePackedFactorWords
        (physicalLagrangeNumeratorNodeFactorValues
          formula node
          (physicalInterpolationFamilyRowGridPosition
            family row formula) count) := by
  let cell := affineCellQuery row column (encodeThreeCNF formula)
  let outer := compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val cell
  let inner := compactPhysicalLagrangeNestedNodePrefixWidth width
  apply compactPhysicalLagrangeNodeFactorCatalogue_map inner
    (paperVariableArityPhysicalInterpolationNumeratorNodeFactorComputer family)
    outer count (physicalLagrangeNumeratorNodeFactorValue formula node
      (physicalInterpolationFamilyRowGridPosition family row formula))
  · exact compactPhysicalLagrangeNestedNodePrefixWidth_valid
      width outerWidth node.val cell ▸ correctWidth
  · intro rank present
    let other : PaperVariableArityPhysicalLagrangeNodeGridIndex formula :=
      ⟨rank, lt_of_lt_of_le present bounded⟩
    change physicalInterpolationNumeratorNodeFactorWord family
      (compactPhysicalLagrangeNestedNodeEnvelope inner other.val
        (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val cell)) = _
    rw [paperVariableArityPhysicalInterpolationNumeratorNodeFactorWord_valid
      family inner outerWidth row column formula other node]
    exact congrArg finiteWordBits
      (physicalLagrangeNumeratorNodeFactorValue_fin formula node
        (physicalInterpolationFamilyRowGridPosition family row formula) other)

private theorem paperVariableArityPhysicalInterpolationDenominatorNodeCatalogue_valid
    (width outerWidth : SourceQaryMaskDynamicGridWidth)
    (row column : ℕ) (formula : ThreeCNF)
    (node : PaperVariableArityPhysicalLagrangeNodeGridIndex formula)
    (count : ℕ)
    (correctWidth : width.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
        List.replicate count true)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount) :
    compactPhysicalLagrangeNodeFactorCatalogue
      (compactPhysicalLagrangeNestedNodePrefixWidth width)
      paperVariableArityPhysicalInterpolationDenominatorNodeFactorComputer
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
        (affineCellQuery row column
          (encodeThreeCNF formula))) =
      sourcePhysicalLagrangePackedFactorWords
        (physicalLagrangeDenominatorNodeFactorValues
          formula node count) := by
  let cell := affineCellQuery row column (encodeThreeCNF formula)
  let outer := compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val cell
  let inner := compactPhysicalLagrangeNestedNodePrefixWidth width
  apply compactPhysicalLagrangeNodeFactorCatalogue_map inner
    paperVariableArityPhysicalInterpolationDenominatorNodeFactorComputer
    outer count (physicalLagrangeDenominatorNodeFactorValue formula node)
  · exact compactPhysicalLagrangeNestedNodePrefixWidth_valid
      width outerWidth node.val cell ▸ correctWidth
  · intro rank present
    let other : PaperVariableArityPhysicalLagrangeNodeGridIndex formula :=
      ⟨rank, lt_of_lt_of_le present bounded⟩
    change physicalInterpolationDenominatorNodeFactorWord
      (compactPhysicalLagrangeNestedNodeEnvelope inner other.val
        (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val cell)) = _
    rw [paperVariableArityPhysicalInterpolationDenominatorNodeFactorWord_valid
      inner outerWidth row column formula other node]
    exact congrArg finiteWordBits
      (physicalLagrangeNumeratorNodeFactorValue_fin formula node node other)

end PhysicalLagrangeNodeProductCatalogueCorrectness

namespace PhysicalInterpolationNestedNodeProductTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalLagrangeProductFoldTM
open GapCVP.BinaryCompactPhysicalLagrangeFactorStreamTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM
open GapCVP.BinaryCompactPhysicalLagrangeNodeProductTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
open GapCVP.PhysicalInterpolationNodeGridMaskTM GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalLagrangeNodeProductAlgebra
open GapCVP.PhysicalLagrangeNodeProductCatalogueCorrectness
open GapCVP.BinarySourceFieldMultiplicationTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

private def physicalInterpolationNestedNodeSelectedModulusWord :
    List Bool → List Bool :=
  sourceSelectedIrreducibleWord ∘
    compactPhysicalLagrangeNestedNodeOriginalSource

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusComputable :
    BitTM
      physicalInterpolationNestedNodeSelectedModulusWord :=
  GapCVP.TMComposition.computableInPolyTime
    compactPhysicalLagrangeNestedNodeOriginalSourceComputable
    paperVariableAritySourceSelectedIrreducibleWordComputable

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationNestedNodeSelectedModulusWord
  computer :=
    paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusComputable

theorem
    paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusComputer_output
    (input : List Bool) :
    paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusComputer.output
        input =
      physicalInterpolationNestedNodeSelectedModulusWord
        input := by
  rfl

@[simp] theorem
    paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusWord_valid
    (width : SourceQaryMaskDynamicGridWidth)
    (node row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationNestedNodeSelectedModulusWord
        (compactPhysicalLagrangeNestedNodeEnvelope width node
          (affineCellQuery row column
            (encodeThreeCNF formula))) =
      finiteWordBits
        (irreducibleWord
          (sourceIrreducibleFormulaDegree formula)) := by
  unfold physicalInterpolationNestedNodeSelectedModulusWord
  rw [Function.comp_apply,
    compactPhysicalLagrangeNestedNodeOriginalSource_query]
  exact paperVariableAritySourceSelectedIrreducibleWord_valid formula

private def physicalInterpolationNestedNodeFieldOneWord :
    List Bool → List Bool :=
  physicalInterpolationCellFieldOneWord ∘
    compactPhysicalLagrangeNestedNodeOuterCell

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedNodeFieldOneComputable :
    BitTM
      physicalInterpolationNestedNodeFieldOneWord :=
  GapCVP.TMComposition.computableInPolyTime
    compactPhysicalLagrangeNestedNodeOuterCellComputable
    paperVariableArityPhysicalInterpolationCellFieldOneWordComputable

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationNestedNodeFieldOneComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationNestedNodeFieldOneWord
  computer :=
    paperVariableArityPhysicalInterpolationNestedNodeFieldOneComputable

@[simp] theorem
    paperVariableArityPhysicalInterpolationNestedNodeFieldOneWord_valid
    (width : SourceQaryMaskDynamicGridWidth)
    (node row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationNestedNodeFieldOneWord
        (compactPhysicalLagrangeNestedNodeEnvelope width node
          (affineCellQuery row column
            (encodeThreeCNF formula))) =
      finiteWordBits
        (oneWord (sourceIrreducibleFormulaDegree formula)) := by
  unfold physicalInterpolationNestedNodeFieldOneWord
  rw [Function.comp_apply,
    compactPhysicalLagrangeNestedNodeOuterCell_query]
  exact paperVariableArityPhysicalInterpolationCellFieldOneWord_valid
    row column formula

private def paperVariableArityPhysicalInterpolationNestedNodeInverseQuery
    (operand : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (operand.output input) ++
    compactPhysicalLagrangeNestedNodeOriginalSource input

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedNodeInverseQueryComputable
    (operand : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (paperVariableArityPhysicalInterpolationNestedNodeInverseQuery
        operand) := by
  exact pointwiseAppendComputable
    (sourcePhysicalLagrangePrefixedComputable operand)
    compactPhysicalLagrangeNestedNodeOriginalSourceComputable

private def physicalInterpolationNestedNodeInverseWord
    (operand : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  sourceSelectedFieldInverseWord ∘
    paperVariableArityPhysicalInterpolationNestedNodeInverseQuery operand

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedNodeInverseWordComputable
    (operand : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalInterpolationNestedNodeInverseWord
        operand) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityPhysicalInterpolationNestedNodeInverseQueryComputable
      operand)
    paperVariableAritySourceSelectedFieldInverseComputable

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationNestedNodeInverseComputer
    (operand : SourcePhysicalLagrangeWordComputer) :
    SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationNestedNodeInverseWord
    operand
  computer :=
    paperVariableArityPhysicalInterpolationNestedNodeInverseWordComputable
      operand

private theorem paperVariableArityPhysicalInterpolationNestedNodeInverseWord_valid
    (operand : SourcePhysicalLagrangeWordComputer)
    (width : SourceQaryMaskDynamicGridWidth)
    (node row column : ℕ) (formula : ThreeCNF)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (sourceIrreducibleFormulaDegree formula))
    (correctOperand : operand.output
      (compactPhysicalLagrangeNestedNodeEnvelope width node
        (affineCellQuery row column
          (encodeThreeCNF formula))) = finiteWordBits value) :
    physicalInterpolationNestedNodeInverseWord operand
      (compactPhysicalLagrangeNestedNodeEnvelope width node
        (affineCellQuery row column
          (encodeThreeCNF formula))) =
      finiteWordBits (sourceInverseWord value) := by
  unfold physicalInterpolationNestedNodeInverseWord
    paperVariableArityPhysicalInterpolationNestedNodeInverseQuery
  rw [Function.comp_apply, correctOperand,
    compactPhysicalLagrangeNestedNodeOriginalSource_query]
  exact paperVariableAritySourceSelectedFieldInverseWord_valid
    formula value

private def paperVariableArityPhysicalInterpolationNestedNodeMultiplyQuery
    (lower left right : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  factor400BinarySourceFieldQuery
    (lower.output input) (left.output input) (right.output input)
    (compactPhysicalLagrangeNestedNodeOriginalSource input)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedNodeMultiplyQueryComputable
    (lower left right : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (paperVariableArityPhysicalInterpolationNestedNodeMultiplyQuery
        lower left right) := by
  have hright := pointwiseAppendComputable
    (sourcePhysicalLagrangePrefixedComputable right)
    compactPhysicalLagrangeNestedNodeOriginalSourceComputable
  have hmiddle := pointwiseAppendComputable
    (sourcePhysicalLagrangePrefixedComputable left) hright
  have hcomplete := pointwiseAppendComputable
    (sourcePhysicalLagrangePrefixedComputable lower) hmiddle
  change BitTM
    (fun input => factor400BinarySourceFieldQuery
      (lower.output input) (left.output input) (right.output input)
      (compactPhysicalLagrangeNestedNodeOriginalSource input))
  simpa only [factor400BinarySourceFieldQuery, List.append_assoc,
      sourcePhysicalLagrangePrefixedOutput] using
      hcomplete

private def physicalInterpolationNestedNodeMultiplyWord
    (left right : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  binarySourceMultiplyModWord ∘
    paperVariableArityPhysicalInterpolationNestedNodeMultiplyQuery
      paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusComputer
      left right

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedNodeMultiplyWordComputable
    (left right : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalInterpolationNestedNodeMultiplyWord
        left right) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityPhysicalInterpolationNestedNodeMultiplyQueryComputable
      paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusComputer
      left right)
    binarySourceMultiplyModComputable

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationNestedNodeMultiplyComputer
    (left right : SourcePhysicalLagrangeWordComputer) :
    SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationNestedNodeMultiplyWord
    left right
  computer :=
    paperVariableArityPhysicalInterpolationNestedNodeMultiplyWordComputable
      left right

private theorem paperVariableArityPhysicalInterpolationNestedNodeMultiplyWord_valid
    (left right : SourcePhysicalLagrangeWordComputer)
    (width : SourceQaryMaskDynamicGridWidth)
    (node row column : ℕ) (formula : ThreeCNF)
    (leftWord rightWord : GapCVP.Core.EffectiveBinaryField.Word
      (sourceIrreducibleFormulaDegree formula))
    (correctLeft : left.output
      (compactPhysicalLagrangeNestedNodeEnvelope width node
        (affineCellQuery row column
          (encodeThreeCNF formula))) = finiteWordBits leftWord)
    (correctRight : right.output
      (compactPhysicalLagrangeNestedNodeEnvelope width node
        (affineCellQuery row column
          (encodeThreeCNF formula))) = finiteWordBits rightWord) :
    physicalInterpolationNestedNodeMultiplyWord
      left right
      (compactPhysicalLagrangeNestedNodeEnvelope width node
        (affineCellQuery row column
          (encodeThreeCNF formula))) =
      finiteWordBits
        (multiplyMod
          (irreducibleWord
            (sourceIrreducibleFormulaDegree formula))
          leftWord rightWord) := by
  unfold physicalInterpolationNestedNodeMultiplyWord
    paperVariableArityPhysicalInterpolationNestedNodeMultiplyQuery
  rw [Function.comp_apply, correctLeft, correctRight,
    paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusComputer_output,
    paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusWord_valid,
    compactPhysicalLagrangeNestedNodeOriginalSource_query]
  exact binarySourceMultiplyModWord_valid
    (irreducibleWord
      (sourceIrreducibleFormulaDegree formula))
    leftWord rightWord (encodeThreeCNF formula)

private def physicalInterpolationNestedNumeratorNodeProductWord
    (family : Fin 4) (width : SourceQaryMaskDynamicGridWidth) :
    List Bool → List Bool :=
  compactPhysicalLagrangeFactorProductWord
    (compactPhysicalLagrangeNestedNodePrefixWidth width)
    paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusComputer
    paperVariableArityPhysicalInterpolationNestedNodeFieldOneComputer
    compactPhysicalLagrangeNestedNodeSourceWordComputer
    (paperVariableArityPhysicalInterpolationNumeratorNodeFactorComputer family)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedNumeratorNodeProductComputable
    (family : Fin 4) (width : SourceQaryMaskDynamicGridWidth) :
    BitTM
      (physicalInterpolationNestedNumeratorNodeProductWord
        family width) :=
  compactPhysicalLagrangeFactorProductComputable
    (compactPhysicalLagrangeNestedNodePrefixWidth width)
    paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusComputer
    paperVariableArityPhysicalInterpolationNestedNodeFieldOneComputer
    compactPhysicalLagrangeNestedNodeSourceWordComputer
    (paperVariableArityPhysicalInterpolationNumeratorNodeFactorComputer family)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationNestedNumeratorNodeProductComputer
    (family : Fin 4) (width : SourceQaryMaskDynamicGridWidth) :
    SourcePhysicalLagrangeWordComputer where
  output :=
    physicalInterpolationNestedNumeratorNodeProductWord
      family width
  computer :=
    paperVariableArityPhysicalInterpolationNestedNumeratorNodeProductComputable
      family width

private def physicalInterpolationNestedDenominatorNodeProductWord
    (width : SourceQaryMaskDynamicGridWidth) :
    List Bool → List Bool :=
  compactPhysicalLagrangeFactorProductWord
    (compactPhysicalLagrangeNestedNodePrefixWidth width)
    paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusComputer
    paperVariableArityPhysicalInterpolationNestedNodeFieldOneComputer
    compactPhysicalLagrangeNestedNodeSourceWordComputer
    paperVariableArityPhysicalInterpolationDenominatorNodeFactorComputer

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedDenominatorNodeProductComputable
    (width : SourceQaryMaskDynamicGridWidth) :
    BitTM
      (physicalInterpolationNestedDenominatorNodeProductWord
        width) :=
  compactPhysicalLagrangeFactorProductComputable
    (compactPhysicalLagrangeNestedNodePrefixWidth width)
    paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusComputer
    paperVariableArityPhysicalInterpolationNestedNodeFieldOneComputer
    compactPhysicalLagrangeNestedNodeSourceWordComputer
    paperVariableArityPhysicalInterpolationDenominatorNodeFactorComputer

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationNestedDenominatorNodeProductComputer
    (width : SourceQaryMaskDynamicGridWidth) :
    SourcePhysicalLagrangeWordComputer where
  output :=
    physicalInterpolationNestedDenominatorNodeProductWord
      width
  computer :=
    paperVariableArityPhysicalInterpolationNestedDenominatorNodeProductComputable
      width

private theorem physicalInterpolationNestedNodeProductWord_valid
    (width outerWidth : SourceQaryMaskDynamicGridWidth)
    (row column : ℕ) (formula : ThreeCNF)
    (node : PaperVariableArityPhysicalLagrangeNodeGridIndex formula)
    (count : ℕ)
    (factors : List (GapCVP.Core.EffectiveBinaryField.Word (physDegree formula)))
    (computer : SourcePhysicalLagrangeWordComputer)
    (correctWidth : width.output
      (affineCellQuery row column (encodeThreeCNF formula)) =
        List.replicate count true)
    (factorLength : factors.length = count)
    (correctFactors : compactPhysicalLagrangeNodeFactorCatalogue
      (compactPhysicalLagrangeNestedNodePrefixWidth width) computer
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
        (affineCellQuery row column (encodeThreeCNF formula))) =
        sourcePhysicalLagrangePackedFactorWords factors) :
    compactPhysicalLagrangeFactorProductWord
      (compactPhysicalLagrangeNestedNodePrefixWidth width)
      paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusComputer
      paperVariableArityPhysicalInterpolationNestedNodeFieldOneComputer
      compactPhysicalLagrangeNestedNodeSourceWordComputer computer
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
        (affineCellQuery row column (encodeThreeCNF formula))) =
      finiteWordBits (physicalLagrangeNodeSelectedWordProduct formula factors) := by
  let cell := affineCellQuery row column (encodeThreeCNF formula)
  let outer := compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val cell
  let inner := compactPhysicalLagrangeNestedNodePrefixWidth width
  apply compactPhysicalLagrangeFactorProductWord_valid inner
    paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusComputer
    paperVariableArityPhysicalInterpolationNestedNodeFieldOneComputer
    compactPhysicalLagrangeNestedNodeSourceWordComputer computer outer
    (irreducibleWord (physDegree formula)) (oneWord (physDegree formula))
    factors (encodeThreeCNF formula)
  · simpa only [factorLength] using
      compactPhysicalLagrangeNestedNodePrefixWidth_valid
        width outerWidth node.val cell ▸ correctWidth
  · exact paperVariableArityPhysicalInterpolationNestedNodeSelectedModulusWord_valid
      outerWidth node.val row column formula
  · exact paperVariableArityPhysicalInterpolationNestedNodeFieldOneWord_valid
      outerWidth node.val row column formula
  · exact compactPhysicalLagrangeNestedNodeOriginalSource_query
      outerWidth node.val row column formula
  · exact correctFactors

theorem
    paperVariableArityPhysicalInterpolationNestedNumeratorNodeProductWord_valid
    (family : Fin 4)
    (width outerWidth : SourceQaryMaskDynamicGridWidth)
    (row column : ℕ) (formula : ThreeCNF)
    (node : PaperVariableArityPhysicalLagrangeNodeGridIndex formula)
    (count : ℕ)
    (correctWidth : width.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate count true)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount) :
    physicalInterpolationNestedNumeratorNodeProductWord
      family width
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
        (affineCellQuery row column
          (encodeThreeCNF formula))) =
      finiteWordBits
        (physicalLagrangeNodeSelectedWordProduct formula
          (physicalLagrangeNumeratorNodeFactorValues
            formula node
            (physicalInterpolationFamilyRowGridPosition
              family row formula) count)) := by
  apply physicalInterpolationNestedNodeProductWord_valid
    width outerWidth row column formula node count
    (physicalLagrangeNumeratorNodeFactorValues formula node
      (physicalInterpolationFamilyRowGridPosition family row formula) count)
    (paperVariableArityPhysicalInterpolationNumeratorNodeFactorComputer family)
    correctWidth
  · simp only [physicalLagrangeNumeratorNodeFactorValues, List.length_map, List.length_range]
  · exact paperVariableArityPhysicalInterpolationNumeratorNodeCatalogue_valid
      family width outerWidth row column formula node count correctWidth bounded

theorem
    paperVariableArityPhysicalInterpolationNestedDenominatorNodeProductWord_valid
    (width outerWidth : SourceQaryMaskDynamicGridWidth)
    (row column : ℕ) (formula : ThreeCNF)
    (node : PaperVariableArityPhysicalLagrangeNodeGridIndex formula)
    (count : ℕ)
    (correctWidth : width.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate count true)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount) :
    physicalInterpolationNestedDenominatorNodeProductWord
      width
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
        (affineCellQuery row column
          (encodeThreeCNF formula))) =
      finiteWordBits
        (physicalLagrangeNodeSelectedWordProduct formula
          (physicalLagrangeDenominatorNodeFactorValues
            formula node count)) := by
  apply physicalInterpolationNestedNodeProductWord_valid
    width outerWidth row column formula node count
    (physicalLagrangeDenominatorNodeFactorValues formula node count)
    paperVariableArityPhysicalInterpolationDenominatorNodeFactorComputer
    correctWidth
  · simp only [physicalLagrangeDenominatorNodeFactorValues, List.length_map, List.length_range]
  · exact paperVariableArityPhysicalInterpolationDenominatorNodeCatalogue_valid
      width outerWidth row column formula node count correctWidth bounded

end PhysicalInterpolationNestedNodeProductTM

namespace PhysicalLagrangeNodeDenominatorNonzero

open scoped BigOperators

open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra
open GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFieldWordSemantics
open GapCVP.PhysicalLagrangeNodeProductAlgebra GapCVP.BinarySourceCoordinateOrder
open GapCVP.Factor400BinaryConstructiveSourcePlaces

private theorem paperVariableArityPhysicalLagrangeNodeEvaluationWord_injective
    (formula : ThreeCNF) :
    Function.Injective
      (physicalLagrangeNodeEvaluationWord formula) := by
  intro first second equal
  apply
    (evaluationWordIndex
      (variableCount_le_fieldWordCount
        (encodeThreeCNF formula).length
        (srcFormula formula))).injective
  apply indexedWord_injective
    (physDegree formula)
  exact equal

private theorem paperVariableArityPhysicalLagrangeNodeEvaluationSourceValue_injective
    (formula : ThreeCNF) :
    Function.Injective
      (fun point : PaperVariableArityPhysicalLagrangeNodeGridIndex formula =>
        sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalLagrangeNodeEvaluationWord
            formula point)) := by
  intro first second equal
  apply paperVariableArityPhysicalLagrangeNodeEvaluationWord_injective formula
  apply paperVariableArityPhysicalSourceWordValue_injective
    (encodeThreeCNF formula).length formula
  exact equal

theorem
    paperVariableArityPhysicalLagrangeNodeEvaluationSourceValue_ne_variableAnchor
    (formula : ThreeCNF)
    (point : PaperVariableArityPhysicalLagrangeNodeGridIndex formula)
    (anchor : Fin (srcFormula formula).variableCount) :
    sourceWordValue (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalLagrangeNodeEvaluationWord
          formula point) ≠
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
        (encodeThreeCNF formula).length
        (srcFormula formula) anchor := by
  rw [physicalLagrangeNodeEvaluationWord_sourceField]
  exact sourceFormulaEvaluationWord_ne_variablePlace
    (encodeThreeCNF formula).length
    (srcFormula formula) point anchor

theorem
    paperVariableArityPhysicalLagrangeNodeEvaluationSourceValue_sub_variableAnchor_ne_zero
    (formula : ThreeCNF)
    (point : PaperVariableArityPhysicalLagrangeNodeGridIndex formula)
    (anchor : Fin (srcFormula formula).variableCount) :
    sourceWordValue (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalLagrangeNodeEvaluationWord
          formula point) -
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
        (encodeThreeCNF formula).length
        (srcFormula formula) anchor ≠ 0 := by
  exact sub_ne_zero.mpr
    (paperVariableArityPhysicalLagrangeNodeEvaluationSourceValue_ne_variableAnchor
      formula point anchor)

private theorem paperVariableArityPhysicalLagrangeDenominatorNodeFactors_sourceField_ne_zero
    (formula : ThreeCNF)
    (count : ℕ)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount)
    (node : Fin count) :
    (∏ other ∈ (Finset.univ.erase node),
      (sourceFormulaEvaluationWord
        (encodeThreeCNF formula).length
        (srcFormula formula)
        (Fin.castLE bounded node) -
        sourceFormulaEvaluationWord
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (Fin.castLE bounded other))) ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro other present
  apply sub_ne_zero.mpr
  intro equal
  have same : Fin.castLE bounded node = Fin.castLE bounded other := by
    apply paperVariableArityPhysicalLagrangeNodeEvaluationSourceValue_injective
      formula
    simpa only
      [physicalLagrangeNodeEvaluationWord_sourceField]
      using equal
  have sameNode : node = other := by
    apply Fin.ext
    exact congrArg
      (fun point : PaperVariableArityPhysicalLagrangeNodeGridIndex formula =>
        point.val) same
  exact (Finset.mem_erase.mp present).1 sameNode.symm

private theorem paperVariableArityPhysicalLagrangeDenominatorNodeProduct_sourceField_ne_zero
    (formula : ThreeCNF)
    (count : ℕ)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount)
    (node : Fin count) :
    sourceWordValue (encodeThreeCNF formula).length
      (srcFormula formula)
      (physicalLagrangeNodeSelectedWordProduct formula
        (physicalLagrangeDenominatorNodeFactorValues
          formula (Fin.castLE bounded node) count)) ≠ 0 := by
  rw [paperVariableArityPhysicalLagrangeDenominatorNodeFactorValues_sourceField]
  exact paperVariableArityPhysicalLagrangeDenominatorNodeFactors_sourceField_ne_zero
    formula count bounded node

private theorem paperVariableArityPhysicalLagrangeDenominatorInverse_sourceField
    (formula : ThreeCNF)
    (count : ℕ)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount)
    (node : Fin count) :
    sourceWordValue (encodeThreeCNF formula).length
      (srcFormula formula)
      (sourceInverseWord
        (physicalLagrangeNodeSelectedWordProduct formula
          (physicalLagrangeDenominatorNodeFactorValues
            formula (Fin.castLE bounded node) count))) =
      (∏ other ∈ (Finset.univ.erase node),
        (sourceFormulaEvaluationWord
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (Fin.castLE bounded node) -
          sourceFormulaEvaluationWord
            (encodeThreeCNF formula).length
            (srcFormula formula)
            (Fin.castLE bounded other)))⁻¹ := by
  rw [sourceWordValue_sourceInverseWord
    (encodeThreeCNF formula).length
    (srcFormula formula)
    (physicalLagrangeNodeSelectedWordProduct formula
      (physicalLagrangeDenominatorNodeFactorValues
        formula (Fin.castLE bounded node) count))
    (paperVariableArityPhysicalLagrangeDenominatorNodeProduct_sourceField_ne_zero
      formula count bounded node)]
  rw [paperVariableArityPhysicalLagrangeDenominatorNodeFactorValues_sourceField]

end PhysicalLagrangeNodeDenominatorNonzero

namespace PhysicalInterpolationNodeWeightTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.SourceFieldMomentOperationsTM GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalLagrangeNodeProductAlgebra GapCVP.PhysicalInterpolationNestedNodeProductTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

private def physicalInterpolationNestedNodeMomentWord
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  physicalFamilyMomentPowerWord family base ∘
    compactPhysicalLagrangeNestedNodeOuterCell

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNestedNodeMomentWordComputable
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalInterpolationNestedNodeMomentWord
        family base) :=
  GapCVP.TMComposition.computableInPolyTime
    compactPhysicalLagrangeNestedNodeOuterCellComputable
    (paperVariableArityPhysicalFamilyMomentPowerComputable family base)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationNestedNodeMomentComputer
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer) :
    SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationNestedNodeMomentWord
    family base
  computer :=
    paperVariableArityPhysicalInterpolationNestedNodeMomentWordComputable
      family base

private theorem paperVariableArityPhysicalInterpolationNestedNodeMomentWord_valid
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer)
    (width : SourceQaryMaskDynamicGridWidth)
    (node row column : ℕ) (formula : ThreeCNF)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (sourceIrreducibleFormulaDegree formula))
    (correctBase : base.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits value) :
    physicalInterpolationNestedNodeMomentWord
      family base
      (compactPhysicalLagrangeNestedNodeEnvelope width node
        (affineCellQuery row column
          (encodeThreeCNF formula))) =
      finiteWordBits
        (sourceWordPow value
          (physicalFamilyRowMoment family row formula)) := by
  unfold physicalInterpolationNestedNodeMomentWord
  rw [Function.comp_apply,
    compactPhysicalLagrangeNestedNodeOuterCell_query]
  exact paperVariableArityPhysicalFamilyMomentPowerWord_valid
    family base row column formula value correctBase

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationNestedDenominatorInverseComputer
    (width : SourceQaryMaskDynamicGridWidth) :
    SourcePhysicalLagrangeWordComputer :=
  paperVariableArityPhysicalInterpolationNestedNodeInverseComputer
    (paperVariableArityPhysicalInterpolationNestedDenominatorNodeProductComputer
      width)

private def paperVariableArityPhysicalInterpolationNodeWeightWord
    (family : Fin 4) (width : SourceQaryMaskDynamicGridWidth)
    (base : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  physicalInterpolationNestedNodeMultiplyWord
    (paperVariableArityPhysicalInterpolationNestedNodeMultiplyComputer
      (paperVariableArityPhysicalInterpolationNestedNumeratorNodeProductComputer
        family width)
      (paperVariableArityPhysicalInterpolationNestedDenominatorInverseComputer
        width))
    (paperVariableArityPhysicalInterpolationNestedNodeMomentComputer
      family base)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalInterpolationNodeWeightWordComputable
    (family : Fin 4) (width : SourceQaryMaskDynamicGridWidth)
    (base : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (paperVariableArityPhysicalInterpolationNodeWeightWord
        family width base) :=
  paperVariableArityPhysicalInterpolationNestedNodeMultiplyWordComputable
    (paperVariableArityPhysicalInterpolationNestedNodeMultiplyComputer
      (paperVariableArityPhysicalInterpolationNestedNumeratorNodeProductComputer
        family width)
      (paperVariableArityPhysicalInterpolationNestedDenominatorInverseComputer
        width))
    (paperVariableArityPhysicalInterpolationNestedNodeMomentComputer
      family base)

private noncomputable def physicalInterpolationNodeWeightComputer
    (family : Fin 4) (width : SourceQaryMaskDynamicGridWidth)
    (base : SourcePhysicalLagrangeWordComputer) :
    SourcePhysicalLagrangeWordComputer where
  output := paperVariableArityPhysicalInterpolationNodeWeightWord
    family width base
  computer := paperVariableArityPhysicalInterpolationNodeWeightWordComputable
    family width base

/-- GapCVP reduction support. -/
def physicalInterpolationNodeWeightSourceWord
    (family : Fin 4) (row : ℕ) (formula : ThreeCNF)
    (count : ℕ)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount)
    (node : Fin count)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula)) :
    GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula) :=
  multiplyMod
    (irreducibleWord (physDegree formula))
    (multiplyMod
      (irreducibleWord (physDegree formula))
      (physicalLagrangeNodeSelectedWordProduct formula
        (physicalLagrangeNumeratorNodeFactorValues
          formula (Fin.castLE bounded node)
          (physicalInterpolationFamilyRowGridPosition
            family row formula) count))
      (sourceInverseWord
        (physicalLagrangeNodeSelectedWordProduct formula
          (physicalLagrangeDenominatorNodeFactorValues
            formula (Fin.castLE bounded node) count))))
    (sourceWordPow value
      (physicalFamilyRowMoment family row formula))

theorem
    paperVariableArityPhysicalInterpolationNestedDenominatorInverseComputer_valid
    (width outerWidth : SourceQaryMaskDynamicGridWidth)
    (row column : ℕ) (formula : ThreeCNF)
    (count : ℕ)
    (correctWidth : width.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate count true)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount)
    (node : Fin count) :
    (paperVariableArityPhysicalInterpolationNestedDenominatorInverseComputer
      width).output
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
        (affineCellQuery row column
          (encodeThreeCNF formula))) =
      finiteWordBits
        (sourceInverseWord
          (physicalLagrangeNodeSelectedWordProduct formula
            (physicalLagrangeDenominatorNodeFactorValues
              formula (Fin.castLE bounded node) count))) := by
  let cell := affineCellQuery row column
    (encodeThreeCNF formula)
  let outer := compactPhysicalLagrangeNestedNodeEnvelope
    outerWidth node.val cell
  let denominator := physicalLagrangeNodeSelectedWordProduct
    formula (physicalLagrangeDenominatorNodeFactorValues
      formula (Fin.castLE bounded node) count)
  have correctDenominator :
      (paperVariableArityPhysicalInterpolationNestedDenominatorNodeProductComputer
        width).output outer = finiteWordBits denominator := by
    change
      physicalInterpolationNestedDenominatorNodeProductWord
        width outer = finiteWordBits denominator
    simpa only [outer, cell, denominator, Fin.val_castLE] using
      paperVariableArityPhysicalInterpolationNestedDenominatorNodeProductWord_valid
        width outerWidth row column formula
        (Fin.castLE bounded node) count correctWidth bounded
  change physicalInterpolationNestedNodeInverseWord
    (paperVariableArityPhysicalInterpolationNestedDenominatorNodeProductComputer
      width) outer = finiteWordBits (sourceInverseWord denominator)
  exact paperVariableArityPhysicalInterpolationNestedNodeInverseWord_valid
    (paperVariableArityPhysicalInterpolationNestedDenominatorNodeProductComputer
      width)
    outerWidth node.val row column formula denominator correctDenominator

end PhysicalInterpolationNodeWeightTM

namespace PhysicalInterpolationNodeWeightCorrectness

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.SourceFieldMomentOperationsTM
open GapCVP.PhysicalInterpolationNodeFactorTM GapCVP.PhysicalLagrangeNodeProductAlgebra
open GapCVP.PhysicalInterpolationNestedNodeProductTM GapCVP.PhysicalInterpolationNodeWeightTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

theorem
    paperVariableArityPhysicalInterpolationNestedNumeratorNodeComputer_valid
    (family : Fin 4)
    (width outerWidth : SourceQaryMaskDynamicGridWidth)
    (row column : ℕ) (formula : ThreeCNF)
    (count : ℕ)
    (correctWidth : width.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate count true)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount)
    (node : Fin count) :
    (paperVariableArityPhysicalInterpolationNestedNumeratorNodeProductComputer
      family width).output
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
        (affineCellQuery row column
          (encodeThreeCNF formula))) =
      finiteWordBits
        (physicalLagrangeNodeSelectedWordProduct formula
          (physicalLagrangeNumeratorNodeFactorValues
            formula (Fin.castLE bounded node)
            (physicalInterpolationFamilyRowGridPosition
              family row formula) count)) := by
  change
    physicalInterpolationNestedNumeratorNodeProductWord
      family width
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
        (affineCellQuery row column
          (encodeThreeCNF formula))) = _
  simpa only [Fin.val_castLE] using
    paperVariableArityPhysicalInterpolationNestedNumeratorNodeProductWord_valid
      family width outerWidth row column formula
      (Fin.castLE bounded node) count correctWidth bounded

private theorem paperVariableArityPhysicalInterpolationNestedNodeMomentComputer_output
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) :
    (paperVariableArityPhysicalInterpolationNestedNodeMomentComputer
      family base).output input =
      physicalInterpolationNestedNodeMomentWord
        family base input := by
  dsimp only [paperVariableArityPhysicalInterpolationNestedNodeMomentComputer]

private theorem paperVariableArityPhysicalInterpolationNestedNodeMomentComputer_valid
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer)
    (width : SourceQaryMaskDynamicGridWidth)
    (node row column : ℕ) (formula : ThreeCNF)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula))
    (correctBase : base.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits value) :
    (paperVariableArityPhysicalInterpolationNestedNodeMomentComputer
      family base).output
      (compactPhysicalLagrangeNestedNodeEnvelope width node
        (affineCellQuery row column
          (encodeThreeCNF formula))) =
      finiteWordBits
        (sourceWordPow value
          (physicalFamilyRowMoment family row formula)) := by
  rw [paperVariableArityPhysicalInterpolationNestedNodeMomentComputer_output]
  exact paperVariableArityPhysicalInterpolationNestedNodeMomentWord_valid
    family base width node row column formula value correctBase

theorem
    paperVariableArityPhysicalInterpolationNestedNumeratorInverseComputer_valid
    (family : Fin 4)
    (width outerWidth : SourceQaryMaskDynamicGridWidth)
    (row column : ℕ) (formula : ThreeCNF)
    (count : ℕ)
    (correctWidth : width.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate count true)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount)
    (node : Fin count) :
    (paperVariableArityPhysicalInterpolationNestedNodeMultiplyComputer
      (paperVariableArityPhysicalInterpolationNestedNumeratorNodeProductComputer
        family width)
      (paperVariableArityPhysicalInterpolationNestedDenominatorInverseComputer
        width)).output
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
        (affineCellQuery row column
          (encodeThreeCNF formula))) =
      finiteWordBits
        (multiplyMod
          (irreducibleWord (physDegree formula))
          (physicalLagrangeNodeSelectedWordProduct formula
            (physicalLagrangeNumeratorNodeFactorValues
              formula (Fin.castLE bounded node)
              (physicalInterpolationFamilyRowGridPosition
                family row formula) count))
          (sourceInverseWord
            (physicalLagrangeNodeSelectedWordProduct formula
              (physicalLagrangeDenominatorNodeFactorValues
                formula (Fin.castLE bounded node) count)))) := by
  change physicalInterpolationNestedNodeMultiplyWord
    (paperVariableArityPhysicalInterpolationNestedNumeratorNodeProductComputer
      family width)
    (paperVariableArityPhysicalInterpolationNestedDenominatorInverseComputer
      width)
    (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
      (affineCellQuery row column
        (encodeThreeCNF formula))) = _
  apply paperVariableArityPhysicalInterpolationNestedNodeMultiplyWord_valid
    (paperVariableArityPhysicalInterpolationNestedNumeratorNodeProductComputer
      family width)
    (paperVariableArityPhysicalInterpolationNestedDenominatorInverseComputer
      width)
    outerWidth node.val row column formula
  · exact
      paperVariableArityPhysicalInterpolationNestedNumeratorNodeComputer_valid
        family width outerWidth row column formula
        count correctWidth bounded node
  · exact
      paperVariableArityPhysicalInterpolationNestedDenominatorInverseComputer_valid
        width outerWidth row column formula count correctWidth bounded node

private theorem paperVariableArityPhysicalInterpolationNodeWeightWord_valid
    (family : Fin 4)
    (width outerWidth : SourceQaryMaskDynamicGridWidth)
    (base : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (count : ℕ)
    (correctWidth : width.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate count true)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount)
    (node : Fin count)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula))
    (correctBase : base.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits value) :
    paperVariableArityPhysicalInterpolationNodeWeightWord family width base
      (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
        (affineCellQuery row column
          (encodeThreeCNF formula))) =
      finiteWordBits
        (physicalInterpolationNodeWeightSourceWord
          family row formula count bounded node value) := by
  let numerator := physicalLagrangeNodeSelectedWordProduct
    formula (physicalLagrangeNumeratorNodeFactorValues
      formula (Fin.castLE bounded node)
      (physicalInterpolationFamilyRowGridPosition
        family row formula) count)
  let denominator := physicalLagrangeNodeSelectedWordProduct
    formula (physicalLagrangeDenominatorNodeFactorValues
      formula (Fin.castLE bounded node) count)
  let moment := sourceWordPow value
    (physicalFamilyRowMoment family row formula)
  change physicalInterpolationNestedNodeMultiplyWord
    (paperVariableArityPhysicalInterpolationNestedNodeMultiplyComputer
      (paperVariableArityPhysicalInterpolationNestedNumeratorNodeProductComputer
        family width)
      (paperVariableArityPhysicalInterpolationNestedDenominatorInverseComputer
        width))
    (paperVariableArityPhysicalInterpolationNestedNodeMomentComputer
      family base)
    (compactPhysicalLagrangeNestedNodeEnvelope outerWidth node.val
      (affineCellQuery row column
        (encodeThreeCNF formula))) =
    finiteWordBits
      (multiplyMod
        (irreducibleWord (physDegree formula))
        (multiplyMod
          (irreducibleWord (physDegree formula))
          numerator (sourceInverseWord denominator)) moment)
  apply paperVariableArityPhysicalInterpolationNestedNodeMultiplyWord_valid
    (paperVariableArityPhysicalInterpolationNestedNodeMultiplyComputer
      (paperVariableArityPhysicalInterpolationNestedNumeratorNodeProductComputer
        family width)
      (paperVariableArityPhysicalInterpolationNestedDenominatorInverseComputer
        width))
    (paperVariableArityPhysicalInterpolationNestedNodeMomentComputer
      family base)
    outerWidth node.val row column formula
  · exact
      paperVariableArityPhysicalInterpolationNestedNumeratorInverseComputer_valid
        family width outerWidth row column formula
        count correctWidth bounded node
  · exact paperVariableArityPhysicalInterpolationNestedNodeMomentComputer_valid
      family base outerWidth node.val row column formula value correctBase

end PhysicalInterpolationNodeWeightCorrectness

namespace PhysicalOrdinaryShiftedCheckBitInstantiation

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryFieldBasis
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalRowBasisDivisionTM
open GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.PhysicalGlobalRefinementCoefficientTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
open GapCVP.SourceFieldMomentOperationsTM GapCVP.PhysicalInterpolationDirectMomentBitTM
open GapCVP.PhysicalOrdinaryShiftedCoefficientSumTM
open GapCVP.PhysicalMaskedInterpolationNodeParityTM GapCVP.PhysicalInterpolationNodeWeightTM
open GapCVP.PhysicalInterpolationNodeWeightCorrectness

private def physicalBooleanOrOutput
    (first second : List Bool → List Bool) : List Bool → List Bool :=
  sourceFourFamilyBooleanOrOutput first second

private noncomputable def paperVariableArityPhysicalBooleanOrComputable
    {first second : List Bool → List Bool}
    (firstComputer : BitTM first)
    (secondComputer : BitTM second) :
    BitTM
      (physicalBooleanOrOutput first second) :=
  sourceFourFamilyBooleanOrComputable firstComputer secondComputer

private theorem paperVariableArityPhysicalBooleanOrOutput_bits
    (first second : List Bool → List Bool)
    (input : List Bool) (firstBit secondBit : Bool)
    (firstCorrect : first input = [firstBit])
    (secondCorrect : second input = [secondBit]) :
    physicalBooleanOrOutput first second input =
      [firstBit || secondBit] :=
  fourFamilyBooleanOrOutput_bits first second input firstBit secondBit
    firstCorrect secondCorrect

/-- GapCVP reduction support. -/
def physicalBooleanXorOutput
    (first second : List Bool → List Bool) : List Bool → List Bool :=
  physicalBooleanOrOutput
    (sourceFourFamilyBooleanAndOutput first
      (sourceFourFamilyBooleanNotOutput second))
    (sourceFourFamilyBooleanAndOutput
      (sourceFourFamilyBooleanNotOutput first) second)

private noncomputable def paperVariableArityPhysicalBooleanXorComputable
    {first second : List Bool → List Bool}
    (firstComputer : BitTM first)
    (secondComputer : BitTM second) :
    BitTM
      (physicalBooleanXorOutput first second) :=
  paperVariableArityPhysicalBooleanOrComputable
    (fourFamilyBooleanAndComputable
      firstComputer
      (fourFamilyBooleanNotOutputComputable secondComputer))
    (fourFamilyBooleanAndComputable
      (fourFamilyBooleanNotOutputComputable firstComputer)
      secondComputer)

private theorem paperVariableArityPhysicalBooleanXorOutput_bits
    (first second : List Bool → List Bool)
    (input : List Bool) (firstBit secondBit : Bool)
    (firstCorrect : first input = [firstBit])
    (secondCorrect : second input = [secondBit]) :
    physicalBooleanXorOutput first second input =
      [Bool.xor firstBit secondBit] := by
  have firstNegation := fourFamilyBooleanNotOutput_bit
    first input firstBit firstCorrect
  have secondNegation := fourFamilyBooleanNotOutput_bit
    second input secondBit secondCorrect
  have leftTerm := fourFamilyBooleanAndOutput_bits
    first (sourceFourFamilyBooleanNotOutput second)
    input firstBit (!secondBit) firstCorrect secondNegation
  have rightTerm := fourFamilyBooleanAndOutput_bits
    (sourceFourFamilyBooleanNotOutput first) second
    input (!firstBit) secondBit firstNegation secondCorrect
  have result := paperVariableArityPhysicalBooleanOrOutput_bits
    (sourceFourFamilyBooleanAndOutput first
      (sourceFourFamilyBooleanNotOutput second))
    (sourceFourFamilyBooleanAndOutput
      (sourceFourFamilyBooleanNotOutput first) second)
    input (firstBit && !secondBit) ((!firstBit) && secondBit)
    leftTerm rightTerm
  change physicalBooleanOrOutput
    (sourceFourFamilyBooleanAndOutput first
      (sourceFourFamilyBooleanNotOutput second))
    (sourceFourFamilyBooleanAndOutput
      (sourceFourFamilyBooleanNotOutput first) second) input = _
  cases firstBit <;> cases secondBit <;> exact result

private noncomputable def physicalInterpolationColumnFieldRankComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalColumnFieldValueRankUnary
  computer := paperVariableArityPhysicalColumnFieldValueRankUnaryComputable

private theorem paperVariableArityPhysicalInterpolationColumnFieldRankComputer_output :
    physicalInterpolationColumnFieldRankComputer.output =
      physicalColumnFieldValueRankUnary := by
  dsimp only [physicalInterpolationColumnFieldRankComputer]

private def physicalInterpolationColumnFieldWord :
    List Bool → List Bool :=
  physicalCellFieldWordAt
    physicalInterpolationColumnFieldRankComputer

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationColumnFieldWordComputable :
    BitTM
      physicalInterpolationColumnFieldWord :=
  physicalCellFieldWordAtComputable
    physicalInterpolationColumnFieldRankComputer

/-- GapCVP reduction support. -/
noncomputable def physicalInterpolationColumnFieldComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationColumnFieldWord
  computer := paperVariableArityPhysicalInterpolationColumnFieldWordComputable

private theorem paperVariableArityPhysicalInterpolationColumnFieldComputer_output :
    physicalInterpolationColumnFieldComputer.output =
      physicalInterpolationColumnFieldWord := by
  dsimp only [physicalInterpolationColumnFieldComputer]

private theorem paperVariableArityPhysicalInterpolationColumnFieldWord_valid
    (row column : ℕ) (formula : ThreeCNF)
    (index : Fin
      (2 ^ sourceIrreducibleFormulaDegree formula))
    (correctIndex : index.val =
      column % physFieldCard formula) :
    physicalInterpolationColumnFieldWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      finiteWordBits
        (indexedWord
          (sourceIrreducibleFormulaDegree formula)
          index) := by
  unfold physicalInterpolationColumnFieldWord
  apply physicalCellFieldWordAt_valid
    physicalInterpolationColumnFieldRankComputer
    row column formula index
  rw [paperVariableArityPhysicalInterpolationColumnFieldRankComputer_output,
    paperVariableArityPhysicalColumnFieldValueRankUnary_query,
    correctIndex]

private def physicalInterpolationFamilyTypeRankUnary
    (family : Fin 4) : List Bool → List Bool :=
  sourcePhysicalComputedUnaryQuotient
    (physicalFamilyRowGridQuotientWord family)
    physicalMomentCellMomentCountUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationFamilyTypeRankUnaryComputable
    (family : Fin 4) :
    BitTM
      (physicalInterpolationFamilyTypeRankUnary family) :=
  sourcePhysicalComputedUnaryQuotientComputable
    (paperVariableArityPhysicalFamilyRowGridQuotientComputable family)
    paperVariableArityPhysicalMomentCellMomentCountUnaryComputable

private theorem paperVariableArityPhysicalInterpolationFamilyTypeRankUnary_valid
    (family : Fin 4) (row column : ℕ) (formula : ThreeCNF) :
    physicalInterpolationFamilyTypeRankUnary family
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        ((((row - physicalFamilyStart family formula) /
          physDegree formula) /
          physGridCard formula) /
          physicalFormulaMomentCount formula) true := by
  exact sourcePhysicalComputedUnaryQuotient_valid
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

/-- GapCVP reduction support. -/
noncomputable def physicalInterpolationFamilyTypeRankComputer
    (family : Fin 4) : SourcePhysicalLagrangeWordComputer where
  output := physicalInterpolationFamilyTypeRankUnary family
  computer :=
    paperVariableArityPhysicalInterpolationFamilyTypeRankUnaryComputable family

/-- GapCVP reduction support. -/
def physicalInterpolationExpectedTypeMatchBit
    (expected : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  physicalCoefficientUnaryEquality
    expected.output physicalColumnTypeRankUnary

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationExpectedTypeMatchBitComputable
    (expected : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalInterpolationExpectedTypeMatchBit expected) :=
  paperVariableArityPhysicalCoefficientUnaryEqualityComputable
    expected.computer paperVariableArityPhysicalColumnTypeRankUnaryComputable

/-- GapCVP reduction support. -/
def physicalInterpolationNodeCorrectionBit
    (family : Fin 4) (width : SourceQaryMaskDynamicGridWidth)
    (base : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  physicalInterpolationNodeParity width
    (paperVariableArityPhysicalMaskedNodeInterpolationBitComputable
      (physicalInterpolationNodeWeightComputer
        family width base))

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalInterpolationNodeCorrectionBitComputable
    (family : Fin 4) (width : SourceQaryMaskDynamicGridWidth)
    (base : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalInterpolationNodeCorrectionBit
        family width base) :=
  paperVariableArityPhysicalInterpolationNodeParityComputable width
    (paperVariableArityPhysicalMaskedNodeInterpolationBitComputable
      (physicalInterpolationNodeWeightComputer
        family width base))

/-- GapCVP reduction support. -/
def physicalInterpolationNodeSourceWord
    (family : Fin 4) (row : ℕ) (formula : ThreeCNF)
    (count : ℕ)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula))
    (node : ℕ) :
    GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula) :=
  if valid : node < count then
    physicalInterpolationNodeWeightSourceWord
      family row formula count bounded ⟨node, valid⟩ value
  else
    fun _ => false

private theorem paperVariableArityPhysicalInterpolationNodeCorrectionBit_valid
    (family : Fin 4) (width : SourceQaryMaskDynamicGridWidth)
    (base : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (count : ℕ)
    (correctWidth : width.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate count true)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula))
    (correctBase : base.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits value) :
    physicalInterpolationNodeCorrectionBit
        family width base
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [((List.range count).map
        (physicalMaskedInterpolationNodeValue
          row column formula
          (physicalInterpolationNodeSourceWord
            family row formula count bounded value))).foldl
          Bool.xor false] := by
  unfold physicalInterpolationNodeCorrectionBit
  apply paperVariableArityPhysicalMaskedInterpolationParity_valid
    width
    (physicalInterpolationNodeWeightComputer
      family width base)
    (affineCellQuery row column
      (encodeThreeCNF formula))
    count
    (physicalMaskedInterpolationNodeValue
      row column formula
      (physicalInterpolationNodeSourceWord
        family row formula count bounded value))
    correctWidth
  intro node member
  have valid : node < count := List.mem_range.mp member
  have actualWeight :
      (physicalInterpolationNodeWeightComputer
        family width base).output
        (GapCVP.BinaryCompactPhysicalLagrangeNestedNodeTM.compactPhysicalLagrangeNestedNodeEnvelope
          width node
          (affineCellQuery row column
            (encodeThreeCNF formula))) =
        finiteWordBits
          (physicalInterpolationNodeWeightSourceWord
            family row formula count bounded ⟨node, valid⟩ value) := by
    dsimp only [physicalInterpolationNodeWeightComputer]
    exact paperVariableArityPhysicalInterpolationNodeWeightWord_valid
      family width width base row column formula count correctWidth
      bounded ⟨node, valid⟩ value correctBase
  simpa only [physicalMaskedInterpolationNodeValue,
    physicalInterpolationNodeSourceWord,
    dite_eq_left valid] using
    paperVariableArityPhysicalMaskedNodeInterpolationBit_valid
      (physicalInterpolationNodeWeightComputer
        family width base)
      width node row column formula
      (physicalInterpolationNodeWeightSourceWord
        family row formula count bounded ⟨node, valid⟩ value)
      actualWeight

/-- GapCVP reduction support. -/
def physicalSourceInterpolationFamilyCheckBit
    (family : Fin 4) (marker : List Bool → List Bool)
    (expected : SourcePhysicalLagrangeWordComputer)
    (width : SourceQaryMaskDynamicGridWidth)
    (base : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput marker
    (sourceFourFamilyBooleanAndOutput
      (physicalInterpolationExpectedTypeMatchBit expected)
      (physicalBooleanXorOutput
        (physicalFamilyDirectMomentBit family base)
        (physicalInterpolationNodeCorrectionBit
          family width base)))

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalSourceInterpolationFamilyCheckBitComputable
    (family : Fin 4) (marker : List Bool → List Bool)
    (markerComputer : BitTM marker)
    (expected : SourcePhysicalLagrangeWordComputer)
    (width : SourceQaryMaskDynamicGridWidth)
    (base : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (physicalSourceInterpolationFamilyCheckBit
        family marker expected width base) :=
  fourFamilyBooleanAndComputable markerComputer
    (fourFamilyBooleanAndComputable
      (paperVariableArityPhysicalInterpolationExpectedTypeMatchBitComputable
        expected)
      (paperVariableArityPhysicalBooleanXorComputable
        (paperVariableArityPhysicalFamilyDirectMomentBitComputable
          family base)
        (paperVariableArityPhysicalInterpolationNodeCorrectionBitComputable
          family width base)))

theorem paperVariableArityPhysicalSourceInterpolationFamilyCheckBit_bits
    (family : Fin 4) (marker : List Bool → List Bool)
    (expected : SourcePhysicalLagrangeWordComputer)
    (width : SourceQaryMaskDynamicGridWidth)
    (base : SourcePhysicalLagrangeWordComputer)
    (input : List Bool)
    (markerBit expectedBit directBit correctionBit : Bool)
    (markerCorrect : marker input = [markerBit])
    (expectedCorrect :
      physicalInterpolationExpectedTypeMatchBit
        expected input = [expectedBit])
    (directCorrect :
      physicalFamilyDirectMomentBit family base input =
        [directBit])
    (correctionCorrect :
      physicalInterpolationNodeCorrectionBit
        family width base input = [correctionBit]) :
    physicalSourceInterpolationFamilyCheckBit
        family marker expected width base input =
      [markerBit &&
        (expectedBit && Bool.xor directBit correctionBit)] := by
  exact fourFamilyBooleanAndOutput_bits
    marker
    (sourceFourFamilyBooleanAndOutput
      (physicalInterpolationExpectedTypeMatchBit expected)
      (physicalBooleanXorOutput
        (physicalFamilyDirectMomentBit family base)
        (physicalInterpolationNodeCorrectionBit
          family width base)))
    input markerBit
    (expectedBit && Bool.xor directBit correctionBit) markerCorrect
    (fourFamilyBooleanAndOutput_bits
      (physicalInterpolationExpectedTypeMatchBit expected)
      (physicalBooleanXorOutput
        (physicalFamilyDirectMomentBit family base)
        (physicalInterpolationNodeCorrectionBit
          family width base))
      input expectedBit (Bool.xor directBit correctionBit)
      expectedCorrect
      (paperVariableArityPhysicalBooleanXorOutput_bits
        (physicalFamilyDirectMomentBit family base)
        (physicalInterpolationNodeCorrectionBit
          family width base)
        input directBit correctionBit directCorrect correctionCorrect))

/-- GapCVP reduction support. -/
def physicalOrdinaryCheckBit : List Bool → List Bool :=
  physicalSourceInterpolationFamilyCheckBit
    (2 : Fin 4)
    physicalOrdinaryRowMarker
    (physicalInterpolationFamilyTypeRankComputer (2 : Fin 4))
    (physicalOrdinaryNodePrefixWidth
      physicalOrdinaryInterpolationMomentComputer)
    physicalInterpolationColumnFieldComputer

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalOrdinaryCheckBitComputable :
    BitTM
      physicalOrdinaryCheckBit :=
  paperVariableArityPhysicalSourceInterpolationFamilyCheckBitComputable
    (2 : Fin 4)
    physicalOrdinaryRowMarker
    paperVariableArityPhysicalOrdinaryRowMarkerComputable
    (physicalInterpolationFamilyTypeRankComputer (2 : Fin 4))
    (physicalOrdinaryNodePrefixWidth
      physicalOrdinaryInterpolationMomentComputer)
    physicalInterpolationColumnFieldComputer

end PhysicalOrdinaryShiftedCheckBitInstantiation

namespace BinaryPhysicalLagrangeParityEntry

open scoped BigOperators

open Polynomial GapCVP.BinaryReedSolomonParity

theorem constructiveParityMatrix_apply_eq_orderedNodeProducts
    {K : Type*} [Field K]
    {gridCardinality degreeBound : ℕ}
    (points : Fin gridCardinality → K)
    (hdegree : degreeBound < gridCardinality)
    (row column : Fin gridCardinality) :
    constructiveParityMatrix points hdegree row column =
      (if row = column then (1 : K) else 0) -
        ∑ node : Fin (degreeBound + 1),
          (if Fin.castLE (Nat.succ_le_of_lt hdegree) node = column
            then (1 : K) else 0) *
            ∏ other ∈ (Finset.univ.erase node),
              (points
                  (Fin.castLE (Nat.succ_le_of_lt hdegree) node) -
                points
                  (Fin.castLE (Nat.succ_le_of_lt hdegree) other))⁻¹ *
                (points row -
                  points
                    (Fin.castLE (Nat.succ_le_of_lt hdegree) other)) := by
  classical
  simp only [constructiveParityMatrix, LinearMap.toMatrix'_apply,
      constructiveParityLinearMap_apply,
      Pi.single_apply, orderedInterpolationPolynomial, orderedInterpolationPrefix,
          Nat.succ_eq_add_one, LinearMap.coe_mk,
      AddHom.coe_mk, Lagrange.interpolate_apply, MonoidWithZeroHom.map_ite_one_zero,
          Lagrange.basis,
      Lagrange.basisDivisor, orderedInterpolationNode, ite_mul, one_mul, zero_mul, eval_finsetSum,
          sub_right_inj]
  apply Finset.sum_congr rfl
  intro node _
  split_ifs with hnode
  · simp only [eval_prod, eval_mul, eval_C, eval_sub, eval_X]
  · simp only [eval_zero]

end BinaryPhysicalLagrangeParityEntry

namespace PhysicalSelectedInterpolationCoefficientProjection

open scoped BigOperators

open GapCVP.Core GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryReedSolomonParity
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.PhysicalColumnOrder
open GapCVP.MatrixEntrySemantics

attribute [local instance] Classical.propDecidable

@[simp] private theorem paperVariableArityPhysicalWordCoordinateDelta_eq_selectedCoordinate
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
  simp only [physicalWordCoordinateDelta, physicalCoordinateIndex, Equiv.symm_apply_eq]

private theorem paperVariableArityPhysicalWordCoordinateDelta_sum_field
    (encodingLength : ℕ) (formula : ThreeCNF)
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula))
    (tableType : sourceSATTableType
      (srcFormula formula))
    (point : sourceSATGridPoint
      (PaperVariableArityPhysicalWordGrid encodingLength formula))
    (weight : PaperVariableArityPhysicalWordField encodingLength formula →
      PaperVariableArityPhysicalWordField encodingLength formula) :
    ∑ value : PaperVariableArityPhysicalWordField
      encodingLength formula,
      physicalWordCoordinateDelta
        encodingLength formula column tableType point value *
          weight value =
      if tableType =
          (sourceCoordinateWordOrder
            encodingLength formula column).1 ∧
        point =
          (sourceCoordinateWordOrder
            encodingLength formula column).2.1
      then weight
        (sourceCoordinateWordOrder
          encodingLength formula column).2.2
      else 0 := by
  classical
  simp_rw [paperVariableArityPhysicalWordCoordinateDelta_eq_selectedCoordinate]
  by_cases htype :
      tableType =
        (sourceCoordinateWordOrder
          encodingLength formula column).1
  · by_cases hpoint :
        point =
          (sourceCoordinateWordOrder
            encodingLength formula column).2.1
    · subst tableType
      subst point
      simp only [Prod.ext_iff, true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ,
          ↓reduceIte, and_self]
    · simp only [Prod.ext_iff, hpoint, false_and, and_false, ↓reduceIte, zero_mul,
        Finset.sum_const_zero]
  · simp only [Prod.ext_iff, htype, false_and, ↓reduceIte, zero_mul, Finset.sum_const_zero]

private theorem paperVariableArityPhysicalWordCoordinateDelta_sum_dependentOrderedGrid
    (encodingLength : ℕ) (formula : ThreeCNF)
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula))
    (tableType : sourceSATTableType
      (srcFormula formula))
    {gridCardinality : ℕ}
    (gridOrder : Fin gridCardinality ≃
      sourceSATGridPoint
        (PaperVariableArityPhysicalWordGrid encodingLength formula))
    (parity : Fin gridCardinality →
      PaperVariableArityPhysicalWordField encodingLength formula)
    (weight : Fin gridCardinality →
      PaperVariableArityPhysicalWordField encodingLength formula →
      PaperVariableArityPhysicalWordField encodingLength formula) :
    (∑ position : Fin gridCardinality,
      parity position *
        ∑ value : PaperVariableArityPhysicalWordField
          encodingLength formula,
          physicalWordCoordinateDelta
            encodingLength formula column tableType
              (gridOrder position) value * weight position value) =
      if tableType =
          (sourceCoordinateWordOrder
            encodingLength formula column).1
      then parity
        (gridOrder.symm
          (sourceCoordinateWordOrder
            encodingLength formula column).2.1) *
        weight
          (gridOrder.symm
            (sourceCoordinateWordOrder
              encodingLength formula column).2.1)
          (sourceCoordinateWordOrder
            encodingLength formula column).2.2
      else 0 := by
  classical
  simp_rw [paperVariableArityPhysicalWordCoordinateDelta_sum_field]
  by_cases htype :
      tableType =
        (sourceCoordinateWordOrder
          encodingLength formula column).1
  · subst tableType
    simp only [(gridOrder.eq_symm_apply).symm, true_and, mul_ite, mul_zero,
        Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
  · simp only [htype, false_and, ↓reduceIte, mul_zero, Finset.sum_const_zero]

private theorem paperVariableArityPhysicalWordOrdinaryFieldCoefficient_eq_selectedCoordinate
    (encodingLength : ℕ) (formula : ThreeCNF)
    (tableType : sourceSATTableType
      (srcFormula formula))
    (moment : Fin
      (explicitMomentBudget encodingLength
        (srcFormula formula) + 1))
    (row : Fin (Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula))))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    physicalWordFamilyFieldCoefficient
      encodingLength formula
        (.inr (.inr (.inl (tableType, moment)))) row column =
      if tableType =
          (sourceCoordinateWordOrder
            encodingLength formula column).1
      then
        constructiveParityMatrix
          (fun index =>
            (sourceFormulaExplicitGridOrder encodingLength
              (srcFormula formula) index).val)
          (explicitOrdinaryDegree_lt_grid encodingLength
            (srcFormula formula) moment)
          row
          ((sourceFormulaExplicitGridOrder encodingLength
            (srcFormula formula)).symm
              (sourceCoordinateWordOrder
                encodingLength formula column).2.1) *
          (sourceCoordinateWordOrder
            encodingLength formula column).2.2 ^ moment.val
      else 0 := by
  rw [paperVariableArityPhysicalWordOrdinaryFieldCoefficient]
  exact paperVariableArityPhysicalWordCoordinateDelta_sum_dependentOrderedGrid
    encodingLength formula column tableType
    (sourceFormulaExplicitGridOrder encodingLength
      (srcFormula formula))
    (fun position =>
      constructiveParityMatrix
        (fun index =>
          (sourceFormulaExplicitGridOrder encodingLength
            (srcFormula formula) index).val)
        (explicitOrdinaryDegree_lt_grid encodingLength
          (srcFormula formula) moment)
        row position)
    (fun _ value => value ^ moment.val)

theorem paperVariableArityPhysicalWordShiftedFieldCoefficient_eq_selectedCoordinate
    (encodingLength : ℕ) (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length)
    (tuple : ((srcFormula
      formula).clauses.get clause).SatisfyingLocalTuple)
    (localVariable : ((srcFormula
      formula).clauses.get clause).LocalVariable)
    (moment : Fin
      (explicitMomentBudget encodingLength
        (srcFormula formula) + 1))
    (row : Fin (Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula))))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    physicalWordFamilyFieldCoefficient
      encodingLength formula
        (.inr (.inr (.inr
          ⟨clause, tuple, localVariable, moment⟩))) row column =
      if (Sum.inr ⟨clause, tuple⟩ :
          sourceSATTableType (srcFormula formula)) =
          (sourceCoordinateWordOrder
            encodingLength formula column).1
      then
        constructiveParityMatrix
          (fun index =>
            (sourceFormulaExplicitGridOrder encodingLength
              (srcFormula formula) index).val)
          (explicitShiftedDegree_lt_grid encodingLength
            (srcFormula formula) moment)
          row
          ((sourceFormulaExplicitGridOrder encodingLength
            (srcFormula formula)).symm
              (sourceCoordinateWordOrder
                encodingLength formula column).2.1) *
          (((sourceCoordinateWordOrder
              encodingLength formula column).2.2 -
            sourceSATFieldBit
              (K := PaperVariableArityPhysicalWordField
                encodingLength formula)
              (tuple.val localVariable)) /
            ((sourceCoordinateWordOrder
              encodingLength formula column).2.1.val -
              GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
                encodingLength (srcFormula formula)
                localVariable.val)) ^ moment.val
      else 0 := by
  rw [paperVariableArityPhysicalWordShiftedFieldCoefficient]
  simpa only [Equiv.apply_symm_apply] using
    paperVariableArityPhysicalWordCoordinateDelta_sum_dependentOrderedGrid
      encodingLength formula column
      (Sum.inr ⟨clause, tuple⟩ :
        sourceSATTableType (srcFormula formula))
      (sourceFormulaExplicitGridOrder encodingLength
        (srcFormula formula))
      (fun position =>
        constructiveParityMatrix
          (fun index =>
            (sourceFormulaExplicitGridOrder encodingLength
              (srcFormula formula) index).val)
          (explicitShiftedDegree_lt_grid encodingLength
            (srcFormula formula) moment)
          row position)
      (fun position value =>
        ((value -
            sourceSATFieldBit
              (K := PaperVariableArityPhysicalWordField
                encodingLength formula)
              (tuple.val localVariable)) /
          ((sourceFormulaExplicitGridOrder encodingLength
            (srcFormula formula) position).val -
            GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
              encodingLength (srcFormula formula)
              localVariable.val)) ^ moment.val)

end PhysicalSelectedInterpolationCoefficientProjection

namespace PhysicalInterpolationNodeParitySemanticCorrectness

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField

private theorem paperVariableArityPhysicalBoolXorFold_bitValue_aux
    (bits : List Bool) (initial : Bool) :
    bitValue (bits.foldl Bool.xor initial) =
      bitValue initial + (bits.map bitValue).sum := by
  induction bits generalizing initial with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons bit remaining ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, bitValue_xor]
      simp only [add_assoc]

private theorem paperVariableArityPhysicalBoolXorFold_bitValue
    (bits : List Bool) :
    bitValue (bits.foldl Bool.xor false) =
      (bits.map bitValue).sum := by
  simpa only [bitValue, Bool.false_eq_true, ↓reduceIte, zero_add] using
      paperVariableArityPhysicalBoolXorFold_bitValue_aux bits false

end PhysicalInterpolationNodeParitySemanticCorrectness

namespace PhysicalMaskedInterpolationNodeParitySemanticCorrectness

open GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.BinaryCompactPhysicalFieldBasisCoordinates GapCVP.BinaryFieldInverseAlgebra
open GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationNodeParitySemanticCorrectness
open GapCVP.PhysicalOrdinaryShiftedCoefficientTM

private theorem paperVariableArityPhysicalFiniteMaskedBasisBitParity_sourceField
    (formula : ThreeCNF)
    (terms : List
      (Bool × PaperVariableArityPhysicalInterpolationWord formula))
    (index : Fin (physDegree formula)) :
    (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
      (encodeThreeCNF formula).length
      (srcFormula formula)).equivFun
        ((terms.map (fun term =>
          if term.1 then
            sourceWordValue (encodeThreeCNF formula).length
              (srcFormula formula) term.2
          else 0)).sum) index =
      bitValue
        ((terms.map (fun term => term.1 && term.2 index)).foldl
          Bool.xor false) := by
  rw [paperVariableArityPhysicalBoolXorFold_bitValue]
  induction terms with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      rw [map_zero]
      rfl
  | cons term remaining ih =>
      rcases term with ⟨mask, word⟩
      cases mask
      · simpa only [List.map_cons, Bool.false_eq_true, ↓reduceIte, List.sum_cons, zero_add,
            Module.Basis.equivFun_apply, Bool.false_and, bitValue, List.map_map] using ih
      · simp only [List.map_cons, List.sum_cons, Bool.true_and, ↓reduceIte]
        rw [map_add]
        change
          (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
            (encodeThreeCNF formula).length
            (srcFormula formula)).equivFun
              (sourceWordValue (encodeThreeCNF formula).length
                (srcFormula formula) word) index +
            (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
              (encodeThreeCNF formula).length
              (srcFormula formula)).equivFun
                ((remaining.map (fun item =>
                  if item.1 then
                    sourceWordValue (encodeThreeCNF formula).length
                      (srcFormula formula) item.2
                  else 0)).sum) index =
            bitValue (word index) +
              ((remaining.map
                (fun item => item.1 && item.2 index)).map bitValue).sum
        rw [ih]
        exact congrArg (fun value =>
          value + ((remaining.map
            (fun item => item.1 && item.2 index)).map bitValue).sum)
          (sourceFormulaFieldBasis_sourceWordValue_coordinate
            (encodeThreeCNF formula).length
            (srcFormula formula) word index)

private theorem paperVariableArityPhysicalFiniteMaskedBasisBitParity_decide
    (formula : ThreeCNF)
    (terms : List
      (Bool × PaperVariableArityPhysicalInterpolationWord formula))
    (index : Fin (physDegree formula)) :
    ((terms.map (fun term => term.1 && term.2 index)).foldl
      Bool.xor false) =
      decide
        ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
          (encodeThreeCNF formula).length
          (srcFormula formula)).equivFun
            ((terms.map (fun term =>
              if term.1 then
                sourceWordValue (encodeThreeCNF formula).length
                  (srcFormula formula) term.2
              else 0)).sum) index = (1 : ZMod 2)) := by
  rw [paperVariableArityPhysicalFiniteMaskedBasisBitParity_sourceField]
  generalize
    ((terms.map (fun term => term.1 && term.2 index)).foldl
      Bool.xor false) = bit
  cases bit <;> decide

private theorem paperVariableArityPhysicalMaskedGridNodeBasisParity_decide
    (formula : ThreeCNF) (count grid : ℕ)
    (index : Fin (physDegree formula))
    (word : ℕ → PaperVariableArityPhysicalInterpolationWord formula) :
    (((List.range count).map (fun node =>
      decide (node = grid) && word node index)).foldl
        Bool.xor false) =
      decide
        ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
          (encodeThreeCNF formula).length
          (srcFormula formula)).equivFun
            (((List.range count).map (fun node =>
              if node = grid then
                sourceWordValue (encodeThreeCNF formula).length
                  (srcFormula formula) (word node)
              else 0)).sum) index = (1 : ZMod 2)) := by
  have actual := paperVariableArityPhysicalFiniteMaskedBasisBitParity_decide
    formula
    ((List.range count).map
      (fun node => (decide (node = grid), word node))) index
  simpa only [List.map_map, Function.comp_def,
    Prod.fst, Prod.snd, decide_eq_true_eq] using actual

end PhysicalMaskedInterpolationNodeParitySemanticCorrectness

namespace PhysicalInterpolationNodeWeightSourceFieldCorrectness

open scoped BigOperators

open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryFieldInverseAlgebra GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalInterpolationNodeWeightTM GapCVP.PhysicalLagrangeNodeDenominatorNonzero
open GapCVP.PhysicalLagrangeNodeProductAlgebra GapCVP.SourceFieldMomentOperationsTM
open GapCVP.BinarySourceCoordinateOrder

theorem paperVariableArityPhysicalInterpolationNodeWeightSourceWord_sourceField
    (family : Fin 4)
    (row : ℕ)
    (formula : ThreeCNF)
    (count : ℕ)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount)
    (node : Fin count)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula)) :
    sourceWordValue (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalInterpolationNodeWeightSourceWord
          family row formula count bounded node value) =
      (∏ other ∈ (Finset.univ.erase node),
        (sourceFormulaEvaluationWord
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalInterpolationFamilyRowGridPosition
            family row formula) -
          sourceFormulaEvaluationWord
            (encodeThreeCNF formula).length
            (srcFormula formula)
            (Fin.castLE bounded other))) *
      (∏ other ∈ (Finset.univ.erase node),
        (sourceFormulaEvaluationWord
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (Fin.castLE bounded node) -
          sourceFormulaEvaluationWord
            (encodeThreeCNF formula).length
            (srcFormula formula)
            (Fin.castLE bounded other)))⁻¹ *
      sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula) value ^
        physicalFamilyRowMoment family row formula := by
  unfold physicalInterpolationNodeWeightSourceWord
  rw [sourceWordValue_multiplyMod, sourceWordValue_multiplyMod,
    paperVariableArityPhysicalLagrangeNumeratorNodeFactorValues_sourceField,
    paperVariableArityPhysicalLagrangeDenominatorInverse_sourceField,
    sourceWordValue_sourceWordPow]

end PhysicalInterpolationNodeWeightSourceFieldCorrectness

namespace PhysicalOrdinaryShiftedCheckBitInstantiation

open Turing GapCVP.Core GapCVP.BinaryEncoding
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalMaskedInterpolationNodeParitySemanticCorrectness

theorem paperVariableArityPhysicalInterpolationNodeCorrectionBit_sourceField_valid
    (family : Fin 4) (width : SourceQaryMaskDynamicGridWidth)
    (base : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (count : ℕ)
    (correctWidth : width.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate count true)
    (bounded : count ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula))
    (correctBase : base.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits value) :
    physicalInterpolationNodeCorrectionBit
        family width base
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
          (encodeThreeCNF formula).length
          (srcFormula formula)).equivFun
            (((List.range count).map (fun node =>
              if node =
                (column /
                  physFieldCard formula) %
                  physGridCard formula
              then
                sourceWordValue (encodeThreeCNF formula).length
                  (srcFormula formula)
                  (physicalInterpolationNodeSourceWord
                    family row formula count bounded value node)
              else 0)).sum)
              (physicalInterpolationRowBasisIndex
                row formula) = (1 : ZMod 2))] := by
  calc
    physicalInterpolationNodeCorrectionBit
        family width base
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
        [((List.range count).map
          (physicalMaskedInterpolationNodeValue
            row column formula
            (physicalInterpolationNodeSourceWord
              family row formula count bounded value))).foldl
                Bool.xor false] :=
      paperVariableArityPhysicalInterpolationNodeCorrectionBit_valid
        family width base row column formula count correctWidth bounded
        value correctBase
    _ = _ := by
      congr 1
      change
        (((List.range count).map (fun node =>
          decide
            (node =
              (column /
                physFieldCard formula) %
                  physGridCard formula) &&
            physicalInterpolationNodeSourceWord
              family row formula count bounded value node
                (physicalInterpolationRowBasisIndex
                  row formula))).foldl Bool.xor false) = _
      exact paperVariableArityPhysicalMaskedGridNodeBasisParity_decide
        formula count
        ((column /
          physFieldCard formula) %
            physGridCard formula)
        (physicalInterpolationRowBasisIndex row formula)
        (physicalInterpolationNodeSourceWord
          family row formula count bounded value)

end PhysicalOrdinaryShiftedCheckBitInstantiation

namespace ShiftedTupleBetaTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert
open GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceIndexedClauseLookupTM GapCVP.SourceIndexedClauseSignTM
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalRowBasisDivisionTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingTM
open GapCVP.SourcePreprocessingSemantics GapCVP.ClauseOffsetTM

/-- GapCVP reduction support. -/
structure PaperVariableArityShiftedTupleRankComputers where
  /-- GapCVP reduction support. -/
  clause : SourcePhysicalLagrangeWordComputer
  /-- GapCVP reduction support. -/
  tuple : SourcePhysicalLagrangeWordComputer
  /-- GapCVP reduction support. -/
  variablePosition : SourcePhysicalLagrangeWordComputer

private def paperShiftedTupleRetainedSource :
    List Bool → List Bool :=
  paperPreprocessingFilteredFormulaWord ∘
    sourceExplicitAffineCellOriginalSource

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleRetainedSourceComputable :
    BitTM
      paperShiftedTupleRetainedSource :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    paperSourcePreprocessingFilteredFormulaWordComputable

@[simp] private theorem paperVariableArityShiftedTupleRetainedSource_query
    (row column : ℕ) (formula : ThreeCNF) :
    paperShiftedTupleRetainedSource
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      encodeThreeCNF (noTautClauses formula) := by
  unfold paperShiftedTupleRetainedSource
  rw [Function.comp_apply,
    sourceExplicitAffineCellOriginalSource_query,
    paperSourcePreprocessingFilteredFormulaWord_valid]

private def paperVariableArityShiftedTupleClauseQuery
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (input : List Bool) : List Bool :=
  ranks.clause.output input ++
    false :: paperShiftedTupleRetainedSource input

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleClauseQueryComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperVariableArityShiftedTupleClauseQuery ranks) := by
  have retained := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityShiftedTupleRetainedSourceComputable
    (prependBitComputable false)
  exact pointwiseAppendComputable ranks.clause.computer retained

private def paperShiftedTupleOriginalClauseWord
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  sourceOriginalIndexedClauseOutput ∘
    paperVariableArityShiftedTupleClauseQuery ranks

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleOriginalClauseWordComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperShiftedTupleOriginalClauseWord ranks) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityShiftedTupleClauseQueryComputable ranks)
    sourceOriginalIndexedClauseComputable

private theorem paperShiftedTupleOriginalClauseWord_query
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (hrank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true) :
    paperShiftedTupleOriginalClauseWord ranks
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      encodeThreeClause
        ((noTautClauses formula).get
          ⟨rank, hbound⟩) := by
  unfold paperShiftedTupleOriginalClauseWord
    paperVariableArityShiftedTupleClauseQuery
  rw [Function.comp_apply, hrank,
    paperVariableArityShiftedTupleRetainedSource_query]
  exact sourceOriginalIndexedClauseOutput_valid
    rank (noTautClauses formula) hbound

/-- GapCVP reduction support. -/
def paperShiftedTupleNormalizedArityUnary
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  paperVariableArityClauseArityUnary ∘
    paperShiftedTupleOriginalClauseWord ranks

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleNormalizedArityUnaryComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperShiftedTupleNormalizedArityUnary ranks) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityShiftedTupleOriginalClauseWordComputable ranks)
    paperClauseArityUnaryComputable

theorem paperVariableArityShiftedTupleNormalizedArityUnary_query
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (hrank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true) :
    paperShiftedTupleNormalizedArityUnary ranks
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      List.replicate
        (paperSourceNormalizedClause
          ((noTautClauses formula).get
            ⟨rank, hbound⟩)).length true := by
  unfold paperShiftedTupleNormalizedArityUnary
  rw [Function.comp_apply,
    paperShiftedTupleOriginalClauseWord_query
      ranks row column formula rank hbound hrank]
  simpa only [List.append_nil] using
    (paperVariableArityClauseArityUnary_valid
      ((noTautClauses formula).get
        ⟨rank, hbound⟩) [])

/-- GapCVP reduction support. -/
def paperShiftedTupleGuardedSourceWord
    (marker selected : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  markerConditionalOutput selected [] (marker input ++ input)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleGuardedSourceWordComputable
    {marker selected : List Bool → List Bool}
    (hmarker : BitTM marker)
    (hselected : BitTM selected) :
    BitTM
      (paperShiftedTupleGuardedSourceWord marker selected) := by
  have archived := pointwiseAppendComputable hmarker
    (Turing.idComputableInPolyTime bitEncoding)
  exact GapCVP.TMComposition.computableInPolyTime
    archived (markerConditionalComputable hselected [])

theorem paperShiftedTupleGuardedSourceWord_valid
    (marker selected : List Bool → List Bool)
    (input : List Bool) (bit : Bool)
    (hmarker : marker input = [bit]) :
    paperShiftedTupleGuardedSourceWord
      marker selected input =
      if bit then selected input else [] := by
  unfold paperShiftedTupleGuardedSourceWord
  rw [hmarker]
  cases bit <;> rfl

/-- GapCVP reduction support. -/
def paperShiftedTupleConstantUnary
    (value : ℕ) : List Bool → List Bool :=
  fun _ => List.replicate value true

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleConstantUnaryComputable
    (value : ℕ) :
    BitTM
      (paperShiftedTupleConstantUnary value) :=
  sourceFixedWordComputable (List.replicate value true)

private def paperShiftedTupleOriginalSignWord
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) : List Bool → List Bool :=
  paperSourceClauseSignWord position ∘
    paperShiftedTupleOriginalClauseWord ranks

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleOriginalSignWordComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) :
    BitTM
      (paperShiftedTupleOriginalSignWord ranks position) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityShiftedTupleOriginalClauseWordComputable ranks)
    (paperSourceClauseSignWordComputable position)

private def paperShiftedTupleOriginalSecondKeepBit
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  paperSourceClauseSecondKeepMarker ∘
    paperShiftedTupleOriginalClauseWord ranks

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleOriginalSecondKeepBitComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperShiftedTupleOriginalSecondKeepBit ranks) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityShiftedTupleOriginalClauseWordComputable ranks)
    paperSourceClauseSecondKeepMarkerComputable

private def paperShiftedTupleSelectedSourceBit
    (marker first second : List Bool → List Bool) :
    List Bool → List Bool :=
  sourceFourFamilyBooleanOrOutput
    (sourceFourFamilyBooleanAndOutput marker first)
    (sourceFourFamilyBooleanAndOutput
      (sourceFourFamilyBooleanNotOutput marker) second)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleSelectedSourceBitComputable
    {marker first second : List Bool → List Bool}
    (hmarker : BitTM marker)
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (paperShiftedTupleSelectedSourceBit
        marker first second) :=
  sourceFourFamilyBooleanOrComputable
    (fourFamilyBooleanAndComputable hmarker hfirst)
    (fourFamilyBooleanAndComputable
      (fourFamilyBooleanNotOutputComputable hmarker) hsecond)

private theorem paperVariableArityShiftedTupleSelectedSourceBit_valid
    (marker first second : List Bool → List Bool)
    (input : List Bool) (selector firstBit secondBit : Bool)
    (hselector : marker input = [selector])
    (hfirst : first input = [firstBit])
    (hsecond : second input = [secondBit]) :
    paperShiftedTupleSelectedSourceBit
      marker first second input =
      [if selector then firstBit else secondBit] := by
  have hnot := fourFamilyBooleanNotOutput_bit
    marker input selector hselector
  have hleft := fourFamilyBooleanAndOutput_bits
    marker first input selector firstBit hselector hfirst
  have hright := fourFamilyBooleanAndOutput_bits
    (sourceFourFamilyBooleanNotOutput marker) second input
    (!selector) secondBit hnot hsecond
  unfold paperShiftedTupleSelectedSourceBit
  have selected := fourFamilyBooleanOrOutput_bits
    (sourceFourFamilyBooleanAndOutput marker first)
    (sourceFourFamilyBooleanAndOutput
      (sourceFourFamilyBooleanNotOutput marker) second)
    input (selector && firstBit) ((!selector) && secondBit)
    hleft hright
  cases selector <;> simpa using selected

private def paperShiftedTupleNormalizedSignWord
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) : List Bool → List Bool :=
  if position.val = 0 then
    paperShiftedTupleOriginalSignWord ranks 0
  else if position.val = 1 then
    paperShiftedTupleSelectedSourceBit
      (paperShiftedTupleOriginalSecondKeepBit ranks)
      (paperShiftedTupleOriginalSignWord ranks 1)
      (paperShiftedTupleOriginalSignWord ranks 2)
  else
    paperShiftedTupleOriginalSignWord ranks 2

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleNormalizedSignWordComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) :
    BitTM
      (paperShiftedTupleNormalizedSignWord ranks position) := by
  unfold paperShiftedTupleNormalizedSignWord
  split
  · exact paperVariableArityShiftedTupleOriginalSignWordComputable
      ranks 0
  next =>
    split
    · exact paperVariableArityShiftedTupleSelectedSourceBitComputable
        (paperVariableArityShiftedTupleOriginalSecondKeepBitComputable ranks)
        (paperVariableArityShiftedTupleOriginalSignWordComputable ranks 1)
        (paperVariableArityShiftedTupleOriginalSignWordComputable ranks 2)
    · exact paperVariableArityShiftedTupleOriginalSignWordComputable
        ranks 2

private def paperShiftedTupleNormalizedPositionBit
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) : List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    (paperShiftedTupleConstantUnary position.val)
    (paperShiftedTupleNormalizedArityUnary ranks)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleNormalizedPositionBitComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) :
    BitTM
      (paperShiftedTupleNormalizedPositionBit ranks position) :=
  fourFamilyComputedUnaryLessBitComputable
    (paperVariableArityShiftedTupleConstantUnaryComputable position.val)
    (paperVariableArityShiftedTupleNormalizedArityUnaryComputable ranks)

private def paperShiftedTupleRejectedPositionBit
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    (paperShiftedTupleNormalizedPositionBit ranks position)
    (sourceFourFamilyBooleanNotOutput
      (paperShiftedTupleNormalizedSignWord ranks position))

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleRejectedPositionBitComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) :
    BitTM
      (paperShiftedTupleRejectedPositionBit ranks position) :=
  fourFamilyBooleanAndComputable
    (paperVariableArityShiftedTupleNormalizedPositionBitComputable
      ranks position)
    (fourFamilyBooleanNotOutputComputable
      (paperVariableArityShiftedTupleNormalizedSignWordComputable
        ranks position))

private theorem paperVariableArityShiftedTupleRejectedPositionBit_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3)
    (input : List Bool) (present sign : Bool)
    (hpresent : paperShiftedTupleNormalizedPositionBit
      ranks position input = [present])
    (hsign : paperShiftedTupleNormalizedSignWord
      ranks position input = [sign]) :
    paperShiftedTupleRejectedPositionBit
      ranks position input = [present && !sign] := by
  unfold paperShiftedTupleRejectedPositionBit
  exact fourFamilyBooleanAndOutput_bits
    (paperShiftedTupleNormalizedPositionBit ranks position)
    (sourceFourFamilyBooleanNotOutput
      (paperShiftedTupleNormalizedSignWord ranks position))
    input present (!sign) hpresent
    (fourFamilyBooleanNotOutput_bit
      (paperShiftedTupleNormalizedSignWord ranks position)
      input sign hsign)

private def paperShiftedTupleRejectedWeightedUnary
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) : List Bool → List Bool :=
  paperShiftedTupleGuardedSourceWord
    (paperShiftedTupleRejectedPositionBit ranks position)
    (paperShiftedTupleConstantUnary (2 ^ position.val))

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleRejectedWeightedUnaryComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) :
    BitTM
      (paperShiftedTupleRejectedWeightedUnary
        ranks position) :=
  paperVariableArityShiftedTupleGuardedSourceWordComputable
    (paperVariableArityShiftedTupleRejectedPositionBitComputable
      ranks position)
    (paperVariableArityShiftedTupleConstantUnaryComputable
      (2 ^ position.val))

private theorem paperVariableArityShiftedTupleRejectedWeightedUnary_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) (input : List Bool)
    (present sign : Bool)
    (hpresent : paperShiftedTupleNormalizedPositionBit
      ranks position input = [present])
    (hsign : paperShiftedTupleNormalizedSignWord
      ranks position input = [sign]) :
    paperShiftedTupleRejectedWeightedUnary
      ranks position input =
      List.replicate
        (if present && !sign then 2 ^ position.val else 0) true := by
  unfold paperShiftedTupleRejectedWeightedUnary
  rw [paperShiftedTupleGuardedSourceWord_valid
    (paperShiftedTupleRejectedPositionBit ranks position)
    (paperShiftedTupleConstantUnary (2 ^ position.val))
    input (present && !sign)
    (paperVariableArityShiftedTupleRejectedPositionBit_valid
      ranks position input present sign hpresent hsign)]
  cases present <;> cases sign <;>
    simp [paperShiftedTupleConstantUnary]

private def paperShiftedTupleRejectedRankUnary
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    (fourFamilyComputedUnarySumOutput
      (paperShiftedTupleRejectedWeightedUnary ranks 0)
      (paperShiftedTupleRejectedWeightedUnary ranks 1))
    (paperShiftedTupleRejectedWeightedUnary ranks 2)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleRejectedRankUnaryComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperShiftedTupleRejectedRankUnary ranks) :=
  fourFamilyComputedUnarySumComputable
    (fourFamilyComputedUnarySumComputable
      (paperVariableArityShiftedTupleRejectedWeightedUnaryComputable
        ranks 0)
      (paperVariableArityShiftedTupleRejectedWeightedUnaryComputable
        ranks 1))
    (paperVariableArityShiftedTupleRejectedWeightedUnaryComputable
      ranks 2)

/-- GapCVP reduction support. -/
def paperShiftedTupleRejectedNatural
    (arity : ℕ) (sign : Fin 3 → Bool) : ℕ :=
  (if 0 < arity && !(sign 0) then 1 else 0) +
    (if 1 < arity && !(sign 1) then 2 else 0) +
    (if 2 < arity && !(sign 2) then 4 else 0)

private theorem paperVariableArityShiftedTupleRejectedRankUnary_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (input : List Bool) (arity : ℕ) (sign : Fin 3 → Bool)
    (harity : paperShiftedTupleNormalizedArityUnary
      ranks input = List.replicate arity true)
    (hsign : ∀ position : Fin 3,
      paperShiftedTupleNormalizedSignWord
        ranks position input = [sign position]) :
    paperShiftedTupleRejectedRankUnary ranks input =
      List.replicate
        (paperShiftedTupleRejectedNatural arity sign) true := by
  have hpresent (position : Fin 3) :
      paperShiftedTupleNormalizedPositionBit
        ranks position input = [decide (position.val < arity)] := by
    exact fourFamilyComputedUnaryLessBitOutput_valid
      (paperShiftedTupleConstantUnary position.val)
      (paperShiftedTupleNormalizedArityUnary ranks)
      input position.val arity rfl harity
  have hzero := paperVariableArityShiftedTupleRejectedWeightedUnary_valid
    ranks 0 input (decide ((0 : Fin 3).val < arity))
    (sign 0) (hpresent 0) (hsign 0)
  have hone := paperVariableArityShiftedTupleRejectedWeightedUnary_valid
    ranks 1 input (decide ((1 : Fin 3).val < arity))
    (sign 1) (hpresent 1) (hsign 1)
  have htwo := paperVariableArityShiftedTupleRejectedWeightedUnary_valid
    ranks 2 input (decide ((2 : Fin 3).val < arity))
    (sign 2) (hpresent 2) (hsign 2)
  have hfirst := fourFamilyComputedUnarySumOutput_valid
    (paperShiftedTupleRejectedWeightedUnary ranks 0)
    (paperShiftedTupleRejectedWeightedUnary ranks 1)
    input
    (if decide ((0 : Fin 3).val < arity) && !(sign 0)
      then 2 ^ (0 : Fin 3).val else 0)
    (if decide ((1 : Fin 3).val < arity) && !(sign 1)
      then 2 ^ (1 : Fin 3).val else 0)
    hzero hone
  have hfull := fourFamilyComputedUnarySumOutput_valid
    (fourFamilyComputedUnarySumOutput
      (paperShiftedTupleRejectedWeightedUnary ranks 0)
      (paperShiftedTupleRejectedWeightedUnary ranks 1))
    (paperShiftedTupleRejectedWeightedUnary ranks 2)
    input
    ((if decide ((0 : Fin 3).val < arity) && !(sign 0)
        then 2 ^ (0 : Fin 3).val else 0) +
      (if decide ((1 : Fin 3).val < arity) && !(sign 1)
        then 2 ^ (1 : Fin 3).val else 0))
    (if decide ((2 : Fin 3).val < arity) && !(sign 2)
      then 2 ^ (2 : Fin 3).val else 0)
    hfirst htwo
  simpa only [paperShiftedTupleRejectedRankUnary, Fin.isValue, paperShiftedTupleRejectedNatural,
      Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
          Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      pow_zero, Nat.one_mod, pow_one, Nat.mod_succ, Nat.reducePow] using hfull

private def paperVariableArityShiftedTupleBeforeRejectedBit
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    ranks.tuple.output
    (paperShiftedTupleRejectedRankUnary ranks)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleBeforeRejectedBitComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperVariableArityShiftedTupleBeforeRejectedBit ranks) :=
  fourFamilyComputedUnaryLessBitComputable
    ranks.tuple.computer
    (paperVariableArityShiftedTupleRejectedRankUnaryComputable ranks)

private def paperShiftedTupleSkipUnary
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  sourceOriginalClauseBooleanUnaryOutput ∘
    sourceFourFamilyBooleanNotOutput
      (paperVariableArityShiftedTupleBeforeRejectedBit ranks)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleSkipUnaryComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperShiftedTupleSkipUnary ranks) :=
  GapCVP.TMComposition.computableInPolyTime
    (fourFamilyBooleanNotOutputComputable
      (paperVariableArityShiftedTupleBeforeRejectedBitComputable ranks))
    sourceOriginalClauseBooleanUnaryComputable

private def paperShiftedTupleSatisfyingWordRankUnary
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    ranks.tuple.output
    (paperShiftedTupleSkipUnary ranks)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleSatisfyingWordRankUnaryComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperShiftedTupleSatisfyingWordRankUnary ranks) :=
  fourFamilyComputedUnarySumComputable
    ranks.tuple.computer
    (paperVariableArityShiftedTupleSkipUnaryComputable ranks)

private theorem paperVariableArityShiftedTupleSatisfyingWordRankUnary_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (input : List Bool) (arity tuple : ℕ) (sign : Fin 3 → Bool)
    (harity : paperShiftedTupleNormalizedArityUnary
      ranks input = List.replicate arity true)
    (hsign : ∀ position : Fin 3,
      paperShiftedTupleNormalizedSignWord
        ranks position input = [sign position])
    (htuple : ranks.tuple.output input = List.replicate tuple true) :
    paperShiftedTupleSatisfyingWordRankUnary ranks input =
      List.replicate
        (tuple +
          if tuple < paperShiftedTupleRejectedNatural arity sign
          then 0 else 1) true := by
  have rejected := paperVariableArityShiftedTupleRejectedRankUnary_valid
    ranks input arity sign harity hsign
  have comparison := fourFamilyComputedUnaryLessBitOutput_valid
    ranks.tuple.output
    (paperShiftedTupleRejectedRankUnary ranks)
    input tuple
    (paperShiftedTupleRejectedNatural arity sign)
    htuple rejected
  have inverted := fourFamilyBooleanNotOutput_bit
    (paperVariableArityShiftedTupleBeforeRejectedBit ranks)
    input
    (decide
      (tuple < paperShiftedTupleRejectedNatural arity sign))
    comparison
  have skip :
      paperShiftedTupleSkipUnary ranks input =
        List.replicate
          (if tuple < paperShiftedTupleRejectedNatural arity sign
            then 0 else 1) true := by
    unfold paperShiftedTupleSkipUnary
    rw [Function.comp_apply, inverted,
      sourceOriginalClauseBooleanUnaryOutput_bit]
    by_cases hless :
      tuple < paperShiftedTupleRejectedNatural arity sign
    · simp only [hless, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        List.replicate_zero]
    · simp only [hless, decide_false, Bool.not_false, ↓reduceIte, List.replicate_one]
  exact fourFamilyComputedUnarySumOutput_valid
    ranks.tuple.output
    (paperShiftedTupleSkipUnary ranks)
    input tuple
    (if tuple < paperShiftedTupleRejectedNatural arity sign
      then 0 else 1) htuple skip

private def paperShiftedTupleLocalPowerNumeratorUnary
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    (fourFamilyComputedUnaryProductOutput
      ranks.variablePosition.output ranks.variablePosition.output)
    (fourFamilyComputedUnarySumOutput
      ranks.variablePosition.output
      (paperShiftedTupleConstantUnary 2))

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleLocalPowerNumeratorUnaryComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperShiftedTupleLocalPowerNumeratorUnary ranks) :=
  fourFamilyComputedUnarySumComputable
    (fourFamilyComputedUnaryProductComputable
      ranks.variablePosition.computer ranks.variablePosition.computer)
    (fourFamilyComputedUnarySumComputable
      ranks.variablePosition.computer
      (paperVariableArityShiftedTupleConstantUnaryComputable 2))

private theorem paperVariableArityShiftedTupleLocalPowerNumeratorUnary_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (input : List Bool) (position : ℕ)
    (hposition : ranks.variablePosition.output input =
      List.replicate position true) :
    paperShiftedTupleLocalPowerNumeratorUnary ranks input =
      List.replicate (position * position + (position + 2)) true := by
  have product := fourFamilyComputedUnaryProductOutput_valid
    ranks.variablePosition.output ranks.variablePosition.output
    input position position hposition hposition
  have offset := fourFamilyComputedUnarySumOutput_valid
    ranks.variablePosition.output
    (paperShiftedTupleConstantUnary 2)
    input position 2 hposition rfl
  exact fourFamilyComputedUnarySumOutput_valid
    (fourFamilyComputedUnaryProductOutput
      ranks.variablePosition.output ranks.variablePosition.output)
    (fourFamilyComputedUnarySumOutput
      ranks.variablePosition.output
      (paperShiftedTupleConstantUnary 2))
    input (position * position) (position + 2) product offset

private def paperShiftedTupleLocalBinaryPowerUnary
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryQuotient
    (paperShiftedTupleLocalPowerNumeratorUnary ranks)
    (paperShiftedTupleConstantUnary 2)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleLocalBinaryPowerUnaryComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperShiftedTupleLocalBinaryPowerUnary ranks) :=
  sourcePhysicalComputedUnaryQuotientComputable
    (paperVariableArityShiftedTupleLocalPowerNumeratorUnaryComputable ranks)
    (paperVariableArityShiftedTupleConstantUnaryComputable 2)

private theorem paperVariableArityShiftedTupleBoundedBinaryPower
    (position : ℕ) (hposition : position < 3) :
    (position * position + (position + 2)) / 2 = 2 ^ position := by
  interval_cases position <;> norm_num

private theorem paperVariableArityShiftedTupleLocalBinaryPowerUnary_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (input : List Bool) (position : ℕ)
    (hposition : position < 3)
    (hrank : ranks.variablePosition.output input =
      List.replicate position true) :
    paperShiftedTupleLocalBinaryPowerUnary ranks input =
      List.replicate (2 ^ position) true := by
  unfold paperShiftedTupleLocalBinaryPowerUnary
  rw [sourcePhysicalComputedUnaryQuotient_valid
    (paperShiftedTupleLocalPowerNumeratorUnary ranks)
    (paperShiftedTupleConstantUnary 2)
    input (position * position + (position + 2)) 2 (by norm_num)
    (paperVariableArityShiftedTupleLocalPowerNumeratorUnary_valid
      ranks input position hrank) rfl,
    paperVariableArityShiftedTupleBoundedBinaryPower position hposition]

private def paperVariableArityShiftedTupleSatisfyingPositionQuotientUnary
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryQuotient
    (paperShiftedTupleSatisfyingWordRankUnary ranks)
    (paperShiftedTupleLocalBinaryPowerUnary ranks)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleSatisfyingPositionQuotientUnaryComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperVariableArityShiftedTupleSatisfyingPositionQuotientUnary ranks) :=
  sourcePhysicalComputedUnaryQuotientComputable
    (paperVariableArityShiftedTupleSatisfyingWordRankUnaryComputable ranks)
    (paperVariableArityShiftedTupleLocalBinaryPowerUnaryComputable ranks)

private def paperVariableArityShiftedTupleSatisfyingPositionDigitUnary
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryRemainder
    (paperVariableArityShiftedTupleSatisfyingPositionQuotientUnary ranks)
    (paperShiftedTupleConstantUnary 2)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleSatisfyingPositionDigitUnaryComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperVariableArityShiftedTupleSatisfyingPositionDigitUnary ranks) :=
  sourcePhysicalComputedUnaryRemainderComputable
    (paperVariableArityShiftedTupleSatisfyingPositionQuotientUnaryComputable
      ranks)
    (paperVariableArityShiftedTupleConstantUnaryComputable 2)

/-- GapCVP reduction support. -/
def paperShiftedTupleBetaBit
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    (paperShiftedTupleConstantUnary 0)
    (paperVariableArityShiftedTupleSatisfyingPositionDigitUnary ranks)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityShiftedTupleBetaBitComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperShiftedTupleBetaBit ranks) :=
  fourFamilyComputedUnaryLessBitComputable
    (paperVariableArityShiftedTupleConstantUnaryComputable 0)
    (paperVariableArityShiftedTupleSatisfyingPositionDigitUnaryComputable
      ranks)

private theorem paperVariableArityShiftedTupleBinaryDigitComparison
    (value position : ℕ) :
    decide (0 < value / 2 ^ position % 2) = value.testBit position := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  apply Bool.decide_congr
  have bound : value / 2 ^ position % 2 < 2 :=
    Nat.mod_lt _ (by norm_num)
  omega

theorem paperVariableArityShiftedTupleBetaBit_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (input : List Bool) (arity tuple position : ℕ)
    (sign : Fin 3 → Bool)
    (hposition : position < 3)
    (harity : paperShiftedTupleNormalizedArityUnary
      ranks input = List.replicate arity true)
    (hsign : ∀ slot : Fin 3,
      paperShiftedTupleNormalizedSignWord
        ranks slot input = [sign slot])
    (htuple : ranks.tuple.output input = List.replicate tuple true)
    (hlocal : ranks.variablePosition.output input =
      List.replicate position true) :
    paperShiftedTupleBetaBit ranks input =
      [(tuple +
        if tuple < paperShiftedTupleRejectedNatural arity sign
        then 0 else 1).testBit position] := by
  let assignment := tuple +
    if tuple < paperShiftedTupleRejectedNatural arity sign
    then 0 else 1
  have satisfying := paperVariableArityShiftedTupleSatisfyingWordRankUnary_valid
    ranks input arity tuple sign harity hsign htuple
  have power := paperVariableArityShiftedTupleLocalBinaryPowerUnary_valid
    ranks input position hposition hlocal
  have quotient := sourcePhysicalComputedUnaryQuotient_valid
    (paperShiftedTupleSatisfyingWordRankUnary ranks)
    (paperShiftedTupleLocalBinaryPowerUnary ranks)
    input assignment (2 ^ position) (by positivity) satisfying power
  have digit := sourcePhysicalComputedUnaryRemainder_valid
    (paperVariableArityShiftedTupleSatisfyingPositionQuotientUnary ranks)
    (paperShiftedTupleConstantUnary 2)
    input (assignment / 2 ^ position) 2 (by norm_num)
    quotient rfl
  have beta := fourFamilyComputedUnaryLessBitOutput_valid
    (paperShiftedTupleConstantUnary 0)
    (paperVariableArityShiftedTupleSatisfyingPositionDigitUnary ranks)
    input 0 (assignment / 2 ^ position % 2) rfl digit
  change paperShiftedTupleBetaBit ranks input =
    [assignment.testBit position]
  exact beta.trans (congrArg (fun bit : Bool => [bit])
    (paperVariableArityShiftedTupleBinaryDigitComparison
      assignment position))

end ShiftedTupleBetaTM

namespace SatisfyingWordSourceRankSemantics

open GapCVP.SourceOrder GapCVP.ShiftedTupleBetaTM

/-- GapCVP reduction support. -/
def paperVariableArityBoundedSourceSign
    (arity : ℕ) (harity : arity ≤ 3)
    (sign : Fin 3 → Bool) : Fin arity → Bool :=
  fun position =>
    sign ⟨position.val, Nat.lt_of_lt_of_le position.isLt harity⟩

private theorem paperVariableArityShiftedTupleRejectedNatural_lt
    (arity : ℕ) (harity : arity ≤ 3)
    (sign : Fin 3 → Bool) :
    paperShiftedTupleRejectedNatural arity sign < 2 ^ arity := by
  interval_cases arity <;>
    cases hzero : sign 0 <;>
    cases hone : sign 1 <;>
    cases htwo : sign 2 <;>
    simp [paperShiftedTupleRejectedNatural,
      hzero, hone, htwo]

private def paperVariableArityShiftedTupleRejectedSourceWord
    (arity : ℕ) (harity : arity ≤ 3)
    (sign : Fin 3 → Bool) : Fin (2 ^ arity) :=
  ⟨paperShiftedTupleRejectedNatural arity sign,
    paperVariableArityShiftedTupleRejectedNatural_lt arity harity sign⟩

private theorem paperVariableArityRejectedWord_eq_shiftedTupleRejectedSourceWord
    (arity : ℕ) (harity : arity ≤ 3)
    (sign : Fin 3 → Bool) :
    paperVariableArityRejectedWord arity
        (paperVariableArityBoundedSourceSign arity harity sign) =
      paperVariableArityShiftedTupleRejectedSourceWord
        arity harity sign := by
  apply (paperVariableArityBooleanWordOrder arity).injective
  rw [show
    paperVariableArityBooleanWordOrder arity
      (paperVariableArityRejectedWord arity
        (paperVariableArityBoundedSourceSign arity harity sign)) =
      (fun position : Fin arity =>
        !(paperVariableArityBoundedSourceSign
          arity harity sign position)) by
      simp only [paperVariableArityRejectedWord, Equiv.apply_symm_apply]]
  change
    (fun position : Fin arity =>
      !(paperVariableArityBoundedSourceSign
        arity harity sign position)) =
      (fun position : Fin arity =>
        (paperVariableArityShiftedTupleRejectedSourceWord
          arity harity sign).val.testBit position.val)
  funext position
  interval_cases arity <;>
    fin_cases position <;>
    cases hzero : sign 0 <;>
    cases hone : sign 1 <;>
    cases htwo : sign 2 <;>
    simp only [paperVariableArityBoundedSourceSign,
      paperVariableArityShiftedTupleRejectedSourceWord,
      paperShiftedTupleRejectedNatural,
      hzero, hone, htwo, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue, Nat.reducePow, Bool.not_eq_eq_eq_not] <;>
    decide

private theorem paperVariableArityShiftedTupleRejectedNatural_eq_rejectedWord_val
    (arity : ℕ) (harity : arity ≤ 3)
    (sign : Fin 3 → Bool) :
    paperShiftedTupleRejectedNatural arity sign =
      (paperVariableArityRejectedWord arity
        (paperVariableArityBoundedSourceSign
          arity harity sign)).val := by
  rw [paperVariableArityRejectedWord_eq_shiftedTupleRejectedSourceWord]
  rfl

private theorem paperVariableAritySuccAbove_val
    {count : ℕ} (removed : Fin (count + 1))
    (tuple : Fin count) :
    (removed.succAbove tuple).val =
      tuple.val + if tuple.val < removed.val then 0 else 1 := by
  by_cases h : tuple.val < removed.val <;>
    simp [Fin.succAbove, Fin.lt_def, h]

private theorem paperVariableAritySatisfyingWordOrder_apply_eq_testBit
    (arity : ℕ) (sign : Fin arity → Bool)
    (tuple : Fin (2 ^ arity - 1))
    (position : Fin arity) :
    (paperSatisfyingWordOrder arity sign tuple).val position =
      (tuple.val +
        if tuple.val < (paperVariableArityRejectedWord arity sign).val
        then 0 else 1).testBit position.val := by
  have positive : 0 < 2 ^ arity := by positivity
  have cardinality : 2 ^ arity - 1 + 1 = 2 ^ arity := by omega
  let correction :
      Fin (2 ^ arity - 1 + 1) ≃ Fin (2 ^ arity) :=
    finCongr cardinality
  let removed : Fin (2 ^ arity - 1 + 1) :=
    correction.symm (paperVariableArityRejectedWord arity sign)
  change
    (correction (removed.succAbove tuple)).val.testBit position.val = _
  change
    (removed.succAbove tuple).val.testBit position.val = _
  rw [paperVariableAritySuccAbove_val]
  have hremoved :
      removed.val = (paperVariableArityRejectedWord arity sign).val := by
    rfl
  rw [hremoved]

theorem paperVariableAritySatisfyingWordOrder_apply_eq_shiftedTupleBetaBit
    (arity : ℕ) (harity : arity ≤ 3)
    (sign : Fin 3 → Bool)
    (tuple : Fin (2 ^ arity - 1))
    (position : Fin arity) :
    (paperSatisfyingWordOrder arity
      (paperVariableArityBoundedSourceSign
        arity harity sign) tuple).val position =
      (tuple.val +
        if tuple.val <
          paperShiftedTupleRejectedNatural arity sign
        then 0 else 1).testBit position.val := by
  rw [paperVariableAritySatisfyingWordOrder_apply_eq_testBit,
    ← paperVariableArityShiftedTupleRejectedNatural_eq_rejectedWord_val
      arity harity sign]

end SatisfyingWordSourceRankSemantics

namespace PhysicalInterpolationRowFamilyProjection

open scoped BigOperators

open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.FormulaBridge GapCVP.ClauseOffsetTM
open GapCVP.ShiftedTupleTM GapCVP.SourceOrder GapCVP.CanonicalOffsetIdentity
open GapCVP.PhysicalRowOrderProjection GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalRefinementRowProjection
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalRowCountMachine

/-- GapCVP reduction support. -/
abbrev physicalInterpolationMomentBudget
    (formula : ThreeCNF) : ℕ :=
  explicitMomentBudget (encodeThreeCNF formula).length
    (srcFormula formula)

private abbrev physicalInterpolationMomentCount
    (formula : ThreeCNF) : ℕ :=
  physicalInterpolationMomentBudget formula + 1

private abbrev physicalOrdinaryInterpolationTagCount
    (formula : ThreeCNF) : ℕ :=
  (1 + paperVariableArityLocalTagCount formula) *
    physicalInterpolationMomentCount formula

/-- GapCVP reduction support. -/
abbrev physicalShiftedInterpolationTagCount
    (formula : ThreeCNF) : ℕ :=
  paperShiftedFamilyTagCount formula
    (physicalInterpolationMomentBudget formula)

/-- GapCVP reduction support. -/
abbrev physicalInterpolationBlockWidth
    (formula : ThreeCNF) : ℕ :=
  physGridCard formula *
    physDegree formula

private def physicalOrdinaryDependentFamilyIndex
    (formula : ThreeCNF)
    (tag : Fin
      (physicalOrdinaryInterpolationTagCount formula)) :
    Fin (paperExplicitFamilyTagCount
      (encodeThreeCNF formula).length formula) := by
  change Fin
    (1 + ((srcFormula formula).clauses.length +
      (physicalOrdinaryInterpolationTagCount formula +
        physicalShiftedInterpolationTagCount formula)))
  exact Fin.natAdd 1
    (Fin.natAdd (srcFormula formula).clauses.length
      (Fin.castAdd
        (physicalShiftedInterpolationTagCount formula)
        tag))

/-- GapCVP reduction support. -/
def physicalShiftedDependentFamilyIndex
    (formula : ThreeCNF)
    (tag : Fin
      (physicalShiftedInterpolationTagCount formula)) :
    Fin (paperExplicitFamilyTagCount
      (encodeThreeCNF formula).length formula) := by
  change Fin
    (1 + ((srcFormula formula).clauses.length +
      (physicalOrdinaryInterpolationTagCount formula +
        physicalShiftedInterpolationTagCount formula)))
  exact Fin.natAdd 1
    (Fin.natAdd (srcFormula formula).clauses.length
      (Fin.natAdd
        (physicalOrdinaryInterpolationTagCount formula)
        tag))

@[simp] private theorem paperVariableArityPhysicalOrdinaryDependentFamilyIndex_val
    (formula : ThreeCNF)
    (tag : Fin
      (physicalOrdinaryInterpolationTagCount formula)) :
    (physicalOrdinaryDependentFamilyIndex
      formula tag).val =
      1 + (srcFormula formula).clauses.length +
        tag.val := by
  change
    1 + ((srcFormula formula).clauses.length +
      tag.val) = _
  omega

@[simp] private theorem paperVariableArityPhysicalShiftedDependentFamilyIndex_val
    (formula : ThreeCNF)
    (tag : Fin
      (physicalShiftedInterpolationTagCount formula)) :
    (physicalShiftedDependentFamilyIndex
      formula tag).val =
      1 + (srcFormula formula).clauses.length +
        (physicalOrdinaryInterpolationTagCount formula +
          tag.val) := by
  change
    1 + ((srcFormula formula).clauses.length +
      (physicalOrdinaryInterpolationTagCount formula +
        tag.val)) = _
  omega

private theorem paperVariableArityPhysicalOrdinaryDependentFamilyWordOrder
    (formula : ThreeCNF)
    (tag : Fin
      (physicalOrdinaryInterpolationTagCount formula)) :
    paperExplicitFamilyWordOrder
        (encodeThreeCNF formula).length formula
        (physicalOrdinaryDependentFamilyIndex
          formula tag) =
      .inr (.inr (.inl
        (paperOrdinaryFamilyWordOrder formula
          (physicalInterpolationMomentBudget formula)
          tag))) := by
  change
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr finOneEquiv _))
      (Fin.natAdd 1
        (Fin.natAdd (srcFormula formula).clauses.length
          (Fin.castAdd
            (physicalShiftedInterpolationTagCount formula)
            tag))) = _
  simp only [Equiv.trans_apply,
    finSumFinEquiv_symm_apply_natAdd,
    finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl]

theorem paperVariableArityPhysicalShiftedDependentFamilyWordOrder
    (formula : ThreeCNF)
    (tag : Fin
      (physicalShiftedInterpolationTagCount formula)) :
    paperExplicitFamilyWordOrder
        (encodeThreeCNF formula).length formula
        (physicalShiftedDependentFamilyIndex
          formula tag) =
      .inr (.inr (.inr
        (paperShiftedFamilyWordOrder formula
          (physicalInterpolationMomentBudget formula)
          tag))) := by
  change
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr finOneEquiv _))
      (Fin.natAdd 1
        (Fin.natAdd (srcFormula formula).clauses.length
          (Fin.natAdd
            (physicalOrdinaryInterpolationTagCount formula)
            tag))) = _
  simp only [Equiv.trans_apply,
    finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inr]

private theorem paperVariableArityPhysicalOrdinaryDependentFamilyBlockCount
    (formula : ThreeCNF)
    (tag : Fin
      (physicalOrdinaryInterpolationTagCount formula)) :
    paperExplicitBinaryFamilyBlockCount
        (encodeThreeCNF formula).length formula
        (physicalOrdinaryDependentFamilyIndex
          formula tag) =
      physicalInterpolationBlockWidth formula := by
  unfold paperExplicitBinaryFamilyBlockCount
  rw [paperVariableArityPhysicalOrdinaryDependentFamilyWordOrder]
  change
    Fintype.card
      (ExplicitGridPoint (encodeThreeCNF formula).length
        (srcFormula formula)) *
        physDegree formula = _
  rw [physicalRefinementGridCard_eq]

theorem paperVariableArityPhysicalShiftedDependentFamilyBlockCount
    (formula : ThreeCNF)
    (tag : Fin
      (physicalShiftedInterpolationTagCount formula)) :
    paperExplicitBinaryFamilyBlockCount
        (encodeThreeCNF formula).length formula
        (physicalShiftedDependentFamilyIndex
          formula tag) =
      physicalInterpolationBlockWidth formula := by
  unfold paperExplicitBinaryFamilyBlockCount
  rw [paperVariableArityPhysicalShiftedDependentFamilyWordOrder]
  change
    Fintype.card
      (ExplicitGridPoint (encodeThreeCNF formula).length
        (srcFormula formula)) *
        physDegree formula = _
  rw [physicalRefinementGridCard_eq]

private theorem paperVariableArityPhysicalInterpolationRefinementPrefix
    (formula : ThreeCNF)
    (hbound :
      1 + (srcFormula formula).clauses.length ≤
        paperExplicitFamilyTagCount
          (encodeThreeCNF formula).length formula) :
    (∑ index : Fin
        (1 + (srcFormula formula).clauses.length),
      paperExplicitBinaryFamilyBlockCount
        (encodeThreeCNF formula).length formula
        (Fin.castLE hbound index)) =
      physicalFormulaRefinementBoundary formula := by
  rw [Fin.sum_univ_add, Fin.sum_univ_one]
  have first :
      (Fin.castLE hbound
        (Fin.castAdd
          (srcFormula formula).clauses.length
          (0 : Fin 1))) =
        (⟨0, physicalFamilyTagCount_pos
          (encodeThreeCNF formula).length formula⟩ :
          Fin (paperExplicitFamilyTagCount
            (encodeThreeCNF formula).length formula)) := by
    apply Fin.ext
    rfl
  rw [first, physicalFirstFamilyBlockCount,
    physicalRefinementGridCard_eq]
  have blocks :
      (∑ index : Fin
        (srcFormula formula).clauses.length,
        paperExplicitBinaryFamilyBlockCount
          (encodeThreeCNF formula).length formula
          (Fin.castLE hbound (Fin.natAdd 1 index))) =
        ∑ _index : Fin
          (srcFormula formula).clauses.length,
          physicalRefinementBlockWidth formula := by
    apply Finset.sum_congr rfl
    intro index _
    have selected :
        (Fin.castLE hbound (Fin.natAdd 1 index)) =
          physicalRefinementFamilyIndex
            (encodeThreeCNF formula).length formula index := by
      apply Fin.ext
      rw [paperVariableArityPhysicalRefinementFamilyIndex_val]
      rfl
    rw [selected,
      physicalRefinementFamilySourceBlockCount]
  rw [blocks, paperVariableAritySourceFormula_clauses_length]
  simp only [physicalRefinementBlockWidth, Nat.mul_assoc, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul,
    physicalFormulaRefinementBoundary, physicalFormulaGlobalBoundary]

private theorem paperVariableArityPhysicalInterpolationOrdinaryBoundary_eq
    (formula : ThreeCNF) :
    physicalFormulaOrdinaryBoundary formula =
      physicalFormulaRefinementBoundary formula +
        physicalOrdinaryInterpolationTagCount formula *
          physicalInterpolationBlockWidth formula := by
  change
    physicalFormulaRefinementBoundary formula +
        (1 + sourceClauseWeightSum
          (noTautClauses formula)) *
          physicalFormulaMomentCount formula *
          physGridCard formula *
          physDegree formula = _
  rw [sourceClauseWeightSum_eq_localTagCount]
  change
    physicalFormulaRefinementBoundary formula +
      (1 + paperVariableArityLocalTagCount formula) *
        physicalInterpolationMomentCount formula *
        physGridCard formula *
        physDegree formula =
      physicalFormulaRefinementBoundary formula +
        ((1 + paperVariableArityLocalTagCount formula) *
          physicalInterpolationMomentCount formula) *
          (physGridCard formula *
            physDegree formula)
  ring

theorem paperVariableArityPhysicalInterpolationRowCount_eq
    (formula : ThreeCNF) :
    paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula =
      physicalFormulaOrdinaryBoundary formula +
        physicalShiftedInterpolationTagCount formula *
          physicalInterpolationBlockWidth formula := by
  rw [paperVariableArityExplicitBinaryRowWordCount_eq_fourFamily]
  change
    physicalFormulaOrdinaryBoundary formula +
      paperShiftedSourceClauseWeightSum
        (noTautClauses formula) *
        physicalInterpolationMomentCount formula *
        physGridCard formula *
        physDegree formula =
      physicalFormulaOrdinaryBoundary formula +
        paperShiftedFamilyTagCount formula
          (physicalInterpolationMomentBudget formula) *
          (physGridCard formula *
            physDegree formula)
  rw [paperVariableArityShiftedFamilyTagCount_eq_sourceWeight]
  change
    physicalFormulaOrdinaryBoundary formula +
      physicalFormulaShiftedTupleCount formula *
        physicalInterpolationMomentCount formula *
        physGridCard formula *
        physDegree formula =
      physicalFormulaOrdinaryBoundary formula +
        (physicalFormulaShiftedTupleCount formula *
          physicalInterpolationMomentCount formula) *
          (physGridCard formula *
            physDegree formula)
  ring

private theorem paperVariableArityPhysicalOrdinaryDependentFamilyPrefix
    (formula : ThreeCNF)
    (tag : Fin
      (physicalOrdinaryInterpolationTagCount formula)) :
    physicalSigmaPrefix
        (paperExplicitBinaryFamilyBlockCount
          (encodeThreeCNF formula).length formula)
        (physicalOrdinaryDependentFamilyIndex
          formula tag) =
      physicalFormulaRefinementBoundary formula +
        tag.val *
          physicalInterpolationBlockWidth formula := by
  let count := (srcFormula formula).clauses.length
  let familyCount := paperExplicitFamilyTagCount
    (encodeThreeCNF formula).length formula
  let blockCount := paperExplicitBinaryFamilyBlockCount
    (encodeThreeCNF formula).length formula
  let width := physicalInterpolationBlockWidth formula
  have hstrict : 1 + count + tag.val < familyCount := by
    have bounded :=
      (physicalOrdinaryDependentFamilyIndex
        formula tag).isLt
    rw [paperVariableArityPhysicalOrdinaryDependentFamilyIndex_val]
      at bounded
    simpa only [count, familyCount] using bounded
  have hwhole : 1 + count + tag.val ≤ familyCount := hstrict.le
  have hfirst : 1 + count ≤ familyCount := by omega
  let candidate : Fin familyCount :=
    ⟨1 + count + tag.val, hstrict⟩
  have hcandidate :
      physicalOrdinaryDependentFamilyIndex
        formula tag = candidate := by
    apply Fin.ext
    rw [paperVariableArityPhysicalOrdinaryDependentFamilyIndex_val]
  rw [hcandidate]
  unfold physicalSigmaPrefix
  change
    (∑ index : Fin (1 + count + tag.val),
      blockCount (Fin.castLE hwhole index)) =
      physicalFormulaRefinementBoundary formula +
        tag.val * width
  rw [Fin.sum_univ_add]
  have refinement :
      (∑ index : Fin (1 + count),
        blockCount (Fin.castLE hwhole
          (Fin.castAdd tag.val index))) =
        physicalFormulaRefinementBoundary formula := by
    have original :=
      paperVariableArityPhysicalInterpolationRefinementPrefix
        formula hfirst
    calc
      (∑ index : Fin (1 + count),
        blockCount (Fin.castLE hwhole
          (Fin.castAdd tag.val index))) =
        ∑ index : Fin (1 + count),
          blockCount (Fin.castLE hfirst index) := by
            apply Finset.sum_congr rfl
            intro index _
            congr 1
      _ = physicalFormulaRefinementBoundary formula :=
        original
  have ordinary :
      (∑ index : Fin tag.val,
        blockCount (Fin.castLE hwhole
          (Fin.natAdd (1 + count) index))) =
        ∑ _index : Fin tag.val, width := by
    apply Finset.sum_congr rfl
    intro index _
    let selected : Fin
      (physicalOrdinaryInterpolationTagCount formula) :=
      ⟨index.val, Nat.lt_trans index.isLt tag.isLt⟩
    have heq :
        Fin.castLE hwhole (Fin.natAdd (1 + count) index) =
          physicalOrdinaryDependentFamilyIndex
            formula selected := by
      apply Fin.ext
      rw [paperVariableArityPhysicalOrdinaryDependentFamilyIndex_val]
      change 1 + count + index.val =
        1 + count + selected.val
      rfl
    rw [heq]
    exact paperVariableArityPhysicalOrdinaryDependentFamilyBlockCount
      formula selected
  rw [refinement, ordinary]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem paperVariableArityPhysicalShiftedDependentFamilyPrefix
    (formula : ThreeCNF)
    (tag : Fin
      (physicalShiftedInterpolationTagCount formula)) :
    physicalSigmaPrefix
        (paperExplicitBinaryFamilyBlockCount
          (encodeThreeCNF formula).length formula)
        (physicalShiftedDependentFamilyIndex
          formula tag) =
      physicalFormulaOrdinaryBoundary formula +
        tag.val *
          physicalInterpolationBlockWidth formula := by
  let count := (srcFormula formula).clauses.length
  let ordinaryCount :=
    physicalOrdinaryInterpolationTagCount formula
  let familyCount := paperExplicitFamilyTagCount
    (encodeThreeCNF formula).length formula
  let blockCount := paperExplicitBinaryFamilyBlockCount
    (encodeThreeCNF formula).length formula
  let width := physicalInterpolationBlockWidth formula
  have hstrict :
      1 + count + ordinaryCount + tag.val < familyCount := by
    have bounded :=
      (physicalShiftedDependentFamilyIndex
        formula tag).isLt
    rw [paperVariableArityPhysicalShiftedDependentFamilyIndex_val]
      at bounded
    simp only [count, ordinaryCount, familyCount] at bounded ⊢
    omega
  have hwhole :
      1 + count + ordinaryCount + tag.val ≤ familyCount := hstrict.le
  have hbefore : 1 + count + ordinaryCount ≤ familyCount := by omega
  have hfirst : 1 + count ≤ familyCount := by omega
  let candidate : Fin familyCount :=
    ⟨1 + count + ordinaryCount + tag.val, hstrict⟩
  have hcandidate :
      physicalShiftedDependentFamilyIndex
        formula tag = candidate := by
    apply Fin.ext
    rw [paperVariableArityPhysicalShiftedDependentFamilyIndex_val]
    dsimp [candidate, count, ordinaryCount]
    omega
  rw [hcandidate]
  unfold physicalSigmaPrefix
  change
    (∑ index : Fin (1 + count + ordinaryCount + tag.val),
      blockCount (Fin.castLE hwhole index)) =
      physicalFormulaOrdinaryBoundary formula +
        tag.val * width
  rw [Fin.sum_univ_add]
  have before :
      (∑ index : Fin (1 + count + ordinaryCount),
        blockCount (Fin.castLE hwhole
          (Fin.castAdd tag.val index))) =
        physicalFormulaOrdinaryBoundary formula := by
    have reduced :
        (∑ index : Fin (1 + count + ordinaryCount),
          blockCount (Fin.castLE hbefore index)) =
          physicalFormulaOrdinaryBoundary formula := by
      rw [Fin.sum_univ_add]
      have refinement :
          (∑ index : Fin (1 + count),
            blockCount (Fin.castLE hbefore
              (Fin.castAdd ordinaryCount index))) =
            physicalFormulaRefinementBoundary formula := by
        calc
          (∑ index : Fin (1 + count),
            blockCount (Fin.castLE hbefore
              (Fin.castAdd ordinaryCount index))) =
            ∑ index : Fin (1 + count),
              blockCount (Fin.castLE hfirst index) := by
                apply Finset.sum_congr rfl
                intro index _
                congr 1
          _ = physicalFormulaRefinementBoundary formula :=
            paperVariableArityPhysicalInterpolationRefinementPrefix
              formula hfirst
      have ordinary :
          (∑ index : Fin ordinaryCount,
            blockCount (Fin.castLE hbefore
              (Fin.natAdd (1 + count) index))) =
            ∑ _index : Fin ordinaryCount, width := by
        apply Finset.sum_congr rfl
        intro index _
        have selected :
            Fin.castLE hbefore (Fin.natAdd (1 + count) index) =
              physicalOrdinaryDependentFamilyIndex
                formula index := by
          apply Fin.ext
          rw [paperVariableArityPhysicalOrdinaryDependentFamilyIndex_val]
          change 1 + count + index.val = 1 + count + index.val
          rfl
        rw [selected]
        exact paperVariableArityPhysicalOrdinaryDependentFamilyBlockCount
          formula index
      rw [refinement, ordinary]
      rw [paperVariableArityPhysicalInterpolationOrdinaryBoundary_eq]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          Nat.add_left_cancel_iff]
      rfl
    calc
      (∑ index : Fin (1 + count + ordinaryCount),
        blockCount (Fin.castLE hwhole
          (Fin.castAdd tag.val index))) =
        ∑ index : Fin (1 + count + ordinaryCount),
          blockCount (Fin.castLE hbefore index) := by
            apply Finset.sum_congr rfl
            intro index _
            congr 1
      _ = physicalFormulaOrdinaryBoundary formula :=
        reduced
  have shifted :
      (∑ index : Fin tag.val,
        blockCount (Fin.castLE hwhole
          (Fin.natAdd (1 + count + ordinaryCount) index))) =
        ∑ _index : Fin tag.val, width := by
    apply Finset.sum_congr rfl
    intro index _
    let selected : Fin
      (physicalShiftedInterpolationTagCount formula) :=
      ⟨index.val, Nat.lt_trans index.isLt tag.isLt⟩
    have heq :
        Fin.castLE hwhole
          (Fin.natAdd (1 + count + ordinaryCount) index) =
          physicalShiftedDependentFamilyIndex
            formula selected := by
      apply Fin.ext
      rw [paperVariableArityPhysicalShiftedDependentFamilyIndex_val]
      dsimp [count, ordinaryCount, selected]
      omega
    rw [heq]
    exact paperVariableArityPhysicalShiftedDependentFamilyBlockCount
      formula selected
  rw [before, shifted]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end PhysicalInterpolationRowFamilyProjection

namespace PhysicalOrdinaryInterpolationRowTagCorrectness

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationRowFamilyProjection GapCVP.PhysicalRefinementRowProjection
open GapCVP.PhysicalRowOrderProjection GapCVP.SourceOrder

private theorem paperVariableArityPhysicalOrdinaryFamilySourceTypeWordRank
    (formula : ThreeCNF)
    (momentBudget : ℕ)
    (tag : Fin
      ((1 + paperVariableArityLocalTagCount formula) *
        (momentBudget + 1))) :
    ((sourceTypeWordOrder formula).symm
      ((paperOrdinaryFamilyWordOrder formula
        momentBudget tag).1)).val = tag.val / (momentBudget + 1) := by
  simp only [paperOrdinaryFamilyWordOrder, finProdFinEquiv, Equiv.symm_mk, Equiv.trans_apply,
      Equiv.coe_fn_mk,
      Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq, Equiv.symm_apply_apply,
          Fin.coe_divNat]

private theorem paperVariableArityPhysicalOrdinarySourceInterpolationBlockWidth_pos
    (formula : ThreeCNF) :
    0 < physicalInterpolationBlockWidth formula :=
  Nat.mul_pos
    (physicalRefinementGridCard_pos formula)
    (physicalRefinementDegree_pos formula)

private def physicalOrdinarySourceRowFamilyCoordinate
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    Fin (physicalOrdinaryInterpolationTagCount formula) := by
  refine
    ⟨(row.val - physicalFormulaRefinementBoundary formula) /
      physicalInterpolationBlockWidth formula, ?_⟩
  apply (Nat.div_lt_iff_lt_mul
    (paperVariableArityPhysicalOrdinarySourceInterpolationBlockWidth_pos
      formula)).mpr
  rw [paperVariableArityPhysicalInterpolationOrdinaryBoundary_eq]
    at inOrdinary
  omega

private theorem paperVariableArityPhysicalOrdinarySourceRowDecodedFamilyIndex
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    physicalRowDependentFamilyIndex
        (encodeThreeCNF formula).length formula row =
      physicalOrdinaryDependentFamilyIndex formula
        (physicalOrdinarySourceRowFamilyCoordinate
          formula row inOrdinary) := by
  apply (paperVariableArityPhysicalSigmaFamilyIndex_eq_iff
    (paperExplicitBinaryFamilyBlockCount
      (encodeThreeCNF formula).length formula) row _).mpr
  rw [paperVariableArityPhysicalOrdinaryDependentFamilyPrefix,
    paperVariableArityPhysicalOrdinaryDependentFamilyBlockCount]
  let width := physicalInterpolationBlockWidth formula
  let offset := row.val - physicalFormulaRefinementBoundary formula
  have positive : 0 < width :=
    paperVariableArityPhysicalOrdinarySourceInterpolationBlockWidth_pos formula
  have lower := Nat.div_mul_le_self offset width
  have upper := Nat.lt_div_mul_add positive (a := offset)
  have restore : offset + physicalFormulaRefinementBoundary formula = row.val :=
    Nat.sub_add_cancel inOrdinary.1
  change physicalFormulaRefinementBoundary formula +
      (offset / width) * width ≤ row.val ∧
    row.val < physicalFormulaRefinementBoundary formula +
      (offset / width) * width + width
  omega

private theorem paperVariableArityPhysicalOrdinarySourceRowDecodedFamily
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    (physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row).1 =
      .inr (.inr (.inl
        (paperOrdinaryFamilyWordOrder formula
          (physicalInterpolationMomentBudget formula)
          (physicalOrdinarySourceRowFamilyCoordinate
            formula row inOrdinary)))) := by
  rw [physicalRowOrder_family,
    paperVariableArityPhysicalOrdinarySourceRowDecodedFamilyIndex,
    paperVariableArityPhysicalOrdinaryDependentFamilyWordOrder]

end PhysicalOrdinaryInterpolationRowTagCorrectness

namespace PhysicalOrdinaryInterpolationCheckFieldCorrectness

open scoped BigOperators

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.FormulaBridge
open GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationRowFamilyProjection
open GapCVP.PhysicalOrdinaryInterpolationRowTagCorrectness
open GapCVP.PhysicalSelectedInterpolationCoefficientProjection GapCVP.SourceOrder
open GapCVP.BinaryReedSolomonParity

/-- GapCVP reduction support. -/
def physicalOrdinarySourceRowTableMoment
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    sourceSATTableType (srcFormula formula) ×
      Fin (physicalInterpolationMomentBudget formula + 1) :=
  paperOrdinaryFamilyWordOrder formula
    (physicalInterpolationMomentBudget formula)
    (physicalOrdinarySourceRowFamilyCoordinate
      formula row inOrdinary)

/-- GapCVP reduction support. -/
def physicalOrdinarySourceRowGrid
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    Fin (Fintype.card
      (ExplicitGridPoint (encodeThreeCNF formula).length
        (srcFormula formula))) := by
  let decoded := physicalWordDecodedRow
    (encodeThreeCNF formula).length formula row
  refine ⟨decoded.2.1.val, ?_⟩
  have bounded := decoded.2.1.isLt
  have family := paperVariableArityPhysicalOrdinarySourceRowDecodedFamily
    formula row inOrdinary
  change decoded.1 = _ at family
  have rowCount :
      explicitFamilyRowCount
        (encodeThreeCNF formula).length
        (srcFormula formula) decoded.1 =
      Fintype.card
        (ExplicitGridPoint (encodeThreeCNF formula).length
          (srcFormula formula)) := by
    rw [family]
  exact lt_of_lt_of_eq bounded rowCount

theorem paperVariableArityPhysicalOrdinarySourceRowFieldCoefficient_eq_selected
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    physicalWordFamilyFieldCoefficient
        (encodeThreeCNF formula).length formula
        (physicalWordDecodedRow
          (encodeThreeCNF formula).length formula row).1
        (physicalWordDecodedRow
          (encodeThreeCNF formula).length formula row).2.1
        column =
      if (physicalOrdinarySourceRowTableMoment
          formula row inOrdinary).1 =
        (sourceCoordinateWordOrder
          (encodeThreeCNF formula).length formula column).1
      then
        constructiveParityMatrix
          (fun index =>
            (sourceFormulaExplicitGridOrder
              (encodeThreeCNF formula).length
              (srcFormula formula) index).val)
          (explicitOrdinaryDegree_lt_grid
            (encodeThreeCNF formula).length
            (srcFormula formula)
            (physicalOrdinarySourceRowTableMoment
              formula row inOrdinary).2)
          (physicalOrdinarySourceRowGrid
            formula row inOrdinary)
          ((sourceFormulaExplicitGridOrder
            (encodeThreeCNF formula).length
            (srcFormula formula)).symm
              (sourceCoordinateWordOrder
                (encodeThreeCNF formula).length formula column).2.1) *
          (sourceCoordinateWordOrder
            (encodeThreeCNF formula).length formula column).2.2 ^
              (physicalOrdinarySourceRowTableMoment
                formula row inOrdinary).2.val
      else 0 := by
  let tableMoment := physicalOrdinarySourceRowTableMoment
    formula row inOrdinary
  let grid := physicalOrdinarySourceRowGrid
    formula row inOrdinary
  have family := paperVariableArityPhysicalOrdinarySourceRowDecodedFamily
    formula row inOrdinary
  have selected :=
    paperVariableArityPhysicalWordOrdinaryFieldCoefficient_eq_selectedCoordinate
      (encodeThreeCNF formula).length formula
      tableMoment.1 tableMoment.2 grid column
  generalize decodedEquality :
    physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row = decoded
    at family ⊢
  rcases decoded with ⟨decodedFamily, decodedRow, decodedBasis⟩
  have exactFamily : decodedFamily =
      .inr (.inr (.inl tableMoment)) := family
  subst decodedFamily
  have exactGrid : decodedRow = grid := by
    apply Fin.ext
    change decodedRow.val = grid.val
    change decodedRow.val =
      (physicalWordDecodedRow
        (encodeThreeCNF formula).length formula row).2.1.val
    exact (congrArg
      (fun value => value.2.1.val) decodedEquality).symm
  subst decodedRow
  exact selected

end PhysicalOrdinaryInterpolationCheckFieldCorrectness

namespace PhysicalOrdinaryInterpolationTypeMatchCorrectness

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.MatrixEntrySemantics GapCVP.PhysicalColumnOrderProjection
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalInterpolationRowFamilyProjection
open GapCVP.PhysicalOrdinaryInterpolationRowTagCorrectness GapCVP.SourceOrder

private theorem paperVariableArityPhysicalOrdinaryFamilySourceTypeCardWordRank
    (formula : ThreeCNF)
    (momentBudget : ℕ)
    (tag : Fin
      ((1 + paperVariableArityLocalTagCount formula) *
        (momentBudget + 1))) :
    ((sourceTypeCardWordOrder formula).symm
      ((paperOrdinaryFamilyWordOrder formula
        momentBudget tag).1)).val = tag.val / (momentBudget + 1) := by
  simpa only [sourceTypeCardWordOrder, Equiv.symm_trans, finCongr_symm, Equiv.trans_apply,
      finCongr_apply,
      Fin.val_cast] using paperVariableArityPhysicalOrdinaryFamilySourceTypeWordRank formula
          momentBudget tag

private theorem paperVariableArityPhysicalOrdinarySourceRowTypeCardWordRank
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    ((sourceTypeCardWordOrder formula).symm
      ((paperOrdinaryFamilyWordOrder formula
        (physicalInterpolationMomentBudget formula)
        (physicalOrdinarySourceRowFamilyCoordinate
          formula row inOrdinary)).1)).val =
      (((row.val -
          physicalFormulaRefinementBoundary formula) /
        physDegree formula) /
          physGridCard formula) /
            physicalFormulaMomentCount formula := by
  rw [paperVariableArityPhysicalOrdinaryFamilySourceTypeCardWordRank]
  change
    ((row.val - physicalFormulaRefinementBoundary formula) /
      (physGridCard formula *
        physDegree formula)) /
      physicalFormulaMomentCount formula = _
  congr 1
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm]

private theorem paperVariableArityPhysicalOrdinarySourceRowTable_eq_column_iff
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    (paperOrdinaryFamilyWordOrder formula
      (physicalInterpolationMomentBudget formula)
      (physicalOrdinarySourceRowFamilyCoordinate
        formula row inOrdinary)).1 =
        (sourceCoordinateWordOrder
          (encodeThreeCNF formula).length formula column).1 ↔
      (((row.val -
          physicalFormulaRefinementBoundary formula) /
        physDegree formula) /
          physGridCard formula) /
            physicalFormulaMomentCount formula =
        (column.val /
          physFieldCard formula) /
            physGridCard formula := by
  let rowType :=
    (paperOrdinaryFamilyWordOrder formula
      (physicalInterpolationMomentBudget formula)
      (physicalOrdinarySourceRowFamilyCoordinate
        formula row inOrdinary)).1
  let columnType :=
    (sourceCoordinateWordOrder
      (encodeThreeCNF formula).length formula column).1
  have rowRank := paperVariableArityPhysicalOrdinarySourceRowTypeCardWordRank
    formula row inOrdinary
  have columnRank := sourceCoordinateTypeWordRank
    (encodeThreeCNF formula).length formula column
  rw [physicalFormulaFieldCardinality_eq_card,
    physicalFormulaGridCardinality_eq_card] at columnRank
  change rowType = columnType ↔ _
  constructor
  · intro equal
    have ranks := congrArg
      (fun sourceType =>
        ((sourceTypeCardWordOrder formula).symm
          sourceType).val) equal
    exact rowRank.symm.trans (ranks.trans columnRank)
  · intro ranks
    apply (sourceTypeCardWordOrder formula).symm.injective
    apply Fin.ext
    exact rowRank.trans (ranks.trans columnRank.symm)

end PhysicalOrdinaryInterpolationTypeMatchCorrectness

namespace PhysicalOrdinaryShiftedCheckBitInstantiation

open Turing GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalGlobalRefinementCoefficientTM GapCVP.SourceFieldMomentOperationsTM

private theorem paperVariableArityPhysicalInterpolationFamilyTypeRankComputer_output
    (family : Fin 4) :
    (physicalInterpolationFamilyTypeRankComputer
      family).output =
      physicalInterpolationFamilyTypeRankUnary family := by
  dsimp only [physicalInterpolationFamilyTypeRankComputer]

private theorem paperVariableArityPhysicalOrdinaryExpectedTypeMatchBit_valid
    (formula : ThreeCNF) (row column : ℕ) :
    physicalInterpolationExpectedTypeMatchBit
        (physicalInterpolationFamilyTypeRankComputer
          (2 : Fin 4))
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (((((row - physicalFamilyStart
              (2 : Fin 4) formula) /
            physDegree formula) /
            physGridCard formula) /
            physicalFormulaMomentCount formula) =
          ((column /
              physFieldCard formula) /
            physGridCard formula))] := by
  unfold physicalInterpolationExpectedTypeMatchBit
  apply physicalCoefficientUnaryEquality_valid
    (physicalInterpolationFamilyTypeRankComputer
      (2 : Fin 4)).output
    physicalColumnTypeRankUnary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    ((((row - physicalFamilyStart
      (2 : Fin 4) formula) /
      physDegree formula) /
      physGridCard formula) /
      physicalFormulaMomentCount formula)
    ((column / physFieldCard formula) /
      physGridCard formula)
  · rw [paperVariableArityPhysicalInterpolationFamilyTypeRankComputer_output]
    exact paperVariableArityPhysicalInterpolationFamilyTypeRankUnary_valid
      (2 : Fin 4) row column formula
  · exact paperVariableArityPhysicalColumnTypeRankUnary_query
      row column formula

end PhysicalOrdinaryShiftedCheckBitInstantiation

namespace PhysicalOrdinaryInterpolationRowGridBasisCorrectness

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationRowFamilyProjection
open GapCVP.PhysicalOrdinaryInterpolationCheckFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationRowTagCorrectness GapCVP.PhysicalRowOrderProjection
open GapCVP.SourceOrder

private theorem paperVariableArityPhysicalOrdinarySourceRowDependentBlockRank
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    (physicalRowDependentBlockRank
      (encodeThreeCNF formula).length formula row).val =
      (row.val - physicalFormulaRefinementBoundary formula) %
        physicalInterpolationBlockWidth formula := by
  have rank := physicalRowDependentRank_eq_prefix
    (encodeThreeCNF formula).length formula row
  change row.val = physicalSigmaPrefix _
    (physicalRowDependentFamilyIndex
      (encodeThreeCNF formula).length formula row) +
      (physicalRowDependentBlockRank
        (encodeThreeCNF formula).length formula row).val at rank
  have prefixEquality := congrArg
    (physicalSigmaPrefix (paperExplicitBinaryFamilyBlockCount
      (encodeThreeCNF formula).length formula))
    (paperVariableArityPhysicalOrdinarySourceRowDecodedFamilyIndex formula row inOrdinary)
  rw [paperVariableArityPhysicalOrdinaryDependentFamilyPrefix] at prefixEquality
  rw [prefixEquality] at rank
  let width := physicalInterpolationBlockWidth formula
  let offset := row.val - physicalFormulaRefinementBoundary formula
  change row.val = physicalFormulaRefinementBoundary formula +
    (offset / width) * width +
      (physicalRowDependentBlockRank
        (encodeThreeCNF formula).length formula row).val at rank
  have decomposition := Nat.mod_add_div' offset width
  have restore : offset + physicalFormulaRefinementBoundary formula = row.val :=
    Nat.sub_add_cancel inOrdinary.1
  change (physicalRowDependentBlockRank
    (encodeThreeCNF formula).length formula row).val = offset % width
  omega

theorem paperVariableArityPhysicalOrdinarySourceRowGrid_val
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    (physicalOrdinarySourceRowGrid
      formula row inOrdinary).val =
      ((row.val - physicalFormulaRefinementBoundary formula) /
        physDegree formula) %
          physGridCard formula := by
  change
    (physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row).2.1.val = _
  rw [physicalRowOrder_fieldRow,
    paperVariableArityPhysicalOrdinarySourceRowDependentBlockRank
      formula row inOrdinary]
  change
    ((row.val - physicalFormulaRefinementBoundary formula) %
      (physGridCard formula *
        physDegree formula)) /
      physDegree formula = _
  exact Nat.mod_mul_left_div_self
    (row.val - physicalFormulaRefinementBoundary formula)
    (physDegree formula)
    (physGridCard formula)

theorem paperVariableArityPhysicalOrdinarySourceRowBasis_val
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula)) :
    (physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row).2.2.val =
      row.val % physDegree formula := by
  exact physicalRowOrder_basis_val
    (encodeThreeCNF formula).length formula row

theorem paperVariableArityPhysicalOrdinarySourceRowMoment_val
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    (physicalOrdinarySourceRowTableMoment
      formula row inOrdinary).2.val =
      (((row.val - physicalFormulaRefinementBoundary formula) /
        physDegree formula) /
          physGridCard formula) %
            physicalFormulaMomentCount formula := by
  change
    ((paperOrdinaryFamilyWordOrder formula
      (physicalInterpolationMomentBudget formula)
      (physicalOrdinarySourceRowFamilyCoordinate
        formula row inOrdinary)).2).val = _
  simp only [paperOrdinaryFamilyWordOrder,
    Equiv.trans_apply, Equiv.prodCongr_apply,
    finProdFinEquiv_symm_apply]
  change
    ((row.val - physicalFormulaRefinementBoundary formula) /
      (physGridCard formula *
        physDegree formula)) %
      physicalFormulaMomentCount formula = _
  congr 1
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm]

end PhysicalOrdinaryInterpolationRowGridBasisCorrectness

namespace PhysicalInterpolationNodeCountBounds

open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalColumnOrderProjection
open GapCVP.SourceFieldMomentOperationsTM GapCVP.PhysicalMaskedInterpolationNodeParityTM

private def paperVariableArityPhysicalInterpolationSourceMomentIndex
    (family : Fin 4) (row : ℕ) (formula : ThreeCNF) :
    Fin (explicitMomentBudget (encodeThreeCNF formula).length
      (srcFormula formula) + 1) := by
  refine ⟨physicalFamilyRowMoment family row formula, ?_⟩
  change physicalFamilyRowMoment family row formula <
    physicalFormulaMomentCount formula
  unfold physicalFamilyRowMoment
  exact Nat.mod_lt _
    (physicalFormulaMomentCount_pos formula)

theorem physicalInterpolationExplicitGridCardinality_eq
    (formula : ThreeCNF) :
    Fintype.card
        (ExplicitGridPoint (encodeThreeCNF formula).length
          (srcFormula formula)) =
      2 ^ physDegree formula -
        (srcFormula formula).variableCount := by
  calc
    Fintype.card
        (ExplicitGridPoint (encodeThreeCNF formula).length
          (srcFormula formula)) =
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
          (encodeThreeCNF formula).length
          (srcFormula formula)).card := by
          simp only [ExplicitGridPoint, Fintype.card_coe]
    _ = physGridCard formula :=
      physicalFormulaGridCardinality_eq_card formula
    _ = 2 ^ physDegree formula -
        (srcFormula formula).variableCount := by
      change 2 ^ physDegree formula -
        paperVariableArityVariableCount formula = _
      rw [paperVariableAritySourceFormula_variableCount]

theorem physicalOrdinaryInterpolationNodeCount_le_grid
    (formula : ThreeCNF) (row : ℕ) :
    physicalOrdinaryInterpolationNodeCount row formula ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount := by
  have degree := explicitOrdinaryDegree_lt_grid
    (encodeThreeCNF formula).length
    (srcFormula formula)
    (paperVariableArityPhysicalInterpolationSourceMomentIndex
      (2 : Fin 4) row formula)
  rw [physicalInterpolationExplicitGridCardinality_eq]
    at degree
  change
    (srcFormula formula).variableCount *
      physicalFamilyRowMoment (2 : Fin 4) row formula <
      2 ^ physDegree formula -
        (srcFormula formula).variableCount at degree
  unfold physicalOrdinaryInterpolationNodeCount
  change paperVariableArityVariableCount formula *
      physicalFamilyRowMoment (2 : Fin 4) row formula + 1 ≤
    2 ^ physDegree formula -
      (srcFormula formula).variableCount
  rw [paperVariableAritySourceFormula_variableCount] at degree
  exact Nat.succ_le_of_lt degree

theorem physicalShiftedInterpolationNodeCount_le_grid
    (formula : ThreeCNF) (row : ℕ) :
    physicalShiftedInterpolationNodeCount row formula ≤
      2 ^ physDegree formula -
        (srcFormula formula).variableCount := by
  have degree := explicitShiftedDegree_lt_grid
    (encodeThreeCNF formula).length
    (srcFormula formula)
    (paperVariableArityPhysicalInterpolationSourceMomentIndex
      (3 : Fin 4) row formula)
  rw [physicalInterpolationExplicitGridCardinality_eq]
    at degree
  change
    ((srcFormula formula).variableCount - 1) *
      physicalFamilyRowMoment (3 : Fin 4) row formula <
      2 ^ physDegree formula -
        (srcFormula formula).variableCount at degree
  unfold physicalShiftedInterpolationNodeCount
  change (paperVariableArityVariableCount formula - 1) *
      physicalFamilyRowMoment (3 : Fin 4) row formula + 1 ≤
    2 ^ physDegree formula -
      (srcFormula formula).variableCount
  rw [paperVariableAritySourceFormula_variableCount] at degree
  exact Nat.succ_le_of_lt degree

end PhysicalInterpolationNodeCountBounds

namespace BinaryCompactSourceVariableRankTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceNormalizedVariableRankScanTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinarySourceVariableCompaction
open GapCVP.BinaryCompactRankPrefixIdentity GapCVP.BinaryCompactSourceFirstOccurrenceTM

private def compactSourceVariableRankPreparation (input : List Bool) : List Bool :=
  sourceNormalizedVariableRankOutput input ++
    false :: compactFirstOccurrenceScanSeed (firstFieldSuffix input)

private noncomputable def compactSourceVariableRankPreparationComputable :
    BitTM
      compactSourceVariableRankPreparation := by
  have hseed := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable compactFirstOccurrenceScanSeedComputable
  have hdelimited := GapCVP.TMComposition.computableInPolyTime
    hseed (prependBitComputable false)
  exact pointwiseAppendComputable
    sourceNormalizedVariableRankComputable hdelimited

private def compactSourceVariableRankUnary : List Bool → List Bool :=
  compactFirstOccurrenceCounter ∘
    boundedRecordFoldOutput compactFirstOccurrenceScanStep ∘
    compactSourceVariableRankPreparation

private noncomputable def compactSourceVariableRankUnaryComputable :
    BitTM
      compactSourceVariableRankUnary := by
  have hfold := GapCVP.TMComposition.computableInPolyTime
    compactSourceVariableRankPreparationComputable
    compactFirstOccurrenceScanFoldComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hfold compactFirstOccurrenceCounterComputable

private theorem compactSourceVariableRawRank_le_literalLength
    (formula : ThreeCNF) (name : ℕ) :
    variableRank formula name ≤
      (sourceNormalizedVariableLiteralList formula).length := by
  unfold variableRank
  calc
    (formulaVariables formula).idxOf name ≤
        (formulaVariables formula).length := List.idxOf_le_length
    _ = (sourceNormalizedVariableLiteralList formula).length := by
      rw [← sourceNormalizedVariableLiteralList_variables,
        List.length_map]

private theorem compactSourceVariableRankPreparation_valid
    (formula : ThreeCNF) (name : ℕ) :
    compactSourceVariableRankPreparation
        (sourceNormalizedVariableRankQuery name formula) =
      unaryBoundedFoldWord (variableRank formula name)
        (compactFirstOccurrenceValidState formula 0 0
          (sourceNormalizedVariableLiteralList formula)) := by
  unfold compactSourceVariableRankPreparation
  rw [sourceNormalizedVariableRankOutput_valid]
  have hsource :
      firstFieldSuffix
        (sourceNormalizedVariableRankQuery name formula) =
          encodeThreeCNF formula := by
    simp only [sourceNormalizedVariableRankQuery, firstFieldSuffix_valid]
  rw [hsource, compactFirstOccurrenceScanSeed_valid]
  rfl

private theorem compactSourceVariableRankUnary_valid
    (formula : ThreeCNF) (name : ℕ) :
    compactSourceVariableRankUnary
        (sourceNormalizedVariableRankQuery name formula) =
      List.replicate (compactVariableRank formula name) true := by
  unfold compactSourceVariableRankUnary
  rw [Function.comp_apply, Function.comp_apply,
    compactSourceVariableRankPreparation_valid]
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word]
  rw [compactFirstOccurrenceValidState_iterate
    formula (variableRank formula name)
    (compactSourceVariableRawRank_le_literalLength formula name)]
  rw [compactFirstOccurrenceValidState_counter,
    ← compactVariableRank_eq_firstOccurrencePrefixCount]

end BinaryCompactSourceVariableRankTM

namespace ShiftedTupleBetaSourceCorrectness

open Turing GapCVP.BinaryEncoding GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
open GapCVP.SourceNormalizedVariableRankScanTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryCompactSourceVariableRankTM
open GapCVP.BinarySourceVariableCompaction GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingTM GapCVP.SourcePreprocessingSemantics
open GapCVP.SourcePreprocessingPairwiseIdentity
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
open GapCVP.ShiftedTupleBetaTM

private theorem paperVariableArityShiftedTupleOriginalSignWord_query
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (hrank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true)
    (position : Fin 3) :
    paperShiftedTupleOriginalSignWord ranks position
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [(((noTautClauses formula).get
        ⟨rank, hbound⟩) position).2] := by
  unfold paperShiftedTupleOriginalSignWord
  rw [Function.comp_apply,
    paperShiftedTupleOriginalClauseWord_query
      ranks row column formula rank hbound hrank]
  simpa only [List.get_eq_getElem, List.append_nil] using
      paperSourceClauseSignWord_valid position ((noTautClauses formula).get ⟨rank, hbound⟩) []

private theorem paperVariableArityShiftedTupleOriginalSecondKeepBit_query
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (hrank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true) :
    paperShiftedTupleOriginalSecondKeepBit ranks
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [!(decide
        (((noTautClauses formula).get
            ⟨rank, hbound⟩) 0 =
          ((noTautClauses formula).get
            ⟨rank, hbound⟩) 1))] := by
  unfold paperShiftedTupleOriginalSecondKeepBit
  rw [Function.comp_apply,
    paperShiftedTupleOriginalClauseWord_query
      ranks row column formula rank hbound hrank]
  simpa only [List.get_eq_getElem, Fin.isValue, List.append_nil] using
      paperSourceClauseSecondKeepMarker_valid ((noTautClauses formula).get ⟨rank, hbound⟩) []

private def paperShiftedTupleOriginalVariableWord
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) : List Bool → List Bool :=
  paperSourceClauseVariableWord position ∘
    paperShiftedTupleOriginalClauseWord ranks

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityShiftedTupleOriginalVariableWordComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) :
    BitTM
      (paperShiftedTupleOriginalVariableWord ranks position) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityShiftedTupleOriginalClauseWordComputable ranks)
    (paperSourceClauseVariableWordComputable position)

private theorem paperVariableArityShiftedTupleOriginalVariableWord_query
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (hrank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true)
    (position : Fin 3) :
    paperShiftedTupleOriginalVariableWord ranks position
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      Computability.encodeNat
        (((noTautClauses formula).get
          ⟨rank, hbound⟩) position).1 := by
  unfold paperShiftedTupleOriginalVariableWord
  rw [Function.comp_apply,
    paperShiftedTupleOriginalClauseWord_query
      ranks row column formula rank hbound hrank]
  simpa only [List.get_eq_getElem, List.append_nil] using
      paperSourceClauseVariableWord_valid position ((noTautClauses formula).get ⟨rank, hbound⟩) []

private def paperShiftedTupleSelectedSourceWord
    (marker first second : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  paperShiftedTupleGuardedSourceWord marker first input ++
    paperShiftedTupleGuardedSourceWord
      (sourceFourFamilyBooleanNotOutput marker) second input

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityShiftedTupleSelectedSourceWordComputable
    {marker first second : List Bool → List Bool}
    (hmarker : BitTM marker)
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (paperShiftedTupleSelectedSourceWord
        marker first second) :=
  pointwiseAppendComputable
    (paperVariableArityShiftedTupleGuardedSourceWordComputable
      hmarker hfirst)
    (paperVariableArityShiftedTupleGuardedSourceWordComputable
      (fourFamilyBooleanNotOutputComputable hmarker) hsecond)

private theorem paperVariableArityShiftedTupleSelectedSourceWord_valid
    (marker first second : List Bool → List Bool)
    (input : List Bool) (selector : Bool)
    (hmarker : marker input = [selector]) :
    paperShiftedTupleSelectedSourceWord
      marker first second input =
      if selector then first input else second input := by
  have hnot := fourFamilyBooleanNotOutput_bit
    marker input selector hmarker
  unfold paperShiftedTupleSelectedSourceWord
  rw [paperShiftedTupleGuardedSourceWord_valid
    marker first input selector hmarker,
    paperShiftedTupleGuardedSourceWord_valid
      (sourceFourFamilyBooleanNotOutput marker) second
      input (!selector) hnot]
  cases selector <;> simp

private def paperShiftedTupleNormalizedVariableWord
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) : List Bool → List Bool :=
  if position.val = 0 then
    paperShiftedTupleOriginalVariableWord ranks 0
  else if position.val = 1 then
    paperShiftedTupleSelectedSourceWord
      (paperShiftedTupleOriginalSecondKeepBit ranks)
      (paperShiftedTupleOriginalVariableWord ranks 1)
      (paperShiftedTupleOriginalVariableWord ranks 2)
  else
    paperShiftedTupleOriginalVariableWord ranks 2

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityShiftedTupleNormalizedVariableWordComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) :
    BitTM
      (paperShiftedTupleNormalizedVariableWord
        ranks position) := by
  unfold paperShiftedTupleNormalizedVariableWord
  split
  · exact paperVariableArityShiftedTupleOriginalVariableWordComputable
      ranks 0
  next =>
    split
    · exact paperVariableArityShiftedTupleSelectedSourceWordComputable
        (paperVariableArityShiftedTupleOriginalSecondKeepBitComputable ranks)
        (paperVariableArityShiftedTupleOriginalVariableWordComputable ranks 1)
        (paperVariableArityShiftedTupleOriginalVariableWordComputable ranks 2)
    · exact paperVariableArityShiftedTupleOriginalVariableWordComputable
        ranks 2

/-- GapCVP reduction support. -/
def paperShiftedTuplePotentialNormalizedLiteral
    (clause : ThreeClause) (position : Fin 3) : Literal :=
  if position.val = 0 then clause 0
  else if position.val = 1 then
    if clause 0 = clause 1 then clause 2 else clause 1
  else clause 2

theorem paperVariableArityShiftedTuplePotentialNormalizedLiteral_get
    (clause : ThreeClause) (position : Fin 3)
    (hposition : position.val <
      (paperSourceNormalizedClause clause).length) :
    paperShiftedTuplePotentialNormalizedLiteral
      clause position =
      (paperSourceNormalizedClause clause).get
        ⟨position.val, hposition⟩ := by
  have hlength := hposition
  rw [paperSourceNormalizedClause_pairwise clause] at hlength
  fin_cases position <;>
    by_cases hfirst : clause 0 = clause 1 <;>
    by_cases hsecond : clause 0 = clause 2 <;>
    by_cases hthird : clause 1 = clause 2 <;>
    simp_all [paperShiftedTuplePotentialNormalizedLiteral,
      paperSourceNormalizedClause_pairwise]

theorem paperVariableArityShiftedTupleNormalizedSignWord_potential_query
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (hrank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true)
    (position : Fin 3) :
    paperShiftedTupleNormalizedSignWord ranks position
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [(paperShiftedTuplePotentialNormalizedLiteral
        ((noTautClauses formula).get
          ⟨rank, hbound⟩) position).2] := by
  let clause : ThreeClause :=
    (noTautClauses formula).get ⟨rank, hbound⟩
  let input := affineCellQuery row column
    (encodeThreeCNF formula)
  have hzero := paperVariableArityShiftedTupleOriginalSignWord_query
    ranks row column formula rank hbound hrank 0
  have hone := paperVariableArityShiftedTupleOriginalSignWord_query
    ranks row column formula rank hbound hrank 1
  have htwo := paperVariableArityShiftedTupleOriginalSignWord_query
    ranks row column formula rank hbound hrank 2
  have hkeep := paperVariableArityShiftedTupleOriginalSecondKeepBit_query
    ranks row column formula rank hbound hrank
  have hselect := paperVariableArityShiftedTupleSelectedSourceBit_valid
    (paperShiftedTupleOriginalSecondKeepBit ranks)
    (paperShiftedTupleOriginalSignWord ranks 1)
    (paperShiftedTupleOriginalSignWord ranks 2)
    input (!(decide (clause 0 = clause 1)))
    (clause 1).2 (clause 2).2 hkeep hone htwo
  fin_cases position
  · simpa only [paperShiftedTupleNormalizedSignWord, ↓reduceIte, Fin.isValue,
        paperShiftedTuplePotentialNormalizedLiteral, List.get_eq_getElem] using hzero
  · by_cases hequal : clause 0 = clause 1
    · change paperShiftedTupleSelectedSourceBit
        (paperShiftedTupleOriginalSecondKeepBit ranks)
        (paperShiftedTupleOriginalSignWord ranks 1)
        (paperShiftedTupleOriginalSignWord ranks 2)
        input =
        [(paperShiftedTuplePotentialNormalizedLiteral
          clause 1).2]
      simpa only [Fin.isValue, paperShiftedTuplePotentialNormalizedLiteral, Fin.coe_ofNat_eq_mod,
          Nat.one_mod,
          one_ne_zero, ↓reduceIte, hequal, decide_true, Bool.not_true, Bool.false_eq_true]
              using hselect
    · change paperShiftedTupleSelectedSourceBit
        (paperShiftedTupleOriginalSecondKeepBit ranks)
        (paperShiftedTupleOriginalSignWord ranks 1)
        (paperShiftedTupleOriginalSignWord ranks 2)
        input =
        [(paperShiftedTuplePotentialNormalizedLiteral
          clause 1).2]
      simpa only [Fin.isValue, paperShiftedTuplePotentialNormalizedLiteral, Fin.coe_ofNat_eq_mod,
          Nat.one_mod,
          one_ne_zero, ↓reduceIte, hequal, decide_false, Bool.not_false] using hselect
  · simpa only [paperShiftedTupleNormalizedSignWord, OfNat.ofNat_ne_zero, ↓reduceIte,
      OfNat.ofNat_ne_one,
        Fin.isValue, paperShiftedTuplePotentialNormalizedLiteral, List.get_eq_getElem] using htwo

private theorem paperVariableArityShiftedTupleNormalizedVariableWord_potential_query
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (hrank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true)
    (position : Fin 3) :
    paperShiftedTupleNormalizedVariableWord ranks position
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      Computability.encodeNat
        (paperShiftedTuplePotentialNormalizedLiteral
          ((noTautClauses formula).get
            ⟨rank, hbound⟩) position).1 := by
  let clause : ThreeClause :=
    (noTautClauses formula).get ⟨rank, hbound⟩
  let input := affineCellQuery row column
    (encodeThreeCNF formula)
  have hzero := paperVariableArityShiftedTupleOriginalVariableWord_query
    ranks row column formula rank hbound hrank 0
  have hone := paperVariableArityShiftedTupleOriginalVariableWord_query
    ranks row column formula rank hbound hrank 1
  have htwo := paperVariableArityShiftedTupleOriginalVariableWord_query
    ranks row column formula rank hbound hrank 2
  have hkeep := paperVariableArityShiftedTupleOriginalSecondKeepBit_query
    ranks row column formula rank hbound hrank
  have hselect := paperVariableArityShiftedTupleSelectedSourceWord_valid
    (paperShiftedTupleOriginalSecondKeepBit ranks)
    (paperShiftedTupleOriginalVariableWord ranks 1)
    (paperShiftedTupleOriginalVariableWord ranks 2)
    input (!(decide (clause 0 = clause 1))) hkeep
  fin_cases position
  · simpa only [paperShiftedTupleNormalizedVariableWord, ↓reduceIte, Fin.isValue,
        paperShiftedTuplePotentialNormalizedLiteral, List.get_eq_getElem] using hzero
  · by_cases hequal : clause 0 = clause 1
    · change paperShiftedTupleSelectedSourceWord
        (paperShiftedTupleOriginalSecondKeepBit ranks)
        (paperShiftedTupleOriginalVariableWord ranks 1)
        (paperShiftedTupleOriginalVariableWord ranks 2)
        input = Computability.encodeNat
          (paperShiftedTuplePotentialNormalizedLiteral
            clause 1).1
      simp only [paperShiftedTuplePotentialNormalizedLiteral,
        Fin.isValue, ↓reduceIte, hequal]
      calc
        paperShiftedTupleSelectedSourceWord
            (paperShiftedTupleOriginalSecondKeepBit ranks)
            (paperShiftedTupleOriginalVariableWord ranks 1)
            (paperShiftedTupleOriginalVariableWord ranks 2)
            input =
            paperShiftedTupleOriginalVariableWord
              ranks 2 input := by simpa only [Fin.isValue, hequal, decide_true, Bool.not_true,
                  Bool.false_eq_true, ↓reduceIte] using hselect
        _ = Computability.encodeNat (clause 2).1 := by
          simpa only [Fin.isValue, List.get_eq_getElem, input, clause] using htwo
    · change paperShiftedTupleSelectedSourceWord
        (paperShiftedTupleOriginalSecondKeepBit ranks)
        (paperShiftedTupleOriginalVariableWord ranks 1)
        (paperShiftedTupleOriginalVariableWord ranks 2)
        input = Computability.encodeNat
          (paperShiftedTuplePotentialNormalizedLiteral
            clause 1).1
      simp only [paperShiftedTuplePotentialNormalizedLiteral,
        Fin.isValue, ↓reduceIte, hequal]
      calc
        paperShiftedTupleSelectedSourceWord
            (paperShiftedTupleOriginalSecondKeepBit ranks)
            (paperShiftedTupleOriginalVariableWord ranks 1)
            (paperShiftedTupleOriginalVariableWord ranks 2)
            input =
            paperShiftedTupleOriginalVariableWord
              ranks 1 input := by simpa only [Fin.isValue, hequal, decide_false, Bool.not_false,
                  ↓reduceIte] using hselect
        _ = Computability.encodeNat (clause 1).1 := by
          simpa only [Fin.isValue, List.get_eq_getElem, input, clause] using hone
  · simpa only [paperShiftedTupleNormalizedVariableWord, OfNat.ofNat_ne_zero, ↓reduceIte,
      OfNat.ofNat_ne_one,
        Fin.isValue, paperShiftedTuplePotentialNormalizedLiteral, List.get_eq_getElem] using htwo

private theorem paperVariableArityShiftedTupleNormalizedVariableWord_query
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (hrank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true)
    (position : Fin 3)
    (hposition : position.val <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, hbound⟩)).length) :
    paperShiftedTupleNormalizedVariableWord ranks position
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      Computability.encodeNat
        ((paperSourceNormalizedClause
          ((noTautClauses formula).get
            ⟨rank, hbound⟩)).get
              ⟨position.val, hposition⟩).1 := by
  rw [paperVariableArityShiftedTupleNormalizedVariableWord_potential_query
    ranks row column formula rank hbound hrank position,
    paperVariableArityShiftedTuplePotentialNormalizedLiteral_get
      ((noTautClauses formula).get
        ⟨rank, hbound⟩) position hposition]

private def paperShiftedTupleLocalPositionMarker
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) : List Bool → List Bool :=
  maskComputedWordEquality
    ranks.variablePosition.output
    (paperShiftedTupleConstantUnary position.val)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityShiftedTupleLocalPositionMarkerComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) :
    BitTM
      (paperShiftedTupleLocalPositionMarker
        ranks position) :=
  maskComputedWordEqualityComputable
    ranks.variablePosition.computer
    (paperVariableArityShiftedTupleConstantUnaryComputable position.val)

private theorem paperVariableArityShiftedTupleLocalPositionMarker_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (slot : Fin 3) (input : List Bool) (position : ℕ)
    (hposition : ranks.variablePosition.output input =
      List.replicate position true) :
    paperShiftedTupleLocalPositionMarker ranks slot input =
      [decide (position = slot.val)] := by
  unfold paperShiftedTupleLocalPositionMarker
  rw [sourceQaryMaskSquareComputedWordEquality_valid, hposition]
  simp only [paperShiftedTupleConstantUnary, List.replicate_inj, or_true, and_true]

private def paperShiftedTupleSelectedNormalizedVariableWord
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (input : List Bool) : List Bool :=
  paperShiftedTupleGuardedSourceWord
    (paperShiftedTupleLocalPositionMarker ranks 0)
    (paperShiftedTupleNormalizedVariableWord ranks 0)
    input ++
    (paperShiftedTupleGuardedSourceWord
      (paperShiftedTupleLocalPositionMarker ranks 1)
      (paperShiftedTupleNormalizedVariableWord ranks 1)
      input ++
      paperShiftedTupleGuardedSourceWord
        (paperShiftedTupleLocalPositionMarker ranks 2)
        (paperShiftedTupleNormalizedVariableWord ranks 2)
        input)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityShiftedTupleSelectedNormalizedVariableWordComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperShiftedTupleSelectedNormalizedVariableWord ranks) :=
  pointwiseAppendComputable
    (paperVariableArityShiftedTupleGuardedSourceWordComputable
      (paperVariableArityShiftedTupleLocalPositionMarkerComputable ranks 0)
      (paperVariableArityShiftedTupleNormalizedVariableWordComputable ranks 0))
    (pointwiseAppendComputable
      (paperVariableArityShiftedTupleGuardedSourceWordComputable
        (paperVariableArityShiftedTupleLocalPositionMarkerComputable ranks 1)
        (paperVariableArityShiftedTupleNormalizedVariableWordComputable ranks 1))
      (paperVariableArityShiftedTupleGuardedSourceWordComputable
        (paperVariableArityShiftedTupleLocalPositionMarkerComputable ranks 2)
        (paperVariableArityShiftedTupleNormalizedVariableWordComputable ranks 2)))

private theorem paperVariableArityShiftedTupleSelectedNormalizedVariableWord_query
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (hrank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true)
    (position : ℕ)
    (hposition : position <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, hbound⟩)).length)
    (hlocal : ranks.variablePosition.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate position true) :
    paperShiftedTupleSelectedNormalizedVariableWord ranks
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      Computability.encodeNat
        ((paperSourceNormalizedClause
          ((noTautClauses formula).get
            ⟨rank, hbound⟩)).get
              ⟨position, hposition⟩).1 := by
  let input := affineCellQuery row column
    (encodeThreeCNF formula)
  have hzero := paperVariableArityShiftedTupleLocalPositionMarker_valid
    ranks 0 input position hlocal
  have hone := paperVariableArityShiftedTupleLocalPositionMarker_valid
    ranks 1 input position hlocal
  have htwo := paperVariableArityShiftedTupleLocalPositionMarker_valid
    ranks 2 input position hlocal
  change paperShiftedTupleSelectedNormalizedVariableWord
    ranks input = _
  unfold paperShiftedTupleSelectedNormalizedVariableWord
  rw [paperShiftedTupleGuardedSourceWord_valid
    (paperShiftedTupleLocalPositionMarker ranks 0)
    (paperShiftedTupleNormalizedVariableWord ranks 0)
    input (decide (position = 0)) hzero,
    paperShiftedTupleGuardedSourceWord_valid
      (paperShiftedTupleLocalPositionMarker ranks 1)
      (paperShiftedTupleNormalizedVariableWord ranks 1)
      input (decide (position = 1)) hone,
    paperShiftedTupleGuardedSourceWord_valid
      (paperShiftedTupleLocalPositionMarker ranks 2)
      (paperShiftedTupleNormalizedVariableWord ranks 2)
      input (decide (position = 2)) htwo]
  have hthree : position < 3 := lt_of_lt_of_le hposition
    (paperNormalizedClause_length_le_three
      ((noTautClauses formula).get
        ⟨rank, hbound⟩))
  have hcases : position = 0 ∨ position = 1 ∨ position = 2 := by
    omega
  rcases hcases with hcase | hcase | hcase
  · subst position
    simpa only [decide_true, ↓reduceIte, Fin.isValue, zero_ne_one, decide_false,
        Bool.false_eq_true,
        OfNat.zero_ne_ofNat, List.append_nil, List.get_eq_getElem, Fin.coe_ofNat_eq_mod,
            Nat.zero_mod] using
        paperVariableArityShiftedTupleNormalizedVariableWord_query ranks row column formula rank
            hbound hrank 0 hposition
  · subst position
    simpa only [one_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte, decide_true,
        Fin.isValue,
        OfNat.one_ne_ofNat, List.append_nil, List.nil_append, List.get_eq_getElem,
            Fin.coe_ofNat_eq_mod, Nat.one_mod] using
        paperVariableArityShiftedTupleNormalizedVariableWord_query ranks row column formula rank
            hbound hrank 1 hposition
  · subst position
    simpa only [OfNat.ofNat_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte,
        OfNat.ofNat_ne_one,
        decide_true, Fin.isValue, List.nil_append, List.get_eq_getElem, Fin.coe_ofNat_eq_mod,
            Nat.mod_succ] using
        paperVariableArityShiftedTupleNormalizedVariableWord_query ranks row column formula rank
            hbound hrank 2 hposition

private def paperShiftedTupleRetainedAnchorRankQuery
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (paperShiftedTupleSelectedNormalizedVariableWord
        ranks input) ++
    paperShiftedTupleRetainedSource input

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityShiftedTupleRetainedAnchorRankQueryComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperShiftedTupleRetainedAnchorRankQuery ranks) := by
  have hname := GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityShiftedTupleSelectedNormalizedVariableWordComputable
      ranks)
    structuralPrefixWriterComputable
  exact pointwiseAppendComputable hname
    paperVariableArityShiftedTupleRetainedSourceComputable

private theorem paperVariableArityShiftedTupleRetainedAnchorRankQuery_query
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (hrank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true)
    (position : ℕ)
    (hposition : position <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, hbound⟩)).length)
    (hlocal : ranks.variablePosition.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate position true) :
    paperShiftedTupleRetainedAnchorRankQuery ranks
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      sourceNormalizedVariableRankQuery
        ((paperSourceNormalizedClause
          ((noTautClauses formula).get
            ⟨rank, hbound⟩)).get
              ⟨position, hposition⟩).1
        (noTautClauses formula) := by
  unfold paperShiftedTupleRetainedAnchorRankQuery
  rw [paperVariableArityShiftedTupleSelectedNormalizedVariableWord_query
    ranks row column formula rank hbound hrank position hposition hlocal,
    paperVariableArityShiftedTupleRetainedSource_query]
  rfl

private def paperShiftedTupleRetainedAnchorRankUnary
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  compactSourceVariableRankUnary ∘
    paperShiftedTupleRetainedAnchorRankQuery ranks

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityShiftedTupleRetainedAnchorRankUnaryComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperShiftedTupleRetainedAnchorRankUnary ranks) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityShiftedTupleRetainedAnchorRankQueryComputable ranks)
    compactSourceVariableRankUnaryComputable

private theorem paperVariableArityShiftedTupleRetainedAnchorRankUnary_query
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (hrank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true)
    (position : ℕ)
    (hposition : position <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, hbound⟩)).length)
    (hlocal : ranks.variablePosition.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate position true) :
    paperShiftedTupleRetainedAnchorRankUnary ranks
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (compactVariableRank (noTautClauses formula)
          ((paperSourceNormalizedClause
            ((noTautClauses formula).get
              ⟨rank, hbound⟩)).get
                ⟨position, hposition⟩).1) true := by
  unfold paperShiftedTupleRetainedAnchorRankUnary
  rw [Function.comp_apply,
    paperVariableArityShiftedTupleRetainedAnchorRankQuery_query
      ranks row column formula rank hbound hrank
      position hposition hlocal]
  exact compactSourceVariableRankUnary_valid
    (noTautClauses formula)
    ((paperSourceNormalizedClause
      ((noTautClauses formula).get
        ⟨rank, hbound⟩)).get
          ⟨position, hposition⟩).1

private noncomputable def paperShiftedTupleRetainedAnchorRankComputer
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    SourcePhysicalLagrangeWordComputer where
  output := paperShiftedTupleRetainedAnchorRankUnary ranks
  computer :=
    paperVariableArityShiftedTupleRetainedAnchorRankUnaryComputable ranks

/-- GapCVP reduction support. -/
def paperShiftedTupleRetainedAnchorFieldWord
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  physicalCellFieldWordAt
    (paperShiftedTupleRetainedAnchorRankComputer ranks)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityShiftedTupleRetainedAnchorFieldWordComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperShiftedTupleRetainedAnchorFieldWord ranks) :=
  physicalCellFieldWordAtComputable
    (paperShiftedTupleRetainedAnchorRankComputer ranks)

/-- GapCVP reduction support. -/
noncomputable def paperShiftedTupleRetainedAnchorFieldComputer
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    SourcePhysicalLagrangeWordComputer where
  output := paperShiftedTupleRetainedAnchorFieldWord ranks
  computer :=
    paperVariableArityShiftedTupleRetainedAnchorFieldWordComputable ranks

end ShiftedTupleBetaSourceCorrectness

namespace SourceVariableRankBridge

open Turing GapCVP.SourceMachineCert GapCVP.BinarySourceVariableCompaction
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.SourcePreprocessingPairwiseIdentity GapCVP.FormulaBridge

private theorem paperVariableArityReverseNameEquality_false
    {first second : ℕ} (hne : first ≠ second) :
    (second == first) = false := by
  exact beq_eq_false_iff_ne.mpr (Ne.symm hne)

private theorem paperVariableAritySignedTripleFirstOccurrence_prefix_suffix
    (seen : List ℕ) (first second third : Literal)
    (suffix : List ℕ) :
    (seen ++ [first.1, second.1, third.1] ++ suffix).eraseDups =
      (seen ++ ([first, second, third].eraseDups).map Prod.fst ++
        suffix).eraseDups := by
  classical
  rw [paperSourceEraseDupsThree_pairwise]
  by_cases hfirst : first = second <;>
    by_cases hsecond : first = third <;>
    by_cases hthird : second = third <;>
    by_cases hname : first.1 = second.1 <;>
    by_cases hseenFirst : first.1 ∈ seen <;>
    by_cases hseenSecond : second.1 ∈ seen <;>
    by_cases hseenThird : third.1 ∈ seen <;>
      simp_all [List.eraseDups_append, List.removeAll,
        List.eraseDups_cons,
        paperVariableArityReverseNameEquality_false]

private theorem paperVariableAritySignedClauseStreamFirstOccurrence
    (clauses : List ThreeClause) (seen suffix : List ℕ) :
    (seen ++ formulaVariables clauses ++ suffix).eraseDups =
      (seen ++
        (clauses.flatMap fun clause =>
          (paperSourceNormalizedClause clause).map Prod.fst) ++
        suffix).eraseDups := by
  induction clauses generalizing seen with
  | nil =>
      simp only [formulaVariables, Fin.isValue, List.flatMap_nil, List.append_nil]
  | cons clause remaining ih =>
      have head := paperVariableAritySignedTripleFirstOccurrence_prefix_suffix
        seen (clause 0) (clause 1) (clause 2)
        (formulaVariables remaining ++ suffix)
      have rest := ih
        (seen ++ (paperSourceNormalizedClause clause).map Prod.fst)
      calc
        (seen ++ formulaVariables (clause :: remaining) ++ suffix).eraseDups =
            (seen ++ [(clause 0).1, (clause 1).1, (clause 2).1] ++
              (formulaVariables remaining ++ suffix)).eraseDups := by
                simp only [formulaVariables, Fin.isValue, List.flatMap_cons, List.cons_append,
                    List.nil_append,
                    List.append_assoc]
        _ = (seen ++ (paperSourceNormalizedClause clause).map Prod.fst ++
              (formulaVariables remaining ++ suffix)).eraseDups := by
                simpa only [Fin.isValue, List.append_assoc, List.cons_append, List.nil_append,
                    paperSourceNormalizedClause,
                    paperSourceClauseLiterals] using head
        _ = (seen ++ (paperSourceNormalizedClause clause).map Prod.fst ++
              ((remaining.flatMap fun item =>
                (paperSourceNormalizedClause item).map Prod.fst) ++
                suffix)).eraseDups := by
                simpa only [List.append_assoc] using rest
        _ = (seen ++
              ((clause :: remaining).flatMap fun item =>
                (paperSourceNormalizedClause item).map Prod.fst) ++
              suffix).eraseDups := by
                simp only [List.append_assoc, List.flatMap_cons]

private theorem paperVariableArityRetainedOccurringVariables_eq
    (formula : ThreeCNF) :
    occurringVariables
        (noTautClauses formula) =
      paperNormalizedOccurringVariables formula := by
  have source := paperVariableAritySignedClauseStreamFirstOccurrence
    (noTautClauses formula) [] []
  simpa only [occurringVariables, paperNormalizedOccurringVariables,
      paperSourceNormalizedVariables,
      paperSourceNormalizedClauses, List.flatMap_map, List.nil_append, List.append_nil]
          using source

private theorem paperVariableArityCompactVariableRank_eq
    (formula : ThreeCNF) (name : ℕ) :
    compactVariableRank
        (noTautClauses formula) name =
      paperVariableArityVariableRank formula name := by
  unfold compactVariableRank paperVariableArityVariableRank
  rw [paperVariableArityRetainedOccurringVariables_eq]

end SourceVariableRankBridge

namespace ShiftedTupleAnchorSourceFieldCorrectness

open Turing GapCVP.BinaryEncoding GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.FormulaBridge GapCVP.SourceVariableRankBridge
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
open GapCVP.ShiftedTupleBetaTM GapCVP.ShiftedTupleBetaSourceCorrectness

theorem paperShiftedTupleRetainedNormalizedClause_mem
    (formula : ThreeCNF) (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length) :
    paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, hbound⟩) ∈ paperSourceNormalizedClauses formula := by
  unfold paperSourceNormalizedClauses
  apply List.mem_map.mpr
  exact ⟨(noTautClauses formula).get
    ⟨rank, hbound⟩,
    List.get_mem _ ⟨rank, hbound⟩, rfl⟩

/-- GapCVP reduction support. -/
def paperShiftedTupleSelectedSourceVariableIndex
    (formula : ThreeCNF) (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (position : ℕ)
    (hposition : position <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, hbound⟩)).length) :
    Fin (paperVariableArityVariableCount formula) :=
  ⟨paperVariableArityVariableRank formula
    ((paperSourceNormalizedClause
      ((noTautClauses formula).get
        ⟨rank, hbound⟩)).get ⟨position, hposition⟩).1,
    paperVariableArityVariableRank_lt formula
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, hbound⟩))
      (paperShiftedTupleRetainedNormalizedClause_mem
        formula rank hbound)
      ((paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, hbound⟩)).get ⟨position, hposition⟩)
      (List.get_mem _ ⟨position, hposition⟩)⟩

private theorem paperVariableArityShiftedTupleRetainedAnchorRankUnary_paper_query
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (hrank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true)
    (position : ℕ)
    (hposition : position <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, hbound⟩)).length)
    (hlocal : ranks.variablePosition.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate position true) :
    paperShiftedTupleRetainedAnchorRankUnary ranks
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (paperVariableArityVariableRank formula
          ((paperSourceNormalizedClause
            ((noTautClauses formula).get
              ⟨rank, hbound⟩)).get
                ⟨position, hposition⟩).1) true := by
  rw [paperVariableArityShiftedTupleRetainedAnchorRankUnary_query
    ranks row column formula rank hbound hrank
    position hposition hlocal,
    paperVariableArityCompactVariableRank_eq]

private theorem paperVariableArityShiftedTupleRetainedAnchorRankComputer_output
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    (paperShiftedTupleRetainedAnchorRankComputer ranks).output =
      paperShiftedTupleRetainedAnchorRankUnary ranks := by
  dsimp only [paperShiftedTupleRetainedAnchorRankComputer]

/-- GapCVP reduction support. -/
def paperShiftedTupleSelectedSourceVariableWord
    (formula : ThreeCNF) (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (position : ℕ)
    (hposition : position <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, hbound⟩)).length) :
    GapCVP.Core.EffectiveBinaryField.Word
      (sourceIrreducibleFormulaDegree formula) :=
  sourceFormulaVariableWord (encodeThreeCNF formula).length
    (srcFormula formula)
    (paperShiftedTupleSelectedSourceVariableIndex
      formula rank hbound position hposition)

theorem paperVariableArityShiftedTupleRetainedAnchorFieldWord_query
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (hrank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true)
    (position : ℕ)
    (hposition : position <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, hbound⟩)).length)
    (hlocal : ranks.variablePosition.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate position true) :
    paperShiftedTupleRetainedAnchorFieldWord ranks
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      finiteWordBits
        (paperShiftedTupleSelectedSourceVariableWord
          formula rank hbound position hposition) := by
  let index := sourceFormulaVariableWordIndex
    (encodeThreeCNF formula).length
    (srcFormula formula)
    (paperShiftedTupleSelectedSourceVariableIndex
      formula rank hbound position hposition)
  have hsource :
      (paperShiftedTupleRetainedAnchorRankComputer ranks).output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
        List.replicate index.val true := by
    rw [paperVariableArityShiftedTupleRetainedAnchorRankComputer_output,
      paperVariableArityShiftedTupleRetainedAnchorRankUnary_paper_query
        ranks row column formula rank hbound hrank
        position hposition hlocal]
    rfl
  have emitted := physicalCellFieldWordAt_valid
    (paperShiftedTupleRetainedAnchorRankComputer ranks)
    row column formula index hsource
  simpa only [index,
    sourceIrreducibleFormulaDegree,
    paperShiftedTupleRetainedAnchorFieldWord,
    paperShiftedTupleSelectedSourceVariableWord,
    sourceFormulaVariableWord] using emitted

theorem paperVariableArityShiftedTupleSelectedSourceVariableWord_sourceField
    (formula : ThreeCNF) (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length)
    (position : ℕ)
    (hposition : position <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, hbound⟩)).length) :
    sourceWordValue (encodeThreeCNF formula).length
      (srcFormula formula)
      (paperShiftedTupleSelectedSourceVariableWord
        formula rank hbound position hposition) =
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
        (encodeThreeCNF formula).length
        (srcFormula formula)
        (paperShiftedTupleSelectedSourceVariableIndex
          formula rank hbound position hposition) := by
  rfl

end ShiftedTupleAnchorSourceFieldCorrectness

namespace ShiftedTupleBetaSourceFieldCorrectness

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceIndexedClauseSignTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalLagrangeMomentWeightTM GapCVP.FormulaBridge
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
open GapCVP.ShiftedTupleBetaTM

private def paperShiftedTupleBetaRankUnary
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  sourceOriginalClauseBooleanUnaryOutput ∘
    paperShiftedTupleBetaBit ranks

private noncomputable def paperVariableArityShiftedTupleBetaRankUnaryComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperShiftedTupleBetaRankUnary ranks) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityShiftedTupleBetaBitComputable ranks)
    sourceOriginalClauseBooleanUnaryComputable

private theorem paperVariableArityShiftedTupleBetaRankUnary_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (input : List Bool) (bit : Bool)
    (hbit : paperShiftedTupleBetaBit ranks input = [bit]) :
    paperShiftedTupleBetaRankUnary ranks input =
      List.replicate (if bit then 1 else 0) true := by
  unfold paperShiftedTupleBetaRankUnary
  rw [Function.comp_apply, hbit]
  exact sourceOriginalClauseBooleanUnaryOutput_bit bit

private noncomputable def paperShiftedTupleBetaRankComputer
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    SourcePhysicalLagrangeWordComputer where
  output := paperShiftedTupleBetaRankUnary ranks
  computer := paperVariableArityShiftedTupleBetaRankUnaryComputable ranks

private theorem paperVariableArityShiftedTupleBetaRankComputer_output
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    (paperShiftedTupleBetaRankComputer ranks).output =
      paperShiftedTupleBetaRankUnary ranks := by
  dsimp only [paperShiftedTupleBetaRankComputer]

private theorem paperVariableArityShiftedTupleSourceFieldDegree_pos
    (formula : ThreeCNF) :
    0 < sourceIrreducibleFormulaDegree formula := by
  unfold sourceIrreducibleFormulaDegree
  exact sourceFieldExponent_pos
    (sourceSizeParameter_ge_one_hundred
      (encodeThreeCNF formula).length
      (srcFormula formula))

/-- GapCVP reduction support. -/
def paperShiftedTupleBetaFieldIndex
    (formula : ThreeCNF) (bit : Bool) :
    Fin (2 ^ sourceIrreducibleFormulaDegree formula) := by
  refine ⟨if bit then 1 else 0, ?_⟩
  cases bit
  · simp only [Bool.false_eq_true, ↓reduceIte, Order.lt_two_iff, zero_le, pow_pos]
  · exact Nat.one_lt_two_pow
      (Nat.ne_of_gt
        (paperVariableArityShiftedTupleSourceFieldDegree_pos formula))

/-- GapCVP reduction support. -/
def paperShiftedTupleBetaFieldWord
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  physicalCellFieldWordAt
    (paperShiftedTupleBetaRankComputer ranks)

private noncomputable def paperVariableArityShiftedTupleBetaFieldWordComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (paperShiftedTupleBetaFieldWord ranks) :=
  physicalCellFieldWordAtComputable
    (paperShiftedTupleBetaRankComputer ranks)

/-- GapCVP reduction support. -/
noncomputable def paperShiftedTupleBetaFieldComputer
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    SourcePhysicalLagrangeWordComputer where
  output := paperShiftedTupleBetaFieldWord ranks
  computer := paperVariableArityShiftedTupleBetaFieldWordComputable ranks

theorem paperVariableArityShiftedTupleBetaFieldComputer_output
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    (paperShiftedTupleBetaFieldComputer ranks).output =
      paperShiftedTupleBetaFieldWord ranks := by
  dsimp only [paperShiftedTupleBetaFieldComputer]

theorem paperVariableArityShiftedTupleBetaFieldWord_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF) (bit : Bool)
    (hbit : paperShiftedTupleBetaBit ranks
      (affineCellQuery row column
        (encodeThreeCNF formula)) = [bit]) :
    paperShiftedTupleBetaFieldWord ranks
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      finiteWordBits
        (indexedWord (sourceIrreducibleFormulaDegree formula)
          (paperShiftedTupleBetaFieldIndex formula bit)) := by
  have hsource :
      (paperShiftedTupleBetaRankComputer ranks).output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
        List.replicate
          (paperShiftedTupleBetaFieldIndex formula bit).val
          true := by
    rw [paperVariableArityShiftedTupleBetaRankComputer_output,
      paperVariableArityShiftedTupleBetaRankUnary_valid
        ranks (affineCellQuery row column
          (encodeThreeCNF formula)) bit hbit]
    rfl
  exact physicalCellFieldWordAt_valid
    (paperShiftedTupleBetaRankComputer ranks)
    row column formula
    (paperShiftedTupleBetaFieldIndex formula bit)
    hsource

private theorem paperVariableArityShiftedTupleIndexedZeroWord
    (degree : ℕ) :
    indexedWord degree ⟨0, by positivity⟩ = zeroWord degree := by
  funext position
  simp only [indexedWord, Nat.zero_testBit, zeroWord]

private theorem paperVariableArityShiftedTupleZeroWord_sourceField
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula) :
    sourceWordValue encodingLength formula
      (zeroWord
        (sourceFieldExponent
          (sourceSizeParameter encodingLength formula))) = 0 := by
  unfold sourceWordValue
    GapCVP.BinaryFieldBasis.wordElement
  rw [wordPolynomial_zeroWord, map_zero, map_zero]

theorem paperVariableArityShiftedTupleBetaIndexedWord_sourceField
    (formula : ThreeCNF) (bit : Bool) :
    sourceWordValue (encodeThreeCNF formula).length
      (srcFormula formula)
      (indexedWord (sourceIrreducibleFormulaDegree formula)
        (paperShiftedTupleBetaFieldIndex formula bit)) =
      sourceSATFieldBit
        (K := GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
          (encodeThreeCNF formula).length
          (srcFormula formula)) bit := by
  cases bit
  · have hzero :
        indexedWord
            (sourceIrreducibleFormulaDegree formula)
            (paperShiftedTupleBetaFieldIndex formula false) =
          zeroWord
            (sourceIrreducibleFormulaDegree formula) := by
        exact paperVariableArityShiftedTupleIndexedZeroWord
          (sourceIrreducibleFormulaDegree formula)
    rw [hzero]
    change sourceWordValue (encodeThreeCNF formula).length
      (srcFormula formula)
      (zeroWord (sourceFieldExponent
        (sourceSizeParameter (encodeThreeCNF formula).length
          (srcFormula formula)))) = _
    rw [paperVariableArityShiftedTupleZeroWord_sourceField]
    simp only [sourceSATFieldBit, Bool.false_eq_true, ↓reduceIte]
  · have hdegree := paperVariableArityShiftedTupleSourceFieldDegree_pos formula
    have hone :
        indexedWord
            (sourceIrreducibleFormulaDegree formula)
            (paperShiftedTupleBetaFieldIndex formula true) =
          oneWord
            (sourceIrreducibleFormulaDegree formula) := by
        exact compactPhysicalLagrangeIndexedOneWord
          (sourceIrreducibleFormulaDegree formula) hdegree
    rw [hone]
    change sourceWordValue (encodeThreeCNF formula).length
      (srcFormula formula)
      (oneWord (sourceFieldExponent
        (sourceSizeParameter (encodeThreeCNF formula).length
          (srcFormula formula)))) = _
    rw [sourceWordValue_oneWord]
    simp only [sourceSATFieldBit, ↓reduceIte]

end ShiftedTupleBetaSourceFieldCorrectness

namespace PhysicalShiftedInterpolationBaseTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinaryCompactPhysicalFieldWordXorTM GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalGlobalRefinementCoefficientTM GapCVP.PhysicalOrdinaryShiftedCoefficientTM
open GapCVP.PhysicalRefinementRowProjection
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
open GapCVP.ShiftedTupleBetaTM GapCVP.ShiftedTupleBetaSourceCorrectness
open GapCVP.ShiftedTupleBetaSourceFieldCorrectness
open GapCVP.ShiftedTupleAnchorSourceFieldCorrectness

private noncomputable def paperVariableArityPhysicalShiftedColumnValueRankComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalColumnFieldValueRankUnary
  computer := paperVariableArityPhysicalColumnFieldValueRankUnaryComputable

/-- GapCVP reduction support. -/
def physicalShiftedColumnValueWord :
    List Bool → List Bool :=
  physicalCellFieldWordAt
    paperVariableArityPhysicalShiftedColumnValueRankComputer

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedColumnValueWordComputable :
    BitTM
      physicalShiftedColumnValueWord :=
  physicalCellFieldWordAtComputable
    paperVariableArityPhysicalShiftedColumnValueRankComputer

/-- GapCVP reduction support. -/
noncomputable def physicalShiftedColumnValueComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalShiftedColumnValueWord
  computer := paperVariableArityPhysicalShiftedColumnValueWordComputable

private def physicalShiftedColumnValueIndex
    (formula : ThreeCNF) (column : ℕ) :
    Fin (2 ^ sourceIrreducibleFormulaDegree formula) :=
  ⟨column % physFieldCard formula,
    Nat.mod_lt _
      (physicalCoefficientFieldCardinality_pos formula)⟩

/-- GapCVP reduction support. -/
def physicalShiftedColumnValueSourceWord
    (formula : ThreeCNF) (column : ℕ) :
    GapCVP.Core.EffectiveBinaryField.Word
      (sourceIrreducibleFormulaDegree formula) :=
  indexedWord (sourceIrreducibleFormulaDegree formula)
    (physicalShiftedColumnValueIndex formula column)

theorem paperVariableArityPhysicalShiftedColumnValueWord_valid
    (row column : ℕ) (formula : ThreeCNF) :
    physicalShiftedColumnValueWord
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      finiteWordBits
        (physicalShiftedColumnValueSourceWord
          formula column) := by
  unfold physicalShiftedColumnValueWord
    physicalShiftedColumnValueSourceWord
  apply physicalCellFieldWordAt_valid
    paperVariableArityPhysicalShiftedColumnValueRankComputer
    row column formula
    (physicalShiftedColumnValueIndex formula column)
  change physicalColumnFieldValueRankUnary
    (affineCellQuery row column
      (encodeThreeCNF formula)) =
      List.replicate
        (column % physFieldCard formula)
        true
  exact paperVariableArityPhysicalColumnFieldValueRankUnary_query
    row column formula

private noncomputable def paperVariableArityPhysicalShiftedColumnGridRankComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalColumnGridRankUnary
  computer := physicalColumnGridRankUnaryComputable

/-- GapCVP reduction support. -/
def physicalShiftedColumnGridWord :
    List Bool → List Bool :=
  physicalCellGridWordAt
    paperVariableArityPhysicalShiftedColumnGridRankComputer

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedColumnGridWordComputable :
    BitTM
      physicalShiftedColumnGridWord :=
  paperVariableArityPhysicalCellGridWordAtComputable
    paperVariableArityPhysicalShiftedColumnGridRankComputer

/-- GapCVP reduction support. -/
noncomputable def physicalShiftedColumnGridComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalShiftedColumnGridWord
  computer := paperVariableArityPhysicalShiftedColumnGridWordComputable

/-- GapCVP reduction support. -/
def physicalShiftedColumnGridIndex
    (formula : ThreeCNF) (column : ℕ) :
    Fin (2 ^ sourceIrreducibleFormulaDegree formula -
      (srcFormula formula).variableCount) :=
  ⟨(column / physFieldCard formula) %
      physGridCard formula,
    Nat.mod_lt _
      (physicalRefinementGridCard_pos formula)⟩

/-- GapCVP reduction support. -/
def physicalShiftedColumnGridSourceWord
    (formula : ThreeCNF) (column : ℕ) :
    GapCVP.Core.EffectiveBinaryField.Word
      (sourceIrreducibleFormulaDegree formula) :=
  indexedWord (sourceIrreducibleFormulaDegree formula)
    (evaluationWordIndex
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.variableCount_le_fieldWordCount
        (encodeThreeCNF formula).length
        (srcFormula formula))
      (physicalShiftedColumnGridIndex formula column))

theorem paperVariableArityPhysicalShiftedColumnGridWord_valid
    (row column : ℕ) (formula : ThreeCNF) :
    physicalShiftedColumnGridWord
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      finiteWordBits
        (physicalShiftedColumnGridSourceWord
          formula column) := by
  unfold physicalShiftedColumnGridWord
    physicalShiftedColumnGridSourceWord
  apply paperVariableArityPhysicalCellGridWordAt_valid
    paperVariableArityPhysicalShiftedColumnGridRankComputer
    row column formula
    (physicalShiftedColumnGridIndex formula column)
  simp only [paperVariableArityPhysicalShiftedColumnGridRankComputer,
    physicalShiftedColumnGridIndex]
  exact paperVariableArityPhysicalColumnGridRankUnary_query
    row column formula

/-- GapCVP reduction support. -/
noncomputable def physicalShiftedInterpolationNumeratorComputer
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    SourcePhysicalLagrangeWordComputer :=
  paperVariableArityPhysicalInterpolationDifferenceComputer
    physicalShiftedColumnValueComputer
    (paperShiftedTupleBetaFieldComputer ranks)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalShiftedInterpolationDenominatorComputer
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    SourcePhysicalLagrangeWordComputer :=
  paperVariableArityPhysicalInterpolationDifferenceComputer
    physicalShiftedColumnGridComputer
    (paperShiftedTupleRetainedAnchorFieldComputer ranks)

/-- GapCVP reduction support. -/
def physicalShiftedInterpolationBaseWord
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    List Bool → List Bool :=
  paperVariableArityPhysicalInterpolationProductWord
    (physicalShiftedInterpolationNumeratorComputer ranks)
    (paperVariableArityPhysicalCellInverseComputer
      (paperVariableArityPhysicalShiftedInterpolationDenominatorComputer
        ranks))

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedInterpolationBaseWordComputable
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    BitTM
      (physicalShiftedInterpolationBaseWord ranks) :=
  paperVariableArityPhysicalInterpolationProductWordComputable
    (physicalShiftedInterpolationNumeratorComputer ranks)
    (paperVariableArityPhysicalCellInverseComputer
      (paperVariableArityPhysicalShiftedInterpolationDenominatorComputer
        ranks))

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalShiftedInterpolationBaseComputer
    (ranks : PaperVariableArityShiftedTupleRankComputers) :
    SourcePhysicalLagrangeWordComputer where
  output := physicalShiftedInterpolationBaseWord ranks
  computer := paperVariableArityPhysicalShiftedInterpolationBaseWordComputable
    ranks

/-- GapCVP reduction support. -/
def physicalShiftedInterpolationBaseSourceWord
    (formula : ThreeCNF) (column rank : ℕ)
    (bounded : rank < (noTautClauses formula).length)
    (position : ℕ)
    (validPosition : position <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, bounded⟩)).length)
    (bit : Bool) :
    GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula) :=
  multiplyMod
    (irreducibleWord (physDegree formula))
    (compactPhysicalFieldWordXorValue
      (physicalShiftedColumnValueSourceWord
        formula column)
      (indexedWord
        (sourceIrreducibleFormulaDegree formula)
        (paperShiftedTupleBetaFieldIndex formula bit)))
    (sourceInverseWord
      (compactPhysicalFieldWordXorValue
        (physicalShiftedColumnGridSourceWord
          formula column)
        (paperShiftedTupleSelectedSourceVariableWord
          formula rank bounded position validPosition)))

end PhysicalShiftedInterpolationBaseTM

namespace PhysicalInterpolationColumnSourceFieldCorrectness

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinarySourceCoordinateOrder GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalColumnOrderProjection
open GapCVP.PhysicalLagrangeNodeProductAlgebra GapCVP.PhysicalShiftedInterpolationBaseTM
open GapCVP.SourceOrder

private theorem sourceIndexedWord_sourceFieldCardOrder_symm_val
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (index : Fin (2 ^ sourceFormulaWordDegree encodingLength formula)) :
    ((sourceFormulaFieldCardOrder encodingLength formula).symm
      (sourceWordValue encodingLength formula
        (indexedWord
          (sourceFormulaWordDegree encodingLength formula) index))).val =
      index.val := by
  change
    ((((finCongr
      (sourceFormulaFieldWordOrder_card encodingLength formula)).trans
      (sourceFormulaFieldWordOrder encodingLength formula)).symm
      ((sourceFormulaFieldWordOrder encodingLength formula) index))).val =
      index.val
  simp only [Equiv.symm_trans, finCongr_symm, Equiv.trans_apply, Equiv.symm_apply_apply,
      finCongr_apply,
      Fin.val_cast]

private theorem sourceGridWord_sourceGridCardOrder_symm_val
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (index : Fin
      (2 ^ sourceFormulaWordDegree encodingLength formula -
        formula.variableCount)) :
    ((sourceFormulaGridOrder encodingLength formula).symm
      (sourceFormulaGridWordOrder encodingLength formula index)).val =
      index.val := by
  change
    ((((finCongr
      (sourceFormulaGrid_card_eq_fieldWordCount encodingLength formula)).trans
      (sourceFormulaGridWordOrder encodingLength formula)).symm
      ((sourceFormulaGridWordOrder encodingLength formula) index))).val =
      index.val
  simp only [Equiv.symm_trans, finCongr_symm, Equiv.trans_apply, Equiv.symm_apply_apply,
      finCongr_apply,
      Fin.val_cast]

theorem paperVariableArityPhysicalInterpolationColumnValueSourceWord_sourceField
    (formula : ThreeCNF)
    (column : Fin
      (sourceFormulaDimension (encodeThreeCNF formula).length
        (srcFormula formula))) :
    sourceWordValue (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalShiftedColumnValueSourceWord
          formula column.val) =
      (sourceCoordinateWordOrder
        (encodeThreeCNF formula).length formula column).2.2 := by
  apply (sourceFormulaFieldCardOrder
    (encodeThreeCNF formula).length
    (srcFormula formula)).symm.injective
  apply Fin.ext
  calc
    ((sourceFormulaFieldCardOrder
        (encodeThreeCNF formula).length
        (srcFormula formula)).symm
        (sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedColumnValueSourceWord
            formula column.val))).val =
        (physicalShiftedColumnValueIndex
          formula column.val).val := by
            exact sourceIndexedWord_sourceFieldCardOrder_symm_val
              (encodeThreeCNF formula).length
              (srcFormula formula)
              (physicalShiftedColumnValueIndex
                formula column.val)
    _ = column.val %
        physFieldCard formula := by
          rfl
    _ = ((sourceFormulaFieldCardOrder
          (encodeThreeCNF formula).length
          (srcFormula formula)).symm
          ((sourceCoordinateWordOrder
            (encodeThreeCNF formula).length formula column).2.2)).val := by
          symm
          simpa only [physicalFormulaFieldCardinality_eq_card]
            using paperVariableAritySourceCoordinateFieldWordRank
              (encodeThreeCNF formula).length formula column

private theorem paperVariableArityPhysicalInterpolationColumnGridPoint_eq_sourceCoordinate
    (formula : ThreeCNF)
    (column : Fin
      (sourceFormulaDimension (encodeThreeCNF formula).length
        (srcFormula formula))) :
    sourceFormulaGridWordOrder
        (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalShiftedColumnGridIndex
          formula column.val) =
      (sourceCoordinateWordOrder
        (encodeThreeCNF formula).length formula column).2.1 := by
  apply (sourceFormulaGridOrder
    (encodeThreeCNF formula).length
    (srcFormula formula)).symm.injective
  apply Fin.ext
  calc
    ((sourceFormulaGridOrder
        (encodeThreeCNF formula).length
        (srcFormula formula)).symm
        (sourceFormulaGridWordOrder
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedColumnGridIndex
            formula column.val))).val =
        (physicalShiftedColumnGridIndex
          formula column.val).val := by
            exact sourceGridWord_sourceGridCardOrder_symm_val
              (encodeThreeCNF formula).length
              (srcFormula formula)
              (physicalShiftedColumnGridIndex
                formula column.val)
    _ = (column.val /
          physFieldCard formula) %
        physGridCard formula := by
          rfl
    _ = ((sourceFormulaGridOrder
          (encodeThreeCNF formula).length
          (srcFormula formula)).symm
          ((sourceCoordinateWordOrder
            (encodeThreeCNF formula).length formula column).2.1)).val := by
          symm
          simpa only
            [physicalFormulaFieldCardinality_eq_card,
              physicalFormulaGridCardinality_eq_card]
            using sourceCoordinateGridWordRank
              (encodeThreeCNF formula).length formula column

theorem paperVariableArityPhysicalInterpolationColumnGridSourceWord_sourceField
    (formula : ThreeCNF)
    (column : Fin
      (sourceFormulaDimension (encodeThreeCNF formula).length
        (srcFormula formula))) :
    sourceWordValue (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalShiftedColumnGridSourceWord
          formula column.val) =
      ((sourceCoordinateWordOrder
        (encodeThreeCNF formula).length formula column).2.1).val := by
  calc
    sourceWordValue (encodeThreeCNF formula).length
      (srcFormula formula)
      (physicalShiftedColumnGridSourceWord
        formula column.val) =
        sourceFormulaEvaluationWord
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedColumnGridIndex
            formula column.val) := by
              exact physicalLagrangeNodeEvaluationWord_sourceField
                formula
                (physicalShiftedColumnGridIndex
                  formula column.val)
    _ = ((sourceCoordinateWordOrder
        (encodeThreeCNF formula).length formula column).2.1).val := by
          exact congrArg Subtype.val
            (paperVariableArityPhysicalInterpolationColumnGridPoint_eq_sourceCoordinate
              formula column)

end PhysicalInterpolationColumnSourceFieldCorrectness

namespace PhysicalOrdinaryShiftedCheckBitInstantiation

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryCompactPhysicalFieldBasisCoordinates GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalFamilyMarkerTM GapCVP.PhysicalFieldWordSemantics
open GapCVP.PhysicalOrdinaryInterpolationCheckFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationTypeMatchCorrectness
open GapCVP.PhysicalShiftedInterpolationBaseTM GapCVP.SourceOrder
open GapCVP.SourceFieldMomentOperationsTM

theorem paperVariableArityPhysicalSourceWordBasisCoordinate_decide
    (formula : ThreeCNF)
    (word : GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula))
    (index : Fin (physDegree formula)) :
    decide
      ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
        (encodeThreeCNF formula).length
        (srcFormula formula)).equivFun
          (sourceWordValue (encodeThreeCNF formula).length
            (srcFormula formula) word)
          index = (1 : ZMod 2)) = word index := by
  rw [sourceFormulaFieldBasis_sourceWordValue_coordinate]
  cases word index <;> simp [bitValue]

theorem paperVariableArityPhysicalSourceBasisCoordinate_sub_decide
    (formula : ThreeCNF)
    (first second : PaperVariableArityPhysicalWordField
      (encodeThreeCNF formula).length formula)
    (index : Fin (physDegree formula)) :
    decide
      ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
        (encodeThreeCNF formula).length
        (srcFormula formula)).equivFun
          (first - second) index = (1 : ZMod 2)) =
      Bool.xor
        (decide
          ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
            (encodeThreeCNF formula).length
            (srcFormula formula)).equivFun
              first index = (1 : ZMod 2)))
        (decide
          ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
            (encodeThreeCNF formula).length
            (srcFormula formula)).equivFun
              second index = (1 : ZMod 2))) := by
  apply GapCVP.Core.EffectiveBinaryField.bitValue_injective
  rw [GapCVP.Core.EffectiveBinaryField.bitValue_xor,
    paperVariableArityPhysicalBitValue_decide,
    paperVariableArityPhysicalBitValue_decide,
    paperVariableArityPhysicalBitValue_decide, map_sub]
  exact CharTwo.sub_eq_add _ _

private theorem paperVariableArityPhysicalBooleanAnd_false_of_first
    (first second : List Bool → List Bool)
    (input : List Bool)
    (rejected : first input = [false]) :
    sourceFourFamilyBooleanAndOutput first second input = [false] := by
  change sourceFourFamilyBooleanAndPairWord
    (first input ++ second input) = [false]
  rw [rejected]
  rfl

theorem paperVariableArityPhysicalOrdinaryCheckBit_of_not_in_family
    (formula : ThreeCNF) (row column : ℕ)
    (outside : ¬
      (physicalFormulaRefinementBoundary formula ≤ row ∧
        row < physicalFormulaOrdinaryBoundary formula)) :
    physicalOrdinaryCheckBit
        (affineCellQuery row column
          (encodeThreeCNF formula)) = [false] := by
  let query := affineCellQuery row column
    (encodeThreeCNF formula)
  have rejected :
      physicalOrdinaryRowMarker query = [false] := by
    change physicalOrdinaryRowMarker
      (affineCellQuery row column
        (encodeThreeCNF formula)) = [false]
    rw [paperVariableArityPhysicalOrdinaryRowMarker_query]
    simp only [outside, decide_false]
  unfold physicalOrdinaryCheckBit
    physicalSourceInterpolationFamilyCheckBit
  exact paperVariableArityPhysicalBooleanAnd_false_of_first
    physicalOrdinaryRowMarker _ query rejected

theorem paperVariableArityPhysicalOrdinaryColumnFieldComputer_valid
    (formula : ThreeCNF) (row : ℕ)
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula)) :
    physicalInterpolationColumnFieldComputer.output
        (affineCellQuery row column.val
          (encodeThreeCNF formula)) =
      finiteWordBits
        (physicalShiftedColumnValueSourceWord
          formula column.val) := by
  rw [paperVariableArityPhysicalInterpolationColumnFieldComputer_output]
  exact paperVariableArityPhysicalInterpolationColumnFieldWord_valid
    row column.val formula
    (physicalShiftedColumnValueIndex
      formula column.val) rfl

theorem paperVariableArityPhysicalOrdinaryFamilyStart_eq_refinement
    (formula : ThreeCNF) :
    physicalFamilyStart (2 : Fin 4) formula =
      physicalFormulaRefinementBoundary formula := by
  rfl

theorem paperVariableArityPhysicalOrdinaryExpectedTypeMatchBit_eq_sourceTable
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    physicalInterpolationExpectedTypeMatchBit
        (physicalInterpolationFamilyTypeRankComputer
          (2 : Fin 4))
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        ((physicalOrdinarySourceRowTableMoment
          formula row inOrdinary).1 =
          (GapCVP.SourceOrder.sourceCoordinateWordOrder
            (encodeThreeCNF formula).length formula column).1)] := by
  have actual := paperVariableArityPhysicalOrdinarySourceRowTable_eq_column_iff
    formula row column inOrdinary
  have computed := paperVariableArityPhysicalOrdinaryExpectedTypeMatchBit_valid
    formula row.val column.val
  rw [paperVariableArityPhysicalOrdinaryFamilyStart_eq_refinement] at computed
  by_cases selected :
      (physicalOrdinarySourceRowTableMoment
        formula row inOrdinary).1 =
        (sourceCoordinateWordOrder
          (encodeThreeCNF formula).length formula column).1
  · have rank := actual.mp selected
    simpa only [rank, selected, decide_true] using computed
  · have rank : ¬
        ((((row.val -
          physicalFormulaRefinementBoundary formula) /
          physDegree formula) /
          physGridCard formula) /
          physicalFormulaMomentCount formula =
            (column.val /
              physFieldCard formula) /
              physGridCard formula) := by
      intro equal
      exact selected (actual.mpr equal)
    simpa only [rank, selected, decide_false] using computed

end PhysicalOrdinaryShiftedCheckBitInstantiation


end GapCVP

end
