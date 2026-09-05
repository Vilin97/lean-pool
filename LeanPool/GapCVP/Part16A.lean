/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part15
import Mathlib.Data.List.Intervals

/-! # GapCVP proof, part 16 -/

noncomputable section

open StateTransition (EvalsToInTime)
open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.PhysicalInterpolationColumnSourceFieldCorrectness

namespace PhysicalOrdinaryInterpolationParityFieldCorrectness

open scoped BigOperators

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem
open GapCVP.BinaryPhysicalLagrangeParityEntry GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationNodeCountBounds GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryInterpolationCheckFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationRowGridBasisCorrectness
open GapCVP.SourceFieldMomentOperationsTM GapCVP.SourceOrder GapCVP.BinaryReedSolomonParity
open GapCVP.BinarySourceCoordinateOrder

private theorem paperVariableArityPhysicalOrderedLagrangeParity_eq_selectedCorrection
    {K : Type*} [Field K]
    {gridCardinality degreeBound : ℕ}
    (points : Fin gridCardinality → K)
    (hdegree : degreeBound < gridCardinality)
    (row position : Fin gridCardinality) :
    constructiveParityMatrix points hdegree row position =
      (if row = position then (1 : K) else 0) -
        if hposition : position.val < degreeBound + 1 then
          ∏ other ∈ (Finset.univ.erase
            (⟨position.val, hposition⟩ : Fin (degreeBound + 1))),
              (points
                (Fin.castLE (Nat.succ_le_of_lt hdegree)
                  (⟨position.val, hposition⟩ : Fin (degreeBound + 1))) -
               points (Fin.castLE (Nat.succ_le_of_lt hdegree) other))⁻¹ *
              (points row -
               points (Fin.castLE (Nat.succ_le_of_lt hdegree) other))
        else 0 := by
  classical
  rw [constructiveParityMatrix_apply_eq_orderedNodeProducts]
  congr 1
  by_cases hposition : position.val < degreeBound + 1
  · simp only [dite_eq_left hposition]
    let selected : Fin (degreeBound + 1) :=
      ⟨position.val, hposition⟩
    have hcast (node : Fin (degreeBound + 1)) :
        Fin.castLE (Nat.succ_le_of_lt hdegree) node = position ↔
          node = selected := by
      constructor
      · intro equality
        apply Fin.ext
        exact congrArg (fun value : Fin gridCardinality => value.val) equality
      · intro equality
        subst node
        apply Fin.ext
        rfl
    simp_rw [ite_mul, one_mul, zero_mul, hcast]
    simp only [Nat.succ_eq_add_one, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fin.castLE_mk,
        Fin.eta,
        selected]
  · simp only [dite_eq_right hposition]
    have hcast (node : Fin (degreeBound + 1)) :
        Fin.castLE (Nat.succ_le_of_lt hdegree) node ≠ position := by
      intro equality
      apply hposition
      have rank := congrArg Fin.val equality
      simpa only [Fin.val_castLE] using (rank ▸ node.isLt)
    simp only [Nat.succ_eq_add_one, hcast, ↓reduceIte, zero_mul, Finset.sum_const_zero]

private theorem paperVariableArityPhysicalOrdinaryMaskedNodeSum_eq_selected
    {K : Type*} [AddCommMonoid K]
    (count grid : ℕ) (value : ℕ → K) :
    (((List.range count).map (fun node =>
      if node = grid then value node else 0)).sum) =
      if grid < count then value grid else 0 := by
  change (∑ node ∈ Finset.range count,
    if node = grid then value node else 0) = _
  simp only [Finset.sum_ite_eq', Finset.mem_range]

private theorem paperVariableArityPhysicalExplicitGridOrder_value_eq_evaluation
    (formula : ThreeCNF)
    (index : Fin (Fintype.card
      (ExplicitGridPoint (encodeThreeCNF formula).length
        (srcFormula formula)))) :
    (sourceFormulaExplicitGridOrder
      (encodeThreeCNF formula).length
      (srcFormula formula) index).val =
      sourceFormulaEvaluationWord
        (encodeThreeCNF formula).length
        (srcFormula formula)
        (Fin.cast
          (physicalInterpolationExplicitGridCardinality_eq
            formula) index) := by
  rfl

private theorem paperVariableArityPhysicalOrdinarySourceRowMoment_eq_family
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    (physicalOrdinarySourceRowTableMoment
      formula row inOrdinary).2.val =
      physicalFamilyRowMoment (2 : Fin 4)
        row.val formula := by
  simpa only [physicalFamilyRowMoment, physicalFamilyStart, Fin.isValue, Fin.coe_ofNat_eq_mod,
      Nat.reduceMod,
      OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one] using
      paperVariableArityPhysicalOrdinarySourceRowMoment_val formula row inOrdinary

private theorem paperVariableArityPhysicalOrdinarySourceRowNodeCount
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    physicalOrdinaryInterpolationNodeCount
        row.val formula =
      (srcFormula formula).variableCount *
        (physicalOrdinarySourceRowTableMoment
          formula row inOrdinary).2.val + 1 := by
  unfold physicalOrdinaryInterpolationNodeCount
  rw [paperVariableArityPhysicalOrdinarySourceRowMoment_eq_family
    formula row inOrdinary]

end PhysicalOrdinaryInterpolationParityFieldCorrectness

open GapCVP.PhysicalOrdinaryInterpolationParityFieldCorrectness

namespace PhysicalOrdinaryInterpolationSelectedSourceWeightCorrectness

open scoped BigOperators

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryFieldInverseAlgebra
open GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationColumnSourceFieldCorrectness
open GapCVP.PhysicalInterpolationNodeCountBounds GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalInterpolationNodeWeightTM
open GapCVP.PhysicalInterpolationNodeWeightSourceFieldCorrectness
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryInterpolationCheckFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationParityFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationRowGridBasisCorrectness
open GapCVP.PhysicalShiftedInterpolationBaseTM GapCVP.SourceFieldMomentOperationsTM
open GapCVP.SourceOrder GapCVP.BinarySourceCoordinateOrder

private def physicalOrdinaryInterpolationExplicitNode
    (formula : ThreeCNF) (row : ℕ)
    (node : Fin
      (physicalOrdinaryInterpolationNodeCount row formula)) :
    Fin (Fintype.card
      (ExplicitGridPoint (encodeThreeCNF formula).length
        (srcFormula formula))) :=
  Fin.castLE (by
    rw [physicalInterpolationExplicitGridCardinality_eq]
    exact physicalOrdinaryInterpolationNodeCount_le_grid
      formula row) node

private theorem paperVariableArityPhysicalOrdinaryInterpolationExplicitNode_value
    (formula : ThreeCNF) (row : ℕ)
    (node : Fin
      (physicalOrdinaryInterpolationNodeCount row formula)) :
    (sourceFormulaExplicitGridOrder
      (encodeThreeCNF formula).length
      (srcFormula formula)
      (physicalOrdinaryInterpolationExplicitNode
        formula row node)).val =
      sourceFormulaEvaluationWord
        (encodeThreeCNF formula).length
        (srcFormula formula)
        (Fin.castLE
          (physicalOrdinaryInterpolationNodeCount_le_grid
            formula row) node) := by
  rw [paperVariableArityPhysicalExplicitGridOrder_value_eq_evaluation]
  congr 1

private theorem paperVariableArityPhysicalOrdinarySourceRowGridEvaluation
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    (sourceFormulaExplicitGridOrder
      (encodeThreeCNF formula).length
      (srcFormula formula)
      (physicalOrdinarySourceRowGrid
        formula row inOrdinary)).val =
      sourceFormulaEvaluationWord
        (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalInterpolationFamilyRowGridPosition
          (2 : Fin 4) row.val formula) := by
  rw [paperVariableArityPhysicalExplicitGridOrder_value_eq_evaluation]
  congr 1
  apply Fin.ext
  change
    (physicalOrdinarySourceRowGrid
      formula row inOrdinary).val =
      (((row.val - physicalFamilyStart
        (2 : Fin 4) formula) /
        physDegree formula) %
          physGridCard formula)
  simpa only [physicalFamilyStart, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
      OfNat.ofNat_ne_zero,
      ↓reduceIte, OfNat.ofNat_ne_one] using paperVariableArityPhysicalOrdinarySourceRowGrid_val
          formula row inOrdinary

private theorem paperVariableArityPhysicalOrdinaryInterpolationNodeWeight_eq_explicitProducts
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula)
    (node : Fin (physicalOrdinaryInterpolationNodeCount
      row.val formula)) :
    sourceWordValue (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalInterpolationNodeWeightSourceWord
          (2 : Fin 4) row.val formula
          (physicalOrdinaryInterpolationNodeCount
            row.val formula)
          (physicalOrdinaryInterpolationNodeCount_le_grid
            formula row.val)
          node
          (physicalShiftedColumnValueSourceWord
            formula column.val)) =
      (∏ other ∈ (Finset.univ.erase node),
        ((sourceFormulaExplicitGridOrder
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalOrdinarySourceRowGrid
            formula row inOrdinary)).val -
        (sourceFormulaExplicitGridOrder
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalOrdinaryInterpolationExplicitNode
            formula row.val other)).val)) *
      (∏ other ∈ (Finset.univ.erase node),
        ((sourceFormulaExplicitGridOrder
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalOrdinaryInterpolationExplicitNode
            formula row.val node)).val -
        (sourceFormulaExplicitGridOrder
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalOrdinaryInterpolationExplicitNode
            formula row.val other)).val))⁻¹ *
      (sourceCoordinateWordOrder
        (encodeThreeCNF formula).length formula column).2.2 ^
        (physicalOrdinarySourceRowTableMoment
          formula row inOrdinary).2.val := by
  rw [paperVariableArityPhysicalInterpolationNodeWeightSourceWord_sourceField]
  simp_rw [paperVariableArityPhysicalOrdinarySourceRowGridEvaluation,
    paperVariableArityPhysicalOrdinaryInterpolationExplicitNode_value,
    paperVariableArityPhysicalInterpolationColumnValueSourceWord_sourceField,
    paperVariableArityPhysicalOrdinarySourceRowMoment_eq_family]

end PhysicalOrdinaryInterpolationSelectedSourceWeightCorrectness

namespace PhysicalOrdinaryInterpolationSourceParityCorrectness

open scoped BigOperators

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryFieldInverseAlgebra
open GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationNodeCountBounds GapCVP.PhysicalInterpolationNodeWeightTM
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryInterpolationCheckFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationParityFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationSelectedSourceWeightCorrectness
open GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.PhysicalShiftedInterpolationBaseTM GapCVP.SourceOrder GapCVP.BinaryReedSolomonParity

private theorem paperVariableArityPhysicalOrdinaryErasedNodeProductAlgebra
    {K : Type*} [Field K]
    {ι : Type*}
    (nodes : Finset ι)
    (numerator denominator : ι → K)
    (value : K) :
    (nodes.prod (fun other => (denominator other)⁻¹ * numerator other)) *
        value =
      nodes.prod numerator * (nodes.prod denominator)⁻¹ * value := by
  classical
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  ac_rfl

private theorem paperVariableArityPhysicalOrdinarySelectedNodeWeightProduct
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula)
    (node : Fin (physicalOrdinaryInterpolationNodeCount
      row.val formula)) :
    (∏ other ∈ (Finset.univ.erase node),
      ((sourceFormulaExplicitGridOrder
        (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalOrdinaryInterpolationExplicitNode
          formula row.val node)).val -
       (sourceFormulaExplicitGridOrder
        (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalOrdinaryInterpolationExplicitNode
          formula row.val other)).val)⁻¹ *
      ((sourceFormulaExplicitGridOrder
        (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalOrdinarySourceRowGrid
          formula row inOrdinary)).val -
       (sourceFormulaExplicitGridOrder
        (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalOrdinaryInterpolationExplicitNode
          formula row.val other)).val)) *
      (sourceCoordinateWordOrder
        (encodeThreeCNF formula).length formula column).2.2 ^
        (physicalOrdinarySourceRowTableMoment
          formula row inOrdinary).2.val =
    sourceWordValue (encodeThreeCNF formula).length
      (srcFormula formula)
      (physicalInterpolationNodeWeightSourceWord
        (2 : Fin 4) row.val formula
        (physicalOrdinaryInterpolationNodeCount
          row.val formula)
        (physicalOrdinaryInterpolationNodeCount_le_grid
          formula row.val) node
        (physicalShiftedColumnValueSourceWord
          formula column.val)) := by
  rw [paperVariableArityPhysicalOrdinaryInterpolationNodeWeight_eq_explicitProducts
    formula row column inOrdinary node]
  exact paperVariableArityPhysicalOrdinaryErasedNodeProductAlgebra
    (Finset.univ.erase node)
    (fun other =>
      (sourceFormulaExplicitGridOrder
        (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalOrdinarySourceRowGrid
          formula row inOrdinary)).val -
      (sourceFormulaExplicitGridOrder
        (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalOrdinaryInterpolationExplicitNode
          formula row.val other)).val)
    (fun other =>
      (sourceFormulaExplicitGridOrder
        (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalOrdinaryInterpolationExplicitNode
          formula row.val node)).val -
      (sourceFormulaExplicitGridOrder
        (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalOrdinaryInterpolationExplicitNode
          formula row.val other)).val)
    ((sourceCoordinateWordOrder
      (encodeThreeCNF formula).length formula column).2.2 ^
      (physicalOrdinarySourceRowTableMoment
        formula row inOrdinary).2.val)

private theorem paperVariableArityPhysicalOrdinaryParityCorrection_mul_masked_sum
    {K ι : Type*} [Field K] [DecidableEq ι]
    (matrix : K) (row position : ι) (value : K)
    (count index : ℕ) (nodeValue : ℕ → K)
    (correction : index < count → K)
    (hparity : matrix =
      (if row = position then 1 else 0) -
        dite (index < count) correction (fun _ => 0))
    (hselected : ∀ selected : index < count,
      correction selected * value = nodeValue index) :
    matrix * value =
      (if row = position then value else 0) -
        (((List.range count).map (fun node =>
          if node = index then nodeValue node else 0)).sum) := by
  rw [hparity, sub_mul,
    paperVariableArityPhysicalOrdinaryMaskedNodeSum_eq_selected]
  simp only [ite_mul, one_mul, zero_mul]
  congr 1
  by_cases selected : index < count
  · simp only [dite_eq_left selected, ite_eq_left selected]
    exact hselected selected
  · simp only [dite_eq_right selected, ite_eq_right selected, zero_mul]

private theorem paperVariableArityPhysicalOrdinaryOrderedLagrangeParity_count
    {K : Type*} [Field K] {gridCardinality degreeBound count : ℕ}
    (points : Fin gridCardinality → K)
    (hdegree : degreeBound < gridCardinality)
    (hcount : count = degreeBound + 1)
    (hcountGrid : count ≤ gridCardinality)
    (row position : Fin gridCardinality) :
    constructiveParityMatrix points hdegree row position =
      (if row = position then (1 : K) else 0) -
        if hposition : position.val < count then
          ∏ other ∈ (Finset.univ.erase (⟨position.val, hposition⟩ : Fin count)),
            (points (Fin.castLE hcountGrid
              (⟨position.val, hposition⟩ : Fin count)) -
             points (Fin.castLE hcountGrid other))⁻¹ *
            (points row - points (Fin.castLE hcountGrid other))
        else 0 := by
  subst count
  simpa only [Order.lt_add_one_iff, Fin.castLE_mk, Fin.eta, Nat.succ_eq_add_one] using
      paperVariableArityPhysicalOrderedLagrangeParity_eq_selectedCorrection points hdegree row
          position

private theorem paperVariableArityPhysicalOrdinaryInterpolationSourceParity_eq
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
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
          formula row inOrdinary).2.val =
      (if physicalOrdinarySourceRowGrid
          formula row inOrdinary =
        ((sourceFormulaExplicitGridOrder
          (encodeThreeCNF formula).length
          (srcFormula formula)).symm
            (sourceCoordinateWordOrder
              (encodeThreeCNF formula).length formula column).2.1)
       then
        (sourceCoordinateWordOrder
          (encodeThreeCNF formula).length formula column).2.2 ^
          (physicalOrdinarySourceRowTableMoment
            formula row inOrdinary).2.val
       else 0) -
      (((List.range
        (physicalOrdinaryInterpolationNodeCount
          row.val formula)).map (fun node =>
          if node =
            (((sourceFormulaExplicitGridOrder
              (encodeThreeCNF formula).length
              (srcFormula formula)).symm
                (sourceCoordinateWordOrder
                  (encodeThreeCNF formula).length formula column).2.1)).val
          then
            sourceWordValue (encodeThreeCNF formula).length
              (srcFormula formula)
              (physicalInterpolationNodeSourceWord
                (2 : Fin 4) row.val formula
                (physicalOrdinaryInterpolationNodeCount
                  row.val formula)
                (physicalOrdinaryInterpolationNodeCount_le_grid
                  formula row.val)
                (physicalShiftedColumnValueSourceWord
                  formula column.val) node)
          else 0)).sum) := by
  classical
  let sourceMoment :=
    physicalOrdinarySourceRowTableMoment
      formula row inOrdinary
  let sourceRow := physicalOrdinarySourceRowGrid
    formula row inOrdinary
  let sourceColumn := sourceCoordinateWordOrder
    (encodeThreeCNF formula).length formula column
  let sourcePosition :=
    (sourceFormulaExplicitGridOrder
      (encodeThreeCNF formula).length
      (srcFormula formula)).symm sourceColumn.2.1
  let count := physicalOrdinaryInterpolationNodeCount
    row.val formula
  have count_eq :
      count = (srcFormula formula).variableCount *
        sourceMoment.2.val + 1 :=
    paperVariableArityPhysicalOrdinarySourceRowNodeCount
      formula row inOrdinary
  have count_grid : count ≤ Fintype.card
      (ExplicitGridPoint (encodeThreeCNF formula).length
        (srcFormula formula)) := by
    rw [count_eq]
    exact Nat.succ_le_of_lt
      (explicitOrdinaryDegree_lt_grid
        (encodeThreeCNF formula).length
        (srcFormula formula) sourceMoment.2)
  have parity :=
    paperVariableArityPhysicalOrdinaryOrderedLagrangeParity_count
      (fun index =>
        (sourceFormulaExplicitGridOrder
          (encodeThreeCNF formula).length
          (srcFormula formula) index).val)
      (explicitOrdinaryDegree_lt_grid
        (encodeThreeCNF formula).length
        (srcFormula formula) sourceMoment.2)
      count_eq count_grid sourceRow sourcePosition
  change
    constructiveParityMatrix
        (fun index =>
          (sourceFormulaExplicitGridOrder
            (encodeThreeCNF formula).length
            (srcFormula formula) index).val)
        (explicitOrdinaryDegree_lt_grid
          (encodeThreeCNF formula).length
          (srcFormula formula) sourceMoment.2)
        sourceRow sourcePosition * sourceColumn.2.2 ^ sourceMoment.2.val =
      (if sourceRow = sourcePosition
        then sourceColumn.2.2 ^ sourceMoment.2.val else 0) -
      (((List.range count).map (fun node =>
          if node = sourcePosition.val then
            sourceWordValue (encodeThreeCNF formula).length
              (srcFormula formula)
              (physicalInterpolationNodeSourceWord
                (2 : Fin 4) row.val formula count
                (physicalOrdinaryInterpolationNodeCount_le_grid
                  formula row.val)
                (physicalShiftedColumnValueSourceWord
                  formula column.val) node)
          else 0)).sum)
  apply paperVariableArityPhysicalOrdinaryParityCorrection_mul_masked_sum
    _ sourceRow sourcePosition (sourceColumn.2.2 ^ sourceMoment.2.val)
    count sourcePosition.val
    (fun node =>
      sourceWordValue (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalInterpolationNodeSourceWord
          (2 : Fin 4) row.val formula count
          (physicalOrdinaryInterpolationNodeCount_le_grid
            formula row.val)
          (physicalShiftedColumnValueSourceWord
            formula column.val) node))
    _ parity
  intro selected
  simp only [physicalInterpolationNodeSourceWord,
    dite_eq_left selected]
  exact paperVariableArityPhysicalOrdinarySelectedNodeWeightProduct
    formula row column inOrdinary ⟨sourcePosition.val, selected⟩

end PhysicalOrdinaryInterpolationSourceParityCorrectness

namespace PhysicalShiftedSourceColumnGridProjection

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.FormulaBridge
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalColumnOrderProjection GapCVP.SourceOrder

private theorem physicalSourceColumnExplicitGridPosition_val
    (formula : ThreeCNF)
    (column : Fin
      (sourceFormulaDimension (encodeThreeCNF formula).length
        (srcFormula formula))) :
    ((sourceFormulaExplicitGridOrder
      (encodeThreeCNF formula).length
      (srcFormula formula)).symm
      ((sourceCoordinateWordOrder
        (encodeThreeCNF formula).length formula column).2.1)).val =
      (column.val /
        physFieldCard formula) %
        physGridCard formula := by
  have genuine := sourceCoordinateGridWordRank
    (encodeThreeCNF formula).length formula column
  simpa only [sourceFormulaExplicitGridOrder, Equiv.symm_trans, finCongr_symm, Equiv.trans_apply,
      finCongr_apply, Fin.val_cast, physicalFormulaFieldCardinality_eq_card,
          physicalFormulaGridCardinality_eq_card] using
      genuine

end PhysicalShiftedSourceColumnGridProjection

open GapCVP.PhysicalShiftedSourceColumnGridProjection

namespace PhysicalOrdinaryInterpolationBinaryCheckBitCorrectness

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryFieldInverseAlgebra
open GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics GapCVP.PhysicalColumnOrder
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalInterpolationNodeCountBounds
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryInterpolationCheckFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationParityFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationRowGridBasisCorrectness
open GapCVP.PhysicalOrdinaryInterpolationSourceParityCorrectness
open GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.PhysicalShiftedInterpolationBaseTM GapCVP.PhysicalShiftedSourceColumnGridProjection
open GapCVP.SourceFieldMomentOperationsTM GapCVP.SourceOrder

private def physicalOrdinaryActualSourceCorrectionField
    (formula : ThreeCNF) (row : ℕ)
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula)) :
    PaperVariableArityPhysicalWordField
      (encodeThreeCNF formula).length formula :=
  (((List.range
    (physicalOrdinaryInterpolationNodeCount
      row formula)).map (fun node =>
      if node =
        (column.val /
          physFieldCard formula) %
          physGridCard formula
      then
        sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalInterpolationNodeSourceWord
            (2 : Fin 4) row formula
            (physicalOrdinaryInterpolationNodeCount
              row formula)
            (physicalOrdinaryInterpolationNodeCount_le_grid
              formula row)
            (physicalShiftedColumnValueSourceWord
              formula column.val) node)
      else 0)).sum)

private theorem paperVariableArityPhysicalOrdinaryActualSourceGridMatch_iff
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    physicalOrdinarySourceRowGrid
        formula row inOrdinary =
      (sourceFormulaExplicitGridOrder
        (encodeThreeCNF formula).length
        (srcFormula formula)).symm
          (sourceCoordinateWordOrder
            (encodeThreeCNF formula).length formula column).2.1 ↔
      (((row.val -
        physicalFormulaRefinementBoundary formula) /
        physDegree formula) %
        physGridCard formula =
        (column.val /
          physFieldCard formula) %
          physGridCard formula) := by
  constructor
  · intro matching
    have ranks := congrArg Fin.val matching
    rw [paperVariableArityPhysicalOrdinarySourceRowGrid_val,
      physicalSourceColumnExplicitGridPosition_val]
      at ranks
    exact ranks
  · intro matching
    apply Fin.ext
    rw [paperVariableArityPhysicalOrdinarySourceRowGrid_val,
      physicalSourceColumnExplicitGridPosition_val]
    exact matching

private theorem paperVariableArityPhysicalOrdinaryActualDirectMomentBasis_decide
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    decide
      ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
        (encodeThreeCNF formula).length
        (srcFormula formula)).equivFun
          (if physicalOrdinarySourceRowGrid
                formula row inOrdinary =
              (sourceFormulaExplicitGridOrder
                (encodeThreeCNF formula).length
                (srcFormula formula)).symm
                  (sourceCoordinateWordOrder
                    (encodeThreeCNF formula).length formula column).2.1
           then
              (sourceCoordinateWordOrder
                (encodeThreeCNF formula).length formula column).2.2 ^
                (physicalOrdinarySourceRowTableMoment
                  formula row inOrdinary).2.val
           else 0)
          (physicalInterpolationRowBasisIndex
          row.val formula) = (1 : ZMod 2)) =
      (decide
        ((((row.val -
          physicalFormulaRefinementBoundary formula) /
          physDegree formula) %
          physGridCard formula) =
          ((column.val /
            physFieldCard formula) %
            physGridCard formula)) &&
      (sourceWordPow
        (physicalShiftedColumnValueSourceWord
          formula column.val)
        (physicalFamilyRowMoment
          (2 : Fin 4) row.val formula))
        (physicalInterpolationRowBasisIndex
          row.val formula)) := by
  classical
  let sourceIndex := physicalInterpolationRowBasisIndex
    row.val formula
  let sourceWord := physicalShiftedColumnValueSourceWord
    formula column.val
  let sourceMoment := physicalFamilyRowMoment
    (2 : Fin 4) row.val formula
  have wordField :
      sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (sourceWordPow sourceWord sourceMoment) =
        (sourceCoordinateWordOrder
          (encodeThreeCNF formula).length formula column).2.2 ^
          (physicalOrdinarySourceRowTableMoment
            formula row inOrdinary).2.val := by
    rw [sourceWordValue_sourceWordPow,
      paperVariableArityPhysicalInterpolationColumnValueSourceWord_sourceField,
      paperVariableArityPhysicalOrdinarySourceRowMoment_eq_family]
  by_cases matching :
      physicalOrdinarySourceRowGrid
        formula row inOrdinary =
      (sourceFormulaExplicitGridOrder
        (encodeThreeCNF formula).length
        (srcFormula formula)).symm
          (sourceCoordinateWordOrder
            (encodeThreeCNF formula).length formula column).2.1
  · have physical :=
      (paperVariableArityPhysicalOrdinaryActualSourceGridMatch_iff
        formula row column inOrdinary).mp matching
    have coordinate := paperVariableArityPhysicalSourceWordBasisCoordinate_decide
      formula (sourceWordPow sourceWord sourceMoment) sourceIndex
    rw [wordField] at coordinate
    rw [ite_eq_left matching]
    simp only [physical, decide_true, Bool.true_and]
    exact coordinate
  · have physical : ¬
        (((row.val -
          physicalFormulaRefinementBoundary formula) /
          physDegree formula) %
          physGridCard formula =
          (column.val /
            physFieldCard formula) %
            physGridCard formula) := by
      intro equal
      exact matching
        ((paperVariableArityPhysicalOrdinaryActualSourceGridMatch_iff
          formula row column inOrdinary).mpr equal)
    rw [ite_eq_right matching]
    simp only [map_zero, Pi.zero_apply, zero_ne_one, decide_false, physical, Fin.isValue,
        Bool.false_and]

private theorem paperVariableArityPhysicalOrdinaryActualBinaryCheckBit_decide
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    decide
      ((physicalWordBinarySystem
        (encodeThreeCNF formula).length formula).check row column =
          (1 : ZMod 2)) =
      (decide
        ((physicalOrdinarySourceRowTableMoment
          formula row inOrdinary).1 =
          (sourceCoordinateWordOrder
            (encodeThreeCNF formula).length formula column).1) &&
      Bool.xor
        (decide
          ((((row.val -
            physicalFormulaRefinementBoundary formula) /
            physDegree formula) %
            physGridCard formula) =
            ((column.val /
              physFieldCard formula) %
              physGridCard formula)) &&
          (sourceWordPow
            (physicalShiftedColumnValueSourceWord
              formula column.val)
            (physicalFamilyRowMoment
              (2 : Fin 4) row.val formula))
            (physicalInterpolationRowBasisIndex
              row.val formula))
        (decide
          ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
            (encodeThreeCNF formula).length
            (srcFormula formula)).equivFun
              (physicalOrdinaryActualSourceCorrectionField
                formula row.val column)
              (physicalInterpolationRowBasisIndex
                row.val formula) = (1 : ZMod 2)))) := by
  classical
  have basis :
      (physicalWordDecodedRow
        (encodeThreeCNF formula).length formula row).2.2 =
        physicalInterpolationRowBasisIndex
          row.val formula := by
    apply Fin.ext
    exact paperVariableArityPhysicalOrdinarySourceRowBasis_val
      formula row
  rw [physicalWordBinaryCheckCoefficient,
    paperVariableArityPhysicalOrdinarySourceRowFieldCoefficient_eq_selected
      formula row column inOrdinary, basis]
  by_cases matching :
      (physicalOrdinarySourceRowTableMoment
        formula row inOrdinary).1 =
        (sourceCoordinateWordOrder
          (encodeThreeCNF formula).length formula column).1
  · simp only [matching, ite_eq_left, decide_true, Bool.true_and]
    have parity := paperVariableArityPhysicalOrdinaryInterpolationSourceParity_eq
      formula row column inOrdinary
    rw [physicalSourceColumnExplicitGridPosition_val]
      at parity
    rw [parity]
    change
      decide
        ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
          (encodeThreeCNF formula).length
          (srcFormula formula)).equivFun
          ((if physicalOrdinarySourceRowGrid
              formula row inOrdinary =
            (sourceFormulaExplicitGridOrder
              (encodeThreeCNF formula).length
              (srcFormula formula)).symm
                (sourceCoordinateWordOrder
                  (encodeThreeCNF formula).length formula column).2.1
            then
              (sourceCoordinateWordOrder
                (encodeThreeCNF formula).length formula column).2.2 ^
                (physicalOrdinarySourceRowTableMoment
                  formula row inOrdinary).2.val
            else 0) -
            physicalOrdinaryActualSourceCorrectionField
              formula row.val column)
          (physicalInterpolationRowBasisIndex
            row.val formula) = (1 : ZMod 2)) = _
    rw [paperVariableArityPhysicalSourceBasisCoordinate_sub_decide,
      paperVariableArityPhysicalOrdinaryActualDirectMomentBasis_decide]
  · rw [ite_eq_right matching]
    simp only [Module.Basis.equivFun_apply, map_zero, Pi.zero_apply, zero_ne_one, decide_false,
        matching,
      Fin.isValue, Bool.false_and]

end PhysicalOrdinaryInterpolationBinaryCheckBitCorrectness

open GapCVP.PhysicalOrdinaryInterpolationBinaryCheckBitCorrectness

namespace PhysicalOrdinaryShiftedCheckBitInstantiation

open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryFieldInverseAlgebra GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalColumnOrder GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.PhysicalInterpolationDirectMomentBitTM GapCVP.PhysicalInterpolationNodeCountBounds
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryShiftedCoefficientSumTM
open GapCVP.PhysicalOrdinaryInterpolationCheckFieldCorrectness
open GapCVP.PhysicalOrdinaryInterpolationBinaryCheckBitCorrectness
open GapCVP.PhysicalShiftedInterpolationBaseTM GapCVP.SourceFieldMomentOperationsTM
open GapCVP.SourceOrder

private def physicalOrdinarySourceCorrectionField
    (formula : ThreeCNF) (row : ℕ)
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula)) :
    PaperVariableArityPhysicalWordField
      (encodeThreeCNF formula).length formula :=
  physicalOrdinaryActualSourceCorrectionField
    formula row column

private theorem paperVariableArityPhysicalOrdinaryCorrectionBit_sourceCorrection
    (formula : ThreeCNF) (row : ℕ)
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula)) :
    physicalInterpolationNodeCorrectionBit
        (2 : Fin 4)
        (physicalOrdinaryNodePrefixWidth
          physicalOrdinaryInterpolationMomentComputer)
        physicalInterpolationColumnFieldComputer
        (affineCellQuery row column.val
          (encodeThreeCNF formula)) =
      [decide
        ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
          (encodeThreeCNF formula).length
          (srcFormula formula)).equivFun
            (physicalOrdinarySourceCorrectionField
              formula row column)
            (physicalInterpolationRowBasisIndex
              row formula) = (1 : ZMod 2))] := by
  exact paperVariableArityPhysicalInterpolationNodeCorrectionBit_sourceField_valid
    (2 : Fin 4)
    (physicalOrdinaryNodePrefixWidth
      physicalOrdinaryInterpolationMomentComputer)
    physicalInterpolationColumnFieldComputer
    row column.val formula
    (physicalOrdinaryInterpolationNodeCount row formula)
    (paperVariableArityPhysicalOrdinaryInterpolationNodeWidth_valid
      row column.val formula)
    (physicalOrdinaryInterpolationNodeCount_le_grid
      formula row)
    (physicalShiftedColumnValueSourceWord
      formula column.val)
    (paperVariableArityPhysicalOrdinaryColumnFieldComputer_valid
      formula row column)

private def physicalOrdinarySourceDirectBit
    (formula : ThreeCNF) (row : ℕ)
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula)) : Bool :=
  decide
    ((((row - physicalFamilyStart
          (2 : Fin 4) formula) /
        physDegree formula) %
        physGridCard formula) =
      ((column.val /
          physFieldCard formula) %
        physGridCard formula)) &&
    (sourceWordPow
      (physicalShiftedColumnValueSourceWord
        formula column.val)
      (physicalFamilyRowMoment
        (2 : Fin 4) row formula))
      (physicalInterpolationRowBasisIndex row formula)

private theorem paperVariableArityPhysicalOrdinaryDirectMomentBit_sourceDirect
    (formula : ThreeCNF) (row : ℕ)
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula)) :
    physicalFamilyDirectMomentBit
        (2 : Fin 4)
        physicalInterpolationColumnFieldComputer
        (affineCellQuery row column.val
          (encodeThreeCNF formula)) =
      [physicalOrdinarySourceDirectBit
        formula row column] := by
  exact paperVariableArityPhysicalFamilyDirectMomentBit_valid
    (2 : Fin 4)
    physicalInterpolationColumnFieldComputer
    row column.val formula
    (physicalShiftedColumnValueSourceWord
      formula column.val)
    (physicalInterpolationRowBasisIndex
      row formula)
    rfl
    (paperVariableArityPhysicalOrdinaryColumnFieldComputer_valid
      formula row column)

private theorem paperVariableArityPhysicalOrdinaryCheckBit_actualSourceBits
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula) :
    physicalOrdinaryCheckBit
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        ((physicalOrdinarySourceRowTableMoment
          formula row inOrdinary).1 =
          (sourceCoordinateWordOrder
            (encodeThreeCNF formula).length formula column).1) &&
       Bool.xor
        (physicalOrdinarySourceDirectBit
          formula row.val column)
        (decide
          ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
            (encodeThreeCNF formula).length
            (srcFormula formula)).equivFun
              (physicalOrdinarySourceCorrectionField
                formula row.val column)
              (physicalInterpolationRowBasisIndex
                row.val formula) = (1 : ZMod 2)))] := by
  have marker :
      physicalOrdinaryRowMarker
          (affineCellQuery row.val column.val
            (encodeThreeCNF formula)) = [true] := by
    rw [paperVariableArityPhysicalOrdinaryRowMarker_query]
    simp only [inOrdinary, and_self, decide_true]
  have bits := paperVariableArityPhysicalSourceInterpolationFamilyCheckBit_bits
    (2 : Fin 4)
    physicalOrdinaryRowMarker
    (physicalInterpolationFamilyTypeRankComputer
      (2 : Fin 4))
    (physicalOrdinaryNodePrefixWidth
      physicalOrdinaryInterpolationMomentComputer)
    physicalInterpolationColumnFieldComputer
    (affineCellQuery row.val column.val
      (encodeThreeCNF formula))
    true
    (decide
      ((physicalOrdinarySourceRowTableMoment
        formula row inOrdinary).1 =
        (sourceCoordinateWordOrder
          (encodeThreeCNF formula).length formula column).1))
    (physicalOrdinarySourceDirectBit
      formula row.val column)
    (decide
      ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
        (encodeThreeCNF formula).length
        (srcFormula formula)).equivFun
          (physicalOrdinarySourceCorrectionField
            formula row.val column)
          (physicalInterpolationRowBasisIndex
            row.val formula) = (1 : ZMod 2)))
    marker
    (paperVariableArityPhysicalOrdinaryExpectedTypeMatchBit_eq_sourceTable
      formula row column inOrdinary)
    (paperVariableArityPhysicalOrdinaryDirectMomentBit_sourceDirect
      formula row.val column)
    (paperVariableArityPhysicalOrdinaryCorrectionBit_sourceCorrection
      formula row.val column)
  exact bits

/-- Internal support shared across GapCVP continuation modules. -/
theorem paperVariableArityPhysicalOrdinaryCheckBit_valid
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula)) :
    physicalOrdinaryCheckBit
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        (physicalFormulaRefinementBoundary formula ≤
            row.val ∧
          row.val <
            physicalFormulaOrdinaryBoundary formula) &&
       decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).check
            row column = (1 : ZMod 2))] := by
  by_cases inOrdinary :
      physicalFormulaRefinementBoundary formula ≤ row.val ∧
        row.val < physicalFormulaOrdinaryBoundary formula
  · have bits := paperVariableArityPhysicalOrdinaryCheckBit_actualSourceBits
      formula row column inOrdinary
    have direct :
        physicalOrdinarySourceDirectBit
          formula row.val column =
        (decide
          ((((row.val -
              physicalFormulaRefinementBoundary formula) /
              physDegree formula) %
              physGridCard formula) =
            ((column.val /
              physFieldCard formula) %
              physGridCard formula)) &&
          (sourceWordPow
            (physicalShiftedColumnValueSourceWord
              formula column.val)
            (physicalFamilyRowMoment
              (2 : Fin 4) row.val formula))
            (physicalInterpolationRowBasisIndex
              row.val formula)) := by
      unfold physicalOrdinarySourceDirectBit
      rw [paperVariableArityPhysicalOrdinaryFamilyStart_eq_refinement]
    have correction :
        physicalOrdinarySourceCorrectionField
          formula row.val column =
        physicalOrdinaryActualSourceCorrectionField
          formula row.val column := by
      rfl
    rw [direct, correction] at bits
    have actual := paperVariableArityPhysicalOrdinaryActualBinaryCheckBit_decide
      formula row column inOrdinary
    calc
      physicalOrdinaryCheckBit
          (affineCellQuery row.val column.val
            (encodeThreeCNF formula)) =
          [decide
            ((physicalWordBinarySystem
              (encodeThreeCNF formula).length formula).check
                row column = (1 : ZMod 2))] :=
            bits.trans (congrArg (fun bit : Bool => [bit]) actual.symm)
      _ = _ := by simp only [inOrdinary,
          and_self, decide_true,
                      Bool.true_and]
  · calc
      physicalOrdinaryCheckBit
          (affineCellQuery row.val column.val
            (encodeThreeCNF formula)) = [false] :=
            paperVariableArityPhysicalOrdinaryCheckBit_of_not_in_family
              formula row.val column.val inOrdinary
      _ = _ := by simp only [inOrdinary, decide_false,
          Bool.false_and]

end PhysicalOrdinaryShiftedCheckBitInstantiation

namespace ShiftedClauseOffsetTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert
open GapCVP.SourceIndexedClauseLookupTM GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingTM GapCVP.ClauseOffsetTM GapCVP.RefinementClauseOffsetTM
open GapCVP.ShiftedTupleTM

private noncomputable def paperShiftedPrefixRankWidth :
    SourceQaryMaskDynamicGridWidth :=
  paperRefinementPrefixRankWidth

@[simp] private theorem paperVariableArityShiftedPrefixRankWidth_output
    (input : List Bool) :
    paperShiftedPrefixRankWidth.output input =
      firstFieldContents input := by
  rfl

private def paperVariableArityShiftedPrefixIndexedClauseQuery
    (input : List Bool) : List Bool :=
  paperRefinementPrefixIndexedClauseQuery input

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityShiftedPrefixIndexedClauseQueryComputable :
    BitTM
      paperVariableArityShiftedPrefixIndexedClauseQuery :=
  paperVariableArityRefinementPrefixIndexedClauseQueryComputable

private def paperShiftedClauseRankEnvelope
    (formula : ThreeCNF) (rank : ℕ) : List Bool :=
  lengthPrefixedWord (List.replicate rank true) ++
    sourceQaryMaskDynamicGridBaseSource
      paperShiftedRetainedClauseWidth
      (encodeThreeCNF formula)

private def paperVariableArityShiftedPrefixRankEnvelope
    (formula : ThreeCNF) (outer inner : ℕ) : List Bool :=
  paperRefinementPrefixRankEnvelope formula outer inner

@[simp] private theorem paperVariableArityShiftedPrefixIndexedClauseQuery_valid
    (formula : ThreeCNF) (outer inner : ℕ) :
    paperVariableArityShiftedPrefixIndexedClauseQuery
      (paperVariableArityShiftedPrefixRankEnvelope formula outer inner) =
      sourceOriginalIndexedClauseQuery inner
        (noTautClauses formula) :=
  paperVariableArityRefinementPrefixIndexedClauseQuery_valid formula outer inner

private def paperShiftedPrefixIndexedClauseWeightUnary :
    List Bool → List Bool :=
  paperShiftedClauseWeightUnary ∘
    sourceOriginalIndexedClauseOutput ∘
    paperVariableArityShiftedPrefixIndexedClauseQuery

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityShiftedPrefixIndexedClauseWeightUnaryComputable :
    BitTM
      paperShiftedPrefixIndexedClauseWeightUnary := by
  have indexed := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityShiftedPrefixIndexedClauseQueryComputable
    sourceOriginalIndexedClauseComputable
  exact GapCVP.TMComposition.computableInPolyTime
    indexed paperVariableArityShiftedClauseWeightUnaryComputable

private theorem paperVariableArityShiftedPrefixIndexedClauseWeightUnary_valid
    (formula : ThreeCNF) (outer inner : ℕ)
    (hinner : inner < (noTautClauses formula).length) :
    paperShiftedPrefixIndexedClauseWeightUnary
      (paperVariableArityShiftedPrefixRankEnvelope
        formula outer inner) =
      List.replicate
        (paperShiftedSourceClauseWeight
          ((noTautClauses formula).get
            ⟨inner, hinner⟩)) true := by
  unfold paperShiftedPrefixIndexedClauseWeightUnary
  simp only [Function.comp_apply]
  rw [paperVariableArityShiftedPrefixIndexedClauseQuery_valid,
    sourceOriginalIndexedClauseOutput_valid inner
      (noTautClauses formula) hinner]
  simpa only [List.get_eq_getElem, List.append_nil] using
      paperVariableArityShiftedClauseWeightUnary_valid ((noTautClauses formula).get ⟨inner,
          hinner⟩) []

private def paperShiftedClauseOffsetUnary :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    paperShiftedPrefixRankWidth
    paperVariableArityShiftedPrefixIndexedClauseWeightUnaryComputable

private noncomputable def paperVariableArityShiftedClauseOffsetUnaryComputable :
    BitTM
      paperShiftedClauseOffsetUnary :=
  maskDynamicGridRecordCatalogueComputable
    paperShiftedPrefixRankWidth
    paperVariableArityShiftedPrefixIndexedClauseWeightUnaryComputable

private theorem paperVariableArityShiftedClauseOffsetUnary_valid
    (formula : ThreeCNF) (rank : ℕ)
    (hbound : rank ≤ (noTautClauses formula).length) :
    paperShiftedClauseOffsetUnary
        (paperShiftedClauseRankEnvelope formula rank) =
      List.replicate
        (paperShiftedSourceClauseWeightSum
          ((noTautClauses formula).take rank)) true := by
  have hwidth :
      paperShiftedPrefixRankWidth.output
          (paperShiftedClauseRankEnvelope formula rank) =
        List.replicate rank true := by
    rw [paperVariableArityShiftedPrefixRankWidth_output]
    simp only [paperShiftedClauseRankEnvelope, firstFieldContents_valid]
  have catalogue := maskDynamicGridRecordCatalogueOutput_valid
    paperShiftedPrefixRankWidth
    paperVariableArityShiftedPrefixIndexedClauseWeightUnaryComputable
    (paperShiftedClauseRankEnvelope formula rank)
    rank hwidth
  change maskDynamicGridRecordCatalogueOutput
    paperShiftedPrefixRankWidth
    paperVariableArityShiftedPrefixIndexedClauseWeightUnaryComputable
    (paperShiftedClauseRankEnvelope formula rank) = _
  rw [catalogue]
  rw [← paperVariableArityShiftedSourceClauseWeight_flatMap
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
  change paperShiftedPrefixIndexedClauseWeightUnary
    (paperVariableArityShiftedPrefixRankEnvelope
      formula rank inner) = _
  rw [paperVariableArityShiftedPrefixIndexedClauseWeightUnary_valid
    formula rank inner hinner]
  simp only [paperShiftedIndexedSourceClauseWeight,
    List.getElem?_take, ite_eq_left hlt,
    List.getElem?_eq_getElem hinner, List.get_eq_getElem]

private def paperShiftedSelectedOriginalClauseWord :
    List Bool → List Bool :=
  sourceOriginalIndexedClauseOutput ∘
    paperShiftedIndexedClauseQuery

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityShiftedSelectedOriginalClauseWordComputable :
    BitTM
      paperShiftedSelectedOriginalClauseWord :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityShiftedIndexedClauseQueryComputable
    sourceOriginalIndexedClauseComputable

private theorem paperVariableArityShiftedSelectedOriginalClauseWord_valid
    (formula : ThreeCNF) (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length) :
    paperShiftedSelectedOriginalClauseWord
      (paperShiftedClauseRankEnvelope formula rank) =
      encodeThreeClause
        ((noTautClauses formula).get
          ⟨rank, hbound⟩) := by
  unfold paperShiftedSelectedOriginalClauseWord
  simp only [Function.comp_apply,
    paperShiftedClauseRankEnvelope]
  rw [paperVariableArityShiftedIndexedClauseQuery_valid,
    sourceOriginalIndexedClauseOutput_valid rank
      (noTautClauses formula) hbound]

private def paperVariableArityShiftedSelectedClauseArityUnary :
    List Bool → List Bool :=
  paperVariableArityClauseArityUnary ∘
    paperShiftedSelectedOriginalClauseWord

private noncomputable def paperVariableArityShiftedSelectedClauseArityUnaryComputable :
    BitTM
      paperVariableArityShiftedSelectedClauseArityUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityShiftedSelectedOriginalClauseWordComputable
    paperClauseArityUnaryComputable

end ShiftedClauseOffsetTM

namespace PhysicalShiftedRowTupleRankTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryDimensionTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalRowBasisDivisionTM
open GapCVP.SourcePreprocessingTM GapCVP.SourcePreprocessingSemantics GapCVP.ClauseOffsetTM
open GapCVP.ShiftedTupleTM GapCVP.ShiftedClauseOffsetTM GapCVP.ShiftedTupleBetaTM
open GapCVP.PhysicalFamilyRowTM GapCVP.SourceFieldMomentOperationsTM

private def physicalShiftedRowMixedTagWord :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryQuotient
    (physicalFamilyRowGridQuotientWord (3 : Fin 4))
    physicalMomentCellMomentCountUnary

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowMixedTagComputable :
    BitTM
      physicalShiftedRowMixedTagWord :=
  sourcePhysicalComputedUnaryQuotientComputable
    (paperVariableArityPhysicalFamilyRowGridQuotientComputable (3 : Fin 4))
    paperVariableArityPhysicalMomentCellMomentCountUnaryComputable

@[simp] private theorem paperVariableArityPhysicalShiftedRowMixedTagWord_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalShiftedRowMixedTagWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        ((((row - physicalFormulaOrdinaryBoundary formula) /
          physDegree formula) /
          physGridCard formula) /
          physicalFormulaMomentCount formula) true := by
  unfold physicalShiftedRowMixedTagWord
  apply sourcePhysicalComputedUnaryQuotient_valid
    (physicalFamilyRowGridQuotientWord (3 : Fin 4))
    physicalMomentCellMomentCountUnary
    (affineCellQuery row column (encodeThreeCNF formula))
    (((row - physicalFormulaOrdinaryBoundary formula) /
      physDegree formula) /
      physGridCard formula)
    (physicalFormulaMomentCount formula)
    (physicalFormulaMomentCount_pos formula)
  · have start :
        physicalFamilyStart (3 : Fin 4) formula =
          physicalFormulaOrdinaryBoundary formula := by
      simp only [physicalFamilyStart, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
          OfNat.ofNat_ne_zero,
        ↓reduceIte, OfNat.ofNat_ne_one, OfNat.ofNat_eq_ofNat, Nat.succ_ne_self]
    rw [← start]
    exact paperVariableArityPhysicalFamilyRowGridQuotientWord_valid
      (3 : Fin 4) row column formula
  · exact paperVariableArityPhysicalMomentCellMomentCountUnary_valid
      row column formula

private def physicalShiftedRowRetainedCountWord :
    List Bool → List Bool :=
  paperRetainedClauseCountUnary ∘
    sourceExplicitAffineCellOriginalSource

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowRetainedCountComputable :
    BitTM
      physicalShiftedRowRetainedCountWord :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    paperVariableArityRetainedClauseCountUnaryComputable

@[simp] private theorem paperVariableArityPhysicalShiftedRowRetainedCountWord_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalShiftedRowRetainedCountWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate (noTautClauses formula).length true := by
  unfold physicalShiftedRowRetainedCountWord
  rw [Function.comp_apply, sourceExplicitAffineCellOriginalSource_query,
    paperVariableArityRetainedClauseCountUnary_valid]

private noncomputable def physicalShiftedRowRetainedClauseWidth :
    SourceQaryMaskDynamicGridWidth where
  output := physicalShiftedRowRetainedCountWord
  computer := paperVariableArityPhysicalShiftedRowRetainedCountComputable

@[simp] private theorem paperVariableArityPhysicalShiftedRowRetainedClauseWidth_output
    (input : List Bool) :
    physicalShiftedRowRetainedClauseWidth.output input =
      physicalShiftedRowRetainedCountWord input := by
  rfl

private def physicalShiftedRowMixedTag
    (formula : ThreeCNF) (row : ℕ) : ℕ :=
  (((row - physicalFormulaOrdinaryBoundary formula) /
    physDegree formula) /
    physGridCard formula) /
    physicalFormulaMomentCount formula

private def physicalShiftedRowClausePrefix
    (formula : ThreeCNF) (rank : ℕ) : ℕ :=
  paperShiftedSourceClauseWeightSum
    ((noTautClauses formula).take rank)

private def physicalShiftedRowCandidateRankEnvelope
    (formula : ThreeCNF) (row column rank : ℕ) : List Bool :=
  lengthPrefixedWord (List.replicate rank true) ++
    sourceQaryMaskDynamicGridBaseSource
      physicalShiftedRowRetainedClauseWidth
      (affineCellQuery row column (encodeThreeCNF formula))

private def physicalShiftedRowCandidateCell :
    List Bool → List Bool :=
  paperSourcePreprocessingSuffixAt 2

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowCandidateCellComputable :
    BitTM
      physicalShiftedRowCandidateCell :=
  paperPreprocessingSuffixAtComputable 2

@[simp] private theorem paperVariableArityPhysicalShiftedRowCandidateCell_query
    (formula : ThreeCNF) (row column rank : ℕ) :
    physicalShiftedRowCandidateCell
        (physicalShiftedRowCandidateRankEnvelope
          formula row column rank) =
      affineCellQuery row column (encodeThreeCNF formula) := by
  simp [physicalShiftedRowCandidateCell,
    physicalShiftedRowCandidateRankEnvelope,
    sourceQaryMaskDynamicGridBaseSource,
    paperSourcePreprocessingSuffixAt, Function.iterate_succ_apply]

private def physicalShiftedRowCandidateClauseEnvelope
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (firstFieldContents input) ++
    sourceQaryMaskDynamicGridBaseSource
      paperShiftedRetainedClauseWidth
      (sourceExplicitAffineCellOriginalSource
        (physicalShiftedRowCandidateCell input))

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowCandidateClauseEnvelopeComputable :
    BitTM
      physicalShiftedRowCandidateClauseEnvelope := by
  have rank := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable structuralPrefixWriterComputable
  have source := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalShiftedRowCandidateCellComputable
    sourceExplicitAffineCellOriginalSourceComputable
  have base := GapCVP.TMComposition.computableInPolyTime
    source
    (maskDynamicGridBaseSourceComputable
      paperShiftedRetainedClauseWidth)
  exact pointwiseAppendComputable rank base

@[simp] theorem
    paperVariableArityPhysicalShiftedRowCandidateClauseEnvelope_query
    (formula : ThreeCNF) (row column rank : ℕ) :
    physicalShiftedRowCandidateClauseEnvelope
        (physicalShiftedRowCandidateRankEnvelope
          formula row column rank) =
      paperShiftedClauseRankEnvelope formula rank := by
  simp [physicalShiftedRowCandidateClauseEnvelope,
    physicalShiftedRowCandidateRankEnvelope,
    paperShiftedClauseRankEnvelope,
    sourceQaryMaskDynamicGridBaseSource,
    physicalShiftedRowCandidateCell,
    paperSourcePreprocessingSuffixAt, Function.iterate_succ_apply]

private def physicalShiftedRowCandidatePrefixWord :
    List Bool → List Bool :=
  paperShiftedClauseOffsetUnary ∘
    physicalShiftedRowCandidateClauseEnvelope

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowCandidatePrefixComputable :
    BitTM
      physicalShiftedRowCandidatePrefixWord :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalShiftedRowCandidateClauseEnvelopeComputable
    paperVariableArityShiftedClauseOffsetUnaryComputable

private theorem paperVariableArityPhysicalShiftedRowCandidatePrefixWord_query
    (formula : ThreeCNF) (row column rank : ℕ)
    (hbound : rank ≤ (noTautClauses formula).length) :
    physicalShiftedRowCandidatePrefixWord
        (physicalShiftedRowCandidateRankEnvelope
          formula row column rank) =
      List.replicate
        (physicalShiftedRowClausePrefix formula rank) true := by
  unfold physicalShiftedRowCandidatePrefixWord
  rw [Function.comp_apply,
    paperVariableArityPhysicalShiftedRowCandidateClauseEnvelope_query,
    paperVariableArityShiftedClauseOffsetUnary_valid formula rank hbound]
  rfl

private def physicalShiftedRowCandidateMixedTagWord :
    List Bool → List Bool :=
  physicalShiftedRowMixedTagWord ∘
    physicalShiftedRowCandidateCell

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowCandidateMixedTagComputable :
    BitTM
      physicalShiftedRowCandidateMixedTagWord :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalShiftedRowCandidateCellComputable
    paperVariableArityPhysicalShiftedRowMixedTagComputable

@[simp] theorem
    paperVariableArityPhysicalShiftedRowCandidateMixedTagWord_query
    (formula : ThreeCNF) (row column rank : ℕ) :
    physicalShiftedRowCandidateMixedTagWord
        (physicalShiftedRowCandidateRankEnvelope
          formula row column rank) =
      List.replicate
        (physicalShiftedRowMixedTag formula row) true := by
  unfold physicalShiftedRowCandidateMixedTagWord
  rw [Function.comp_apply,
    paperVariableArityPhysicalShiftedRowCandidateCell_query,
    paperVariableArityPhysicalShiftedRowMixedTagWord_query]
  rfl

private def paperVariableArityPhysicalShiftedRowCandidatePrefixMarker :
    List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    (fourFamilyComputedUnaryLessBitOutput
      physicalShiftedRowCandidateMixedTagWord
      physicalShiftedRowCandidatePrefixWord)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowCandidatePrefixMarkerComputable :
    BitTM
      paperVariableArityPhysicalShiftedRowCandidatePrefixMarker :=
  fourFamilyBooleanNotOutputComputable
    (fourFamilyComputedUnaryLessBitComputable
      paperVariableArityPhysicalShiftedRowCandidateMixedTagComputable
      paperVariableArityPhysicalShiftedRowCandidatePrefixComputable)

private def physicalShiftedRowCandidatePrefixRecord :
    List Bool → List Bool :=
  paperShiftedTupleGuardedSourceWord
    paperVariableArityPhysicalShiftedRowCandidatePrefixMarker
    (paperShiftedTupleConstantUnary 1)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowCandidatePrefixRecordComputable :
    BitTM
      physicalShiftedRowCandidatePrefixRecord :=
  paperVariableArityShiftedTupleGuardedSourceWordComputable
    paperVariableArityPhysicalShiftedRowCandidatePrefixMarkerComputable
    (paperVariableArityShiftedTupleConstantUnaryComputable 1)

private theorem paperVariableArityPhysicalShiftedRowCandidatePrefixRecord_query
    (formula : ThreeCNF) (row column rank : ℕ)
    (hbound : rank ≤ (noTautClauses formula).length) :
    physicalShiftedRowCandidatePrefixRecord
        (physicalShiftedRowCandidateRankEnvelope
          formula row column rank) =
      if physicalShiftedRowMixedTag formula row <
          physicalShiftedRowClausePrefix formula rank
      then [] else [true] := by
  let input := physicalShiftedRowCandidateRankEnvelope
    formula row column rank
  let tag := physicalShiftedRowMixedTag formula row
  let sourceOffset :=
    physicalShiftedRowClausePrefix formula rank
  have comparison := fourFamilyComputedUnaryLessBitOutput_valid
    physicalShiftedRowCandidateMixedTagWord
    physicalShiftedRowCandidatePrefixWord
    input tag sourceOffset
    (paperVariableArityPhysicalShiftedRowCandidateMixedTagWord_query
      formula row column rank)
    (paperVariableArityPhysicalShiftedRowCandidatePrefixWord_query
      formula row column rank hbound)
  have marker := fourFamilyBooleanNotOutput_bit
    (fourFamilyComputedUnaryLessBitOutput
      physicalShiftedRowCandidateMixedTagWord
      physicalShiftedRowCandidatePrefixWord)
    input (decide (tag < sourceOffset)) comparison
  unfold physicalShiftedRowCandidatePrefixRecord
  rw [paperShiftedTupleGuardedSourceWord_valid
    paperVariableArityPhysicalShiftedRowCandidatePrefixMarker
    (paperShiftedTupleConstantUnary 1)
    input (!(decide (tag < sourceOffset))) marker]
  by_cases reached : tag < sourceOffset
  · simp only [reached, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, tag,
      sourceOffset]
  · simp only [reached, decide_false, Bool.not_false, ↓reduceIte, paperShiftedTupleConstantUnary,
        List.replicate_one, tag, sourceOffset]

private def physicalShiftedRowAcceptedPrefixCountWord :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    physicalShiftedRowRetainedClauseWidth
    paperVariableArityPhysicalShiftedRowCandidatePrefixRecordComputable

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowAcceptedPrefixCountComputable :
    BitTM
      physicalShiftedRowAcceptedPrefixCountWord :=
  maskDynamicGridRecordCatalogueComputable
    physicalShiftedRowRetainedClauseWidth
    paperVariableArityPhysicalShiftedRowCandidatePrefixRecordComputable

private def physicalShiftedRowAcceptedPrefixCount
    (formula : ThreeCNF) (row : ℕ) : ℕ :=
  ((List.range (noTautClauses formula).length).filter
    fun rank => decide
      (physicalShiftedRowClausePrefix formula rank ≤
        physicalShiftedRowMixedTag formula row)).length

private theorem paperVariableArityPhysicalShiftedRowAcceptedPrefixFlatMap
    (ranks : List ℕ) (tag : ℕ) (weightPrefix : ℕ → ℕ) :
    ranks.flatMap (fun rank =>
      if tag < weightPrefix rank then [] else [true]) =
      List.replicate
        (ranks.filter (fun rank => decide (weightPrefix rank ≤ tag))).length
        true := by
  induction ranks with
  | nil => rfl
  | cons rank remaining induction =>
      by_cases less : tag < weightPrefix rank
      · simp only [List.flatMap_cons, less, ↓reduceIte, induction, List.nil_append, Nat.not_le.mpr
          less, decide_false,
            Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg]
      · have reached : weightPrefix rank ≤ tag := Nat.le_of_not_gt less
        simp only [List.flatMap_cons, less, ↓reduceIte, induction, List.cons_append,
            List.nil_append, reached,
            decide_true, List.filter_cons_of_pos, List.length_cons, List.replicate_succ]

private theorem paperVariableArityPhysicalShiftedRowAcceptedPrefixCountWord_query
    (formula : ThreeCNF) (row column : ℕ) :
    physicalShiftedRowAcceptedPrefixCountWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalShiftedRowAcceptedPrefixCount formula row)
        true := by
  let input := affineCellQuery row column
    (encodeThreeCNF formula)
  let count := (noTautClauses formula).length
  have width :
      physicalShiftedRowRetainedClauseWidth.output input =
        List.replicate count true := by
    rw [paperVariableArityPhysicalShiftedRowRetainedClauseWidth_output,
      paperVariableArityPhysicalShiftedRowRetainedCountWord_query]
  have catalogue := maskDynamicGridRecordCatalogueOutput_valid
    physicalShiftedRowRetainedClauseWidth
    paperVariableArityPhysicalShiftedRowCandidatePrefixRecordComputable
    input count width
  unfold physicalShiftedRowAcceptedPrefixCountWord
  rw [catalogue]
  change
    (List.range count).flatMap
      (fun rank => physicalShiftedRowCandidatePrefixRecord
        (physicalShiftedRowCandidateRankEnvelope
          formula row column rank)) =
      List.replicate
        (physicalShiftedRowAcceptedPrefixCount
          formula row) true
  unfold physicalShiftedRowAcceptedPrefixCount
  rw [← paperVariableArityPhysicalShiftedRowAcceptedPrefixFlatMap
    (List.range (noTautClauses formula).length)
    (physicalShiftedRowMixedTag formula row)
    (physicalShiftedRowClausePrefix formula)]
  apply List.flatMap_congr
  intro rank membership
  exact paperVariableArityPhysicalShiftedRowCandidatePrefixRecord_query
    formula row column rank
    (Nat.le_of_lt (List.mem_range.mp membership))

private def physicalShiftedRowClauseRankWord :
    List Bool → List Bool :=
  unarySubtractionOutput
    physicalShiftedRowAcceptedPrefixCountWord
    (paperShiftedTupleConstantUnary 1)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowClauseRankComputable :
    BitTM
      physicalShiftedRowClauseRankWord :=
  unarySubtractionComputable
    paperVariableArityPhysicalShiftedRowAcceptedPrefixCountComputable
    (paperVariableArityShiftedTupleConstantUnaryComputable 1)

private def physicalShiftedRowClauseRank
    (formula : ThreeCNF) (row : ℕ) : ℕ :=
  physicalShiftedRowAcceptedPrefixCount formula row - 1

@[simp] private theorem paperVariableArityPhysicalShiftedRowClauseRankWord_query
    (formula : ThreeCNF) (row column : ℕ) :
    physicalShiftedRowClauseRankWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalShiftedRowClauseRank formula row) true := by
  unfold physicalShiftedRowClauseRankWord
    physicalShiftedRowClauseRank
  apply unarySubtractionOutput_valid
    physicalShiftedRowAcceptedPrefixCountWord
    (paperShiftedTupleConstantUnary 1)
    (affineCellQuery row column (encodeThreeCNF formula))
    (physicalShiftedRowAcceptedPrefixCount formula row) 1
  · exact paperVariableArityPhysicalShiftedRowAcceptedPrefixCountWord_query
      formula row column
  · rfl

private def physicalShiftedRowSelectedClauseEnvelope
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (physicalShiftedRowClauseRankWord input) ++
    sourceQaryMaskDynamicGridBaseSource
      paperShiftedRetainedClauseWidth
      (sourceExplicitAffineCellOriginalSource input)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowSelectedClauseEnvelopeComputable :
    BitTM
      physicalShiftedRowSelectedClauseEnvelope := by
  have rank := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalShiftedRowClauseRankComputable
    structuralPrefixWriterComputable
  have source := GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    (maskDynamicGridBaseSourceComputable
      paperShiftedRetainedClauseWidth)
  exact pointwiseAppendComputable rank source

@[simp] private theorem paperVariableArityPhysicalShiftedRowSelectedClauseEnvelope_query
    (formula : ThreeCNF) (row column : ℕ) :
    physicalShiftedRowSelectedClauseEnvelope
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      paperShiftedClauseRankEnvelope formula
        (physicalShiftedRowClauseRank formula row) := by
  unfold physicalShiftedRowSelectedClauseEnvelope
    paperShiftedClauseRankEnvelope
  rw [paperVariableArityPhysicalShiftedRowClauseRankWord_query,
    sourceExplicitAffineCellOriginalSource_query]

private def physicalShiftedRowSelectedClauseArityWord :
    List Bool → List Bool :=
  paperVariableArityShiftedSelectedClauseArityUnary ∘
    physicalShiftedRowSelectedClauseEnvelope

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowSelectedClauseArityComputable :
    BitTM
      physicalShiftedRowSelectedClauseArityWord :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalShiftedRowSelectedClauseEnvelopeComputable
    paperVariableArityShiftedSelectedClauseArityUnaryComputable

private def physicalShiftedRowSelectedClausePrefixWord :
    List Bool → List Bool :=
  paperShiftedClauseOffsetUnary ∘
    physicalShiftedRowSelectedClauseEnvelope

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowSelectedClausePrefixComputable :
    BitTM
      physicalShiftedRowSelectedClausePrefixWord :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalShiftedRowSelectedClauseEnvelopeComputable
    paperVariableArityShiftedClauseOffsetUnaryComputable

private theorem paperVariableArityPhysicalShiftedRowSelectedClausePrefixWord_query
    (formula : ThreeCNF) (row column : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row ≤
      (noTautClauses formula).length) :
    physicalShiftedRowSelectedClausePrefixWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalShiftedRowClausePrefix formula
          (physicalShiftedRowClauseRank formula row))
        true := by
  unfold physicalShiftedRowSelectedClausePrefixWord
  rw [Function.comp_apply,
    paperVariableArityPhysicalShiftedRowSelectedClauseEnvelope_query,
    paperVariableArityShiftedClauseOffsetUnary_valid _ _ hbound]
  rfl

private def physicalShiftedRowSelectedClauseArity
    (formula : ThreeCNF) (row : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) : ℕ :=
  (paperSourceNormalizedClause
    ((noTautClauses formula).get
      ⟨physicalShiftedRowClauseRank formula row,
        hbound⟩)).length

private theorem paperVariableArityPhysicalShiftedRowSelectedClauseArityWord_query
    (formula : ThreeCNF) (row column : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) :
    physicalShiftedRowSelectedClauseArityWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalShiftedRowSelectedClauseArity
          formula row hbound) true := by
  unfold physicalShiftedRowSelectedClauseArityWord
    physicalShiftedRowSelectedClauseArity
  rw [Function.comp_apply,
    paperVariableArityPhysicalShiftedRowSelectedClauseEnvelope_query]
  unfold paperVariableArityShiftedSelectedClauseArityUnary
  rw [Function.comp_apply,
    paperVariableArityShiftedSelectedOriginalClauseWord_valid
      formula (physicalShiftedRowClauseRank formula row)
      hbound]
  have actual := paperVariableArityClauseArityUnary_valid
    ((noTautClauses formula).get
      ⟨physicalShiftedRowClauseRank formula row,
        hbound⟩) []
  simpa only [List.append_nil] using actual

private theorem paperVariableArityPhysicalShiftedRowSelectedClauseArity_pos
    (formula : ThreeCNF) (row : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) :
    0 < physicalShiftedRowSelectedClauseArity
      formula row hbound := by
  unfold physicalShiftedRowSelectedClauseArity
  exact List.length_pos_iff.mpr
    (paperSourceNormalizedClause_ne_nil
      ((noTautClauses formula).get
        ⟨physicalShiftedRowClauseRank formula row,
          hbound⟩))

private def physicalShiftedRowLocalTagWord :
    List Bool → List Bool :=
  unarySubtractionOutput
    physicalShiftedRowMixedTagWord
    physicalShiftedRowSelectedClausePrefixWord

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowLocalTagComputable :
    BitTM
      physicalShiftedRowLocalTagWord :=
  unarySubtractionComputable
    paperVariableArityPhysicalShiftedRowMixedTagComputable
    paperVariableArityPhysicalShiftedRowSelectedClausePrefixComputable

private def physicalShiftedRowLocalTag
    (formula : ThreeCNF) (row : ℕ) : ℕ :=
  physicalShiftedRowMixedTag formula row -
    physicalShiftedRowClausePrefix formula
      (physicalShiftedRowClauseRank formula row)

private theorem paperVariableArityPhysicalShiftedRowLocalTagWord_query
    (formula : ThreeCNF) (row column : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row ≤
      (noTautClauses formula).length) :
    physicalShiftedRowLocalTagWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalShiftedRowLocalTag formula row) true := by
  unfold physicalShiftedRowLocalTagWord
    physicalShiftedRowLocalTag
  apply unarySubtractionOutput_valid
    physicalShiftedRowMixedTagWord
    physicalShiftedRowSelectedClausePrefixWord
    (affineCellQuery row column (encodeThreeCNF formula))
    (physicalShiftedRowMixedTag formula row)
    (physicalShiftedRowClausePrefix formula
      (physicalShiftedRowClauseRank formula row))
  · exact paperVariableArityPhysicalShiftedRowMixedTagWord_query
      row column formula
  · exact paperVariableArityPhysicalShiftedRowSelectedClausePrefixWord_query
      formula row column hbound

private def physicalShiftedRowTupleRankWord :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryQuotient
    physicalShiftedRowLocalTagWord
    physicalShiftedRowSelectedClauseArityWord

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowTupleRankComputable :
    BitTM
      physicalShiftedRowTupleRankWord :=
  sourcePhysicalComputedUnaryQuotientComputable
    paperVariableArityPhysicalShiftedRowLocalTagComputable
    paperVariableArityPhysicalShiftedRowSelectedClauseArityComputable

private def physicalShiftedRowVariablePositionWord :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryRemainder
    physicalShiftedRowLocalTagWord
    physicalShiftedRowSelectedClauseArityWord

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedRowVariablePositionComputable :
    BitTM
      physicalShiftedRowVariablePositionWord :=
  sourcePhysicalComputedUnaryRemainderComputable
    paperVariableArityPhysicalShiftedRowLocalTagComputable
    paperVariableArityPhysicalShiftedRowSelectedClauseArityComputable

private def physicalShiftedRowTupleRank
    (formula : ThreeCNF) (row : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) : ℕ :=
  physicalShiftedRowLocalTag formula row /
    physicalShiftedRowSelectedClauseArity
      formula row hbound

private def physicalShiftedRowVariablePosition
    (formula : ThreeCNF) (row : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) : ℕ :=
  physicalShiftedRowLocalTag formula row %
    physicalShiftedRowSelectedClauseArity
      formula row hbound

private theorem paperVariableArityPhysicalShiftedRowTupleRankWord_query
    (formula : ThreeCNF) (row column : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) :
    physicalShiftedRowTupleRankWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalShiftedRowTupleRank
          formula row hbound) true := by
  unfold physicalShiftedRowTupleRankWord
    physicalShiftedRowTupleRank
  apply sourcePhysicalComputedUnaryQuotient_valid
    physicalShiftedRowLocalTagWord
    physicalShiftedRowSelectedClauseArityWord
    (affineCellQuery row column (encodeThreeCNF formula))
    (physicalShiftedRowLocalTag formula row)
    (physicalShiftedRowSelectedClauseArity
      formula row hbound)
    (paperVariableArityPhysicalShiftedRowSelectedClauseArity_pos
      formula row hbound)
  · exact paperVariableArityPhysicalShiftedRowLocalTagWord_query
      formula row column (Nat.le_of_lt hbound)
  · exact paperVariableArityPhysicalShiftedRowSelectedClauseArityWord_query
      formula row column hbound

private theorem paperVariableArityPhysicalShiftedRowVariablePositionWord_query
    (formula : ThreeCNF) (row column : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) :
    physicalShiftedRowVariablePositionWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalShiftedRowVariablePosition
          formula row hbound) true := by
  unfold physicalShiftedRowVariablePositionWord
    physicalShiftedRowVariablePosition
  apply sourcePhysicalComputedUnaryRemainder_valid
    physicalShiftedRowLocalTagWord
    physicalShiftedRowSelectedClauseArityWord
    (affineCellQuery row column (encodeThreeCNF formula))
    (physicalShiftedRowLocalTag formula row)
    (physicalShiftedRowSelectedClauseArity
      formula row hbound)
    (paperVariableArityPhysicalShiftedRowSelectedClauseArity_pos
      formula row hbound)
  · exact paperVariableArityPhysicalShiftedRowLocalTagWord_query
      formula row column (Nat.le_of_lt hbound)
  · exact paperVariableArityPhysicalShiftedRowSelectedClauseArityWord_query
      formula row column hbound

private noncomputable def physicalShiftedRowTupleRankComputers :
    PaperVariableArityShiftedTupleRankComputers where
  clause :=
    { output := physicalShiftedRowClauseRankWord
      computer := paperVariableArityPhysicalShiftedRowClauseRankComputable }
  tuple :=
    { output := physicalShiftedRowTupleRankWord
      computer := paperVariableArityPhysicalShiftedRowTupleRankComputable }
  variablePosition :=
    { output := physicalShiftedRowVariablePositionWord
      computer :=
        paperVariableArityPhysicalShiftedRowVariablePositionComputable }

@[simp] theorem
    paperVariableArityPhysicalShiftedRowTupleRankComputers_clause_query
    (formula : ThreeCNF) (row column : ℕ) :
    physicalShiftedRowTupleRankComputers.clause.output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalShiftedRowClauseRank formula row) true := by
  dsimp only [physicalShiftedRowTupleRankComputers]
  exact paperVariableArityPhysicalShiftedRowClauseRankWord_query
    formula row column

private theorem paperVariableArityPhysicalShiftedRowTupleRankComputers_tuple_query
    (formula : ThreeCNF) (row column : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) :
    physicalShiftedRowTupleRankComputers.tuple.output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalShiftedRowTupleRank
          formula row hbound) true := by
  dsimp only [physicalShiftedRowTupleRankComputers]
  exact paperVariableArityPhysicalShiftedRowTupleRankWord_query
    formula row column hbound

theorem
    paperVariableArityPhysicalShiftedRowTupleRankComputers_variablePosition_query
    (formula : ThreeCNF) (row column : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) :
    physicalShiftedRowTupleRankComputers.variablePosition.output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalShiftedRowVariablePosition
          formula row hbound) true := by
  dsimp only [physicalShiftedRowTupleRankComputers]
  exact paperVariableArityPhysicalShiftedRowVariablePositionWord_query
    formula row column hbound

private theorem paperVariableArityPhysicalShiftedRowVariablePosition_lt_arity
    (formula : ThreeCNF) (row : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) :
    physicalShiftedRowVariablePosition formula row hbound <
      physicalShiftedRowSelectedClauseArity
        formula row hbound := by
  unfold physicalShiftedRowVariablePosition
  exact Nat.mod_lt _
    (paperVariableArityPhysicalShiftedRowSelectedClauseArity_pos
      formula row hbound)

private theorem paperVariableArityPhysicalShiftedRowVariablePosition_lt_three
    (formula : ThreeCNF) (row : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) :
    physicalShiftedRowVariablePosition
      formula row hbound < 3 := by
  have arity := paperVariableArityPhysicalShiftedRowVariablePosition_lt_arity
    formula row hbound
  have bounded := paperNormalizedClause_length_le_three
    ((noTautClauses formula).get
      ⟨physicalShiftedRowClauseRank formula row,
        hbound⟩)
  change physicalShiftedRowVariablePosition
      formula row hbound <
    (paperSourceNormalizedClause
      ((noTautClauses formula).get
        ⟨physicalShiftedRowClauseRank formula row,
          hbound⟩)).length at arity
  omega

end PhysicalShiftedRowTupleRankTM

namespace PhysicalShiftedExpectedTypeRankTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.ClauseOffsetTM GapCVP.ShiftedTupleBetaTM
open GapCVP.RefinementClauseOffsetTM GapCVP.PhysicalShiftedRowTupleRankTM

private def physicalShiftedExpectedLocalTypePrefixWord :
    List Bool → List Bool :=
  paperRefinementClauseOffsetUnary ∘
    physicalShiftedRowSelectedClauseEnvelope

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedExpectedLocalTypePrefixComputable :
    BitTM
      physicalShiftedExpectedLocalTypePrefixWord :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalShiftedRowSelectedClauseEnvelopeComputable
    paperVariableArityRefinementClauseOffsetUnaryComputable

private def physicalShiftedExpectedLocalTypePrefix
    (formula : ThreeCNF) (row : ℕ) : ℕ :=
  sourceClauseWeightSum
    ((noTautClauses formula).take
      (physicalShiftedRowClauseRank formula row))

private theorem paperVariableArityPhysicalShiftedExpectedLocalTypePrefixWord_query
    (formula : ThreeCNF) (row column : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row ≤
      (noTautClauses formula).length) :
    physicalShiftedExpectedLocalTypePrefixWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalShiftedExpectedLocalTypePrefix
          formula row) true := by
  unfold physicalShiftedExpectedLocalTypePrefixWord
  rw [Function.comp_apply,
    paperVariableArityPhysicalShiftedRowSelectedClauseEnvelope_query]
  change paperRefinementClauseOffsetUnary
    (paperRefinementClauseRankEnvelope formula
      (physicalShiftedRowClauseRank formula row)) = _
  exact paperVariableArityRefinementClauseOffsetUnary_valid
    formula (physicalShiftedRowClauseRank formula row)
    hbound

private def physicalShiftedExpectedTableTypeRankWord :
    List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    (paperShiftedTupleConstantUnary 1)
    (fourFamilyComputedUnarySumOutput
      physicalShiftedExpectedLocalTypePrefixWord
      physicalShiftedRowTupleRankWord)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalShiftedExpectedTableTypeRankComputable :
    BitTM
      physicalShiftedExpectedTableTypeRankWord :=
  fourFamilyComputedUnarySumComputable
    (paperVariableArityShiftedTupleConstantUnaryComputable 1)
    (fourFamilyComputedUnarySumComputable
      paperVariableArityPhysicalShiftedExpectedLocalTypePrefixComputable
      paperVariableArityPhysicalShiftedRowTupleRankComputable)

private def physicalShiftedExpectedTableTypeRank
    (formula : ThreeCNF) (row : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) : ℕ :=
  1 + (physicalShiftedExpectedLocalTypePrefix formula row +
    physicalShiftedRowTupleRank formula row hbound)

private theorem paperVariableArityPhysicalShiftedExpectedTableTypeRankWord_query
    (formula : ThreeCNF) (row column : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) :
    physicalShiftedExpectedTableTypeRankWord
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalShiftedExpectedTableTypeRank
          formula row hbound) true := by
  let input := affineCellQuery row column
    (encodeThreeCNF formula)
  have predecessors :=
    paperVariableArityPhysicalShiftedExpectedLocalTypePrefixWord_query
      formula row column (Nat.le_of_lt hbound)
  have tuple := paperVariableArityPhysicalShiftedRowTupleRankWord_query
    formula row column hbound
  have localSum := fourFamilyComputedUnarySumOutput_valid
    physicalShiftedExpectedLocalTypePrefixWord
    physicalShiftedRowTupleRankWord input
    (physicalShiftedExpectedLocalTypePrefix formula row)
    (physicalShiftedRowTupleRank formula row hbound)
    predecessors tuple
  unfold physicalShiftedExpectedTableTypeRankWord
    physicalShiftedExpectedTableTypeRank
  exact fourFamilyComputedUnarySumOutput_valid
    (paperShiftedTupleConstantUnary 1)
    (fourFamilyComputedUnarySumOutput
      physicalShiftedExpectedLocalTypePrefixWord
      physicalShiftedRowTupleRankWord)
    input 1
    (physicalShiftedExpectedLocalTypePrefix formula row +
      physicalShiftedRowTupleRank formula row hbound)
    rfl localSum

private noncomputable def physicalShiftedExpectedTableTypeRankComputer :
    SourcePhysicalLagrangeWordComputer where
  output := physicalShiftedExpectedTableTypeRankWord
  computer := paperVariableArityPhysicalShiftedExpectedTableTypeRankComputable

private theorem paperVariableArityPhysicalShiftedExpectedTableTypeRankComputer_query
    (formula : ThreeCNF) (row column : ℕ)
    (hbound : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) :
    physicalShiftedExpectedTableTypeRankComputer.output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalShiftedExpectedTableTypeRank
          formula row hbound) true := by
  dsimp only [physicalShiftedExpectedTableTypeRankComputer]
  exact paperVariableArityPhysicalShiftedExpectedTableTypeRankWord_query
    formula row column hbound

end PhysicalShiftedExpectedTypeRankTM

namespace PhysicalShiftedInterpolationBaseCorrectness

open Turing GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldBasis
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryCompactPhysicalFieldWordXorTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.PhysicalOrdinaryShiftedCoefficientTM
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine
open GapCVP.ShiftedTupleBetaTM GapCVP.ShiftedTupleBetaSourceCorrectness
open GapCVP.ShiftedTupleBetaSourceFieldCorrectness
open GapCVP.ShiftedTupleAnchorSourceFieldCorrectness GapCVP.PhysicalShiftedInterpolationBaseTM

private theorem paperVariableArityPhysicalShiftedColumnValueComputer_output
    (input : List Bool) :
    physicalShiftedColumnValueComputer.output input =
      physicalShiftedColumnValueWord input := by
  dsimp only [physicalShiftedColumnValueComputer]

private theorem paperVariableArityPhysicalShiftedColumnGridComputer_output
    (input : List Bool) :
    physicalShiftedColumnGridComputer.output input =
      physicalShiftedColumnGridWord input := by
  dsimp only [physicalShiftedColumnGridComputer]

private theorem paperVariableArityPhysicalShiftedBetaComputer_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF) (bit : Bool)
    (correctBit : paperShiftedTupleBetaBit ranks
      (affineCellQuery row column
        (encodeThreeCNF formula)) = [bit]) :
    (paperShiftedTupleBetaFieldComputer ranks).output
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      finiteWordBits
        (indexedWord
          (sourceIrreducibleFormulaDegree formula)
          (paperShiftedTupleBetaFieldIndex formula bit)) := by
  rw [paperVariableArityShiftedTupleBetaFieldComputer_output]
  exact paperVariableArityShiftedTupleBetaFieldWord_valid
    ranks row column formula bit correctBit

private theorem paperVariableArityPhysicalShiftedInterpolationNumeratorComputer_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF) (bit : Bool)
    (correctBit : paperShiftedTupleBetaBit ranks
      (affineCellQuery row column
        (encodeThreeCNF formula)) = [bit]) :
    (physicalShiftedInterpolationNumeratorComputer
      ranks).output
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      finiteWordBits
        (compactPhysicalFieldWordXorValue
          (physicalShiftedColumnValueSourceWord
            formula column)
          (indexedWord
            (sourceIrreducibleFormulaDegree formula)
            (paperShiftedTupleBetaFieldIndex formula bit))) := by
  simp only [physicalShiftedInterpolationNumeratorComputer,
    paperVariableArityPhysicalInterpolationDifferenceComputer]
  apply paperVariableArityPhysicalInterpolationDifferenceWord_valid
    physicalShiftedColumnValueComputer
    (paperShiftedTupleBetaFieldComputer ranks)
    row column formula
  · rw [paperVariableArityPhysicalShiftedColumnValueComputer_output]
    exact paperVariableArityPhysicalShiftedColumnValueWord_valid
      row column formula
  · exact paperVariableArityPhysicalShiftedBetaComputer_valid
      ranks row column formula bit correctBit

private theorem paperVariableArityPhysicalShiftedAnchorComputer_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (bounded : rank < (noTautClauses formula).length)
    (correctRank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true)
    (position : ℕ)
    (validPosition : position <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, bounded⟩)).length)
    (correctPosition : ranks.variablePosition.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate position true) :
    (paperShiftedTupleRetainedAnchorFieldComputer ranks).output
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      finiteWordBits
        (paperShiftedTupleSelectedSourceVariableWord
          formula rank bounded position validPosition) := by
  change paperShiftedTupleRetainedAnchorFieldWord ranks
    (affineCellQuery row column
      (encodeThreeCNF formula)) = _
  exact paperVariableArityShiftedTupleRetainedAnchorFieldWord_query
    ranks row column formula rank bounded correctRank
    position validPosition correctPosition

private theorem paperVariableArityPhysicalShiftedInterpolationDenominatorComputer_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (bounded : rank < (noTautClauses formula).length)
    (correctRank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true)
    (position : ℕ)
    (validPosition : position <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, bounded⟩)).length)
    (correctPosition : ranks.variablePosition.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate position true) :
    (paperVariableArityPhysicalShiftedInterpolationDenominatorComputer
      ranks).output
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      finiteWordBits
        (compactPhysicalFieldWordXorValue
          (physicalShiftedColumnGridSourceWord
            formula column)
          (paperShiftedTupleSelectedSourceVariableWord
            formula rank bounded position validPosition)) := by
  simp only [paperVariableArityPhysicalShiftedInterpolationDenominatorComputer,
    paperVariableArityPhysicalInterpolationDifferenceComputer]
  apply paperVariableArityPhysicalInterpolationDifferenceWord_valid
    physicalShiftedColumnGridComputer
    (paperShiftedTupleRetainedAnchorFieldComputer ranks)
    row column formula
  · rw [paperVariableArityPhysicalShiftedColumnGridComputer_output]
    exact paperVariableArityPhysicalShiftedColumnGridWord_valid
      row column formula
  · exact paperVariableArityPhysicalShiftedAnchorComputer_valid
      ranks row column formula rank bounded correctRank
      position validPosition correctPosition

private theorem paperVariableArityPhysicalShiftedInterpolationDenominatorInverse_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (bounded : rank < (noTautClauses formula).length)
    (correctRank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true)
    (position : ℕ)
    (validPosition : position <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, bounded⟩)).length)
    (correctPosition : ranks.variablePosition.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate position true) :
    (paperVariableArityPhysicalCellInverseComputer
      (paperVariableArityPhysicalShiftedInterpolationDenominatorComputer
        ranks)).output
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      finiteWordBits
        (sourceInverseWord
          (compactPhysicalFieldWordXorValue
            (physicalShiftedColumnGridSourceWord
              formula column)
            (paperShiftedTupleSelectedSourceVariableWord
              formula rank bounded position validPosition))) := by
  change physicalCellInverseWord
    (paperVariableArityPhysicalShiftedInterpolationDenominatorComputer
      ranks)
    (affineCellQuery row column
      (encodeThreeCNF formula)) = _
  apply paperVariableArityPhysicalCellInverseWord_valid
    (paperVariableArityPhysicalShiftedInterpolationDenominatorComputer
      ranks)
    row column formula
  exact paperVariableArityPhysicalShiftedInterpolationDenominatorComputer_valid
    ranks row column formula rank bounded correctRank
    position validPosition correctPosition

private theorem paperVariableArityPhysicalShiftedInterpolationBaseWord_valid
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (row column : ℕ) (formula : ThreeCNF)
    (rank : ℕ)
    (bounded : rank < (noTautClauses formula).length)
    (correctRank : ranks.clause.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate rank true)
    (position : ℕ)
    (validPosition : position <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, bounded⟩)).length)
    (correctPosition : ranks.variablePosition.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = List.replicate position true)
    (bit : Bool)
    (correctBit : paperShiftedTupleBetaBit ranks
      (affineCellQuery row column
        (encodeThreeCNF formula)) = [bit]) :
    physicalShiftedInterpolationBaseWord ranks
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
      finiteWordBits
        (physicalShiftedInterpolationBaseSourceWord
          formula column rank bounded position validPosition bit) := by
  unfold physicalShiftedInterpolationBaseWord
    physicalShiftedInterpolationBaseSourceWord
  apply paperVariableArityPhysicalInterpolationProductWord_valid
    (physicalShiftedInterpolationNumeratorComputer ranks)
    (paperVariableArityPhysicalCellInverseComputer
      (paperVariableArityPhysicalShiftedInterpolationDenominatorComputer
        ranks))
    row column formula
  · exact paperVariableArityPhysicalShiftedInterpolationNumeratorComputer_valid
      ranks row column formula bit correctBit
  · exact paperVariableArityPhysicalShiftedInterpolationDenominatorInverse_valid
      ranks row column formula rank bounded correctRank
      position validPosition correctPosition

end PhysicalShiftedInterpolationBaseCorrectness

namespace PhysicalShiftedInterpolationBaseInstantiation

open Turing GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.PhysicalFamilyRowTM GapCVP.ShiftedTupleBetaTM
open GapCVP.ShiftedTupleBetaSourceCorrectness GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.PhysicalShiftedInterpolationBaseTM
open GapCVP.PhysicalShiftedInterpolationBaseCorrectness

private def physicalShiftedRowNormalizedSign
    (formula : ThreeCNF) (row : ℕ)
    (bounded : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length)
    (slot : Fin 3) : Bool :=
  (paperShiftedTuplePotentialNormalizedLiteral
    ((noTautClauses formula).get
      ⟨physicalShiftedRowClauseRank formula row,
        bounded⟩) slot).2

private def physicalShiftedRowBetaBit
    (formula : ThreeCNF) (row : ℕ)
    (bounded : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) : Bool :=
  let tuple := physicalShiftedRowTupleRank
    formula row bounded
  let arity := physicalShiftedRowSelectedClauseArity
    formula row bounded
  let sign := physicalShiftedRowNormalizedSign
    formula row bounded
  let assignment := tuple +
    if tuple < paperShiftedTupleRejectedNatural arity sign
    then 0 else 1
  assignment.testBit
    (physicalShiftedRowVariablePosition
      formula row bounded)

private theorem paperVariableArityPhysicalShiftedRowBetaBit_query
    (formula : ThreeCNF) (row column : ℕ)
    (bounded : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) :
    paperShiftedTupleBetaBit
        physicalShiftedRowTupleRankComputers
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [physicalShiftedRowBetaBit
        formula row bounded] := by
  unfold physicalShiftedRowBetaBit
  apply paperVariableArityShiftedTupleBetaBit_valid
    physicalShiftedRowTupleRankComputers
    (affineCellQuery row column (encodeThreeCNF formula))
    (physicalShiftedRowSelectedClauseArity
      formula row bounded)
    (physicalShiftedRowTupleRank
      formula row bounded)
    (physicalShiftedRowVariablePosition
      formula row bounded)
    (physicalShiftedRowNormalizedSign
      formula row bounded)
  · exact paperVariableArityPhysicalShiftedRowVariablePosition_lt_three
      formula row bounded
  · simpa only [physicalShiftedRowSelectedClauseArity]
      using paperVariableArityShiftedTupleNormalizedArityUnary_query
        physicalShiftedRowTupleRankComputers
        row column formula
        (physicalShiftedRowClauseRank formula row)
        bounded
        (paperVariableArityPhysicalShiftedRowTupleRankComputers_clause_query
          formula row column)
  · intro slot
    exact paperVariableArityShiftedTupleNormalizedSignWord_potential_query
      physicalShiftedRowTupleRankComputers
      row column formula
      (physicalShiftedRowClauseRank formula row)
      bounded
      (paperVariableArityPhysicalShiftedRowTupleRankComputers_clause_query
        formula row column)
      slot
  · exact paperVariableArityPhysicalShiftedRowTupleRankComputers_tuple_query
      formula row column bounded
  · exact
      paperVariableArityPhysicalShiftedRowTupleRankComputers_variablePosition_query
        formula row column bounded

private theorem physicalShiftedRowVariablePosition_lt_normalized
    (formula : ThreeCNF) (row : ℕ)
    (bounded : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) :
    physicalShiftedRowVariablePosition
        formula row bounded <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨physicalShiftedRowClauseRank formula row,
            bounded⟩)).length := by
  exact paperVariableArityPhysicalShiftedRowVariablePosition_lt_arity
    formula row bounded

private def physicalShiftedCanonicalInterpolationBaseSourceWord
    (formula : ThreeCNF) (row column : ℕ)
    (bounded : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) :
    GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula) :=
  physicalShiftedInterpolationBaseSourceWord
    formula column
    (physicalShiftedRowClauseRank formula row)
    bounded
    (physicalShiftedRowVariablePosition
      formula row bounded)
    (physicalShiftedRowVariablePosition_lt_normalized
      formula row bounded)
    (physicalShiftedRowBetaBit formula row bounded)

private noncomputable def physicalShiftedCanonicalInterpolationBaseComputer :
    SourcePhysicalLagrangeWordComputer :=
  paperVariableArityPhysicalShiftedInterpolationBaseComputer
    physicalShiftedRowTupleRankComputers

private theorem paperVariableArityPhysicalShiftedCanonicalInterpolationBaseComputer_output
    (input : List Bool) :
    physicalShiftedCanonicalInterpolationBaseComputer.output
        input =
      physicalShiftedInterpolationBaseWord
        physicalShiftedRowTupleRankComputers input := by
  dsimp only [physicalShiftedCanonicalInterpolationBaseComputer,
    paperVariableArityPhysicalShiftedInterpolationBaseComputer]

private theorem paperVariableArityPhysicalShiftedCanonicalInterpolationBaseComputer_valid
    (formula : ThreeCNF) (row column : ℕ)
    (bounded : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) :
    physicalShiftedCanonicalInterpolationBaseComputer.output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      finiteWordBits
        (physicalShiftedCanonicalInterpolationBaseSourceWord
          formula row column bounded) := by
  rw [paperVariableArityPhysicalShiftedCanonicalInterpolationBaseComputer_output]
  unfold physicalShiftedCanonicalInterpolationBaseSourceWord
  exact paperVariableArityPhysicalShiftedInterpolationBaseWord_valid
    physicalShiftedRowTupleRankComputers
    row column formula
    (physicalShiftedRowClauseRank formula row)
    bounded
    (paperVariableArityPhysicalShiftedRowTupleRankComputers_clause_query
      formula row column)
    (physicalShiftedRowVariablePosition
      formula row bounded)
    (physicalShiftedRowVariablePosition_lt_normalized
      formula row bounded)
    (paperVariableArityPhysicalShiftedRowTupleRankComputers_variablePosition_query
      formula row column bounded)
    (physicalShiftedRowBetaBit formula row bounded)
    (paperVariableArityPhysicalShiftedRowBetaBit_query
      formula row column bounded)

end PhysicalShiftedInterpolationBaseInstantiation

open GapCVP.PhysicalShiftedInterpolationBaseInstantiation

namespace PhysicalOrdinaryShiftedCheckBitInstantiation

open Turing GapCVP.PhysicalFamilyMarkerTM GapCVP.PhysicalOrdinaryShiftedCoefficientSumTM
open GapCVP.PhysicalMaskedInterpolationNodeParityTM GapCVP.PhysicalShiftedExpectedTypeRankTM
open GapCVP.PhysicalShiftedInterpolationBaseInstantiation

/-- Internal support shared across GapCVP continuation modules. -/
def physicalShiftedCheckBit : List Bool → List Bool :=
  physicalSourceInterpolationFamilyCheckBit
    (3 : Fin 4)
    physicalShiftedRowMarker
    physicalShiftedExpectedTableTypeRankComputer
    (physicalShiftedNodePrefixWidth
      physicalShiftedInterpolationMomentComputer)
    physicalShiftedCanonicalInterpolationBaseComputer

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def paperVariableArityPhysicalShiftedCheckBitComputable :
    BitTM
      physicalShiftedCheckBit :=
  paperVariableArityPhysicalSourceInterpolationFamilyCheckBitComputable
    (3 : Fin 4)
    physicalShiftedRowMarker
    paperVariableArityPhysicalShiftedRowMarkerComputable
    physicalShiftedExpectedTableTypeRankComputer
    (physicalShiftedNodePrefixWidth
      physicalShiftedInterpolationMomentComputer)
    physicalShiftedCanonicalInterpolationBaseComputer

end PhysicalOrdinaryShiftedCheckBitInstantiation

namespace PhysicalShiftedRowTupleRankBounds

open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourceOrder
open GapCVP.ShiftedTupleTM GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalRefinementRowProjection
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalRowCountMachine
open GapCVP.SourceFieldMomentOperationsTM GapCVP.PhysicalShiftedRowTupleRankTM

private theorem paperVariableArityPhysicalShiftedRowWordCount_eq
    (formula : ThreeCNF) :
    paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula =
      physicalFormulaOrdinaryBoundary formula +
        (((paperShiftedSourceClauseWeightSum
            (noTautClauses formula) *
          physicalFormulaMomentCount formula) *
          physGridCard formula) *
          physDegree formula) := by
  rw [paperVariableArityExplicitBinaryRowWordCount_eq_fourFamily]

private theorem paperVariableArityPhysicalShiftedRowMixedTag_lt_of_row
    (formula : ThreeCNF) (row : ℕ)
    (hshifted : physicalFormulaOrdinaryBoundary formula ≤ row)
    (hrow : row < paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula) :
    physicalShiftedRowMixedTag formula row <
      paperShiftedSourceClauseWeightSum
        (noTautClauses formula) := by
  have upper :
      row < physicalFormulaOrdinaryBoundary formula +
        (((paperShiftedSourceClauseWeightSum
            (noTautClauses formula) *
          physicalFormulaMomentCount formula) *
          physGridCard formula) *
          physDegree formula) := by
    rw [← paperVariableArityPhysicalShiftedRowWordCount_eq]
    exact hrow
  have offset :
      row - physicalFormulaOrdinaryBoundary formula <
        (((paperShiftedSourceClauseWeightSum
            (noTautClauses formula) *
          physicalFormulaMomentCount formula) *
          physGridCard formula) *
          physDegree formula) := by
    omega
  unfold physicalShiftedRowMixedTag
  apply (Nat.div_lt_iff_lt_mul
    (physicalFormulaMomentCount_pos formula)).mpr
  apply (Nat.div_lt_iff_lt_mul
    (physicalRefinementGridCard_pos formula)).mpr
  apply (Nat.div_lt_iff_lt_mul
    (physicalRefinementDegree_pos formula)).mpr
  exact offset

private theorem paperVariableArityPhysicalShiftedRowAcceptedPrefixCount_le
    (formula : ThreeCNF) (row : ℕ) :
    physicalShiftedRowAcceptedPrefixCount formula row ≤
      (noTautClauses formula).length := by
  unfold physicalShiftedRowAcceptedPrefixCount
  have filtered := List.length_filter_le
    (fun rank => decide
      (physicalShiftedRowClausePrefix formula rank ≤
        physicalShiftedRowMixedTag formula row))
    (List.range (noTautClauses formula).length)
  simpa only [List.length_range] using filtered

private theorem paperVariableArityPhysicalShiftedRetainedClauseCount_pos_of_row
    (formula : ThreeCNF) (row : ℕ)
    (hshifted : physicalFormulaOrdinaryBoundary formula ≤ row)
    (hrow : row < paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula) :
    0 < (noTautClauses formula).length := by
  have mixed := paperVariableArityPhysicalShiftedRowMixedTag_lt_of_row
    formula row hshifted hrow
  by_contra notPositive
  have zero : (noTautClauses formula).length = 0 :=
    Nat.eq_zero_of_not_pos notPositive
  have empty : noTautClauses formula = [] :=
    List.length_eq_zero_iff.mp zero
  rw [empty] at mixed
  simp only [paperShiftedSourceClauseWeightSum, List.map_nil, List.sum_nil, not_lt_zero] at mixed

private theorem paperVariableArityPhysicalShiftedRowClauseRank_lt_of_row
    (formula : ThreeCNF) (row : ℕ)
    (hshifted : physicalFormulaOrdinaryBoundary formula ≤ row)
    (hrow : row < paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula) :
    physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length := by
  have positive :=
    paperVariableArityPhysicalShiftedRetainedClauseCount_pos_of_row
      formula row hshifted hrow
  have bounded := paperVariableArityPhysicalShiftedRowAcceptedPrefixCount_le
    formula row
  unfold physicalShiftedRowClauseRank
  omega

private theorem physicalShiftedRowClauseRank_lt_of_fin
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (hshifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    physicalShiftedRowClauseRank formula row.val <
      (noTautClauses formula).length :=
  paperVariableArityPhysicalShiftedRowClauseRank_lt_of_row
    formula row.val hshifted row.isLt

end PhysicalShiftedRowTupleRankBounds

namespace PhysicalOrdinaryShiftedCheckBitInstantiation

open Turing GapCVP.BinaryEncoding GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.PhysicalGlobalRefinementCoefficientTM GapCVP.PhysicalShiftedExpectedTypeRankTM
open GapCVP.PhysicalShiftedInterpolationBaseInstantiation GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.SourceOrder GapCVP.BinarySourceTautologyNormalizationExact

private theorem paperVariableArityPhysicalShiftedCheckBit_of_not_in_family
    (formula : ThreeCNF) (row column : ℕ)
    (outside : ¬
      physicalFormulaOrdinaryBoundary formula ≤ row) :
    physicalShiftedCheckBit
        (affineCellQuery row column
          (encodeThreeCNF formula)) = [false] := by
  let query := affineCellQuery row column
    (encodeThreeCNF formula)
  have rejected :
      physicalShiftedRowMarker query = [false] := by
    change physicalShiftedRowMarker
      (affineCellQuery row column
        (encodeThreeCNF formula)) = [false]
    rw [paperVariableArityPhysicalShiftedRowMarker_query]
    simp only [outside, decide_false]
  unfold physicalShiftedCheckBit
    physicalSourceInterpolationFamilyCheckBit
  change sourceFourFamilyBooleanAndPairWord
    (physicalShiftedRowMarker query ++ _) = [false]
  rw [rejected]
  rfl

private theorem paperVariableArityPhysicalShiftedCheckBase_on_physical_row
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (bounded : physicalShiftedRowClauseRank
      formula row.val < (noTautClauses formula).length) :
    physicalShiftedCanonicalInterpolationBaseComputer.output
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      finiteWordBits
        (physicalShiftedCanonicalInterpolationBaseSourceWord
          formula row.val column.val bounded) := by
  exact paperVariableArityPhysicalShiftedCanonicalInterpolationBaseComputer_valid
    formula row.val column.val bounded

private theorem paperVariableArityPhysicalShiftedExpectedTypeMatchBit_valid
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (bounded : physicalShiftedRowClauseRank
      formula row.val < (noTautClauses formula).length) :
    physicalInterpolationExpectedTypeMatchBit
        physicalShiftedExpectedTableTypeRankComputer
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        (physicalShiftedExpectedTableTypeRank
            formula row.val bounded =
          (column.val /
            physFieldCard formula) /
            physGridCard formula)] := by
  unfold physicalInterpolationExpectedTypeMatchBit
  exact physicalCoefficientUnaryEquality_valid
    physicalShiftedExpectedTableTypeRankComputer.output
    physicalColumnTypeRankUnary
    (affineCellQuery row.val column.val
      (encodeThreeCNF formula))
    (physicalShiftedExpectedTableTypeRank
      formula row.val bounded)
    ((column.val /
      physFieldCard formula) /
      physGridCard formula)
    (paperVariableArityPhysicalShiftedExpectedTableTypeRankComputer_query
      formula row.val column.val bounded)
    (paperVariableArityPhysicalColumnTypeRankUnary_query
      row.val column.val formula)

end PhysicalOrdinaryShiftedCheckBitInstantiation

namespace PhysicalShiftedInterpolationBaseSourceFieldCorrectness

open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryFieldBasis GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryCompactPhysicalFieldWordXorTM GapCVP.BinarySourceCoordinateOrder
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.FormulaBridge
open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine
open GapCVP.PhysicalLagrangeNodeProductAlgebra GapCVP.PhysicalLagrangeNodeDenominatorNonzero
open GapCVP.ShiftedTupleAnchorSourceFieldCorrectness
open GapCVP.ShiftedTupleBetaSourceFieldCorrectness GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.PhysicalShiftedInterpolationBaseTM
open GapCVP.PhysicalShiftedInterpolationBaseInstantiation

private theorem paperVariableArityPhysicalShiftedColumnGridSourceWord_eq_evaluationWord
    (formula : ThreeCNF) (column : ℕ) :
    physicalShiftedColumnGridSourceWord formula column =
      physicalLagrangeNodeEvaluationWord formula
        (physicalShiftedColumnGridIndex formula column) := by
  rfl

private theorem paperVariableArityPhysicalShiftedInterpolationDenominatorSourceValue_ne_zero
    (formula : ThreeCNF) (column rank : ℕ)
    (bounded : rank < (noTautClauses formula).length)
    (position : ℕ)
    (validPosition : position <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, bounded⟩)).length) :
    sourceWordValue (encodeThreeCNF formula).length
        (srcFormula formula)
        (compactPhysicalFieldWordXorValue
          (physicalShiftedColumnGridSourceWord
            formula column)
          (paperShiftedTupleSelectedSourceVariableWord
            formula rank bounded position validPosition)) ≠ 0 := by
  rw [compactPhysicalFieldWordXorValue_sourceWordValue_sub,
    paperVariableArityPhysicalShiftedColumnGridSourceWord_eq_evaluationWord,
    paperVariableArityShiftedTupleSelectedSourceVariableWord_sourceField]
  exact
    paperVariableArityPhysicalLagrangeNodeEvaluationSourceValue_sub_variableAnchor_ne_zero
      formula
      (physicalShiftedColumnGridIndex formula column)
      (paperShiftedTupleSelectedSourceVariableIndex
        formula rank bounded position validPosition)

private theorem paperVariableArityPhysicalShiftedInterpolationNumeratorSourceWord_sourceField
    (formula : ThreeCNF) (column : ℕ) (bit : Bool) :
    sourceWordValue (encodeThreeCNF formula).length
        (srcFormula formula)
        (compactPhysicalFieldWordXorValue
          (physicalShiftedColumnValueSourceWord
            formula column)
          (indexedWord
            (sourceIrreducibleFormulaDegree formula)
            (paperShiftedTupleBetaFieldIndex formula bit))) =
      sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedColumnValueSourceWord
            formula column) -
        sourceSATFieldBit
          (K := GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
            (encodeThreeCNF formula).length
            (srcFormula formula)) bit := by
  rw [compactPhysicalFieldWordXorValue_sourceWordValue_sub,
    paperVariableArityShiftedTupleBetaIndexedWord_sourceField]

private theorem paperVariableArityPhysicalShiftedInterpolationBaseSourceWord_sourceField
    (formula : ThreeCNF) (column rank : ℕ)
    (bounded : rank < (noTautClauses formula).length)
    (position : ℕ)
    (validPosition : position <
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          ⟨rank, bounded⟩)).length)
    (bit : Bool) :
    sourceWordValue (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalShiftedInterpolationBaseSourceWord
          formula column rank bounded position validPosition bit) =
      (sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedColumnValueSourceWord
            formula column) -
        sourceSATFieldBit
          (K := GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
            (encodeThreeCNF formula).length
            (srcFormula formula)) bit) /
        (sourceFormulaEvaluationWord
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedColumnGridIndex
            formula column) -
          GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
            (encodeThreeCNF formula).length
            (srcFormula formula)
            (paperShiftedTupleSelectedSourceVariableIndex
              formula rank bounded position validPosition)) := by
  unfold physicalShiftedInterpolationBaseSourceWord
  rw [sourceWordValue_multiplyMod,
    paperVariableArityPhysicalShiftedInterpolationNumeratorSourceWord_sourceField,
    sourceWordValue_sourceInverseWord
      (encodeThreeCNF formula).length
      (srcFormula formula)
      (compactPhysicalFieldWordXorValue
        (physicalShiftedColumnGridSourceWord
          formula column)
        (paperShiftedTupleSelectedSourceVariableWord
          formula rank bounded position validPosition))
      (paperVariableArityPhysicalShiftedInterpolationDenominatorSourceValue_ne_zero
        formula column rank bounded position validPosition),
    compactPhysicalFieldWordXorValue_sourceWordValue_sub,
    paperVariableArityPhysicalShiftedColumnGridSourceWord_eq_evaluationWord,
    physicalLagrangeNodeEvaluationWord_sourceField,
    paperVariableArityShiftedTupleSelectedSourceVariableWord_sourceField,
    div_eq_mul_inv]

theorem
    paperVariableArityPhysicalShiftedCanonicalInterpolationBaseSourceWord_sourceField
    (formula : ThreeCNF) (row column : ℕ)
    (bounded : physicalShiftedRowClauseRank formula row <
      (noTautClauses formula).length) :
    sourceWordValue (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalShiftedCanonicalInterpolationBaseSourceWord
          formula row column bounded) =
      (sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedColumnValueSourceWord
            formula column) -
        sourceSATFieldBit
          (K := GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
            (encodeThreeCNF formula).length
            (srcFormula formula))
          (physicalShiftedRowBetaBit
            formula row bounded)) /
        (sourceFormulaEvaluationWord
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedColumnGridIndex
            formula column) -
          GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
            (encodeThreeCNF formula).length
            (srcFormula formula)
            (paperShiftedTupleSelectedSourceVariableIndex
              formula
              (physicalShiftedRowClauseRank formula row)
              bounded
              (physicalShiftedRowVariablePosition
                formula row bounded)
              (physicalShiftedRowVariablePosition_lt_normalized
                formula row bounded))) := by
  unfold physicalShiftedCanonicalInterpolationBaseSourceWord
  exact paperVariableArityPhysicalShiftedInterpolationBaseSourceWord_sourceField
    formula column
    (physicalShiftedRowClauseRank formula row)
    bounded
    (physicalShiftedRowVariablePosition
      formula row bounded)
    (physicalShiftedRowVariablePosition_lt_normalized
      formula row bounded)
    (physicalShiftedRowBetaBit formula row bounded)

end PhysicalShiftedInterpolationBaseSourceFieldCorrectness

namespace PhysicalShiftedInterpolationParityFieldCorrectness

open scoped BigOperators

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryReedSolomonParity
open GapCVP.BinarySourceCoordinateOrder GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalLagrangeNodeProductAlgebra GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalInterpolationNodeWeightTM
open GapCVP.PhysicalInterpolationNodeWeightSourceFieldCorrectness
open GapCVP.PhysicalInterpolationNodeCountBounds GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation GapCVP.SourceFieldMomentOperationsTM

private theorem paperVariableArityPhysicalShiftedOrderedLagrangeParity_eq_selectedCorrection
    {K : Type*} [Field K]
    {gridCardinality degreeBound : ℕ}
    (points : Fin gridCardinality → K)
    (degreeBounded : degreeBound < gridCardinality)
    (row position : Fin gridCardinality) :
    constructiveParityMatrix points degreeBounded row position =
      (if row = position then (1 : K) else 0) -
        if selected : position.val < degreeBound + 1 then
          ∏ other ∈ (Finset.univ.erase
            (⟨position.val, selected⟩ : Fin (degreeBound + 1))),
              (points
                (Fin.castLE (Nat.succ_le_of_lt degreeBounded)
                  (⟨position.val, selected⟩ : Fin (degreeBound + 1))) -
               points (Fin.castLE (Nat.succ_le_of_lt degreeBounded) other))⁻¹ *
              (points row -
               points (Fin.castLE (Nat.succ_le_of_lt degreeBounded) other))
        else 0 :=
  paperVariableArityPhysicalOrderedLagrangeParity_eq_selectedCorrection
    points degreeBounded row position

private theorem paperVariableArityPhysicalShiftedOrderedLagrangeParity_mul
    {K : Type*} [Field K]
    {gridCardinality degreeBound : ℕ}
    (points : Fin gridCardinality → K)
    (degreeBounded : degreeBound < gridCardinality)
    (row position : Fin gridCardinality)
    (power : K) :
    constructiveParityMatrix points degreeBounded row position * power =
      (if row = position then power else 0) -
        if selected : position.val < degreeBound + 1 then
          (∏ other ∈ (Finset.univ.erase
            (⟨position.val, selected⟩ : Fin (degreeBound + 1))),
              (points row -
                points (Fin.castLE (Nat.succ_le_of_lt degreeBounded)
                  other))) *
          (∏ other ∈ (Finset.univ.erase
            (⟨position.val, selected⟩ : Fin (degreeBound + 1))),
              (points position -
                points (Fin.castLE (Nat.succ_le_of_lt degreeBounded)
                  other)))⁻¹ * power
        else 0 := by
  rw [paperVariableArityPhysicalShiftedOrderedLagrangeParity_eq_selectedCorrection,
    sub_mul]
  simp only [ite_mul, one_mul, zero_mul]
  by_cases selected : position.val < degreeBound + 1
  · simp only [dite_eq_left selected]
    have same :
        Fin.castLE (Nat.succ_le_of_lt degreeBounded)
            (⟨position.val, selected⟩ : Fin (degreeBound + 1)) = position := by
      apply Fin.ext
      rfl
    rw [same, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    ac_rfl
  · simp only [selected, ↓reduceDIte, zero_mul, sub_zero]

private abbrev physicalShiftedSourceInterpolationDegree
    (formula : ThreeCNF) (row : ℕ) : ℕ :=
  ((srcFormula formula).variableCount - 1) *
    physicalFamilyRowMoment (3 : Fin 4) row formula

private theorem paperVariableArityPhysicalShiftedInterpolationNodeCount_eq_sourceDegree
    (formula : ThreeCNF) (row : ℕ) :
    physicalShiftedInterpolationNodeCount row formula =
      physicalShiftedSourceInterpolationDegree
        formula row + 1 := by
  unfold physicalShiftedInterpolationNodeCount
  change
    (paperVariableArityVariableCount formula - 1) *
        physicalFamilyRowMoment (3 : Fin 4) row formula + 1 =
      ((srcFormula formula).variableCount - 1) *
        physicalFamilyRowMoment (3 : Fin 4) row formula + 1
  rw [paperVariableAritySourceFormula_variableCount]

private theorem physicalShiftedSourceInterpolationDegree_lt_grid
    (formula : ThreeCNF) (row : ℕ) :
    physicalShiftedSourceInterpolationDegree formula row <
      2 ^ physDegree formula -
        (srcFormula formula).variableCount := by
  have bounded := physicalShiftedInterpolationNodeCount_le_grid
    formula row
  rw [paperVariableArityPhysicalShiftedInterpolationNodeCount_eq_sourceDegree]
    at bounded
  exact Nat.lt_of_succ_le bounded

private noncomputable def physicalShiftedSourceGridPoints
    (formula : ThreeCNF) :
    PaperVariableArityPhysicalLagrangeNodeGridIndex formula →
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
        (encodeThreeCNF formula).length
        (srcFormula formula) :=
  sourceFormulaEvaluationWord (encodeThreeCNF formula).length
    (srcFormula formula)

private theorem paperVariableArityPhysicalShiftedLagrangeParity_mul_eq_selectedNodeWeight
    (formula : ThreeCNF) (row : ℕ)
    (position : PaperVariableArityPhysicalLagrangeNodeGridIndex formula)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula)) :
    constructiveParityMatrix
        (physicalShiftedSourceGridPoints formula)
        (physicalShiftedSourceInterpolationDegree_lt_grid
          formula row)
        (physicalInterpolationFamilyRowGridPosition
          (3 : Fin 4) row formula)
        position *
      sourceWordValue (encodeThreeCNF formula).length
        (srcFormula formula) value ^
          physicalFamilyRowMoment
            (3 : Fin 4) row formula =
      (if physicalInterpolationFamilyRowGridPosition
          (3 : Fin 4) row formula = position
        then sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula) value ^
            physicalFamilyRowMoment
              (3 : Fin 4) row formula
        else 0) -
        if selected : position.val <
          physicalShiftedSourceInterpolationDegree
            formula row + 1 then
          sourceWordValue (encodeThreeCNF formula).length
            (srcFormula formula)
            (physicalInterpolationNodeWeightSourceWord
              (3 : Fin 4) row formula
              (physicalShiftedSourceInterpolationDegree
                formula row + 1)
              (Nat.succ_le_of_lt
                (physicalShiftedSourceInterpolationDegree_lt_grid
                  formula row))
              ⟨position.val, selected⟩ value)
        else 0 := by
  rw [paperVariableArityPhysicalShiftedOrderedLagrangeParity_mul]
  by_cases selected : position.val <
      physicalShiftedSourceInterpolationDegree
        formula row + 1
  · simp only [dite_eq_left selected]
    rw [paperVariableArityPhysicalInterpolationNodeWeightSourceWord_sourceField]
    have same :
        Fin.castLE
            (Nat.succ_le_of_lt
              (physicalShiftedSourceInterpolationDegree_lt_grid
                formula row))
            (⟨position.val, selected⟩ : Fin
              (physicalShiftedSourceInterpolationDegree
                formula row + 1)) = position := by
      apply Fin.ext
      rfl
    simp only [physicalShiftedSourceGridPoints]
    rw [same]
  · simp only [dite_eq_right selected]

private theorem paperVariableArityPhysicalShiftedMaskedNodeSum_eq_selected
    {K : Type*} [AddCommMonoid K]
    (count grid : ℕ) (value : ℕ → K) :
    (((List.range count).map (fun node =>
      if node = grid then value node else 0)).sum) =
      if grid < count then value grid else 0 := by
  change (∑ node ∈ Finset.range count,
    if node = grid then value node else 0) = _
  simp only [Finset.sum_ite_eq', Finset.mem_range]

private theorem paperVariableArityPhysicalShiftedMaskedSourceNodeWeightSum_eq_selected
    (formula : ThreeCNF) (row column : ℕ)
    (value : GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula)) :
    (((List.range
      (physicalShiftedInterpolationNodeCount row formula)).map
        (fun node =>
          if node =
              (column /
                physFieldCard formula) %
                  physGridCard formula
          then
            sourceWordValue (encodeThreeCNF formula).length
              (srcFormula formula)
              (physicalInterpolationNodeSourceWord
                (3 : Fin 4) row formula
                (physicalShiftedInterpolationNodeCount
                  row formula)
                (physicalShiftedInterpolationNodeCount_le_grid
                  formula row)
                value node)
          else 0)).sum) =
      if selected :
        (column /
          physFieldCard formula) %
            physGridCard formula <
              physicalShiftedInterpolationNodeCount
                row formula
      then
        sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalInterpolationNodeWeightSourceWord
            (3 : Fin 4) row formula
            (physicalShiftedInterpolationNodeCount
              row formula)
            (physicalShiftedInterpolationNodeCount_le_grid
              formula row)
            ⟨(column /
              physFieldCard formula) %
                physGridCard formula,
              selected⟩ value)
      else 0 := by
  rw [paperVariableArityPhysicalShiftedMaskedNodeSum_eq_selected]
  split_ifs with selected
  · simp only [physicalInterpolationNodeSourceWord,
      dite_eq_left selected]
  · rfl

end PhysicalShiftedInterpolationParityFieldCorrectness

namespace PhysicalShiftedInterpolationRowSourceProjection

open scoped BigOperators

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.FormulaBridge
open GapCVP.SourceOrder GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalRefinementRowProjection GapCVP.PhysicalRowOrderProjection
open GapCVP.PhysicalInterpolationRowFamilyProjection

private theorem paperVariableArityPhysicalShiftedSourceInterpolationBlockWidth_pos
    (formula : ThreeCNF) :
    0 < physicalInterpolationBlockWidth formula :=
  Nat.mul_pos
    (physicalRefinementGridCard_pos formula)
    (physicalRefinementDegree_pos formula)

private def physicalShiftedSourceRowFamilyCoordinate
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    Fin (physicalShiftedInterpolationTagCount formula) := by
  refine
    ⟨(row.val - physicalFormulaOrdinaryBoundary formula) /
      physicalInterpolationBlockWidth formula, ?_⟩
  apply (Nat.div_lt_iff_lt_mul
    (paperVariableArityPhysicalShiftedSourceInterpolationBlockWidth_pos
      formula)).mpr
  have actualUpper :
      row.val < physicalFormulaOrdinaryBoundary formula +
        physicalShiftedInterpolationTagCount formula *
          physicalInterpolationBlockWidth formula := by
    calc
      row.val < paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula := row.isLt
      _ = physicalFormulaOrdinaryBoundary formula +
          physicalShiftedInterpolationTagCount formula *
            physicalInterpolationBlockWidth formula :=
        paperVariableArityPhysicalInterpolationRowCount_eq formula
  omega

private theorem paperVariableArityPhysicalShiftedSourceRowDecodedFamilyIndex
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    physicalRowDependentFamilyIndex
        (encodeThreeCNF formula).length formula row =
      physicalShiftedDependentFamilyIndex formula
        (physicalShiftedSourceRowFamilyCoordinate
          formula row inShifted) := by
  apply (paperVariableArityPhysicalSigmaFamilyIndex_eq_iff
    (paperExplicitBinaryFamilyBlockCount
      (encodeThreeCNF formula).length formula) row _).mpr
  rw [paperVariableArityPhysicalShiftedDependentFamilyPrefix,
    paperVariableArityPhysicalShiftedDependentFamilyBlockCount]
  let width := physicalInterpolationBlockWidth formula
  let offset := row.val - physicalFormulaOrdinaryBoundary formula
  have positive : 0 < width :=
    paperVariableArityPhysicalShiftedSourceInterpolationBlockWidth_pos formula
  have lower := Nat.div_mul_le_self offset width
  have upper := Nat.lt_div_mul_add positive (a := offset)
  have restore : offset + physicalFormulaOrdinaryBoundary formula = row.val :=
    Nat.sub_add_cancel inShifted
  change physicalFormulaOrdinaryBoundary formula +
      (offset / width) * width ≤ row.val ∧
    row.val < physicalFormulaOrdinaryBoundary formula +
      (offset / width) * width + width
  omega

private def physicalShiftedSourceRowClauseTupleVariableMoment
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    (Σ clause : Fin (srcFormula formula).clauses.length,
      Σ _tuple :
        ((srcFormula formula).clauses.get clause).SatisfyingLocalTuple,
      ((srcFormula formula).clauses.get clause).LocalVariable ×
        Fin (physicalInterpolationMomentBudget formula + 1)) :=
  paperShiftedFamilyWordOrder formula
    (physicalInterpolationMomentBudget formula)
    (physicalShiftedSourceRowFamilyCoordinate
      formula row inShifted)

private theorem paperVariableArityPhysicalShiftedSourceRowDecodedFamily
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    (physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row).1 =
      .inr (.inr (.inr
        (physicalShiftedSourceRowClauseTupleVariableMoment
          formula row inShifted))) := by
  rw [physicalRowOrder_family]
  rw [paperVariableArityPhysicalShiftedSourceRowDecodedFamilyIndex
    formula row inShifted]
  rw [paperVariableArityPhysicalShiftedDependentFamilyWordOrder]
  rfl

private def physicalShiftedSourceRowGrid
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    Fin (Fintype.card
      (ExplicitGridPoint (encodeThreeCNF formula).length
        (srcFormula formula))) := by
  let decoded := physicalWordDecodedRow
    (encodeThreeCNF formula).length formula row
  refine ⟨decoded.2.1.val, ?_⟩
  have bounded := decoded.2.1.isLt
  have family := paperVariableArityPhysicalShiftedSourceRowDecodedFamily
    formula row inShifted
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

end PhysicalShiftedInterpolationRowSourceProjection

namespace PhysicalShiftedInterpolationParityMaskedFieldCorrectness

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryReedSolomonParity
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.FormulaBridge GapCVP.SourceOrder
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalInterpolationNodeCountBounds GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.PhysicalShiftedRowTupleRankBounds
open GapCVP.PhysicalShiftedInterpolationBaseInstantiation
open GapCVP.PhysicalShiftedInterpolationBaseTM
open GapCVP.PhysicalShiftedInterpolationParityFieldCorrectness
open GapCVP.SourceFieldMomentOperationsTM

private noncomputable def physicalShiftedFiniteRowCanonicalBaseSourceWord
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (sourceFormulaDimension (encodeThreeCNF formula).length
        (srcFormula formula)))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    GapCVP.Core.EffectiveBinaryField.Word
      (physDegree formula) :=
  physicalShiftedCanonicalInterpolationBaseSourceWord
    formula row.val column.val
    (physicalShiftedRowClauseRank_lt_of_fin
      formula row inShifted)

private theorem paperVariableArityPhysicalShiftedFiniteRowParity_eq_maskedSourceCorrection
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (sourceFormulaDimension (encodeThreeCNF formula).length
        (srcFormula formula)))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    constructiveParityMatrix
        (physicalShiftedSourceGridPoints formula)
        (physicalShiftedSourceInterpolationDegree_lt_grid
          formula row.val)
        (physicalInterpolationFamilyRowGridPosition
          (3 : Fin 4) row.val formula)
        (physicalShiftedColumnGridIndex
          formula column.val) *
      sourceWordValue (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalShiftedFiniteRowCanonicalBaseSourceWord
          formula row column inShifted) ^
        physicalFamilyRowMoment
          (3 : Fin 4) row.val formula =
      (if physicalInterpolationFamilyRowGridPosition
          (3 : Fin 4) row.val formula =
          physicalShiftedColumnGridIndex
            formula column.val
        then sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedFiniteRowCanonicalBaseSourceWord
            formula row column inShifted) ^
            physicalFamilyRowMoment
              (3 : Fin 4) row.val formula
        else 0) -
      (((List.range
        (physicalShiftedInterpolationNodeCount
          row.val formula)).map
          (fun node =>
            if node =
                (column.val /
                  physFieldCard formula) %
                    physGridCard formula
            then
              sourceWordValue (encodeThreeCNF formula).length
                (srcFormula formula)
                (physicalInterpolationNodeSourceWord
                  (3 : Fin 4) row.val formula
                  (physicalShiftedInterpolationNodeCount
                    row.val formula)
                  (physicalShiftedInterpolationNodeCount_le_grid
                    formula row.val)
                  (physicalShiftedFiniteRowCanonicalBaseSourceWord
                    formula row column inShifted)
                  node)
            else 0)).sum) := by
  rw [paperVariableArityPhysicalShiftedMaskedSourceNodeWeightSum_eq_selected]
  have parity :=
    paperVariableArityPhysicalShiftedLagrangeParity_mul_eq_selectedNodeWeight
      formula row.val
      (physicalShiftedColumnGridIndex
        formula column.val)
      (physicalShiftedFiniteRowCanonicalBaseSourceWord
        formula row column inShifted)
  have nodeCount :=
    paperVariableArityPhysicalShiftedInterpolationNodeCount_eq_sourceDegree
      formula row.val
  cases nodeCount
  exact parity

end PhysicalShiftedInterpolationParityMaskedFieldCorrectness

namespace PhysicalShiftedInterpolationRowFieldCorrectness

open scoped BigOperators

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryReedSolomonParity
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalRowOrderProjection
open GapCVP.PhysicalInterpolationRowFamilyProjection
open GapCVP.PhysicalSelectedInterpolationCoefficientProjection
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection

private def physicalShiftedSourceRowClause
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    Fin (srcFormula formula).clauses.length :=
  (physicalShiftedSourceRowClauseTupleVariableMoment
    formula row inShifted).1

private def physicalShiftedSourceRowTuple
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    ((srcFormula formula).clauses.get
      (physicalShiftedSourceRowClause
        formula row inShifted)).SatisfyingLocalTuple :=
  (physicalShiftedSourceRowClauseTupleVariableMoment
    formula row inShifted).2.1

private def physicalShiftedSourceRowLocalVariable
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    ((srcFormula formula).clauses.get
      (physicalShiftedSourceRowClause
        formula row inShifted)).LocalVariable :=
  (physicalShiftedSourceRowClauseTupleVariableMoment
    formula row inShifted).2.2.1

private def physicalShiftedSourceRowMoment
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    Fin (physicalInterpolationMomentBudget formula + 1) :=
  (physicalShiftedSourceRowClauseTupleVariableMoment
    formula row inShifted).2.2.2

private theorem paperVariableArityPhysicalShiftedSourceRowDecodedFamily_components
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    (physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row).1 =
      .inr (.inr (.inr
        ⟨physicalShiftedSourceRowClause
            formula row inShifted,
          physicalShiftedSourceRowTuple
            formula row inShifted,
          physicalShiftedSourceRowLocalVariable
            formula row inShifted,
          physicalShiftedSourceRowMoment
            formula row inShifted⟩)) := by
  exact paperVariableArityPhysicalShiftedSourceRowDecodedFamily
    formula row inShifted

private theorem paperVariableArityPhysicalShiftedSourceRowDependentBlockRank
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    (physicalRowDependentBlockRank
      (encodeThreeCNF formula).length formula row).val =
      (row.val - physicalFormulaOrdinaryBoundary formula) %
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
    (paperVariableArityPhysicalShiftedSourceRowDecodedFamilyIndex formula row inShifted)
  rw [paperVariableArityPhysicalShiftedDependentFamilyPrefix] at prefixEquality
  rw [prefixEquality] at rank
  let width := physicalInterpolationBlockWidth formula
  let offset := row.val - physicalFormulaOrdinaryBoundary formula
  change row.val = physicalFormulaOrdinaryBoundary formula +
    (offset / width) * width +
      (physicalRowDependentBlockRank
        (encodeThreeCNF formula).length formula row).val at rank
  have decomposition := Nat.mod_add_div' offset width
  have restore : offset + physicalFormulaOrdinaryBoundary formula = row.val :=
    Nat.sub_add_cancel inShifted
  change (physicalRowDependentBlockRank
    (encodeThreeCNF formula).length formula row).val = offset % width
  omega

private theorem paperVariableArityPhysicalShiftedSourceRowGrid_val
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    (physicalShiftedSourceRowGrid
      formula row inShifted).val =
      ((row.val - physicalFormulaOrdinaryBoundary formula) /
        physDegree formula) %
          physGridCard formula := by
  change
    (physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row).2.1.val = _
  rw [physicalRowOrder_fieldRow,
    paperVariableArityPhysicalShiftedSourceRowDependentBlockRank
      formula row inShifted]
  change
    ((row.val - physicalFormulaOrdinaryBoundary formula) %
      (physGridCard formula *
        physDegree formula)) /
        physDegree formula = _
  exact Nat.mod_mul_left_div_self
    (row.val - physicalFormulaOrdinaryBoundary formula)
    (physDegree formula)
    (physGridCard formula)

private theorem paperVariableArityPhysicalShiftedSourceRowBasis_val
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula)) :
    (physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row).2.2.val =
      row.val % physDegree formula := by
  exact physicalRowOrder_basis_val
    (encodeThreeCNF formula).length formula row

private theorem paperVariableArityPhysicalShiftedSourceRowFieldCoefficient_eq_selected
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    physicalWordFamilyFieldCoefficient
        (encodeThreeCNF formula).length formula
        (physicalWordDecodedRow
          (encodeThreeCNF formula).length formula row).1
        (physicalWordDecodedRow
          (encodeThreeCNF formula).length formula row).2.1
        column =
      if (Sum.inr
          ⟨physicalShiftedSourceRowClause
              formula row inShifted,
            physicalShiftedSourceRowTuple
              formula row inShifted⟩ :
          sourceSATTableType (srcFormula formula)) =
        (sourceCoordinateWordOrder
          (encodeThreeCNF formula).length formula column).1
      then
        constructiveParityMatrix
          (fun index =>
            (sourceFormulaExplicitGridOrder
              (encodeThreeCNF formula).length
              (srcFormula formula) index).val)
          (explicitShiftedDegree_lt_grid
            (encodeThreeCNF formula).length
            (srcFormula formula)
            (physicalShiftedSourceRowMoment
              formula row inShifted))
          (physicalShiftedSourceRowGrid
            formula row inShifted)
          ((sourceFormulaExplicitGridOrder
            (encodeThreeCNF formula).length
            (srcFormula formula)).symm
              (sourceCoordinateWordOrder
                (encodeThreeCNF formula).length formula column).2.1) *
          (((sourceCoordinateWordOrder
              (encodeThreeCNF formula).length formula column).2.2 -
            sourceSATFieldBit
              (K := PaperVariableArityPhysicalWordField
                (encodeThreeCNF formula).length formula)
              ((physicalShiftedSourceRowTuple
                formula row inShifted).val
                (physicalShiftedSourceRowLocalVariable
                  formula row inShifted))) /
            ((sourceCoordinateWordOrder
                (encodeThreeCNF formula).length formula column).2.1.val -
              GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
                (encodeThreeCNF formula).length
                (srcFormula formula)
                (physicalShiftedSourceRowLocalVariable
                  formula row inShifted).val)) ^
            (physicalShiftedSourceRowMoment
              formula row inShifted).val
      else 0 := by
  let clause := physicalShiftedSourceRowClause
    formula row inShifted
  let tuple := physicalShiftedSourceRowTuple
    formula row inShifted
  let omitted := physicalShiftedSourceRowLocalVariable
    formula row inShifted
  let moment := physicalShiftedSourceRowMoment
    formula row inShifted
  let grid := physicalShiftedSourceRowGrid
    formula row inShifted
  have family := paperVariableArityPhysicalShiftedSourceRowDecodedFamily_components
    formula row inShifted
  have selected :=
    paperVariableArityPhysicalWordShiftedFieldCoefficient_eq_selectedCoordinate
      (encodeThreeCNF formula).length formula
      clause tuple omitted moment grid column
  generalize decodedEquality :
    physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row = decoded
    at family ⊢
  rcases decoded with ⟨decodedFamily, decodedRow, decodedBasis⟩
  have exactFamily : decodedFamily =
      .inr (.inr (.inr ⟨clause, tuple, omitted, moment⟩)) := family
  subst decodedFamily
  have exactGrid : decodedRow = grid := by
    apply Fin.ext
    change decodedRow.val = grid.val
    change decodedRow.val =
      (physicalWordDecodedRow
        (encodeThreeCNF formula).length formula row).2.1.val
    exact (congrArg (fun value => value.2.1.val)
      decodedEquality).symm
  subst decodedRow
  exact selected

end PhysicalShiftedInterpolationRowFieldCorrectness

namespace PhysicalShiftedInterpolationRowDigitCorrectness

open scoped BigOperators

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.SourceFieldMomentOperationsTM GapCVP.PhysicalLagrangeNodeProductAlgebra
open GapCVP.PhysicalInterpolationNodeFactorTM GapCVP.PhysicalInterpolationNodeCountBounds
open GapCVP.PhysicalInterpolationRowFamilyProjection
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness

private theorem paperVariableArityPhysicalShiftedSourceRowGrid_val_eq_family
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    (physicalShiftedSourceRowGrid
      formula row inShifted).val =
      (physicalInterpolationFamilyRowGridPosition
        (3 : Fin 4) row.val formula).val := by
  rw [paperVariableArityPhysicalShiftedSourceRowGrid_val
    formula row inShifted]
  change
    ((row.val - physicalFormulaOrdinaryBoundary formula) /
      physDegree formula) %
      physGridCard formula =
    ((row.val - physicalFamilyStart (3 : Fin 4) formula) /
      physDegree formula) %
      physGridCard formula
  simp only [physicalFamilyStart, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
      OfNat.ofNat_ne_zero,
      ↓reduceIte, OfNat.ofNat_ne_one, OfNat.ofNat_eq_ofNat, Nat.succ_ne_self]

private def paperVariableArityPhysicalShiftedSourceRowNodeGrid
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    PaperVariableArityPhysicalLagrangeNodeGridIndex formula := by
  refine ⟨(physicalShiftedSourceRowGrid
    formula row inShifted).val, ?_⟩
  have bounded := (physicalShiftedSourceRowGrid
    formula row inShifted).isLt
  exact lt_of_lt_of_eq bounded
    (physicalInterpolationExplicitGridCardinality_eq
      formula)

private theorem paperVariableArityPhysicalShiftedSourceRowNodeGrid_eq_family
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    paperVariableArityPhysicalShiftedSourceRowNodeGrid
        formula row inShifted =
      physicalInterpolationFamilyRowGridPosition
        (3 : Fin 4) row.val formula := by
  apply Fin.ext
  exact paperVariableArityPhysicalShiftedSourceRowGrid_val_eq_family
    formula row inShifted

private theorem paperVariableArityPhysicalShiftedClauseWordMoment_val
    (formula : ThreeCNF) (budget : ℕ)
    (clause : Fin (srcFormula formula).clauses.length)
    (tag : Fin (paperShiftedClauseTagCount
      formula budget clause)) :
    ((paperShiftedClauseWordOrder
      formula budget clause tag).2.2).val = tag.val % (budget + 1) := by
  change
    (tag.val %
      (paperFormulaClauseWidth formula clause * (budget + 1))) %
        (budget + 1) = tag.val % (budget + 1)
  exact Nat.mod_mod_of_dvd tag.val
    (dvd_mul_left (budget + 1)
      (paperFormulaClauseWidth formula clause))

private theorem paperVariableArityPhysicalShiftedClauseTagCount_moment_dvd
    (formula : ThreeCNF) (budget : ℕ)
    (clause : Fin (srcFormula formula).clauses.length) :
    budget + 1 ∣ paperShiftedClauseTagCount
      formula budget clause := by
  refine ⟨(2 ^ paperFormulaClauseWidth formula clause - 1) *
    paperFormulaClauseWidth formula clause, ?_⟩
  unfold paperShiftedClauseTagCount
  ring

private theorem paperVariableArityPhysicalShiftedSourceRowMoment_val
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    (physicalShiftedSourceRowMoment
      formula row inShifted).val =
      (((row.val - physicalFormulaOrdinaryBoundary formula) /
        physDegree formula) /
        physGridCard formula) %
        physicalFormulaMomentCount formula := by
  let budget := physicalInterpolationMomentBudget formula
  let tag := physicalShiftedSourceRowFamilyCoordinate
    formula row inShifted
  let decoded :
      (clause : Fin (srcFormula formula).clauses.length) ×
        Fin (paperShiftedClauseTagCount
          formula budget clause) := finSigmaFinEquiv.symm tag
  have rank :
      tag.val =
        (∑ index : Fin decoded.1.val,
          paperShiftedClauseTagCount formula budget
            (Fin.castLE decoded.1.isLt.le index)) + decoded.2.val := by
    have actual := finSigmaFinEquiv_apply decoded
    change
      (finSigmaFinEquiv decoded).val =
        (∑ index : Fin decoded.1.val,
          paperShiftedClauseTagCount formula budget
            (Fin.castLE decoded.1.isLt.le index)) + decoded.2.val at actual
    rw [show finSigmaFinEquiv decoded = tag from
      Equiv.apply_symm_apply _ tag] at actual
    exact actual
  have divisible :
      budget + 1 ∣
        ∑ index : Fin decoded.1.val,
          paperShiftedClauseTagCount formula budget
            (Fin.castLE decoded.1.isLt.le index) := by
    apply Finset.dvd_sum
    intro index _
    exact paperVariableArityPhysicalShiftedClauseTagCount_moment_dvd
      formula budget (Fin.castLE decoded.1.isLt.le index)
  have sameMoment :
      decoded.2.val % (budget + 1) = tag.val % (budget + 1) := by
    rw [rank, Nat.add_mod,
      Nat.mod_eq_zero_of_dvd divisible, Nat.zero_add, Nat.mod_mod]
  change
    ((paperShiftedClauseWordOrder formula budget
      decoded.1 decoded.2).2.2).val = _
  rw [paperVariableArityPhysicalShiftedClauseWordMoment_val,
    sameMoment]
  change
    ((row.val - physicalFormulaOrdinaryBoundary formula) /
      (physGridCard formula *
        physDegree formula)) %
      physicalFormulaMomentCount formula = _
  congr 1
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm]

private theorem paperVariableArityPhysicalShiftedSourceRowMoment_eq_family
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    (physicalShiftedSourceRowMoment
      formula row inShifted).val =
      physicalFamilyRowMoment
        (3 : Fin 4) row.val formula := by
  rw [paperVariableArityPhysicalShiftedSourceRowMoment_val
    formula row inShifted]
  unfold physicalFamilyRowMoment
  simp only [physicalFamilyStart, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
      OfNat.ofNat_ne_zero,
      ↓reduceIte, OfNat.ofNat_ne_one, OfNat.ofNat_eq_ofNat, Nat.succ_ne_self]

end PhysicalShiftedInterpolationRowDigitCorrectness

namespace PhysicalShiftedInterpolationBinaryCheckBitCorrectness

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryFieldInverseAlgebra GapCVP.FormulaBridge
open GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationNodeCountBounds GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.PhysicalShiftedInterpolationBaseTM
open GapCVP.PhysicalShiftedInterpolationParityMaskedFieldCorrectness
open GapCVP.SourceFieldMomentOperationsTM GapCVP.SourceOrder

private noncomputable def paperVariableArityPhysicalShiftedActualSourceCorrectionField
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    PaperVariableArityPhysicalWordField
      (encodeThreeCNF formula).length formula :=
  (((List.range
    (physicalShiftedInterpolationNodeCount
      row.val formula)).map (fun node =>
      if node =
        (column.val /
          physFieldCard formula) %
          physGridCard formula
      then
        sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalInterpolationNodeSourceWord
            (3 : Fin 4) row.val formula
            (physicalShiftedInterpolationNodeCount
              row.val formula)
            (physicalShiftedInterpolationNodeCount_le_grid
              formula row.val)
            (physicalShiftedFiniteRowCanonicalBaseSourceWord
              formula row column inShifted) node)
      else 0)).sum)

private theorem paperVariableArityPhysicalShiftedActualSourceGridMatch_iff
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula)) :
    physicalInterpolationFamilyRowGridPosition
        (3 : Fin 4) row.val formula =
      physicalShiftedColumnGridIndex
        formula column.val ↔
      (((row.val - physicalFamilyStart
        (3 : Fin 4) formula) /
        physDegree formula) %
        physGridCard formula =
        (column.val /
          physFieldCard formula) %
          physGridCard formula) := by
  constructor
  · intro matching
    exact congrArg Fin.val matching
  · intro matching
    exact Fin.ext matching

private theorem paperVariableArityPhysicalShiftedActualDirectMomentBasis_decide
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    decide
      ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
        (encodeThreeCNF formula).length
        (srcFormula formula)).equivFun
        (if physicalInterpolationFamilyRowGridPosition
              (3 : Fin 4) row.val formula =
            physicalShiftedColumnGridIndex
              formula column.val
         then
          sourceWordValue (encodeThreeCNF formula).length
            (srcFormula formula)
            (physicalShiftedFiniteRowCanonicalBaseSourceWord
              formula row column inShifted) ^
            physicalFamilyRowMoment
              (3 : Fin 4) row.val formula
         else 0)
        (physicalInterpolationRowBasisIndex
          row.val formula) = (1 : ZMod 2)) =
      (decide
        ((((row.val - physicalFamilyStart
          (3 : Fin 4) formula) /
          physDegree formula) %
          physGridCard formula) =
          (column.val /
            physFieldCard formula) %
            physGridCard formula) &&
        (sourceWordPow
          (physicalShiftedFiniteRowCanonicalBaseSourceWord
            formula row column inShifted)
          (physicalFamilyRowMoment
            (3 : Fin 4) row.val formula))
          (physicalInterpolationRowBasisIndex
            row.val formula)) := by
  classical
  let sourceWord := physicalShiftedFiniteRowCanonicalBaseSourceWord
    formula row column inShifted
  let sourceMoment := physicalFamilyRowMoment
    (3 : Fin 4) row.val formula
  let sourceIndex := physicalInterpolationRowBasisIndex
    row.val formula
  by_cases matching :
      physicalInterpolationFamilyRowGridPosition
        (3 : Fin 4) row.val formula =
      physicalShiftedColumnGridIndex
        formula column.val
  · have physical :=
      (paperVariableArityPhysicalShiftedActualSourceGridMatch_iff
        formula row column).mp matching
    have coordinate := paperVariableArityPhysicalSourceWordBasisCoordinate_decide
      formula (sourceWordPow sourceWord sourceMoment) sourceIndex
    rw [sourceWordValue_sourceWordPow] at coordinate
    rw [ite_eq_left matching]
    simp only [physical, decide_true, Bool.true_and]
    exact coordinate
  · have physical : ¬
        (((row.val - physicalFamilyStart
          (3 : Fin 4) formula) /
          physDegree formula) %
          physGridCard formula =
          (column.val /
            physFieldCard formula) %
            physGridCard formula) := by
      intro equal
      exact matching
        ((paperVariableArityPhysicalShiftedActualSourceGridMatch_iff
          formula row column).mpr equal)
    rw [ite_eq_right matching]
    simp only [map_zero, Pi.zero_apply, zero_ne_one, decide_false, Fin.isValue, physical,
        Bool.false_and]

end PhysicalShiftedInterpolationBinaryCheckBitCorrectness

open GapCVP.PhysicalShiftedInterpolationBinaryCheckBitCorrectness

namespace PhysicalShiftedInterpolationParityDecodedFieldCorrectness

open scoped BigOperators

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryFieldInverseAlgebra
open GapCVP.BinaryReedSolomonParity GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationNodeCountBounds GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.PhysicalOrdinaryInterpolationParityFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowDigitCorrectness
open GapCVP.PhysicalShiftedSourceColumnGridProjection
open GapCVP.PhysicalShiftedInterpolationParityFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationParityMaskedFieldCorrectness
open GapCVP.SourceFieldMomentOperationsTM

private theorem paperVariableArityPhysicalShiftedExplicitGridParity_eq_sourceGridParity
    (formula : ThreeCNF) (degree : ℕ)
    (bounded : degree < Fintype.card
      (ExplicitGridPoint (encodeThreeCNF formula).length
        (srcFormula formula)))
    (row position : Fin (Fintype.card
      (ExplicitGridPoint (encodeThreeCNF formula).length
        (srcFormula formula)))) :
    constructiveParityMatrix
        (fun index =>
          (sourceFormulaExplicitGridOrder
            (encodeThreeCNF formula).length
            (srcFormula formula) index).val)
        bounded row position =
      constructiveParityMatrix
        (physicalShiftedSourceGridPoints formula)
        (lt_of_lt_of_eq bounded
          (physicalInterpolationExplicitGridCardinality_eq
            formula))
        (Fin.cast
          (physicalInterpolationExplicitGridCardinality_eq
            formula) row)
        (Fin.cast
          (physicalInterpolationExplicitGridCardinality_eq
            formula) position) := by
  classical
  rw [paperVariableArityPhysicalShiftedOrderedLagrangeParity_eq_selectedCorrection,
    paperVariableArityPhysicalShiftedOrderedLagrangeParity_eq_selectedCorrection]
  have sameRow :
      (Fin.cast
          (physicalInterpolationExplicitGridCardinality_eq
            formula) row =
        Fin.cast
          (physicalInterpolationExplicitGridCardinality_eq
            formula) position) ↔ row = position := by
    constructor
    · intro equal
      apply Fin.ext
      exact congrArg (fun value => value.val) equal
    · intro equal
      rw [equal]
  simp only [sameRow]
  by_cases selected : position.val < degree + 1
  · simp only [dite_eq_left selected]
    have selectedCast :
        (Fin.cast
          (physicalInterpolationExplicitGridCardinality_eq
            formula) position).val < degree + 1 := by
      exact selected
    simp only [dite_eq_left selectedCast]
    simp_rw [paperVariableArityPhysicalExplicitGridOrder_value_eq_evaluation]
    simp only [physicalShiftedSourceGridPoints]
    have nodeCast (node : Fin (degree + 1)) :
        Fin.cast
            (physicalInterpolationExplicitGridCardinality_eq
              formula)
            (Fin.castLE (Nat.succ_le_of_lt bounded) node) =
          Fin.castLE
            (Nat.succ_le_of_lt
              (lt_of_lt_of_eq bounded
                (physicalInterpolationExplicitGridCardinality_eq
                  formula))) node := by
      apply Fin.ext
      rfl
    have sameNode :
        (⟨position.val, selected⟩ : Fin (degree + 1)) =
          (⟨(Fin.cast
            (physicalInterpolationExplicitGridCardinality_eq
              formula) position).val, selectedCast⟩ : Fin (degree + 1)) := by
      apply Fin.ext
      rfl
    rw [← sameNode]
    simp_rw [nodeCast]
  · simp only [selected, ↓reduceDIte, sub_zero, Fin.val_cast]

private theorem paperVariableArityPhysicalShiftedDecodedRowParity_eq_maskedSourceCorrection
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (sourceFormulaDimension (encodeThreeCNF formula).length
        (srcFormula formula)))
    (inShifted : physicalFormulaOrdinaryBoundary formula ≤
      row.val) :
    constructiveParityMatrix
        (fun index =>
          (sourceFormulaExplicitGridOrder
            (encodeThreeCNF formula).length
            (srcFormula formula) index).val)
        (explicitShiftedDegree_lt_grid
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedSourceRowMoment
            formula row inShifted))
        (physicalShiftedSourceRowGrid
          formula row inShifted)
        ((sourceFormulaExplicitGridOrder
          (encodeThreeCNF formula).length
          (srcFormula formula)).symm
          ((sourceCoordinateWordOrder
            (encodeThreeCNF formula).length formula column).2.1)) *
      sourceWordValue (encodeThreeCNF formula).length
        (srcFormula formula)
        (physicalShiftedFiniteRowCanonicalBaseSourceWord
          formula row column inShifted) ^
        (physicalShiftedSourceRowMoment
          formula row inShifted).val =
      (if physicalShiftedSourceRowGrid
            formula row inShifted =
          (sourceFormulaExplicitGridOrder
            (encodeThreeCNF formula).length
            (srcFormula formula)).symm
            ((sourceCoordinateWordOrder
              (encodeThreeCNF formula).length formula column).2.1)
        then sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedFiniteRowCanonicalBaseSourceWord
            formula row column inShifted) ^
            (physicalShiftedSourceRowMoment
              formula row inShifted).val
        else 0) -
      (((List.range
        (physicalShiftedInterpolationNodeCount
          row.val formula)).map
          (fun node =>
            if node =
                (column.val /
                  physFieldCard formula) %
                    physGridCard formula
            then
              sourceWordValue (encodeThreeCNF formula).length
                (srcFormula formula)
                (physicalInterpolationNodeSourceWord
                  (3 : Fin 4) row.val formula
                  (physicalShiftedInterpolationNodeCount
                    row.val formula)
                  (physicalShiftedInterpolationNodeCount_le_grid
                    formula row.val)
                  (physicalShiftedFiniteRowCanonicalBaseSourceWord
                    formula row column inShifted)
                  node)
            else 0)).sum) := by
  let point := (sourceFormulaExplicitGridOrder
    (encodeThreeCNF formula).length
    (srcFormula formula)).symm
      ((sourceCoordinateWordOrder
        (encodeThreeCNF formula).length formula column).2.1)
  let degree := ((srcFormula formula).variableCount - 1) *
    (physicalShiftedSourceRowMoment
      formula row inShifted).val
  have correctMoment := paperVariableArityPhysicalShiftedSourceRowMoment_eq_family
    formula row inShifted
  have correctColumn :=
    physicalSourceColumnExplicitGridPosition_val
      formula column
  have rowCast :
      Fin.cast
          (physicalInterpolationExplicitGridCardinality_eq
            formula)
          (physicalShiftedSourceRowGrid
            formula row inShifted) =
        physicalInterpolationFamilyRowGridPosition
          (3 : Fin 4) row.val formula :=
    paperVariableArityPhysicalShiftedSourceRowNodeGrid_eq_family
      formula row inShifted
  have pointCast :
      Fin.cast
          (physicalInterpolationExplicitGridCardinality_eq
            formula) point =
        GapCVP.PhysicalShiftedInterpolationBaseTM.physicalShiftedColumnGridIndex
          formula column.val := by
    apply Fin.ext
    exact correctColumn
  have parityTransport :
      constructiveParityMatrix
          (fun index =>
            (sourceFormulaExplicitGridOrder
              (encodeThreeCNF formula).length
              (srcFormula formula) index).val)
          (explicitShiftedDegree_lt_grid
            (encodeThreeCNF formula).length
            (srcFormula formula)
            (physicalShiftedSourceRowMoment
              formula row inShifted))
          (physicalShiftedSourceRowGrid
            formula row inShifted) point =
        constructiveParityMatrix
          (physicalShiftedSourceGridPoints formula)
          (physicalShiftedSourceInterpolationDegree_lt_grid
            formula row.val)
          (physicalInterpolationFamilyRowGridPosition
            (3 : Fin 4) row.val formula)
          (GapCVP.PhysicalShiftedInterpolationBaseTM.physicalShiftedColumnGridIndex
            formula column.val) := by
    have transported :=
      paperVariableArityPhysicalShiftedExplicitGridParity_eq_sourceGridParity
        formula degree
        (explicitShiftedDegree_lt_grid
          (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedSourceRowMoment
            formula row inShifted))
        (physicalShiftedSourceRowGrid
          formula row inShifted) point
    rw [rowCast, pointCast] at transported
    simpa only [degree, correctMoment] using transported
  have sameDirect :
      (physicalShiftedSourceRowGrid
        formula row inShifted = point) ↔
      (physicalInterpolationFamilyRowGridPosition
        (3 : Fin 4) row.val formula =
        GapCVP.PhysicalShiftedInterpolationBaseTM.physicalShiftedColumnGridIndex
          formula column.val) := by
    constructor
    · intro equal
      exact rowCast.symm.trans
        ((congrArg
          (Fin.cast
            (physicalInterpolationExplicitGridCardinality_eq
              formula)) equal).trans pointCast)
    · intro equal
      apply Fin.ext
      have castEquality := rowCast.trans (equal.trans pointCast.symm)
      exact congrArg (fun value => value.val) castEquality
  have directEquality :
      (if physicalInterpolationFamilyRowGridPosition
            (3 : Fin 4) row.val formula =
          GapCVP.PhysicalShiftedInterpolationBaseTM.physicalShiftedColumnGridIndex
            formula column.val
        then sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedFiniteRowCanonicalBaseSourceWord
            formula row column inShifted) ^
            physicalFamilyRowMoment
              (3 : Fin 4) row.val formula
        else 0) =
      (if physicalShiftedSourceRowGrid
            formula row inShifted = point
        then sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedFiniteRowCanonicalBaseSourceWord
            formula row column inShifted) ^
            (physicalShiftedSourceRowMoment
              formula row inShifted).val
        else 0) := by
    rw [correctMoment]
    simp only [sameDirect]
  calc
    _ = constructiveParityMatrix
          (physicalShiftedSourceGridPoints formula)
          (physicalShiftedSourceInterpolationDegree_lt_grid
            formula row.val)
          (physicalInterpolationFamilyRowGridPosition
            (3 : Fin 4) row.val formula)
          (GapCVP.PhysicalShiftedInterpolationBaseTM.physicalShiftedColumnGridIndex
            formula column.val) *
        sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedFiniteRowCanonicalBaseSourceWord
            formula row column inShifted) ^
            physicalFamilyRowMoment
              (3 : Fin 4) row.val formula := by
          rw [parityTransport, correctMoment]
    _ = _ := by
      rw [paperVariableArityPhysicalShiftedFiniteRowParity_eq_maskedSourceCorrection
        formula row column inShifted, directEquality]

end PhysicalShiftedInterpolationParityDecodedFieldCorrectness

namespace PhysicalShiftedInterpolationRowCanonicalRankCorrectness

open scoped BigOperators

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge GapCVP.ClauseOffsetTM
open GapCVP.ShiftedTupleTM GapCVP.CanonicalOffsetIdentity GapCVP.SourceClausePrefixBridge
open GapCVP.SourceOrder GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalColumnOrderProjection GapCVP.PhysicalInterpolationRowFamilyProjection
open GapCVP.PhysicalRefinementColumnTagSourceCorrectness GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.PhysicalShiftedRowTupleRankBounds GapCVP.PhysicalShiftedExpectedTypeRankTM
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness

private theorem paperVariableArityPhysicalShiftedRowClausePrefix_mono
    (formula : ThreeCNF) (first second : ℕ)
    (ordered : first ≤ second) :
    physicalShiftedRowClausePrefix formula first ≤
      physicalShiftedRowClausePrefix formula second := by
  obtain ⟨gap, rfl⟩ := Nat.exists_eq_add_of_le ordered
  unfold physicalShiftedRowClausePrefix
    paperShiftedSourceClauseWeightSum
  rw [List.take_add, List.map_append, List.sum_append]
  omega

private theorem paperVariableArityPhysicalShiftedRowClausePrefix_succ
    (formula : ThreeCNF) (rank : ℕ)
    (bounded : rank < (noTautClauses formula).length) :
    physicalShiftedRowClausePrefix formula (rank + 1) =
      physicalShiftedRowClausePrefix formula rank +
        paperShiftedSourceClauseWeight
          ((noTautClauses formula).get
            ⟨rank, bounded⟩) := by
  unfold physicalShiftedRowClausePrefix
    paperShiftedSourceClauseWeightSum
  simp only [List.map_take]
  have mappedBound :
      rank <
        ((noTautClauses formula).map
          paperShiftedSourceClauseWeight).length := by
    simpa only [List.length_map] using bounded
  rw [← List.take_concat_get mappedBound]
  simp only [List.getElem_map, List.concat_eq_append, List.sum_append, List.sum_cons, List.sum_nil,
      add_zero,
    List.get_eq_getElem]

private theorem paperVariableArityPhysicalShiftedRangeFilter_le_length
    (count index : ℕ) (bounded : index < count) :
    ((List.range count).filter
      (fun rank => decide (rank ≤ index))).length = index + 1 := by
  rw [← List.Ico.zero_bot count]
  simp_rw [← Nat.lt_succ_iff]
  rw [List.Ico.filter_lt]
  simp only [Nat.succ_eq_add_one, Nat.min_eq_right (Nat.succ_le_of_lt bounded), List.Ico.length,
      tsub_zero]

private theorem paperVariableArityPhysicalShiftedRowClauseRank_eq_of_interval
    (formula : ThreeCNF) (row : ℕ)
    (clause : Fin (noTautClauses formula).length)
    (lower : physicalShiftedRowClausePrefix
      formula clause.val ≤ physicalShiftedRowMixedTag
        formula row)
    (upper : physicalShiftedRowMixedTag formula row <
      physicalShiftedRowClausePrefix
        formula (clause.val + 1)) :
    physicalShiftedRowClauseRank formula row = clause.val := by
  have same (rank : ℕ)
      (_membership : rank ∈
        List.range (noTautClauses formula).length) :
      decide
          (physicalShiftedRowClausePrefix formula rank ≤
            physicalShiftedRowMixedTag formula row) =
        decide (rank ≤ clause.val) := by
    apply Bool.decide_congr
    constructor
    · intro accepted
      by_contra after
      have ordered : clause.val + 1 ≤ rank := by omega
      have later := paperVariableArityPhysicalShiftedRowClausePrefix_mono
        formula (clause.val + 1) rank ordered
      omega
    · intro before
      have earlier := paperVariableArityPhysicalShiftedRowClausePrefix_mono
        formula rank clause.val before
      omega
  have filtered := List.filter_congr same
  have actual := paperVariableArityPhysicalShiftedRangeFilter_le_length
    (noTautClauses formula).length
    clause.val clause.isLt
  unfold physicalShiftedRowClauseRank
    physicalShiftedRowAcceptedPrefixCount
  rw [filtered, actual]
  omega

private theorem paperVariableArityPhysicalShiftedFiniteClauseWeight_eq
    (formula : ThreeCNF)
    (index : Fin (srcFormula formula).clauses.length) :
    paperFormulaClauseWidth formula index *
        (2 ^ paperFormulaClauseWidth formula index - 1) =
      paperShiftedSourceClauseWeight
        ((noTautClauses formula).get
          (Fin.cast
            (paperVariableAritySourceFormula_clauses_length formula)
            index)) := by
  let retainedIndex : Fin
      (noTautClauses formula).length :=
    Fin.cast
      (paperVariableAritySourceFormula_clauses_length formula)
      index
  have sameIndex :
      paperRetainedOriginalClauseIndexOrder
          formula retainedIndex = index := by
    apply Fin.ext
    rfl
  have sameWidth := paperFormulaClauseWidth_retainedOriginal
    formula retainedIndex
  rw [sameIndex] at sameWidth
  rw [sameWidth]
  rfl

private theorem paperVariableArityPhysicalShiftedIndexedClausePrefix_eq_weightSum
    (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length) :
    (∑ index : Fin clause.val,
      paperShiftedSourceClauseWeight
        ((noTautClauses formula).get
          (sourceRetainedPrefixIndex
            formula clause index))) =
      paperShiftedSourceClauseWeightSum
        ((noTautClauses formula).take clause.val) := by
  let retained := noTautClauses formula
  have retainedBound : clause.val ≤ retained.length := by
    have strict : clause.val < retained.length := by
      simpa only [srcFormula,
        GapCVP.SourcePreprocessingSemantics.paperSourceNormalizedClauses,
        List.length_map, List.length_attach, retained] using clause.isLt
    exact strict.le
  have takeLength : (retained.take clause.val).length = clause.val := by
    simp only [List.length_take, Nat.min_eq_left retainedBound]
  let order : Fin (retained.take clause.val).length ≃ Fin clause.val :=
    finCongr takeLength
  let weight : Fin clause.val → ℕ := fun index =>
    paperShiftedSourceClauseWeight
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
          paperShiftedSourceClauseWeight
            ((retained.take clause.val).get index) := by
          apply Finset.sum_congr rfl
          intro index _
          have sameClause :
              retained.get
                  (sourceRetainedPrefixIndex
                    formula clause (order index)) =
                (retained.take clause.val).get index := by
            simp only [List.get_eq_getElem, List.getElem_take]
            rfl
          exact congrArg paperShiftedSourceClauseWeight sameClause
    _ = paperShiftedSourceClauseWeightSum
          (retained.take clause.val) := by
          symm
          exact sourceListWeightSum
            (retained.take clause.val)
            paperShiftedSourceClauseWeight

private theorem paperVariableArityPhysicalShiftedDependentClausePrefix_eq_weightSum
    (formula : ThreeCNF) (budget : ℕ)
    (clause : Fin (srcFormula formula).clauses.length) :
    (∑ index : Fin clause.val,
      paperShiftedClauseTagCount formula budget
        (Fin.castLE clause.isLt.le index)) =
      physicalShiftedRowClausePrefix formula clause.val *
        (budget + 1) := by
  unfold paperShiftedClauseTagCount
  calc
    (∑ index : Fin clause.val,
      (2 ^ paperFormulaClauseWidth formula
        (Fin.castLE clause.isLt.le index) - 1) *
        (paperFormulaClauseWidth formula
          (Fin.castLE clause.isLt.le index) * (budget + 1))) =
      ∑ index : Fin clause.val,
        (paperFormulaClauseWidth formula
          (Fin.castLE clause.isLt.le index) *
          (2 ^ paperFormulaClauseWidth formula
            (Fin.castLE clause.isLt.le index) - 1)) * (budget + 1) := by
        apply Finset.sum_congr rfl
        intro index _
        ring
    _ =
      (∑ index : Fin clause.val,
        paperFormulaClauseWidth formula
          (Fin.castLE clause.isLt.le index) *
          (2 ^ paperFormulaClauseWidth formula
            (Fin.castLE clause.isLt.le index) - 1)) * (budget + 1) := by
        rw [Finset.sum_mul]
    _ =
      (∑ index : Fin clause.val,
        paperShiftedSourceClauseWeight
          ((noTautClauses formula).get
            (sourceRetainedPrefixIndex
              formula clause index))) * (budget + 1) := by
        congr 1
        apply Finset.sum_congr rfl
        intro index _
        exact paperVariableArityPhysicalShiftedFiniteClauseWeight_eq
          formula (Fin.castLE clause.isLt.le index)
    _ = physicalShiftedRowClausePrefix
          formula clause.val * (budget + 1) := by
        rw [paperVariableArityPhysicalShiftedIndexedClausePrefix_eq_weightSum
          formula clause]
        rfl

private theorem paperVariableArityPhysicalShiftedClauseTupleWordRank
    (formula : ThreeCNF) (budget : ℕ)
    (clause : Fin (srcFormula formula).clauses.length)
    (word : Fin (paperShiftedClauseTagCount
      formula budget clause)) :
    ((paperFormulaClauseTupleWordOrder formula clause).symm
      ((paperShiftedClauseWordOrder
        formula budget clause word).1)).val =
      word.val /
        (paperFormulaClauseWidth formula clause *
          (budget + 1)) := by
  change
    ((paperFormulaClauseTupleWordOrder formula clause).symm
      (paperFormulaClauseTupleWordOrder formula clause
        ((finProdFinEquiv
          (m := 2 ^ paperFormulaClauseWidth
            formula clause - 1)
          (n := paperFormulaClauseWidth formula clause *
            (budget + 1))).symm word).1)).val = _
  rw [Equiv.symm_apply_apply]
  rfl

end PhysicalShiftedInterpolationRowCanonicalRankCorrectness

namespace PhysicalShiftedInterpolationRowCanonicalSourceDigits

open scoped BigOperators

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact GapCVP.FormulaBridge
open GapCVP.ShiftedTupleTM GapCVP.SourceOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationRowFamilyProjection GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowCanonicalRankCorrectness

private theorem paperVariableArityPhysicalShiftedSourceRowClauseRank_eq
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    physicalShiftedRowClauseRank formula row.val =
      (physicalShiftedSourceRowClause
        formula row inShifted).val := by
  let budget := physicalInterpolationMomentBudget formula
  let moment := budget + 1
  let tag := physicalShiftedSourceRowFamilyCoordinate
    formula row inShifted
  let decoded :
      (clause : Fin (srcFormula formula).clauses.length) ×
        Fin (paperShiftedClauseTagCount
          formula budget clause) := finSigmaFinEquiv.symm tag
  let retainedClause : Fin (noTautClauses formula).length :=
    Fin.cast (paperVariableAritySourceFormula_clauses_length formula)
      decoded.1
  let sourcePrefix := physicalShiftedRowClausePrefix
    formula decoded.1.val
  have positive : 0 < moment := by
    dsimp [moment]
    omega
  have sigmaRank :
      tag.val =
        (∑ index : Fin decoded.1.val,
          paperShiftedClauseTagCount formula budget
            (Fin.castLE decoded.1.isLt.le index)) + decoded.2.val := by
    have actual := finSigmaFinEquiv_apply decoded
    change
      (finSigmaFinEquiv decoded).val =
        (∑ index : Fin decoded.1.val,
          paperShiftedClauseTagCount formula budget
            (Fin.castLE decoded.1.isLt.le index)) + decoded.2.val at actual
    rw [show finSigmaFinEquiv decoded = tag from
      Equiv.apply_symm_apply _ tag] at actual
    exact actual
  have rank : tag.val = sourcePrefix * moment + decoded.2.val := by
    rw [sigmaRank,
      paperVariableArityPhysicalShiftedDependentClausePrefix_eq_weightSum]
  have mixedTag :
      tag.val / moment =
        physicalShiftedRowMixedTag formula row.val := by
    change
      ((row.val - physicalFormulaOrdinaryBoundary formula) /
        (physGridCard formula *
          physDegree formula)) /
          physicalFormulaMomentCount formula = _
    congr 1
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  have shiftedWeight :
      paperShiftedClauseTagCount formula budget decoded.1 =
        paperShiftedSourceClauseWeight
          ((noTautClauses formula).get retainedClause) *
            moment := by
    calc
      paperShiftedClauseTagCount formula budget decoded.1 =
          (paperFormulaClauseWidth formula decoded.1 *
            (2 ^ paperFormulaClauseWidth
              formula decoded.1 - 1)) * moment := by
            unfold paperShiftedClauseTagCount
            dsimp [moment]
            ring
      _ = paperShiftedSourceClauseWeight
          ((noTautClauses formula).get retainedClause) *
            moment := by
            rw [paperVariableArityPhysicalShiftedFiniteClauseWeight_eq
              formula decoded.1]
  have mixedDecomposition :
      physicalShiftedRowMixedTag formula row.val =
        sourcePrefix + decoded.2.val / moment := by
    rw [← mixedTag, rank]
    rw [show sourcePrefix * moment = moment * sourcePrefix by ac_rfl,
      Nat.mul_add_div positive]
  have inClause :
      decoded.2.val / moment <
        paperShiftedSourceClauseWeight
          ((noTautClauses formula).get retainedClause) := by
    apply (Nat.div_lt_iff_lt_mul positive).mpr
    rw [← shiftedWeight]
    exact decoded.2.isLt
  have sameSourcePrefix :
      physicalShiftedRowClausePrefix
        formula retainedClause.val = sourcePrefix := by
    rfl
  have lower :
      physicalShiftedRowClausePrefix
          formula retainedClause.val ≤
        physicalShiftedRowMixedTag formula row.val := by
    calc
      physicalShiftedRowClausePrefix
          formula retainedClause.val = sourcePrefix := sameSourcePrefix
      _ ≤ sourcePrefix + decoded.2.val / moment := Nat.le_add_right _ _
      _ = physicalShiftedRowMixedTag formula row.val :=
        mixedDecomposition.symm
  have upper :
      physicalShiftedRowMixedTag formula row.val <
        physicalShiftedRowClausePrefix
          formula (retainedClause.val + 1) := by
    calc
      physicalShiftedRowMixedTag formula row.val =
          sourcePrefix + decoded.2.val / moment := mixedDecomposition
      _ < sourcePrefix +
          paperShiftedSourceClauseWeight
            ((noTautClauses formula).get retainedClause) :=
        Nat.add_lt_add_left inClause sourcePrefix
      _ = physicalShiftedRowClausePrefix
          formula (retainedClause.val + 1) := by
        rw [paperVariableArityPhysicalShiftedRowClausePrefix_succ
          formula retainedClause.val retainedClause.isLt,
          sameSourcePrefix]
  have selected :=
    paperVariableArityPhysicalShiftedRowClauseRank_eq_of_interval
      formula row.val retainedClause lower upper
  have sourceClause :
      (physicalShiftedSourceRowClause
        formula row inShifted).val = decoded.1.val := by
    change
      ((Equiv.sigmaCongrRight fun clause =>
        paperShiftedClauseWordOrder
          formula budget clause)
        (finSigmaFinEquiv.symm tag)).fst.val = decoded.1.val
    rfl
  exact selected.trans sourceClause.symm

end PhysicalShiftedInterpolationRowCanonicalSourceDigits

namespace PhysicalShiftedInterpolationLocalVariableWordRank

open GapCVP.Core GapCVP.FormulaBridge GapCVP.SourceOrder

private theorem paperVariableArityPhysicalShiftedClauseLocalVariableWordRank
    (formula : ThreeCNF) (budget : ℕ)
    (clause : Fin (srcFormula formula).clauses.length)
    (word : Fin
      (paperShiftedClauseTagCount formula budget clause)) :
    ((paperFormulaClauseVariableWordOrder formula clause).symm
      ((paperShiftedClauseWordOrder formula budget clause
        word).2.1)).val =
      (word.val / (budget + 1)) %
        paperFormulaClauseWidth formula clause := by
  change
    ((paperFormulaClauseVariableWordOrder formula clause).symm
      (paperFormulaClauseVariableWordOrder formula clause
        ((finProdFinEquiv
          (m := paperFormulaClauseWidth formula clause)
          (n := budget + 1)).symm
          ((finProdFinEquiv
            (m := 2 ^ paperFormulaClauseWidth
              formula clause - 1)
            (n := paperFormulaClauseWidth formula clause *
              (budget + 1))).symm word).2).1)).val = _
  rw [Equiv.symm_apply_apply]
  exact Nat.mod_mul_left_div_self
    word.val (budget + 1)
    (paperFormulaClauseWidth formula clause)

end PhysicalShiftedInterpolationLocalVariableWordRank

namespace PhysicalShiftedInterpolationRowCanonicalSourceTupleDigits

open scoped BigOperators

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge GapCVP.CanonicalOffsetIdentity
open GapCVP.SourceOrder GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalInterpolationRowFamilyProjection GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.PhysicalShiftedRowTupleRankBounds
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowCanonicalRankCorrectness
open GapCVP.PhysicalShiftedInterpolationRowCanonicalSourceDigits
open GapCVP.PhysicalShiftedInterpolationLocalVariableWordRank

private def paperVariableArityPhysicalShiftedSourceRowCanonicalSigma
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    (clause : Fin (srcFormula formula).clauses.length) ×
      Fin (paperShiftedClauseTagCount formula
        (physicalInterpolationMomentBudget formula) clause) :=
  finSigmaFinEquiv.symm
    (physicalShiftedSourceRowFamilyCoordinate
      formula row inShifted)

private theorem paperVariableArityPhysicalShiftedSourceRowCanonicalMixedDigits
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    physicalShiftedRowSelectedClauseArity
        formula row.val
        (physicalShiftedRowClauseRank_lt_of_fin
          formula row inShifted) =
        paperFormulaClauseWidth formula
          (physicalShiftedSourceRowClause
            formula row inShifted) ∧
      physicalShiftedRowLocalTag formula row.val =
        (paperVariableArityPhysicalShiftedSourceRowCanonicalSigma
          formula row inShifted).2.val /
            physicalFormulaMomentCount formula := by
  let budget := physicalInterpolationMomentBudget formula
  let moment := budget + 1
  let tag := physicalShiftedSourceRowFamilyCoordinate
    formula row inShifted
  let decoded :
      (clause : Fin (srcFormula formula).clauses.length) ×
        Fin (paperShiftedClauseTagCount
          formula budget clause) := finSigmaFinEquiv.symm tag
  let retainedClause : Fin (noTautClauses formula).length :=
    Fin.cast (paperVariableAritySourceFormula_clauses_length formula)
      decoded.1
  let sourcePrefix := physicalShiftedRowClausePrefix
    formula decoded.1.val
  have positive : 0 < moment := by
    dsimp [moment]
    omega
  have sourceClause :
      physicalShiftedSourceRowClause
        formula row inShifted = decoded.1 := by
    apply Fin.ext
    change
      ((Equiv.sigmaCongrRight fun clause =>
        paperShiftedClauseWordOrder
          formula budget clause)
        (finSigmaFinEquiv.symm tag)).fst.val = decoded.1.val
    rfl
  have selectedClause :
      physicalShiftedRowClauseRank formula row.val =
        decoded.1.val := by
    exact (paperVariableArityPhysicalShiftedSourceRowClauseRank_eq
      formula row inShifted).trans (congrArg Fin.val sourceClause)
  have sigmaRank :
      tag.val =
        (∑ index : Fin decoded.1.val,
          paperShiftedClauseTagCount formula budget
            (Fin.castLE decoded.1.isLt.le index)) + decoded.2.val := by
    have actual := finSigmaFinEquiv_apply decoded
    change
      (finSigmaFinEquiv decoded).val =
        (∑ index : Fin decoded.1.val,
          paperShiftedClauseTagCount formula budget
            (Fin.castLE decoded.1.isLt.le index)) + decoded.2.val at actual
    rw [show finSigmaFinEquiv decoded = tag from
      Equiv.apply_symm_apply _ tag] at actual
    exact actual
  have rank : tag.val = sourcePrefix * moment + decoded.2.val := by
    rw [sigmaRank,
      paperVariableArityPhysicalShiftedDependentClausePrefix_eq_weightSum]
  have mixedTag :
      tag.val / moment =
        physicalShiftedRowMixedTag formula row.val := by
    change
      ((row.val - physicalFormulaOrdinaryBoundary formula) /
        (physGridCard formula *
          physDegree formula)) /
          physicalFormulaMomentCount formula = _
    congr 1
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  have mixedDecomposition :
      physicalShiftedRowMixedTag formula row.val =
        sourcePrefix + decoded.2.val / moment := by
    rw [← mixedTag, rank]
    rw [show sourcePrefix * moment = moment * sourcePrefix by ac_rfl,
      Nat.mul_add_div positive]
  have selectedWidth :
      physicalShiftedRowSelectedClauseArity
        formula row.val
        (physicalShiftedRowClauseRank_lt_of_fin
          formula row inShifted) =
        paperFormulaClauseWidth formula decoded.1 := by
    let actualRetained : Fin
        (noTautClauses formula).length :=
      ⟨physicalShiftedRowClauseRank formula row.val,
        physicalShiftedRowClauseRank_lt_of_fin
          formula row inShifted⟩
    have sameRetained : actualRetained = retainedClause := by
      apply Fin.ext
      exact selectedClause
    have width := paperFormulaClauseWidth_retainedOriginal
      formula retainedClause
    have index :
        paperRetainedOriginalClauseIndexOrder
          formula retainedClause = decoded.1 := by
      apply Fin.ext
      rfl
    rw [index] at width
    change
      (paperSourceNormalizedClause
        ((noTautClauses formula).get
          actualRetained)).length = _
    rw [sameRetained]
    exact width.symm
  have selectedLocalTag :
      physicalShiftedRowLocalTag formula row.val =
        decoded.2.val / moment := by
    unfold physicalShiftedRowLocalTag
    rw [selectedClause, mixedDecomposition]
    change sourcePrefix + decoded.2.val / moment - sourcePrefix = _
    exact Nat.add_sub_cancel_left sourcePrefix (decoded.2.val / moment)
  constructor
  · rw [sourceClause]
    exact selectedWidth
  · change
      physicalShiftedRowLocalTag formula row.val =
        decoded.2.val / moment
    exact selectedLocalTag

private theorem paperVariableArityPhysicalShiftedSourceRowTupleRank_eq
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    physicalShiftedRowTupleRank
        formula row.val
        (physicalShiftedRowClauseRank_lt_of_fin
          formula row inShifted) =
      ((paperFormulaClauseTupleWordOrder formula
        (physicalShiftedSourceRowClause
          formula row inShifted)).symm
        (physicalShiftedSourceRowTuple
          formula row inShifted)).val := by
  let budget := physicalInterpolationMomentBudget formula
  let moment := budget + 1
  let tag := physicalShiftedSourceRowFamilyCoordinate
    formula row inShifted
  let decoded :
      (clause : Fin (srcFormula formula).clauses.length) ×
        Fin (paperShiftedClauseTagCount
          formula budget clause) := finSigmaFinEquiv.symm tag
  have digits := paperVariableArityPhysicalShiftedSourceRowCanonicalMixedDigits
    formula row inShifted
  unfold physicalShiftedRowTupleRank
  rw [digits.2, digits.1, Nat.div_div_eq_div_mul]
  rw [Nat.mul_comm (physicalFormulaMomentCount formula)]
  change
    decoded.2.val /
      (paperFormulaClauseWidth formula decoded.1 * moment) =
      ((paperFormulaClauseTupleWordOrder formula
        ((finSigmaFinEquiv.symm tag).1)).symm
        ((paperShiftedClauseWordOrder formula budget
          (finSigmaFinEquiv.symm tag).1
          (finSigmaFinEquiv.symm tag).2).1)).val
  symm
  simpa only [decoded, moment] using
    paperVariableArityPhysicalShiftedClauseTupleWordRank
      formula budget decoded.1 decoded.2

private theorem paperVariableArityPhysicalShiftedSourceRowLocalVariableRank_eq
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    physicalShiftedRowVariablePosition
        formula row.val
        (physicalShiftedRowClauseRank_lt_of_fin
          formula row inShifted) =
      ((paperFormulaClauseVariableWordOrder formula
        (physicalShiftedSourceRowClause
          formula row inShifted)).symm
        (physicalShiftedSourceRowLocalVariable
          formula row inShifted)).val := by
  let budget := physicalInterpolationMomentBudget formula
  let moment := budget + 1
  let tag := physicalShiftedSourceRowFamilyCoordinate
    formula row inShifted
  let decoded :
      (clause : Fin (srcFormula formula).clauses.length) ×
        Fin (paperShiftedClauseTagCount
          formula budget clause) := finSigmaFinEquiv.symm tag
  have digits := paperVariableArityPhysicalShiftedSourceRowCanonicalMixedDigits
    formula row inShifted
  unfold physicalShiftedRowVariablePosition
  rw [digits.2, digits.1]
  change
    decoded.2.val / moment %
        paperFormulaClauseWidth formula decoded.1 =
      ((paperFormulaClauseVariableWordOrder formula
        ((finSigmaFinEquiv.symm tag).1)).symm
        ((paperShiftedClauseWordOrder formula budget
          (finSigmaFinEquiv.symm tag).1
          (finSigmaFinEquiv.symm tag).2).2.1)).val
  symm
  simpa only [decoded, moment] using
    paperVariableArityPhysicalShiftedClauseLocalVariableWordRank
      formula budget decoded.1 decoded.2

end PhysicalShiftedInterpolationRowCanonicalSourceTupleDigits

namespace PhysicalShiftedInterpolationRowCanonicalRankCorrectness

open scoped BigOperators

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge GapCVP.ClauseOffsetTM
open GapCVP.ShiftedTupleTM GapCVP.CanonicalOffsetIdentity GapCVP.SourceClausePrefixBridge
open GapCVP.SourceOrder GapCVP.MatrixEntrySemantics GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalColumnOrderProjection GapCVP.PhysicalInterpolationRowFamilyProjection
open GapCVP.PhysicalRefinementColumnTagSourceCorrectness GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.PhysicalShiftedRowTupleRankBounds GapCVP.PhysicalShiftedExpectedTypeRankTM
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness

open GapCVP.PhysicalShiftedInterpolationRowCanonicalSourceDigits
open GapCVP.PhysicalShiftedInterpolationRowCanonicalSourceTupleDigits

private theorem paperVariableArityPhysicalShiftedSourceRowTable_eq_column_iff
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    (Sum.inr
      ⟨physicalShiftedSourceRowClause
          formula row inShifted,
        physicalShiftedSourceRowTuple
          formula row inShifted⟩ :
      sourceSATTableType (srcFormula formula)) =
        (sourceCoordinateWordOrder
          (encodeThreeCNF formula).length formula column).1 ↔
      physicalShiftedExpectedTableTypeRank
          formula row.val
          (physicalShiftedRowClauseRank_lt_of_fin
            formula row inShifted) =
        (column.val /
          physFieldCard formula) /
            physGridCard formula := by
  let sourceTable : sourceSATTableType
      (srcFormula formula) :=
    Sum.inr
      ⟨physicalShiftedSourceRowClause
          formula row inShifted,
        physicalShiftedSourceRowTuple
          formula row inShifted⟩
  let columnTable :=
    (sourceCoordinateWordOrder
      (encodeThreeCNF formula).length formula column).1
  have clauseRank :=
    paperVariableArityPhysicalShiftedSourceRowClauseRank_eq
      formula row inShifted
  have tupleRank :=
    paperVariableArityPhysicalShiftedSourceRowTupleRank_eq
      formula row inShifted
  have sourceRank :
      ((sourceTypeCardWordOrder formula).symm
        sourceTable).val =
        physicalShiftedExpectedTableTypeRank
          formula row.val
          (physicalShiftedRowClauseRank_lt_of_fin
            formula row inShifted) := by
    dsimp [sourceTable]
    rw [paperVariableAritySourceLocalTypeWordRank,
      finSigmaFinEquiv_apply,
      paperVariableAritySourceDependentClausePrefix_eq_weightSum]
    unfold physicalShiftedExpectedTableTypeRank
      physicalShiftedExpectedLocalTypePrefix
    rw [clauseRank, tupleRank]
  have columnRank := sourceCoordinateTypeWordRank
    (encodeThreeCNF formula).length formula column
  rw [physicalFormulaFieldCardinality_eq_card,
    physicalFormulaGridCardinality_eq_card] at columnRank
  change sourceTable = columnTable ↔ _
  rw [← sourceRank, ← columnRank]
  exact ⟨fun same => congrArg (fun value =>
      ((sourceTypeCardWordOrder formula).symm value).val) same,
    fun same => (sourceTypeCardWordOrder formula).symm.injective
      (Fin.ext same)⟩

end PhysicalShiftedInterpolationRowCanonicalRankCorrectness

namespace PhysicalShiftedInterpolationBinaryHCoreCorrectness

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryFieldInverseAlgebra
open GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics GapCVP.PhysicalColumnOrder
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalInterpolationNodeFactorTM
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryShiftedCheckBitInstantiation
open GapCVP.PhysicalShiftedExpectedTypeRankTM
open GapCVP.PhysicalShiftedInterpolationBinaryCheckBitCorrectness
open GapCVP.PhysicalShiftedInterpolationBaseTM
open GapCVP.PhysicalShiftedInterpolationParityDecodedFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationParityMaskedFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowCanonicalRankCorrectness
open GapCVP.PhysicalShiftedInterpolationRowDigitCorrectness
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowSourceProjection
open GapCVP.PhysicalShiftedRowTupleRankBounds GapCVP.SourceFieldMomentOperationsTM
open GapCVP.SourceOrder GapCVP.PhysicalInterpolationNodeCountBounds

private theorem paperVariableArityPhysicalShiftedActualBinaryCheckBit_decide_of_sourceRatio
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val)
    (correctRatio :
      sourceWordValue (encodeThreeCNF formula).length
          (srcFormula formula)
          (physicalShiftedFiniteRowCanonicalBaseSourceWord
            formula row column inShifted) =
        ((sourceCoordinateWordOrder
            (encodeThreeCNF formula).length formula column).2.2 -
          sourceSATFieldBit
            (K := PaperVariableArityPhysicalWordField
              (encodeThreeCNF formula).length formula)
            ((physicalShiftedSourceRowTuple
              formula row inShifted).val
              (physicalShiftedSourceRowLocalVariable
                formula row inShifted))) /
        ((sourceCoordinateWordOrder
            (encodeThreeCNF formula).length formula column).2.1.val -
          GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
            (encodeThreeCNF formula).length
            (srcFormula formula)
            (physicalShiftedSourceRowLocalVariable
              formula row inShifted).val)) :
    decide
      ((physicalWordBinarySystem
        (encodeThreeCNF formula).length formula).check row column =
        (1 : ZMod 2)) =
      (decide
        (physicalShiftedExpectedTableTypeRank
          formula row.val
          (physicalShiftedRowClauseRank_lt_of_fin
            formula row inShifted) =
          (column.val /
            physFieldCard formula) /
            physGridCard formula) &&
       Bool.xor
        (decide
          ((((row.val - physicalFamilyStart
            (3 : Fin 4) formula) /
            physDegree formula) %
            physGridCard formula) =
            (column.val /
              physFieldCard formula) %
              physGridCard formula) &&
          (sourceWordPow
            (physicalShiftedFiniteRowCanonicalBaseSourceWord
              formula row column inShifted)
            (physicalFamilyRowMoment
              (3 : Fin 4) row.val formula))
            (physicalInterpolationRowBasisIndex
              row.val formula))
        (decide
          ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
            (encodeThreeCNF formula).length
            (srcFormula formula)).equivFun
            (paperVariableArityPhysicalShiftedActualSourceCorrectionField
              formula row column inShifted)
            (physicalInterpolationRowBasisIndex
              row.val formula) = (1 : ZMod 2)))) := by
  classical
  have basis : (physicalWordDecodedRow
      (encodeThreeCNF formula).length formula row).2.2 =
      physicalInterpolationRowBasisIndex row.val formula :=
    Fin.ext (paperVariableArityPhysicalShiftedSourceRowBasis_val formula row)
  rw [physicalWordBinaryCheckCoefficient,
    paperVariableArityPhysicalShiftedSourceRowFieldCoefficient_eq_selected
      formula row column inShifted, basis]
  by_cases matching :
      (Sum.inr ⟨physicalShiftedSourceRowClause formula row inShifted,
          physicalShiftedSourceRowTuple formula row inShifted⟩ :
        sourceSATTableType (srcFormula formula)) =
        (sourceCoordinateWordOrder
          (encodeThreeCNF formula).length formula column).1
  · have expected :=
      (paperVariableArityPhysicalShiftedSourceRowTable_eq_column_iff
        formula row column inShifted).mp matching
    simp only [matching, ite_eq_left, expected, decide_true, Bool.true_and]
    have sourceRow := paperVariableArityPhysicalShiftedSourceRowNodeGrid_eq_family
      formula row inShifted
    have sourceColumn :
        Fin.cast (physicalInterpolationExplicitGridCardinality_eq formula)
            ((sourceFormulaExplicitGridOrder (encodeThreeCNF formula).length
              (srcFormula formula)).symm
                (sourceCoordinateWordOrder
                  (encodeThreeCNF formula).length formula column).2.1) =
          physicalShiftedColumnGridIndex formula column.val :=
      Fin.ext (physicalSourceColumnExplicitGridPosition_val
        formula column)
    have sameGrid :
        physicalShiftedSourceRowGrid formula row inShifted =
          (sourceFormulaExplicitGridOrder (encodeThreeCNF formula).length
            (srcFormula formula)).symm
              (sourceCoordinateWordOrder
                (encodeThreeCNF formula).length formula column).2.1 ↔
        physicalInterpolationFamilyRowGridPosition
          (3 : Fin 4) row.val formula =
          physicalShiftedColumnGridIndex formula column.val := by
      constructor
      · intro same
        exact sourceRow.symm.trans ((congrArg
          (Fin.cast (physicalInterpolationExplicitGridCardinality_eq
            formula)) same).trans sourceColumn)
      · intro same
        exact Fin.cast_injective
          (physicalInterpolationExplicitGridCardinality_eq formula)
          (sourceRow.trans (same.trans sourceColumn.symm))
    rw [← correctRatio,
      paperVariableArityPhysicalShiftedDecodedRowParity_eq_maskedSourceCorrection,
      paperVariableArityPhysicalSourceBasisCoordinate_sub_decide]
    simp only [sameGrid,
      paperVariableArityPhysicalShiftedSourceRowMoment_eq_family]
    rw [paperVariableArityPhysicalShiftedActualDirectMomentBasis_decide]
    rfl
  · have expected : ¬
        physicalShiftedExpectedTableTypeRank formula row.val
          (physicalShiftedRowClauseRank_lt_of_fin
            formula row inShifted) =
          (column.val /
            physFieldCard formula) /
            physGridCard formula :=
      fun same => matching
        ((paperVariableArityPhysicalShiftedSourceRowTable_eq_column_iff
          formula row column inShifted).mpr same)
    simp only [List.get_eq_getElem, matching, ↓reduceIte, Module.Basis.equivFun_apply, map_zero,
      Pi.zero_apply, zero_ne_one, decide_false, expected, Fin.isValue, Bool.false_and]

end PhysicalShiftedInterpolationBinaryHCoreCorrectness

namespace PhysicalShiftedCanonicalInterpolationBaseSourceWordSemanticBridge

open GapCVP.SourcePreprocessingSemantics GapCVP.SourceOrder

private theorem paperVariableAritySourceClauseTupleWordOrder_apply_localVariable
    (formula : ThreeCNF)
    (clause : List GapCVP.Literal)
    (hclause : clause ∈ paperSourceNormalizedClauses formula)
    (tuple : Fin (2 ^ clause.length - 1))
    (position : Fin clause.length) :
    (sourceClauseTupleWordOrder
      formula clause hclause tuple).val
        (paperLocalVariableWordOrder
          formula clause hclause position) =
      (paperSatisfyingWordOrder clause.length
        (fun index => (clause.get index).2) tuple).val position := by
  simp only [sourceClauseTupleWordOrder, List.get_eq_getElem,
      paperVariableAritySatisfyingLocalTupleWordEquiv,
      paperLocalAssignmentWordOrder, Equiv.subtypeEquiv_symm, Equiv.arrowCongr_symm,
          Equiv.symm_symm, Equiv.refl_symm,
      Equiv.trans_apply, Equiv.subtypeEquiv_apply, Equiv.arrowCongr_apply, Equiv.coe_refl,
          Function.comp_apply,
      Equiv.symm_apply_apply, id_eq]

end PhysicalShiftedCanonicalInterpolationBaseSourceWordSemanticBridge

namespace PhysicalShiftedCanonicalRetainedClauseSourceCorrectness

open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.FormulaBridge GapCVP.CanonicalOffsetIdentity GapCVP.SourceOrder

theorem paperFormulaRetainedClause_retainedOriginal
    (formula : ThreeCNF)
    (original : Fin (noTautClauses formula).length) :
    (paperFormulaRetainedClause formula
      (paperRetainedOriginalClauseIndexOrder
        formula original)).val =
      paperSourceNormalizedClause
        ((noTautClauses formula).get original) := by
  simp only [paperSourceNormalizedClauses, paperFormulaRetainedClause, Fin.cast, srcFormula,
      paperRetainedOriginalClauseIndexOrder, finCongr, List.get_eq_getElem, List.getElem_attach,
          List.getElem_map]
  rfl

end PhysicalShiftedCanonicalRetainedClauseSourceCorrectness

open GapCVP.PhysicalShiftedCanonicalRetainedClauseSourceCorrectness

local notation "retainedClause_source" =>
  paperFormulaRetainedClause_retainedOriginal

namespace PhysicalShiftedCanonicalInterpolationBaseSourceFormulaTransport

open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.CanonicalOffsetIdentity
open GapCVP.PhysicalShiftedCanonicalInterpolationBaseSourceWordSemanticBridge

private theorem paperVariableArityNormalizedClauseTupleTransport_sourceBit
    (formula : ThreeCNF)
    (normalized : List GapCVP.Literal)
    (membership : normalized ∈ paperSourceNormalizedClauses formula)
    (target : GapCVP.Core.Clause (paperVariableArityVariableCount formula))
    (equality : paperVariableAritySourceClause
      formula normalized membership = target)
    (tuple : Fin (2 ^ normalized.length - 1))
    (position : Fin normalized.length) :
    ((equality ▸ sourceClauseTupleWordOrder
      formula normalized membership) tuple).val
      ((equality ▸ paperLocalVariableWordOrder
        formula normalized membership) position) =
      (paperSatisfyingWordOrder normalized.length
        (fun index => (normalized.get index).2) tuple).val position := by
  subst target
  exact paperVariableAritySourceClauseTupleWordOrder_apply_localVariable
    formula normalized membership tuple position

private theorem paperVariableArityNormalizedClauseVariableTransport_sourceRank
    (formula : ThreeCNF)
    (normalized : List GapCVP.Literal)
    (membership : normalized ∈ paperSourceNormalizedClauses formula)
    (target : GapCVP.Core.Clause (paperVariableArityVariableCount formula))
    (equality : paperVariableAritySourceClause
      formula normalized membership = target)
    (position : Fin normalized.length) :
    ((equality ▸ paperLocalVariableWordOrder
      formula normalized membership) position).val.val =
        paperVariableArityVariableRank formula
          (normalized.get position).1 := by
  subst target
  rfl

private theorem paperVariableArityFormulaClauseTupleWordOrder_sourceBit
    (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length)
    (tuple : Fin (2 ^ paperFormulaClauseWidth formula clause - 1))
    (position : Fin (paperFormulaClauseWidth formula clause)) :
    (paperFormulaClauseTupleWordOrder
      formula clause tuple).val
        (paperFormulaClauseVariableWordOrder
          formula clause position) =
      (paperSatisfyingWordOrder
        (paperFormulaClauseWidth formula clause)
        (fun index =>
          ((paperFormulaRetainedClause
            formula clause).val.get
              ⟨index.val, by
                exact index.isLt⟩).2)
        tuple).val position := by
  let retained := paperFormulaRetainedClause formula clause
  have equality := paperFormulaRetainedClause_sourceClause
    formula clause
  change
    (paperFormulaClauseTupleWordOrder
      formula clause tuple).val
        (paperFormulaClauseVariableWordOrder
          formula clause position) =
      (paperSatisfyingWordOrder retained.val.length
        (fun index => (retained.val.get index).2) tuple).val position
  unfold paperFormulaClauseTupleWordOrder
    paperFormulaClauseVariableWordOrder
  change
    ((equality ▸
      sourceClauseTupleWordOrder
        formula retained.val retained.property) tuple).val
      ((equality ▸
        paperLocalVariableWordOrder
          formula retained.val retained.property) position) = _
  exact paperVariableArityNormalizedClauseTupleTransport_sourceBit
    formula retained.val retained.property
    ((srcFormula formula).clauses.get clause)
    equality tuple position

private theorem paperVariableArityFormulaClauseVariableWordOrder_sourceVariableRank
    (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length)
    (position : Fin (paperFormulaClauseWidth formula clause)) :
    (paperFormulaClauseVariableWordOrder
      formula clause position).val.val =
      paperVariableArityVariableRank formula
        (((paperFormulaRetainedClause formula clause).val.get
          ⟨position.val, by
            exact position.isLt⟩).1) := by
  let retained := paperFormulaRetainedClause formula clause
  have equality := paperFormulaRetainedClause_sourceClause
    formula clause
  change
    (paperFormulaClauseVariableWordOrder
      formula clause position).val.val =
      paperVariableArityVariableRank formula
        (retained.val.get position).1
  unfold paperFormulaClauseVariableWordOrder
  change
    ((equality ▸
      paperLocalVariableWordOrder
        formula retained.val retained.property) position).val.val = _
  exact paperVariableArityNormalizedClauseVariableTransport_sourceRank
    formula retained.val retained.property
    ((srcFormula formula).clauses.get clause)
    equality position

end PhysicalShiftedCanonicalInterpolationBaseSourceFormulaTransport

namespace PhysicalShiftedCanonicalBetaSourceCorrectness

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge GapCVP.SourceOrder
open GapCVP.CanonicalOffsetIdentity GapCVP.SatisfyingWordSourceRankSemantics
open GapCVP.ShiftedTupleBetaTM GapCVP.ShiftedTupleBetaSourceCorrectness
open GapCVP.ShiftedTupleAnchorSourceFieldCorrectness GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalShiftedRowTupleRankTM GapCVP.PhysicalShiftedRowTupleRankBounds
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowCanonicalSourceDigits
open GapCVP.PhysicalShiftedInterpolationRowCanonicalSourceTupleDigits
open GapCVP.PhysicalShiftedCanonicalInterpolationBaseSourceFormulaTransport
open GapCVP.PhysicalShiftedInterpolationBaseInstantiation

private theorem paperVariableArityPhysicalShiftedSourceRowCanonicalBeta_eq
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    physicalShiftedRowBetaBit
      formula row.val
      (physicalShiftedRowClauseRank_lt_of_fin
        formula row inShifted) =
      (physicalShiftedSourceRowTuple
        formula row inShifted).val
        (physicalShiftedSourceRowLocalVariable
          formula row inShifted) := by
  classical
  let bounded := physicalShiftedRowClauseRank_lt_of_fin
    formula row inShifted
  let sourceClause := physicalShiftedSourceRowClause
    formula row inShifted
  let original : Fin (noTautClauses formula).length :=
    ⟨physicalShiftedRowClauseRank formula row.val,
      bounded⟩
  let tuple :=
    (paperFormulaClauseTupleWordOrder
      formula sourceClause).symm
        (physicalShiftedSourceRowTuple
          formula row inShifted)
  let position :=
    (paperFormulaClauseVariableWordOrder
      formula sourceClause).symm
        (physicalShiftedSourceRowLocalVariable
          formula row inShifted)
  have index :
      paperRetainedOriginalClauseIndexOrder formula original =
        sourceClause := by
    apply Fin.ext
    exact paperVariableArityPhysicalShiftedSourceRowClauseRank_eq
      formula row inShifted
  have width :
      physicalShiftedRowSelectedClauseArity
        formula row.val bounded =
        paperFormulaClauseWidth formula sourceClause := by
    unfold physicalShiftedRowSelectedClauseArity
    rw [← index]
    exact
      (paperFormulaClauseWidth_retainedOriginal
        formula original).symm
  have tupleRank :
      physicalShiftedRowTupleRank
        formula row.val bounded = tuple.val :=
    paperVariableArityPhysicalShiftedSourceRowTupleRank_eq
      formula row inShifted
  have localRank :
      physicalShiftedRowVariablePosition
        formula row.val bounded = position.val :=
    paperVariableArityPhysicalShiftedSourceRowLocalVariableRank_eq
      formula row inShifted
  have retained :
      (paperFormulaRetainedClause
        formula sourceClause).val =
        paperSourceNormalizedClause
          ((noTautClauses formula).get original) := by
    rw [← index]
    exact retainedClause_source
      formula original
  have sign :
      paperVariableArityBoundedSourceSign
        (paperFormulaClauseWidth formula sourceClause)
        (by
          rw [← width]
          exact paper_retainedClause_length_le_three formula
            (paperSourceNormalizedClause
              ((noTautClauses formula).get original))
            (paperShiftedTupleRetainedNormalizedClause_mem
              formula original.val original.isLt))
        (physicalShiftedRowNormalizedSign
          formula row.val bounded) =
        (fun index : Fin
          (paperFormulaClauseWidth formula sourceClause) =>
            ((paperFormulaRetainedClause
              formula sourceClause).val.get
              ⟨index.val, index.isLt⟩).2) := by
    funext slot
    unfold paperVariableArityBoundedSourceSign
      physicalShiftedRowNormalizedSign
    have normalized :
        slot.val <
          (paperSourceNormalizedClause
            ((noTautClauses formula).get
              original)).length := by
      rw [← paperFormulaClauseWidth_retainedOriginal
        formula original, index]
      exact slot.isLt
    have actual :=
      paperVariableArityShiftedTuplePotentialNormalizedLiteral_get
        ((noTautClauses formula).get original)
        ⟨slot.val, by
          have bound :=
            paper_retainedClause_length_le_three formula
              (paperSourceNormalizedClause
                ((noTautClauses formula).get original))
              (paperShiftedTupleRetainedNormalizedClause_mem
                formula original.val original.isLt)
          exact Nat.lt_of_lt_of_le normalized bound⟩
        normalized
    have bits := congrArg (fun literal : GapCVP.Literal => literal.2)
      actual
    simpa only [List.get_eq_getElem, Fin.eta, retained] using bits
  have word := paperVariableAritySatisfyingWordOrder_apply_eq_shiftedTupleBetaBit
    (paperFormulaClauseWidth formula sourceClause)
    (by
      rw [← width]
      exact paper_retainedClause_length_le_three formula
        (paperSourceNormalizedClause
          ((noTautClauses formula).get original))
        (paperShiftedTupleRetainedNormalizedClause_mem
          formula original.val original.isLt))
    (physicalShiftedRowNormalizedSign
      formula row.val bounded)
    tuple position
  rw [sign] at word
  have source := paperVariableArityFormulaClauseTupleWordOrder_sourceBit
    formula sourceClause tuple position
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at source
  unfold physicalShiftedRowBetaBit
  change
    (physicalShiftedRowTupleRank formula row.val bounded +
      if physicalShiftedRowTupleRank formula row.val bounded <
        paperShiftedTupleRejectedNatural
          (physicalShiftedRowSelectedClauseArity
            formula row.val bounded)
          (physicalShiftedRowNormalizedSign
            formula row.val bounded)
      then 0 else 1).testBit
        (physicalShiftedRowVariablePosition
          formula row.val bounded) = _
  rw [tupleRank, localRank, width]
  exact word.symm.trans source.symm

end PhysicalShiftedCanonicalBetaSourceCorrectness

namespace PhysicalShiftedCanonicalAnchorSourceCorrectness

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinarySourceTautologyNormalizationExact
open GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge GapCVP.CanonicalOffsetIdentity
open GapCVP.SourceOrder GapCVP.ShiftedTupleAnchorSourceFieldCorrectness
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalShiftedRowTupleRankTM
open GapCVP.PhysicalShiftedRowTupleRankBounds
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationRowCanonicalSourceDigits
open GapCVP.PhysicalShiftedInterpolationRowCanonicalSourceTupleDigits
open GapCVP.PhysicalShiftedCanonicalInterpolationBaseSourceFormulaTransport

private theorem paperVariableArityPhysicalShiftedRetainedGet_eq
    {α : Type*} (first second : List α)
    (same : first = second)
    (firstIndex : Fin first.length)
    (secondIndex : Fin second.length)
    (rank : firstIndex.val = secondIndex.val) :
    first.get firstIndex = second.get secondIndex := by
  subst second
  have equal : firstIndex = secondIndex := Fin.ext rank
  rw [equal]

private theorem paperVariableArityPhysicalShiftedSourceRowCanonicalAnchor_eq
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    paperShiftedTupleSelectedSourceVariableIndex
      formula
      (physicalShiftedRowClauseRank formula row.val)
      (physicalShiftedRowClauseRank_lt_of_fin
        formula row inShifted)
      (physicalShiftedRowVariablePosition
        formula row.val
        (physicalShiftedRowClauseRank_lt_of_fin
          formula row inShifted))
      (physicalShiftedRowVariablePosition_lt_normalized
        formula row.val
        (physicalShiftedRowClauseRank_lt_of_fin
          formula row inShifted)) =
      (physicalShiftedSourceRowLocalVariable
        formula row inShifted).val := by
  classical
  let bounded := physicalShiftedRowClauseRank_lt_of_fin
    formula row inShifted
  let sourceClause := physicalShiftedSourceRowClause
    formula row inShifted
  let original : Fin (noTautClauses formula).length :=
    ⟨physicalShiftedRowClauseRank formula row.val,
      bounded⟩
  let sourcePosition :=
    (paperFormulaClauseVariableWordOrder
      formula sourceClause).symm
      (physicalShiftedSourceRowLocalVariable
        formula row inShifted)
  have sourceIndex :
      paperRetainedOriginalClauseIndexOrder
          formula original = sourceClause := by
    apply Fin.ext
    exact paperVariableArityPhysicalShiftedSourceRowClauseRank_eq
      formula row inShifted
  have retained :
      (paperFormulaRetainedClause
        formula sourceClause).val =
      paperSourceNormalizedClause
        ((noTautClauses formula).get original) := by
    rw [← sourceIndex]
    exact retainedClause_source
      formula original
  have positionRank :
      physicalShiftedRowVariablePosition
          formula row.val bounded = sourcePosition.val :=
    paperVariableArityPhysicalShiftedSourceRowLocalVariableRank_eq
      formula row inShifted
  let normalized := paperSourceNormalizedClause
    ((noTautClauses formula).get original)
  let retainedClause :=
    (paperFormulaRetainedClause
      formula sourceClause).val
  let physicalPosition : Fin normalized.length :=
    ⟨physicalShiftedRowVariablePosition
      formula row.val bounded,
      physicalShiftedRowVariablePosition_lt_normalized
        formula row.val bounded⟩
  let retainedPosition : Fin retainedClause.length :=
    ⟨sourcePosition.val, by
      exact sourcePosition.isLt⟩
  have sameLiteral :
      normalized.get physicalPosition =
        retainedClause.get retainedPosition :=
    paperVariableArityPhysicalShiftedRetainedGet_eq
      normalized retainedClause retained.symm
      physicalPosition retainedPosition positionRank
  have source :=
    paperVariableArityFormulaClauseVariableWordOrder_sourceVariableRank
      formula sourceClause sourcePosition
  rw [Equiv.apply_symm_apply] at source
  apply Fin.ext
  change
    paperVariableArityVariableRank formula
      (normalized.get physicalPosition).1 =
      (physicalShiftedSourceRowLocalVariable
        formula row inShifted).val.val
  rw [source]
  exact congrArg (fun literal : GapCVP.Literal =>
    paperVariableArityVariableRank formula literal.1) sameLiteral

end PhysicalShiftedCanonicalAnchorSourceCorrectness

namespace PhysicalShiftedCanonicalInterpolationBaseSemanticCorrectness

open GapCVP.Core hiding sourceFormulaField
open GapCVP.BinaryEncoding GapCVP.BinaryFieldInverseAlgebra
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.FormulaBridge GapCVP.SourceOrder
open GapCVP.PhysicalLagrangeNodeProductAlgebra GapCVP.PhysicalFamilyRowTM
open GapCVP.PhysicalShiftedInterpolationRowFieldCorrectness
open GapCVP.PhysicalShiftedCanonicalBetaSourceCorrectness
open GapCVP.PhysicalShiftedCanonicalAnchorSourceCorrectness
open GapCVP.PhysicalShiftedInterpolationBaseSourceFieldCorrectness
open GapCVP.PhysicalInterpolationColumnSourceFieldCorrectness
open GapCVP.PhysicalShiftedInterpolationParityMaskedFieldCorrectness

theorem
    paperVariableArityPhysicalShiftedFiniteRowCanonicalBaseSourceWord_eq_decodedSourceRatio
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin (sourceFormulaDimension
      (encodeThreeCNF formula).length
      (srcFormula formula)))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    sourceWordValue (encodeThreeCNF formula).length
      (srcFormula formula)
      (physicalShiftedFiniteRowCanonicalBaseSourceWord
        formula row column inShifted) =
      ((sourceCoordinateWordOrder
          (encodeThreeCNF formula).length formula column).2.2 -
        sourceSATFieldBit
          (K := GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
            (encodeThreeCNF formula).length
            (srcFormula formula))
          ((physicalShiftedSourceRowTuple
            formula row inShifted).val
            (physicalShiftedSourceRowLocalVariable
              formula row inShifted))) /
        (((sourceCoordinateWordOrder
            (encodeThreeCNF formula).length formula column).2.1).val -
          GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
            (encodeThreeCNF formula).length
            (srcFormula formula)
            (physicalShiftedSourceRowLocalVariable
              formula row inShifted).val) := by
  unfold physicalShiftedFiniteRowCanonicalBaseSourceWord
  rw [paperVariableArityPhysicalShiftedCanonicalInterpolationBaseSourceWord_sourceField,
    paperVariableArityPhysicalInterpolationColumnValueSourceWord_sourceField
      formula column,
    paperVariableArityPhysicalShiftedSourceRowCanonicalBeta_eq
      formula row inShifted,
    paperVariableArityPhysicalShiftedSourceRowCanonicalAnchor_eq
      formula row inShifted]
  have grid :=
    paperVariableArityPhysicalInterpolationColumnGridSourceWord_sourceField
      formula column
  rw [paperVariableArityPhysicalShiftedColumnGridSourceWord_eq_evaluationWord,
    physicalLagrangeNodeEvaluationWord_sourceField] at grid
  rw [grid]

end PhysicalShiftedCanonicalInterpolationBaseSemanticCorrectness

namespace PhysicalOrdinaryShiftedCheckBitInstantiation

open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.FormulaBridge GapCVP.MatrixEntrySemantics
open GapCVP.PhysicalColumnOrder GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM
open GapCVP.PhysicalInterpolationDirectMomentBitTM GapCVP.PhysicalInterpolationNodeCountBounds
open GapCVP.PhysicalMaskedInterpolationNodeParityTM
open GapCVP.PhysicalOrdinaryShiftedCoefficientSumTM GapCVP.PhysicalShiftedExpectedTypeRankTM
open GapCVP.PhysicalShiftedInterpolationBinaryCheckBitCorrectness
open GapCVP.PhysicalShiftedCanonicalInterpolationBaseSemanticCorrectness
open GapCVP.PhysicalShiftedInterpolationBinaryHCoreCorrectness
open GapCVP.PhysicalShiftedInterpolationBaseInstantiation
open GapCVP.PhysicalShiftedInterpolationParityMaskedFieldCorrectness
open GapCVP.PhysicalShiftedRowTupleRankBounds GapCVP.SourceFieldMomentOperationsTM
open GapCVP.SourceOrder

private noncomputable def physicalShiftedSourceCorrectionField
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    PaperVariableArityPhysicalWordField
      (encodeThreeCNF formula).length formula :=
  paperVariableArityPhysicalShiftedActualSourceCorrectionField
    formula row column inShifted

private theorem paperVariableArityPhysicalShiftedFiniteRowBaseComputer_valid
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    physicalShiftedCanonicalInterpolationBaseComputer.output
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      finiteWordBits
        (physicalShiftedFiniteRowCanonicalBaseSourceWord
          formula row column inShifted) := by
  exact paperVariableArityPhysicalShiftedCheckBase_on_physical_row
    formula row column
    (physicalShiftedRowClauseRank_lt_of_fin
      formula row inShifted)

private theorem paperVariableArityPhysicalShiftedCorrectionBit_sourceCorrection
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    physicalInterpolationNodeCorrectionBit
        (3 : Fin 4)
        (physicalShiftedNodePrefixWidth
          physicalShiftedInterpolationMomentComputer)
        physicalShiftedCanonicalInterpolationBaseComputer
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
          (encodeThreeCNF formula).length
          (srcFormula formula)).equivFun
            (physicalShiftedSourceCorrectionField
              formula row column inShifted)
            (physicalInterpolationRowBasisIndex
              row.val formula) = (1 : ZMod 2))] := by
  exact paperVariableArityPhysicalInterpolationNodeCorrectionBit_sourceField_valid
    (3 : Fin 4)
    (physicalShiftedNodePrefixWidth
      physicalShiftedInterpolationMomentComputer)
    physicalShiftedCanonicalInterpolationBaseComputer
    row.val column.val formula
    (physicalShiftedInterpolationNodeCount
      row.val formula)
    (paperVariableArityPhysicalShiftedInterpolationNodeWidth_valid
      row.val column.val formula)
    (physicalShiftedInterpolationNodeCount_le_grid
      formula row.val)
    (physicalShiftedFiniteRowCanonicalBaseSourceWord
      formula row column inShifted)
    (paperVariableArityPhysicalShiftedFiniteRowBaseComputer_valid
      formula row column inShifted)

private noncomputable def physicalShiftedSourceExpectedTypeBit
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    Bool :=
  decide
    (physicalShiftedExpectedTableTypeRank
        formula row.val
        (physicalShiftedRowClauseRank_lt_of_fin
          formula row inShifted) =
      (column.val /
        physFieldCard formula) /
        physGridCard formula)

private theorem paperVariableArityPhysicalShiftedExpectedTypeMatch_sourceExpected
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    physicalInterpolationExpectedTypeMatchBit
        physicalShiftedExpectedTableTypeRankComputer
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [physicalShiftedSourceExpectedTypeBit
        formula row column inShifted] := by
  exact paperVariableArityPhysicalShiftedExpectedTypeMatchBit_valid
    formula row column
    (physicalShiftedRowClauseRank_lt_of_fin
      formula row inShifted)

private noncomputable def physicalShiftedSourceDirectBit
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    Bool :=
  decide
    ((((row.val - physicalFamilyStart
          (3 : Fin 4) formula) /
        physDegree formula) %
        physGridCard formula) =
      ((column.val /
          physFieldCard formula) %
        physGridCard formula)) &&
    (sourceWordPow
      (physicalShiftedFiniteRowCanonicalBaseSourceWord
        formula row column inShifted)
      (physicalFamilyRowMoment
        (3 : Fin 4) row.val formula))
      (physicalInterpolationRowBasisIndex
        row.val formula)

private theorem paperVariableArityPhysicalShiftedDirectMomentBit_sourceDirect
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    physicalFamilyDirectMomentBit
        (3 : Fin 4)
        physicalShiftedCanonicalInterpolationBaseComputer
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [physicalShiftedSourceDirectBit
        formula row column inShifted] := by
  exact paperVariableArityPhysicalFamilyDirectMomentBit_valid
    (3 : Fin 4)
    physicalShiftedCanonicalInterpolationBaseComputer
    row.val column.val formula
    (physicalShiftedFiniteRowCanonicalBaseSourceWord
      formula row column inShifted)
    (physicalInterpolationRowBasisIndex
      row.val formula)
    rfl
    (paperVariableArityPhysicalShiftedFiniteRowBaseComputer_valid
      formula row column inShifted)

private theorem paperVariableArityPhysicalShiftedCheckBit_actualSourceBits
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val) :
    physicalShiftedCheckBit
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [physicalShiftedSourceExpectedTypeBit
          formula row column inShifted &&
       Bool.xor
        (physicalShiftedSourceDirectBit
          formula row column inShifted)
        (decide
          ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
            (encodeThreeCNF formula).length
            (srcFormula formula)).equivFun
              (physicalShiftedSourceCorrectionField
                formula row column inShifted)
              (physicalInterpolationRowBasisIndex
                row.val formula) = (1 : ZMod 2)))] := by
  have marker :
      physicalShiftedRowMarker
          (affineCellQuery row.val column.val
            (encodeThreeCNF formula)) = [true] := by
    rw [paperVariableArityPhysicalShiftedRowMarker_query]
    simp only [inShifted, decide_true]
  exact paperVariableArityPhysicalSourceInterpolationFamilyCheckBit_bits
    (3 : Fin 4)
    physicalShiftedRowMarker
    physicalShiftedExpectedTableTypeRankComputer
    (physicalShiftedNodePrefixWidth
      physicalShiftedInterpolationMomentComputer)
    physicalShiftedCanonicalInterpolationBaseComputer
    (affineCellQuery row.val column.val
      (encodeThreeCNF formula))
    true
    (physicalShiftedSourceExpectedTypeBit
      formula row column inShifted)
    (physicalShiftedSourceDirectBit
      formula row column inShifted)
    (decide
      ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
        (encodeThreeCNF formula).length
        (srcFormula formula)).equivFun
          (physicalShiftedSourceCorrectionField
            formula row column inShifted)
          (physicalInterpolationRowBasisIndex
            row.val formula) = (1 : ZMod 2)))
    marker
    (paperVariableArityPhysicalShiftedExpectedTypeMatch_sourceExpected
      formula row column inShifted)
    (paperVariableArityPhysicalShiftedDirectMomentBit_sourceDirect
      formula row column inShifted)
    (paperVariableArityPhysicalShiftedCorrectionBit_sourceCorrection
      formula row column inShifted)

private theorem paperVariableArityPhysicalShiftedCheckBit_valid_of_binary
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula))
    (correct : ∀ inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val,
      decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).check
            row column = (1 : ZMod 2)) =
        (physicalShiftedSourceExpectedTypeBit
          formula row column inShifted &&
        Bool.xor
          (physicalShiftedSourceDirectBit
            formula row column inShifted)
          (decide
            ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
              (encodeThreeCNF formula).length
              (srcFormula formula)).equivFun
                (physicalShiftedSourceCorrectionField
                  formula row column inShifted)
                (physicalInterpolationRowBasisIndex
                  row.val formula) = (1 : ZMod 2))))) :
    physicalShiftedCheckBit
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        (physicalFormulaOrdinaryBoundary formula ≤
          row.val) &&
       decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).check
            row column = (1 : ZMod 2))] := by
  by_cases inShifted :
      physicalFormulaOrdinaryBoundary formula ≤ row.val
  · have bits := paperVariableArityPhysicalShiftedCheckBit_actualSourceBits
      formula row column inShifted
    have actual := correct inShifted
    calc
      physicalShiftedCheckBit
          (affineCellQuery row.val column.val
            (encodeThreeCNF formula)) =
          [decide
            ((physicalWordBinarySystem
              (encodeThreeCNF formula).length formula).check
                row column = (1 : ZMod 2))] :=
            bits.trans (congrArg (fun bit : Bool => [bit]) actual.symm)
      _ = _ := by simp only [inShifted,
          decide_true, Bool.true_and]
  · calc
      physicalShiftedCheckBit
          (affineCellQuery row.val column.val
            (encodeThreeCNF formula)) = [false] :=
            paperVariableArityPhysicalShiftedCheckBit_of_not_in_family
              formula row.val column.val inShifted
      _ = _ := by simp only [inShifted, decide_false,
          Bool.false_and]

/-- Internal support shared across GapCVP continuation modules. -/
theorem paperVariableArityPhysicalShiftedCheckBit_valid
    (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula)) :
    physicalShiftedCheckBit
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        (physicalFormulaOrdinaryBoundary formula ≤
          row.val) &&
       decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).check
            row column = (1 : ZMod 2))] := by
  apply paperVariableArityPhysicalShiftedCheckBit_valid_of_binary
    formula row column
  intro inShifted
  have correction :
      physicalShiftedSourceCorrectionField
        formula row column inShifted =
      paperVariableArityPhysicalShiftedActualSourceCorrectionField
        formula row column inShifted := by
    rfl
  rw [correction]
  have ratio :=
    paperVariableArityPhysicalShiftedFiniteRowCanonicalBaseSourceWord_eq_decodedSourceRatio
      formula row column inShifted
  exact paperVariableArityPhysicalShiftedActualBinaryCheckBit_decide_of_sourceRatio
    formula row column inShifted ratio

end PhysicalOrdinaryShiftedCheckBitInstantiation

end GapCVP

end
