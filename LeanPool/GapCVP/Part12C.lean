/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part12B

/-! # GapCVP proof, part 12, continuation 03 -/

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace SourceOrder

open scoped BigOperators

open GapCVP.Core GapCVP.BinaryFieldBasis GapCVP.BinarySourceCoordinateOrder

open GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryOrderedAssembly

open GapCVP.BinaryOrderedRefinement GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge

open GapCVP.ClauseCardinality

/-- GapCVP reduction support. -/
def sourceTypeCardWordOrder
    (formula : ThreeCNF) :
    Fin (Fintype.card
      (sourceSATTableType (srcFormula formula))) ≃
        sourceSATTableType (srcFormula formula) :=
  (finCongr (sourceTableType_card formula)).trans
    (sourceTypeWordOrder formula)

/-- GapCVP reduction support. -/
def sourceCoordinateWordOrder
    (encodingLength : ℕ) (formula : ThreeCNF) :
    Fin (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
      encodingLength (srcFormula formula)) ≃
      sourceSATTableCoordinate (srcFormula formula)
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
          encodingLength (srcFormula formula))
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
          encodingLength (srcFormula formula)) :=
  sourceFormulaCoordinateOrder
    encodingLength (srcFormula formula)
    (sourceTypeCardWordOrder formula)

private def paperVariableArityLocalVariableMomentWordOrder
    (formula : ThreeCNF) (momentBudget : ℕ)
    (index : Fin (srcFormula formula).clauses.length) :
    Fin (paperFormulaClauseWidth formula index *
      (momentBudget + 1)) ≃
      ((srcFormula
        formula).clauses.get index).LocalVariable ×
        Fin (momentBudget + 1) :=
  (finProdFinEquiv
    (m := paperFormulaClauseWidth formula index)
    (n := momentBudget + 1)).symm.trans
      ((paperFormulaClauseVariableWordOrder
        formula index).prodCongr
          (Equiv.refl (Fin (momentBudget + 1))))

/-- GapCVP reduction support. -/
def paperShiftedClauseTagCount
    (formula : ThreeCNF) (momentBudget : ℕ)
    (index : Fin (srcFormula formula).clauses.length) : ℕ :=
  (2 ^ paperFormulaClauseWidth formula index - 1) *
    (paperFormulaClauseWidth formula index *
      (momentBudget + 1))

/-- GapCVP reduction support. -/
def paperShiftedClauseWordOrder
    (formula : ThreeCNF) (momentBudget : ℕ)
    (index : Fin (srcFormula formula).clauses.length) :
    Fin (paperShiftedClauseTagCount
      formula momentBudget index) ≃
      (Σ _tuple :
        ((srcFormula
          formula).clauses.get index).SatisfyingLocalTuple,
        ((srcFormula
          formula).clauses.get index).LocalVariable ×
          Fin (momentBudget + 1)) := by
  change Fin
    ((2 ^ paperFormulaClauseWidth formula index - 1) *
      (paperFormulaClauseWidth formula index *
        (momentBudget + 1))) ≃ _
  exact (finProdFinEquiv
    (m := 2 ^ paperFormulaClauseWidth formula index - 1)
    (n := paperFormulaClauseWidth formula index *
      (momentBudget + 1))).symm.trans
    ((Equiv.sigmaEquivProd
      (Fin (2 ^ paperFormulaClauseWidth formula index - 1))
      (Fin (paperFormulaClauseWidth formula index *
        (momentBudget + 1)))).symm.trans
      (Equiv.sigmaCongr
        (paperFormulaClauseTupleWordOrder formula index)
        (fun _ => paperVariableArityLocalVariableMomentWordOrder
          formula momentBudget index)))

/-- GapCVP reduction support. -/
def paperShiftedFamilyTagCount
    (formula : ThreeCNF) (momentBudget : ℕ) : ℕ :=
  ∑ index : Fin (srcFormula formula).clauses.length,
    paperShiftedClauseTagCount
      formula momentBudget index

/-- GapCVP reduction support. -/
def paperShiftedFamilyWordOrder
    (formula : ThreeCNF) (momentBudget : ℕ) :
    Fin (paperShiftedFamilyTagCount
      formula momentBudget) ≃
      (Σ clause : Fin (srcFormula formula).clauses.length,
        Σ _tuple :
          ((srcFormula
            formula).clauses.get clause).SatisfyingLocalTuple,
        ((srcFormula
          formula).clauses.get clause).LocalVariable ×
          Fin (momentBudget + 1)) := by
  change Fin
    (∑ index : Fin (srcFormula formula).clauses.length,
      paperShiftedClauseTagCount
        formula momentBudget index) ≃ _
  exact finSigmaFinEquiv.symm.trans
    (Equiv.sigmaCongrRight fun clause =>
      paperShiftedClauseWordOrder
        formula momentBudget clause)

/-- GapCVP reduction support. -/
def paperOrdinaryFamilyWordOrder
    (formula : ThreeCNF) (momentBudget : ℕ) :
    Fin ((1 + paperVariableArityLocalTagCount formula) *
      (momentBudget + 1)) ≃
        sourceSATTableType (srcFormula formula) ×
          Fin (momentBudget + 1) :=
  (finProdFinEquiv
    (m := 1 + paperVariableArityLocalTagCount formula)
    (n := momentBudget + 1)).symm.trans
      ((sourceTypeWordOrder formula).prodCongr
        (Equiv.refl (Fin (momentBudget + 1))))

/-- GapCVP reduction support. -/
def paperExplicitFamilyTagCount
    (encodingLength : ℕ) (formula : ThreeCNF) : ℕ :=
  let budget :=
    explicitMomentBudget encodingLength
      (srcFormula formula)
  1 + ((srcFormula formula).clauses.length +
    ((1 + paperVariableArityLocalTagCount formula) * (budget + 1) +
      paperShiftedFamilyTagCount formula budget))

/-- GapCVP reduction support. -/
def paperExplicitFamilyWordOrder
    (encodingLength : ℕ) (formula : ThreeCNF) :
    Fin (paperExplicitFamilyTagCount
      encodingLength formula) ≃
        ExplicitConstraintFamily
          encodingLength (srcFormula formula) := by
  let budget :=
    explicitMomentBudget encodingLength
      (srcFormula formula)
  change Fin
    (1 + ((srcFormula formula).clauses.length +
      ((1 + paperVariableArityLocalTagCount formula) * (budget + 1) +
        paperShiftedFamilyTagCount formula budget))) ≃ _
  exact (finSumFinEquiv
    (m := 1)
    (n := (srcFormula formula).clauses.length +
      ((1 + paperVariableArityLocalTagCount formula) * (budget + 1) +
        paperShiftedFamilyTagCount formula budget))).symm.trans
    (Equiv.sumCongr finOneEquiv
      ((finSumFinEquiv
        (m := (srcFormula formula).clauses.length)
        (n := (1 + paperVariableArityLocalTagCount formula) * (budget + 1) +
          paperShiftedFamilyTagCount
            formula budget)).symm.trans
        (Equiv.sumCongr
          (Equiv.refl
            (Fin (srcFormula formula).clauses.length))
          ((finSumFinEquiv
            (m := (1 + paperVariableArityLocalTagCount formula) *
              (budget + 1))
            (n := paperShiftedFamilyTagCount
              formula budget)).symm.trans
            (Equiv.sumCongr
              (paperOrdinaryFamilyWordOrder
                formula budget)
              (paperShiftedFamilyWordOrder
                formula budget))))))

/-- GapCVP reduction support. -/
abbrev paperExplicitBinaryRowDegree
    (encodingLength : ℕ) (formula : ThreeCNF) : ℕ :=
  sourceFieldExponent
    (sourceSizeParameter encodingLength
      (srcFormula formula))

/-- GapCVP reduction support. -/
def paperExplicitBinaryFamilyBlockCount
    (encodingLength : ℕ) (formula : ThreeCNF)
    (index : Fin
      (paperExplicitFamilyTagCount encodingLength formula)) : ℕ :=
  explicitFamilyRowCount
    encodingLength (srcFormula formula)
      (paperExplicitFamilyWordOrder
        encodingLength formula index) *
    paperExplicitBinaryRowDegree encodingLength formula

/-- GapCVP reduction support. -/
def paperExplicitBinaryRowWordCount
    (encodingLength : ℕ) (formula : ThreeCNF) : ℕ :=
  ∑ index : Fin
    (paperExplicitFamilyTagCount encodingLength formula),
    paperExplicitBinaryFamilyBlockCount
      encodingLength formula index

/-- GapCVP reduction support. -/
def paperVariableArityExplicitBinaryRowWordOrder
    (encodingLength : ℕ) (formula : ThreeCNF) :
    Fin (paperExplicitBinaryRowWordCount
      encodingLength formula) ≃
      assembledBinaryRow
        (explicitFamilyRowCount
          encodingLength (srcFormula formula))
        (paperExplicitBinaryRowDegree
          encodingLength formula) := by
  let familyOrder :=
    paperExplicitFamilyWordOrder
      encodingLength formula
  change Fin
    (∑ index : Fin
      (paperExplicitFamilyTagCount encodingLength formula),
      explicitFamilyRowCount
        encodingLength (srcFormula formula)
          (familyOrder index) *
        paperExplicitBinaryRowDegree
          encodingLength formula) ≃ _
  exact finSigmaFinEquiv.symm.trans
    (Equiv.sigmaCongr familyOrder (fun index =>
      (finProdFinEquiv
        (m := explicitFamilyRowCount
          encodingLength (srcFormula formula)
          (familyOrder index))
        (n := paperExplicitBinaryRowDegree
          encodingLength formula)).symm))

/-- GapCVP reduction support. -/
def physicalBinarySystem
    (encodingLength : ℕ) (formula : ThreeCNF) : BinaryAffineSystem :=
  assembledBinaryAffineSystemOrdered
    (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
      encodingLength (srcFormula formula))
    (explicitFamilyRowCount
      encodingLength (srcFormula formula))
    (sourceFormulaPhysicalFamilyFieldMatrix
      encodingLength (srcFormula formula))
    (explicitFamilyTarget
      encodingLength (srcFormula formula))
    (paperVariableArityExplicitBinaryRowWordOrder
      encodingLength formula)

private theorem paperVariableArityPhysicalBinarySystem_solves_iff_explicit
    (encodingLength : ℕ) (formula : ThreeCNF)
    (values : Fin
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength (srcFormula formula)) → ℤ) :
    (physicalBinarySystem
      encodingLength formula).Solves values ↔
      (sourceFormulaExplicitBinarySystem
        encodingLength (srcFormula formula)).Solves values := by
  unfold physicalBinarySystem
  rw [assembledBinaryAffineSystemOrdered_solves_iff]
  rw [sourceFormulaExplicitBinarySystem_solves_iff_family]
  simp only [sourceFormulaPhysicalFamilyFieldMatrix,
    LinearMap.toMatrix'_mulVec]
  constructor
  · intro hphysical family
    exact (sourceFormulaPhysicalFamilyLinearMap_eq_iff_explicit
      encodingLength (srcFormula formula) family
      (fun position => algebraMap (ZMod 2)
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
          encodingLength (srcFormula formula))
        (values position : ZMod 2))).mp (hphysical family)
  · intro hexplicit family
    exact (sourceFormulaPhysicalFamilyLinearMap_eq_iff_explicit
      encodingLength (srcFormula formula) family
      (fun position => algebraMap (ZMod 2)
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
          encodingLength (srcFormula formula))
        (values position : ZMod 2))).mpr (hexplicit family)

end SourceOrder

namespace PhysicalColumnOrder

open GapCVP.Core GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryExplicitFourFamilyKernel
open GapCVP.FormulaBridge GapCVP.SourceOrder

/-- GapCVP reduction support. -/
abbrev physicalColumnPermutation
    (encodingLength : ℕ) (formula : ThreeCNF) :
    Fin
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength (srcFormula formula)) ≃
    Fin
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength (srcFormula formula)) :=
  (sourceCoordinateWordOrder
    encodingLength formula).trans
      (Fintype.equivFin
        (sourceSATTableCoordinate (srcFormula formula)
          (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
            encodingLength (srcFormula formula))
          (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
            encodingLength (srcFormula formula))))

/-- GapCVP reduction support. -/
def physicalCoordinateIndex
    (encodingLength : ℕ) (formula : ThreeCNF)
    (tableType : sourceSATTableType (srcFormula formula))
    (point : sourceSATGridPoint
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
        encodingLength (srcFormula formula)))
    (value :
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
        encodingLength (srcFormula formula)) :
    Fin
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength (srcFormula formula)) :=
  (sourceCoordinateWordOrder
    encodingLength formula).symm (tableType, point, value)

@[simp] theorem
    paperVariableArityPhysicalColumnPermutation_symm_sourceSATColumnIndex
    (encodingLength : ℕ) (formula : ThreeCNF)
    (tableType : sourceSATTableType (srcFormula formula))
    (point : sourceSATGridPoint
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
        encodingLength (srcFormula formula)))
    (value :
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
        encodingLength (srcFormula formula)) :
    (physicalColumnPermutation
      encodingLength formula).symm
        (sourceSATColumnIndex (srcFormula formula)
          (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
            encodingLength (srcFormula formula))
          tableType point value) =
      physicalCoordinateIndex
        encodingLength formula tableType point value := by
  let coordinateOrder := sourceCoordinateWordOrder encodingLength formula
  let finiteOrder := Fintype.equivFin
    (sourceSATTableCoordinate (srcFormula formula)
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
        encodingLength (srcFormula formula))
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
        encodingLength (srcFormula formula)))
  change (coordinateOrder.trans finiteOrder).symm
      (finiteOrder (tableType, point, value)) =
    coordinateOrder.symm (tableType, point, value)
  rw [Equiv.symm_trans_apply, Equiv.symm_apply_apply]

/-- GapCVP reduction support. -/
abbrev physicalWordBinarySystem
    (encodingLength : ℕ) (formula : ThreeCNF) : BinaryAffineSystem :=
  reindexBinaryAffineSystem
    (physicalBinarySystem
      encodingLength formula)
    (Equiv.refl
      (Fin (paperExplicitBinaryRowWordCount
        encodingLength formula)))
    (physicalColumnPermutation
      encodingLength formula)

@[simp] theorem paperVariableArityPhysicalWordBinarySystem_rowCount
    (encodingLength : ℕ) (formula : ThreeCNF) :
    (physicalWordBinarySystem
      encodingLength formula).rowCount =
        paperExplicitBinaryRowWordCount
          encodingLength formula := by
  rfl

theorem paperVariableArityPhysicalWordBinarySystem_check_apply
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      encodingLength formula))
    (column : Fin
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength (srcFormula formula))) :
    (physicalWordBinarySystem
      encodingLength formula).check row column =
      (physicalBinarySystem
        encodingLength formula).check row
          (physicalColumnPermutation
            encodingLength formula column) := by
  rfl

private theorem paperVariableArityPhysicalWordBinarySystem_solves_iff_physical
    (encodingLength : ℕ) (formula : ThreeCNF)
    (values : Fin
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength (srcFormula formula)) → ℤ) :
    (physicalWordBinarySystem
      encodingLength formula).Solves values ↔
        (physicalBinarySystem
          encodingLength formula).Solves
            (fun column => values
              ((physicalColumnPermutation
                encodingLength formula).symm column)) := by
  exact reindexBinaryAffineSystem_solves_iff
    (physicalBinarySystem
      encodingLength formula)
    (Equiv.refl
      (Fin (paperExplicitBinaryRowWordCount
        encodingLength formula)))
    (physicalColumnPermutation
      encodingLength formula) values

private theorem physicalWordBinarySystem_solves_iff_explicit
    (encodingLength : ℕ) (formula : ThreeCNF)
    (values : Fin
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength (srcFormula formula)) → ℤ) :
    (physicalWordBinarySystem
      encodingLength formula).Solves values ↔
        (sourceFormulaExplicitBinarySystem
          encodingLength (srcFormula formula)).Solves
            (fun column => values
              ((physicalColumnPermutation
                encodingLength formula).symm column)) :=
  (paperVariableArityPhysicalWordBinarySystem_solves_iff_physical
    encodingLength formula values).trans
      (paperVariableArityPhysicalBinarySystem_solves_iff_explicit
        encodingLength formula
          (fun column => values
            ((physicalColumnPermutation
              encodingLength formula).symm column)))

private theorem physicalColumnPermutation_norm
    (encodingLength : ℕ) (formula : ThreeCNF)
    (values : Fin
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength (srcFormula formula)) → ℤ) :
    integerSquaredNorm
      (fun column => values
        ((physicalColumnPermutation
          encodingLength formula).symm column)) =
      integerSquaredNorm values :=
  integerSquaredNorm_wordOrder
    (physicalColumnPermutation
      encodingLength formula) values

end PhysicalColumnOrder

namespace PhysicalWordSoundness

open GapCVP.Core GapCVP.Factor400BinaryCodeDecodingCorollary
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.FormulaBridge
open GapCVP.FourFamilySoundness GapCVP.PhysicalColumnOrder

theorem paperVariableArityPhysicalWordBinarySystem_oneHot_of_satisfiable
    (encodingLength : ℕ) (formula : ThreeCNF)
    (hsatisfiable : ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    ∃ vector : Fin
        (sourceFormulaDimension encodingLength
          (srcFormula formula)) → ℤ,
      (physicalWordBinarySystem
        encodingLength formula).Solves vector ∧
      (∀ index, vector index = 0 ∨ vector index = 1) ∧
      integerSquaredNorm vector =
        paperVariableArityIntegerRadius encodingLength formula := by
  obtain ⟨canonical, hsolve, hbinary, hnorm⟩ :=
    paperVariableArityExplicitBinarySystem_oneHot_of_satisfiable
      encodingLength formula hsatisfiable
  let coordinate :=
    physicalColumnPermutation encodingLength formula
  let vector : Fin
      (sourceFormulaDimension encodingLength
        (srcFormula formula)) → ℤ :=
    fun index => canonical (coordinate index)
  refine ⟨vector, ?_, ?_, ?_⟩
  · apply
      (physicalWordBinarySystem_solves_iff_explicit
        encodingLength formula vector).mpr
    simpa [vector, coordinate, paperExplicitBinarySystem]
      using hsolve
  · intro index
    exact hbinary (coordinate index)
  · have htransport :=
      physicalColumnPermutation_norm
        encodingLength formula vector
    have hequal :
        integerSquaredNorm canonical = integerSquaredNorm vector := by
      simpa [vector, coordinate] using htransport
    exact hequal.symm.trans hnorm

private theorem paperVariableArityPhysicalWordBinarySystem_signedSolution_of_satisfiable
    (encodingLength : ℕ) (formula : ThreeCNF)
    (hsatisfiable : ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    ∃ vector : Fin
        (sourceFormulaDimension encodingLength
          (srcFormula formula)) → ℤ,
      (physicalWordBinarySystem
        encodingLength formula).Solves vector ∧
      (integerSquaredNorm vector : ℝ) ≤
        ((sourceOneHotCompletenessRadius
          (srcFormula formula)
          (sourceFormulaGrid encodingLength
            (srcFormula formula)) : ℚ) : ℝ) ^ 2 := by
  obtain ⟨canonical, hsolve, hbound⟩ :=
    paperVariableArityExplicitBinarySystem_signedSolution_of_satisfiable
      encodingLength formula hsatisfiable
  let coordinate :=
    physicalColumnPermutation encodingLength formula
  let vector : Fin
      (sourceFormulaDimension encodingLength
        (srcFormula formula)) → ℤ :=
    fun index => canonical (coordinate index)
  refine ⟨vector, ?_, ?_⟩
  · apply
      (physicalWordBinarySystem_solves_iff_explicit
        encodingLength formula vector).mpr
    simpa [vector, coordinate, paperExplicitBinarySystem]
      using hsolve
  · have htransport :=
      physicalColumnPermutation_norm
        encodingLength formula vector
    have hequal :
        integerSquaredNorm canonical = integerSquaredNorm vector := by
      simpa [vector, coordinate] using htransport
    rw [← hequal]
    exact hbound

theorem
    paperVariableArityPhysicalWordBinarySystem_satisfiable_of_scaled_hamming
    (encodingLength : ℕ) (formula : ThreeCNF)
    (vector : Fin
      (sourceFormulaDimension encodingLength
        (srcFormula formula)) → ℤ)
    (hsolve : (physicalWordBinarySystem
      encodingLength formula).Solves vector)
    (hshort :
      (integerSquaredNorm vector : ℝ) ≤
        2 * binaryCodeGapFactor
          ((physicalWordBinarySystem
            encodingLength formula).dimension) *
          (paperVariableArityIntegerRadius
            encodingLength formula : ℝ)) :
    ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause := by
  let canonical : Fin
      (sourceFormulaDimension encodingLength
        (srcFormula formula)) → ℤ :=
    fun index => vector
      ((physicalColumnPermutation
        encodingLength formula).symm index)
  have hcanonical :
      (paperExplicitBinarySystem
        encodingLength formula).Solves canonical := by
    exact
      (physicalWordBinarySystem_solves_iff_explicit
        encodingLength formula vector).mp hsolve
  apply
    paperVariableArityExplicitBinarySystem_satisfiable_of_scaled_hamming
      encodingLength formula canonical hcanonical
  have hnorm :
      integerSquaredNorm canonical = integerSquaredNorm vector :=
    physicalColumnPermutation_norm
      encodingLength formula vector
  rw [hnorm]
  simpa only [ge_iff_le] using hshort

theorem
    paperVariableArityPhysicalWordBinarySystem_strict_factor400_of_unsatisfiable
    (encodingLength : ℕ) (formula : ThreeCNF)
    (vector : Fin
      (sourceFormulaDimension encodingLength
        (srcFormula formula)) → ℤ)
    (hsolve : (physicalWordBinarySystem
      encodingLength formula).Solves vector)
    (hunsatisfiable :
      ¬ ∃ assignment : ℕ → Bool,
        ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    (GapCVP.SourceFactor400BinaryConstructionABounds.gapFactor400
      ((physicalWordBinarySystem
        encodingLength formula).dimension) *
      ((sourceOneHotCompletenessRadius
        (srcFormula formula)
        (sourceFormulaGrid encodingLength
          (srcFormula formula)) : ℚ) : ℝ)) ^ 2 <
        (integerSquaredNorm vector : ℝ) := by
  let canonical : Fin
      (sourceFormulaDimension encodingLength
        (srcFormula formula)) → ℤ :=
    fun index => vector
      ((physicalColumnPermutation
        encodingLength formula).symm index)
  have hcanonical :
      (paperExplicitBinarySystem
        encodingLength formula).Solves canonical := by
    exact
      (physicalWordBinarySystem_solves_iff_explicit
        encodingLength formula vector).mp hsolve
  have hstrict :=
    paperVariableArityExplicitBinarySystem_strict_factor400_of_unsatisfiable
      encodingLength formula canonical hcanonical hunsatisfiable
  have hnorm :
      integerSquaredNorm canonical = integerSquaredNorm vector :=
    physicalColumnPermutation_norm
      encodingLength formula vector
  simpa only [gt_iff_lt, hnorm] using hstrict

end PhysicalWordSoundness

namespace Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap

open Turing GapCVP.Core GapCVP.Factor400BinaryInstanceBridge
open GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.OriginalThreeSATNPHardness
open GapCVP.SourcePreprocessingSemantics GapCVP.SourcePreprocessingTM GapCVP.FormulaBridge
open GapCVP.FourFamilySoundness GapCVP.NormalizedRecordDecoder GapCVP.PhysicalColumnOrder
open GapCVP.PhysicalWordSoundness

/-- GapCVP reduction support. -/
def physicalFormulaSystem
    (encodingLength : ℕ) (formula : ThreeCNF) : BinaryAffineSystem :=
  physicalWordBinarySystem encodingLength formula

@[simp] theorem paperVariableArityPhysicalFormulaSystem_dimension
    (encodingLength : ℕ) (formula : ThreeCNF) :
    (physicalFormulaSystem encodingLength formula).dimension =
      sourceFormulaDimension encodingLength
        (srcFormula formula) := by
  rfl

theorem physicalFormulaSystem_dimension_pos
    (encodingLength : ℕ) (formula : ThreeCNF) :
    0 < (physicalFormulaSystem
      encodingLength formula).dimension := by
  change 0 < sourceFormulaDimension encodingLength
    (srcFormula formula)
  exact Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension_pos
    encodingLength
    (srcFormula formula)

/-- GapCVP reduction support. -/
def physicalFormulaRadius
    (encodingLength : ℕ) (formula : ThreeCNF) : ℚ :=
  sourceOneHotCompletenessRadius
    (srcFormula formula)
    (sourceFormulaGrid encodingLength
      (srcFormula formula))

theorem physicalFormulaRadius_pos
    (encodingLength : ℕ) (formula : ThreeCNF) :
    0 < physicalFormulaRadius
      encodingLength formula := by
  apply GapCVP.Core.sourceOneHotCompletenessRadius_pos
    (srcFormula formula)
    (sourceFormulaGrid encodingLength
      (srcFormula formula))
  exact Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid_card_pos
    encodingLength
    (srcFormula formula)

/-- GapCVP reduction support. -/
def physicalFormulaInstance
    (encodingLength : ℕ) (formula : ThreeCNF) : GapCVPInstance :=
  effectiveGapCVPInstance
    (physicalFormulaSystem encodingLength formula)
    (physicalFormulaSystem_dimension_pos
      encodingLength formula)
    (physicalFormulaRadius encodingLength formula)
    (physicalFormulaRadius_pos
      encodingLength formula)

theorem paperVariableArityPhysicalFormulaSystem_oneHot_of_satisfiable
    (encodingLength : ℕ) (formula : ThreeCNF)
    (satisfiable : ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    ∃ vector : Fin
        (sourceFormulaDimension encodingLength
          (srcFormula formula)) → ℤ,
      (physicalFormulaSystem
        encodingLength formula).Solves vector ∧
      (∀ index, vector index = 0 ∨ vector index = 1) ∧
      integerSquaredNorm vector =
        paperVariableArityIntegerRadius encodingLength formula := by
  exact paperVariableArityPhysicalWordBinarySystem_oneHot_of_satisfiable
    encodingLength formula satisfiable

theorem physicalFormulaSystem_consistent_of_satisfiable
    (encodingLength : ℕ) (formula : ThreeCNF)
    (satisfiable : ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    (physicalFormulaSystem
      encodingLength formula).effectiveReducedConsistent = true := by
  apply (BinaryAffineSystem.effectiveReducedConsistent_iff_solvable
    (physicalFormulaSystem
      encodingLength formula)).mpr
  obtain ⟨vector, solution, _, _⟩ :=
    paperVariableArityPhysicalFormulaSystem_oneHot_of_satisfiable
      encodingLength formula satisfiable
  exact ⟨vector, solution⟩

private theorem paperVariableArityPhysicalFormulaInstance_gapYES400_of_satisfiable
    (encodingLength : ℕ) (formula : ThreeCNF)
    (satisfiable : ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    gapYES400
      (physicalFormulaInstance
        encodingLength formula) := by
  let H := physicalFormulaSystem
    encodingLength formula
  let radius := physicalFormulaRadius
    encodingLength formula
  let positiveDimension :=
    physicalFormulaSystem_dimension_pos
      encodingLength formula
  let positiveRadius := physicalFormulaRadius_pos
    encodingLength formula
  have consistent :=
    physicalFormulaSystem_consistent_of_satisfiable
      encodingLength formula satisfiable
  obtain ⟨vector, solution, bound⟩ :=
    paperVariableArityPhysicalWordBinarySystem_signedSolution_of_satisfiable
      encodingLength formula satisfiable
  change gapYES400 (adaptGapCVPInstance
    (effectiveConstructionAInstance H positiveDimension
      radius positiveRadius))
  apply (adaptGapCVPInstance_gapYES400_iff_metricYes
    (effectiveConstructionAInstance H positiveDimension
      radius positiveRadius)).mpr
  apply (effectiveConstructionAInstance_yes_iff_signedSolution
    H positiveDimension consistent radius positiveRadius).mpr
  refine ⟨vector, solution, ?_⟩
  change
    (integerSquaredNorm vector : ℝ) ≤
      ((sourceOneHotCompletenessRadius
        (srcFormula formula)
        (sourceFormulaGrid encodingLength
          (srcFormula formula)) : ℚ) : ℝ) ^ 2
  exact bound

private theorem paperVariableArityPhysicalFormulaInstance_gapNO400_of_unsatisfiable
    (encodingLength : ℕ) (formula : ThreeCNF)
    (consistent :
      (physicalFormulaSystem
        encodingLength formula).effectiveReducedConsistent = true)
    (unsatisfiable : ¬ ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    gapNO400
      (physicalFormulaInstance
        encodingLength formula) := by
  let H := physicalFormulaSystem
    encodingLength formula
  let radius := physicalFormulaRadius
    encodingLength formula
  let positiveDimension :=
    physicalFormulaSystem_dimension_pos
      encodingLength formula
  let positiveRadius := physicalFormulaRadius_pos
    encodingLength formula
  change gapNO400 (adaptGapCVPInstance
    (effectiveConstructionAInstance H positiveDimension
      radius positiveRadius))
  apply (adaptGapCVPInstance_gapNO400_iff_metricNo
    (effectiveConstructionAInstance H positiveDimension
      radius positiveRadius)).mpr
  apply (effectiveConstructionAInstance_no_iff_signedSolutionNorm
    H positiveDimension consistent radius positiveRadius
    ((1 : ℝ) / 400)).mpr
  intro vector solution
  have separation :=
    paperVariableArityPhysicalWordBinarySystem_strict_factor400_of_unsatisfiable
      encodingLength formula vector solution unsatisfiable
  change
    ((GapCVP.SourceFactor400BinaryConstructionABounds.gapFactor400
      ((physicalWordBinarySystem
        encodingLength formula).dimension)) *
      ((sourceOneHotCompletenessRadius
        (srcFormula formula)
        (sourceFormulaGrid encodingLength
          (srcFormula formula)) : ℚ) : ℝ)) ^ 2 <
      (integerSquaredNorm vector : ℝ)
  exact separation

private theorem paperVariableArityPhysicalCanonicalYes_mem :
    gapCVP400Promise.yes SourceMachineRouting.canonicalYesWord := by
  simp only [GapCVP.gapCVP400Promise, decide_eq_true_eq]
  refine ⟨SourceMachineRouting.canonicalYesInstance, rfl, ?_⟩
  exact (gapYES400_iff_gapYES
    SourceMachineRouting.canonicalYesInstance).mpr
      SourceMachineRouting.canonicalYesInstance_gapYES

theorem paperVariableArityOriginal_satisfiable_of_normalized_empty
    (formula : ThreeCNF)
    (empty : paperSourceNormalizedClauses formula = []) :
    ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause := by
  refine ⟨fun _ => false, ?_⟩
  apply (paperSourceNormalizedClauses_satisfied_iff
    formula (fun _ => false)).mp
  simp only [empty, List.not_mem_nil, Prod.exists, Bool.exists_bool, IsEmpty.forall_iff,
      implies_true]

/-- GapCVP reduction support. -/
def physicalSourceInstance
    (input : List Bool) : GapCVPInstance := by
  classical
  exact
    match BinaryEncoding.decodeThreeCNF input with
    | none => Factor400BinaryCanonicalNo.adaptedCanonicalNoInstance
    | some formula =>
      if BinaryEncoding.encodeThreeCNF formula = input then
        match readPaperVariableArityNormalizedSourceDescriptor
            (paperSourcePreprocessingOutput input) with
        | none => Factor400BinaryCanonicalNo.adaptedCanonicalNoInstance
        | some descriptor =>
          if descriptor.originalWord = input then
            if descriptor.normalizedClauses = [] then
              SourceMachineRouting.canonicalYesInstance
            else
              if (physicalFormulaSystem
                    input.length descriptor.originalFormula).effectiveReducedConsistent then
                physicalFormulaInstance
                  input.length descriptor.originalFormula
              else
                Factor400BinaryCanonicalNo.adaptedCanonicalNoInstance
          else
            Factor400BinaryCanonicalNo.adaptedCanonicalNoInstance
      else
        Factor400BinaryCanonicalNo.adaptedCanonicalNoInstance

/-- GapCVP reduction support. -/
def paperVariableArityPhysicalSourceMap
    (input : List Bool) : List Bool :=
  BinaryEncoding.encodeGapCVPInstance
    (physicalSourceInstance input)

theorem paperVariableArityPhysicalSourceInstance_of_decode_none
    (input : List Bool)
    (decode : BinaryEncoding.decodeThreeCNF input = none) :
    physicalSourceInstance input =
      Factor400BinaryCanonicalNo.adaptedCanonicalNoInstance := by
  simp only [physicalSourceInstance, decode]

theorem paperVariableArityPhysicalSourceInstance_of_noncanonical
    (input : List Bool) (formula : ThreeCNF)
    (decode : BinaryEncoding.decodeThreeCNF input = some formula)
    (noncanonical :
      BinaryEncoding.encodeThreeCNF formula ≠ input) :
    physicalSourceInstance input =
      Factor400BinaryCanonicalNo.adaptedCanonicalNoInstance := by
  simp only [physicalSourceInstance, decode, noncanonical, ↓reduceIte]

theorem paperVariableArityPhysicalSourceInstance_of_normalized_empty
    (input : List Bool) (formula : ThreeCNF)
    (decode : BinaryEncoding.decodeThreeCNF input = some formula)
    (canonical : BinaryEncoding.encodeThreeCNF formula = input)
    (empty : paperSourceNormalizedClauses formula = []) :
    physicalSourceInstance input =
      SourceMachineRouting.canonicalYesInstance := by
  unfold physicalSourceInstance
  simp only [decode, ite_eq_left canonical]
  have descriptor :
      readPaperVariableArityNormalizedSourceDescriptor
          (paperSourcePreprocessingOutput input) =
        some
          { retainedFormula := noTautClauses formula
            normalizedClauses := paperSourceNormalizedClauses formula
            originalFormula := formula
            originalWord :=
              BinaryEncoding.encodeThreeCNF formula } := by
    rw [← canonical]
    exact readPaperVariableArityNormalizedSourceDescriptor_valid formula
  rw [descriptor]
  simp only [canonical, ↓reduceIte, empty]

theorem paperVariableArityPhysicalSourceInstance_of_inconsistent
    (input : List Bool) (formula : ThreeCNF)
    (decode : BinaryEncoding.decodeThreeCNF input = some formula)
    (canonical : BinaryEncoding.encodeThreeCNF formula = input)
    (nonempty : paperSourceNormalizedClauses formula ≠ [])
    (inconsistent :
      (physicalFormulaSystem
        input.length formula).effectiveReducedConsistent = false) :
    physicalSourceInstance input =
      Factor400BinaryCanonicalNo.adaptedCanonicalNoInstance := by
  unfold physicalSourceInstance
  simp only [decode, ite_eq_left canonical]
  have descriptor :
      readPaperVariableArityNormalizedSourceDescriptor
          (paperSourcePreprocessingOutput input) =
        some
          { retainedFormula := noTautClauses formula
            normalizedClauses := paperSourceNormalizedClauses formula
            originalFormula := formula
            originalWord :=
              BinaryEncoding.encodeThreeCNF formula } := by
    rw [← canonical]
    exact readPaperVariableArityNormalizedSourceDescriptor_valid formula
  rw [descriptor]
  simp only [canonical, ↓reduceIte, nonempty, inconsistent, Bool.false_eq_true]

theorem paperVariableArityPhysicalSourceInstance_of_consistent
    (input : List Bool) (formula : ThreeCNF)
    (decode : BinaryEncoding.decodeThreeCNF input = some formula)
    (canonical : BinaryEncoding.encodeThreeCNF formula = input)
    (nonempty : paperSourceNormalizedClauses formula ≠ [])
    (consistent :
      (physicalFormulaSystem
        input.length formula).effectiveReducedConsistent = true) :
    physicalSourceInstance input =
      physicalFormulaInstance
        input.length formula := by
  unfold physicalSourceInstance
  simp only [decode, ite_eq_left canonical]
  have descriptor :
      readPaperVariableArityNormalizedSourceDescriptor
          (paperSourcePreprocessingOutput input) =
        some
          { retainedFormula := noTautClauses formula
            normalizedClauses := paperSourceNormalizedClauses formula
            originalFormula := formula
            originalWord :=
              BinaryEncoding.encodeThreeCNF formula } := by
    rw [← canonical]
    exact readPaperVariableArityNormalizedSourceDescriptor_valid formula
  rw [descriptor]
  simp only [canonical, ↓reduceIte, nonempty, consistent]

private theorem paperVariableArityPhysicalSourceMap_completeness
    (input : List Bool)
    (satisfiable : ∃ formula : ThreeCNF,
      BinaryEncoding.encodeThreeCNF formula = input ∧
        ∃ assignment : ℕ → Bool,
          ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    gapCVP400Promise.yes
      (paperVariableArityPhysicalSourceMap input) := by
  obtain ⟨formula, canonical, assignment⟩ := satisfiable
  have decode : BinaryEncoding.decodeThreeCNF input =
      some formula := by
    rw [← canonical]
    exact BinaryEncoding.decodeThreeCNF_encode formula
  by_cases empty : paperSourceNormalizedClauses formula = []
  · unfold paperVariableArityPhysicalSourceMap
    rw [paperVariableArityPhysicalSourceInstance_of_normalized_empty
      input formula decode canonical empty]
    exact paperVariableArityPhysicalCanonicalYes_mem
  · have consistent :=
      physicalFormulaSystem_consistent_of_satisfiable
        input.length formula assignment
    simp only [GapCVP.gapCVP400Promise, decide_eq_true_eq]
    refine ⟨physicalFormulaInstance
      input.length formula, ?_, ?_⟩
    · change
        BinaryEncoding.encodeGapCVPInstance
            (physicalFormulaInstance
              input.length formula) =
          paperVariableArityPhysicalSourceMap input
      unfold paperVariableArityPhysicalSourceMap
      rw [paperVariableArityPhysicalSourceInstance_of_consistent
        input formula decode canonical empty consistent]
    · exact
        paperVariableArityPhysicalFormulaInstance_gapYES400_of_satisfiable
          input.length formula assignment

private theorem paperVariableArityPhysicalSourceMap_soundness
    (input : List Bool)
    (unsatisfiable : ¬ ∃ formula : ThreeCNF,
      BinaryEncoding.encodeThreeCNF formula = input ∧
        ∃ assignment : ℕ → Bool,
          ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    gapCVP400Promise.no
      (paperVariableArityPhysicalSourceMap input) := by
  classical
  cases decode : BinaryEncoding.decodeThreeCNF input with
  | none =>
      unfold paperVariableArityPhysicalSourceMap
      rw [paperVariableArityPhysicalSourceInstance_of_decode_none
        input decode]
      exact Factor400BinaryCanonicalNo.adaptedCanonicalNoWord_mem_no
  | some formula =>
      by_cases canonical :
          BinaryEncoding.encodeThreeCNF formula = input
      · by_cases empty : paperSourceNormalizedClauses formula = []
        · exfalso
          apply unsatisfiable
          exact ⟨formula, canonical,
            paperVariableArityOriginal_satisfiable_of_normalized_empty
              formula empty⟩
        · cases consistent :
              (physicalFormulaSystem
                input.length formula).effectiveReducedConsistent with
          | false =>
              unfold paperVariableArityPhysicalSourceMap
              rw [paperVariableArityPhysicalSourceInstance_of_inconsistent
                input formula decode canonical empty consistent]
              exact Factor400BinaryCanonicalNo.adaptedCanonicalNoWord_mem_no
          | true =>
              have originalUnsatisfiable :
                  ¬ ∃ assignment : ℕ → Bool,
                    ∀ clause ∈ formula,
                      clauseSatisfied assignment clause := by
                intro assignment
                exact unsatisfiable ⟨formula, canonical, assignment⟩
              simp only [GapCVP.gapCVP400Promise, decide_eq_true_eq]
              refine ⟨physicalFormulaInstance
                input.length formula, ?_, ?_⟩
              · change
                  BinaryEncoding.encodeGapCVPInstance
                      (physicalFormulaInstance
                        input.length formula) =
                    paperVariableArityPhysicalSourceMap input
                unfold paperVariableArityPhysicalSourceMap
                rw [paperVariableArityPhysicalSourceInstance_of_consistent
                  input formula decode canonical empty consistent]
              · exact
                  paperVariableArityPhysicalFormulaInstance_gapNO400_of_unsatisfiable
                    input.length formula consistent originalUnsatisfiable
      · unfold paperVariableArityPhysicalSourceMap
        rw [paperVariableArityPhysicalSourceInstance_of_noncanonical
          input formula decode canonical]
        exact Factor400BinaryCanonicalNo.adaptedCanonicalNoWord_mem_no

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalSourceReductionOfMachine
    (machine : BitTM paperVariableArityPhysicalSourceMap) :
    PromiseReduction paperOriginalThreeSATLanguage gapCVP400Promise where
  map := paperVariableArityPhysicalSourceMap
  polynomial_time := ⟨machine⟩
  completeness input satisfiable :=
    paperVariableArityPhysicalSourceMap_completeness input
      ((paperOriginalThreeSATLanguage_iff input).mp satisfiable)
  soundness input unsatisfiable :=
    paperVariableArityPhysicalSourceMap_soundness input
      (fun satisfiable => unsatisfiable
        ((paperOriginalThreeSATLanguage_iff input).mpr satisfiable))

end Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap

namespace ClauseOffsetTM

open Turing
open scoped BigOperators

open GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceStructuralTuringTM
open GapCVP.SourceMachineCert GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceIndexedClauseLookupTM
open GapCVP.SourceNormalizedVariableRankScanTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.CNFBoundedRecordFoldTM GapCVP.CLStructuralPrefixWriter GapCVP.BinaryDimensionTM
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics
open GapCVP.SourcePreprocessingTM

/-- GapCVP reduction support. -/
def paperVariableArityClauseArityUnary (input : List Bool) : List Bool :=
  (unaryPrefixOutput (paperSourceClauseNormalizedRecord input)).tail

/-- GapCVP reduction support. -/
noncomputable def paperClauseArityUnaryComputable :
    BitTM
      paperVariableArityClauseArityUnary := by
  have parsed := GapCVP.TMComposition.computableInPolyTime
    paperSourceClauseNormalizedRecordComputable unaryPrefixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    parsed dropHeadComputable

@[simp] theorem paperVariableArityClauseArityUnary_valid
    (clause : ThreeClause) (suffix : List Bool) :
    paperVariableArityClauseArityUnary
        (encodeThreeClause clause ++ suffix) =
      List.replicate (paperSourceNormalizedClause clause).length true := by
  unfold paperVariableArityClauseArityUnary
  rw [paperSourceClauseNormalizedRecord_valid]
  simp only [paperSourceNormalizedClauseRecord, unaryPrefixOutput_replicate_delimiter,
      List.tail_cons]

private theorem paperVariableArityClauseArityUnary_length_le_three
    (input : List Bool) :
    (paperVariableArityClauseArityUnary input).length ≤ 3 := by
  unfold paperVariableArityClauseArityUnary
    paperSourceClauseNormalizedRecord
    paperSourceClauseSecondKeepUnary
    paperSourceClauseThirdKeepUnary
  split <;> split <;>
    simp [unaryPrefixOutput, unaryPrefixLength]

private def paperVariableArityClauseSquarePlusOneUnary
    (input : List Bool) : List Bool :=
  List.replicate
    ((paperVariableArityClauseArityUnary input).length ^ 2 + 1) true

private noncomputable def paperVariableArityClauseSquarePlusOneUnaryComputable :
    BitTM
      paperVariableArityClauseSquarePlusOneUnary := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    paperClauseArityUnaryComputable
    (polynomialValueUnaryComputable (Polynomial.X ^ 2 + 1))
  change BitTM
    (fun input : List Bool => List.replicate
      ((paperVariableArityClauseArityUnary input).length ^ 2 + 1) true)
  simpa only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
      Function.comp_def] using physical

/-- GapCVP reduction support. -/
def paperVariableArityClauseWeightUnary : List Bool → List Bool :=
  unarySubtractionOutput
    paperVariableArityClauseSquarePlusOneUnary
    paperVariableArityClauseArityUnary

/-- GapCVP reduction support. -/
noncomputable def paperClauseWeightUnaryComputable :
    BitTM
      paperVariableArityClauseWeightUnary :=
  unarySubtractionComputable
    paperVariableArityClauseSquarePlusOneUnaryComputable
    paperClauseArityUnaryComputable

private theorem paperVariableArityClauseWeightUnary_eq
    (input : List Bool) :
    paperVariableArityClauseWeightUnary input =
      List.replicate
        ((paperVariableArityClauseArityUnary input).length ^ 2 + 1 -
          (paperVariableArityClauseArityUnary input).length) true := by
  unfold paperVariableArityClauseWeightUnary
  apply unarySubtractionOutput_valid
    paperVariableArityClauseSquarePlusOneUnary
    paperVariableArityClauseArityUnary input
    ((paperVariableArityClauseArityUnary input).length ^ 2 + 1)
    (paperVariableArityClauseArityUnary input).length
  · rfl
  · unfold paperVariableArityClauseArityUnary
      paperSourceClauseNormalizedRecord
      paperSourceClauseSecondKeepUnary
      paperSourceClauseThirdKeepUnary
    split <;> split <;>
      simp [unaryPrefixOutput, unaryPrefixLength]

private theorem paperVariableArityClausePolynomialWeight_eq
    (arity : ℕ) (hpositive : 0 < arity) (hbound : arity ≤ 3) :
    arity ^ 2 + 1 - arity = 2 ^ arity - 1 := by
  interval_cases arity <;> norm_num at *

@[simp] theorem paperVariableArityClauseWeightUnary_valid
    (clause : ThreeClause) (suffix : List Bool) :
    paperVariableArityClauseWeightUnary
        (encodeThreeClause clause ++ suffix) =
      List.replicate (2 ^ (paperSourceNormalizedClause clause).length - 1)
        true := by
  rw [paperVariableArityClauseWeightUnary_eq,
    paperVariableArityClauseArityUnary_valid]
  simp only [List.length_replicate]
  rw [paperVariableArityClausePolynomialWeight_eq
    (paperSourceNormalizedClause clause).length
    (List.length_pos_iff.mpr
      (paperSourceNormalizedClause_ne_nil clause))
    (paperNormalizedClause_length_le_three clause)]

private theorem paperVariableArityClauseWeightUnary_length_le_seven
    (input : List Bool) :
    (paperVariableArityClauseWeightUnary input).length ≤ 7 := by
  rw [paperVariableArityClauseWeightUnary_eq,
    List.length_replicate]
  have bound := paperVariableArityClauseArityUnary_length_le_three input
  interval_cases h : (paperVariableArityClauseArityUnary input).length <;>
    norm_num

private def paperVariableArityOffsetAccumulator : List Bool → List Bool :=
  paperSourcePreprocessingField 0

private def paperOffsetCatalogueField : List Bool → List Bool :=
  paperSourcePreprocessingField 1

private def paperVariableArityOffsetPending : List Bool → List Bool :=
  paperSourcePreprocessingField 2

private def paperVariableArityOffsetPreserved : List Bool → List Bool :=
  paperSourcePreprocessingSuffixAt 3

private def paperOffsetCurrentNormalized : List Bool → List Bool :=
  paperSourceClauseNormalizedRecord ∘ paperVariableArityOffsetPending

private def paperOffsetCurrentArity : List Bool → List Bool :=
  paperVariableArityClauseArityUnary ∘ paperVariableArityOffsetPending

private def paperOffsetCurrentWeight : List Bool → List Bool :=
  paperVariableArityClauseWeightUnary ∘ paperVariableArityOffsetPending

@[simp] private theorem paperVariableArityOffsetCurrentNormalized_apply
    (state : List Bool) :
    paperOffsetCurrentNormalized state =
      paperSourceClauseNormalizedRecord
        (paperVariableArityOffsetPending state) := by
  simp only [paperOffsetCurrentNormalized,
    Function.comp_apply]

@[simp] private theorem paperVariableArityOffsetCurrentArity_apply
    (state : List Bool) :
    paperOffsetCurrentArity state =
      paperVariableArityClauseArityUnary
        (paperVariableArityOffsetPending state) := by
  simp only [paperOffsetCurrentArity,
    Function.comp_apply]

@[simp] private theorem paperVariableArityOffsetCurrentWeight_apply
    (state : List Bool) :
    paperOffsetCurrentWeight state =
      paperVariableArityClauseWeightUnary
        (paperVariableArityOffsetPending state) := by
  simp only [paperOffsetCurrentWeight,
    Function.comp_apply]

private def paperOffsetCurrentRecord
    (state : List Bool) : List Bool :=
  lengthPrefixedWord (paperVariableArityOffsetAccumulator state) ++
    (lengthPrefixedWord (paperOffsetCurrentArity state) ++
    (lengthPrefixedWord (paperOffsetCurrentWeight state) ++
      lengthPrefixedWord (paperOffsetCurrentNormalized state)))

private def paperOffsetNextAccumulator
    (state : List Bool) : List Bool :=
  paperVariableArityOffsetAccumulator state ++
    paperOffsetCurrentWeight state

private def paperOffsetNextCatalogue
    (state : List Bool) : List Bool :=
  paperOffsetCatalogueField state ++
    paperOffsetCurrentRecord state

private def paperVariableArityOffsetNextPending : List Bool → List Bool :=
  clauseSuffix ∘ paperVariableArityOffsetPending

private def paperVariableArityClauseOffsetStep
    (state : List Bool) : List Bool :=
  lengthPrefixedWord (paperOffsetNextAccumulator state) ++
    (lengthPrefixedWord (paperOffsetNextCatalogue state) ++
    (lengthPrefixedWord (paperVariableArityOffsetNextPending state) ++
      paperVariableArityOffsetPreserved state))

private noncomputable def paperVariableArityOffsetAccumulatorComputable :
    BitTM
      paperVariableArityOffsetAccumulator :=
  paperPreprocessingFieldComputable 0

private noncomputable def paperVariableArityOffsetCatalogueFieldComputable :
    BitTM
      paperOffsetCatalogueField :=
  paperPreprocessingFieldComputable 1

private noncomputable def paperOffsetPendingComputable :
    BitTM
      paperVariableArityOffsetPending :=
  paperPreprocessingFieldComputable 2

private noncomputable def paperVariableArityOffsetPreservedComputable :
    BitTM
      paperVariableArityOffsetPreserved :=
  paperPreprocessingSuffixAtComputable 3

private noncomputable def paperVariableArityOffsetCurrentNormalizedComputable :
    BitTM
      paperOffsetCurrentNormalized :=
  GapCVP.TMComposition.computableInPolyTime
    paperOffsetPendingComputable
    paperSourceClauseNormalizedRecordComputable

private noncomputable def paperVariableArityOffsetCurrentArityComputable :
    BitTM
      paperOffsetCurrentArity :=
  GapCVP.TMComposition.computableInPolyTime
    paperOffsetPendingComputable
    paperClauseArityUnaryComputable

private noncomputable def paperVariableArityOffsetCurrentWeightComputable :
    BitTM
      paperOffsetCurrentWeight :=
  GapCVP.TMComposition.computableInPolyTime
    paperOffsetPendingComputable
    paperClauseWeightUnaryComputable

private noncomputable def paperVariableArityOffsetCurrentRecordComputable :
    BitTM
      paperOffsetCurrentRecord := by
  have offset := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityOffsetAccumulatorComputable
    structuralPrefixWriterComputable
  have arity := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityOffsetCurrentArityComputable
    structuralPrefixWriterComputable
  have weight := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityOffsetCurrentWeightComputable
    structuralPrefixWriterComputable
  have normalized := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityOffsetCurrentNormalizedComputable
    structuralPrefixWriterComputable
  exact pointwiseAppendComputable offset
    (pointwiseAppendComputable arity
      (pointwiseAppendComputable weight normalized))

private noncomputable def paperVariableArityOffsetNextAccumulatorComputable :
    BitTM
      paperOffsetNextAccumulator :=
  pointwiseAppendComputable
    paperVariableArityOffsetAccumulatorComputable
    paperVariableArityOffsetCurrentWeightComputable

private noncomputable def paperVariableArityOffsetNextCatalogueComputable :
    BitTM
      paperOffsetNextCatalogue :=
  pointwiseAppendComputable
    paperVariableArityOffsetCatalogueFieldComputable
    paperVariableArityOffsetCurrentRecordComputable

private noncomputable def paperVariableArityOffsetNextPendingComputable :
    BitTM
      paperVariableArityOffsetNextPending :=
  GapCVP.TMComposition.computableInPolyTime
    paperOffsetPendingComputable clauseSuffixComputable

private noncomputable def paperVariableArityClauseOffsetStepComputable :
    BitTM
      paperVariableArityClauseOffsetStep := by
  have offset := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityOffsetNextAccumulatorComputable
    structuralPrefixWriterComputable
  have catalogue := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityOffsetNextCatalogueComputable
    structuralPrefixWriterComputable
  have pending := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityOffsetNextPendingComputable
    structuralPrefixWriterComputable
  exact pointwiseAppendComputable offset
    (pointwiseAppendComputable catalogue
      (pointwiseAppendComputable pending
        paperVariableArityOffsetPreservedComputable))

private theorem paperVariableArityOffsetFieldAccounting
    (state : List Bool) :
    2 * (paperVariableArityOffsetAccumulator state).length +
      2 * (paperOffsetCatalogueField state).length +
      2 * (paperVariableArityOffsetPending state).length +
      (paperVariableArityOffsetPreserved state).length ≤ state.length := by
  have first := sourceNormalizedVariableScanStructuralFieldAccounting state
  have second := sourceNormalizedVariableScanStructuralFieldAccounting
    (firstFieldSuffix state)
  have third := sourceNormalizedVariableScanStructuralFieldAccounting
    (firstFieldSuffix (firstFieldSuffix state))
  simp only [paperVariableArityOffsetAccumulator, paperSourcePreprocessingField,
    paperSourcePreprocessingSuffixAt, Function.iterate_zero, Function.comp_apply, id_eq,
    paperOffsetCatalogueField, paperVariableArityOffsetPending, Function.iterate_succ,
    paperVariableArityOffsetPreserved, ge_iff_le] at *
  omega

private theorem paperVariableArityOffsetCurrentNormalized_length_le
    (state : List Bool) :
    (paperOffsetCurrentNormalized state).length ≤
      3 * (paperVariableArityOffsetPending state).length + 10 := by
  rw [paperVariableArityOffsetCurrentNormalized_apply]
  exact paperSourceClauseNormalizedRecord_length_le
    (paperVariableArityOffsetPending state)

private theorem paperVariableArityOffsetCurrentWeight_length_le
    (state : List Bool) :
    (paperOffsetCurrentWeight state).length ≤ 7 := by
  rw [paperVariableArityOffsetCurrentWeight_apply]
  exact paperVariableArityClauseWeightUnary_length_le_seven
    (paperVariableArityOffsetPending state)

private theorem paperVariableArityOffsetCurrentArity_length_le
    (state : List Bool) :
    (paperOffsetCurrentArity state).length ≤ 3 := by
  rw [paperVariableArityOffsetCurrentArity_apply]
  exact paperVariableArityClauseArityUnary_length_le_three
    (paperVariableArityOffsetPending state)

private theorem paperVariableArityClauseOffsetStep_length_le
    (state : List Bool) :
    (paperVariableArityClauseOffsetStep state).length ≤
      state.length +
        4 * (paperVariableArityOffsetAccumulator state).length +
        12 * (paperVariableArityOffsetPending state).length + 110 := by
  have accounting := paperVariableArityOffsetFieldAccounting state
  have arity := paperVariableArityOffsetCurrentArity_length_le state
  have weight := paperVariableArityOffsetCurrentWeight_length_le state
  have normalized := paperVariableArityOffsetCurrentNormalized_length_le state
  have pending := sourceOriginalIndexedClauseSuffix_length_le
    (paperVariableArityOffsetPending state)
  simp only [paperVariableArityClauseOffsetStep,
    paperOffsetNextAccumulator,
    paperOffsetNextCatalogue,
    paperVariableArityOffsetNextPending,
    paperOffsetCurrentRecord,
    Function.comp_apply, List.length_append,
    lengthPrefixedWord_length] at *
  omega

@[simp] private theorem paperVariableArityOffsetAccumulator_step
    (state : List Bool) :
    paperVariableArityOffsetAccumulator
        (paperVariableArityClauseOffsetStep state) =
      paperVariableArityOffsetAccumulator state ++
        paperOffsetCurrentWeight state := by
  simp only [paperVariableArityOffsetAccumulator, paperSourcePreprocessingField,
      paperSourcePreprocessingSuffixAt, Function.iterate_zero, paperVariableArityClauseOffsetStep,
      paperOffsetNextAccumulator, Function.comp_apply, id_eq,
          paperVariableArityOffsetCurrentWeight_apply,
      firstFieldContents_valid]

@[simp] private theorem paperVariableArityOffsetPending_step
    (state : List Bool) :
    paperVariableArityOffsetPending
        (paperVariableArityClauseOffsetStep state) =
      clauseSuffix (paperVariableArityOffsetPending state) := by
  simp [paperVariableArityOffsetPending,
    paperVariableArityClauseOffsetStep,
    paperVariableArityOffsetNextPending,
    paperSourcePreprocessingField,
    paperSourcePreprocessingSuffixAt,
    Function.comp_apply]

private theorem paperVariableArityOffsetAccumulator_iterate_length_le
    (seed : List Bool) (stage : ℕ) :
    (paperVariableArityOffsetAccumulator
      ((paperVariableArityClauseOffsetStep^[stage]) seed)).length ≤
      (paperVariableArityOffsetAccumulator seed).length + 7 * stage := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, mul_zero, add_zero, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply',
        paperVariableArityOffsetAccumulator_step,
        List.length_append]
      have weight := paperVariableArityOffsetCurrentWeight_length_le
        ((paperVariableArityClauseOffsetStep^[stage]) seed)
      omega

private theorem paperVariableArityOffsetPending_iterate_length_le
    (seed : List Bool) (stage : ℕ) :
    (paperVariableArityOffsetPending
      ((paperVariableArityClauseOffsetStep^[stage]) seed)).length ≤
      (paperVariableArityOffsetPending seed).length := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply',
        paperVariableArityOffsetPending_step]
      exact (sourceOriginalIndexedClauseSuffix_length_le _).trans ih

private theorem paperVariableArityClauseOffsetStep_iterate_length_le
    (seed : List Bool) (stage : ℕ) :
    (((paperVariableArityClauseOffsetStep^[stage]) seed)).length ≤
      seed.length + stage * (16 * seed.length + 28 * stage + 110) := by
  have accounting := paperVariableArityOffsetFieldAccounting seed
  have initialAccumulator :
      (paperVariableArityOffsetAccumulator seed).length ≤ seed.length := by
    omega
  have initialPending :
      (paperVariableArityOffsetPending seed).length ≤ seed.length := by
    omega
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, mul_zero, add_zero, zero_mul, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      have worker := paperVariableArityClauseOffsetStep_length_le
        ((paperVariableArityClauseOffsetStep^[stage]) seed)
      have accumulator :=
        paperVariableArityOffsetAccumulator_iterate_length_le seed stage
      have pending :=
        paperVariableArityOffsetPending_iterate_length_le seed stage
      linarith

private def paperVariableArityClauseOffsetFoldBound : Polynomial ℕ :=
  160 * (Polynomial.X + 1) ^ 2

private theorem paperVariableArityClauseOffset_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates paperVariableArityClauseOffsetStep
      paperVariableArityClauseOffsetFoldBound := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed parsed stage bounded
  have seedBound := sourceAtomicFoldSeed_length_le
    input count seed parsed
  have countBound := parsedUnaryFold_count_le_length
    input count seed parsed
  have stageBound : stage ≤ input.length :=
    Nat.le_trans bounded countBound
  have stageSeed : stage * seed.length ≤ input.length * input.length :=
    Nat.mul_le_mul stageBound seedBound
  have stageSquare : stage * stage ≤ input.length * input.length :=
    Nat.mul_le_mul stageBound stageBound
  have intermediate :=
    paperVariableArityClauseOffsetStep_iterate_length_le seed stage
  simp only [paperVariableArityClauseOffsetFoldBound,
    Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

private noncomputable def paperVariableArityClauseOffsetFoldComputable :
    BitTM
      (boundedRecordFoldOutput paperVariableArityClauseOffsetStep) :=
  boundedDependentRecordFoldComputable
    paperVariableArityClauseOffsetStepComputable
    paperVariableArityClauseOffsetFoldBound
    paperVariableArityClauseOffset_polynomiallyBoundedFoldStates

/-- GapCVP reduction support. -/
def sourceClauseWeight (clause : ThreeClause) : ℕ :=
  2 ^ (paperSourceNormalizedClause clause).length - 1

private def paperVariableAritySourceClauseOffsetRecord
    (offset : ℕ) (clause : ThreeClause) : List Bool :=
  lengthPrefixedWord (List.replicate offset true) ++
    (lengthPrefixedWord
      (List.replicate (paperSourceNormalizedClause clause).length true) ++
    (lengthPrefixedWord
      (List.replicate (sourceClauseWeight clause) true) ++
      lengthPrefixedWord (paperSourceNormalizedClauseRecord clause)))

/-- GapCVP reduction support. -/
def sourceClauseWeightSum
    (clauses : List ThreeClause) : ℕ :=
  (clauses.map sourceClauseWeight).sum

/-- GapCVP reduction support. -/
def sourceClauseOffsetCatalogue :
    ℕ → List ThreeClause → List Bool
  | _, [] => []
  | offset, clause :: remaining =>
      paperVariableAritySourceClauseOffsetRecord offset clause ++
        sourceClauseOffsetCatalogue
          (offset + sourceClauseWeight clause) remaining

private def paperClauseOffsetValidState
    (formula : ThreeCNF) (offset : ℕ)
    (catalogue : List Bool) (pending : List ThreeClause) : List Bool :=
  lengthPrefixedWord (List.replicate offset true) ++
    (lengthPrefixedWord catalogue ++
    (lengthPrefixedWord (pending.flatMap encodeThreeClause) ++
      paperSourcePreprocessingOutput (encodeThreeCNF formula)))

@[simp] private theorem paperVariableArityOffsetAccumulator_validState
    (formula : ThreeCNF) (offset : ℕ)
    (catalogue : List Bool) (pending : List ThreeClause) :
    paperVariableArityOffsetAccumulator
        (paperClauseOffsetValidState
          formula offset catalogue pending) =
      List.replicate offset true := by
  simp only [paperVariableArityOffsetAccumulator, paperSourcePreprocessingField,
      paperSourcePreprocessingSuffixAt, Function.iterate_zero, paperClauseOffsetValidState,
          Function.comp_apply, id_eq,
      firstFieldContents_valid]

@[simp] private theorem paperVariableArityOffsetCatalogueField_validState
    (formula : ThreeCNF) (offset : ℕ)
    (catalogue : List Bool) (pending : List ThreeClause) :
    paperOffsetCatalogueField
        (paperClauseOffsetValidState
          formula offset catalogue pending) = catalogue := by
  simp only [paperOffsetCatalogueField, paperSourcePreprocessingField,
      paperSourcePreprocessingSuffixAt,
      Function.iterate_one, paperClauseOffsetValidState, Function.comp_apply,
          firstFieldSuffix_valid,
      firstFieldContents_valid]

@[simp] private theorem paperVariableArityOffsetPending_validState
    (formula : ThreeCNF) (offset : ℕ)
    (catalogue : List Bool) (pending : List ThreeClause) :
    paperVariableArityOffsetPending
        (paperClauseOffsetValidState
          formula offset catalogue pending) =
      pending.flatMap encodeThreeClause := by
  simp [paperVariableArityOffsetPending,
    paperSourcePreprocessingField,
    paperSourcePreprocessingSuffixAt,
    paperClauseOffsetValidState,
    Function.comp_apply]

@[simp] private theorem paperVariableArityOffsetPreserved_validState
    (formula : ThreeCNF) (offset : ℕ)
    (catalogue : List Bool) (pending : List ThreeClause) :
    paperVariableArityOffsetPreserved
        (paperClauseOffsetValidState
          formula offset catalogue pending) =
      paperSourcePreprocessingOutput (encodeThreeCNF formula) := by
  simp [paperVariableArityOffsetPreserved,
    paperSourcePreprocessingSuffixAt,
    paperClauseOffsetValidState,
    Function.comp_apply]

private theorem paperVariableArityClauseOffsetStep_valid_cons
    (formula : ThreeCNF) (offset : ℕ)
    (catalogue : List Bool) (clause : ThreeClause)
    (pending : List ThreeClause) :
    paperVariableArityClauseOffsetStep
        (paperClauseOffsetValidState
          formula offset catalogue (clause :: pending)) =
      paperClauseOffsetValidState formula
        (offset + sourceClauseWeight clause)
        (catalogue ++
          paperVariableAritySourceClauseOffsetRecord offset clause)
        pending := by
  unfold paperVariableArityClauseOffsetStep
    paperOffsetNextAccumulator
    paperOffsetNextCatalogue
    paperVariableArityOffsetNextPending
    paperOffsetCurrentRecord
  simp only [Function.comp_apply,
    paperVariableArityOffsetAccumulator_validState,
    paperVariableArityOffsetCatalogueField_validState,
    paperVariableArityOffsetPending_validState,
    paperVariableArityOffsetPreserved_validState,
    List.flatMap_cons,
    paperVariableArityOffsetCurrentNormalized_apply,
    paperVariableArityOffsetCurrentArity_apply,
    paperVariableArityOffsetCurrentWeight_apply,
    paperSourceClauseNormalizedRecord_valid,
    paperVariableArityClauseArityUnary_valid,
    paperVariableArityClauseWeightUnary_valid,
    clauseSuffix_valid]
  simp only [List.replicate_append_replicate, paperClauseOffsetValidState, sourceClauseWeight,
      paperVariableAritySourceClauseOffsetRecord]

private theorem paperVariableArityClauseOffsetStep_iterate_valid
    (formula : ThreeCNF) (offset : ℕ)
    (catalogue : List Bool) (pending : List ThreeClause) :
    ((paperVariableArityClauseOffsetStep^[pending.length])
      (paperClauseOffsetValidState
        formula offset catalogue pending)) =
      paperClauseOffsetValidState formula
        (offset + sourceClauseWeightSum pending)
        (catalogue ++
          sourceClauseOffsetCatalogue offset pending)
        [] := by
  induction pending generalizing offset catalogue with
  | nil =>
      simp only [List.length_nil, Function.iterate_zero, id_eq, sourceClauseWeightSum,
          List.map_nil, List.sum_nil,
          add_zero, sourceClauseOffsetCatalogue, List.append_nil]
  | cons clause remaining ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply,
        paperVariableArityClauseOffsetStep_valid_cons,
        ih]
      simp only [sourceClauseWeightSum, Nat.add_assoc, List.append_assoc, List.map_cons,
          List.sum_cons,
          sourceClauseOffsetCatalogue]

private def paperVariableArityClauseOffsetSeed
    (input : List Bool) : List Bool :=
  lengthPrefixedWord [] ++
    (lengthPrefixedWord [] ++
    (lengthPrefixedWord
      (paperSourcePreprocessingFinalField 0 input) ++
      paperSourcePreprocessingOutput input))

private noncomputable def paperVariableArityClauseOffsetSeedComputable :
    BitTM
      paperVariableArityClauseOffsetSeed := by
  have pending := GapCVP.TMComposition.computableInPolyTime
    (paperPreprocessingFinalFieldComputable 0)
    structuralPrefixWriterComputable
  have body := pointwiseAppendComputable pending
    paperSourcePreprocessingComputable
  have empties := GapCVP.TMComposition.computableInPolyTime
    body (prependWordComputable
      (lengthPrefixedWord [] ++ lengthPrefixedWord []))
  change BitTM
    (fun input : List Bool =>
      lengthPrefixedWord [] ++
        (lengthPrefixedWord [] ++
        (lengthPrefixedWord
          (paperSourcePreprocessingFinalField 0 input) ++
          paperSourcePreprocessingOutput input)))
  simpa only [List.append_assoc, Function.comp_apply, Function.comp_def] using empties

@[simp] private theorem paperVariableArityClauseOffsetSeed_valid
    (formula : ThreeCNF) :
    paperVariableArityClauseOffsetSeed (encodeThreeCNF formula) =
      paperClauseOffsetValidState formula 0 []
        (noTautClauses formula) := by
  simp only [paperVariableArityClauseOffsetSeed, paperSourcePreprocessingFinalOriginalBody_valid,
      paperClauseOffsetValidState, List.replicate_zero]

/-- GapCVP reduction support. -/
def paperRetainedClauseCountUnary : List Bool → List Bool :=
  paperSourcePreprocessingFinalField 2

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityRetainedClauseCountUnaryComputable :
    BitTM
      paperRetainedClauseCountUnary :=
  paperPreprocessingFinalFieldComputable 2

@[simp] theorem paperVariableArityRetainedClauseCountUnary_valid
    (formula : ThreeCNF) :
    paperRetainedClauseCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (noTautClauses formula).length true := by
  unfold paperRetainedClauseCountUnary
    paperSourcePreprocessingFinalField
  rw [Function.comp_apply,
    paperSourcePreprocessingFinalState_valid,
    paperSourcePreprocessingField_valid_two]

private def paperClauseOffsetPreparation
    (input : List Bool) : List Bool :=
  paperRetainedClauseCountUnary input ++
    false :: paperVariableArityClauseOffsetSeed input

private noncomputable def paperVariableArityClauseOffsetPreparationComputable :
    BitTM
      paperClauseOffsetPreparation := by
  have delimited := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityClauseOffsetSeedComputable
    (prependBitComputable false)
  exact pointwiseAppendComputable
    paperVariableArityRetainedClauseCountUnaryComputable delimited

@[simp] private theorem paperVariableArityClauseOffsetPreparation_valid
    (formula : ThreeCNF) :
    paperClauseOffsetPreparation
        (encodeThreeCNF formula) =
      unaryBoundedFoldWord
        (noTautClauses formula).length
        (paperClauseOffsetValidState formula 0 []
          (noTautClauses formula)) := by
  simp only [paperClauseOffsetPreparation, paperVariableArityRetainedClauseCountUnary_valid,
      paperVariableArityClauseOffsetSeed_valid, unaryBoundedFoldWord]

private def paperClauseOffsetFinalState : List Bool → List Bool :=
  boundedRecordFoldOutput paperVariableArityClauseOffsetStep ∘
    paperClauseOffsetPreparation

private noncomputable def paperVariableArityClauseOffsetFinalStateComputable :
    BitTM
      paperClauseOffsetFinalState :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityClauseOffsetPreparationComputable
    paperVariableArityClauseOffsetFoldComputable

@[simp] private theorem paperVariableArityClauseOffsetFinalState_valid
    (formula : ThreeCNF) :
    paperClauseOffsetFinalState
        (encodeThreeCNF formula) =
      paperClauseOffsetValidState formula
        (sourceClauseWeightSum
          (noTautClauses formula))
        (sourceClauseOffsetCatalogue 0
          (noTautClauses formula))
        [] := by
  unfold paperClauseOffsetFinalState
  rw [Function.comp_apply,
    paperVariableArityClauseOffsetPreparation_valid]
  simp only [boundedRecordFoldOutput,
    parseUnaryBoundedFold_word]
  simpa only [zero_add, List.nil_append] using
      paperVariableArityClauseOffsetStep_iterate_valid formula 0 [] (noTautClauses formula)

/-- GapCVP reduction support. -/
def paperClauseOffsetOutput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (paperOffsetCatalogueField
        (paperClauseOffsetFinalState input)) ++
    (lengthPrefixedWord
      (paperVariableArityOffsetAccumulator
        (paperClauseOffsetFinalState input)) ++
      paperVariableArityOffsetPreserved
        (paperClauseOffsetFinalState input))

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityClauseOffsetOutputComputable :
    BitTM
      paperClauseOffsetOutput := by
  have catalogueField := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityClauseOffsetFinalStateComputable
    paperVariableArityOffsetCatalogueFieldComputable
  have catalogue := GapCVP.TMComposition.computableInPolyTime
    catalogueField structuralPrefixWriterComputable
  have offsetField := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityClauseOffsetFinalStateComputable
    paperVariableArityOffsetAccumulatorComputable
  have offset := GapCVP.TMComposition.computableInPolyTime
    offsetField structuralPrefixWriterComputable
  have preserved := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityClauseOffsetFinalStateComputable
    paperVariableArityOffsetPreservedComputable
  exact pointwiseAppendComputable catalogue
    (pointwiseAppendComputable offset preserved)

theorem paperVariableArityClauseOffsetOutput_valid
    (formula : ThreeCNF) :
    paperClauseOffsetOutput
        (encodeThreeCNF formula) =
      lengthPrefixedWord
        (sourceClauseOffsetCatalogue 0
          (noTautClauses formula)) ++
      (lengthPrefixedWord
        (List.replicate
          (sourceClauseWeightSum
            (noTautClauses formula)) true) ++
        paperSourcePreprocessingOutput (encodeThreeCNF formula)) := by
  unfold paperClauseOffsetOutput
  rw [paperVariableArityClauseOffsetFinalState_valid]
  simp only [paperVariableArityOffsetCatalogueField_validState,
      paperVariableArityOffsetAccumulator_validState,
      paperVariableArityOffsetPreserved_validState]

end ClauseOffsetTM

namespace BinaryPhysicalWordQueryCatalogueTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows

private def sourcePhysicalWordCatalogueRankQuery
    (rank : ℕ) (width source : List Bool) : List Bool :=
  lengthPrefixedWord (List.replicate rank true) ++
    lengthPrefixedWord width ++ source

private def sourcePhysicalWordCatalogueRankUnary : List Bool → List Bool :=
  firstFieldContents

private noncomputable def sourcePhysicalWordCatalogueRankUnaryComputable :
    BitTM
      sourcePhysicalWordCatalogueRankUnary :=
  firstFieldContentsComputable

private def sourcePhysicalWordCatalogueRankOriginalSource :
    List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix

private noncomputable def sourcePhysicalWordCatalogueRankOriginalSourceComputable :
    BitTM
      sourcePhysicalWordCatalogueRankOriginalSource :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable

@[simp] private theorem sourcePhysicalWordCatalogueRankUnary_query
    (rank : ℕ) (width source : List Bool) :
    sourcePhysicalWordCatalogueRankUnary
        (sourcePhysicalWordCatalogueRankQuery rank width source) =
      List.replicate rank true := by
  simp only [sourcePhysicalWordCatalogueRankUnary, sourcePhysicalWordCatalogueRankQuery,
      List.append_assoc,
      firstFieldContents_valid]

@[simp] private theorem sourcePhysicalWordCatalogueRankOriginalSource_query
    (rank : ℕ) (width source : List Bool) :
    sourcePhysicalWordCatalogueRankOriginalSource
        (sourcePhysicalWordCatalogueRankQuery rank width source) =
      source := by
  simp only [sourcePhysicalWordCatalogueRankOriginalSource, sourcePhysicalWordCatalogueRankQuery,
      List.append_assoc, Function.comp_apply, firstFieldSuffix_valid]

private def sourcePhysicalWordCanonicalRhsCandidate
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (sourcePhysicalWordCatalogueRankUnary input) ++
    lengthPrefixedWord [] ++
    sourcePhysicalWordCatalogueRankOriginalSource input

private noncomputable def sourcePhysicalWordCanonicalRhsCandidateComputable :
    BitTM
      sourcePhysicalWordCanonicalRhsCandidate := by
  have hrank := GapCVP.TMComposition.computableInPolyTime
    sourcePhysicalWordCatalogueRankUnaryComputable
    structuralPrefixWriterComputable
  have hzero := sourceFixedWordComputable (lengthPrefixedWord [])
  have hphysical := pointwiseAppendComputable hrank
    (pointwiseAppendComputable hzero
      sourcePhysicalWordCatalogueRankOriginalSourceComputable)
  change BitTM
    (fun input =>
      lengthPrefixedWord (sourcePhysicalWordCatalogueRankUnary input) ++
        lengthPrefixedWord [] ++
        sourcePhysicalWordCatalogueRankOriginalSource input)
  simpa only [Function.comp_apply, List.append_assoc] using hphysical

@[simp] private theorem sourcePhysicalWordCanonicalRhsCandidate_query
    (rank : ℕ) (width source : List Bool) :
    sourcePhysicalWordCanonicalRhsCandidate
        (sourcePhysicalWordCatalogueRankQuery rank width source) =
      affineCellQuery rank 0 source := by
  simp only [sourcePhysicalWordCanonicalRhsCandidate, sourcePhysicalWordCatalogueRankUnary_query,
      sourcePhysicalWordCatalogueRankOriginalSource_query, List.append_assoc, affineCellQuery,
          List.replicate_zero]

theorem sourcePhysicalWordCanonical_range_mul_flatMap
    (rows columns : ℕ) :
    List.range (rows * columns) =
      (List.range rows).flatMap
        (fun row => (List.range columns).map
          (fun column => row * columns + column)) := by
  exact
    GapCVP.BinarySourceConvolutionCorrectness.factor400BinarySourceConvolution_range_mul_flatMap
      rows columns

end BinaryPhysicalWordQueryCatalogueTM

namespace CanonicalMatrixShape

open scoped BigOperators

open Turing GapCVP.Core GapCVP.BinaryEncoding
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.ClauseOffsetTM
open GapCVP.PhysicalColumnOrder GapCVP.BinaryExplicitAffineRows

/-- GapCVP reduction support. -/
structure PaperVariableArityCanonicalBinaryMatrixShape where
  /-- GapCVP reduction support. -/
  system : (encodingLength : ℕ) → ThreeCNF → BinaryAffineSystem
  systemCorrect : ∀ (encodingLength : ℕ) (formula : ThreeCNF),
    system encodingLength formula =
      physicalWordBinarySystem encodingLength formula
  /-- GapCVP reduction support. -/
  rows : List Bool → List Bool
  /-- GapCVP reduction support. -/
  columns : List Bool → List Bool
  /-- GapCVP reduction support. -/
  rowsComputable :
    BitTM rows
  /-- GapCVP reduction support. -/
  columnsComputable :
    BitTM columns
  rowsCorrect : ∀ (formula : ThreeCNF),
    rows (encodeThreeCNF formula) =
      List.replicate
        (system (encodeThreeCNF formula).length formula).rowCount true
  columnsCorrect : ∀ (formula : ThreeCNF),
    columns (encodeThreeCNF formula) =
      List.replicate
        (system (encodeThreeCNF formula).length formula).dimension true
  columnsPositive : ∀ (formula : ThreeCNF),
    0 < (system (encodeThreeCNF formula).length formula).dimension

/-- GapCVP reduction support. -/
structure PaperVariableArityCanonicalBinaryMatrixCellComputer
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) where
  /-- GapCVP reduction support. -/
  check : List Bool → List Bool
  /-- GapCVP reduction support. -/
  rhs : List Bool → List Bool
  /-- GapCVP reduction support. -/
  checkComputable :
    BitTM check
  /-- GapCVP reduction support. -/
  rhsComputable :
    BitTM rhs
  checkCorrect : ∀ (formula : ThreeCNF)
    (row : Fin
      (shape.system (encodeThreeCNF formula).length formula).rowCount)
    (column : Fin
      (shape.system (encodeThreeCNF formula).length formula).dimension),
    check (affineCellQuery
      row.val column.val (encodeThreeCNF formula)) =
      [decide
        ((shape.system (encodeThreeCNF formula).length formula).check
          row column = (1 : ZMod 2))]
  rhsCorrect : ∀ (formula : ThreeCNF)
    (row : Fin
      (shape.system (encodeThreeCNF formula).length formula).rowCount)
    (column : Fin
      (shape.system (encodeThreeCNF formula).length formula).dimension),
    rhs (affineCellQuery
      row.val column.val (encodeThreeCNF formula)) =
      [decide
        ((shape.system (encodeThreeCNF formula).length formula).rightHandSide
          row = (1 : ZMod 2))]

private def paperVariableArityCanonicalBinaryMatrixRawCheckWidth
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput shape.rows shape.columns

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityCanonicalBinaryMatrixRawCheckWidthComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperVariableArityCanonicalBinaryMatrixRawCheckWidth shape) :=
  fourFamilyComputedUnaryProductComputable
    shape.rowsComputable shape.columnsComputable

private theorem paperVariableArityCanonicalBinaryMatrixRawCheckWidth_valid
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) :
    paperVariableArityCanonicalBinaryMatrixRawCheckWidth shape
        (encodeThreeCNF formula) =
      List.replicate
        ((shape.system (encodeThreeCNF formula).length formula).rowCount *
          (shape.system (encodeThreeCNF formula).length formula).dimension)
        true := by
  exact fourFamilyComputedUnaryProductOutput_valid
    shape.rows shape.columns (encodeThreeCNF formula)
    (shape.system (encodeThreeCNF formula).length formula).rowCount
    (shape.system (encodeThreeCNF formula).length formula).dimension
    (shape.rowsCorrect formula) (shape.columnsCorrect formula)

end CanonicalMatrixShape

namespace CanonicalSourceCatalogue

open scoped BigOperators

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceMachineCert GapCVP.SourceStructuralTuringTM
open GapCVP.CNFCappedUnaryPairArithmeticTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.OutputPolynomialCompositionClosure
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceMixedRadixUnaryQuotientRemainderTM
open GapCVP.SourceMixedRadixDimensionRowMajorIndexTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM
open GapCVP.SourceFourFamilyMarkerRotationTM GapCVP.GaussianRowWorker
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryPhysicalWordPackedMatrixTM
open GapCVP.BinaryPhysicalWordQueryCatalogueTM GapCVP.CanonicalMatrixShape
open GapCVP.PhysicalColumnOrder

private noncomputable def paperCanonicalBinaryMatrixCheckWidth
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    SourceQaryMaskDynamicGridWidth where
  output := paperVariableArityCanonicalBinaryMatrixRawCheckWidth shape
  computer :=
    paperVariableArityCanonicalBinaryMatrixRawCheckWidthComputable shape

private noncomputable def paperCanonicalBinaryMatrixRhsWidth
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    SourceQaryMaskDynamicGridWidth where
  output := shape.rows
  computer := shape.rowsComputable

private theorem paperVariableArityCanonicalBinaryMatrixCheckWidth_valid
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) :
    (paperCanonicalBinaryMatrixCheckWidth shape).output
        (encodeThreeCNF formula) =
      List.replicate
        ((shape.system (encodeThreeCNF formula).length formula).rowCount *
          (shape.system (encodeThreeCNF formula).length formula).dimension)
        true :=
  paperVariableArityCanonicalBinaryMatrixRawCheckWidth_valid
    shape formula

private theorem paperVariableArityCanonicalBinaryMatrixRhsWidth_valid
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) :
    (paperCanonicalBinaryMatrixRhsWidth shape).output
        (encodeThreeCNF formula) =
      List.replicate
        (shape.system (encodeThreeCNF formula).length formula).rowCount
        true :=
  shape.rowsCorrect formula

private def paperVariableArityCanonicalBinaryMatrixRankDimension
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    List Bool → List Bool :=
  shape.columns ∘ sourcePhysicalWordCatalogueRankOriginalSource

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityCanonicalBinaryMatrixRankDimensionComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperVariableArityCanonicalBinaryMatrixRankDimension shape) :=
  GapCVP.TMComposition.computableInPolyTime
    sourcePhysicalWordCatalogueRankOriginalSourceComputable
    shape.columnsComputable

private def paperCanonicalBinaryMatrixRankDivisionInput
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (input : List Bool) : List Bool :=
  sourcePhysicalWordCatalogueRankUnary input ++ false ::
    (paperVariableArityCanonicalBinaryMatrixRankDimension
      shape input ++ false ::
      sourcePhysicalWordCatalogueRankOriginalSource input)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityCanonicalBinaryMatrixRankDivisionInputComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperCanonicalBinaryMatrixRankDivisionInput shape) := by
  have source := GapCVP.TMComposition.computableInPolyTime
    sourcePhysicalWordCatalogueRankOriginalSourceComputable
    (prependBitComputable false)
  have dimension := pointwiseAppendComputable
    (paperVariableArityCanonicalBinaryMatrixRankDimensionComputable shape)
    source
  have separator := GapCVP.TMComposition.computableInPolyTime
    dimension (prependBitComputable false)
  exact pointwiseAppendComputable
    sourcePhysicalWordCatalogueRankUnaryComputable separator

private def paperCanonicalBinaryMatrixRankDivisionOutput
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    List Bool → List Bool :=
  sourceMixedRadixRowMajorPairOutput ∘
    paperCanonicalBinaryMatrixRankDivisionInput shape

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityCanonicalBinaryMatrixRankDivisionOutputComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperCanonicalBinaryMatrixRankDivisionOutput shape) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityCanonicalBinaryMatrixRankDivisionInputComputable shape)
    sourceMixedRadixRowMajorPairComputable

private def paperCanonicalBinaryMatrixRankRow
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (input : List Bool) : List Bool :=
  (unaryPrefixOutput
    (paperCanonicalBinaryMatrixRankDivisionOutput
      shape input)).tail

private noncomputable def paperVariableArityCanonicalBinaryMatrixRankRowComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperCanonicalBinaryMatrixRankRow shape) := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityCanonicalBinaryMatrixRankDivisionOutputComputable
      shape) unaryPrefixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hprefix dropHeadComputable

private def paperCanonicalBinaryMatrixRankColumn
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (input : List Bool) : List Bool :=
  (unaryPrefixOutput
    (unaryPrefixSuffixOutput
      (paperCanonicalBinaryMatrixRankDivisionOutput
        shape input))).tail

private noncomputable def paperVariableArityCanonicalBinaryMatrixRankColumnComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperCanonicalBinaryMatrixRankColumn shape) := by
  have hsuffix := GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityCanonicalBinaryMatrixRankDivisionOutputComputable
      shape) actualUnaryPrefixSuffixComputable
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    hsuffix unaryPrefixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hprefix dropHeadComputable

private def paperVariableArityCanonicalBinaryMatrixCheckCandidate
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (paperCanonicalBinaryMatrixRankRow shape input) ++
    lengthPrefixedWord
      (paperCanonicalBinaryMatrixRankColumn shape input) ++
    sourcePhysicalWordCatalogueRankOriginalSource input

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityCanonicalBinaryMatrixCheckCandidateComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperVariableArityCanonicalBinaryMatrixCheckCandidate shape) := by
  have row := GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityCanonicalBinaryMatrixRankRowComputable shape)
    structuralPrefixWriterComputable
  have column := GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityCanonicalBinaryMatrixRankColumnComputable shape)
    structuralPrefixWriterComputable
  have physical := pointwiseAppendComputable row
    (pointwiseAppendComputable column
      sourcePhysicalWordCatalogueRankOriginalSourceComputable)
  change BitTM
    (fun input =>
      lengthPrefixedWord
          (paperCanonicalBinaryMatrixRankRow shape input) ++
        lengthPrefixedWord
          (paperCanonicalBinaryMatrixRankColumn shape input) ++
        sourcePhysicalWordCatalogueRankOriginalSource input)
  simpa only [Function.comp_apply, List.append_assoc] using physical

private theorem paperVariableArityCanonicalBinaryMatrixRankDivisionInput_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (rank dimension : ℕ) (width source : List Bool)
    (hdimension : shape.columns source =
      List.replicate dimension true) :
    paperCanonicalBinaryMatrixRankDivisionInput shape
        (sourcePhysicalWordCatalogueRankQuery rank width source) =
      sourceUnaryDivisionQuery rank dimension source := by
  simp only [paperCanonicalBinaryMatrixRankDivisionInput,
      sourcePhysicalWordCatalogueRankUnary_query,
      paperVariableArityCanonicalBinaryMatrixRankDimension, Function.comp_apply,
      sourcePhysicalWordCatalogueRankOriginalSource_query, hdimension, sourceUnaryDivisionQuery]

private theorem paperVariableArityCanonicalBinaryMatrixRankDivisionOutput_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (rank dimension : ℕ) (width source : List Bool)
    (hdimension : shape.columns source =
      List.replicate dimension true)
    (hpositive : 0 < dimension) :
    paperCanonicalBinaryMatrixRankDivisionOutput shape
        (sourcePhysicalWordCatalogueRankQuery rank width source) =
      List.replicate (rank / dimension) true ++ false ::
        (List.replicate (rank % dimension) true ++ false ::
          sourceUnaryDivisionQuery rank dimension source) := by
  unfold paperCanonicalBinaryMatrixRankDivisionOutput
  rw [Function.comp_apply,
    paperVariableArityCanonicalBinaryMatrixRankDivisionInput_query
      shape rank dimension width source hdimension,
    sourceMixedRadixRowMajorPairOutput_valid
      rank dimension source hpositive]

private theorem paperVariableArityCanonicalBinaryMatrixRankRow_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (rank dimension : ℕ) (width source : List Bool)
    (hdimension : shape.columns source =
      List.replicate dimension true)
    (hpositive : 0 < dimension) :
    paperCanonicalBinaryMatrixRankRow shape
        (sourcePhysicalWordCatalogueRankQuery rank width source) =
      List.replicate (rank / dimension) true := by
  unfold paperCanonicalBinaryMatrixRankRow
  rw [paperVariableArityCanonicalBinaryMatrixRankDivisionOutput_query
    shape rank dimension width source hdimension hpositive,
    unaryPrefixOutput_replicate_delimiter]
  rfl

private theorem paperVariableArityCanonicalBinaryMatrixRankColumn_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (rank dimension : ℕ) (width source : List Bool)
    (hdimension : shape.columns source =
      List.replicate dimension true)
    (hpositive : 0 < dimension) :
    paperCanonicalBinaryMatrixRankColumn shape
        (sourcePhysicalWordCatalogueRankQuery rank width source) =
      List.replicate (rank % dimension) true := by
  unfold paperCanonicalBinaryMatrixRankColumn
  rw [paperVariableArityCanonicalBinaryMatrixRankDivisionOutput_query
    shape rank dimension width source hdimension hpositive,
    unaryPrefixSuffixOutput_valid,
    unaryPrefixOutput_replicate_delimiter]
  rfl

private theorem paperVariableArityCanonicalBinaryMatrixCheckCandidate_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (rank dimension : ℕ) (width source : List Bool)
    (hdimension : shape.columns source =
      List.replicate dimension true)
    (hpositive : 0 < dimension) :
    paperVariableArityCanonicalBinaryMatrixCheckCandidate shape
        (sourcePhysicalWordCatalogueRankQuery rank width source) =
      affineCellQuery
        (rank / dimension) (rank % dimension) source := by
  unfold paperVariableArityCanonicalBinaryMatrixCheckCandidate
    affineCellQuery
  rw [paperVariableArityCanonicalBinaryMatrixRankRow_query
    shape rank dimension width source hdimension hpositive,
    paperVariableArityCanonicalBinaryMatrixRankColumn_query
      shape rank dimension width source hdimension hpositive,
    sourcePhysicalWordCatalogueRankOriginalSource_query]

private def paperVariableArityCanonicalBinaryMatrixCheckQueryCatalogue
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    List Bool → List Bool :=
  maskDynamicGridCandidateCatalogueOutput
    (paperCanonicalBinaryMatrixCheckWidth shape)
    (paperVariableArityCanonicalBinaryMatrixCheckCandidateComputable shape)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityCanonicalBinaryMatrixCheckQueryCatalogueComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperVariableArityCanonicalBinaryMatrixCheckQueryCatalogue shape) :=
  maskDynamicGridCandidateCatalogueComputable
    (paperCanonicalBinaryMatrixCheckWidth shape)
    (paperVariableArityCanonicalBinaryMatrixCheckCandidateComputable shape)

private def paperVariableArityCanonicalBinaryMatrixRhsQueryCatalogue
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    List Bool → List Bool :=
  maskDynamicGridCandidateCatalogueOutput
    (paperCanonicalBinaryMatrixRhsWidth shape)
    sourcePhysicalWordCanonicalRhsCandidateComputable

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityCanonicalBinaryMatrixRhsQueryCatalogueComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperVariableArityCanonicalBinaryMatrixRhsQueryCatalogue shape) :=
  maskDynamicGridCandidateCatalogueComputable
    (paperCanonicalBinaryMatrixRhsWidth shape)
    sourcePhysicalWordCanonicalRhsCandidateComputable

/-- GapCVP reduction support. -/
def paperCanonicalBinaryMatrixCheckQueries
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) : List (List Bool) :=
  let source := encodeThreeCNF formula
  let system := shape.system source.length formula
  (List.finRange system.rowCount).flatMap fun row =>
    (List.finRange system.dimension).map fun column =>
      affineCellQuery row.val column.val source

/-- GapCVP reduction support. -/
def paperCanonicalBinaryMatrixRhsQueries
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) : List (List Bool) :=
  let source := encodeThreeCNF formula
  let system := shape.system source.length formula
  (List.finRange system.rowCount).map fun row =>
    affineCellQuery row.val 0 source

private theorem paperVariableArityCanonicalBinaryMatrixCheckQueryCatalogue_valid
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) :
    paperVariableArityCanonicalBinaryMatrixCheckQueryCatalogue shape
        (encodeThreeCNF formula) =
      sourceMixedRadixOriginalSourceQueryStream
        (paperCanonicalBinaryMatrixCheckQueries
          shape formula) := by
  let source := encodeThreeCNF formula
  let system := shape.system source.length formula
  have hdimension : shape.columns source =
      List.replicate system.dimension true :=
    shape.columnsCorrect formula
  have hpositive : 0 < system.dimension :=
    shape.columnsPositive formula
  have hwidth := paperVariableArityCanonicalBinaryMatrixCheckWidth_valid
    shape formula
  have hcatalogue :=
    maskDynamicGridCandidateCatalogueOutput_valid
      (paperCanonicalBinaryMatrixCheckWidth shape)
      (paperVariableArityCanonicalBinaryMatrixCheckCandidateComputable shape)
      source (system.rowCount * system.dimension) hwidth
  change maskDynamicGridCandidateCatalogueOutput
    (paperCanonicalBinaryMatrixCheckWidth shape)
    (paperVariableArityCanonicalBinaryMatrixCheckCandidateComputable shape)
    source = _
  rw [hcatalogue,
    sourcePhysicalWordCanonical_range_mul_flatMap]
  have hrow : List.range system.rowCount =
      (List.finRange system.rowCount).map (fun row => row.val) :=
    List.map_coe_finRange_eq_range.symm
  have hcolumn : List.range system.dimension =
      (List.finRange system.dimension).map
        (fun column => column.val) :=
    List.map_coe_finRange_eq_range.symm
  simp_rw [hrow, hcolumn]
  unfold paperCanonicalBinaryMatrixCheckQueries
    sourceMixedRadixOriginalSourceQueryStream
  simp only [List.flatMap_assoc, List.flatMap_map]
  apply List.flatMap_congr
  intro row _
  apply List.flatMap_congr
  intro column _
  have hquotient :
      (row.val * system.dimension + column.val) /
        system.dimension = row.val := by
    simpa only [Nat.mul_comm, Nat.div_eq_of_lt column.isLt, add_zero] using
        Nat.mul_add_div hpositive row.val column.val
  have hremainder :
      (row.val * system.dimension + column.val) %
        system.dimension = column.val := by
    simp only [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt column.isLt, zero_add]
  have hcandidate :=
    paperVariableArityCanonicalBinaryMatrixCheckCandidate_query
      shape (row.val * system.dimension + column.val)
      system.dimension
      ((paperCanonicalBinaryMatrixCheckWidth shape).output
        source)
      source hdimension hpositive
  rw [hquotient, hremainder] at hcandidate
  simpa only [sourceQaryMaskDynamicGridBaseSource, sourcePhysicalWordCatalogueRankQuery,
      List.append_assoc] using congrArg lengthPrefixedWord hcandidate

private theorem paperVariableArityCanonicalBinaryMatrixRhsQueryCatalogue_valid
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) :
    paperVariableArityCanonicalBinaryMatrixRhsQueryCatalogue shape
        (encodeThreeCNF formula) =
      sourceMixedRadixOriginalSourceQueryStream
        (paperCanonicalBinaryMatrixRhsQueries
          shape formula) := by
  let source := encodeThreeCNF formula
  let system := shape.system source.length formula
  have hwidth := paperVariableArityCanonicalBinaryMatrixRhsWidth_valid
    shape formula
  have hcatalogue :=
    maskDynamicGridCandidateCatalogueOutput_valid
      (paperCanonicalBinaryMatrixRhsWidth shape)
      sourcePhysicalWordCanonicalRhsCandidateComputable
      source system.rowCount hwidth
  change maskDynamicGridCandidateCatalogueOutput
    (paperCanonicalBinaryMatrixRhsWidth shape)
    sourcePhysicalWordCanonicalRhsCandidateComputable source = _
  rw [hcatalogue]
  have hrow : List.range system.rowCount =
      (List.finRange system.rowCount).map (fun row => row.val) :=
    List.map_coe_finRange_eq_range.symm
  rw [hrow]
  unfold paperCanonicalBinaryMatrixRhsQueries
    sourceMixedRadixOriginalSourceQueryStream
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro row _
  have hcandidate := sourcePhysicalWordCanonicalRhsCandidate_query
    row.val
    ((paperCanonicalBinaryMatrixRhsWidth shape).output source)
    source
  simpa only [sourceQaryMaskDynamicGridBaseSource, sourcePhysicalWordCatalogueRankQuery,
      List.append_assoc] using congrArg lengthPrefixedWord hcandidate

/-- GapCVP reduction support. -/
def paperCanonicalBinaryMatrixCheckFoldPreparation
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (input : List Bool) : List Bool :=
  (paperCanonicalBinaryMatrixCheckWidth shape).output input ++
    false ::
      (paperVariableArityCanonicalBinaryMatrixCheckQueryCatalogue
        shape input ++ lengthPrefixedWord input)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityCanonicalBinaryMatrixCheckFoldPreparationComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperCanonicalBinaryMatrixCheckFoldPreparation shape) := by
  have hsource := GapCVP.TMComposition.computableInPolyTime
    (Turing.idComputableInPolyTime bitEncoding)
    structuralPrefixWriterComputable
  have htail := pointwiseAppendComputable
    (paperVariableArityCanonicalBinaryMatrixCheckQueryCatalogueComputable
      shape) hsource
  have hseparator := GapCVP.TMComposition.computableInPolyTime
    htail (prependBitComputable false)
  exact pointwiseAppendComputable
    (paperVariableArityCanonicalBinaryMatrixRawCheckWidthComputable shape)
    hseparator

/-- GapCVP reduction support. -/
def paperCanonicalBinaryMatrixRhsFoldPreparation
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (input : List Bool) : List Bool :=
  (paperCanonicalBinaryMatrixRhsWidth shape).output input ++
    false ::
      (paperVariableArityCanonicalBinaryMatrixRhsQueryCatalogue
        shape input ++ lengthPrefixedWord input)

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityCanonicalBinaryMatrixRhsFoldPreparationComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperCanonicalBinaryMatrixRhsFoldPreparation shape) := by
  have hsource := GapCVP.TMComposition.computableInPolyTime
    (Turing.idComputableInPolyTime bitEncoding)
    structuralPrefixWriterComputable
  have htail := pointwiseAppendComputable
    (paperVariableArityCanonicalBinaryMatrixRhsQueryCatalogueComputable
      shape) hsource
  have hseparator := GapCVP.TMComposition.computableInPolyTime
    htail (prependBitComputable false)
  exact pointwiseAppendComputable
    shape.rowsComputable hseparator

theorem paperVariableArityCanonicalBinaryMatrixCheckFoldPreparation_valid
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) :
    paperCanonicalBinaryMatrixCheckFoldPreparation shape
        (encodeThreeCNF formula) =
      sourcePhysicalWordPackedQueryPreparation
        (paperCanonicalBinaryMatrixCheckQueries
          shape formula)
        (encodeThreeCNF formula) := by
  unfold paperCanonicalBinaryMatrixCheckFoldPreparation
    sourcePhysicalWordPackedQueryPreparation unaryBoundedFoldWord
  rw [paperVariableArityCanonicalBinaryMatrixCheckWidth_valid
    shape formula,
    paperVariableArityCanonicalBinaryMatrixCheckQueryCatalogue_valid
      shape formula]
  congr 1
  simp only [paperCanonicalBinaryMatrixCheckQueries, List.length_flatMap, List.length_map,
      List.length_finRange,
      List.map_const', List.sum_replicate, smul_eq_mul]

theorem paperVariableArityCanonicalBinaryMatrixRhsFoldPreparation_valid
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) :
    paperCanonicalBinaryMatrixRhsFoldPreparation shape
        (encodeThreeCNF formula) =
      sourcePhysicalWordPackedQueryPreparation
        (paperCanonicalBinaryMatrixRhsQueries
          shape formula)
        (encodeThreeCNF formula) := by
  unfold paperCanonicalBinaryMatrixRhsFoldPreparation
    sourcePhysicalWordPackedQueryPreparation unaryBoundedFoldWord
  rw [paperVariableArityCanonicalBinaryMatrixRhsWidth_valid
    shape formula,
    paperVariableArityCanonicalBinaryMatrixRhsQueryCatalogue_valid
      shape formula]
  congr 1
  simp only [paperCanonicalBinaryMatrixRhsQueries, List.length_map, List.length_finRange]

/-- GapCVP reduction support. -/
def paperCanonicalBinaryMatrixCheckMarker
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    List Bool → List Bool :=
  binaryGaussianFirstCellWord ∘ worker.check

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityCanonicalBinaryMatrixCheckMarkerComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (paperCanonicalBinaryMatrixCheckMarker worker) :=
  GapCVP.TMComposition.computableInPolyTime
    worker.checkComputable binaryGaussianFirstCellComputable

private theorem paperVariableArityCanonicalBinaryMatrixCheckMarker_length
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (input : List Bool) :
    (paperCanonicalBinaryMatrixCheckMarker
      worker input).length ≤ 1 := by
  change (binaryGaussianFirstCellWord (worker.check input)).length ≤ 1
  cases hword : worker.check input with
  | nil =>
      simp only [binaryGaussianFirstCellWord, markerConditionalOutput, List.length_cons,
          List.length_nil, zero_add,
          Std.le_refl]
  | cons bit remaining =>
      rw [binaryGaussianFirstCellWord_valid]
      exact Nat.le_refl 1

/-- GapCVP reduction support. -/
def paperCanonicalBinaryMatrixRhsMarker
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    List Bool → List Bool :=
  binaryGaussianFirstCellWord ∘ worker.rhs

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityCanonicalBinaryMatrixRhsMarkerComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (paperCanonicalBinaryMatrixRhsMarker worker) :=
  GapCVP.TMComposition.computableInPolyTime
    worker.rhsComputable binaryGaussianFirstCellComputable

private theorem paperVariableArityCanonicalBinaryMatrixRhsMarker_length
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (input : List Bool) :
    (paperCanonicalBinaryMatrixRhsMarker
      worker input).length ≤ 1 := by
  change (binaryGaussianFirstCellWord (worker.rhs input)).length ≤ 1
  cases hword : worker.rhs input with
  | nil =>
      simp only [binaryGaussianFirstCellWord, markerConditionalOutput, List.length_cons,
          List.length_nil, zero_add,
          Std.le_refl]
  | cons bit remaining =>
      rw [binaryGaussianFirstCellWord_valid]
      exact Nat.le_refl 1

private def paperCanonicalBinaryMatrixCheckFold
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    List Bool → List Bool :=
  boundedRecordFoldOutput
    (fourFamilyOriginalMarkerRotationOutput
      (paperCanonicalBinaryMatrixCheckMarker worker)) ∘
    paperCanonicalBinaryMatrixCheckFoldPreparation shape

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityCanonicalBinaryMatrixCheckFoldComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (paperCanonicalBinaryMatrixCheckFold worker) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityCanonicalBinaryMatrixCheckFoldPreparationComputable
      shape)
    (fourFamilyOriginalMarkerFoldComputable
      (paperVariableArityCanonicalBinaryMatrixCheckMarkerComputable worker)
      (paperVariableArityCanonicalBinaryMatrixCheckMarker_length worker))

private def paperCanonicalBinaryMatrixRhsFold
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    List Bool → List Bool :=
  boundedRecordFoldOutput
    (fourFamilyOriginalMarkerRotationOutput
      (paperCanonicalBinaryMatrixRhsMarker worker)) ∘
    paperCanonicalBinaryMatrixRhsFoldPreparation shape

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityCanonicalBinaryMatrixRhsFoldComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (paperCanonicalBinaryMatrixRhsFold worker) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityCanonicalBinaryMatrixRhsFoldPreparationComputable
      shape)
    (fourFamilyOriginalMarkerFoldComputable
      (paperVariableArityCanonicalBinaryMatrixRhsMarkerComputable worker)
      (paperVariableArityCanonicalBinaryMatrixRhsMarker_length worker))

private theorem paperVariableArityCanonicalBinaryMatrixCheckFold_valid
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF) :
    paperCanonicalBinaryMatrixCheckFold worker
        (encodeThreeCNF formula) =
      lengthPrefixedWord (encodeThreeCNF formula) ++
        (paperCanonicalBinaryMatrixCheckQueries
          shape formula).flatMap
            (paperCanonicalBinaryMatrixCheckMarker worker) := by
  unfold paperCanonicalBinaryMatrixCheckFold
  simp only [Function.comp_apply,
    paperVariableArityCanonicalBinaryMatrixCheckFoldPreparation_valid
      shape formula]
  unfold sourcePhysicalWordPackedQueryPreparation
  simpa only [fourFamilyOriginalMarkerStream] using
      boundedRecordFoldOutput_sourceFourFamilyOriginalMarkerQueries
          (paperCanonicalBinaryMatrixCheckMarker worker)
        (paperCanonicalBinaryMatrixCheckQueries shape formula) (lengthPrefixedWord (encodeThreeCNF
            formula))

private theorem paperVariableArityCanonicalBinaryMatrixRhsFold_valid
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF) :
    paperCanonicalBinaryMatrixRhsFold worker
        (encodeThreeCNF formula) =
      lengthPrefixedWord (encodeThreeCNF formula) ++
        (paperCanonicalBinaryMatrixRhsQueries
          shape formula).flatMap
            (paperCanonicalBinaryMatrixRhsMarker worker) := by
  unfold paperCanonicalBinaryMatrixRhsFold
  simp only [Function.comp_apply,
    paperVariableArityCanonicalBinaryMatrixRhsFoldPreparation_valid
      shape formula]
  unfold sourcePhysicalWordPackedQueryPreparation
  simpa only [fourFamilyOriginalMarkerStream] using
      boundedRecordFoldOutput_sourceFourFamilyOriginalMarkerQueries
          (paperCanonicalBinaryMatrixRhsMarker worker)
        (paperCanonicalBinaryMatrixRhsQueries shape formula) (lengthPrefixedWord (encodeThreeCNF
            formula))

private def paperCanonicalBinaryMatrixRecoveredSource
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    List Bool → List Bool :=
  firstFieldContents ∘
    paperCanonicalBinaryMatrixCheckFold worker

private def paperCanonicalBinaryMatrixComputedCheckBits
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    List Bool → List Bool :=
  firstFieldSuffix ∘
    paperCanonicalBinaryMatrixCheckFold worker

private def paperCanonicalBinaryMatrixComputedRhsBits
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    List Bool → List Bool :=
  firstFieldSuffix ∘
    paperCanonicalBinaryMatrixRhsFold worker

/-- GapCVP reduction support. -/
def paperCanonicalBinaryMatrixPackedOutput
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (paperCanonicalBinaryMatrixComputedCheckBits
        worker input) ++
    lengthPrefixedWord
      (paperCanonicalBinaryMatrixComputedRhsBits
        worker input) ++
    paperCanonicalBinaryMatrixRecoveredSource
      worker input

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityCanonicalBinaryMatrixPackedComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (paperCanonicalBinaryMatrixPackedOutput worker) := by
  have hcheck :=
    paperVariableArityCanonicalBinaryMatrixCheckFoldComputable worker
  have hrhs :=
    paperVariableArityCanonicalBinaryMatrixRhsFoldComputable worker
  have hcheckBits := GapCVP.TMComposition.computableInPolyTime
    hcheck firstFieldSuffixComputable
  have hrhsBits := GapCVP.TMComposition.computableInPolyTime
    hrhs firstFieldSuffixComputable
  have hsource := GapCVP.TMComposition.computableInPolyTime
    hcheck firstFieldContentsComputable
  have hcheckRecord := GapCVP.TMComposition.computableInPolyTime
    hcheckBits structuralPrefixWriterComputable
  have hrhsRecord := GapCVP.TMComposition.computableInPolyTime
    hrhsBits structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable hcheckRecord
    (pointwiseAppendComputable hrhsRecord hsource)
  change BitTM
    (fun input =>
      lengthPrefixedWord
          (paperCanonicalBinaryMatrixComputedCheckBits
            worker input) ++
        lengthPrefixedWord
          (paperCanonicalBinaryMatrixComputedRhsBits
            worker input) ++
        paperCanonicalBinaryMatrixRecoveredSource
          worker input)
  simpa only [paperCanonicalBinaryMatrixComputedCheckBits, Function.comp_apply,
      paperCanonicalBinaryMatrixComputedRhsBits, paperCanonicalBinaryMatrixRecoveredSource,
          List.append_assoc] using
      hphysical

private theorem paperVariableArityCanonicalBinaryMatrixRecoveredSource_valid
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF) :
    paperCanonicalBinaryMatrixRecoveredSource worker
        (encodeThreeCNF formula) =
      encodeThreeCNF formula := by
  unfold paperCanonicalBinaryMatrixRecoveredSource
  simp only [Function.comp_apply,
    paperVariableArityCanonicalBinaryMatrixCheckFold_valid
      worker formula]
  exact firstFieldContents_valid
    (encodeThreeCNF formula) _

theorem paperVariableArityCanonicalBinaryMatrixCheckMarker_valid
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF)
    (row : Fin
      (shape.system (encodeThreeCNF formula).length formula).rowCount)
    (column : Fin
      (shape.system (encodeThreeCNF formula).length formula).dimension) :
    paperCanonicalBinaryMatrixCheckMarker worker
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        ((shape.system (encodeThreeCNF formula).length formula).check
          row column = (1 : ZMod 2))] := by
  unfold paperCanonicalBinaryMatrixCheckMarker
  simp only [Function.comp_apply,
    worker.checkCorrect formula row column]
  exact binaryGaussianFirstCellWord_valid _ []

theorem paperVariableArityCanonicalBinaryMatrixRhsMarker_valid
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF)
    (row : Fin
      (shape.system (encodeThreeCNF formula).length formula).rowCount)
    (column : Fin
      (shape.system (encodeThreeCNF formula).length formula).dimension) :
    paperCanonicalBinaryMatrixRhsMarker worker
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        ((shape.system (encodeThreeCNF formula).length formula).rightHandSide
          row = (1 : ZMod 2))] := by
  unfold paperCanonicalBinaryMatrixRhsMarker
  simp only [Function.comp_apply,
    worker.rhsCorrect formula row column]
  exact binaryGaussianFirstCellWord_valid _ []

private theorem paperVariableArityCanonicalBinaryMatrixComputedCheckBits_valid
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF) :
    paperCanonicalBinaryMatrixComputedCheckBits worker
        (encodeThreeCNF formula) =
      sourcePhysicalWordPackedCheckBits
        (shape.system (encodeThreeCNF formula).length formula) := by
  unfold paperCanonicalBinaryMatrixComputedCheckBits
  simp only [Function.comp_apply,
    paperVariableArityCanonicalBinaryMatrixCheckFold_valid
      worker formula]
  rw [firstFieldSuffix_valid]
  unfold paperCanonicalBinaryMatrixCheckQueries
    sourcePhysicalWordPackedCheckBits
  simp only [List.flatMap_assoc, List.flatMap_map]
  apply List.flatMap_congr
  intro row _
  calc
    (List.finRange
        (shape.system (encodeThreeCNF formula).length
          formula).dimension).flatMap
        (fun column =>
          paperCanonicalBinaryMatrixCheckMarker worker
            (affineCellQuery
              row.val column.val (encodeThreeCNF formula))) =
      (List.finRange
        (shape.system (encodeThreeCNF formula).length
          formula).dimension).flatMap
        (fun column =>
          [decide
            ((shape.system (encodeThreeCNF formula).length
              formula).check row column = (1 : ZMod 2))]) := by
        apply List.flatMap_congr
        intro column _
        exact paperVariableArityCanonicalBinaryMatrixCheckMarker_valid
          worker formula row column
    _ =
      (List.finRange
        (shape.system (encodeThreeCNF formula).length
          formula).dimension).map
        (fun column => decide
          ((shape.system (encodeThreeCNF formula).length
            formula).check row column = (1 : ZMod 2))) :=
        sourcePhysicalWordPackedFlatMap_singleton _ _

private theorem paperVariableArityCanonicalBinaryMatrixComputedRhsBits_valid
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF) :
    paperCanonicalBinaryMatrixComputedRhsBits worker
        (encodeThreeCNF formula) =
      sourcePhysicalWordPackedRhsBits
        (shape.system (encodeThreeCNF formula).length formula) := by
  unfold paperCanonicalBinaryMatrixComputedRhsBits
  simp only [Function.comp_apply,
    paperVariableArityCanonicalBinaryMatrixRhsFold_valid
      worker formula]
  rw [firstFieldSuffix_valid]
  unfold paperCanonicalBinaryMatrixRhsQueries
    sourcePhysicalWordPackedRhsBits
  simp only [List.flatMap_map]
  let column : Fin
      (shape.system (encodeThreeCNF formula).length
        formula).dimension :=
    ⟨0, shape.columnsPositive formula⟩
  calc
    (List.finRange
        (shape.system (encodeThreeCNF formula).length
          formula).rowCount).flatMap
        (fun row =>
          paperCanonicalBinaryMatrixRhsMarker worker
            (affineCellQuery row.val 0
              (encodeThreeCNF formula))) =
      (List.finRange
        (shape.system (encodeThreeCNF formula).length
          formula).rowCount).flatMap
        (fun row =>
          [decide
            ((shape.system (encodeThreeCNF formula).length
              formula).rightHandSide row = (1 : ZMod 2))]) := by
        apply List.flatMap_congr
        intro row _
        simpa only [column] using paperVariableArityCanonicalBinaryMatrixRhsMarker_valid worker
            formula row column
    _ =
      (List.finRange
        (shape.system (encodeThreeCNF formula).length
          formula).rowCount).map
        (fun row => decide
          ((shape.system (encodeThreeCNF formula).length
            formula).rightHandSide row = (1 : ZMod 2))) :=
        sourcePhysicalWordPackedFlatMap_singleton _ _

theorem paperVariableArityCanonicalBinaryMatrixPackedOutput_valid
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF) :
    paperCanonicalBinaryMatrixPackedOutput worker
        (encodeThreeCNF formula) =
      lengthPrefixedWord
        (sourcePhysicalWordPackedCheckBits
          (physicalWordBinarySystem
            (encodeThreeCNF formula).length formula)) ++
      lengthPrefixedWord
        (sourcePhysicalWordPackedRhsBits
          (physicalWordBinarySystem
            (encodeThreeCNF formula).length formula)) ++
        encodeThreeCNF formula := by
  unfold paperCanonicalBinaryMatrixPackedOutput
  rw [paperVariableArityCanonicalBinaryMatrixComputedCheckBits_valid
    worker formula,
    paperVariableArityCanonicalBinaryMatrixComputedRhsBits_valid
      worker formula,
    paperVariableArityCanonicalBinaryMatrixRecoveredSource_valid
      worker formula,
    shape.systemCorrect (encodeThreeCNF formula).length formula]

end CanonicalSourceCatalogue

namespace GaussianAdaptivePhysicalCandidateCatalogueTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryExplicitAffineRows
open GapCVP.GaussianPivotScheduleTM GapCVP.GaussianAdaptiveEliminationCorrectness
open GapCVP.GaussianAdaptivePackedTraceCorrectness GapCVP.GaussianAdaptivePhysicalStateCellTM
open GapCVP.GaussianAdaptivePackedStateLookupTM

/-- GapCVP reduction support. -/
def gaussianPhysicalPivotColumnQuery
    (column : ℕ) (state : List Bool) : List Bool :=
  lengthPrefixedWord (List.replicate column true) ++ state

private def gaussianPhysicalPivotColumnPackedState : List Bool → List Bool :=
  firstFieldSuffix

private noncomputable def gaussianPhysicalPivotColumnPackedStateComputable :
    BitTM
      gaussianPhysicalPivotColumnPackedState :=
  firstFieldSuffixComputable

private def gaussianPhysicalPivotRowWidthOutput : List Bool → List Bool :=
  gaussianDenseStateRowCountUnary ∘
    gaussianPhysicalPivotColumnPackedState

private noncomputable def gaussianPhysicalPivotRowWidthComputable :
    BitTM
      gaussianPhysicalPivotRowWidthOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPivotColumnPackedStateComputable
    gaussianDenseStateRowCountUnaryComputable

private noncomputable def gaussianPhysicalPivotRowWidth :
    SourceQaryMaskDynamicGridWidth where
  output := gaussianPhysicalPivotRowWidthOutput
  computer := gaussianPhysicalPivotRowWidthComputable

/-- GapCVP reduction support. -/
def gaussianPhysicalPivotRecordWord
    (row width column : ℕ) (state : List Bool) : List Bool :=
  lengthPrefixedWord (List.replicate row true) ++
    lengthPrefixedWord (List.replicate width true) ++
    gaussianPhysicalPivotColumnQuery column state

/-- GapCVP reduction support. -/
def gaussianPhysicalPivotRecordRow : List Bool → List Bool :=
  firstFieldContents

/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalPivotRecordRowComputable :
    BitTM
      gaussianPhysicalPivotRecordRow :=
  firstFieldContentsComputable

/-- Internal support shared across GapCVP continuation modules. -/
def gaussianPhysicalPivotRecordColumn : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix ∘ firstFieldSuffix

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def gaussianPhysicalPivotRecordColumnComputable :
    BitTM
      gaussianPhysicalPivotRecordColumn := by
  have hwidth := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hwidth firstFieldContentsComputable

/-- GapCVP reduction support. -/
def gaussianPhysicalPivotRecordState : List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix ∘ firstFieldSuffix

/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalPivotRecordStateComputable :
    BitTM
      gaussianPhysicalPivotRecordState := by
  have hwidth := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hwidth firstFieldSuffixComputable

/-- Internal support shared across GapCVP continuation modules. -/
def gaussianPhysicalPivotRecordNextUnary : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix ∘ firstFieldSuffix ∘
    gaussianPhysicalPivotRecordState

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def gaussianPhysicalPivotRecordNextUnaryComputable :
    BitTM
      gaussianPhysicalPivotRecordNextUnary := by
  have hcheck := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPivotRecordStateComputable
    firstFieldSuffixComputable
  have hrhs := GapCVP.TMComposition.computableInPolyTime
    hcheck firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hrhs firstFieldContentsComputable

private def gaussianPhysicalPivotRecordEligible : List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    (fourFamilyComputedUnaryLessBitOutput
      gaussianPhysicalPivotRecordRow
      gaussianPhysicalPivotRecordNextUnary)

private noncomputable def gaussianPhysicalPivotRecordEligibleComputable :
    BitTM
      gaussianPhysicalPivotRecordEligible :=
  fourFamilyBooleanNotOutputComputable
    (fourFamilyComputedUnaryLessBitComputable
      gaussianPhysicalPivotRecordRowComputable
      gaussianPhysicalPivotRecordNextUnaryComputable)

private def gaussianPhysicalPivotRecordCellQuery
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (gaussianPhysicalPivotRecordRow input) ++
    lengthPrefixedWord (gaussianPhysicalPivotRecordColumn input) ++
    gaussianPhysicalPivotRecordState input

private noncomputable def gaussianPhysicalPivotRecordCellQueryComputable :
    BitTM
      gaussianPhysicalPivotRecordCellQuery := by
  have hrow := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPivotRecordRowComputable
    structuralPrefixWriterComputable
  have hcolumn := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPivotRecordColumnComputable
    structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable hrow
    (pointwiseAppendComputable hcolumn
      gaussianPhysicalPivotRecordStateComputable)
  have hsimplified :
      BitTM
        (fun input =>
      lengthPrefixedWord (gaussianPhysicalPivotRecordRow input) ++
        (lengthPrefixedWord
          (gaussianPhysicalPivotRecordColumn input) ++
          gaussianPhysicalPivotRecordState input)) := by
    simpa only [Function.comp_apply] using hphysical
  have heq :
      (fun input =>
        lengthPrefixedWord (gaussianPhysicalPivotRecordRow input) ++
          (lengthPrefixedWord
            (gaussianPhysicalPivotRecordColumn input) ++
            gaussianPhysicalPivotRecordState input)) =
        gaussianPhysicalPivotRecordCellQuery := by
    funext input
    simp only [gaussianPhysicalPivotRecordCellQuery,
      List.append_assoc]
  rw [heq] at hsimplified
  exact hsimplified

private def gaussianPhysicalPivotRecordCheckBit : List Bool → List Bool :=
  gaussianPackedStateCheckCellWord ∘
    gaussianPhysicalPivotRecordCellQuery

private noncomputable def gaussianPhysicalPivotRecordCheckBitComputable :
    BitTM
      gaussianPhysicalPivotRecordCheckBit :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPivotRecordCellQueryComputable
    gaussianPackedStateCheckCellComputable

private def gaussianPhysicalPivotRecordBit : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    gaussianPhysicalPivotRecordEligible
    gaussianPhysicalPivotRecordCheckBit

private noncomputable def gaussianPhysicalPivotRecordBitComputable :
    BitTM
      gaussianPhysicalPivotRecordBit :=
  fourFamilyBooleanAndComputable
    gaussianPhysicalPivotRecordEligibleComputable
    gaussianPhysicalPivotRecordCheckBitComputable

@[simp] private theorem gaussianPhysicalPivotRowWidthOutput_query
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : ℕ) :
    gaussianPhysicalPivotRowWidthOutput
        (gaussianPhysicalPivotColumnQuery column
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate m true := by
  simp only [gaussianPhysicalPivotRowWidthOutput, gaussianPhysicalPivotColumnPackedState,
      gaussianPhysicalPivotColumnQuery, Function.comp_apply, firstFieldSuffix_valid,
      gaussianDenseStateRowCountUnary_effective]

@[simp] theorem gaussianPhysicalPivotRecordRow_word
    (row width column : ℕ) (state : List Bool) :
    gaussianPhysicalPivotRecordRow
        (gaussianPhysicalPivotRecordWord row width column state) =
      List.replicate row true := by
  simp only [gaussianPhysicalPivotRecordRow, gaussianPhysicalPivotRecordWord, List.append_assoc,
      firstFieldContents_valid]

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem gaussianPhysicalPivotRecordColumn_word
    (row width column : ℕ) (state : List Bool) :
    gaussianPhysicalPivotRecordColumn
        (gaussianPhysicalPivotRecordWord row width column state) =
      List.replicate column true := by
  simp only [gaussianPhysicalPivotRecordColumn, gaussianPhysicalPivotRecordWord,
      gaussianPhysicalPivotColumnQuery, List.append_assoc, Function.comp_apply,
          firstFieldSuffix_valid,
      firstFieldContents_valid]

@[simp] theorem gaussianPhysicalPivotRecordState_word
    (row width column : ℕ) (state : List Bool) :
    gaussianPhysicalPivotRecordState
        (gaussianPhysicalPivotRecordWord row width column state) =
      state := by
  simp only [gaussianPhysicalPivotRecordState, gaussianPhysicalPivotRecordWord,
      gaussianPhysicalPivotColumnQuery, List.append_assoc, Function.comp_apply,
          firstFieldSuffix_valid]

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem gaussianPhysicalPivotRecordNextUnary_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row width column : ℕ) :
    gaussianPhysicalPivotRecordNextUnary
        (gaussianPhysicalPivotRecordWord row width column
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate state.nextPivot true := by
  simp only [gaussianPhysicalPivotRecordNextUnary, effectiveGaussianPackedStateWord,
      List.append_assoc,
      Function.comp_apply, gaussianPhysicalPivotRecordState_word, firstFieldSuffix_valid,
          firstFieldContents_valid]

private theorem gaussianPhysicalPivotRecordEligible_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row width column : ℕ) :
    gaussianPhysicalPivotRecordEligible
        (gaussianPhysicalPivotRecordWord row width column
          (effectiveGaussianPackedStateWord state source)) =
      [decide (state.nextPivot ≤ row)] := by
  let input := gaussianPhysicalPivotRecordWord row width column
    (effectiveGaussianPackedStateWord state source)
  have hless := fourFamilyComputedUnaryLessBitOutput_valid
    gaussianPhysicalPivotRecordRow
    gaussianPhysicalPivotRecordNextUnary input row state.nextPivot
    (gaussianPhysicalPivotRecordRow_word row width column
      (effectiveGaussianPackedStateWord state source))
    (gaussianPhysicalPivotRecordNextUnary_word
      state source row width column)
  change gaussianPhysicalPivotRecordEligible input = _
  unfold gaussianPhysicalPivotRecordEligible
  rw [fourFamilyBooleanNotOutput_bit _ input _ hless]
  by_cases hrow : row < state.nextPivot
  · have hnot : ¬ state.nextPivot ≤ row := by omega
    simp only [hrow, decide_true, Bool.not_true, hnot, decide_false]
  · have hle : state.nextPivot ≤ row := by omega
    simp only [hrow, decide_false, Bool.not_false, hle, decide_true]

@[simp] private theorem gaussianPhysicalPivotRecordCellQuery_word
    (row width column : ℕ) (state : List Bool) :
    gaussianPhysicalPivotRecordCellQuery
        (gaussianPhysicalPivotRecordWord row width column state) =
      affineCellQuery row column state := by
  simp only [gaussianPhysicalPivotRecordCellQuery, gaussianPhysicalPivotRecordRow_word,
      gaussianPhysicalPivotRecordColumn_word, gaussianPhysicalPivotRecordState_word,
          List.append_assoc, affineCellQuery]

private theorem gaussianPhysicalPivotRecordCheckBit_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row : Fin m) (column : Fin n)
    (width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalPivotRecordCheckBit
        (gaussianPhysicalPivotRecordWord row.val width column.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide (state.system.check row column = (1 : ZMod 2))] := by
  unfold gaussianPhysicalPivotRecordCheckBit
  rw [Function.comp_apply,
    gaussianPhysicalPivotRecordCellQuery_word]
  exact gaussianPackedStateCheckCellWord_query
    state source row column hrows

private theorem gaussianPhysicalPivotRecordBit_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row : Fin m) (column : Fin n)
    (width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalPivotRecordBit
        (gaussianPhysicalPivotRecordWord row.val width column.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide (state.nextPivot ≤ row.val ∧
        state.system.check row column = (1 : ZMod 2))] := by
  let input := gaussianPhysicalPivotRecordWord
    row.val width column.val
    (effectiveGaussianPackedStateWord state source)
  have heligible := gaussianPhysicalPivotRecordEligible_word
    state source row.val width column.val
  have hcheck := gaussianPhysicalPivotRecordCheckBit_word
    state source row column width hrows
  change gaussianPhysicalPivotRecordBit input = _
  unfold gaussianPhysicalPivotRecordBit
  rw [fourFamilyBooleanAndOutput_bits _ _ input _ _
    heligible hcheck]
  by_cases hrow : state.nextPivot ≤ row.val <;>
    by_cases hentry : state.system.check row column = (1 : ZMod 2) <;>
    simp [hrow, hentry]

private def gaussianPhysicalPivotCandidateCatalogueOutput :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    gaussianPhysicalPivotRowWidth
    gaussianPhysicalPivotRecordBitComputable

private noncomputable def gaussianPhysicalPivotCandidateCatalogueComputable :
    BitTM
      gaussianPhysicalPivotCandidateCatalogueOutput :=
  maskDynamicGridRecordCatalogueComputable
    gaussianPhysicalPivotRowWidth
    gaussianPhysicalPivotRecordBitComputable

private theorem gaussianPhysicalPivotCandidateCatalogueOutput_valid
    (input : List Bool) (count : ℕ)
    (hwidth : gaussianPhysicalPivotRowWidth.output input =
      List.replicate count true) :
    gaussianPhysicalPivotCandidateCatalogueOutput input =
      (List.range count).flatMap (fun rank =>
        gaussianPhysicalPivotRecordBit
          (lengthPrefixedWord (List.replicate rank true) ++
            sourceQaryMaskDynamicGridBaseSource
              gaussianPhysicalPivotRowWidth input)) := by
  exact maskDynamicGridRecordCatalogueOutput_valid
    gaussianPhysicalPivotRowWidth
    gaussianPhysicalPivotRecordBitComputable input count hwidth

private theorem gaussianPhysicalPivotRowWidth_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : ℕ) :
    gaussianPhysicalPivotRowWidth.output
        (gaussianPhysicalPivotColumnQuery column
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate m true := by
  exact gaussianPhysicalPivotRowWidthOutput_query
    state source column

private theorem gaussianPhysicalPivotGeneratedRecord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : ℕ) (row : ℕ) :
    lengthPrefixedWord (List.replicate row true) ++
        sourceQaryMaskDynamicGridBaseSource
          gaussianPhysicalPivotRowWidth
          (gaussianPhysicalPivotColumnQuery column
            (effectiveGaussianPackedStateWord state source)) =
      gaussianPhysicalPivotRecordWord row m column
        (effectiveGaussianPackedStateWord state source) := by
  unfold sourceQaryMaskDynamicGridBaseSource
  rw [gaussianPhysicalPivotRowWidth_effective
    state source column]
  simp only [gaussianPhysicalPivotRecordWord,
    List.append_assoc]

theorem gaussianPhysicalPivot_range_flatMap_finRange
    {α : Type} (count : ℕ) (record : ℕ → List α) :
    (List.range count).flatMap record =
      (List.finRange count).flatMap
        (fun index => record index.val) := by
  have hrange : (List.finRange count).map Fin.val =
      List.range count := by
    simp only [List.map_coe_finRange_eq_range]
  calc
    (List.range count).flatMap record =
        ((List.finRange count).map Fin.val).flatMap record := by
          rw [hrange]
    _ = (List.finRange count).flatMap
          (fun index => record index.val) := by
          rw [List.flatMap_map]

private theorem gaussianPhysicalPivotCandidateCatalogueOutput_grid_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : Fin n) :
    gaussianPhysicalPivotCandidateCatalogueOutput
        (gaussianPhysicalPivotColumnQuery column.val
          (effectiveGaussianPackedStateWord state source)) =
      (List.range m).flatMap (fun row =>
        gaussianPhysicalPivotRecordBit
          (gaussianPhysicalPivotRecordWord row m column.val
            (effectiveGaussianPackedStateWord state source))) := by
  let input := gaussianPhysicalPivotColumnQuery column.val
    (effectiveGaussianPackedStateWord state source)
  have hwidth : gaussianPhysicalPivotRowWidth.output input =
      List.replicate m true :=
    gaussianPhysicalPivotRowWidth_effective
      state source column.val
  calc
    gaussianPhysicalPivotCandidateCatalogueOutput input =
        (List.range m).flatMap (fun row =>
          gaussianPhysicalPivotRecordBit
            (lengthPrefixedWord (List.replicate row true) ++
              sourceQaryMaskDynamicGridBaseSource
                gaussianPhysicalPivotRowWidth input)) :=
      gaussianPhysicalPivotCandidateCatalogueOutput_valid
        input m hwidth
    _ = (List.range m).flatMap (fun row =>
          gaussianPhysicalPivotRecordBit
            (gaussianPhysicalPivotRecordWord row m column.val
              (effectiveGaussianPackedStateWord state source))) := by
      apply List.flatMap_congr
      intro row _
      exact congrArg gaussianPhysicalPivotRecordBit
        (gaussianPhysicalPivotGeneratedRecord_effective
          state source column.val row)

private theorem gaussianPhysicalPivotCandidateRange_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : Fin n)
    (hrows : 0 < m) :
    (List.range m).flatMap (fun row =>
        gaussianPhysicalPivotRecordBit
          (gaussianPhysicalPivotRecordWord row m column.val
            (effectiveGaussianPackedStateWord state source))) =
      effectiveGaussianPivotCandidates state column := by
  rw [gaussianPhysicalPivot_range_flatMap_finRange]
  unfold effectiveGaussianPivotCandidates
  rw [← List.flatMap_singleton'
    ((List.finRange m).map (fun row =>
      decide (state.nextPivot ≤ row.val ∧
        state.system.check row column = (1 : ZMod 2))))]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro row _
  exact gaussianPhysicalPivotRecordBit_word
    state source row column m hrows

private theorem gaussianPhysicalPivotCandidateCatalogueOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalPivotCandidateCatalogueOutput
        (gaussianPhysicalPivotColumnQuery column.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianPivotCandidates state column := by
  rw [gaussianPhysicalPivotCandidateCatalogueOutput_grid_effective
    state source column]
  exact gaussianPhysicalPivotCandidateRange_effective
    state source column hrows

/-- Internal support shared across GapCVP continuation modules. -/
def gaussianPhysicalPivotDecisionOutput : List Bool → List Bool :=
  binaryGaussianPivotWord ∘
    gaussianPhysicalPivotCandidateCatalogueOutput

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def gaussianPhysicalPivotDecisionComputable :
    BitTM
      gaussianPhysicalPivotDecisionOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPivotCandidateCatalogueComputable
    binaryGaussianPivotComputable

/-- Internal support shared across GapCVP continuation modules. -/
theorem gaussianPhysicalPivotDecisionOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalPivotDecisionOutput
        (gaussianPhysicalPivotColumnQuery column.val
          (effectiveGaussianPackedStateWord state source)) =
      match findPivotOption state column with
      | none => [false]
      | some row => true :: List.replicate row.val true := by
  unfold gaussianPhysicalPivotDecisionOutput
  rw [Function.comp_apply,
    gaussianPhysicalPivotCandidateCatalogueOutput_effective
      state source column hrows]
  exact binaryGaussianPivotWord_effective state column

end GaussianAdaptivePhysicalCandidateCatalogueTM

namespace GaussianAdaptivePhysicalColumnCellUpdateSemantics

open GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian

private theorem clearTarget_check_of_other_row
    {m n : ℕ} (pivot : Fin m) (active other : Fin n)
    (state : State m n) (target row : Fin m)
    (different : row ≠ target) :
    (clearTarget pivot active state target).system.check row other =
      state.system.check row other := by
  unfold clearTarget
  split
  · rfl
  · split
    · simp only [applyOperation, RowOperation.apply, addRow, different, ↓reduceIte]
    · rfl

private theorem clearTarget_rhs_of_other_row
    {m n : ℕ} (pivot : Fin m) (active : Fin n)
    (state : State m n) (target row : Fin m)
    (different : row ≠ target) :
    (clearTarget pivot active state target).system.rhs row =
      state.system.rhs row := by
  unfold clearTarget
  split
  · rfl
  · split
    · simp only [applyOperation, RowOperation.apply, addRow, different, ↓reduceIte]
    · rfl

private theorem clearTargets_check_of_not_mem
    {m n : ℕ} (pivot : Fin m) (active other : Fin n)
    (targets : List (Fin m)) (state : State m n) (row : Fin m)
    (absent : row ∉ targets) :
    (clearTargets pivot active targets state).system.check row other =
      state.system.check row other := by
  induction targets generalizing state with
  | nil => rfl
  | cons target remaining ih =>
      have different : row ≠ target := by
        intro equal
        apply absent
        simp only [equal, List.mem_cons, true_or]
      have remainingAbsent : row ∉ remaining := by
        intro present
        apply absent
        exact List.mem_cons_of_mem target present
      change
        (clearTargets pivot active remaining
          (clearTarget pivot active state target)).system.check row other =
            state.system.check row other
      rw [ih (clearTarget pivot active state target) remainingAbsent]
      exact clearTarget_check_of_other_row
        pivot active other state target row different

private theorem clearTargets_rhs_of_not_mem
    {m n : ℕ} (pivot : Fin m) (active : Fin n)
    (targets : List (Fin m)) (state : State m n) (row : Fin m)
    (absent : row ∉ targets) :
    (clearTargets pivot active targets state).system.rhs row =
      state.system.rhs row := by
  induction targets generalizing state with
  | nil => rfl
  | cons target remaining ih =>
      have different : row ≠ target := by
        intro equal
        apply absent
        simp only [equal, List.mem_cons, true_or]
      have remainingAbsent : row ∉ remaining := by
        intro present
        apply absent
        exact List.mem_cons_of_mem target present
      change
        (clearTargets pivot active remaining
          (clearTarget pivot active state target)).system.rhs row =
            state.system.rhs row
      rw [ih (clearTarget pivot active state target) remainingAbsent]
      exact clearTarget_rhs_of_other_row
        pivot active state target row different

private theorem clearTargets_check_of_nodup
    {m n : ℕ} (pivot : Fin m) (active other : Fin n)
    (targets : List (Fin m)) (distinct : targets.Nodup)
    (state : State m n) (row : Fin m) :
    (clearTargets pivot active targets state).system.check row other =
      if row ∈ targets ∧ row ≠ pivot ∧
          state.system.check row active = (1 : ZMod 2) then
        state.system.check row other + state.system.check pivot other
      else
        state.system.check row other := by
  induction targets generalizing state with
  | nil =>
      simp only [clearTargets, List.foldl_nil, List.not_mem_nil, ne_eq, false_and, ↓reduceIte]
  | cons target remaining ih =>
      have remainingDistinct : remaining.Nodup :=
        List.nodup_cons.mp distinct |>.2
      by_cases equal : row = target
      · subst target
        have absent : row ∉ remaining :=
          (List.nodup_cons.mp distinct).1
        change
          (clearTargets pivot active remaining
            (clearTarget pivot active state row)).system.check row other = _
        rw [clearTargets_check_of_not_mem
          pivot active other remaining
          (clearTarget pivot active state row) row absent]
        by_cases pivotEqual : row = pivot
        · simp only [clearTarget, pivotEqual, ↓reduceDIte, List.mem_cons, true_or, ne_eq,
            not_true_eq_false, false_and,
              and_false, ↓reduceIte]
        · by_cases selected :
              state.system.check row active = (1 : ZMod 2)
          · simp only [clearTarget, pivotEqual, ↓reduceDIte, selected, ↓reduceIte, applyOperation,
              RowOperation.apply,
                addRow, List.mem_cons, true_or, ne_eq, not_false_eq_true, and_self]
          · simp only [clearTarget, pivotEqual, ↓reduceDIte, selected, ↓reduceIte, List.mem_cons,
              true_or, ne_eq,
                not_false_eq_true, and_false]
      · change
          (clearTargets pivot active remaining
            (clearTarget pivot active state target)).system.check row other = _
        rw [ih remainingDistinct (clearTarget pivot active state target)]
        rw [clearTarget_check_of_other_row
          pivot active active state target row equal]
        rw [clearTarget_check_of_other_row
          pivot active other state target row equal]
        rw [clearTarget_check_pivot pivot active other state target]
        simp only [List.mem_cons, equal, false_or]

private theorem clearTargets_rhs_of_nodup
    {m n : ℕ} (pivot : Fin m) (active : Fin n)
    (targets : List (Fin m)) (distinct : targets.Nodup)
    (state : State m n) (row : Fin m) :
    (clearTargets pivot active targets state).system.rhs row =
      if row ∈ targets ∧ row ≠ pivot ∧
          state.system.check row active = (1 : ZMod 2) then
        state.system.rhs row + state.system.rhs pivot
      else
        state.system.rhs row := by
  induction targets generalizing state with
  | nil =>
      simp only [clearTargets, List.foldl_nil, List.not_mem_nil, ne_eq, false_and, ↓reduceIte]
  | cons target remaining ih =>
      have remainingDistinct : remaining.Nodup :=
        List.nodup_cons.mp distinct |>.2
      by_cases equal : row = target
      · subst target
        have absent : row ∉ remaining :=
          (List.nodup_cons.mp distinct).1
        change
          (clearTargets pivot active remaining
            (clearTarget pivot active state row)).system.rhs row = _
        rw [clearTargets_rhs_of_not_mem
          pivot active remaining
          (clearTarget pivot active state row) row absent]
        by_cases pivotEqual : row = pivot
        · simp only [clearTarget, pivotEqual, ↓reduceDIte, List.mem_cons, true_or, ne_eq,
            not_true_eq_false, false_and,
              and_false, ↓reduceIte]
        · by_cases selected :
              state.system.check row active = (1 : ZMod 2)
          · simp only [clearTarget, pivotEqual, ↓reduceDIte, selected, ↓reduceIte, applyOperation,
              RowOperation.apply,
                addRow, List.mem_cons, true_or, ne_eq, not_false_eq_true, and_self]
          · simp only [clearTarget, pivotEqual, ↓reduceDIte, selected, ↓reduceIte, List.mem_cons,
              true_or, ne_eq,
                not_false_eq_true, and_false]
      · change
          (clearTargets pivot active remaining
            (clearTarget pivot active state target)).system.rhs row = _
        rw [ih remainingDistinct (clearTarget pivot active state target)]
        rw [clearTarget_check_of_other_row
          pivot active active state target row equal]
        rw [clearTarget_rhs_of_other_row
          pivot active state target row equal]
        rw [clearTarget_rhs_pivot pivot active state target]
        simp only [List.mem_cons, equal, false_or]

/-- Internal support shared across GapCVP continuation modules. -/
theorem clearTargets_check_finRange
    {m n : ℕ} (pivot : Fin m) (active other : Fin n)
    (state : State m n) (row : Fin m) :
    (clearTargets pivot active (List.finRange m) state).system.check
        row other =
      if row ≠ pivot ∧
          state.system.check row active = (1 : ZMod 2) then
        state.system.check row other + state.system.check pivot other
      else
        state.system.check row other := by
  have exact := clearTargets_check_of_nodup
    pivot active other (List.finRange m)
    (List.nodup_finRange m) state row
  simpa only [ne_eq, List.mem_finRange, true_and] using exact

/-- Internal support shared across GapCVP continuation modules. -/
theorem clearTargets_rhs_finRange
    {m n : ℕ} (pivot : Fin m) (active : Fin n)
    (state : State m n) (row : Fin m) :
    (clearTargets pivot active (List.finRange m) state).system.rhs row =
      if row ≠ pivot ∧
          state.system.check row active = (1 : ZMod 2) then
        state.system.rhs row + state.system.rhs pivot
      else
        state.system.rhs row := by
  have exact := clearTargets_rhs_of_nodup
    pivot active (List.finRange m)
    (List.nodup_finRange m) state row
  simpa only [ne_eq, List.mem_finRange, true_and] using exact

end GaussianAdaptivePhysicalColumnCellUpdateSemantics

namespace GaussianAdaptivePhysicalColumnCellUpdateTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows
open GapCVP.GaussianRowWorker GapCVP.GaussianAdaptivePivotStepTM
open GapCVP.GaussianAdaptivePackedTraceCorrectness GapCVP.GaussianAdaptivePackedStateLookupTM
open GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM
open GapCVP.GaussianAdaptivePhysicalColumnCellUpdateSemantics
open GapCVP.SourceFourFamilyBooleanPredicateTM
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM

/-- GapCVP reduction support. -/
def gaussianPhysicalColumnCellQuery
    (row column active : ℕ) (state : List Bool) : List Bool :=
  affineCellQuery row column
    (gaussianPhysicalPivotColumnQuery active state)

/-- Internal support shared across GapCVP continuation modules. -/
abbrev gaussianPhysicalColumnCellRow : List Bool → List Bool :=
  sourceExplicitAffineCellRow

/-- Internal support shared across GapCVP continuation modules. -/
abbrev gaussianPhysicalColumnCellColumn : List Bool → List Bool :=
  sourceExplicitAffineCellColumn

/-- Internal support shared across GapCVP continuation modules. -/
def gaussianPhysicalColumnCellActive : List Bool → List Bool :=
  firstFieldContents ∘ sourceExplicitAffineCellOriginalSource

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def gaussianPhysicalColumnCellActiveComputable :
    BitTM
      gaussianPhysicalColumnCellActive :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    firstFieldContentsComputable

/-- Internal support shared across GapCVP continuation modules. -/
def gaussianPhysicalColumnCellPackedState : List Bool → List Bool :=
  firstFieldSuffix ∘ sourceExplicitAffineCellOriginalSource

private noncomputable def gaussianPhysicalColumnCellPackedStateComputable :
    BitTM
      gaussianPhysicalColumnCellPackedState :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    firstFieldSuffixComputable

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem gaussianPhysicalColumnCellRow_query
    (row column active : ℕ) (state : List Bool) :
    gaussianPhysicalColumnCellRow
        (gaussianPhysicalColumnCellQuery row column active state) =
      List.replicate row true := by
  exact sourceExplicitAffineCellRow_query row column
    (gaussianPhysicalPivotColumnQuery active state)

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem gaussianPhysicalColumnCellColumn_query
    (row column active : ℕ) (state : List Bool) :
    gaussianPhysicalColumnCellColumn
        (gaussianPhysicalColumnCellQuery row column active state) =
      List.replicate column true := by
  exact sourceExplicitAffineCellColumn_query row column
    (gaussianPhysicalPivotColumnQuery active state)

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem gaussianPhysicalColumnCellActive_query
    (row column active : ℕ) (state : List Bool) :
    gaussianPhysicalColumnCellActive
        (gaussianPhysicalColumnCellQuery row column active state) =
      List.replicate active true := by
  simp only [gaussianPhysicalColumnCellActive, gaussianPhysicalColumnCellQuery,
      gaussianPhysicalPivotColumnQuery, Function.comp_apply,
          sourceExplicitAffineCellOriginalSource_query,
      firstFieldContents_valid]

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem gaussianPhysicalColumnCellPackedState_query
    (row column active : ℕ) (state : List Bool) :
    gaussianPhysicalColumnCellPackedState
        (gaussianPhysicalColumnCellQuery row column active state) =
      state := by
  simp only [gaussianPhysicalColumnCellPackedState, gaussianPhysicalColumnCellQuery,
      gaussianPhysicalPivotColumnQuery, Function.comp_apply,
          sourceExplicitAffineCellOriginalSource_query,
      firstFieldSuffix_valid]

/-- Internal support shared across GapCVP continuation modules. -/
def gaussianPhysicalColumnDecisionQuery
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (gaussianPhysicalColumnCellActive input) ++
    gaussianPhysicalColumnCellPackedState input

private noncomputable def gaussianPhysicalColumnDecisionQueryComputable :
    BitTM
      gaussianPhysicalColumnDecisionQuery := by
  have hactive := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnCellActiveComputable
    structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable
    hactive gaussianPhysicalColumnCellPackedStateComputable
  change BitTM
    (fun input =>
      lengthPrefixedWord (gaussianPhysicalColumnCellActive input) ++
        gaussianPhysicalColumnCellPackedState input)
  simpa only [Function.comp_apply] using hphysical

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem gaussianPhysicalColumnDecisionQuery_query
    (row column active : ℕ) (state : List Bool) :
    gaussianPhysicalColumnDecisionQuery
        (gaussianPhysicalColumnCellQuery row column active state) =
      gaussianPhysicalPivotColumnQuery active state := by
  simp only [gaussianPhysicalColumnDecisionQuery, gaussianPhysicalColumnCellActive_query,
      gaussianPhysicalColumnCellPackedState_query, gaussianPhysicalPivotColumnQuery]

/-- Internal support shared across GapCVP continuation modules. -/
def gaussianPhysicalColumnDecisionWord : List Bool → List Bool :=
  gaussianPhysicalPivotDecisionOutput ∘
    gaussianPhysicalColumnDecisionQuery

private noncomputable def gaussianPhysicalColumnDecisionComputable :
    BitTM
      gaussianPhysicalColumnDecisionWord :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnDecisionQueryComputable
    gaussianPhysicalPivotDecisionComputable

/-- Internal support shared across GapCVP continuation modules. -/
def gaussianPhysicalColumnPivotPresentWord : List Bool → List Bool :=
  binaryGaussianFirstCellWord ∘ gaussianPhysicalColumnDecisionWord

/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnPivotPresentComputable :
    BitTM
      gaussianPhysicalColumnPivotPresentWord :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnDecisionComputable
    binaryGaussianFirstCellComputable

/-- GapCVP reduction support. -/
def gaussianPhysicalColumnPivotPresent
    (input : List Bool) : Bool :=
  (gaussianPhysicalColumnPivotPresentWord input).headD false

private theorem gaussianPhysicalColumnPivotPresentWord_singleton
    (input : List Bool) :
    gaussianPhysicalColumnPivotPresentWord input =
      [gaussianPhysicalColumnPivotPresent input] := by
  change binaryGaussianFirstCellWord
      (gaussianPhysicalColumnDecisionWord input) =
    [(binaryGaussianFirstCellWord
      (gaussianPhysicalColumnDecisionWord input)).headD false]
  cases gaussianPhysicalColumnDecisionWord input with
  | nil => rfl
  | cons bit remaining =>
      cases bit <;> rfl

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def gaussianPhysicalColumnPivotSelectionComputable :
    BitTM
      (fun input => gaussianPhysicalColumnPivotPresent input :: input) := by
  have hphysical := pointwiseAppendComputable
    gaussianPhysicalColumnPivotPresentComputable
    (Turing.idComputableInPolyTime bitEncoding)
  change BitTM
    (fun input => gaussianPhysicalColumnPivotPresentWord input ++ input)
      at hphysical
  have heq :
      (fun input => gaussianPhysicalColumnPivotPresentWord input ++ input) =
        (fun input => gaussianPhysicalColumnPivotPresent input :: input) := by
    funext input
    rw [gaussianPhysicalColumnPivotPresentWord_singleton]
    rfl
  rw [heq] at hphysical
  exact hphysical

/-- Internal support shared across GapCVP continuation modules. -/
def gaussianPhysicalColumnCandidateUnary : List Bool → List Bool :=
  List.tail ∘ gaussianPhysicalColumnDecisionWord

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def gaussianPhysicalColumnCandidateUnaryComputable :
    BitTM
      gaussianPhysicalColumnCandidateUnary :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnDecisionComputable dropHeadComputable

/-- GapCVP reduction support. -/
def gaussianPhysicalColumnNextPivotUnary : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix ∘ firstFieldSuffix ∘
    gaussianPhysicalColumnCellPackedState

/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnNextPivotUnaryComputable :
    BitTM
      gaussianPhysicalColumnNextPivotUnary := by
  have hcheck := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnCellPackedStateComputable
    firstFieldSuffixComputable
  have hrhs := GapCVP.TMComposition.computableInPolyTime
    hcheck firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hrhs firstFieldContentsComputable

/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem gaussianPhysicalColumnNextPivotUnary_query
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row column active : ℕ) :
    gaussianPhysicalColumnNextPivotUnary
        (gaussianPhysicalColumnCellQuery row column active
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate state.nextPivot true := by
  simp only [gaussianPhysicalColumnNextPivotUnary, effectiveGaussianPackedStateWord,
      List.append_assoc,
      Function.comp_apply, gaussianPhysicalColumnCellPackedState_query, firstFieldSuffix_valid,
          firstFieldContents_valid]

private def gaussianPhysicalColumnDynamicCellQuery
    (row column : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (row input) ++
    (lengthPrefixedWord (column input) ++
      gaussianPhysicalColumnCellPackedState input)

private noncomputable def gaussianPhysicalColumnDynamicCellQueryComputable
    {row column : List Bool → List Bool}
    (hrow : BitTM row)
    (hcolumn : BitTM column) :
    BitTM
      (gaussianPhysicalColumnDynamicCellQuery row column) := by
  have hfirst := GapCVP.TMComposition.computableInPolyTime
    hrow structuralPrefixWriterComputable
  have hsecond := GapCVP.TMComposition.computableInPolyTime
    hcolumn structuralPrefixWriterComputable
  have htail := pointwiseAppendComputable
    hsecond gaussianPhysicalColumnCellPackedStateComputable
  have hphysical := pointwiseAppendComputable hfirst htail
  change BitTM
    (fun input => lengthPrefixedWord (row input) ++
      (lengthPrefixedWord (column input) ++
        gaussianPhysicalColumnCellPackedState input))
  simpa only [Function.comp_apply] using hphysical

/-- Internal support shared across GapCVP continuation modules. -/
def gaussianPhysicalColumnDynamicCheckWord
    (row column : List Bool → List Bool) : List Bool → List Bool :=
  gaussianPackedStateCheckCellWord ∘
    gaussianPhysicalColumnDynamicCellQuery row column

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def gaussianPhysicalColumnDynamicCheckComputable
    {row column : List Bool → List Bool}
    (hrow : BitTM row)
    (hcolumn : BitTM column) :
    BitTM
      (gaussianPhysicalColumnDynamicCheckWord row column) :=
  GapCVP.TMComposition.computableInPolyTime
    (gaussianPhysicalColumnDynamicCellQueryComputable hrow hcolumn)
    gaussianPackedStateCheckCellComputable

/-- Internal support shared across GapCVP continuation modules. -/
def gaussianPhysicalColumnDynamicRhsWord
    (row column : List Bool → List Bool) : List Bool → List Bool :=
  gaussianPackedStateRhsCellWord ∘
    gaussianPhysicalColumnDynamicCellQuery row column

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def gaussianPhysicalColumnDynamicRhsComputable
    {row column : List Bool → List Bool}
    (hrow : BitTM row)
    (hcolumn : BitTM column) :
    BitTM
      (gaussianPhysicalColumnDynamicRhsWord row column) :=
  GapCVP.TMComposition.computableInPolyTime
    (gaussianPhysicalColumnDynamicCellQueryComputable hrow hcolumn)
    gaussianPackedStateRhsCellComputable

/-- Internal support shared across GapCVP continuation modules. -/
theorem gaussianPhysicalColumnDynamicCheckWord_effective
    {m n : ℕ} (state : State m n) (source input : List Bool)
    (rowWorker columnWorker : List Bool → List Bool)
    (row : Fin m) (column : Fin n)
    (hstate : gaussianPhysicalColumnCellPackedState input =
      effectiveGaussianPackedStateWord state source)
    (hrow : rowWorker input = List.replicate row.val true)
    (hcolumn : columnWorker input = List.replicate column.val true) :
    gaussianPhysicalColumnDynamicCheckWord rowWorker columnWorker input =
      [decide (state.system.check row column = (1 : ZMod 2))] := by
  have hquery :
      gaussianPhysicalColumnDynamicCellQuery
          rowWorker columnWorker input =
        affineCellQuery row.val column.val
          (effectiveGaussianPackedStateWord state source) := by
    unfold gaussianPhysicalColumnDynamicCellQuery
      affineCellQuery
    rw [hrow, hcolumn, hstate]
    simp only [List.append_assoc]
  have hrows : 0 < m := by
    have hlt := row.isLt
    omega
  unfold gaussianPhysicalColumnDynamicCheckWord
  rw [Function.comp_apply, hquery]
  exact gaussianPackedStateCheckCellWord_query
    state source row column hrows

/-- Internal support shared across GapCVP continuation modules. -/
theorem gaussianPhysicalColumnDynamicRhsWord_effective
    {m n : ℕ} (state : State m n) (source input : List Bool)
    (rowWorker columnWorker : List Bool → List Bool)
    (row : Fin m) (column : Fin n)
    (hstate : gaussianPhysicalColumnCellPackedState input =
      effectiveGaussianPackedStateWord state source)
    (hrow : rowWorker input = List.replicate row.val true)
    (hcolumn : columnWorker input = List.replicate column.val true) :
    gaussianPhysicalColumnDynamicRhsWord rowWorker columnWorker input =
      [decide (state.system.rhs row = (1 : ZMod 2))] := by
  have hquery :
      gaussianPhysicalColumnDynamicCellQuery
          rowWorker columnWorker input =
        affineCellQuery row.val column.val
          (effectiveGaussianPackedStateWord state source) := by
    unfold gaussianPhysicalColumnDynamicCellQuery
      affineCellQuery
    rw [hrow, hcolumn, hstate]
    simp only [List.append_assoc]
  unfold gaussianPhysicalColumnDynamicRhsWord
  rw [Function.comp_apply, hquery]
  exact gaussianPackedStateRhsCellWord_query
    state source row column.val

/-- Internal support shared across GapCVP continuation modules. -/
def gaussianPhysicalColumnRowIsCandidateWord : List Bool → List Bool :=
  fourFamilyComputedUnaryEqBitOutput
    gaussianPhysicalColumnCellRow gaussianPhysicalColumnCandidateUnary

private noncomputable def gaussianPhysicalColumnRowIsCandidateComputable :
    BitTM
      gaussianPhysicalColumnRowIsCandidateWord :=
  fourFamilyComputedUnaryEqBitComputable
    sourceExplicitAffineCellRowComputable
    gaussianPhysicalColumnCandidateUnaryComputable

/-- Internal support shared across GapCVP continuation modules. -/
def gaussianPhysicalColumnRowIsPivotWord : List Bool → List Bool :=
  fourFamilyComputedUnaryEqBitOutput
    gaussianPhysicalColumnCellRow gaussianPhysicalColumnNextPivotUnary

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def gaussianPhysicalColumnRowIsPivotComputable :
    BitTM
      gaussianPhysicalColumnRowIsPivotWord :=
  fourFamilyComputedUnaryEqBitComputable
    sourceExplicitAffineCellRowComputable
    gaussianPhysicalColumnNextPivotUnaryComputable

/-- Internal support shared across GapCVP continuation modules. -/
def gaussianPhysicalColumnSwappedBitWord
    (original pivot candidate : List Bool → List Bool) :
    List Bool → List Bool :=
  sourceFourFamilyBooleanOrOutput
    (sourceFourFamilyBooleanAndOutput
      gaussianPhysicalColumnRowIsCandidateWord pivot)
    (sourceFourFamilyBooleanOrOutput
      (sourceFourFamilyBooleanAndOutput
        gaussianPhysicalColumnRowIsPivotWord candidate)
      (sourceFourFamilyBooleanAndOutput
        (sourceFourFamilyBooleanAndOutput
          (sourceFourFamilyBooleanNotOutput
            gaussianPhysicalColumnRowIsCandidateWord)
          (sourceFourFamilyBooleanNotOutput
            gaussianPhysicalColumnRowIsPivotWord)) original))

/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def gaussianPhysicalColumnSwappedBitComputable
    {original pivot candidate : List Bool → List Bool}
    (horiginal : BitTM original)
    (hpivot : BitTM pivot)
    (hcandidate : BitTM candidate) :
    BitTM
      (gaussianPhysicalColumnSwappedBitWord original pivot candidate) :=
  sourceFourFamilyBooleanOrComputable
    (fourFamilyBooleanAndComputable
      gaussianPhysicalColumnRowIsCandidateComputable hpivot)
    (sourceFourFamilyBooleanOrComputable
      (fourFamilyBooleanAndComputable
        gaussianPhysicalColumnRowIsPivotComputable hcandidate)
      (fourFamilyBooleanAndComputable
        (fourFamilyBooleanAndComputable
          (fourFamilyBooleanNotOutputComputable
            gaussianPhysicalColumnRowIsCandidateComputable)
          (fourFamilyBooleanNotOutputComputable
            gaussianPhysicalColumnRowIsPivotComputable))
        horiginal))

/-- Internal support shared across GapCVP continuation modules. -/
theorem gaussianPhysicalColumnSwappedBitWord_bits
    (original pivot candidate : List Bool → List Bool)
    (input : List Bool)
    (rowIsCandidate rowIsPivot originalBit pivotBit candidateBit : Bool)
    (hcandidateDecision :
      gaussianPhysicalColumnRowIsCandidateWord input = [rowIsCandidate])
    (hpivotDecision :
      gaussianPhysicalColumnRowIsPivotWord input = [rowIsPivot])
    (horiginal : original input = [originalBit])
    (hpivot : pivot input = [pivotBit])
    (hcandidate : candidate input = [candidateBit]) :
    gaussianPhysicalColumnSwappedBitWord
        original pivot candidate input =
      [(rowIsCandidate && pivotBit) ||
        ((rowIsPivot && candidateBit) ||
          (((!rowIsCandidate) && (!rowIsPivot)) && originalBit))] := by
  have hleft := fourFamilyBooleanAndOutput_bits
    gaussianPhysicalColumnRowIsCandidateWord pivot
    input rowIsCandidate pivotBit hcandidateDecision hpivot
  have hmiddle := fourFamilyBooleanAndOutput_bits
    gaussianPhysicalColumnRowIsPivotWord candidate
    input rowIsPivot candidateBit hpivotDecision hcandidate
  have hnotCandidate := fourFamilyBooleanNotOutput_bit
    gaussianPhysicalColumnRowIsCandidateWord
    input rowIsCandidate hcandidateDecision
  have hnotPivot := fourFamilyBooleanNotOutput_bit
    gaussianPhysicalColumnRowIsPivotWord
    input rowIsPivot hpivotDecision
  have hneither := fourFamilyBooleanAndOutput_bits
    (sourceFourFamilyBooleanNotOutput
      gaussianPhysicalColumnRowIsCandidateWord)
    (sourceFourFamilyBooleanNotOutput
      gaussianPhysicalColumnRowIsPivotWord)
    input (!rowIsCandidate) (!rowIsPivot) hnotCandidate hnotPivot
  have hright := fourFamilyBooleanAndOutput_bits
    (sourceFourFamilyBooleanAndOutput
      (sourceFourFamilyBooleanNotOutput
        gaussianPhysicalColumnRowIsCandidateWord)
      (sourceFourFamilyBooleanNotOutput
        gaussianPhysicalColumnRowIsPivotWord))
    original input ((!rowIsCandidate) && (!rowIsPivot))
    originalBit hneither horiginal
  have hrest := fourFamilyBooleanOrOutput_bits
    (sourceFourFamilyBooleanAndOutput
      gaussianPhysicalColumnRowIsPivotWord candidate)
    (sourceFourFamilyBooleanAndOutput
      (sourceFourFamilyBooleanAndOutput
        (sourceFourFamilyBooleanNotOutput
          gaussianPhysicalColumnRowIsCandidateWord)
        (sourceFourFamilyBooleanNotOutput
          gaussianPhysicalColumnRowIsPivotWord)) original)
    input (rowIsPivot && candidateBit)
    (((!rowIsCandidate) && (!rowIsPivot)) && originalBit)
    hmiddle hright
  exact fourFamilyBooleanOrOutput_bits
    (sourceFourFamilyBooleanAndOutput
      gaussianPhysicalColumnRowIsCandidateWord pivot)
    (sourceFourFamilyBooleanOrOutput
      (sourceFourFamilyBooleanAndOutput
        gaussianPhysicalColumnRowIsPivotWord candidate)
      (sourceFourFamilyBooleanAndOutput
        (sourceFourFamilyBooleanAndOutput
          (sourceFourFamilyBooleanNotOutput
            gaussianPhysicalColumnRowIsCandidateWord)
          (sourceFourFamilyBooleanNotOutput
            gaussianPhysicalColumnRowIsPivotWord)) original))
    input (rowIsCandidate && pivotBit)
    ((rowIsPivot && candidateBit) ||
      (((!rowIsCandidate) && (!rowIsPivot)) && originalBit))
    hleft hrest

end GaussianAdaptivePhysicalColumnCellUpdateTM

end GapCVP

end
